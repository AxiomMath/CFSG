module

public import CFSG.ClassicalInvolution.Q3.Q3PlanSplit
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthLift
public import CFSG.ClassicalInvolution.Q3.Quasisimple
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

theorem sl2Three_exists_metabelian_commutator :
    ∃ a b c d : SL(2, ZMod 3), ⁅⁅a, b⁆, ⁅c, d⁆⁆ = -1 := by
  refine ⟨⟨!![0, 1; 2, 0], by decide⟩, ⟨!![0, 1; 2, 1], by decide⟩,
    ⟨!![0, 1; 2, 0], by decide⟩, ⟨!![0, 1; 2, 2], by decide⟩, ?_⟩
  decide +kernel

theorem sl2Three_derivedSeries_two_ne_bot : derivedSeries SL(2, ZMod 3) 2 ≠ ⊥ := by
  obtain ⟨a, b, c, d, h⟩ := sl2Three_exists_metabelian_commutator
  intro hbot
  have hmem : ⁅⁅a, b⁆, ⁅c, d⁆⁆ ∈ derivedSeries SL(2, ZMod 3) 2 := by
    have h1 : ∀ x y : SL(2, ZMod 3), ⁅x, y⁆ ∈ derivedSeries SL(2, ZMod 3) 1 := fun x y =>
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [derivedSeries_succ]
    exact Subgroup.commutator_mem_commutator (h1 a b) (h1 c d)
  rw [hbot, Subgroup.mem_bot, h] at hmem
  have : (-1 : SL(2, ZMod 3)) ≠ 1 := by decide +kernel
  exact this hmem

section Member

variable {X : Type} [Group X] [Finite X] {L : Subgroup X} {z : X}

theorem odd_orderOf_of_pow_three_mem_oddCore₃ {u : L}
    (hu : u ^ 3 ∈ classicalInvolutionOddCore L) : Odd (orderOf u) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  have h1 : (⟨u ^ 3, hu⟩ : classicalInvolutionOddCore L) ^
      Nat.card (classicalInvolutionOddCore L) = 1 := pow_card_eq_one'
  have h2 : u ^ (3 * Nat.card (classicalInvolutionOddCore L)) = 1 := by
    have h3 : (u ^ 3) ^ Nat.card (classicalInvolutionOddCore L) = 1 := congrArg Subtype.val h1
    rwa [← pow_mul] at h3
  exact Odd.of_dvd_nat (Odd.mul (by decide) hodd) (orderOf_dvd_of_pow_eq_one h2)

theorem odd_orderOf_of_mem_oddCore₃ {u : L} (hu : u ∈ classicalInvolutionOddCore L) :
    Odd (orderOf u) := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hu)

theorem IsClassicalMember3.le_closure_odd (h : IsClassicalMember3 L z) :
    L ≤ Subgroup.closure {u : X | u ∈ L ∧ Odd (orderOf u)} := by
  intro a ha
  obtain ⟨e⟩ := h.nonempty_equiv
  have hlift : ∀ w : SL(2, ZMod 3), w ^ 3 = 1 →
      ∃ u : L, e (QuotientGroup.mk u) = w ∧ Odd (orderOf u) := by
    intro w hw
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (e.symm w)
    refine ⟨u, by rw [hu]; simp, ?_⟩
    apply odd_orderOf_of_pow_three_mem_oddCore₃
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hu, ← map_pow, hw, map_one]
  obtain ⟨b, c, d, hb, hc, hd, hbcd⟩ :=
    sl2Three_exists_cubes (e (QuotientGroup.mk (⟨a, ha⟩ : L)))
  obtain ⟨u₁, hu₁, ho₁⟩ := hlift b hb
  obtain ⟨u₂, hu₂, ho₂⟩ := hlift c hc
  obtain ⟨u₃, hu₃, ho₃⟩ := hlift d hd
  have hmem : (u₁ * u₂ * u₃)⁻¹ * ⟨a, ha⟩ ∈ classicalInvolutionOddCore L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    apply e.injective
    rw [map_mul, map_inv, map_one, QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, map_mul,
      hu₁, hu₂, hu₃, ← hbcd, inv_mul_cancel]
  have hgen : ∀ u : L, Odd (orderOf u) →
      (u : X) ∈ Subgroup.closure {u : X | u ∈ L ∧ Odd (orderOf u)} :=
    fun u hu => Subgroup.subset_closure ⟨u.2, by rwa [Subgroup.orderOf_coe]⟩
  have hao : (⟨a, ha⟩ : L) = u₁ * u₂ * u₃ * ((u₁ * u₂ * u₃)⁻¹ * ⟨a, ha⟩) := by group
  have := (Subgroup.closure {u : X | u ∈ L ∧ Odd (orderOf u)}).mul_mem
    ((Subgroup.closure {u : X | u ∈ L ∧ Odd (orderOf u)}).mul_mem
      ((Subgroup.closure {u : X | u ∈ L ∧ Odd (orderOf u)}).mul_mem (hgen u₁ ho₁) (hgen u₂ ho₂))
      (hgen u₃ ho₃))
    (hgen _ (odd_orderOf_of_mem_oddCore₃ hmem))
  have h2 := congrArg Subtype.val hao
  simp only [Subgroup.coe_mul] at h2 this
  rwa [← h2] at this

theorem sl2Three_pow_four_of_pow_eight : ∀ g : SL(2, ZMod 3), g ^ 8 = 1 → g ^ 4 = 1 := by
  decide +kernel

theorem IsClassicalMember3.exists_quaternion_pair (h : IsClassicalMember3 L z) :
    ∃ x ∈ L, ∃ y ∈ L, x * x = z ∧ x * y * x⁻¹ * y⁻¹ = z := by
  have hodd3 : Odd (Nat.card (ZMod 3)) := odd_natCard_zmod_three
  obtain ⟨e⟩ := h.nonempty_equiv
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  set ρ : L →* SL(2, ZMod 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore L)) with hρ
  have hρker : ∀ q : L, ρ q = 1 → q ∈ classicalInvolutionOddCore L := fun q hq =>
    (QuotientGroup.eq_one_iff q).mp (e.injective (by simpa [hρ] using hq))
  set z' : L := ⟨z, h.mem⟩ with hz'
  have hz'2 : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_mk]; exact h.orderOf_eq_two
  have hρz : ρ z' = -1 := by
    have h1 := (orderOf_eq_two_iff_of_equiv_sl2 hodd3 e
      (QuotientGroup.mk' (classicalInvolutionOddCore L) z')).mp (orderOf_mk_oddCore_eq_two hz'2)
    rw [hρ]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h1, MulEquiv.apply_symm_apply]
  have hLcard : Nat.card L = 24 * Nat.card (classicalInvolutionOddCore L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore L),
      Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hfac : (Nat.card L).factorization 2 = 3 := by
    have h24 : (24 : ℕ).factorization 2 = 3 := by
      have : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.Prime.factorization Nat.prime_three]
    have hm : (Nat.card (classicalInvolutionOddCore L)).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd fun hd =>
        (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr hd)
    rw [hLcard, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply, h24, hm]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'2, pow_one])
  obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
  have hQcard : Nat.card (Q : Subgroup L) = 8 := by
    rw [Sylow.card_eq_multiplicity Q, hfac]
    norm_num
  have hinj : ∀ q ∈ (Q : Subgroup L), ρ q = 1 → q = 1 := by
    intro q hq hρq
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp Q.isPGroup') ⟨q, hq⟩
    rw [Subgroup.orderOf_mk] at hk
    have hodd := odd_orderOf_of_mem_oddCore₃ (hρker q hρq)
    rw [hk] at hodd
    have hk0 : k = 0 := by
      by_contra hk0
      exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hk0⟩)
    rw [hk0, pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  have hQsub : (Q : Subgroup L).map ρ ≤ sl2ThreeQ := by
    rintro _ ⟨q, hq, rfl⟩
    refine mem_sl2ThreeQ_iff.mpr (sl2Three_pow_four_of_pow_eight _ ?_)
    have h1 : q ^ 8 = 1 := by
      have h2 : (⟨q, hq⟩ : (Q : Subgroup L)) ^ Nat.card (Q : Subgroup L) = 1 := pow_card_eq_one'
      have h3 : q ^ Nat.card (Q : Subgroup L) = 1 := congrArg Subtype.val h2
      rwa [hQcard] at h3
    rw [← map_pow, h1, map_one]
  have hQeq : (Q : Subgroup L).map ρ = sl2ThreeQ := by
    refine Subgroup.eq_of_le_of_card_ge hQsub ?_
    rw [natCard_sl2ThreeQ]
    have hinj' : Function.Injective (ρ.comp (Q : Subgroup L).subtype) := by
      rw [injective_iff_map_eq_one]
      intro q hq
      exact Subtype.ext (hinj q.1 q.2 hq)
    have hrange : (ρ.comp (Q : Subgroup L).subtype).range = (Q : Subgroup L).map ρ := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj', Subgroup.card_top,
      hQcard]
  have hQz : z' ∈ (Q : Subgroup L) := hQ (Subgroup.mem_zpowers z')
  have heq : ∀ q ∈ (Q : Subgroup L), ρ q = -1 → q = z' := by
    intro q hq hρq
    have h1 : z'⁻¹ * q = 1 := hinj _ ((Q : Subgroup L).mul_mem ((Q : Subgroup L).inv_mem hQz) hq)
      (by rw [map_mul, map_inv, hρz, hρq]; simp)
    exact (inv_mul_eq_one.mp h1).symm
  have hi₀ : (⟨!![2, 2; 2, 1], by decide⟩ : SL(2, ZMod 3)) ∈ sl2ThreeQ :=
    mem_sl2ThreeQ_iff.mpr (by decide +kernel)
  have hj₀ : (⟨!![2, 1; 1, 1], by decide⟩ : SL(2, ZMod 3)) ∈ sl2ThreeQ :=
    mem_sl2ThreeQ_iff.mpr (by decide +kernel)
  obtain ⟨x, hxQ, hx⟩ := hQeq ▸ hi₀
  obtain ⟨y, hyQ, hy⟩ := hQeq ▸ hj₀
  have hxx : x * x = z' := heq _ ((Q : Subgroup L).mul_mem hxQ hxQ) (by
    rw [map_mul, hx]; decide +kernel)
  have hxy : x * y * x⁻¹ * y⁻¹ = z' := heq _ (by
      exact (Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem hxQ hyQ)
        ((Q : Subgroup L).inv_mem hxQ)) ((Q : Subgroup L).inv_mem hyQ)) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx, hy]; decide +kernel)
  refine ⟨x, x.2, y, y.2, ?_, ?_⟩
  · exact congrArg Subtype.val hxx
  · exact congrArg Subtype.val hxy

end Member

section Lift

variable {K X : Type} [Group K] [Group X] [Finite X] (ψ : K →* X)

theorem comap_le_centralizer_of_isClassicalMember3 (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z)
    {z₀ : K} (hz₀ : ψ z₀ = z) : L.comap ψ ≤ Subgroup.centralizer ({z₀} : Set K) := by
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.orderOf_eq_two, pow_two] at this
  have hLC : L ≤ Subgroup.centralizer ({z} : Set X) := isSubnormal_le h.subnormal
  have hcent : ∀ c ∈ ψ.ker, ∀ g : K, c * g = g * c := fun c hc g =>
    (Subgroup.mem_center_iff.mp (hker hc) g).symm
  have hz₀sq : z₀ * z₀ ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_mul, hz₀, hzz]
  have hodd : ∀ g : K, ψ g ∈ L → Odd (orderOf (ψ g)) → g * z₀ = z₀ * g := by
    intro g hgL hgo
    obtain ⟨c, hc⟩ : ∃ c : K, c = g * z₀ * g⁻¹ * z₀⁻¹ := ⟨_, rfl⟩
    have hcker : c ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hc]
      simp only [map_mul, map_inv, hz₀]
      have := Subgroup.mem_centralizer_singleton_iff.mp (hLC hgL)
      rw [this]
      group
    have hgz : g * z₀ * g⁻¹ = c * z₀ := by rw [hc]; group
    have hpow : ∀ k : ℕ, g ^ k * z₀ * (g ^ k)⁻¹ = c ^ k * z₀ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have e1 : g ^ (k + 1) * z₀ * (g ^ (k + 1))⁻¹ = g * (g ^ k * z₀ * (g ^ k)⁻¹) * g⁻¹ := by
          group
        rw [e1, ih]
        have e2 : g * (c ^ k * z₀) * g⁻¹ = c ^ k * (g * z₀ * g⁻¹) := by
          have := hcent (c ^ k) (pow_mem hcker k) g
          calc g * (c ^ k * z₀) * g⁻¹ = (g * c ^ k) * z₀ * g⁻¹ := by group
            _ = (c ^ k * g) * z₀ * g⁻¹ := by rw [← this]
            _ = c ^ k * (g * z₀ * g⁻¹) := by group
        rw [e2, hgz, pow_succ, mul_assoc]
    set m := orderOf (ψ g) with hm
    have hgm : g ^ m ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_pow, hm, pow_orderOf_eq_one]
    have hcm : c ^ m = 1 := by
      have h1 := hpow m
      have h2 : g ^ m * z₀ * (g ^ m)⁻¹ = z₀ := by rw [hcent (g ^ m) hgm z₀]; group
      rw [h2] at h1
      calc c ^ m = c ^ m * z₀ * z₀⁻¹ := by group
        _ = z₀ * z₀⁻¹ := by rw [← h1]
        _ = 1 := by group
    have hc2 : c * c = 1 := by
      have h1 : g * (z₀ * z₀) * g⁻¹ = z₀ * z₀ := by
        rw [← hcent _ hz₀sq g]
        group
      have h2 : g * (z₀ * z₀) * g⁻¹ = (g * z₀ * g⁻¹) * (g * z₀ * g⁻¹) := by group
      rw [h2, hgz] at h1
      have hcz : c * z₀ = z₀ * c := hcent c hcker z₀
      have h3 : (c * z₀) * (c * z₀) = (c * c) * (z₀ * z₀) := by
        calc (c * z₀) * (c * z₀) = c * (z₀ * c) * z₀ := by group
          _ = c * (c * z₀) * z₀ := by rw [← hcz]
          _ = (c * c) * (z₀ * z₀) := by group
      rw [h3] at h1
      calc c * c = (c * c) * (z₀ * z₀) * (z₀ * z₀)⁻¹ := by group
        _ = (z₀ * z₀) * (z₀ * z₀)⁻¹ := by rw [h1]
        _ = 1 := by group
    have hc1 : c = 1 := by
      obtain ⟨k, hk⟩ := hgo
      have h1 : c ^ m = c := by
        rw [hk, pow_succ, pow_mul, sq, hc2, one_pow, one_mul]
      rw [← h1]
      exact hcm
    calc g * z₀ = (g * z₀ * g⁻¹) * g := by group
      _ = (c * z₀) * g := by rw [hgz]
      _ = z₀ * g := by rw [hc1, one_mul]
  have hS : ∀ u ∈ {u : X | u ∈ L ∧ Odd (orderOf u)},
      u ∈ (Subgroup.centralizer ({z₀} : Set K)).map ψ := by
    rintro u ⟨huL, huo⟩
    obtain ⟨g', hg'⟩ := hψ u
    exact ⟨g', Subgroup.mem_centralizer_singleton_iff.mpr (hodd g' (hg' ▸ huL) (hg' ▸ huo)), hg'⟩
  have hLle : L ≤ (Subgroup.centralizer ({z₀} : Set K)).map ψ :=
    h.le_closure_odd.trans ((Subgroup.closure_le _).mpr hS)
  intro g hg
  obtain ⟨y, hyC, hy⟩ := hLle (Subgroup.mem_comap.mp hg)
  have hker' : y⁻¹ * g ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hy, inv_mul_cancel]
  have hy' : y * z₀ = z₀ * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc g * z₀ = y * ((y⁻¹ * g) * z₀) := by group
    _ = y * (z₀ * (y⁻¹ * g)) := by rw [hcent _ hker' z₀]
    _ = (y * z₀) * (y⁻¹ * g) := by group
    _ = (z₀ * y) * (y⁻¹ * g) := by rw [hy']
    _ = z₀ * g := by group

theorem exists_involution_lift_of_isClassicalMember3 (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z) :
    ∃ w : K, w * w = 1 ∧ ψ w = z ∧ L.comap ψ ≤ Subgroup.centralizer ({w} : Set K) := by
  obtain ⟨x, hx, y, hy, hxx, hxy⟩ := h.exists_quaternion_pair
  obtain ⟨xt, hxt⟩ := hψ x
  obtain ⟨yt, hyt⟩ := hψ y
  set w : K := xt * yt * xt⁻¹ * yt⁻¹ with hw
  have hψw : ψ w = z := by rw [hw]; simp only [map_mul, map_inv, hxt, hyt]; exact hxy
  have hCw := comap_le_centralizer_of_isClassicalMember3 ψ hψ hker h hψw
  have hxL : xt ∈ L.comap ψ := by rw [Subgroup.mem_comap, hxt]; exact hx
  have hyL : yt ∈ L.comap ψ := by rw [Subgroup.mem_comap, hyt]; exact hy
  have hxw : xt * w = w * xt := Subgroup.mem_centralizer_singleton_iff.mp (hCw hxL)
  have hψxx : ψ (xt * xt) = z := by rw [map_mul, hxt, hxx]
  have hCxx := comap_le_centralizer_of_isClassicalMember3 ψ hψ hker h hψxx
  have hyxx : yt * (xt * xt) = (xt * xt) * yt :=
    Subgroup.mem_centralizer_singleton_iff.mp (hCxx hyL)
  refine ⟨w, ?_, hψw, hCw⟩
  have e1 : xt * w * xt⁻¹ = w := by rw [hxw]; group
  have e2 : (xt * xt) * yt * (xt * xt)⁻¹ * yt⁻¹ = 1 := by
    rw [← hyxx]; group
  have e3 : (xt * xt) * yt * (xt * xt)⁻¹ * yt⁻¹ = (xt * w * xt⁻¹) * w := by rw [hw]; group
  rw [e1] at e3
  rw [← e3]
  exact e2

end Lift

@[expose] def IsOddGenerated {K : Type*} [Group K] (N : Subgroup K) : Prop :=
  N ≤ Subgroup.closure {x : K | x ∈ N ∧ Odd (orderOf x)}

section Reduction

variable {K X : Type} [Group K] [Finite K] [Group X] (ψ : K →* X)

theorem exists_odd_orderOf_lift (hψ : Function.Surjective ψ) {u : X} (hu : Odd (orderOf u)) :
    ∃ g : K, ψ g = u ∧ Odd (orderOf g) := by
  have hX : Finite X := Finite.of_surjective ψ hψ
  obtain ⟨g, rfl⟩ := hψ u
  obtain ⟨a, n', hn', hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hdvd : 2 ^ a ∣ orderOf g := ⟨n', hn⟩
  have hg₁ : orderOf (g ^ 2 ^ a) = n' := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) hdvd, hn, Nat.mul_div_cancel_left _
      (pow_pos two_pos a)]
  have hcop : (orderOf (ψ g)).Coprime (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hu)
  have hu₁ : orderOf (ψ g ^ 2 ^ a) = orderOf (ψ g) := Nat.Coprime.orderOf_pow hcop
  have hle : Subgroup.zpowers (ψ g ^ 2 ^ a) ≤ Subgroup.zpowers (ψ g) :=
    (Subgroup.zpowers_le).mpr (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
  have hz : Subgroup.zpowers (ψ g ^ 2 ^ a) = Subgroup.zpowers (ψ g) := by
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hu₁])
  have hmem : ψ g ∈ Submonoid.powers (ψ g ^ 2 ^ a) := by
    rw [mem_powers_iff_mem_zpowers, hz]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := hmem
  refine ⟨(g ^ 2 ^ a) ^ k, ?_, ?_⟩
  · rw [map_pow, map_pow]
    exact hk
  · refine Odd.of_dvd_nat (n := n') hn' ?_
    rw [← hg₁]
    exact orderOf_pow_dvd k

variable [Finite X]

theorem exists_oddGenerated_of_isClassicalMember3 (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z) :
    ∃ w : K, w * w = 1 ∧ ∃ N : Subgroup K, N ≤ Subgroup.centralizer ({w} : Set K) ∧
      IsSubnormal N (Subgroup.centralizer ({w} : Set K)) ∧ Group.IsSolvable N ∧
      IsOddGenerated N ∧ derivedSeries N 2 ≠ ⊥ := by
  obtain ⟨w, hw2, hψw, hCw⟩ := exists_involution_lift_of_isClassicalMember3 ψ hψ hker h
  have hsubN : IsSubnormal (L.comap ψ) (Subgroup.centralizer ({w} : Set K)) := by
    have h1 := CFSG.ClassicalInvolution.ModelFacts.isSubnormal_comap ψ h.subnormal
    have hCC : Subgroup.centralizer ({w} : Set K) ≤
        (Subgroup.centralizer ({z} : Set X)).comap ψ := by
      intro g hg
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, ← hψw, ← map_mul,
        ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp hg]
    have h2 := CFSG.ClassicalInvolution.ModelFacts.isSubnormal_inf h1 hCC
    rwa [inf_eq_left.mpr hCw] at h2
  have hsolvN : Group.IsSolvable ↥(L.comap ψ) := by
    have : Group.IsSolvable ↥L := h.isSolvable
    have hkerle : ψ.ker ≤ L.comap ψ := fun x hx => by
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
      exact L.one_mem
    have : Group.IsSolvable ↥ψ.ker :=
      Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hker b.2) a)
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hkerle)
      ((ψ.comp (L.comap ψ).subtype).codRestrict L fun x => Subgroup.mem_comap.mp x.2) ?_
    intro x hx
    refine ⟨⟨x.1, ?_⟩, Subtype.ext rfl⟩
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact MonoidHom.mem_ker.mpr this
  set S : Set K := {x : K | x ∈ L.comap ψ ∧ Odd (orderOf x)} with hS
  set N₀ : Subgroup K := Subgroup.closure S with hN₀
  have hN₀le : N₀ ≤ L.comap ψ := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hN₀nor : (N₀.subgroupOf (L.comap ψ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hN₀le]
    intro a k ha hk
    induction ha using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨?_, ?_⟩
      · exact (L.comap ψ).mul_mem ((L.comap ψ).mul_mem hk hx.1) ((L.comap ψ).inv_mem hk)
      · have h1 := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective x
        have h2 : orderOf (k * x * k⁻¹) = orderOf x := by simpa [MulAut.conj_apply] using h1
        rw [h2]
        exact hx.2
    | one => simp
    | mul x y _ _ hx hy =>
      have : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
      rw [this]
      exact N₀.mul_mem hx hy
    | inv x _ hx =>
      have : k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ := by group
      rw [this]
      exact N₀.inv_mem hx
  refine ⟨w, hw2, N₀, hN₀le.trans hCw,
    isSubnormal_trans (isSubnormal_of_normal_subgroupOf hN₀le hN₀nor) hsubN, ?_, ?_, ?_⟩
  · exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hN₀le)
      (Subgroup.inclusion_injective hN₀le)
  · exact (Subgroup.closure_mono fun x hx => ⟨Subgroup.subset_closure hx, hx.2⟩)
  ·
    intro hbot
    have hLle : L ≤ N₀.map ψ := by
      refine h.le_closure_odd.trans ((Subgroup.closure_le _).mpr ?_)
      rintro u ⟨huL, huo⟩
      obtain ⟨g, hg, hgo⟩ := exists_odd_orderOf_lift ψ hψ huo
      exact ⟨g, Subgroup.subset_closure ⟨Subgroup.mem_comap.mpr (hg ▸ huL), hgo⟩, hg⟩
    obtain ⟨e⟩ := h.nonempty_equiv
    set φ : ↥N₀ →* SL(2, ZMod 3) :=
      e.toMonoidHom.comp ((QuotientGroup.mk' (classicalInvolutionOddCore L)).comp
        ((ψ.comp N₀.subtype).codRestrict L fun x => Subgroup.mem_comap.mp (hN₀le x.2))) with hφ
    have hφsurj : Function.Surjective φ := by
      intro s
      obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e.symm s)
      obtain ⟨g, hg, hgl⟩ := hLle l.2
      refine ⟨⟨g, hg⟩, ?_⟩
      have : (⟨ψ g, Subgroup.mem_comap.mp (hN₀le hg)⟩ : L) = l := Subtype.ext hgl
      simp only [hφ, MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
      rw [this, hl, MulEquiv.apply_symm_apply]
    have := map_derivedSeries_eq hφsurj 2
    rw [hbot, Subgroup.map_bot] at this
    exact sl2Three_derivedSeries_two_ne_bot this.symm

theorem false_of_isClassicalMember3_of_oddGenerated (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K)
    (hP : ∀ w : K, w * w = 1 → ∀ N : Subgroup K, N ≤ Subgroup.centralizer ({w} : Set K) →
      IsSubnormal N (Subgroup.centralizer ({w} : Set K)) → Group.IsSolvable N →
        IsOddGenerated N → derivedSeries N 2 = ⊥)
    {L : Subgroup X} {z : X} (h : IsClassicalMember3 L z) : False := by
  obtain ⟨w, hw, N, hNC, hNs, hNsolv, hNodd, hNd⟩ :=
    exists_oddGenerated_of_isClassicalMember3 ψ hψ hker h
  exact hNd (hP w hw N hNC hNs hNsolv hNodd)

end Reduction

end CFSG.ClassicalInvolution.Q3
