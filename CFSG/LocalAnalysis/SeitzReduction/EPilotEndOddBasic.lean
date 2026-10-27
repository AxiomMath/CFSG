module

public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphBasic
public import Mathlib.GroupTheory.FixedPointFree

public section

namespace CFSG.SeitzReduction.EPilot

open Subgroup CFSG.SeitzReduction.F4Pilot

variable {G : Type*} [Group G]

theorem isConj_of_sq_eq_one_of_odd_orderOf_mul {s y : G} (hs : s ^ 2 = 1) (hy : y ^ 2 = 1)
    (hodd : Odd (orderOf (s * y))) : IsConj s y := by
  obtain ⟨j, hj⟩ := hodd
  have hs' : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, ← sq, hs]
  have hy' : y⁻¹ = y := by rw [inv_eq_iff_mul_eq_one, ← sq, hy]
  set z := s * y with hz
  set w := z ^ (j + 1) with hw
  have hw2 : w ^ 2 = z := by
    rw [hw, ← pow_mul, show (j + 1) * 2 = (2 * j + 1) + 1 by ring, pow_succ, ← hj,
      pow_orderOf_eq_one, one_mul]
  have hsz : s * z * s⁻¹ = z⁻¹ := by
    rw [hz, hs', mul_inv_rev, hy', hs', ← mul_assoc, ← sq, hs, one_mul]
  have hsw : s * w * s⁻¹ = w⁻¹ := by
    rw [hw, ← conj_pow, hsz, inv_pow]
  have key : s * w = w⁻¹ * s := by
    calc s * w = s * w * s⁻¹ * s := by group
      _ = w⁻¹ * s := by rw [hsw]
  refine isConj_iff.2 ⟨w⁻¹, ?_⟩
  calc w⁻¹ * s * w⁻¹⁻¹ = w⁻¹ * (s * w) := by group
    _ = w⁻¹ * (w⁻¹ * s) := by rw [key]
    _ = (w ^ 2)⁻¹ * s := by group
    _ = z⁻¹ * s := by rw [hw2]
    _ = y := by rw [hz, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, hy']

theorem isConj_of_mul_mem_of_odd {Z : Subgroup G} (hZ : Odd (Nat.card Z)) {s y : G}
    (hs : s ^ 2 = 1) (hy : y ^ 2 = 1) (hsy : s * y ∈ Z) : IsConj s y :=
  isConj_of_sq_eq_one_of_odd_orderOf_mul hs hy
    (Odd.of_dvd_nat hZ (Subgroup.orderOf_dvd_natCard Z hsy))

theorem exists_normal_index_two_of_unique_of_quotientSub [Finite G] {M : Subgroup G}
    (H : Subgroup M) [H.Normal] {t : G} (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M) {x : G}
    (hxM : x ∈ M) {a : ℕ} (ha : 1 ≤ a) (hxo : orderOf x = 2 ^ a)
    (hxQ : orderOf (QuotientGroup.mk' H ⟨x, hxM⟩) = 2 ^ a)
    (hQ : ¬ 2 ^ (a + 1) ∣ Nat.card (M ⧸ H)) {n : ℕ} (hpow : IsConj t (x ^ n)) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  obtain ⟨R, hRidx, hxR, hR⟩ := exists_index_two_of_orderOf_eq_two_pow ha hxQ hQ
  set Y := (R.comap (QuotientGroup.mk' H)).map M.subtype with hY
  have hYM : Y ≤ M := map_subtype_le _
  have hmemY : ∀ y (hy : y ∈ M), y ∈ Y ↔ QuotientGroup.mk' H ⟨y, hy⟩ ∈ R := by
    intro y hy
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro h
      exact ⟨⟨y, hy⟩, h, rfl⟩
  have hYidx : Y.relIndex M = 2 := by
    rw [relIndex, hY, ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective,
      index_comap_of_surjective _ (QuotientGroup.mk'_surjective _), hRidx]
  refine exists_normal_index_two_of_unique_of_relIndex_eq_two hYM hYidx huniq hxM
    (fun h => hxR ((hmemY x hxM).1 h)) hxo (fun y hy hyY _ => ?_) hpow
  have h1 := hR _ (fun h => hyY ((hmemY y hy).2 h))
  have h2 : orderOf (QuotientGroup.mk' H ⟨y, hy⟩) ∣ orderOf y := by
    rw [← Subgroup.orderOf_mk y hy]
    exact orderOf_map_dvd _ _
  rw [hxo]
  exact Nat.le_of_dvd (orderOf_pos y) (h1.trans h2)

section Action

variable {X : Type*} [Group X] {M : Subgroup G} (ρ : M →* MulAut X)

theorem isConj_of_action_eq (hker : Odd (Nat.card ρ.ker)) {s y : G} (hs : s ∈ M) (hy : y ∈ M)
    (hs2 : s ^ 2 = 1) (hy2 : y ^ 2 = 1) (hρ : ρ ⟨s, hs⟩ = ρ ⟨y, hy⟩) : IsConj s y := by
  have hs' : s⁻¹ = s := by rw [inv_eq_iff_mul_eq_one, ← sq, hs2]
  have hk : (⟨s, hs⟩ : M)⁻¹ * ⟨y, hy⟩ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hρ, inv_mul_cancel]
  have hodd : Odd (orderOf ((⟨s, hs⟩ : M)⁻¹ * ⟨y, hy⟩)) :=
    Odd.of_dvd_nat hker (Subgroup.orderOf_dvd_natCard ρ.ker hk)
  refine isConj_of_sq_eq_one_of_odd_orderOf_mul hs2 hy2 ?_
  rw [← Subgroup.orderOf_coe] at hodd
  simpa [hs'] using hodd

theorem action_sq_eq_one {t : G} (htM : t ∈ M) (ht : t ^ 2 = 1) : ρ ⟨t, htM⟩ ^ 2 = 1 := by
  have h1 : (⟨t, htM⟩ : M) ^ 2 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact ht)
  rw [← map_pow, h1, map_one]

variable [Finite G]

include ρ in
theorem exists_normal_index_two_of_action_complement (hker : Odd (Nat.card ρ.ker))
    {C : Subgroup (MulAut X)} [IsCyclic C]
    (hCInn : ∀ β ∈ C, β ∈ (MulAut.conj : X →* MulAut X).range → β = 1)
    (hNF : ∀ α : MulAut X, ∃ g : X, ∃ β ∈ C, α = MulAut.conj g * β)
    (hInn : ∀ g : X, ∃ m : M, ρ m = MulAut.conj g) {t : G} (htM : t ∈ M) (ht : orderOf t = 2)
    (hout : ρ ⟨t, htM⟩ ∉ (MulAut.conj : X →* MulAut X).range)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M)
    (hfus : ∀ y (hy : y ∈ M), orderOf y = 2 →
      ρ ⟨y, hy⟩ ∉ (MulAut.conj : X →* MulAut X).range → ρ ⟨y, hy⟩ ∈ C → IsConj t y) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  classical
  set I : Subgroup (MulAut X) := (MulAut.conj : X →* MulAut X).range with hI
  have hIn : I.Normal := by
    constructor
    rintro _ ⟨x, rfl⟩ α
    refine ⟨α x, MulEquiv.ext fun y => ?_⟩
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  set H : Subgroup M := I.comap ρ with hH
  have : H.Normal := hIn.comap ρ
  set P : Subgroup M := C.comap ρ with hP
  set π : P →* M ⧸ H := (QuotientGroup.mk' H).comp P.subtype with hπ
  have hπs : Function.Surjective π := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H m =>
      obtain ⟨g, β, hβ, hm⟩ := hNF (ρ m)
      obtain ⟨z, hz⟩ := hInn g
      refine ⟨⟨z⁻¹ * m, ?_⟩, ?_⟩
      · rw [hP, mem_comap, map_mul, map_inv, hz, hm, inv_mul_cancel_left]
        exact hβ
      · change QuotientGroup.mk' H (z⁻¹ * m) = QuotientGroup.mk' H m
        have hz1 : QuotientGroup.mk' H z = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hH, mem_comap, hz]
          exact ⟨g, rfl⟩
        rw [map_mul, map_inv, hz1, inv_one, one_mul]
  set ψ : P →* C := (ρ.comp P.subtype).codRestrict C (fun p => p.2) with hψ
  have hker' : π.ker = ψ.ker := by
    ext p
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change QuotientGroup.mk' H (p : M) = 1 ↔ ψ p = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hH, mem_comap]
    constructor
    · intro h
      exact Subtype.ext (hCInn _ p.2 h)
    · intro h
      have h1 : ρ p = 1 := congrArg Subtype.val h
      rw [h1]
      exact I.one_mem
  have hQcyc : IsCyclic (M ⧸ H) := by
    let e1 : (M ⧸ H) ≃* ψ.range :=
      ((QuotientGroup.quotientKerEquivOfSurjective π hπs).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hker')).trans (QuotientGroup.quotientKerEquivRange ψ)
    exact isCyclic_of_surjective e1.symm.toMonoidHom e1.symm.surjective
  have htQ : orderOf (QuotientGroup.mk' H ⟨t, htM⟩) = 2 := by
    have h1 : orderOf (QuotientGroup.mk' H ⟨t, htM⟩) ∣ 2 := by
      refine (orderOf_map_dvd _ _).trans ?_
      rw [Subgroup.orderOf_mk, ht]
    have h2 : QuotientGroup.mk' H ⟨t, htM⟩ ≠ 1 := by
      rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff, hH, mem_comap]
      exact hout
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) h2
    · exact h
  have hQpos : Nat.card (M ⧸ H) ≠ 0 := Nat.card_pos.ne'
  have h2Q : 2 ∣ Nat.card (M ⧸ H) := htQ ▸ orderOf_dvd_natCard _
  set a := (Nat.card (M ⧸ H)).factorization 2 with ha_def
  have ha : 1 ≤ a := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hQpos h2Q
  have hQ : ¬ 2 ^ (a + 1) ∣ Nat.card (M ⧸ H) :=
    Nat.pow_succ_factorization_not_dvd hQpos Nat.prime_two
  have haQ : 2 ^ a ∣ Nat.card (M ⧸ H) := Nat.ordProj_dvd _ _
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := M ⧸ H)
  have hk : Nat.card (M ⧸ H) / 2 ^ a ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hQpos) haQ) (by positivity)).ne'
  have hq₀ : orderOf (g ^ (Nat.card (M ⧸ H) / 2 ^ a)) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hk (by rw [hg]; exact Nat.div_dvd_of_dvd haQ), hg,
      Nat.div_div_self haQ hQpos]
  obtain ⟨p, hp⟩ := hπs (g ^ (Nat.card (M ⧸ H) / 2 ^ a))
  set m := orderOf (p ^ 2 ^ a) with hm
  have hpk : p ^ 2 ^ a ∈ ψ.ker := by
    rw [← hker', MonoidHom.mem_ker, map_pow, hp]
    have h1 := pow_orderOf_eq_one (g ^ (Nat.card (M ⧸ H) / 2 ^ a))
    rwa [hq₀] at h1
  have hmodd : Odd m := by
    have h1 : ((p ^ 2 ^ a : P) : M) ∈ ρ.ker := by
      have h2 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hpk)
      exact h2
    have h2 := Subgroup.orderOf_dvd_natCard ρ.ker h1
    rw [Subgroup.orderOf_coe] at h2
    exact Odd.of_dvd_nat hker h2
  set x₀ : P := p ^ m with hx₀
  have hcop : Nat.Coprime (orderOf (π p)) m := by
    rw [hp, hq₀]
    exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hmodd)
  have hπx : orderOf (π x₀) = 2 ^ a := by
    rw [hx₀, map_pow, Nat.Coprime.orderOf_pow hcop, hp, hq₀]
  have hx₀2 : x₀ ^ 2 ^ a = 1 := by
    rw [hx₀, ← pow_mul, mul_comm, pow_mul, hm, pow_orderOf_eq_one]
  have hxo' : orderOf x₀ = 2 ^ a := by
    have h1 : orderOf x₀ ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hx₀2
    have h2 : orderOf (π x₀) ∣ orderOf x₀ := orderOf_map_dvd π x₀
    rw [hπx] at h2
    exact Nat.dvd_antisymm h1 h2
  set x : G := ((x₀ : M) : G) with hxdef
  have hxM : x ∈ M := (x₀ : M).2
  have hxo : orderOf x = 2 ^ a := by
    rw [hxdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hxo']
  have hxQ : orderOf (QuotientGroup.mk' H ⟨x, hxM⟩) = 2 ^ a := hπx
  have hlt : 2 ^ (a - 1) < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hyM : x ^ 2 ^ (a - 1) ∈ M := pow_mem hxM _
  have hy2 : orderOf (x ^ 2 ^ (a - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hxo]; exact pow_dvd_pow 2 (by omega)), hxo,
      Nat.pow_div (by omega) (by norm_num), Nat.sub_sub_self ha, pow_one]
  have e1 : (⟨x ^ 2 ^ (a - 1), hyM⟩ : M) = (x₀ : M) ^ 2 ^ (a - 1) :=
    Subtype.ext (by rw [SubgroupClass.coe_pow])
  have hyC : ρ ⟨x ^ 2 ^ (a - 1), hyM⟩ ∈ C := by
    rw [e1, map_pow]
    exact pow_mem (mem_comap.1 x₀.2) _
  have hyout : ρ ⟨x ^ 2 ^ (a - 1), hyM⟩ ∉ I := by
    intro hyI
    have h1 : QuotientGroup.mk' H (x₀ : M) ^ 2 ^ (a - 1) = 1 := by
      rw [← map_pow, ← e1, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hH, mem_comap]
      exact hyI
    have h3 : orderOf (QuotientGroup.mk' H (x₀ : M)) = 2 ^ a := hπx
    have h2 := Nat.le_of_dvd (by positivity) (h3 ▸ orderOf_dvd_of_pow_eq_one h1)
    omega
  exact exists_normal_index_two_of_unique_of_quotientSub H huniq hxM ha hxo hxQ hQ
    (hfus _ hyM hy2 hyout hyC)

include ρ in
theorem exists_normal_index_two_of_action_complement_of_isConj [Finite X]
    (hker : Odd (Nat.card ρ.ker)) {C : Subgroup (MulAut X)} [IsCyclic C]
    (hCInn : ∀ β ∈ C, β ∈ (MulAut.conj : X →* MulAut X).range → β = 1)
    (hNF : ∀ α : MulAut X, ∃ g : X, ∃ β ∈ C, α = MulAut.conj g * β)
    (hInn : ∀ g : X, ∃ m : M, ρ m = MulAut.conj g) {t : G} (htM : t ∈ M) (ht : orderOf t = 2)
    (hout : ρ ⟨t, htM⟩ ∉ (MulAut.conj : X →* MulAut X).range)
    (huniq : ∀ g : G, g⁻¹ * t * g ∈ M → g ∈ M)
    (hconj : ∃ φ : MulAut X, φ * ρ ⟨t, htM⟩ * φ⁻¹ ∈ C) :
    ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  obtain ⟨φ, hφC⟩ := hconj
  set τ := ρ ⟨t, htM⟩ with hτdef
  set ι := φ * τ * φ⁻¹ with hιdef
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hτ2 : τ ^ 2 = 1 := action_sq_eq_one ρ htM ht2
  have hι2 : ι ^ 2 = 1 := by rw [hιdef, conj_pow, hτ2, mul_one, mul_inv_cancel]
  have hτ1 : τ ≠ 1 := fun h => hout ⟨1, by rw [map_one, h]⟩
  have hι1 : ι ≠ 1 := by
    intro h
    apply hτ1
    have h1 : τ = φ⁻¹ * ι * φ := by rw [hιdef]; group
    rw [h1, h, mul_one, inv_mul_cancel]
  obtain ⟨g, β, hβ, hφg⟩ := hNF φ⁻¹
  have hcomm : β * ι = ι * β :=
    congrArg Subtype.val ((IsCyclic.commGroup (α := C)).mul_comm ⟨β, hβ⟩ ⟨ι, hφC⟩)
  have hτg : τ = MulAut.conj g * ι * (MulAut.conj g)⁻¹ := by
    calc τ = φ⁻¹ * ι * φ⁻¹⁻¹ := by rw [hιdef]; group
      _ = MulAut.conj g * (β * ι) * β⁻¹ * (MulAut.conj g)⁻¹ := by rw [hφg]; group
      _ = MulAut.conj g * ι * (MulAut.conj g)⁻¹ := by rw [hcomm]; group
  obtain ⟨c, hc⟩ := hInn g
  have hAs : ρ (c⁻¹ * ⟨t, htM⟩ * c) = ι := by
    rw [map_mul, map_mul, map_inv, hc, ← hτdef, hτg]
    group
  refine exists_normal_index_two_of_action_complement ρ hker hCInn hNF hInn htM ht hout huniq
    fun y hyM hy2 hyout hyC => ?_
  have hy2' : y ^ 2 = 1 := by rw [← hy2, pow_orderOf_eq_one]
  have hAy1 : ρ ⟨y, hyM⟩ ≠ 1 := fun h => hyout ⟨1, by rw [map_one, h]⟩
  have hAyι : ρ ⟨y, hyM⟩ = ι := by
    have h := eq_of_sq_eq_one_of_ne_one_of_isCyclic (C' := C) (u := ⟨_, hyC⟩) (z := ⟨ι, hφC⟩)
      (Subtype.ext (by rw [SubgroupClass.coe_pow]; exact action_sq_eq_one ρ hyM hy2'))
      (Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hι2))
      (fun h => hAy1 (congrArg Subtype.val h)) (fun h => hι1 (congrArg Subtype.val h))
    exact congrArg Subtype.val h
  set s : M := c⁻¹ * ⟨t, htM⟩ * c with hs
  have hs2 : (s : G) ^ 2 = 1 := by
    have e2 : (((c : M) : G)⁻¹ * t * (c : G)) ^ 2 = ((c : M) : G)⁻¹ * t ^ 2 * (c : G) := by
      rw [sq, sq]; group
    simp only [hs, coe_mul, coe_inv, e2, ht2, mul_one, inv_mul_cancel]
  have h1 : IsConj (s : G) y :=
    isConj_of_action_eq ρ hker s.2 hyM hs2 hy2' (by rw [Subtype.coe_eta, hAs, hAyι])
  have h2 : IsConj t (s : G) := by
    refine isConj_iff.2 ⟨((c : M) : G)⁻¹, ?_⟩
    simp only [hs, coe_mul, coe_inv, inv_inv]
  exact h2.trans h1

end Action

section Normalizer

variable {X : Type*} [Group X] {G₀ : Subgroup G}

theorem ker_normalizerMulAut (e : G₀ ≃* X) :
    (normalizerMulAut e).ker = (centralizer (G₀ : Set G)).subgroupOf (normalizer (G₀ : Set G)) := by
  rw [← normalizerMonoidHom_ker]
  ext n
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  change (MulAut.congr e) (G₀.normalizerMonoidHom n) = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]

theorem card_ker_normalizerMulAut (e : G₀ ≃* X) :
    Nat.card (normalizerMulAut e).ker = Nat.card (centralizer (G₀ : Set G)) := by
  rw [ker_normalizerMulAut]
  exact Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer _)).toEquiv

theorem exists_normalizerMulAut_eq_conj (e : G₀ ≃* X) (g : X) :
    ∃ m : normalizer (G₀ : Set G), normalizerMulAut e m = MulAut.conj g :=
  ⟨⟨(e.symm g : G), le_normalizer (e.symm g).2⟩, by
    rw [normalizerMulAut_of_mem e (e.symm g).2]
    exact congrArg MulAut.conj (e.apply_symm_apply g)⟩

theorem mem_of_normalizerMulAut_mem_range_of_odd (hZ : Odd (Nat.card (centralizer (G₀ : Set G))))
    (e : G₀ ≃* X) {y : G} (hyN : y ∈ normalizer (G₀ : Set G)) (hy2 : y ^ 2 = 1)
    (h : normalizerMulAut e ⟨y, hyN⟩ ∈ (MulAut.conj : X →* MulAut X).range) : y ∈ G₀ := by
  obtain ⟨g, hg⟩ := h
  set z : G := (e.symm g : G) with hzdef
  have hz : z ∈ G₀ := (e.symm g).2
  have hk : (⟨z, le_normalizer hz⟩ : normalizer (G₀ : Set G))⁻¹ * ⟨y, hyN⟩ ∈
      (normalizerMulAut e).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hg, normalizerMulAut_of_mem e hz]
    have : e ⟨z, hz⟩ = g := e.apply_symm_apply g
    rw [this, inv_mul_cancel]
  rw [ker_normalizerMulAut, mem_subgroupOf] at hk
  set u : G := z⁻¹ * y with hu
  have huC : u ∈ centralizer (G₀ : Set G) := by simpa [hu] using hk
  have hzu : z * u = u * z := (mem_centralizer_iff.1 huC z hz)
  have hyzu : y = z * u := by rw [hu, mul_inv_cancel_left]
  have hu2 : u ^ 2 = (z⁻¹) ^ 2 := by
    have h1 : z ^ 2 * u ^ 2 = 1 := by
      have e2 : y ^ 2 = z ^ 2 * u ^ 2 := by
        rw [hyzu, sq, sq, sq]
        calc z * u * (z * u) = z * (u * z) * u := by group
          _ = z * (z * u) * u := by rw [hzu]
          _ = z * z * (u * u) := by group
      rw [← e2, hy2]
    rw [inv_pow]
    exact eq_inv_of_mul_eq_one_right h1
  have hodd : Odd (orderOf u) :=
    Odd.of_dvd_nat hZ (Subgroup.orderOf_dvd_natCard _ huC)
  obtain ⟨j, hj⟩ := hodd
  have hu' : u = (u ^ 2) ^ (j + 1) := by
    rw [← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, ← hj,
      pow_orderOf_eq_one, one_mul]
  have huG : u ∈ G₀ := by
    rw [hu', hu2]
    exact pow_mem (pow_mem (inv_mem hz) 2) _
  rw [hyzu]
  exact mul_mem hz huG

theorem normalizerMulAut_not_mem_range_of_odd (hZ : Odd (Nat.card (centralizer (G₀ : Set G))))
    (e : G₀ ≃* X) {t : G} (htN : t ∈ normalizer (G₀ : Set G)) (ht2 : t ^ 2 = 1) (htG : t ∉ G₀) :
    normalizerMulAut e ⟨t, htN⟩ ∉ (MulAut.conj : X →* MulAut X).range :=
  fun h => htG (mem_of_normalizerMulAut_mem_range_of_odd hZ e htN ht2 h)

theorem two_lt_card_of_odd_centralizer [Finite G]
    (hZ : Odd (Nat.card (centralizer (G₀ : Set G)))) {t : G} (ht : orderOf t = 2)
    (htG : t ∉ G₀) : 2 < Nat.card G := by
  have hbot : G₀ ≠ ⊥ := by
    intro hG₀
    have htC : t ∈ centralizer (G₀ : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [hG₀, coe_bot, Set.mem_singleton_iff] at hh
      rw [hh, one_mul, mul_one]
    have h1 := Subgroup.orderOf_dvd_natCard _ htC
    rw [ht] at h1
    exact (Nat.not_even_iff_odd.2 hZ) (even_iff_two_dvd.2 h1)
  have h1 : 1 < Nat.card G₀ := (Subgroup.one_lt_card_iff_ne_bot _).2 hbot
  have h2 : 1 < G₀.index := Subgroup.one_lt_index_of_ne_top (fun h => htG (h ▸ mem_top t))
  rw [← G₀.card_mul_index]
  nlinarith

end Normalizer

theorem odd_card_centralizer_of_inf_eq_zpowers [Finite G] {L G₀ : Subgroup G} {t : G}
    (hKt : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t) (hLG₀ : L ≤ G₀)
    (ht : orderOf t = 2) (htN : t ∈ normalizer (G₀ : Set G))
    (htC : t ∉ centralizer (G₀ : Set G)) : Odd (Nat.card (centralizer (G₀ : Set G))) := by
  set Z := centralizer (G₀ : Set G) with hZdef
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← sq, ht2]
  have hmem : ∀ z ∈ Z, t * z * t⁻¹ ∈ Z := by
    intro z hz
    rw [hZdef, mem_centralizer_iff] at hz ⊢
    intro g hg
    have hg' : t⁻¹ * g * t ∈ G₀ := by
      have h1 := (mem_normalizer_iff.1 htN (t⁻¹ * g * t)).2
      apply h1
      simpa [mul_assoc] using hg
    have hc := hz _ hg'
    calc g * (t * z * t⁻¹) = t * ((t⁻¹ * g * t) * z) * t⁻¹ := by group
      _ = t * (z * (t⁻¹ * g * t)) * t⁻¹ := by rw [hc]
      _ = t * z * t⁻¹ * g := by group
  set φ : Z →* Z :=
    { toFun := fun z => ⟨t * z * t⁻¹, hmem z z.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [coe_mul]; group) } with hφ
  have hinv : Function.Involutive φ := fun z => Subtype.ext (by
    change t * (t * (z : G) * t⁻¹) * t⁻¹ = z
    rw [htinv]
    calc t * (t * (z : G) * t) * t = t ^ 2 * z * t ^ 2 := by simp only [sq, mul_assoc]
      _ = z := by rw [ht2, one_mul, mul_one])
  have hfpf : MonoidHom.FixedPointFree φ := by
    intro z hz
    have hz1 : t * (z : G) * t⁻¹ = z := congrArg Subtype.val hz
    have hzt : (z : G) ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc (z : G) * t = t * z * t⁻¹ * t := by rw [hz1]
        _ = t * z := by group
    have hzL : (z : G) ∈ centralizer (L : Set G) := centralizer_le hLG₀ z.2
    have hzK : (z : G) ∈ zpowers t := hKt ▸ mem_inf.2 ⟨hzL, hzt⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hzK
    rw [← zpow_mod_orderOf, ht, Nat.cast_ofNat] at hk
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · rw [h0, zpow_zero] at hk
      exact Subtype.ext hk.symm
    · rw [h1, zpow_one] at hk
      exact absurd (hk ▸ z.2) htC
  exact hfpf.odd_card_of_involutive hinv

end CFSG.SeitzReduction.EPilot
