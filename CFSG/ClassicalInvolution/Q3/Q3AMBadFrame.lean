module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadEdge
public import CFSG.ClassicalInvolution.Q3.Q3AMSyl
public import CFSG.ClassicalInvolution.Asc77.AscT7AHyp51

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Q3.Q3DB
open scoped commutatorElement MatrixGroups

section Quaternion

variable {X : Type} [Group X] [Finite X] {L R : Subgroup X} {z : X}

theorem exists_quaternion_pair_of_isSylow2In (h : IsClassicalMember3 L z) (hR : IsSylow2In R L)
    (hzR : z ∈ R) :
    ∃ x ∈ R, ∃ y ∈ R, x * x = z ∧ y * y = z ∧ x * y * x⁻¹ * y⁻¹ = z := by
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
      (QuotientGroup.mk' (classicalInvolutionOddCore L) z')).mp
      (Generic.orderOf_mk_oddCore_eq_two hz'2)
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
  let Q : Sylow 2 ↥L := AscL62.sylowOfIsSylow2In'' hR
  have hQR : (Q : Subgroup ↥L) = R.subgroupOf L := rfl
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
  have hQz : z' ∈ (Q : Subgroup L) := hzR
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
  have hyy : y * y = z' := heq _ ((Q : Subgroup L).mul_mem hyQ hyQ) (by
    rw [map_mul, hy]; decide +kernel)
  have hxy : x * y * x⁻¹ * y⁻¹ = z' := heq _ (by
      exact (Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem ((Q : Subgroup L).mul_mem hxQ hyQ)
        ((Q : Subgroup L).inv_mem hxQ)) ((Q : Subgroup L).inv_mem hyQ)) (by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hx, hy]; decide +kernel)
  refine ⟨x, hxQ, y, hyQ, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hxx
  · exact congrArg Subtype.val hyy
  · exact congrArg Subtype.val hxy

end Quaternion

section Triple

variable {G : Type} [Group G]

theorem mem_normalizer_oddCoreOf_of_conjSub_eq [Finite G] {x : G} {M : Subgroup G}
    (hx : conjSub x M = M) :
    x ∈ Subgroup.normalizer (oddCoreOf M : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  show conjSub x (oddCoreIn M) = oddCoreIn M
  rw [← Bootstrap.oddCoreIn_conjSub_eq, hx]

theorem conjSub_eq_of_mem_self {x : G} {M : Subgroup G} (hx : x ∈ M) : conjSub x M = M :=
  mem_normalizer_iff_conjSub_eq.mp (Subgroup.le_normalizer hx)

theorem conj_comm_of_comm {x h c : G} (hx : x * c = c * x) (hh : h * c = c * h) :
    (x * h * x⁻¹) * c = c * (x * h * x⁻¹) := by
  have hxc' : x⁻¹ * c = c * x⁻¹ := by
    calc x⁻¹ * c = x⁻¹ * (c * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * c) * x⁻¹ := by rw [hx]
      _ = c * x⁻¹ := by group
  calc x * h * x⁻¹ * c = x * h * (x⁻¹ * c) := by group
    _ = x * h * (c * x⁻¹) := by rw [hxc']
    _ = x * (h * c) * x⁻¹ := by group
    _ = x * (c * h) * x⁻¹ := by rw [hh]
    _ = (x * c) * h * x⁻¹ := by group
    _ = (c * x) * h * x⁻¹ := by rw [hx]
    _ = c * (x * h * x⁻¹) := by group

theorem mem_normalizer_inf_centralizer {H : Subgroup G} {x c : G}
    (hH : x ∈ Subgroup.normalizer (H : Set G)) (hc : x * c = c * x) :
    x ∈ Subgroup.normalizer ((H ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hH' := Subgroup.mem_normalizer_iff.mp hH h
  have hc' : x⁻¹ * c = c * x⁻¹ := by
    calc x⁻¹ * c = x⁻¹ * (c * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * c) * x⁻¹ := by rw [hc]
      _ = c * x⁻¹ := by group
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨hH'.mp h1, Subgroup.mem_centralizer_singleton_iff.mpr
      (conj_comm_of_comm hc (Subgroup.mem_centralizer_singleton_iff.mp h2))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨hH'.mpr h1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := conj_comm_of_comm hc' (Subgroup.mem_centralizer_singleton_iff.mp h2)
    have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
    rwa [e] at this

@[expose] def oddCentPart (M : Subgroup G) (c : G) : Subgroup G :=
  oddCoreOf M ⊓ Subgroup.centralizer ({c} : Set G)

theorem mem_oddCentPart_iff {M : Subgroup G} {c x : G} :
    x ∈ oddCentPart M c ↔ x ∈ oddCoreOf M ∧ x * c = c * x := by
  unfold oddCentPart
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem oddCentPart_le (M : Subgroup G) (c : G) : oddCentPart M c ≤ oddCoreOf M := inf_le_left

theorem oddCentPart_odd [Finite G] (M : Subgroup G) (c : G) :
    Odd (Nat.card ↥(oddCentPart M c)) :=
  (oddCoreOf_odd_natCard M).of_dvd_nat (Subgroup.card_dvd_of_le (oddCentPart_le M c))

theorem mem_normalizer_oddCentPart [Finite G] {M : Subgroup G} {x c : G}
    (hx : conjSub x M = M) (hc : x * c = c * x) :
    x ∈ Subgroup.normalizer (oddCentPart M c : Set G) :=
  mem_normalizer_inf_centralizer (mem_normalizer_oddCoreOf_of_conjSub_eq hx) hc

theorem commutator_mem_centralizer_singleton {x y c : G} (hx : x * c = c * x)
    (hy : y * c = c * y) : ⁅x, y⁆ ∈ Subgroup.centralizer ({c} : Set G) := by
  have hxm : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hx
  have hym : y ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hy
  rw [commutatorElement_def]
  exact (Subgroup.centralizer ({c} : Set G)).mul_mem
    ((Subgroup.centralizer ({c} : Set G)).mul_mem
      ((Subgroup.centralizer ({c} : Set G)).mul_mem hxm hym)
      ((Subgroup.centralizer ({c} : Set G)).inv_mem hxm))
    ((Subgroup.centralizer ({c} : Set G)).inv_mem hym)


variable [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G} {K₁ K₂ K₃ : Subgroup G}
  {z₁ z₂ z₃ : G}

theorem exists_commuting_sylow_triple
    (h12 : EdgeSetup K z K₁ K₂ z₁ z₂) (h13 : EdgeSetup K z K₁ K₃ z₁ z₃)
    (h23 : EdgeSetup K z K₂ K₃ z₂ z₃) (hz₃ : z₃ = z₁ * z₂)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hBelow : CIT3Below (Nat.card G)) :
    ∃ R₁ R₂ R₃ : Subgroup G, IsSylow2In R₁ K₁ ∧ IsSylow2In R₂ K₂ ∧ IsSylow2In R₃ K₃ ∧
      Nat.card R₁ = 8 ∧ Nat.card R₂ = 8 ∧ Nat.card R₃ = 8 ∧ z₁ ∈ R₁ ∧ z₂ ∈ R₂ ∧ z₃ ∈ R₃ ∧
      Commutes R₁ R₂ ∧ Commutes R₁ R₃ ∧ Commutes R₂ R₃ := by
  obtain ⟨R₂, R₁, hp⟩ := h12.exists_sylowPair
  obtain ⟨R₁', R₃₀, hq⟩ := h13.symm.exists_sylowPair
  have hK₁c : ∀ x ∈ K₁, x * z₁ = z₁ * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h12.invM.subnormal hx)
  have hK₂c : ∀ x ∈ K₂, x * z₂ = z₂ * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h12.invN.subnormal hx)
  have hK₃c : ∀ x ∈ K₃, x * z₃ = z₃ * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h13.invN.subnormal hx)
  have hz₂R₁ : ∀ x ∈ R₁, x * z₂ = z₂ * x := fun x hx => (hp.commutes z₂ hp.mem_t x hx).symm
  have hz₁R₂ : ∀ x ∈ R₂, x * z₁ = z₁ * x := fun x hx => hp.commutes x hx z₁ hp.mem_a
  have hz₁R₃ : ∀ b ∈ R₃₀, b * z₁ = z₁ * b := fun b hb => (hq.commutes z₁ hq.mem_t b hb).symm
  have hR₁z₃ : ∀ x ∈ R₁, x * z₃ = z₃ * x := fun x hx => by
    rw [hz₃]
    calc x * (z₁ * z₂) = (x * z₁) * z₂ := by group
      _ = (z₁ * x) * z₂ := by rw [hK₁c x (hp.syl_R'.1 hx)]
      _ = z₁ * (x * z₂) := by group
      _ = z₁ * (z₂ * x) := by rw [hz₂R₁ x hx]
      _ = z₁ * z₂ * x := by group
  have hR₂z₃ : ∀ x ∈ R₂, x * z₃ = z₃ * x := fun x hx => by
    rw [hz₃]
    calc x * (z₁ * z₂) = (x * z₁) * z₂ := by group
      _ = (z₁ * x) * z₂ := by rw [hz₁R₂ x hx]
      _ = z₁ * (x * z₂) := by group
      _ = z₁ * (z₂ * x) := by rw [hK₂c x (hp.syl_R.1 hx)]
      _ = z₁ * z₂ * x := by group
  have hR₁M : ∀ x ∈ R₁, x ∈ K₁ ⊓ Subgroup.centralizer ({z₃} : Set G) := fun x hx =>
    ⟨hp.syl_R'.1 hx, Subgroup.mem_centralizer_singleton_iff.mpr (hR₁z₃ x hx)⟩
  have hR₂M : ∀ x ∈ R₂, x ∈ K₂ ⊓ Subgroup.centralizer ({z₃} : Set G) := fun x hx =>
    ⟨hp.syl_R.1 hx, Subgroup.mem_centralizer_singleton_iff.mpr (hR₂z₃ x hx)⟩
  have hR₁N : ∀ x ∈ R₁, conjSub x K₃ = K₃ := fun x hx =>
    h13.conjSub_eq_of_mem_centM hnab hBelow x (hR₁M x hx)
  have hR₂N : ∀ x ∈ R₂, conjSub x K₃ = K₃ := fun x hx =>
    h23.conjSub_eq_of_mem_centM hnab hBelow x (hR₂M x hx)
  have hR₁D : ∀ x ∈ R₁, x ∈ Subgroup.normalizer (oddCentPart K₃ z₁ : Set G) := fun x hx =>
    mem_normalizer_oddCentPart (hR₁N x hx) (hK₁c x (hp.syl_R'.1 hx))
  have hR₂D : ∀ x ∈ R₂, x ∈ Subgroup.normalizer (oddCentPart K₃ z₁ : Set G) := fun x hx =>
    mem_normalizer_oddCentPart (hR₂N x hx) (hz₁R₂ x hx)
  have hR₃D : ∀ b ∈ R₃₀, b ∈ Subgroup.normalizer (oddCentPart K₃ z₁ : Set G) := fun b hb =>
    mem_normalizer_oddCentPart (conjSub_eq_of_mem_self (hq.syl_R'.1 hb)) (hz₁R₃ b hb)
  have hAN : R₂ ⊔ R₁ ≤ Subgroup.normalizer (oddCentPart K₃ z₁ : Set G) := sup_le hR₂D hR₁D
  have hc₁ : ∀ x ∈ R₁, ∀ b ∈ R₃₀, ⁅x, b⁆ ∈ oddCentPart K₃ z₁ := fun x hx b hb =>
    mem_oddCentPart_iff.mpr
      ⟨h13.commutator_centM_le_oddCore hnab hBelow x (hR₁M x hx) b (hq.syl_R'.1 hb),
        Subgroup.mem_centralizer_singleton_iff.mp
          (commutator_mem_centralizer_singleton (hK₁c x (hp.syl_R'.1 hx)) (hz₁R₃ b hb))⟩
  have hc₂ : ∀ x ∈ R₂, ∀ b ∈ R₃₀, ⁅x, b⁆ ∈ oddCentPart K₃ z₁ := fun x hx b hb =>
    mem_oddCentPart_iff.mpr
      ⟨h23.commutator_centM_le_oddCore hnab hBelow x (hR₂M x hx) b (hq.syl_R'.1 hb),
        Subgroup.mem_centralizer_singleton_iff.mp
          (commutator_mem_centralizer_singleton (hz₁R₂ x hx) (hz₁R₃ b hb))⟩
  have hAB : ∀ a ∈ R₂ ⊔ R₁, ∀ b ∈ R₃₀, ⁅a, b⁆ ∈ oddCentPart K₃ z₁ := by
    intro a ha b hb
    obtain ⟨r₂, hr₂, r₁, hr₁, rfl⟩ := badEdge_exists_mul_of_mem_sup hp.commutes ha
    have e : ⁅r₂ * r₁, b⁆ = r₂ * ⁅r₁, b⁆ * r₂⁻¹ * ⁅r₂, b⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (oddCentPart K₃ z₁).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hR₂D r₂ hr₂) _).mp (hc₁ r₁ hr₁ b hb)) (hc₂ r₂ hr₂ b hb)
  obtain ⟨p, hpD, hpc⟩ := exists_conj_commutes_of_commutator_mem hp.isPGroup_sup
    hq.syl_R'.2.1 (oddCentPart_odd K₃ z₁) hAN hR₃D hAB
  have hpK₃ : p ∈ K₃ := oddCoreIn_le K₃ (oddCentPart_le K₃ z₁ hpD)
  have hKp : conjSub p K₃ = K₃ := conjSub_eq_of_mem_self hpK₃
  have hsyl : IsSylow2In (conjSub p R₃₀) K₃ := by
    have := hq.syl_R'.conj p
    rwa [hKp] at this
  have hcard : Nat.card (conjSub p R₃₀) = 8 := by
    have : Nat.card ↥(conjSub p R₃₀) = Nat.card ↥R₃₀ :=
      (Nat.card_congr (Subgroup.equivMapOfInjective R₃₀ (MulAut.conj p).toMonoidHom
        (MulAut.conj p).injective).toEquiv).symm
    rw [this]
    exact hq.card_R'
  have hz₃R : z₃ ∈ conjSub p R₃₀ := by
    rw [mem_conjSub_iff]
    have : p⁻¹ * z₃ * p = z₃ := by
      have h1 := hK₃c p hpK₃
      calc p⁻¹ * z₃ * p = p⁻¹ * (z₃ * p) := by group
        _ = p⁻¹ * (p * z₃) := by rw [h1]
        _ = z₃ := by group
    rw [this]
    exact hq.mem_a
  have hcomm : ∀ a ∈ R₂ ⊔ R₁, ∀ y ∈ conjSub p R₃₀, a * y = y * a := by
    intro a ha y hy
    rw [mem_conjSub_iff] at hy
    have e : y = p * (p⁻¹ * y * p) * p⁻¹ := by group
    rw [e]
    exact hpc a ha _ hy
  exact ⟨R₁, R₂, conjSub p R₃₀, hp.syl_R', hp.syl_R, hsyl, hp.card_R', hp.card_R, hcard,
    hp.mem_a, hp.mem_t, hz₃R, fun x hx y hy => (hp.commutes y hy x hx).symm,
    fun a ha y hy => hcomm a (Subgroup.mem_sup_right ha) y hy,
    fun a ha y hy => hcomm a (Subgroup.mem_sup_left ha) y hy⟩

end Triple

section Axis

variable {G : Type} [Group G]

structure BadAxis (K₁ K₂ K₃ : Subgroup G) (z₁ z₂ t₁ t₂ t₃ : G) (R₁ R₂ R₃ : Subgroup G) : Prop where
  uniq₁ : IsUniqueInvolution K₁ z₁
  uniq₂ : IsUniqueInvolution K₂ z₂
  uniq₃ : IsUniqueInvolution K₃ (z₁ * z₂)
  ne : z₁ ≠ z₂
  syl₁ : IsSylow2In R₁ K₁
  syl₂ : IsSylow2In R₂ K₂
  syl₃ : IsSylow2In R₃ K₃
  z_mem₁ : z₁ ∈ R₁
  z_mem₂ : z₂ ∈ R₂
  z_mem₃ : z₁ * z₂ ∈ R₃
  comm₁₂ : Commutes R₁ R₂
  comm₁₃ : Commutes R₁ R₃
  comm₂₃ : Commutes R₂ R₃
  mem₁ : t₁ ∈ R₁
  mem₂ : t₂ ∈ R₂
  mem₃ : t₃ ∈ R₃
  sq₁ : t₁ * t₁ = z₁
  sq₂ : t₂ * t₂ = z₂
  sq₃ : t₃ * t₃ = z₁ * z₂
  noncomm₁ : ∃ u ∈ R₁, t₁ * u ≠ u * t₁
  noncomm₂ : ∃ u ∈ R₂, t₂ * u ≠ u * t₂
  noncomm₃ : ∃ u ∈ R₃, t₃ * u ≠ u * t₃

theorem isUniqueInvolution_comm {K : Subgroup G} {z u : G} (h : IsUniqueInvolution K z)
    (hu : u ∈ K) : u * z = z * u := by
  have hy : u * z * u⁻¹ ∈ K := K.mul_mem (K.mul_mem hu h.mem) (K.inv_mem hu)
  have hy2 : (u * z * u⁻¹) * (u * z * u⁻¹) = 1 := by
    calc (u * z * u⁻¹) * (u * z * u⁻¹) = u * (z * z) * u⁻¹ := by group
      _ = 1 := by rw [h.sq]; group
  rcases h.unique _ hy hy2 with h1 | h1
  · exfalso
    apply h.ne_one
    have e : z = u⁻¹ * (u * z * u⁻¹) * u := by group
    rw [e, h1]
    group
  · calc u * z = (u * z * u⁻¹) * u := by group
      _ = z * u := by rw [h1]

namespace BadAxis

variable {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ t₁ t₂ t₃ : G} {R₁ R₂ R₃ : Subgroup G}
  (h : BadAxis K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ R₁ R₂ R₃)

include h

theorem z_comm : z₁ * z₂ = z₂ * z₁ := h.comm₁₂ z₁ h.z_mem₁ z₂ h.z_mem₂

theorem z₁_sq : z₁ * z₁ = 1 := h.uniq₁.sq

theorem z₂_sq : z₂ * z₂ = 1 := h.uniq₂.sq

theorem s_mul_self : (t₁ * t₂ * t₃) * (t₁ * t₂ * t₃) = 1 := by
  have c12 : Commute t₁ t₂ := h.comm₁₂ t₁ h.mem₁ t₂ h.mem₂
  have c13 : Commute t₁ t₃ := h.comm₁₃ t₁ h.mem₁ t₃ h.mem₃
  have c23 : Commute t₂ t₃ := h.comm₂₃ t₂ h.mem₂ t₃ h.mem₃
  have hc : Commute (t₁ * t₂) t₃ := c13.mul_left c23
  have e : (t₁ * t₂ * t₃) ^ 2 = t₁ ^ 2 * t₂ ^ 2 * t₃ ^ 2 := by
    rw [Commute.mul_pow hc, Commute.mul_pow c12]
  rw [← pow_two, e, pow_two t₁, pow_two t₂, pow_two t₃, h.sq₁, h.sq₂, h.sq₃]
  calc z₁ * z₂ * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
    _ = z₁ * (z₁ * z₂) * z₂ := by rw [← h.z_comm]
    _ = (z₁ * z₁) * (z₂ * z₂) := by group
    _ = 1 := by rw [h.z₁_sq, h.z₂_sq, one_mul]

theorem s_comm₁ : Commute z₁ (t₁ * t₂ * t₃) := by
  have c11 : Commute z₁ t₁ := by
    show z₁ * t₁ = t₁ * z₁
    rw [← h.sq₁]
    group
  have c12 : Commute z₁ t₂ := h.comm₁₂ z₁ h.z_mem₁ t₂ h.mem₂
  have c13 : Commute z₁ t₃ := h.comm₁₃ z₁ h.z_mem₁ t₃ h.mem₃
  exact (c11.mul_right c12).mul_right c13

theorem s_comm₂ : Commute z₂ (t₁ * t₂ * t₃) := by
  have c21 : Commute z₂ t₁ := (h.comm₁₂ t₁ h.mem₁ z₂ h.z_mem₂).symm
  have c22 : Commute z₂ t₂ := by
    show z₂ * t₂ = t₂ * z₂
    rw [← h.sq₂]
    group
  have c23 : Commute z₂ t₃ := h.comm₂₃ z₂ h.z_mem₂ t₃ h.mem₃
  exact (c21.mul_right c22).mul_right c23

theorem s_not_mem_pair : t₁ * t₂ * t₃ ∉ Subgroup.closure ({z₁, z₂} : Set G) := by
  intro hs
  obtain ⟨u, hu, hne⟩ := h.noncomm₃
  have hz₁u : u ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm₁₃ z₁ h.z_mem₁ u hu).symm
  have hz₂u : u ∈ Subgroup.centralizer ({z₂} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.comm₂₃ z₂ h.z_mem₂ u hu).symm
  have hcl : Subgroup.closure ({z₁, z₂} : Set G) ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (h.comm₁₃ _ h.z_mem₁ u hu)
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h.comm₂₃ _ h.z_mem₂ u hu)
  have hsu : (t₁ * t₂ * t₃) * u = u * (t₁ * t₂ * t₃) :=
    Subgroup.mem_centralizer_singleton_iff.mp (hcl hs)
  have c1 : Commute u t₁ := (h.comm₁₃ t₁ h.mem₁ u hu).symm
  have c2 : Commute u t₂ := (h.comm₂₃ t₂ h.mem₂ u hu).symm
  have c12 : Commute u (t₁ * t₂) := c1.mul_right c2
  have cs : Commute u (t₁ * t₂ * t₃) := (hsu.symm : u * (t₁ * t₂ * t₃) = (t₁ * t₂ * t₃) * u)
  have e : t₃ = (t₁ * t₂)⁻¹ * (t₁ * t₂ * t₃) := by group
  have c3 : Commute u t₃ := by
    rw [e]
    exact c12.inv_right.mul_right cs
  exact hne c3.eq.symm

theorem isElemAbelian_axis :
    IsElemAbelian 2 (Subgroup.closure (insert (t₁ * t₂ * t₃) ({z₁, z₂} : Set G))) := by
  have hs1 := h.s_comm₁
  have hs2 := h.s_comm₂
  refine Theorem5.isElemAbelian_closure_of_commuting_involutions ?_ ?_
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx
    · rw [hx]
      exact h.s_mul_self
    · rw [hx]
      exact h.z₁_sq
    · rw [hx]
      exact h.z₂_sq
  · intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy <;> rw [hx, hy] <;>
      first
        | rfl
        | exact hs1.eq
        | exact hs1.symm.eq
        | exact hs2.eq
        | exact hs2.symm.eq
        | exact h.z_comm
        | exact h.z_comm.symm

theorem card_axis [Finite G] :
    Nat.card (Subgroup.closure (insert (t₁ * t₂ * t₃) ({z₁, z₂} : Set G))) = 8 := by
  have hB : Nat.card (Subgroup.closure ({z₁, z₂} : Set G)) = 4 := by
    have := (T7A.isElemAbelian2_closure_pair h.z₁_sq h.z₂_sq h.uniq₁.ne_one h.uniq₂.ne_one h.ne
      h.z_comm).1
    simpa using this
  have hs1 := h.s_comm₁
  have hs2 := h.s_comm₂
  have hscomm : ∀ x ∈ ({z₁, z₂} : Set G), (t₁ * t₂ * t₃) * x = x * (t₁ * t₂ * t₃) := by
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact hs1.symm.eq
    · rw [Set.mem_singleton_iff.mp hx]
      exact hs2.symm.eq
  have hle : Nat.card (Subgroup.closure (insert (t₁ * t₂ * t₃) ({z₁, z₂} : Set G))) ≤ 8 := by
    have := Theorem5.card_closure_insert_le h.s_mul_self hscomm
    rw [hB] at this
    exact this
  have hBA : Subgroup.closure ({z₁, z₂} : Set G) ≤
      Subgroup.closure (insert (t₁ * t₂ * t₃) ({z₁, z₂} : Set G)) :=
    Subgroup.closure_mono (Set.subset_insert _ _)
  have hdvd : 4 ∣ Nat.card (Subgroup.closure (insert (t₁ * t₂ * t₃) ({z₁, z₂} : Set G))) :=
    hB ▸ Subgroup.card_dvd_of_le hBA
  have hpos : 0 < Nat.card (Subgroup.closure (insert (t₁ * t₂ * t₃) ({z₁, z₂} : Set G))) :=
    Nat.card_pos
  by_contra h8
  have h4 : Nat.card (Subgroup.closure (insert (t₁ * t₂ * t₃) ({z₁, z₂} : Set G))) = 4 := by
    omega
  have hEq := Subgroup.eq_of_le_of_card_ge hBA (by omega)
  exact h.s_not_mem_pair (hEq ▸ Subgroup.subset_closure (Set.mem_insert _ _))

theorem flip₁ : BadAxis K₁ K₂ K₃ z₁ z₂ (t₁ * z₁) t₂ t₃ R₁ R₂ R₃ :=
  { h with
    mem₁ := R₁.mul_mem h.mem₁ h.z_mem₁
    sq₁ := by
      have c : z₁ * t₁ = t₁ * z₁ := by
        rw [← h.sq₁]
        group
      calc t₁ * z₁ * (t₁ * z₁) = t₁ * (z₁ * t₁) * z₁ := by group
        _ = t₁ * (t₁ * z₁) * z₁ := by rw [c]
        _ = (t₁ * t₁) * (z₁ * z₁) := by group
        _ = z₁ := by rw [h.sq₁, h.z₁_sq, mul_one]
    noncomm₁ := by
      obtain ⟨u, hu, hne⟩ := h.noncomm₁
      refine ⟨u, hu, fun heq => hne ?_⟩
      have hc : u * z₁ = z₁ * u := isUniqueInvolution_comm h.uniq₁ (h.syl₁.1 hu)
      have e1 : t₁ * u * z₁ = u * t₁ * z₁ := by
        calc t₁ * u * z₁ = t₁ * (u * z₁) := by group
          _ = t₁ * (z₁ * u) := by rw [hc]
          _ = t₁ * z₁ * u := by group
          _ = u * (t₁ * z₁) := heq
          _ = u * t₁ * z₁ := by group
      exact mul_right_cancel e1 }

theorem flip₂ : BadAxis K₁ K₂ K₃ z₁ z₂ t₁ (t₂ * z₂) t₃ R₁ R₂ R₃ :=
  { h with
    mem₂ := R₂.mul_mem h.mem₂ h.z_mem₂
    sq₂ := by
      have c : z₂ * t₂ = t₂ * z₂ := by
        rw [← h.sq₂]
        group
      calc t₂ * z₂ * (t₂ * z₂) = t₂ * (z₂ * t₂) * z₂ := by group
        _ = t₂ * (t₂ * z₂) * z₂ := by rw [c]
        _ = (t₂ * t₂) * (z₂ * z₂) := by group
        _ = z₂ := by rw [h.sq₂, h.z₂_sq, mul_one]
    noncomm₂ := by
      obtain ⟨u, hu, hne⟩ := h.noncomm₂
      refine ⟨u, hu, fun heq => hne ?_⟩
      have hc : u * z₂ = z₂ * u := isUniqueInvolution_comm h.uniq₂ (h.syl₂.1 hu)
      have e1 : t₂ * u * z₂ = u * t₂ * z₂ := by
        calc t₂ * u * z₂ = t₂ * (u * z₂) := by group
          _ = t₂ * (z₂ * u) := by rw [hc]
          _ = t₂ * z₂ * u := by group
          _ = u * (t₂ * z₂) := heq
          _ = u * t₂ * z₂ := by group
      exact mul_right_cancel e1 }

theorem flip₃ : BadAxis K₁ K₂ K₃ z₁ z₂ t₁ t₂ (t₃ * (z₁ * z₂)) R₁ R₂ R₃ :=
  { h with
    mem₃ := R₃.mul_mem h.mem₃ h.z_mem₃
    sq₃ := by
      have c : (z₁ * z₂) * t₃ = t₃ * (z₁ * z₂) := by
        rw [← h.sq₃]
        group
      calc t₃ * (z₁ * z₂) * (t₃ * (z₁ * z₂)) = t₃ * ((z₁ * z₂) * t₃) * (z₁ * z₂) := by group
        _ = t₃ * (t₃ * (z₁ * z₂)) * (z₁ * z₂) := by rw [c]
        _ = (t₃ * t₃) * ((z₁ * z₂) * (z₁ * z₂)) := by group
        _ = z₁ * z₂ := by rw [h.sq₃, h.uniq₃.sq, mul_one]
    noncomm₃ := by
      obtain ⟨u, hu, hne⟩ := h.noncomm₃
      refine ⟨u, hu, fun heq => hne ?_⟩
      have hc : u * (z₁ * z₂) = (z₁ * z₂) * u := isUniqueInvolution_comm h.uniq₃ (h.syl₃.1 hu)
      have e1 : t₃ * u * (z₁ * z₂) = u * t₃ * (z₁ * z₂) := by
        calc t₃ * u * (z₁ * z₂) = t₃ * (u * (z₁ * z₂)) := by group
          _ = t₃ * ((z₁ * z₂) * u) := by rw [hc]
          _ = t₃ * (z₁ * z₂) * u := by group
          _ = u * (t₃ * (z₁ * z₂)) := heq
          _ = u * t₃ * (z₁ * z₂) := by group
      exact mul_right_cancel e1 }

end BadAxis

variable {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ z₃ : G}

section Existence

variable [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}


theorem exists_badAxis
    (h12 : EdgeSetup K z K₁ K₂ z₁ z₂) (h13 : EdgeSetup K z K₁ K₃ z₁ z₃)
    (h23 : EdgeSetup K z K₂ K₃ z₂ z₃) (hz₃ : z₃ = z₁ * z₂)
    (hnab : ∃ x y : G, x * y ≠ y * x) (hBelow : CIT3Below (Nat.card G)) :
    ∃ (t₁ t₂ t₃ : G) (R₁ R₂ R₃ : Subgroup G),
      BadAxis K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ R₁ R₂ R₃ := by
  obtain ⟨R₁, R₂, R₃, hs₁, hs₂, hs₃, -, -, -, hz₁R, hz₂R, hz₃R, c12, c13, c23⟩ :=
    exists_commuting_sylow_triple h12 h13 h23 hz₃ hnab hBelow
  obtain ⟨t₁, ht₁, u₁, hu₁, hq₁, -, hc₁⟩ :=
    exists_quaternion_pair_of_isSylow2In h12.invM hs₁ hz₁R
  obtain ⟨t₂, ht₂, u₂, hu₂, hq₂, -, hc₂⟩ :=
    exists_quaternion_pair_of_isSylow2In h12.invN hs₂ hz₂R
  obtain ⟨t₃, ht₃, u₃, hu₃, hq₃, -, hc₃⟩ :=
    exists_quaternion_pair_of_isSylow2In h13.invN hs₃ hz₃R
  have nc : ∀ {t u z' : G}, z' ≠ 1 → t * u * t⁻¹ * u⁻¹ = z' → t * u ≠ u * t := by
    intro t u z' hz' hc heq
    apply hz'
    rw [← hc, heq]
    group
  subst hz₃
  exact ⟨t₁, t₂, t₃, R₁, R₂, R₃,
    { uniq₁ := h12.uniqueM
      uniq₂ := h12.uniqueN
      uniq₃ := h13.uniqueN
      ne := h12.ne
      syl₁ := hs₁
      syl₂ := hs₂
      syl₃ := hs₃
      z_mem₁ := hz₁R
      z_mem₂ := hz₂R
      z_mem₃ := hz₃R
      comm₁₂ := c12
      comm₁₃ := c13
      comm₂₃ := c23
      mem₁ := ht₁
      mem₂ := ht₂
      mem₃ := ht₃
      sq₁ := hq₁
      sq₂ := hq₂
      sq₃ := hq₃
      noncomm₁ := ⟨u₁, hu₁, nc h12.uniqueM.ne_one hc₁⟩
      noncomm₂ := ⟨u₂, hu₂, nc h12.uniqueN.ne_one hc₂⟩
      noncomm₃ := ⟨u₃, hu₃, nc h13.uniqueN.ne_one hc₃⟩ }⟩

end Existence

end Axis

end CFSG.ClassicalInvolution.Q3.Q3AM
