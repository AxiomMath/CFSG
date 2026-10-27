module

public import CFSG.GH74.Uniqueness.Bender.Dickson
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineTorusCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddPrimeInvertersLinear

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

section Model

open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism

theorem BenderType.exists_subline_unitary {K : Type*} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) :
    ∃ J₀ Q₀ : Subgroup K, Nonempty (J₀ ≃* CFSG.Theory.Comparator.PSL2Model n) ∧ Q₀ ≤ J₀ ∧
      Nat.card Q₀ = 2 ^ n ∧ (∀ x ∈ Q₀, ∀ y ∈ Q₀, x * y = y * x) ∧ (∀ x ∈ Q₀, x * x = 1) := by
  obtain ⟨hn, ⟨ε⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSU3Model n) := by
    cases h with
    | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
  obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, ⟨e'⟩⟩ := exists_psu3_concrete hn
  have : Fintype E := Fintype.ofFinite E
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, ← pow_mul] using hcard)
  have hnormal : (scalarCenter J).Normal :=
    Subgroup.normal_of_le_center (scalarCenter_le_center J)
  have hmain := unitary_central_cover_subline_torus_centralizer J n hn hcard hfixed hJ
    (scalarCenter J) le_rfl
  obtain ⟨-, -, -, hk0, -, ⟨hSL⟩, -, -, -, -, -, -, -, -, -, hQ0⟩ := hmain
  have hsurj := coverToPSU_surjective hJ (le_refl (scalarCenter J))
  have hinj : Function.Injective (coverToPSU J (scalarCenter J) hJ le_rfl) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rw [coverToPSU_mk] at hx
    have : g ∈ scalarCenter J := by rw [scalarCenter_eq_ker J hJ]; exact hx
    exact (QuotientGroup.eq_one_iff g).mpr this
  let ψ := MulEquiv.ofBijective (coverToPSU J (scalarCenter J) hJ le_rfl) ⟨hinj, hsurj⟩
  let θ : (J.specialSubgroup ⧸ scalarCenter J) ≃* K := ψ.trans (e'.symm.trans ε.symm)
  have hcomm : ∀ x ∈ upperRootL J (scalarCenter J) hJ, ∀ y ∈ upperRootL J (scalarCenter J) hJ,
      x * y = y * x := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hsq : ∀ x ∈ upperRootL J (scalarCenter J) hJ, x * x = 1 := by
    rintro _ ⟨s, rfl⟩
    rw [← map_mul]
    have : s * s = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      exact CharTwo.add_self_eq_zero _
    rw [this, map_one]
  refine ⟨(sublineL J (scalarCenter J) hJ).map θ.toMonoidHom,
    (upperRootL J (scalarCenter J) hJ).map θ.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨((Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective).symm.trans
      (((sublineEquiv hJ le_rfl).symm).trans ?_))⟩
    exact CFSG.ShultStronglyClosedTI.OddPrimeInverters.sl2EquivPSL2Binary (by omega) hk0
  · exact Subgroup.map_mono (upperRootL_le_sublineL hJ)
  · rw [Subgroup.card_map_of_injective θ.injective, hQ0]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hsq x hx, map_one]

end Model

section Helpers

variable {K : Type*} [Group K]

theorem isPGroup_two_of_mul_self_eq_one {A : Subgroup K} (hA : ∀ x ∈ A, x * x = 1) :
    IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa [sq] using hA g g.2)⟩

theorem exists_sylow_eq_subgroupOf
    {n : ℕ} [Finite K] {J Z : Subgroup K} (hZJ : Z ≤ J)
    (hZ : ∀ x ∈ Z, x * x = 1) (hZcard : Nat.card Z = 2 ^ n) (hJ : BenderType J n 1 1) :
    ∃ S : Sylow 2 J, (S : Subgroup J) = Z.subgroupOf J := by
  have hZ2 : IsPGroup 2 (Z.subgroupOf J) :=
    isPGroup_two_of_mul_self_eq_one (fun x hx => Subtype.ext (hZ x hx))
  obtain ⟨S, hS⟩ := hZ2.exists_le_sylow
  obtain ⟨t₂, hc₂⟩ := hJ.exists_benderCore S
  refine ⟨S, (Subgroup.eq_of_le_of_card_ge hS ?_).symm⟩
  rw [hc₂.card_eq, pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZJ).toEquiv, hZcard]

theorem BenderCore.normalizer_rootCenter_le [Finite K] {q i e : ℕ} {P : Subgroup K} {t : K}
    (hc : BenderCore q i e P t) : normalizer (rootCenter P : Set K) ≤ borel P := by
  obtain ⟨z, hz, hz1⟩ := hc.exists_involution
  refine IsStronglyEmbedded.normalizer_le hc.strong (le_trans (rootCenter_le P) (le_borel P))
    (isPGroup_two_of_mul_self_eq_one (fun x hx => hc.center_sq x hx)) ?_
  intro hbot
  rw [hbot] at hz
  exact hz1 (Subgroup.mem_bot.mp hz)

end Helpers

section Main

open CFSG.BenderSuzuki

theorem mem_borel_iff {K : Type*} [Group K] {P : Subgroup K} {x : K} :
    x ∈ borel P ↔ ∀ y, y ∈ P ↔ x * y * x⁻¹ ∈ P :=
  Subgroup.mem_normalizer_iff

theorem mem_rootCenter_conj_iff {K : Type*} [Group K] {P : Subgroup K} {d : K} (hd : d ∈ borel P)
    (x : K) : x ∈ rootCenter P ↔ d * x * d⁻¹ ∈ rootCenter P := by
  constructor
  · exact fun hx => conj_mem_rootCenter hd hx
  · intro hx
    have := conj_mem_rootCenter ((borel P).inv_mem hd) hx
    simpa [mul_assoc] using this

theorem BenderType.lemma_3_2_h_unitary
    {K : Type*} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) {z : K} (hz : z ∈ rootCenter (Q : Subgroup K))
    (hz1 : z ≠ 1) :
    Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ =
        rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t ∧
      Nonempty (↥(rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t) ≃* PSL2Model n) := by
  have hc := h.benderCore Q ht htQ
  have hn2 : 2 ≤ n := h.two_le.2
  set Z := rootCenter (Q : Subgroup K) with hZdef
  have hZsq : ∀ x ∈ Z, x * x = 1 := fun x hx => hc.center_sq x hx
  have hZcard : Nat.card Z = 2 ^ n := hc.card_center
  obtain ⟨J₁, hZJ₁, ⟨φ₁⟩⟩ : ∃ J₁ : Subgroup K, Z ≤ J₁ ∧ Nonempty (↥J₁ ≃* PSL2Model n) := by
    obtain ⟨J₀, Q₀, ⟨φ₀⟩, hQ₀J₀, hQ₀card, -, hQ₀sq⟩ := h.exists_subline_unitary
    have hQ₀2 : IsPGroup 2 Q₀ := isPGroup_two_of_mul_self_eq_one hQ₀sq
    obtain ⟨Q₁, hQ₁⟩ := hQ₀2.exists_le_sylow
    obtain ⟨t₁, hc₁⟩ := h.exists_benderCore Q₁
    have hQ₀Z₁ : Q₀ ≤ rootCenter (Q₁ : Subgroup K) := hc₁.elemAbelian_le_rootCenter hQ₁ hQ₀sq
    have hQ₀eq : Q₀ = rootCenter (Q₁ : Subgroup K) :=
      Subgroup.eq_of_le_of_card_ge hQ₀Z₁ (by rw [hQ₀card, hc₁.card_center])
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Q₁ Q
    have hU : (Q₁ : Subgroup K).map (MulAut.conj g).toMonoidHom =
        ((g • Q₁ : Sylow 2 K) : Subgroup K) := by
      ext x
      rw [Subgroup.mem_map_equiv, Sylow.coe_subgroup_smul,
        Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      rfl
    have hZeq : Z = Q₀.map (MulAut.conj g).toMonoidHom := by
      rw [hZdef, ← hg, ← hU, rootCenter_map, hQ₀eq]
    refine ⟨J₀.map (MulAut.conj g).toMonoidHom, ?_, ⟨?_⟩⟩
    · rw [hZeq]
      exact Subgroup.map_mono hQ₀J₀
    · exact (Subgroup.equivMapOfInjective J₀ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm.trans φ₀
  have hJ₁ : BenderType J₁ n 1 1 := BenderType.linear n hn2 φ₁
  have : IsSimpleGroup J₁ := hJ₁.isSimple
  obtain ⟨S₁, hS₁⟩ := exists_sylow_eq_subgroupOf hZJ₁ hZsq hZcard hJ₁
  obtain ⟨t₂, hc₂⟩ := hJ₁.exists_benderCore S₁
  have ht₂sq : (t₂ : K) * t₂ = 1 := congrArg Subtype.val hc₂.sq_eq_one
  have ht₂Q : (t₂ : K) ∉ borel (Q : Subgroup K) := by
    intro hmem
    apply hc₂.not_mem
    rw [mem_borel_iff]
    intro x
    have h1 := mem_rootCenter_conj_iff hmem (x : K)
    rw [hS₁]
    change (x : K) ∈ Z ↔ ((t₂ * x * t₂⁻¹ : J₁) : K) ∈ Z
    exact h1
  have hsup := hc₂.sup_zpowers_eq_top hc₂.not_mem
  have hJ₁eq : Z ⊔ Subgroup.zpowers (t₂ : K) = J₁ := by
    have := congrArg (Subgroup.map J₁.subtype) hsup
    rw [Subgroup.map_sup, hS₁, Subgroup.map_subgroupOf_eq_of_le hZJ₁, MonoidHom.map_zpowers,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
    exact this
  obtain ⟨m, hmM, hmt⟩ := hc.exists_conj_eq ht₂sq ht₂Q
  have hZm : Z.map (MulAut.conj m⁻¹).toMonoidHom = Z := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply, inv_inv]
    exact (mem_rootCenter_conj_iff hmM x).symm
  have hL₀J₁ : (Z ⊔ Subgroup.zpowers t).map (MulAut.conj m⁻¹).toMonoidHom = J₁ := by
    rw [Subgroup.map_sup, hZm, MonoidHom.map_zpowers, ← hJ₁eq, hmt]
    simp
  have hisoL₀ : ↥(Z ⊔ Subgroup.zpowers t) ≃* PSL2Model n :=
    ((Subgroup.equivMapOfInjective _ (MulAut.conj m⁻¹).toMonoidHom
      (MulAut.conj m⁻¹).injective).trans (MulEquiv.subgroupCongr hL₀J₁)).trans φ₁
  refine ⟨?_, ⟨hisoL₀⟩⟩
  set L₀ := Z ⊔ Subgroup.zpowers t with hL₀def
  have htL₀ : t ∈ L₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hZL₀ : Z ≤ L₀ := le_sup_left
  apply le_antisymm
  · refine sup_le ((Subgroup.closure_le _).mpr ?_) ?_
    · intro x hx
      rcases hx with rfl | rfl
      · exact hZL₀ hz
      · exact htL₀
    ·
      have hL₀ : BenderType L₀ n 1 1 := BenderType.linear n hn2 hisoL₀
      obtain ⟨S₀, hS₀⟩ := exists_sylow_eq_subgroupOf hZL₀ hZsq hZcard hL₀
      set t₀ : L₀ := ⟨t, htL₀⟩ with ht₀def
      have ht₀sq : t₀ * t₀ = 1 := Subtype.ext ht
      have hnormS₀ : ∀ x : L₀, x ∈ borel (S₀ : Subgroup L₀) →
          (x : K) ∈ borel (Q : Subgroup K) := by
        intro x hx
        apply hc.normalizer_rootCenter_le
        rw [Subgroup.mem_normalizer_iff]
        intro y
        by_cases hyL : y ∈ L₀
        · have := mem_borel_iff.mp hx ⟨y, hyL⟩
          rw [hS₀] at this
          exact this
        · have h1 : y ∉ Z := fun hyZ => hyL (hZL₀ hyZ)
          have h2 : (x : K) * y * (x : K)⁻¹ ∉ Z := by
            intro hyZ
            apply hyL
            have : (x : K)⁻¹ * ((x : K) * y * (x : K)⁻¹) * x ∈ L₀ :=
              L₀.mul_mem (L₀.mul_mem (L₀.inv_mem x.2) (hZL₀ hyZ)) x.2
            simpa [mul_assoc] using this
          exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
      have ht₀S₀ : t₀ ∉ borel (S₀ : Subgroup L₀) := fun hmem => htQ (hnormS₀ t₀ hmem)
      have hc₀ := hL₀.benderCore S₀ ht₀sq ht₀S₀
      set A : Subgroup K := (cartan (S₀ : Subgroup L₀) t₀).map L₀.subtype with hA
      have hAD : A ≤ ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ := by
        rintro _ ⟨x, hx, rfl⟩
        rw [hc.mem_commutator_cartan_iff]
        refine ⟨?_, ?_⟩
        · refine Subgroup.mem_inf.mpr ⟨hnormS₀ x (cartan_le_borel _ _ hx), ?_⟩
          have hx' : x ∈ conjugate (borel (S₀ : Subgroup L₀)) t₀ := (Subgroup.mem_inf.mp hx).2
          rw [mem_conjugate_iff_mul_inv] at hx' ⊢
          exact hnormS₀ _ hx'
        · have hxc : x ∈ ⁅cartan (S₀ : Subgroup L₀) t₀, Subgroup.zpowers t₀⁆ := by
            rw [← hc₀.cartan_eq_commutator rfl]
            exact hx
          have := (hc₀.mem_commutator_cartan_iff.mp hxc).2
          exact congrArg Subtype.val this
      have hAcard : Nat.card A = 2 ^ n - 1 := by
        rw [hA, Subgroup.card_map_of_injective L₀.subtype_injective, hc₀.card_cartan, mul_one]
      have hAeq : A = ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ :=
        Subgroup.eq_of_le_of_card_ge hAD (by rw [hc.card_commutator_cartan, hAcard])
      rw [← hAeq]
      exact Subgroup.map_subtype_le _
  · refine sup_le (hc.rootCenter_le_sup hz hz1) ?_
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))

end Main

end CFSG.GH74.Uniqueness.Bender
