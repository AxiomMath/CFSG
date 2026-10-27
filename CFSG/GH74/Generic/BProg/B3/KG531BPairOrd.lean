module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.RankThree.Classical.SteinbergBJUnitaryTwoBlock
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace KG531BP

open CFSG Subgroup
open scoped MatrixGroups commutatorElement

variable {K : Type} [Group K] [Finite K]

omit [Finite K] in
theorem card_eq_core_mul {J : Subgroup K} {F : Type} [Field F]
    (e : ↥J ⧸ pPrimeCore 2 ↥J ≃* SL(2, F)) :
    Nat.card ↥J = Nat.card ↥(pPrimeCore 2 ↥J) * Nat.card SL(2, F) := by
  rw [← Nat.card_congr e.toEquiv, mul_comm]
  exact Subgroup.card_eq_card_quotient_mul_card_subgroup _

omit [Finite K] in
theorem card_sup_mul_card_inf {J₁ J₂ : Subgroup K} (hN : J₂ ≤ normalizer (J₁ : Set K)) :
    Nat.card ↥(J₁ ⊔ J₂) * Nat.card ↥(J₁ ⊓ J₂) = Nat.card ↥J₁ * Nat.card ↥J₂ := by
  set H : Subgroup K := J₁ ⊔ J₂ with hH
  have h₁ : J₁ ≤ H := le_sup_left
  have h₂ : J₂ ≤ H := le_sup_right
  set A : Subgroup ↥H := J₁.subgroupOf H with hA
  set B : Subgroup ↥H := J₂.subgroupOf H with hB
  have hAn : A.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h₁).2 (sup_le Subgroup.le_normalizer hN)
  have hsup : B ⊔ A = ⊤ := by
    rw [hA, hB, ← Subgroup.subgroupOf_sup h₂ h₁, sup_comm, ← hH, Subgroup.subgroupOf_self]
  have e1 : A.relIndex (B ⊔ A) = A.relIndex B := Subgroup.relIndex_sup_right B A
  rw [hsup] at e1
  have e2 := Subgroup.relIndex_mul_card A (⊤ : Subgroup ↥H)
  have e3 := Subgroup.relIndex_mul_card A B
  rw [inf_top_eq, Subgroup.card_top, e1] at e2
  have cA : Nat.card ↥A = Nat.card ↥J₁ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₁).toEquiv
  have cB : Nat.card ↥B = Nat.card ↥J₂ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe h₂).toEquiv
  have cI : Nat.card ↥(A ⊓ B) = Nat.card ↥(J₁ ⊓ J₂) := by
    have hinf : (J₁ ⊓ J₂).subgroupOf H = J₁.subgroupOf H ⊓ J₂.subgroupOf H := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [hA, hB, ← hinf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h₁)).toEquiv
  rw [← cA, ← cB, ← cI, ← e2, ← e3]
  ring

theorem card_inf_dvd {J₁ J₂ : Subgroup K} (h₁ : IsPComponent 2 J₁) (h₂ : IsPComponent 2 J₂)
    (hne : J₁ ≠ J₂) {F : Type} [Field F] [Fintype F] (hodd : Odd (Fintype.card F))
    (h5 : 5 ≤ Fintype.card F) (e₁ : ↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* SL(2, F)) :
    Nat.card ↥(J₁ ⊓ J₂) ∣ 2 * Nat.card ↥(pPrimeCore 2 ↥J₁) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hdist⟩ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
      Nat.prime_two J₁ J₂ h₁ h₂
  obtain ⟨-, -, hcomm, -⟩ := hdist hne
  set O₁ := pPrimeCore 2 ↥J₁ with hO₁
  set φ : ↥J₁ →* SL(2, F) := e₁.toMonoidHom.comp (QuotientGroup.mk' O₁) with hφ
  have hφs : Function.Surjective φ := e₁.surjective.comp (QuotientGroup.mk'_surjective _)
  have hφk : φ.ker = O₁ := by
    ext y
    rw [MonoidHom.mem_ker]
    show e₁ (QuotientGroup.mk y) = 1 ↔ _
    rw [← map_one e₁, e₁.injective.eq_iff, QuotientGroup.eq_one_iff]
  have hIle : J₁ ⊓ J₂ ≤ J₁ := inf_le_left
  set I : Subgroup ↥J₁ := (J₁ ⊓ J₂).subgroupOf J₁ with hI
  have hc : ∀ g ∈ J₁, ∀ h ∈ J₂, ⁅g, h⁆ ∈ (O₁.map J₁.subtype) ∧
      ⁅g, h⁆ ∈ (pPrimeCore 2 ↥J₂).map J₂.subtype := fun g hg h hh =>
    Subgroup.mem_inf.1 (hcomm (Subgroup.commutator_mem_commutator hg hh))
  have hIn : I.Normal := by
    constructor
    intro i hi j
    rw [hI, Subgroup.mem_subgroupOf] at hi ⊢
    obtain ⟨hi1, hi2⟩ := Subgroup.mem_inf.1 hi
    refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ j.2 hi1) (inv_mem j.2), ?_⟩
    obtain ⟨o, -, ho⟩ := (hc (j : K) j.2 (i : K) hi2).2
    have hoJ : (o : K) ∈ J₂ := o.2
    have he : ((j * i * j⁻¹ : ↥J₁) : K) = ⁅(j : K), (i : K)⁆ * (i : K) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    rw [he, ← ho]
    exact Subgroup.mul_mem _ hoJ hi2
  have h4 : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ]; omega)
    exact ⟨t, ht⟩
  have hqs : IsQuasisimple SL(2, F) := CFSG.RankThree.Classical.isQuasisimple_SL2 h4
  have hImN : (I.map φ).Normal := hIn.map φ hφs
  have hIZ : I.map φ ≤ center SL(2, F) := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hqs hImN with htop | hle
    · exfalso
      obtain ⟨-, -, a, b, hab⟩ := hqs
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      have hb : b ∈ I.map φ := by rw [htop]; exact Subgroup.mem_top b
      obtain ⟨i, hi, rfl⟩ := hb
      obtain ⟨j, rfl⟩ := hφs a
      have hi2 : (i : K) ∈ J₂ := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hi)).2
      obtain ⟨o, ho, hoe⟩ := (hc (j : K) j.2 (i : K) hi2).1
      have hoeq : o = ⁅j, i⁆ := by
        apply Subtype.ext
        rw [show ((⁅j, i⁆ : ↥J₁) : K) = ⁅(j : K), (i : K)⁆ by simp [commutatorElement_def]]
        exact hoe
      have h1 : φ ⁅j, i⁆ = 1 := by
        rw [← hoeq]
        rw [← MonoidHom.mem_ker, hφk]
        exact ho
      rw [map_commutatorElement] at h1
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        (commutatorElement_eq_one_iff_mul_comm.mp h1)]
    · exact hle
  set Zs : Subgroup ↥J₁ := (center SL(2, F)).comap φ with hZs
  have hIZs : I ≤ Zs := fun i hi => hIZ ⟨i, hi, rfl⟩
  have hker : φ.ker ≤ Zs := fun i hi => by
    rw [hZs, Subgroup.mem_comap, MonoidHom.mem_ker.1 hi]
    exact one_mem _
  have hcZs : Nat.card ↥Zs = Nat.card ↥(center SL(2, F)) * Nat.card ↥O₁ := by
    have e1 := Subgroup.relIndex_mul_card φ.ker Zs
    rw [Subgroup.relIndex_ker, inf_of_le_left hker, hZs,
      Subgroup.map_comap_eq_self_of_surjective hφs, hφk] at e1
    exact e1.symm
  have hcen : Nat.card ↥(center SL(2, F)) = 2 := by
    rw [CFSG.OrderReductions.LinearOrders.card_specialLinear_center F 2 (by norm_num)]
    rw [← Fintype.card_eq_nat_card]
    obtain ⟨k, hk⟩ := hodd
    exact Nat.gcd_eq_left ⟨k, by omega⟩
  have hcI : Nat.card ↥(J₁ ⊓ J₂) = Nat.card ↥I :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIle).toEquiv).symm
  rw [hcI, ← hcen, ← hcZs]
  exact Subgroup.card_dvd_of_le hIZs

theorem sq_card_sl2_dvd {J₁ J₂ : Subgroup K} (h₁ : IsPComponent 2 J₁) (h₂ : IsPComponent 2 J₂)
    (hne : J₁ ≠ J₂) {F : Type} [Field F] [Fintype F] (hodd : Odd (Fintype.card F))
    (h5 : 5 ≤ Fintype.card F) (e₁ : ↥J₁ ⧸ pPrimeCore 2 ↥J₁ ≃* SL(2, F))
    (e₂ : ↥J₂ ⧸ pPrimeCore 2 ↥J₂ ≃* SL(2, F)) :
    Nat.card SL(2, F) ^ 2 ∣ 2 * Nat.card ↥(J₁ ⊔ J₂) := by
  obtain ⟨-, hdist⟩ :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
      Nat.prime_two J₁ J₂ h₁ h₂
  obtain ⟨hN, -, -, -⟩ := hdist hne
  have hp := card_sup_mul_card_inf hN
  obtain ⟨k, hk⟩ := card_inf_dvd h₁ h₂ hne hodd h5 e₁
  rw [card_eq_core_mul e₁, card_eq_core_mul e₂] at hp
  have hO : 0 < Nat.card ↥(pPrimeCore 2 ↥J₁) := Nat.card_pos
  refine ⟨Nat.card ↥(pPrimeCore 2 ↥J₂) * k, ?_⟩
  have h1 : Nat.card ↥(J₁ ⊔ J₂) * (2 * Nat.card ↥(pPrimeCore 2 ↥J₁)) =
      Nat.card ↥(pPrimeCore 2 ↥J₁) * Nat.card SL(2, F) *
        (Nat.card ↥(pPrimeCore 2 ↥J₂) * Nat.card SL(2, F)) * k := by
    rw [hk, ← mul_assoc, hp]
  have h2 : Nat.card ↥(pPrimeCore 2 ↥J₁) * (2 * Nat.card ↥(J₁ ⊔ J₂)) =
      Nat.card ↥(pPrimeCore 2 ↥J₁) * (Nat.card SL(2, F) ^ 2 *
        (Nat.card ↥(pPrimeCore 2 ↥J₂) * k)) := by
    calc Nat.card ↥(pPrimeCore 2 ↥J₁) * (2 * Nat.card ↥(J₁ ⊔ J₂))
        = Nat.card ↥(J₁ ⊔ J₂) * (2 * Nat.card ↥(pPrimeCore 2 ↥J₁)) := by ring
      _ = _ := h1
      _ = _ := by ring
  exact Nat.eq_of_mul_eq_mul_left hO h2

end KG531BP

end CFSG.GH74.Generic.BProg.B3
