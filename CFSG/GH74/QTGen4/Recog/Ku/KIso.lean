module

public import CFSG.GH74.QTGen4.Recog.Ku.AmalgamData
public import CFSG.GH74.QTGen4.Recog.Ku.NInvolutionsB
public import CFSG.Quasithin.Recognition.HSType15f

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
  CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign
  CFSG.Quasithin.Asc94
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem subgroupOf_sup_subgroupOf_eq_top {L : Type*} [Group L] (A B : Subgroup L) :
    A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B) = ⊤ := by
  have hA : A ≤ ((A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B)).map (A ⊔ B).subtype) :=
    fun a ha => ⟨⟨a, Subgroup.mem_sup_left ha⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  have hB : B ≤ ((A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B)).map (A ⊔ B).subtype) :=
    fun b hb => ⟨⟨b, Subgroup.mem_sup_right hb⟩, Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hb), rfl⟩
  have hX : A ⊔ B ≤ ((A.subgroupOf (A ⊔ B) ⊔ B.subgroupOf (A ⊔ B)).map (A ⊔ B).subtype) :=
    sup_le hA hB
  rw [eq_top_iff]
  rintro ⟨x, hx⟩ -
  obtain ⟨s, hs, hsx⟩ := hX hx
  have hsx' : s = ⟨x, hx⟩ := Subtype.ext hsx
  rw [← hsx']
  exact hs

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

section Certs


theorem exists_K_iso [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW] [KuLeaf LeafExistsIsParabolicL1]
    [KuLeaf LeafOTwoUpperInfL2] [KuLeaf LeafCardOTwoUpperInfL2]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) (hc : KuClose' T M H P z Ψ) :
    ∃ Φ : ↥(oTwoUpper M ⊔ Ψ.L2) ≃* ↥(stabilizer M22 (0 : Fin 22)),
      (∀ k : ↥(oTwoUpper M ⊔ Ψ.L2), (k : G) ∈ oTwoUpper M ↔ (Φ k : M22) ∈ m22TwoStab) ∧
      ∀ k : ↥(oTwoUpper M ⊔ Ψ.L2), (k : G) ∈ Ψ.L2 ↔ (Φ k : M22) ∈ m22PtHexStab := by
  obtain ⟨y₂, t, j, t₁, _hy₂, _hy₂o, _htMN, _htoT, _htt, _hty, hjL2, hjoT, _hjj, _hjy, _htj,
    ht₁oT, ht₁N, _ht₁t, _ht₁y, ht₁j⟩ := hc
  obtain ⟨a₁, b₁, hP1⟩ := h.exists_isParabolic_L1
  obtain ⟨a₂, b₂, hP2⟩ := h.exists_isParabolic_L2 Ψ
  have hX1 : oTwoUpper M ≤ oTwoUpper M ⊔ Ψ.L2 := le_sup_left
  have hX2 : Ψ.L2 ≤ oTwoUpper M ⊔ Ψ.L2 := le_sup_right
  have h₁ := hP1.subgroupOf hX1
  have h₂ := hP2.subgroupOf hX2
  have hE₁₂ : (pCoreOf 2 M).subgroupOf (oTwoUpper M ⊔ Ψ.L2) ≤ Ψ.L2.subgroupOf (oTwoUpper M ⊔ Ψ.L2) :=
    fun x hx => Subgroup.mem_subgroupOf.mpr (h.pCore_le_L2 Ψ (Subgroup.mem_subgroupOf.mp hx))
  have hE₂₁ : (kuA P H).subgroupOf (oTwoUpper M ⊔ Ψ.L2) ≤
      (oTwoUpper M).subgroupOf (oTwoUpper M ⊔ Ψ.L2) :=
    fun x hx => Subgroup.mem_subgroupOf.mpr (h.kuA_le_oTwoUpper (Subgroup.mem_subgroupOf.mp hx))
  have hne : (pCoreOf 2 M).subgroupOf (oTwoUpper M ⊔ Ψ.L2) ≠
      (kuA P H).subgroupOf (oTwoUpper M ⊔ Ψ.L2) := by
    intro e
    apply h.kuA_ne_pCore
    have e' := Subgroup.subgroupOf_inj.mp e
    have hp : pCoreOf 2 M ≤ oTwoUpper M ⊔ Ψ.L2 := (h.pCore_le_L2 Ψ).trans hX2
    have hk : kuA P H ≤ oTwoUpper M ⊔ Ψ.L2 := (h.kuA_le_oTwoUpper).trans hX1
    rw [inf_eq_left.mpr hp, inf_eq_left.mpr hk] at e'
    exact e'.symm
  have hB : Nat.card ↥((oTwoUpper M).subgroupOf (oTwoUpper M ⊔ Ψ.L2) ⊓
      Ψ.L2.subgroupOf (oTwoUpper M ⊔ Ψ.L2)) = 192 := by
    have hmap : (((oTwoUpper M).subgroupOf (oTwoUpper M ⊔ Ψ.L2) ⊓
        Ψ.L2.subgroupOf (oTwoUpper M ⊔ Ψ.L2)).map (oTwoUpper M ⊔ Ψ.L2).subtype) =
        oTwoUpper M ⊓ Ψ.L2 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨Subgroup.mem_subgroupOf.mp hy.1, Subgroup.mem_subgroupOf.mp hy.2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x, hX1 h1⟩, ⟨Subgroup.mem_subgroupOf.mpr h1, Subgroup.mem_subgroupOf.mpr h2⟩, rfl⟩
    rw [← Subgroup.card_map_of_injective (oTwoUpper M ⊔ Ψ.L2).subtype_injective, hmap,
      h.card_oTwoUpper_inf_L2 Ψ]
  have ht₁X : t₁ ∈ oTwoUpper M ⊔ Ψ.L2 := hX1 ht₁oT
  have hjX : j ∈ oTwoUpper M ⊔ Ψ.L2 := hX2 hjL2
  have ht₁L₂ : t₁ ∉ Ψ.L2 := by
    intro hm
    have hmem : t₁ ∈ oTwoUpper M ⊓ Ψ.L2 := ⟨ht₁oT, hm⟩
    rw [h.oTwoUpper_inf_L2 Ψ] at hmem
    exact ht₁N hmem.2
  have hgen := subgroupOf_sup_subgroupOf_eq_top (oTwoUpper M) Ψ.L2
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ := exists_mulEquiv_m22Stab_of_parabolics hgen h₁ h₂ hE₁₂ hE₂₁ hne hB
    (t₁ := ⟨t₁, ht₁X⟩) (t₂ := ⟨j, hjX⟩)
    (Subgroup.mem_subgroupOf.mpr ht₁oT) (fun hm => ht₁L₂ (Subgroup.mem_subgroupOf.mp hm))
    (Subgroup.mem_subgroupOf.mpr hjL2) (fun hm => hjoT (Subgroup.mem_subgroupOf.mp hm))
    (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact _ht₁t))
    (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact _hjj))
    (by
      rw [← Subgroup.orderOf_coe]
      exact ht₁j)
  refine ⟨Φ, fun k => ?_, fun k => ?_⟩
  · exact Subgroup.mem_subgroupOf.symm.trans (hΦ₁ k)
  · exact Subgroup.mem_subgroupOf.symm.trans (hΦ₂ k)

theorem K_inf_kuN [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW] [KuLeaf LeafExistsIsParabolicL1]
    [KuLeaf LeafOTwoUpperInfL2] [KuLeaf LeafCardOTwoUpperInfL2]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) (hc : KuClose' T M H P z Ψ) :
    (oTwoUpper M ⊔ Ψ.L2) ⊓ kuN P H = Ψ.L2 := by
  obtain ⟨Φ, _, _⟩ := h.exists_K_iso Ψ hc
  have hLK : Ψ.L2 ≤ oTwoUpper M ⊔ Ψ.L2 := le_sup_right
  have hLN : Ψ.L2 ≤ kuN P H := pre_le_kuN Ψ lamS
  have hKcard : Nat.card ↥(oTwoUpper M ⊔ Ψ.L2) = 20160 := by
    rw [Nat.card_congr Φ.toEquiv, card_stabilizer_point]
  have hrelLK : Ψ.L2.relIndex (oTwoUpper M ⊔ Ψ.L2) = 21 := by
    have hm := Subgroup.relIndex_mul_card (H := Ψ.L2) (K := oTwoUpper M ⊔ Ψ.L2)
    rw [inf_eq_left.mpr hLK, h.card_L2 Ψ, hKcard] at hm
    omega
  have hLQ : Ψ.L2 ≤ (oTwoUpper M ⊔ Ψ.L2) ⊓ kuN P H := le_inf hLK hLN
  set Q : Subgroup G := (oTwoUpper M ⊔ Ψ.L2) ⊓ kuN P H with hQ
  have hm1 := Subgroup.relIndex_mul_relIndex (H := Ψ.L2) (K := Q) (L := oTwoUpper M ⊔ Ψ.L2)
    hLQ (inf_le_left : Q ≤ oTwoUpper M ⊔ Ψ.L2)
  have hm2 := Subgroup.relIndex_mul_relIndex (H := Ψ.L2) (K := Q) (L := kuN P H)
    hLQ (inf_le_right : Q ≤ kuN P H)
  rw [hrelLK] at hm1
  rw [h.relIndex_L2 Ψ] at hm2
  have hdvd : Ψ.L2.relIndex Q ∣ 3 := by
    have h3 : Nat.gcd 21 6 = 3 := by norm_num
    rw [← h3]
    exact Nat.dvd_gcd (Dvd.intro _ hm1) (Dvd.intro _ hm2)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hLQ
  · exfalso
    have hrelQN : Q.relIndex (kuN P H) = 2 := by
      rw [h3] at hm2
      omega
    have hidx : (Q.subgroupOf (kuN P H)).index = 2 := hrelQN
    have hker : ∀ n : ↥(kuN P H), Ψ.π n = 1 → n ∈ Q.subgroupOf (kuN P H) := by
      intro n hn
      have hE : (n : G) ∈ kuA P H := (Ψ.ker n).mp hn
      have hkK : kuA P H ≤ oTwoUpper M ⊔ Ψ.L2 := h.kuA_le_oTwoUpper.trans le_sup_left
      have hkN : kuA P H ≤ kuN P H := Subgroup.le_normalizer
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hkK hE, hkN hE⟩)
    have hA : alternatingGroup (Fin 6) ≤ (Q.subgroupOf (kuN P H)).map Ψ.π := by
      rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
      intro σ hσ
      have hσ' : σ.IsThreeCycle := hσ
      have hσ3 : σ ^ 3 = 1 := by
        have := pow_orderOf_eq_one σ
        rwa [hσ'.orderOf] at this
      obtain ⟨n, hn⟩ := Ψ.π_surj (σ ^ 2)
        (Subgroup.pow_mem _ (Equiv.Perm.IsThreeCycle.mem_alternatingGroup hσ') 2)
      refine Subgroup.mem_map.mpr ⟨n ^ 2, Subgroup.sq_mem_of_index_two hidx n, ?_⟩
      rw [map_pow, hn, ← pow_mul, show 2 * 2 = 1 + 3 from rfl, pow_add, hσ3, mul_one, pow_one]
    have hall : ∀ n : ↥(kuN P H), n ∈ Q.subgroupOf (kuN P H) := by
      intro n
      obtain ⟨q, hq, hqn⟩ := Subgroup.mem_map.mp (hA (Ψ.π_alt n))
      have hk : q⁻¹ * n ∈ Q.subgroupOf (kuN P H) :=
        hker _ (by rw [map_mul, map_inv, hqn, inv_mul_cancel])
      simpa using (Q.subgroupOf (kuN P H)).mul_mem hq hk
    have htop : Q.subgroupOf (kuN P H) = ⊤ := eq_top_iff.mpr fun n _ => hall n
    rw [htop, Subgroup.index_top] at hidx
    omega

end Certs

end KuHyp

end CFSG.GH74.QTGen4.Ku
