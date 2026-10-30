module

public import CFSG.GH74.QTGen4.Recog.Ku.KIso
public import CFSG.GH74.QTGen4.Recog.Ku.JIsoB

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
  CFSG.Quasithin.L34Amalgam MulAction CFSG.ComponentClassification.WittDesign
  CFSG.Quasithin.Asc94
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem conj_mem_iff_of_maximal {K L L₂ N : Subgroup G} {t : G} (htt : t * t = 1)
    (hLK : L ≤ K) (htL : t ∈ Subgroup.normalizer (L : Set G))
    (hmax : ∀ S : Subgroup G, L ≤ S → S ≤ K → S = L ∨ S = K)
    (htN : t ∈ N) (hKN : K ⊓ N = L₂)
    (hself : ∀ n ∈ N, (∀ x ∈ L₂, n * x * n⁻¹ ∈ L₂) → n ∈ L₂)
    (htL₂ : t ∉ L₂) :
    ∀ k ∈ K, t * k * t ∈ K ↔ k ∈ L := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hconjL : ∀ x ∈ L, t * x * t⁻¹ ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp htL x).mp hx
  let φ : G →* G := (MulAut.conj t).toMonoidHom
  have hφ : ∀ x, φ x = t * x * t⁻¹ := fun x => rfl
  let S : Subgroup G := K ⊓ K.comap φ
  have hLS : L ≤ S := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨hLK hx, ?_⟩
    rw [Subgroup.mem_comap, hφ]
    exact hLK (hconjL x hx)
  have hS_eq : S = L := by
    rcases hmax S hLS inf_le_left with h1 | h2
    · exact h1
    · exfalso
      have hKS : K ≤ S := le_of_eq h2.symm
      have hKc : ∀ k ∈ K, t * k * t⁻¹ ∈ K := fun k hk => by
        have hk' := (Subgroup.mem_inf.mp (hKS hk)).2
        rw [Subgroup.mem_comap, hφ] at hk'
        exact hk'
      apply htL₂
      apply hself t htN
      intro x hx
      have hxKN : x ∈ K ⊓ N := by rw [hKN]; exact hx
      have hN' : t * x * t⁻¹ ∈ N :=
        N.mul_mem (N.mul_mem htN (Subgroup.mem_inf.mp hxKN).2) (N.inv_mem htN)
      rw [← hKN]
      exact Subgroup.mem_inf.mpr ⟨hKc x (Subgroup.mem_inf.mp hxKN).1, hN'⟩
  intro k hk
  constructor
  · intro hkt
    have hkS : k ∈ S := by
      refine Subgroup.mem_inf.mpr ⟨hk, ?_⟩
      rw [Subgroup.mem_comap, hφ, hti]
      exact hkt
    rw [hS_eq] at hkS
    exact hkS
  · intro hkL
    have hc := hconjL k hkL
    rw [hti] at hc
    exact hLK hc

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

section Certs

theorem exists_J_iso_of_conj [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW] [KuLeaf LeafKuNEqL2DoubleCoset]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    {t j : G} (htMN : t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) (htoT : t ∉ oTwoUpper M)
    (htt : t * t = 1) (hjL2 : j ∈ Ψ.L2) (hjoT : j ∉ oTwoUpper M) (hjj : j * j = 1)
    (htj : (t * j) ^ 3 = 1) (htJ : t ∈ oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)
    (Φ : ↥(oTwoUpper M ⊔ Ψ.L2) ≃* ↥(stabilizer M22 (0 : Fin 22)))
    (hΦ₁ : ∀ k : ↥(oTwoUpper M ⊔ Ψ.L2), (k : G) ∈ oTwoUpper M ↔ (Φ k : M22) ∈ m22TwoStab)
    (hΦ₂ : ∀ k : ↥(oTwoUpper M ⊔ Ψ.L2), (k : G) ∈ Ψ.L2 ↔ (Φ k : M22) ∈ m22PtHexStab)
    (hKN : (oTwoUpper M ⊔ Ψ.L2) ⊓ kuN P H = Ψ.L2)
    (hconj : ∀ k : ↥(oTwoUpper M ⊔ Ψ.L2),
      t * (k : G) * t ∈ oTwoUpper M ⊔ Ψ.L2 ↔ (Φ k : M22) ∈ m22TwoStab) :
    Nonempty (↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H) ≃* NativeSporadic.M22) := by
  have hX1 : oTwoUpper M ≤ oTwoUpper M ⊔ Ψ.L2 := le_sup_left
  have hX2 : Ψ.L2 ≤ oTwoUpper M ⊔ Ψ.L2 := le_sup_right
  have hKJ : oTwoUpper M ⊔ Ψ.L2 ≤ oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H := le_sup_left
  have hNJ : kuN P H ≤ oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H := le_sup_right
  have hLN : Ψ.L2 ≤ kuN P H := pre_le_kuN Ψ lamS
  have hrelKN : (oTwoUpper M ⊔ Ψ.L2).relIndex (kuN P H) = 6 := by
    have hm1 := Subgroup.relIndex_mul_card (H := oTwoUpper M ⊔ Ψ.L2) (K := kuN P H)
    have hm2 := Subgroup.relIndex_mul_card (H := Ψ.L2) (K := kuN P H)
    rw [hKN, h.card_L2 Ψ] at hm1
    rw [inf_eq_left.mpr hLN, h.relIndex_L2 Ψ, h.card_L2 Ψ] at hm2
    omega
  have hH6 : ((oTwoUpper M ⊔ Ψ.L2).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)).relIndex
      ((kuN P H).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) = 6 := by
    rw [Subgroup.relIndex_subgroupOf hNJ]
    exact hrelKN
  have hgen : (oTwoUpper M ⊔ Ψ.L2).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H) ⊔
      (kuN P H).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H) = ⊤ :=
    subgroupOf_sup_subgroupOf_eq_top (oTwoUpper M ⊔ Ψ.L2) (kuN P H)
  let Φ' : ↥((oTwoUpper M ⊔ Ψ.L2).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) ≃*
      ↥(stabilizer M22 (0 : Fin 22)) :=
    (Subgroup.subgroupOfEquivOfLe hKJ).trans Φ
  have hH : ∀ k : ↥((oTwoUpper M ⊔ Ψ.L2).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)),
      (k : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) ∈
        (kuN P H).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H) ↔
        (Φ' k : M22) ∈ m22PtHexStab := by
    intro k
    have hxK : ((k : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) : G) ∈ oTwoUpper M ⊔ Ψ.L2 :=
      Subgroup.mem_subgroupOf.mp k.2
    rw [Subgroup.mem_subgroupOf]
    have hkey : ((k : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) : G) ∈ kuN P H ↔
        ((k : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) : G) ∈ Ψ.L2 := by
      constructor
      · intro hN
        have hm : ((k : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) : G) ∈ (oTwoUpper M ⊔ Ψ.L2) ⊓ kuN P H :=
          Subgroup.mem_inf.mpr ⟨hxK, hN⟩
        rw [hKN] at hm
        exact hm
      · exact fun hL => hLN hL
    rw [hkey]
    exact hΦ₂ ⟨_, hxK⟩
  have ht : ∀ k : ↥((oTwoUpper M ⊔ Ψ.L2).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)),
      (⟨t, htJ⟩ : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) * (k : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) *
        (⟨t, htJ⟩ : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) ∈
          (oTwoUpper M ⊔ Ψ.L2).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H) ↔
        (Φ' k : M22) ∈ m22TwoStab := by
    intro k
    rw [Subgroup.mem_subgroupOf]
    have hxK : ((k : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) : G) ∈ oTwoUpper M ⊔ Ψ.L2 :=
      Subgroup.mem_subgroupOf.mp k.2
    exact hconj ⟨_, hxK⟩
  have hHt : ∀ x ∈ (kuN P H).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H),
      x ∈ (oTwoUpper M ⊔ Ψ.L2).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H) ∨
      ∃ a ∈ (kuN P H).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H) ⊓
          (oTwoUpper M ⊔ Ψ.L2).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H),
        ∃ b ∈ (kuN P H).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H) ⊓
          (oTwoUpper M ⊔ Ψ.L2).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H),
        x = a * (⟨t, htJ⟩ : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) * b := by
    intro x hx
    have hxN : ((x : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) : G) ∈ kuN P H :=
      Subgroup.mem_subgroupOf.mp hx
    rcases kuN_eq_L2_doubleCoset h Ψ htMN htoT _ hxN with hL | ⟨a, ha, b, hb, hab⟩
    · exact Or.inl (Subgroup.mem_subgroupOf.mpr (hX2 hL))
    · have haJ : a ∈ oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H := hKJ (hX2 ha)
      have hbJ : b ∈ oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H := hKJ (hX2 hb)
      refine Or.inr ⟨⟨a, haJ⟩, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_subgroupOf.mpr (hLN ha), Subgroup.mem_subgroupOf.mpr (hX2 ha)⟩,
        ⟨b, hbJ⟩, Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_subgroupOf.mpr (hLN hb), Subgroup.mem_subgroupOf.mpr (hX2 hb)⟩, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact hab
  have hjX : j ∈ oTwoUpper M ⊔ Ψ.L2 := hX2 hjL2
  have hjJ : j ∈ oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H := hKJ hjX
  have hjK : (⟨j, hjJ⟩ : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) ∈
      (oTwoUpper M ⊔ Ψ.L2).subgroupOf (oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H) :=
    Subgroup.mem_subgroupOf.mpr hjX
  have hj₁ : (Φ' ⟨⟨j, hjJ⟩, hjK⟩ : M22) ∉ m22TwoStab := fun hm =>
    hjoT ((hΦ₁ ⟨j, hjX⟩).mpr hm)
  have htt' : (⟨t, htJ⟩ : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) * ⟨t, htJ⟩ = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact htt)
  have hjj' : (⟨j, hjJ⟩ : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) * ⟨j, hjJ⟩ = 1 :=
    Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one]; exact hjj)
  have htj' : ((⟨t, htJ⟩ : ↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H)) * ⟨j, hjJ⟩) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one]; exact htj)
  obtain ⟨Ψ', -⟩ := M22Witt.nonempty_mulEquiv_m22_of_local Φ' hgen hH hH6 htt' ht hHt hjK hj₁
    hjj' htj'
  exact ⟨Ψ'⟩

theorem t_notMem_L2 [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW] [KuLeaf LeafKuNEqL2DoubleCoset]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    {t : G} (htMN : t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) (htoT : t ∉ oTwoUpper M) :
    t ∉ Ψ.L2 := by
  intro htL
  have hle : kuN P H ≤ Ψ.L2 := by
    intro g hg
    rcases kuN_eq_L2_doubleCoset h Ψ htMN htoT g hg with hL | ⟨a, ha, b, hb, hab⟩
    · exact hL
    · rw [hab]
      exact Ψ.L2.mul_mem (Ψ.L2.mul_mem ha htL) hb
  have h1 : Ψ.L2.relIndex (kuN P H) = 1 := Subgroup.relIndex_eq_one.mpr hle
  have h6 := h.relIndex_L2 Ψ
  rw [h1] at h6
  norm_num at h6

theorem le_maximal_of_Phi (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    (Φ : ↥(oTwoUpper M ⊔ Ψ.L2) ≃* ↥(stabilizer M22 (0 : Fin 22)))
    (hΦ₁ : ∀ k : ↥(oTwoUpper M ⊔ Ψ.L2), (k : G) ∈ oTwoUpper M ↔ (Φ k : M22) ∈ m22TwoStab) :
    ∀ S : Subgroup G, oTwoUpper M ≤ S → S ≤ oTwoUpper M ⊔ Ψ.L2 →
      S = oTwoUpper M ∨ S = oTwoUpper M ⊔ Ψ.L2 := by
  intro S hS hSK
  by_cases heq : S ≤ oTwoUpper M
  · exact Or.inl (le_antisymm heq hS)
  · right
    have hex : ∃ y, y ∈ S ∧ y ∉ oTwoUpper M := by
      by_contra hc
      push Not at hc
      exact heq (fun y hy => hc y hy)
    obtain ⟨y, hyS, hyL1⟩ := hex
    exact le_antisymm hSK (le_of_lt_L1 Φ hΦ₁ hS (hSK hyS) hyS hyL1)

theorem exists_J_iso_of_maximal [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafHInfCentralizerKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW] [KuLeaf LeafKuNEqL2DoubleCoset]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z)
    {t j : G} (htMN : t ∈ M ⊓ Subgroup.normalizer (kuV2 T M : Set G)) (htoT : t ∉ oTwoUpper M)
    (htt : t * t = 1) (hjL2 : j ∈ Ψ.L2) (hjoT : j ∉ oTwoUpper M) (hjj : j * j = 1)
    (htj : (t * j) ^ 3 = 1)
    (Φ : ↥(oTwoUpper M ⊔ Ψ.L2) ≃* ↥(stabilizer M22 (0 : Fin 22)))
    (hΦ₁ : ∀ k : ↥(oTwoUpper M ⊔ Ψ.L2), (k : G) ∈ oTwoUpper M ↔ (Φ k : M22) ∈ m22TwoStab)
    (hΦ₂ : ∀ k : ↥(oTwoUpper M ⊔ Ψ.L2), (k : G) ∈ Ψ.L2 ↔ (Φ k : M22) ∈ m22PtHexStab)
    (hKN : (oTwoUpper M ⊔ Ψ.L2) ⊓ kuN P H = Ψ.L2) :
    Nonempty (↥(oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H) ≃* NativeSporadic.M22) := by
  have htN : t ∈ kuN P H := by
    have h1 : t ∈ M ⊓ kuN P H := by
      rw [h.M_inf_kuN_eq]
      exact htMN
    exact h1.2
  have htJ : t ∈ oTwoUpper M ⊔ Ψ.L2 ⊔ kuN P H := Subgroup.mem_sup_right htN
  have htL : t ∈ Subgroup.normalizer (oTwoUpper M : Set G) := h.M_le_normalizer_oTwoUpper htMN.1
  have hLK : oTwoUpper M ≤ oTwoUpper M ⊔ Ψ.L2 := le_sup_left
  have htL₂ : t ∉ Ψ.L2 := h.t_notMem_L2 Ψ htMN htoT
  have hconj : ∀ k : ↥(oTwoUpper M ⊔ Ψ.L2),
      t * (k : G) * t ∈ oTwoUpper M ⊔ Ψ.L2 ↔ (Φ k : M22) ∈ m22TwoStab := by
    intro k
    rw [← hΦ₁ k]
    exact conj_mem_iff_of_maximal htt hLK htL (le_maximal_of_Phi Ψ Φ hΦ₁) htN hKN
      Ψ.selfNormalizing_L2 htL₂ (k : G) k.2
  exact exists_J_iso_of_conj h Ψ htMN htoT htt hjL2 hjoT hjj htj htJ Φ hΦ₁ hΦ₂ hKN hconj

end Certs

end KuHyp

end CFSG.GH74.QTGen4.Ku

end
