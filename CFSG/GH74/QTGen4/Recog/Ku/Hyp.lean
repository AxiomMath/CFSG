module

public import CFSG.Quasithin.Vol2.Ch6Inputs
public import Certificates.Data.CFSGNative.H13.J4Chain

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

structure KuHyp (G : Type) [Group G] (T M H P : Subgroup G) (z : G) : Prop where
  simple : IsSimpleGroup G
  sylow : quasithinIsSylowTwo T
  tM : T ≤ M
  tH : T ≤ H
  vElem : IsElemAbelian 2 (pCoreOf 2 M)
  vCard : Nat.card (pCoreOf 2 M) = 16
  mNorm : M = Subgroup.normalizer (pCoreOf 2 M : Set G)
  mCent : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) = pCoreOf 2 M
  mQuot : ∃ φ : ↥M →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
    φ.ker = (pCoreOf 2 M).subgroupOf M
  mNat : IsNatModCh5 (oTwoUpper M) (pCoreOf 2 M) 2
  pH : P ≤ H
  hNormP : H ≤ Subgroup.normalizer (P : Set G)
  pExtra : E2.IsExtraspecialPlus 2 P
  hQuot : ∃ φ : ↥H →* Equiv.Perm (Fin 3) × Multiplicative (ZMod 2), Function.Surjective φ ∧
    φ.ker = P.subgroupOf H
  hCentP : H ⊓ Subgroup.centralizer (P : Set G) ≤ P
  pCentP : P ⊓ Subgroup.centralizer (P : Set G) = Subgroup.zpowers z
  xSylow : ∃ X : Subgroup G, IsSylowIn 3 X H ∧
    P ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers z
  hCz : H = Subgroup.centralizer ({z} : Set G)
  typeM22 : ∃ d : G, d⁻¹ * z * d ∈ P ∧ d⁻¹ * z * d ≠ z ∧
    IsElemAbelian 2 (P ⊓ CFSG.Quasithin.conjSubgroup P d) ∧
    Nat.card ↥(P ⊓ CFSG.Quasithin.conjSubgroup P d) = 4

theorem stmtKuM22_iff_of_hyp :
    StmtKuM22 ↔ ∀ (G : Type) [Group G] [Finite G] (T M H P : Subgroup G) (z : G),
      KuHyp G T M H P z → Nonempty (G ≃* NativeSporadic.M22) := by
  constructor
  · intro h G _ _ T M H P z hK
    exact h G T M H P z hK.simple hK.sylow hK.tM hK.tH hK.vElem hK.vCard hK.mNorm hK.mCent
      hK.mQuot hK.mNat hK.pH hK.hNormP hK.pExtra hK.hQuot hK.hCentP hK.pCentP hK.xSylow
      hK.hCz hK.typeM22
  · intro h G _ _ T M H P z hs hT hTM hTH h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    exact h G T M H P z ⟨hs, hT, hTM, hTH, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15⟩

namespace KuHyp

variable {G : Type} [Group G] {T M H P : Subgroup G} {z : G}

theorem isPGroup_P (h : KuHyp G T M H P z) : IsPGroup 2 P := by
  have hc := h.pExtra.2.1
  exact IsPGroup.of_card (n := 1 + 2 * 2) hc

theorem P_le_T (h : KuHyp G T M H P z) : P ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 G := h.sylow.1.toSylow h.sylow.2
  have hTn : T ≤ Subgroup.normalizer (P : Set G) := h.tH.trans h.hNormP
  have hsup : IsPGroup 2 (P ⊔ T : Subgroup G) :=
    h.isPGroup_P.to_sup_of_normal_left' h.sylow.1 hTn
  have : (P ⊔ T : Subgroup G) = (S : Subgroup G) := S.is_maximal' hsup le_sup_right
  have hS : (S : Subgroup G) = T := rfl
  rw [hS] at this
  exact le_sup_left.trans this.le

theorem z_mem_center_T (h : KuHyp G T M H P z) : z ∈ T ∧ ∀ y ∈ T, y * z = z * y := by
  have hzP : z ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
    rw [h.pCentP]; exact Subgroup.mem_zpowers z
  refine ⟨h.P_le_T hzP.1, fun y hy => ?_⟩
  have := h.hCz ▸ h.tH hy
  exact Subgroup.mem_centralizer_singleton_iff.mp this

theorem center_T_le_zpowers (h : KuHyp G T M H P z) :
    ∀ x ∈ T, (∀ y ∈ T, y * x = x * y) → x ∈ Subgroup.zpowers z := by
  intro x hxT hx
  have hxc : x ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact hx p (h.P_le_T hp)
  have hxP : x ∈ P := h.hCentP ⟨h.tH hxT, hxc⟩
  have : x ∈ P ⊓ Subgroup.centralizer (P : Set G) := ⟨hxP, hxc⟩
  rwa [h.pCentP] at this

end KuHyp

end CFSG.GH74.QTGen4.Ku
