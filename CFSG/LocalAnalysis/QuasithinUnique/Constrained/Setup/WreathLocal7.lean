module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellAdapter
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilpA
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathLocal1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.WreathTransfer

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open scoped Pointwise commutatorElement
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Campbell

section Finite

variable {H : Type*} [Group H] [Finite H] {R M V W F : Subgroup H} {r : ℕ} {I : Fin r → Subgroup H}
  {Pm : Subgroup (Equiv.Perm (Fin r))} (h : WreathHyp R M V W F I Pm)

namespace WreathHyp

include h

omit [Finite H] in
theorem B_le_normalizer_Dat (i : Fin r) :
    h.B ≤ Subgroup.normalizer (h.Dat i : Set (MulAut ↥W)) := by
  let _ := h.cg
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    exact mul_mul_inv_mem_cubeAt h.planeFamily hg hd
  · intro hd
    have := mul_mul_inv_mem_cubeAt h.planeFamily ((baseGp (planesIn W I)).inv_mem hg) hd
    have h2 : g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d := by group
    rw [h2] at this
    exact this

omit [Finite H] in
theorem card_Dat (i : Fin r) : Nat.card ↥(h.Dat i) = 3 := by
  let _ := h.cg
  exact card_cubeAt h.planeFamily i

omit [Finite H] in
theorem D_le_B : h.D ≤ h.B := by
  let _ := h.cg
  exact cubeBase_le_baseGp h.planeFamily

omit [Finite H] in
theorem map_conj_rho_Dat (x : H) (i : Fin r) :
    (h.Dat i).map (MulAut.conj (h.rho x)).toMonoidHom = h.Dat (h.piH x i) := by
  apply le_antisymm
  · rintro _ ⟨d, hd, rfl⟩
    exact h.conj_Dat_mem x hd
  · intro d hd
    have h1 := h.conj_Dat_mem x⁻¹ hd
    have h2 : h.piH x⁻¹ (h.piH x i) = i := by
      rw [map_inv]
      simp
    rw [h2, map_inv, inv_inv] at h1
    exact ⟨(h.rho x)⁻¹ * d * h.rho x, h1, by simp [MulAut.conj_apply, mul_assoc]⟩

omit [Finite H] in
theorem map_rho_conj {K : Subgroup H} (x : H) :
    (K.map (MulAut.conj x).toMonoidHom).map h.rho =
      (K.map h.rho).map (MulAut.conj (h.rho x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [map_mul, map_inv]

omit [Finite H] in
theorem blockQ_map_conj {K : Subgroup H} {i : Fin r} (hK : blockQ K = I i) (x : H) :
    blockQ (K.map (MulAut.conj x).toMonoidHom) = I (h.piH x i) := by
  rw [blockQ_map_injective _ (MulAut.conj x).injective, hK]
  exact h.map_conj_plane x i

variable {i : Fin r} {K : Subgroup H}

omit [Finite H] in
theorem rho_eq_one_of_mem_Q0
    (hcent : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓
      Subgroup.centralizer (W : Set H) =
        blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R))
    {q : H} (hq : q ∈ blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)) :
    h.rho q = 1 := by
  rw [← hcent] at hq
  have : q ∈ h.rho.ker := by rw [h.ker_rho]; exact hq.2
  exact this

omit [Finite H] in
theorem map_rho_Q0
    (hcent : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓
      Subgroup.centralizer (W : Set H) =
        blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)) :
    (blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)).map h.rho = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨q, hq, rfl⟩
  exact h.rho_eq_one_of_mem_Q0 hcent hq

omit [Finite H] in
theorem mem_sup_Q0_iff
    (hcent : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓
      Subgroup.centralizer (W : Set H) =
        blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R))
    (hKN : K ≤ oddOrderSubgroup (⊤ : Subgroup H)) (hK : K.map h.rho = h.Dat i) {y : H}
    (hy : y ∈ oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) :
    y ∈ K ⊔ blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ↔
      h.rho y ∈ h.Dat i := by
  constructor
  · intro hmem
    have : (K ⊔ blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)).map h.rho =
        h.Dat i := by
      rw [Subgroup.map_sup, hK, h.map_rho_Q0 hcent, sup_bot_eq]
    rw [← this]
    exact ⟨y, hmem, rfl⟩
  · intro hρ
    rw [← hK] at hρ
    obtain ⟨k, hk, hky⟩ := hρ
    have hkNS : k ∈ oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R :=
      Subgroup.mem_sup_left (hKN hk)
    have h1' : k⁻¹ * y ∈ h.rho.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hky]
      group
    rw [h.ker_rho] at h1'
    have h1 : k⁻¹ * y ∈ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓
        Subgroup.centralizer (W : Set H) :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hkNS) hy, h1'⟩
    rw [hcent] at h1
    have : y = k * (k⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hk h1

theorem isSubnormal_sup_Q0
    (hcent : (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R) ⊓
      Subgroup.centralizer (W : Set H) =
        blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R))
    (hKN : K ≤ oddOrderSubgroup (⊤ : Subgroup H)) (hK : K.map h.rho = h.Dat i) :
    ((K ⊔ blockQ (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)).subgroupOf
      (oddOrderSubgroup (⊤ : Subgroup H) ⊔ elemBaumannIn 2 R)).IsSubnormal := by
  set N := oddOrderSubgroup (⊤ : Subgroup H) with hN
  set S := elemBaumannIn 2 R with hS
  set Q := blockQ (N ⊔ S) with hQ
  have hNn : N.Normal := oddOrderSubgroup_top_normal
  have hQS : Q ≤ S := by
    obtain ⟨t, hTC⟩ := internal_S3_wreath_transfer h
    exact hTC.syl_S.pCoreOf_le
  have hQNS : Q ≤ N ⊔ S := blockQ_le_self _
  have hNQ : N ⊔ Q ≤ N ⊔ S := sup_le_sup_left hQS N
  have hKQ : K ⊔ Q ≤ N ⊔ Q := sup_le_sup_right hKN Q
  have hn1 : ((N ⊔ Q).subgroupOf (N ⊔ S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNQ]
    refine sup_le (fun n hn => ?_) (fun s hs => ?_)
    · exact mem_normalizer_sup' (normal_le_normalizer' hNn N hn)
        (le_normalizer_blockQ _ (Subgroup.mem_sup_left hn))
    · exact mem_normalizer_sup' (normal_le_normalizer' hNn S hs)
        (le_normalizer_blockQ _ (Subgroup.mem_sup_right hs))
  have hρ : ∀ g ∈ N ⊔ Q, h.rho g ∈ h.D := by
    intro g hg
    have : (N ⊔ Q).map h.rho = h.D := by
      rw [Subgroup.map_sup, h.rho_map_odd, h.map_rho_Q0 hcent, sup_bot_eq]
    rw [← this]
    exact ⟨g, hg, rfl⟩
  have hn2 : ((K ⊔ Q).subgroupOf (N ⊔ Q)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKQ]
    intro x g hx hg
    have hxNS : x ∈ N ⊔ S := hNQ (hKQ hx)
    have hgNS : g ∈ N ⊔ S := hNQ hg
    have hxρ : h.rho x ∈ h.Dat i := (h.mem_sup_Q0_iff hcent hKN hK hxNS).mp hx
    refine (h.mem_sup_Q0_iff hcent hKN hK ?_).mpr ?_
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgNS hxNS) (Subgroup.inv_mem _ hgNS)
    · rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp
        (h.B_le_normalizer_Dat i (h.D_le_B (hρ g hg))) _).mp hxρ
  exact Layer.isSubnormal_trans hKQ hNQ hn2.isSubnormal hn1.isSubnormal

end WreathHyp

end Finite

end CFSG.QuasithinUnique.Setup.Wreath
