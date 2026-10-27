module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporRuFin
public import Certificates.Certificate4097
public import CFSG.Sporadic.Schreier.RuCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.RuPairs

open CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native Equiv
open scoped Pointwise

theorem ruSBlock_check :
    (∀ j < 4, ∀ i < 6, imgSorted ruSGensA[j]! (ruCBlockList i) =
      ruCBlockList (ruSBlockArr j)[i]!) ∧ (∀ j < 4, ∀ i < 6, (ruSBlockArr j)[i]! < 6) :=
  Certificates.certificate4097

@[expose] def ruSPi (j : ℕ) (i : Fin 6) : Fin 6 :=
  ⟨(ruSBlockArr j)[(i : ℕ)]! % 6, Nat.mod_lt _ (by norm_num)⟩

theorem ruSPi_val {j : ℕ} (hj : j < 4) (i : Fin 6) :
    ((ruSPi j i : Fin 6) : ℕ) = (ruSBlockArr j)[(i : ℕ)]! :=
  Nat.mod_eq_of_lt (ruSBlock_check.2 j hj i i.2)

theorem ruSGen_block {j : ℕ} (hj : j < 4) (i : Fin 6) :
    ruSGens.getD j 1 • ruCBlock i = ruCBlock (ruSPi j i) := by
  have himg := (ruCBlock_pointList i.2).img (rep_ruSGens j hj)
  rw [ruCBlock, ← himg.2, ruSBlock_check.1 j hj i i.2, ruCBlock, ruSPi_val hj]

theorem rep_ruCBlockHom_S {j : ℕ} (hj : j < 4) :
    Rep 6 (ruSBlockArr j) (ruCBlockHom ⟨ruSGens.getD j 1, ruSGens_memC' j⟩) := by
  intro i
  have h := (ruCBlockHom_spec ⟨ruSGens.getD j 1, ruSGens_memC' j⟩ i).symm.trans
    (ruSGen_block hj i)
  rw [← ruSPi_val hj i, ruCBlock_injective h]

theorem ruCBlockHom_ruSGens :
    ruCBlockHom ⟨ruSGens.getD 0 1, ruSGens_memC' 0⟩ = 1 ∧
    ruCBlockHom ⟨ruSGens.getD 1 1, ruSGens_memC' 1⟩ = 1 ∧
    ruCBlockHom ⟨ruSGens.getD 2 1, ruSGens_memC' 2⟩ = blockTau2 ∧
    ruCBlockHom ⟨ruSGens.getD 3 1, ruSGens_memC' 3⟩ = blockTau3 :=
  ⟨(rep_ruCBlockHom_S (j := 0) (by norm_num)).unique rep_one6,
    (rep_ruCBlockHom_S (j := 1) (by norm_num)).unique rep_one6,
    (rep_ruCBlockHom_S (j := 2) (by norm_num)).unique rep_blockTau2,
    (rep_ruCBlockHom_S (j := 3) (by norm_num)).unique rep_blockTau3⟩

theorem ruCBlockHom_ruC0 : ruCBlockHom ⟨ruC0, ruC0_memC⟩ = blockPerm0 :=
  (rep_ruCBlockHom (g := 0) (by norm_num) ruC0_memC).unique rep_blockPerm0

theorem ruCBlockHom_ruC1 : ruCBlockHom ⟨ruC1, ruC1_memC⟩ = blockPerm1 :=
  (rep_ruCBlockHom (g := 1) (by norm_num) ruC1_memC).unique rep_blockPerm1

theorem mem_ruSGens_getD {x : Perm (Fin 4060)} (hx : x ∈ ruSGens) :
    ∃ j, j < 4 ∧ x = ruSGens.getD j 1 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  refine ⟨j, by simpa [ruSGens, ruSWords] using hj, ?_⟩
  rw [List.getD_eq_getElem ruSGens 1 hj]

theorem getD_mem_ruSGens (j : ℕ) (hj : j < 4) : ruSGens.getD j 1 ∈ ruSGens := by
  rw [List.getD_eq_getElem ruSGens 1 (by simpa [ruSGens, ruSWords] using hj)]
  exact List.getElem_mem _

theorem ruCBlockHom_getD_mem (j : ℕ) (hj : j < 4) :
    ruCBlockHom ⟨ruSGens.getD j 1, ruSGens_memC' j⟩ ∈
      Subgroup.closure ({blockTau2, blockTau3} : Set (Perm (Fin 6))) := by
  obtain ⟨h0, h1, h2, h3⟩ := ruCBlockHom_ruSGens
  interval_cases j
  · rw [h0]
    exact Subgroup.one_mem _
  · rw [h1]
    exact Subgroup.one_mem _
  · rw [h2]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · rw [h3]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem ruS_block_image :
    (ruS.subgroupOf ruC).map ruCBlockHom =
      Subgroup.closure ({blockTau2, blockTau3} : Set (Perm (Fin 6))) := by
  obtain ⟨-, -, h2, h3⟩ := ruCBlockHom_ruSGens
  rw [ruS, map_subgroupOf_closure ruCBlockHom (X := {g | g ∈ ruSGens}) ruSGens_memC]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    obtain ⟨j, hj, rfl⟩ := mem_ruSGens_getD hx
    exact ruCBlockHom_getD_mem j hj
  · rw [Subgroup.closure_le]
    rintro t (rfl | rfl)
    · exact Subgroup.subset_closure ⟨⟨ruSGens.getD 2 1, getD_mem_ruSGens 2 (by norm_num)⟩, h2⟩
    · exact Subgroup.subset_closure ⟨⟨ruSGens.getD 3 1, getD_mem_ruSGens 3 (by norm_num)⟩, h3⟩

theorem eq_one_or_of_mem_zpowers_ruZ {x : Perm (Fin 4060)} (hx : x ∈ Subgroup.zpowers ruZ) :
    x = 1 ∨ x = ruZ := by
  have hord : orderOf ruZ = 2 := orderOf_eq_prime ruZ_sq ruZ_ne_one
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, hord]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    simp [h]
  · right
    simp [h]

theorem comm_ruZ_of_normalizes {g : Perm (Fin 4060)} (hg : ∀ s ∈ ruS, g * s * g⁻¹ ∈ ruS)
    (hg' : ∀ s ∈ ruS, g⁻¹ * s * g ∈ ruS) : g * ruZ = ruZ * g := by
  have hZS : ruZ ∈ ruS := ruJ_leS ruZ_memJ
  have hZc : ∀ s ∈ ruS, s * ruZ = ruZ * s := by
    intro s hs
    have h : ruZ ∈ (Subgroup.center ruS).map ruS.subtype := by
      rw [center_ruS]
      exact Subgroup.mem_zpowers ruZ
    obtain ⟨y, hy, hyz⟩ := h
    have := Subgroup.mem_center_iff.1 hy ⟨s, hs⟩
    have h2 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at h2
    rw [← hyz]
    exact h2
  have hu : g * ruZ * g⁻¹ ∈ (Subgroup.center ruS).map ruS.subtype := by
    refine ⟨⟨g * ruZ * g⁻¹, hg ruZ hZS⟩, Subgroup.mem_center_iff.2 fun s => ?_, rfl⟩
    apply Subtype.ext
    have h := hZc _ (hg' s s.2)
    show (s : Perm (Fin 4060)) * (g * ruZ * g⁻¹) = (g * ruZ * g⁻¹) * s
    calc (s : Perm (Fin 4060)) * (g * ruZ * g⁻¹)
        = g * ((g⁻¹ * s * g) * ruZ) * g⁻¹ := by group
      _ = g * (ruZ * (g⁻¹ * s * g)) * g⁻¹ := by rw [h]
      _ = (g * ruZ * g⁻¹) * s := by group
  rw [center_ruS] at hu
  rcases eq_one_or_of_mem_zpowers_ruZ hu with h | h
  · exfalso
    apply ruZ_ne_one
    have : ruZ = g⁻¹ * (g * ruZ * g⁻¹) * g := by group
    rw [this, h]
    group
  · rw [mul_inv_eq_iff_eq_mul] at h
    exact h

theorem ruS_selfNormalizing {g : Perm (Fin 4060)} (hgP : g ∈ ruP)
    (hg : ∀ s ∈ ruS, g * s * g⁻¹ ∈ ruS) (hg' : ∀ s ∈ ruS, g⁻¹ * s * g ∈ ruS) : g ∈ ruS := by
  have hgC : g ∈ ruC := by
    rw [ruC_eq_centralizer]
    exact ⟨hgP, Subgroup.mem_centralizer_singleton_iff.2 (comm_ruZ_of_normalizes hg hg')⟩
  set x : Perm (Fin 6) := ruCBlockHom ⟨g, hgC⟩ with hx
  have hxH : x ∈ Subgroup.closure ({blockPerm0, blockPerm1} : Set (Perm (Fin 6))) := by
    have h : x ∈ ruCBlockHom.range := ⟨⟨g, hgC⟩, rfl⟩
    have hr : ruCBlockHom.range =
        Subgroup.closure ({blockPerm0, blockPerm1} : Set (Perm (Fin 6))) := by
      rw [← ruCBlockHom_ruC0, ← ruCBlockHom_ruC1]
      exact range_closure_pair (g₀ := ruC0) (g₁ := ruC1) ruCBlockHom
    rwa [hr] at h
  have hxn : ∀ t ∈ ({blockTau2, blockTau3} : Set (Perm (Fin 6))),
      x * t * x⁻¹ ∈ Subgroup.closure ({blockTau2, blockTau3} : Set (Perm (Fin 6))) := by
    intro t ht
    rw [← ruS_block_image]
    obtain ⟨-, -, h2, h3⟩ := ruCBlockHom_ruSGens
    have hmem : ∀ j, j < 4 → (⟨g, hgC⟩ : ruC) * ⟨ruSGens.getD j 1, ruSGens_memC' j⟩ *
        (⟨g, hgC⟩ : ruC)⁻¹ ∈ ruS.subgroupOf ruC := by
      intro j hj
      rw [Subgroup.mem_subgroupOf]
      exact hg _ (ruSGens_getD_mem j)
    rcases ht with rfl | rfl
    · refine ⟨_, hmem 2 (by norm_num), ?_⟩
      rw [map_mul, map_mul, map_inv, h2]
    · refine ⟨_, hmem 3 (by norm_num), ?_⟩
      rw [map_mul, map_mul, map_inv, h3]
  have hxT := block_normalizer hxH hxn
  rw [← ruS_block_image] at hxT
  obtain ⟨s, hs, hsx⟩ := hxT
  have hker : (⟨g, hgC⟩ : ruC)⁻¹ * s ∈ ruCBlockHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hsx, ← hx, inv_mul_cancel]
  rw [ruCBlockHom_ker, Subgroup.mem_subgroupOf] at hker
  have hs' : (s : Perm (Fin 4060)) ∈ ruS := Subgroup.mem_subgroupOf.1 hs
  have hJS : g⁻¹ * (s : Perm (Fin 4060)) ∈ ruS := ruJ_leS hker
  have : g = (s : Perm (Fin 4060)) * (g⁻¹ * (s : Perm (Fin 4060)))⁻¹ := by group
  rw [this]
  exact ruS.mul_mem hs' (ruS.inv_mem hJS)

end CFSG.QuasithinUnique.Vol2Native.L239.RuPairs
