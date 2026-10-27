module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCentralizerTUStd
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotPositionFacts

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  RootOps

local instance f4CentralizerTUNeZeroRank' : NeZero Tag.F4.rank := ⟨by decide⟩

noncomputable abbrev wD : WeylGroup .F4 := weylOfWord .F4 [0, 2, 1, 3, 2, 1, 0]

section Roots


theorem wD_rootR_rootS : wD • rootR = root0122 ∧ wD • rootS = root0121 :=
  weylOfWord_rootR_rootS_mem_C3Roots

theorem image_smul_perp (w : WeylGroup .F4) (L : List (Fin (Tag.rank .F4) → ℤ)) :
    (fun γ => w • γ) '' {γ | IsRoot .F4 γ ∧ ∀ δ ∈ L, iform γ δ = 0} =
      {γ | IsRoot .F4 γ ∧ ∀ δ ∈ L.map (fun δ => w • δ), iform γ δ = 0} := by
  ext γ
  constructor
  · rintro ⟨β, ⟨hβ, hβL⟩, rfl⟩
    refine ⟨IsRoot.smul hβ w, fun δ hδ => ?_⟩
    obtain ⟨δ', hδ', rfl⟩ := List.mem_map.1 hδ
    rw [iform_smul]
    exact hβL δ' hδ'
  · rintro ⟨hγ, hγL⟩
    refine ⟨w⁻¹ • γ, ⟨IsRoot.smul hγ w⁻¹, fun δ hδ => ?_⟩, smul_inv_smul w γ⟩
    have h := hγL (w • δ) (List.mem_map.2 ⟨δ, hδ, rfl⟩)
    rwa [← iform_smul w⁻¹, inv_smul_smul] at h

theorem c3LeviRoots_eq_perp :
    c3LeviRoots = {γ | IsRoot .F4 γ ∧ ∀ δ ∈ [rootR], iform γ δ = 0} := by
  ext γ
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, Set.mem_ofPred_eq]
  rw [mem_c3LeviRoots, iform_comm, iform_rootR]
  exact and_congr_right fun _ => by
    constructor
    · intro h
      change γ 0 = 0 at h
      rw [h, mul_zero]
    · intro h
      change γ 0 = 0
      omega

theorem b3LeviRoots_eq_perp :
    b3LeviRoots = {γ | IsRoot .F4 γ ∧ ∀ δ ∈ [rootS], iform γ δ = 0} := by
  ext γ
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq, Set.mem_ofPred_eq]
  rw [mem_b3LeviRoots, iform_comm, iform_rootS]
  rfl

theorem b2LeviRoots_eq_perp :
    b2LeviRoots = {γ | IsRoot .F4 γ ∧ ∀ δ ∈ [rootR, rootS], iform γ δ = 0} := by
  ext γ
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Set.mem_ofPred_eq]
  rw [mem_b2LeviRoots, iform_comm γ rootR, iform_rootR, iform_comm γ rootS, iform_rootS]
  exact and_congr_right fun _ => and_congr_left fun _ => by omega

theorem image_wD_c3LeviRoots : (fun γ => wD • γ) '' c3LeviRoots = phi0 .t := by
  rw [c3LeviRoots_eq_perp, image_smul_perp]
  simp only [List.map_cons, List.map_nil, wD_rootR_rootS.1]
  rfl

theorem image_wD_b3LeviRoots : (fun γ => wD • γ) '' b3LeviRoots = phi0 .u := by
  rw [b3LeviRoots_eq_perp, image_smul_perp]
  simp only [List.map_cons, List.map_nil, wD_rootR_rootS.2]
  rfl

theorem image_wD_b2LeviRoots : (fun γ => wD • γ) '' b2LeviRoots = phi0 .tu := by
  rw [b2LeviRoots_eq_perp, image_smul_perp]
  simp only [List.map_cons, List.map_nil, wD_rootR_rootS.1, wD_rootR_rootS.2]
  rfl

end Roots

section Conj


variable (K : Type) [Field K]

@[expose] noncomputable def nD : adjointGroup .F4 K :=
  ⟨canonicalRep (coxeterSystem .F4) K wD, canonicalRep_mem_adjointGroup _ K wD⟩

variable {K}


theorem conj_nD_xC [CharP K 2] {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) (c : K) :
    MulAut.conj (nD K) (xC K γ c) = xC K (wD • γ) c :=
  Subtype.ext (canonicalRep_mul_pinnedX_mul_inv_of_two CharTwo.two_eq_zero wD hγ c)

theorem map_conj_nD_rootSpan {S : Set (Fin (Tag.rank .F4) → ℤ)} (hS : ∀ γ ∈ S, IsRoot .F4 γ) :
    ((rootSpan .F4 K S).subgroupOf (adjointGroup .F4 K)).map
        (MulAut.conj (nD K)).toMonoidHom =
      (rootSpan .F4 K ((fun γ => wD • γ) '' S)).subgroupOf (adjointGroup .F4 K) := by
  rw [← (canonical_weyl_root_transport .F4 K).1 wD S hS]
  ext x
  simp only [mem_map, mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, rootSpan_le_adjointGroup K S hy⟩, hy, Subtype.ext hyx⟩

end Conj

section F3

variable {K : Type} [Field K]


theorem conj_nD_zT_zU [CharP K 2] :
    MulAut.conj (nD K) (zT K) = yRep K .t ∧ MulAut.conj (nD K) (zU K) = yRep K .u ∧
      MulAut.conj (nD K) (zT K * zU K) = yRep K .tu := by
  have hT : MulAut.conj (nD K) (zT K) = yRep K .t := by
    have e : zT K = xC K rootR 1 := Subtype.ext (by
      change f4x K 47 1 = pinnedX .F4 K rootR 1
      rw [f4x, orbitCertRoot_47_44.1])
    rw [e, conj_nD_xC isRoot_rootR, wD_rootR_rootS.1]
    rfl
  have hU : MulAut.conj (nD K) (zU K) = yRep K .u := by
    have e : zU K = xC K rootS 1 := Subtype.ext (by
      change f4x K 44 1 = pinnedX .F4 K rootS 1
      rw [f4x, orbitCertRoot_47_44.2])
    rw [e, conj_nD_xC isRoot_rootS, wD_rootR_rootS.2]
    rfl
  refine ⟨hT, hU, ?_⟩
  rw [map_mul, hT, hU]
  rfl

theorem map_conj_nD_levis :
    (C3Levi K).map (MulAut.conj (nD K)).toMonoidHom = levi K .t ∧
      (B3Levi K).map (MulAut.conj (nD K)).toMonoidHom = levi K .u ∧
      (B2Levi K).map (MulAut.conj (nD K)).toMonoidHom = levi K .tu := by
  refine ⟨?_, ?_, ?_⟩
  · rw [C3Levi, map_conj_nD_rootSpan (fun γ hγ => hγ.1), image_wD_c3LeviRoots]
    rfl
  · rw [B3Levi, map_conj_nD_rootSpan (fun γ hγ => hγ.1), image_wD_b3LeviRoots]
    rfl
  · rw [B2Levi, map_conj_nD_rootSpan (fun γ hγ => (mem_b2LeviRoots.1 hγ).1),
      image_wD_b2LeviRoots]
    rfl

theorem factF3 [Finite K] [CharP K 2] : FactF3 K := by
  obtain ⟨hT, hU, hTU⟩ := conj_nD_zT_zU (K := K)
  obtain ⟨hlT, hlU, hlTU⟩ := map_conj_nD_levis (K := K)
  intro κ
  cases κ with
  | t =>
    have h := (isTwoRadicalDecomp_zT (K := K)).map (MulAut.conj (nD K))
    rw [hT, hlT] at h
    exact ⟨_, h⟩
  | u =>
    have h := (isTwoRadicalDecomp_zU (K := K)).map (MulAut.conj (nD K))
    rw [hU, hlU] at h
    exact ⟨_, h⟩
  | tu =>
    have h := (isTwoRadicalDecomp_zTU (K := K)).map (MulAut.conj (nD K))
    rw [hTU, hlTU] at h
    exact ⟨_, h⟩

end F3

end CFSG.SeitzReduction.F4Pilot
