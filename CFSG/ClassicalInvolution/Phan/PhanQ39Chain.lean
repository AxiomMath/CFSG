module

public import CFSG.ClassicalInvolution.Phan.PhanG9Fib

public section

namespace CFSG.ClassicalInvolution.PhanQ


open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section Frames

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {S : PhanFamilyD4 K p f G} {e' : Fin 3 → Fin 4} {ψ : Su K p f 4 →* G}

structure ChainCtx (S : PhanFamilyD4 K p f G) (e' : Fin 3 → Fin 4) (ψ : Su K p f 4 →* G) :
    Prop where
  hK : Nat.card K = (p ^ f) ^ 2
  hq : 5 ≤ p ^ f
  hg : GoodFamily S
  h2 : (2 : K) ≠ 0
  he0 : e' 0 = 0
  hch : PhanChain S e' ψ

theorem ChainCtx.hσ (C : ChainCtx S e' ψ) : IsUnitaryInvolution (unitaryInvolution K p f) :=
  isUnitaryInvolution_unitaryInvolution C.hK

theorem ChainCtx.hT (C : ChainCtx S e' ψ) :
    (torus (unitaryInvolution K p f) 4).map ψ ≤ torusSub S := by
  rintro _ ⟨t, ht, rfl⟩
  exact C.hch.psi_mem_torusSub C.hg ht

@[expose] noncomputable def ChainCtx.Phi (C : ChainCtx S e' ψ)
    (c : Frame (unitaryInvolution K p f) 4) : G ⧸ torusSub S :=
  cosetMap ψ (torusSub S) (torus (unitaryInvolution K p f) 4) C.hT
    ((frameEquivQuotient (n := 3) C.hσ).symm c)

theorem ChainCtx.Phi_smul (C : ChainCtx S e' ψ) (h : Su K p f 4) :
    C.Phi (h • stdFrame (unitaryInvolution K p f) 4) = ((ψ h : G) : G ⧸ torusSub S) := by
  have : (frameEquivQuotient (n := 3) C.hσ).symm (h • stdFrame (unitaryInvolution K p f) 4) =
      (h : Su K p f 4 ⧸ torus (unitaryInvolution K p f) 4) := by
    rw [Equiv.symm_apply_eq, frameEquivQuotient_mk]
  rw [ChainCtx.Phi, this, cosetMap_mk]

theorem ChainCtx.Phi_inj (C : ChainCtx S e' ψ) {c c' : Frame (unitaryInvolution K p f) 4}
    (h : C.Phi c = C.Phi c') : c = c' := by
  obtain ⟨g, rfl⟩ := exists_smul_stdFrame C.hσ c
  obtain ⟨g', rfl⟩ := exists_smul_stdFrame C.hσ c'
  rw [C.Phi_smul, C.Phi_smul, QuotientGroup.eq] at h
  have h1 : ψ (g⁻¹ * g') ∈ torusSub S := by rwa [map_mul, map_inv]
  have h2 := C.hch.mem_torus_of_psi_mem C.hK C.hg C.h2 h1
  have h3 : (g⁻¹ * g') • stdFrame (unitaryInvolution K p f) 4 =
      stdFrame (unitaryInvolution K p f) 4 := (smul_stdFrame_eq_iff _).2 h2
  rw [mul_smul, inv_smul_eq_iff] at h3
  exact h3.symm

theorem ChainCtx.Phi_adj (C : ChainCtx S e' ψ) {i : Fin 3}
    {c c' : Frame (unitaryInvolution K p f) 4}
    (h : (frameSystem (unitaryInvolution K p f) 3).adj i c c') :
    (phanSystem S).adj (e' i) (C.Phi c) (C.Phi c') := by
  obtain ⟨g, rfl⟩ := exists_smul_stdFrame C.hσ c
  obtain ⟨g', rfl⟩ := exists_smul_stdFrame C.hσ c'
  rw [C.Phi_smul, C.Phi_smul, phanSystem_adj_mk, ← map_inv, ← map_mul]
  have hmem := (adj_smul_stdFrame_smul_iff i g g').1 h
  have hle : torus (unitaryInvolution K p f) 4 ⊔ (blockEmb2 K p f 3 i).range ≤
      (parab S {e' i}).comap ψ := by
    refine sup_le (fun t ht => ?_) ?_
    · exact torusSub_le_parab {e' i} (C.hch.psi_mem_torusSub C.hg ht)
    · rintro _ ⟨A, rfl⟩
      obtain ⟨B, hB⟩ := C.hch.le_range i A
      show ψ (blockEmb2 K p f 3 i A) ∈ parab S {e' i}
      rw [← hB]
      exact Lsup_le_parab {e' i} (ι_mem_Lsup (Set.mem_singleton _) B)
  exact hle hmem

theorem ChainCtx.exists_adj_Phi (C : ChainCtx S e' ψ) {i : Fin 3}
    (c : Frame (unitaryInvolution K p f) 4) {g : G ⧸ torusSub S}
    (h : (phanSystem S).adj (e' i) (C.Phi c) g) :
    ∃ c', (frameSystem (unitaryInvolution K p f) 3).adj i c c' ∧ C.Phi c' = g := by
  obtain ⟨h₀, rfl⟩ := exists_smul_stdFrame C.hσ c
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective g
  rw [C.Phi_smul, phanSystem_adj_mk] at h
  obtain ⟨r, hr, t, ht, hrt⟩ := exists_mul_of_mem_parab C.hK (e' i) h
  obtain ⟨A, hA⟩ := C.hch.range_le i r hr
  refine ⟨(h₀ * blockEmb2 K p f 3 i A) • stdFrame (unitaryInvolution K p f) 4, ?_, ?_⟩
  · refine (adj_smul_stdFrame_smul_iff i h₀ (h₀ * blockEmb2 K p f 3 i A)).2 ?_
    rw [inv_mul_cancel_left]
    exact Subgroup.mem_sup_right ⟨A, rfl⟩
  · rw [C.Phi_smul, map_mul, hA, QuotientGroup.eq]
    have : (ψ h₀ * r)⁻¹ * a = t := by
      calc (ψ h₀ * r)⁻¹ * a = r⁻¹ * ((ψ h₀)⁻¹ * a) := by group
        _ = t := by rw [hrt]; group
    rw [this]
    exact ht

theorem ChainCtx.isTypeMorphism (C : ChainCtx S e' ψ) :
    IsTypeMorphism (frameSystem (unitaryInvolution K p f) 3) (phanSystem S) e' C.Phi :=
  fun _ _ _ h => C.Phi_adj h

theorem ChainCtx.mem_residue_Phi (C : ChainCtx S e' ψ) {J : Set (Fin 3)}
    {c c' : Frame (unitaryInvolution K p f) 4}
    (h : c' ∈ (frameSystem (unitaryInvolution K p f) 3).residue J c) :
    C.Phi c' ∈ (phanSystem S).residue (e' '' J) (C.Phi c) := by
  obtain ⟨γ, hγ, hend⟩ := mem_residue_iff_exists_isJGallery.1 h
  refine mem_residue_iff_exists_isJGallery.2 ⟨galleryMapT e' C.Phi γ,
    ⟨C.isTypeMorphism.isGallery hγ.1, ?_⟩, ?_⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := (mem_galleryType_galleryMapT e' C.Phi γ j).1 hj
    exact ⟨i, hγ.2 i hi, rfl⟩
  · rw [galleryEnd_galleryMapT, hend]

theorem ChainCtx.e'_mem (C : ChainCtx S e' ψ) {j : Fin 3} (hj : j ≠ 0) :
    e' j ∈ ({1, 2, 3} : Set (Fin 4)) := by
  have hne : e' j ≠ 0 := fun h => hj (C.hch.inj (h.trans C.he0.symm))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  revert hne
  generalize e' j = x
  intro hne
  fin_cases x <;> simp_all

theorem ChainCtx.ptMap_Phi_eq (C : ChainCtx S e' ψ) {c c' : Frame (unitaryInvolution K p f) 4}
    (h : c.line 0 = c'.line 0) : ptMap S (C.Phi c) = ptMap S (C.Phi c') := by
  have hq3 : 3 ≤ p ^ f := by have := C.hq; omega
  have hres : c' ∈ (frameSystem (unitaryInvolution K p f) 3).residue (typeInt 3 1 3) c := by
    refine (mem_residue_typeInt_iff C.hσ C.hK hq3 (a := 1) (b := 3) (by omega) (by omega)).2 ?_
    intro k hk
    have hk0 : k = 0 := by
      rw [mem_posInt] at hk
      ext
      simp only [Fin.val_zero]
      omega
    subst hk0
    exact h.symm
  have h1 := C.mem_residue_Phi hres
  refine (ptMap_eq_iff _ _).2 (residue_mono ?_ _ h1)
  rintro _ ⟨j, hj, rfl⟩
  refine C.e'_mem fun h0 => ?_
  rw [mem_typeInt] at hj
  have := congrArg Fin.val h0
  simp at this
  omega

end Frames

end CFSG.ClassicalInvolution.PhanQ
