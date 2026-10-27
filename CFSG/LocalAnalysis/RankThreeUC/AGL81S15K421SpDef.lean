module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinGL
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinCG

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421MonoProof

@[expose] def Mono81.restrict {G : Type} [Group G] (D : Mono81 G) (H : Subgroup G)
    (ha : ∀ x : V3, D.av x ∈ H) (hs : D.s ∈ H) (hf : D.f ∈ H) : Mono81 ↥H where
  a := D.a.codRestrict H (fun x => ha (Multiplicative.toAdd x))
  s := ⟨D.s, hs⟩
  a_inj := fun x y h => D.a_inj (congrArg Subtype.val h)
  s_pow := Subtype.ext D.s_pow
  s_conj := fun x => Subtype.ext (D.s_conj x)
  s_ne_a := fun x => ⟨fun h => (D.s_ne_a x).1 (congrArg Subtype.val h), fun h =>
    (D.s_ne_a x).2 (congrArg Subtype.val h)⟩
  f := ⟨D.f, hf⟩
  f_s := by
    obtain ⟨x, hx⟩ := D.f_s
    exact ⟨x, Subtype.ext hx⟩
  f_diag := fun c => Subtype.ext (D.f_diag c)

end K421MonoProof

namespace K421SpProof

open Matrix K421MonoProof K421OrbProof K421LinProof K421CGProof

@[expose] def JI : Matrix Idx Idx F2 := Matrix.of fun i j => if i.1 = j.1 then Jm i.2 j.2 else 0

@[expose] def SympF2 (M : Matrix Idx Idx F2) : Prop := Mᵀ * JI * M = JI

instance (M : Matrix Idx Idx F2) : Decidable (SympF2 M) := by unfold SympF2; infer_instance

theorem symp_aMat : ∀ x : V3, SympF2 (aMat x) := by
  unfold SympF2 JI aMat cpow Cm Jm
  decide +kernel

theorem symp_sMat : SympF2 sMat := by
  unfold SympF2 JI sMat Jm
  decide +kernel

theorem symp_fMat : SympF2 fMat := by
  unfold SympF2 JI fMat Jm Cm
  decide +kernel

theorem symp_nMat : ∀ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool), SympF2 (pMat π * jMat ε) := by
  unfold SympF2 JI pMat jMat Jm
  decide +kernel

@[expose] def SpF2 : Subgroup (GL Idx F2) := CFSG.Open.StatedAPI.gramIsometry JI

theorem aGL_mem (x : V3) : aGL x ∈ SpF2 := symp_aMat x

theorem sGL_mem : sGL ∈ SpF2 := symp_sMat

theorem fGL_mem : fGL ∈ SpF2 := symp_fMat

theorem nGL_mem (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) : nGL π ε ∈ SpF2 := symp_nMat π ε

@[expose] noncomputable def monoF2 : Mono81 ↥SpF2 :=
  mono0.restrict SpF2 (fun x => aGL_mem x) sGL_mem fGL_mem

theorem signedPerms_monoF2 : SignedPerms monoF2 := fun π ε => by
  refine ⟨⟨nGL π ε, nGL_mem π ε⟩, fun x => ?_⟩
  apply Subtype.ext
  show nGL π ε * aGL x * (nGL π ε)⁻¹ = aGL (act π ε x)
  rw [mul_inv_eq_iff_eq_mul]
  exact Units.ext (nMat_aMat π ε x)

section BaseChange

variable (F : Type) [Field F] [CharP F 2]

@[expose] def ι2 : F2 →+* F := ZMod.castHom (dvd_refl 2) F

@[expose] def bc (M : Matrix Idx Idx F2) : Matrix Idx Idx F := M.map (ι2 F)

@[expose] def JF : Matrix Idx Idx F := bc F JI

@[expose] def SpI : Subgroup (GL Idx F) := CFSG.Open.StatedAPI.gramIsometry (JF F)

theorem mem_SpI_iff (g : GL Idx F) :
    g ∈ SpI F ↔ (g : Matrix Idx Idx F)ᵀ * JF F * (g : Matrix Idx Idx F) = JF F := Iff.rfl

theorem bc_mul (M N : Matrix Idx Idx F2) : bc F (M * N) = bc F M * bc F N :=
  (Matrix.map_mul (f := ι2 F))

theorem bc_transpose (M : Matrix Idx Idx F2) : bc F Mᵀ = (bc F M)ᵀ := (Matrix.transpose_map).symm

theorem bc_one : bc F (1 : Matrix Idx Idx F2) = 1 := Matrix.map_one (ι2 F) (map_zero _) (map_one _)

@[expose] def bcGL : GL Idx F2 →* GL Idx F :=
  Units.map
    { toFun := fun M => bc F M
      map_one' := bc_one F
      map_mul' := bc_mul F }

theorem bcGL_injective : Function.Injective (bcGL F) := by
  apply Units.map_injective
  intro M N h
  exact Matrix.map_injective (RingHom.injective (ι2 F)) h

theorem bcGL_mem {g : GL Idx F2} (hg : g ∈ SpF2) : bcGL F g ∈ SpI F := by
  have h : (g : Matrix Idx Idx F2)ᵀ * JI * (g : Matrix Idx Idx F2) = JI := hg
  have h2 := congrArg (bc F) h
  rw [bc_mul, bc_mul, bc_transpose] at h2
  exact h2

@[expose] def spBase : ↥SpF2 →* ↥(SpI F) :=
  ((bcGL F).comp SpF2.subtype).codRestrict (SpI F) (fun g => bcGL_mem F g.2)

theorem spBase_injective : Function.Injective (spBase F) := fun g h hgh =>
  Subtype.ext (bcGL_injective F (congrArg Subtype.val hgh))

@[expose] noncomputable def monoSp : Mono81 ↥(SpI F) := monoF2.map (spBase F) (spBase_injective F)

theorem signedPerms_monoSp : SignedPerms (monoSp F) :=
  signedPerms_monoF2.map (spBase F) (spBase_injective F)

end BaseChange

end K421SpProof

end CFSG.LocalAnalysis.RankThreeUC.S15
