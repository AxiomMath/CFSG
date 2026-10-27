module

public import CFSG.ClassicalInvolution.Q3.Q3VF4SFrame
public import CFSG.ClassicalInvolution.Q3.Q3VFrameTrans

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3V.F4S

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.Q3.Q3V.Lift
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane stdPlane
  planeGroup_map_conj planeGroup_stdPlane mem_center_of_conj_mem_center isHyperbolicPlane_stdPlane
  longBlock longBlock_injective longInv)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

local notation "F₃" => GaloisField 3 1

section Conj

variable {m : ℕ} {X : Type*} [Group X]

theorem range_comp_conj (ψ : StatedSp m F₃ →* X) (γ : StatedSp m F₃) :
    (ψ.comp (MulAut.conj γ).toMonoidHom).range = ψ.range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨γ⁻¹ * x * γ, by simp [mul_assoc]⟩

theorem map_planeGroup_comp_conj (ψ : StatedSp m F₃ →* X) (γ : StatedSp m F₃)
    (P : Submodule F₃ (Fin m ⊕ Fin m → F₃)) :
    (planeGroup P).map (ψ.comp (MulAut.conj γ).toMonoidHom) =
      (planeGroup (P.map (Matrix.mulVecLin (mat m F₃ γ)))).map ψ := by
  rw [planeGroup_map_conj, Subgroup.map_map]

theorem map_planeGroup_comp_conj_inv (ψ : StatedSp m F₃ →* X) (γ : StatedSp m F₃)
    (P : Submodule F₃ (Fin m ⊕ Fin m → F₃)) :
    (planeGroup (P.map (Matrix.mulVecLin (mat m F₃ γ⁻¹)))).map
        (ψ.comp (MulAut.conj γ).toMonoidHom) = (planeGroup P).map ψ := by
  rw [← Subgroup.map_map, ← planeGroup_map_conj, ← Submodule.map_comp]
  have : (Matrix.mulVecLin (mat m F₃ γ)).comp (Matrix.mulVecLin (mat m F₃ γ⁻¹)) =
      LinearMap.id :=
    LinearMap.ext fun v => by
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.id_apply]
      exact Models.SymplecticPairs.mulVec_mulVec_inv γ v
  rw [this, Submodule.map_id]

end Conj

section Relabel

variable {m : ℕ} {G : Type} [Group G] {Ω : Set (Subgroup G)} {z : G}

@[expose] noncomputable def relabelDict (d : ShapeCDictR m Ω z) (γ : StatedSp m F₃) :
    ShapeCDictR m Ω z where
  ψ := d.ψ.comp (MulAut.conj γ).toMonoidHom
  ker_le := fun x hx => by
    have h1 : γ * x * γ⁻¹ ∈ d.ψ.ker := hx
    exact mem_center_of_conj_mem_center (d.ker_le h1)
  Q₀ := d.Q₀
  commutes := by
    rw [range_comp_conj]
    exact d.commutes
  mem_fam := fun P hP => by
    rw [map_planeGroup_comp_conj]
    exact d.mem_fam _ (Frame.isHyperbolicPlane_map γ hP)
  fam_cases := fun K' hK' => by
    rcases d.fam_cases K' hK' with h | ⟨P, hP, hKP⟩
    · exact Or.inl h
    · exact Or.inr ⟨P.map (Matrix.mulVecLin (mat m F₃ γ⁻¹)), Frame.isHyperbolicPlane_map γ⁻¹ hP,
        by rw [hKP, map_planeGroup_comp_conj_inv]⟩
  card_le := d.card_le
  gen := by
    rw [range_comp_conj]
    exact d.gen

@[expose] noncomputable def relabelCore {K : Subgroup G} (c : CCoreR m Ω K z) (γ : StatedSp m F₃) :
    CCoreR m Ω K z :=
  { c with d := relabelDict c.d γ }

@[expose] noncomputable def relabelLayer [Finite G] {K : Subgroup G} {c : CCoreR m Ω K z}
    (l : LayerR c) (γ : StatedSp m F₃) : LayerR (relabelCore c γ) where
  Θ := l.Θ.comp (MulAut.conj γ).toMonoidHom
  mem := fun g => l.mem _
  ker_le := fun x hx => by
    have h1 : γ * x * γ⁻¹ ∈ l.Θ.ker := hx
    exact mem_center_of_conj_mem_center (l.ker_le h1)
  comp_eq := MonoidHom.ext fun g => DFunLike.congr_fun l.comp_eq (γ * g * γ⁻¹)
  plane := fun P hP => by
    have hP' := Frame.isHyperbolicPlane_map γ hP
    have h1 := l.plane _ hP'
    have e1 : (planeGroup P).map (l.Θ.comp (MulAut.conj γ).toMonoidHom) =
        (planeGroup (P.map (Matrix.mulVecLin (mat m F₃ γ)))).map l.Θ :=
      map_planeGroup_comp_conj l.Θ γ P
    have e2 : (planeGroup P).map (relabelCore c γ).d.ψ =
        (planeGroup (P.map (Matrix.mulVecLin (mat m F₃ γ)))).map c.d.ψ :=
      map_planeGroup_comp_conj c.d.ψ γ P
    refine ⟨?_, ?_⟩
    · show (planeGroup P).map (l.Θ.comp (MulAut.conj γ).toMonoidHom) ∈ _
      rw [e1]
      exact h1.1
    · show locImg Ω z ((planeGroup P).map (l.Θ.comp (MulAut.conj γ).toMonoidHom)) =
        (planeGroup P).map (relabelCore c γ).d.ψ
      rw [e1, e2]
      exact h1.2

end Relabel

section LocLift

variable {m : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem layerIsLocLift {c : CCoreR m Ω K z} (l : LayerR c) : IsLocLift m Ω K l.Θ where
  ker_le := l.ker_le
  comm := by
    rintro _ ⟨s, rfl⟩ b hb
    exact l.commutes_K s hb
  plane_mem := fun P hP => (l.plane P hP).1.1
  members := fun M hM hMK hcomm => by
    have hMz : M ∈ centralizingMembers Ω {z} :=
      ⟨hM, fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hcomm x hx z c.hz.mem)⟩
    obtain ⟨P, hP, hMP⟩ := l.exists_plane_of_ne hMz hMK
    exact ⟨P, hP, hMP⟩

theorem layerNotMemPlane {c : CCoreR m Ω K z} (l : LayerR c)
    {P : Submodule F₃ (Fin m ⊕ Fin m → F₃)} (hP : IsHyperbolicPlane P) :
    z ∉ (planeGroup P).map l.Θ := fun hz =>
  false_of_involution_mem_plane_memberR c.hm c.d (le_centralizingLayer (l.plane P hP).1) hz
    c.hz.orderOf_eq_two hP (l.plane P hP).2

end LocLift

theorem eq_map_longInv_of_involution {X : Type*} [Group X] {Θ : StatedSp 3 F₃ →* X}
    (hker : Θ.ker ≤ Subgroup.center (StatedSp 3 F₃)) {k : Fin 3} {w : X}
    (hw : w ∈ (planeGroup (stdPlane F₃ 3 k)).map Θ) (hw2 : orderOf w = 2) :
    w = Θ (longInv F₃ 3 k) := by
  obtain ⟨g, hg, rfl⟩ := hw
  rw [planeGroup_stdPlane] at hg
  obtain ⟨s, rfl⟩ := hg
  have hmem : longBlock F₃ 3 k (s * s) ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, ← pow_two]
    have := pow_orderOf_eq_one (Θ (longBlock F₃ 3 k s))
    rwa [hw2] at this
  have hrange : longBlock F₃ 3 k (s * s) ∈ planeGroup (stdPlane F₃ 3 k) := by
    rw [planeGroup_stdPlane]
    exact ⟨_, rfl⟩
  have h1 : longBlock F₃ 3 k (s * s) = 1 :=
    Lift.planeGroup_central_eq_oneR (by norm_num) (isHyperbolicPlane_stdPlane k) hrange
      (hker hmem)
  have hss : s * s = 1 := longBlock_injective k (h1.trans (map_one _).symm)
  rcases sl2_sq_eq_one Q3Z.gf3_two_ne_zero hss with h | h
  · exfalso
    subst h
    rw [map_one, map_one] at hw2
    rw [orderOf_one] at hw2
    omega
  · subst h
    rfl

end CFSG.ClassicalInvolution.Q3.Q3V.F4S
