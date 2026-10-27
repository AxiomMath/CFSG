module

public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow
public import CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameSylowOvergroups

open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow
open CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration
open CFSG.GH74.GLS.IVK.Proofs2.Sp48

section Generic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 5) V] [FiniteDimensional (ZMod 5) V]
  {Q : QuadraticForm (ZMod 5) V}

theorem zmod5_sq_add_sq_eq_one (a b : ZMod 5) (h : a ^ 2 + b ^ 2 = 1) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
  have h' : ∀ a b : ZMod 5, a ^ 2 + b ^ 2 = 1 →
      (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
    decide
  exact h' a b h

theorem mem_signedFrame_iff (F : FrameData Q) (x : V) :
    x ∈ (Set.range F.e ∪ -(Set.range F.e)) ↔ (∃ i, x = F.e i) ∨ (∃ i, -x = F.e i) := by
  simp [eq_comm]

theorem signedFrame_finite (F : FrameData Q) :
    (Set.range F.e ∪ -(Set.range F.e)).Finite :=
  (Set.finite_range F.e).union (Set.finite_range F.e).neg

theorem neg_mem_signedFrame (F : FrameData Q) {x : V}
    (hx : x ∈ (Set.range F.e ∪ -(Set.range F.e))) :
    -x ∈ (Set.range F.e ∪ -(Set.range F.e)) := by
  rw [mem_signedFrame_iff] at hx ⊢
  rcases hx with ⟨i, rfl⟩ | ⟨i, hi⟩
  · right; exact ⟨i, by simp⟩
  · left; exact ⟨i, by simpa using hi⟩

theorem signed_pair_of_basis (F : FrameData Q) {i j : Fin 5}
    {a b : ZMod 5} (h : a ^ 2 + b ^ 2 = 1) :
    a • F.e i + b • F.e j ∈ (Set.range F.e ∪ -(Set.range F.e)) := by
  rw [mem_signedFrame_iff]
  rcases zmod5_sq_add_sq_eq_one a b h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
  · left
    refine ⟨i, ?_⟩
    rw [ha, hb]
    simp
  · right
    refine ⟨i, ?_⟩
    rw [ha, hb]
    rw [show (-1 : ZMod 5) • F.e i = -F.e i from neg_one_smul (ZMod 5) (F.e i)]
    simp
  · left
    refine ⟨j, ?_⟩
    rw [ha, hb]
    simp
  · right
    refine ⟨j, ?_⟩
    rw [ha, hb]
    rw [show (-1 : ZMod 5) • F.e j = -F.e j from neg_one_smul (ZMod 5) (F.e j)]
    simp

theorem beta_e0_mem (F : FrameData Q) (d1 d2 : O2 (ZMod 5)) :
    F.beta d1 d2 (F.e 0) ∈ (Set.range F.e ∪ -(Set.range F.e)) := by
  rw [FrameData.beta_e_zero]
  refine signed_pair_of_basis F (i := 0) (j := 1) ?_
  simpa [pow_two] using FrameData.O2_entry_00 (K := ZMod 5) d1

theorem beta_e1_mem (F : FrameData Q) (d1 d2 : O2 (ZMod 5)) :
    F.beta d1 d2 (F.e 1) ∈ (Set.range F.e ∪ -(Set.range F.e)) := by
  rw [FrameData.beta_e_one]
  refine signed_pair_of_basis F (i := 0) (j := 1) ?_
  simpa [pow_two] using FrameData.O2_entry_11 (K := ZMod 5) d1

theorem beta_e2_mem (F : FrameData Q) (d1 d2 : O2 (ZMod 5)) :
    F.beta d1 d2 (F.e 2) ∈ (Set.range F.e ∪ -(Set.range F.e)) := by
  rw [FrameData.beta_e_two]
  refine signed_pair_of_basis F (i := 2) (j := 3) ?_
  simpa [pow_two] using FrameData.O2_entry_00 (K := ZMod 5) d2

theorem beta_e3_mem (F : FrameData Q) (d1 d2 : O2 (ZMod 5)) :
    F.beta d1 d2 (F.e 3) ∈ (Set.range F.e ∪ -(Set.range F.e)) := by
  rw [FrameData.beta_e_three]
  refine signed_pair_of_basis F (i := 2) (j := 3) ?_
  simpa [pow_two] using FrameData.O2_entry_11 (K := ZMod 5) d2

theorem beta_e4_mem (F : FrameData Q) (d1 d2 : O2 (ZMod 5)) :
    F.beta d1 d2 (F.e 4) ∈ (Set.range F.e ∪ -(Set.range F.e)) := by
  rw [FrameData.beta_e_four]
  set x : ZMod 5 := (((d1 : GL (Fin 2) (ZMod 5)) : Matrix (Fin 2) (Fin 2) (ZMod 5)).det *
    (((d2 : GL (Fin 2) (ZMod 5)) : Matrix (Fin 2) (Fin 2) (ZMod 5)).det))
  have hx : x ^ 2 = 1 := by
    dsimp [x]
    rw [pow_two, mul_mul_mul_comm, FrameData.O2_det_sq (K := ZMod 5) d1,
      FrameData.O2_det_sq (K := ZMod 5) d2, one_mul]
  have h := signed_pair_of_basis F (i := 4) (j := 0) (a := x) (b := 0) ?_
  · simpa [x] using h
  · simpa using hx

theorem beta_mapsTo_signedFrame (F : FrameData Q) (d1 d2 : O2 (ZMod 5)) :
    Set.MapsTo (F.beta d1 d2) (Set.range F.e ∪ -(Set.range F.e))
      (Set.range F.e ∪ -(Set.range F.e)) := by
  intro x hx
  rw [mem_signedFrame_iff] at hx
  rcases hx with ⟨i, rfl⟩ | ⟨i, hi⟩
  · fin_cases i
    · exact beta_e0_mem F d1 d2
    · exact beta_e1_mem F d1 d2
    · exact beta_e2_mem F d1 d2
    · exact beta_e3_mem F d1 d2
    · exact beta_e4_mem F d1 d2
  · have hxi : x = -F.e i := by rw [← hi, neg_neg]
    rw [hxi, map_neg]
    apply neg_mem_signedFrame
    fin_cases i
    · exact beta_e0_mem F d1 d2
    · exact beta_e1_mem F d1 d2
    · exact beta_e2_mem F d1 d2
    · exact beta_e3_mem F d1 d2
    · exact beta_e4_mem F d1 d2

theorem s_e_mem (F : FrameData Q) (i : Fin 5) :
    F.s (F.e i) ∈ (Set.range F.e ∪ -(Set.range F.e)) := by
  rw [mem_signedFrame_iff]
  fin_cases i
  · left; exact ⟨2, by simp [FrameData.s_e]⟩
  · left; exact ⟨3, by simp [FrameData.s_e]⟩
  · left; exact ⟨0, by simp [FrameData.s_e]⟩
  · left; exact ⟨1, by simp [FrameData.s_e]⟩
  · left; exact ⟨4, by simp [FrameData.s_e]⟩

theorem s_mapsTo_signedFrame (F : FrameData Q) :
    Set.MapsTo F.s (Set.range F.e ∪ -(Set.range F.e))
      (Set.range F.e ∪ -(Set.range F.e)) := by
  intro x hx
  rw [mem_signedFrame_iff] at hx
  rcases hx with ⟨i, rfl⟩ | ⟨i, hi⟩
  · exact s_e_mem F i
  · have hxi : x = -F.e i := by rw [← hi, neg_neg]
    rw [hxi, map_neg]
    exact neg_mem_signedFrame F (s_e_mem F i)

noncomputable def frameStabilizerSO (F : FrameData Q) : Subgroup Q.specialOrthogonalWithin :=
  @MulAction.stabilizer Q.specialOrthogonalWithin (Set V) _
    (Set.mulActionSet) (Set.range F.e ∪ -(Set.range F.e))

noncomputable def frameStabilizerO (F : FrameData Q) :
    Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) :=
  @MulAction.stabilizer (TauCeti.QuadraticMap.orthogonalGroup Q) (Set V) _
    (Set.mulActionSet) (Set.range F.e ∪ -(Set.range F.e))

theorem betaSO_mem_frameStabilizerSO (F : FrameData Q) (d1 d2 : O2 (ZMod 5)) :
    F.betaSO d1 d2 ∈ frameStabilizerSO F := by
  unfold frameStabilizerSO
  rw [MulAction.mem_stabilizer_set' (signedFrame_finite F)]
  intro x hx
  simpa [Subgroup.smul_def, LinearEquiv.smul_def, FrameData.betaSO, FrameData.betaO] using
    (beta_mapsTo_signedFrame F d1 d2 hx)

theorem sSO_mem_frameStabilizerSO (F : FrameData Q) :
    F.sSO ∈ frameStabilizerSO F := by
  unfold frameStabilizerSO
  rw [MulAction.mem_stabilizer_set' (signedFrame_finite F)]
  intro x hx
  simpa [Subgroup.smul_def, LinearEquiv.smul_def, FrameData.sSO, FrameData.sO] using
    (s_mapsTo_signedFrame F hx)

theorem betaBase_le_frameStabilizerSO (F : FrameData Q) (D : Subgroup (O2 (ZMod 5))) :
    betaBase F D ≤ frameStabilizerSO F := by
  intro g hg
  rw [betaBase] at hg
  rcases Subgroup.mem_map.mp hg with ⟨p, hp, rfl⟩
  exact betaSO_mem_frameStabilizerSO F p.1 p.2

theorem swapSub_le_frameStabilizerSO (F : FrameData Q) :
    swapSub F ≤ frameStabilizerSO F := by
  rw [swapSub, Subgroup.zpowers_le]
  exact sSO_mem_frameStabilizerSO F

theorem wreathSub_le_frameStabilizerSO (F : FrameData Q) (D : Subgroup (O2 (ZMod 5))) :
    wreathSub F D ≤ frameStabilizerSO F := by
  rw [wreathSub]
  exact sup_le (betaBase_le_frameStabilizerSO F D) (swapSub_le_frameStabilizerSO F)

theorem wreathSub_map_le_frameStabilizerO (F : FrameData Q) (D : Subgroup (O2 (ZMod 5))) :
    (wreathSub F D).map (Q.specialOrthogonalWithin).subtype ≤ frameStabilizerO F := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  unfold frameStabilizerO
  rw [MulAction.mem_stabilizer_set' (signedFrame_finite F)]
  intro b hb
  have hy' := (MulAction.mem_stabilizer_set' (signedFrame_finite F)).mp
    (wreathSub_le_frameStabilizerSO F D hy)
  simpa [Subgroup.smul_def, LinearEquiv.smul_def] using hy' hb

theorem wreathSub_map_le_centralizer_zO (F : FrameData Q) (D : Subgroup (O2 (ZMod 5))) :
    (wreathSub F D).map (Q.specialOrthogonalWithin).subtype ≤
      Subgroup.centralizer ({F.zO} : Set (TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  have h := wreathSub_le_centralizer_zSO F D hy
  rw [Subgroup.mem_centralizer_iff] at h
  have h' : F.zSO * y = y * F.zSO := h F.zSO (by simp)
  simpa [FrameData.zSO] using congrArg (fun g : Q.specialOrthogonalWithin =>
    (g : TauCeti.QuadraticMap.orthogonalGroup Q)) h'

end Generic

section Assembly

variable {K : Type} [Field K] [Finite K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {Q : QuadraticForm K V}

abbrev OGg : Subgroup (V ≃ₗ[K] V) := TauCeti.QuadraticMap.orthogonalGroup Q
abbrev D0g : Subgroup ↥(OGg (V := V) (Q := Q)) :=
  commutator ↥(OGg (V := V) (Q := Q))

theorem exists_overgroups_of_frame
    (F : FrameData Q) (hodd : Odd (Nat.card K)) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5)
    (G : Subgroup ↥OGg) (hDG : D0g ≤ G) (hGSO : G ≤ Q.specialOrthogonalWithin)
    (T : Sylow 2 G)
    (C M : Subgroup ↥OGg)
    (hgen : (C ⊓ D0g) ⊔ (M ⊓ D0g) = D0g)
    (hnotC : ¬ D0g ≤ C) (hnotM : ¬ D0g ≤ M)
    (hWC : ∀ D : Subgroup (O2 K), wreathO F D ≤ C)
    (hWM : ∀ D : Subgroup (O2 K), wreathO F D ≤ M) :
    ∃ X1 X2 : Subgroup ↥OGg,
      (T : Subgroup G).map G.subtype ≤ X1 ∧
      (T : Subgroup G).map G.subtype ≤ X2 ∧
      X1 ≤ G ∧ X2 ≤ G ∧
      ¬ D0g ≤ X1 ∧ ¬ D0g ≤ X2 ∧
      (X1 ⊓ D0g) ⊔ (X2 ⊓ D0g) = D0g := by
  obtain ⟨W, T0, hT0eq, hzP, htP, hzord0, htord0, htnot0, hcenter0,
    hN0le, hN0card, hN0norm⟩ :=
    CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.fixed_frame_sylow
      F hodd hQ hdim G hDG hGSO
  let P0 : Subgroup ↥(OGg (V := V) (Q := Q)) := (T0 : Subgroup G).map G.subtype
  have hWS : W.S.map (Q.specialOrthogonalWithin).subtype = wreathO F W.D := by
    rw [W.hScoe]
    exact wreathSub_map_eq (F := F) W.D
  have hP0_le_wreath : P0 ≤ wreathO F W.D := by
    rw [show P0 = W.S.map (Q.specialOrthogonalWithin).subtype ⊓ G from hT0eq, hWS]
    exact inf_le_left
  have hP0_le_C : P0 ≤ C := hP0_le_wreath.trans (hWC W.D)
  have hP0_le_M : P0 ≤ M := hP0_le_wreath.trans (hWM W.D)
  let H : Subgroup ↥(OGg (V := V) (Q := Q)) := G ⊓ C
  let K : Subgroup ↥(OGg (V := V) (Q := Q)) := G ⊓ M
  have hP0_le_G : P0 ≤ G := Subgroup.map_subtype_le (T0 : Subgroup G)
  have hP0_le_H : P0 ≤ H := le_inf hP0_le_G hP0_le_C
  have hP0_le_K : P0 ≤ K := le_inf hP0_le_G hP0_le_M
  have hHgen : H ⊓ D0g = C ⊓ D0g := by
    dsimp only [H]
    rw [inf_assoc, inf_eq_right.mpr (le_trans inf_le_right hDG)]
  have hKgen : K ⊓ D0g = M ⊓ D0g := by
    dsimp only [K]
    rw [inf_assoc, inf_eq_right.mpr (le_trans inf_le_right hDG)]
  have hgenHK : (H ⊓ D0g) ⊔ (K ⊓ D0g) = D0g := by
    rw [hHgen, hKgen]
    exact hgen
  have hnotD_H : ¬ D0g ≤ H := fun h => hnotC (h.trans inf_le_right)
  have hnotD_K : ¬ D0g ≤ K := fun h => hnotM (h.trans inf_le_right)
  have hDnorm : (D0g (V := V) (Q := Q)).Normal := by
    change (⁅(⊤ : Subgroup ↥(OGg (V := V) (Q := Q))),
      ⊤⁆ : Subgroup ↥(OGg (V := V) (Q := Q))).Normal
    exact Subgroup.commutator_normal _ _
  haveI : (D0g (V := V) (Q := Q)).Normal := hDnorm
  have hDconj : ∀ g : ↥(OGg (V := V) (Q := Q)),
      (D0g (V := V) (Q := Q)).map (MulAut.conj g).toMonoidHom =
        D0g (V := V) (Q := Q) := by
    intro g
    simpa using
      (Subgroup.Normal.map_conj_eq (H := D0g (V := V) (Q := Q)) g)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T0 T
  have hTcoe : (T : Subgroup G) =
      (T0 : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rw [Subgroup.pointwise_smul_def]
    rfl
  have hPconj : (T : Subgroup G).map G.subtype =
      P0.map (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom := by
    rw [hTcoe, Subgroup.map_map, Subgroup.map_map]
    congr 1
  let X1 : Subgroup ↥(OGg (V := V) (Q := Q)) :=
    H.map (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom
  let X2 : Subgroup ↥(OGg (V := V) (Q := Q)) :=
    K.map (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom
  have hT_le_X1 : (T : Subgroup G).map G.subtype ≤ X1 := by
    rw [hPconj]
    exact Subgroup.map_mono
      (f := (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom) hP0_le_H
  have hT_le_X2 : (T : Subgroup G).map G.subtype ≤ X2 := by
    rw [hPconj]
    exact Subgroup.map_mono
      (f := (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom) hP0_le_K
  have hX1_le_G : X1 ≤ G := by
    rintro x ⟨y, hyH, rfl⟩
    have hyG : y ∈ G := hyH.1
    have hgG : (g : ↥(OGg (V := V) (Q := Q))) ∈ G := g.2
    show (g : ↥(OGg (V := V) (Q := Q))) * y *
      (g : ↥(OGg (V := V) (Q := Q)))⁻¹ ∈ G
    exact G.mul_mem (G.mul_mem hgG hyG) (G.inv_mem hgG)
  have hX2_le_G : X2 ≤ G := by
    rintro x ⟨y, hyK, rfl⟩
    have hyG : y ∈ G := hyK.1
    have hgG : (g : ↥(OGg (V := V) (Q := Q))) ∈ G := g.2
    show (g : ↥(OGg (V := V) (Q := Q))) * y *
      (g : ↥(OGg (V := V) (Q := Q)))⁻¹ ∈ G
    exact G.mul_mem (G.mul_mem hgG hyG) (G.inv_mem hgG)
  have hX1_back : X1.map
      (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))⁻¹).toMonoidHom = H := by
    dsimp only [X1]
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))⁻¹).toMonoidHom.comp
        (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply]
    change H.map ((MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))⁻¹).toMonoidHom.comp
      (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom) = H
    rw [hcomp, Subgroup.map_id]
  have hX2_back : X2.map
      (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))⁻¹).toMonoidHom = K := by
    dsimp only [X2]
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))⁻¹).toMonoidHom.comp
        (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom = MonoidHom.id _ := by
      ext x
      simp [MulAut.conj_apply]
    change K.map ((MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))⁻¹).toMonoidHom.comp
      (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom) = K
    rw [hcomp, Subgroup.map_id]
  have hnotD_X1 : ¬ D0g ≤ X1 := by
    intro h
    have hmap : (D0g (V := V) (Q := Q)).map
        (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))⁻¹).toMonoidHom ≤
        X1.map (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))⁻¹).toMonoidHom :=
      Subgroup.map_mono h
    rw [hDconj, hX1_back] at hmap
    exact hnotD_H hmap
  have hnotD_X2 : ¬ D0g ≤ X2 := by
    intro h
    have hmap : (D0g (V := V) (Q := Q)).map
        (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))⁻¹).toMonoidHom ≤
        X2.map (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))⁻¹).toMonoidHom :=
      Subgroup.map_mono h
    rw [hDconj, hX2_back] at hmap
    exact hnotD_K hmap
  have hX1D : X1 ⊓ D0g =
      (H ⊓ D0g).map (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom := by
    dsimp only [X1]
    conv_lhs => rw [← hDconj (g : ↥(OGg (V := V) (Q := Q)))]
    rw [← Subgroup.map_inf_eq H (D0g (V := V) (Q := Q))
      (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom
      (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).injective]
  have hX2D : X2 ⊓ D0g =
      (K ⊓ D0g).map (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom := by
    dsimp only [X2]
    conv_lhs => rw [← hDconj (g : ↥(OGg (V := V) (Q := Q)))]
    rw [← Subgroup.map_inf_eq K (D0g (V := V) (Q := Q))
      (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).toMonoidHom
      (MulAut.conj (g : ↥(OGg (V := V) (Q := Q)))).injective]
  have hX1Djoin : (X1 ⊓ D0g) ⊔ (X2 ⊓ D0g) = D0g := by
    rw [hX1D, hX2D, ← Subgroup.map_sup, hgenHK, hDconj]
  exact ⟨X1, X2, hT_le_X1, hT_le_X2, hX1_le_G, hX2_le_G, hnotD_X1, hnotD_X2, hX1Djoin⟩

end Assembly


section Native

noncomputable abbrev frameStabilizerNative : Subgroup O :=
  @MulAction.stabilizer O (Set V) _ (Set.mulActionSet)
    (Set.range stdFrame.e ∪ -(Set.range stdFrame.e))

noncomputable abbrev C0 : Subgroup O :=
  Subgroup.centralizer ({stdFrame.zO} : Set O)

noncomputable abbrev M0 : Subgroup O := frameStabilizerNative

noncomputable abbrev D0 : Subgroup ↥O := commutator ↥O

noncomputable def eD0 : ↥D0 ≃* ↥derived :=
  (Subgroup.equivMapOfInjective D0 O.subtype O.subtype_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator O))

theorem eD0_coe (x : ↥D0) : (eD0 x : ↥derived).1 = (x : ↥O).1 := by
  rfl

theorem mem_frameVectors_iff_native (x : V) :
    x ∈ (frameVectors : Set V) ↔ (∃ i, x = e i) ∨ (∃ i, -x = e i) := by
  constructor
  · rintro ⟨i, rfl | rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨i, neg_neg (e i)⟩
  · rintro (⟨i, rfl⟩ | ⟨i, hi⟩)
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr (neg_eq_iff_eq_neg.mp hi)⟩

theorem signedFrame_stdFrame_native :
    (Set.range stdFrame.e ∪ -(Set.range stdFrame.e)) = (frameVectors : Set V) := by
  ext x
  rw [mem_signedFrame_iff]
  simp only [stdFrame_e]
  rw [mem_frameVectors_iff_native]
  rfl

theorem centralizer_subgroupOf_eq_comap :
    C0.subgroupOf D0 = zCentralizer.comap eD0.toMonoidHom := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  rw [C0, Subgroup.mem_centralizer_singleton_iff]
  rw [zCentralizer, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply Subtype.ext
    simpa [eD0_coe, zD, FrameData.zO] using congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    simpa [eD0_coe, zD, FrameData.zO] using congrArg Subtype.val h

theorem frameStabilizer_subgroupOf_eq_comap :
    M0.subgroupOf D0 = frameNormalizer.comap eD0.toMonoidHom := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
  rw [M0, frameStabilizerNative]
  rw [MulAction.mem_stabilizer_set' (signedFrame_finite stdFrame)]
  rw [mem_frameNormalizer_iff]
  rw [signedFrame_stdFrame_native]
  constructor
  · intro h b hb
    simpa [Subgroup.smul_def, LinearEquiv.smul_def, eD0_coe] using h hb
  · intro h b hb
    simpa [Subgroup.smul_def, LinearEquiv.smul_def, eD0_coe] using h hb

theorem generation_subgroupOf :
    C0.subgroupOf D0 ⊔ M0.subgroupOf D0 = ⊤ := by
  rw [centralizer_subgroupOf_eq_comap, frameStabilizer_subgroupOf_eq_comap]
  have hrange : eD0.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr eD0.surjective
  rw [Subgroup.comap_sup_eq_of_le_range eD0.toMonoidHom
    (by rw [hrange]; exact le_top) (by rw [hrange]; exact le_top)]
  rw [centralizer_sup_frameNormalizer, Subgroup.comap_top]

theorem generation_inf :
    (C0 ⊓ D0) ⊔ (M0 ⊓ D0) = D0 := by
  have h := congrArg (Subgroup.map D0.subtype) generation_subgroupOf
  rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h
  simpa only [Subgroup.subgroupOf_map_subtype] using h

theorem not_D0_le_C0 : ¬ D0 ≤ C0 := by
  intro h
  have htop : C0.subgroupOf D0 = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    exact Subgroup.mem_subgroupOf.mpr (h x.2)
  have htopZ : zCentralizer = ⊤ := by
    apply (Subgroup.comap_injective (f := eD0.toMonoidHom) eD0.surjective)
    rw [← centralizer_subgroupOf_eq_comap, htop, Subgroup.comap_top]
  exact (ne_of_lt zCentralizer_lt_top) htopZ

theorem not_D0_le_M0 : ¬ D0 ≤ M0 := by
  intro h
  have htop : M0.subgroupOf D0 = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    exact Subgroup.mem_subgroupOf.mpr (h x.2)
  have htopF : frameNormalizer = ⊤ := by
    apply (Subgroup.comap_injective (f := eD0.toMonoidHom) eD0.surjective)
    rw [← frameStabilizer_subgroupOf_eq_comap, htop, Subgroup.comap_top]
  exact (ne_of_lt frameNormalizer_lt_top) htopF

theorem wreathO_le_C0 (D : Subgroup (O2 F)) : wreathO stdFrame D ≤ C0 := by
  have h := wreathSub_map_le_centralizer_zO (F := stdFrame) D
  rw [wreathSub_map_eq] at h
  exact h

theorem wreathO_le_M0 (D : Subgroup (O2 F)) : wreathO stdFrame D ≤ M0 := by
  have h := wreathSub_map_le_frameStabilizerO (F := stdFrame) D
  rw [wreathSub_map_eq] at h
  exact h


end Native

end CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameSylowOvergroups
