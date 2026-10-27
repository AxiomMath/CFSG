module

public import CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameWeakClosure
public import CFSG.ClassicalGroups.Orthogonal.FiveSquareModel
public import CFSG.ClassicalInvolution.Orders.Symplectic
public import CFSG.GroupTheory.ElemAbelianClosure

public noncomputable section

namespace CFSG.ClassicalGroups.Orthogonal.FiveSquareSylow

open CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameGeneration
open CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameWeakClosure
open CFSG.ClassicalGroups.Orthogonal.FiveSquareSignOrbit
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow
open CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel
open CFSG.ClassicalGroups.Orthogonal.PlaneSignChangeSylow
open CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupScalarSquare
open CFSG.LocalAnalysis.ComponentInitial.OddOrthogonal
open CFSG.GH74.GLS.IVK.Proofs2.Sp48
open QuadraticMap

local instance nativeAddCommGroup : AddCommGroup (Fin 5 → F) :=
  { Pi.addCommGroup with toAddCommMonoid := Pi.addCommMonoid }

local instance nativeFiniteLinearEquiv : Finite ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F)) :=
  Finite.of_injective (fun f : (Fin 5 → F) ≃ₗ[F] (Fin 5 → F) => f.toFun) (by
    intro f g h
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext
    intro x
    exact congrFun h x)

abbrev G : Type := ↥FiveSquareFrameGeneration.derived

@[expose]
noncomputable def frameSylow : Subgroup G :=
  FiveSquareSignOrbit.frameSigns ⊔ FiveSquareFrameWeakClosure.permutationFour

theorem frameSylow_def :
    frameSylow = FiveSquareSignOrbit.frameSigns ⊔
      FiveSquareFrameWeakClosure.permutationFour := rfl

theorem frameSigns_le_frameSylow :
    FiveSquareSignOrbit.frameSigns ≤ frameSylow :=
  le_sup_left

private def sigmaR : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 1 * Equiv.swap 2 3

private def sigmaS : Equiv.Perm (Fin 5) :=
  Equiv.swap 0 2 * Equiv.swap 1 3

private theorem rD_apply_stdFrame (i : Fin 5) :
    ((FiveSquareFrameWeakClosure.rD : G) : V ≃ₗ[F] V) (stdFrame.e i) =
      stdFrame.e (sigmaR i) := by
  fin_cases i
  · have h : sigmaR (0 : Fin 5) = 1 := by decide
    simpa [stdFrame_e, h] using FiveSquareFrameWeakClosure.rD_e0
  · have h : sigmaR (1 : Fin 5) = 0 := by decide
    simpa [stdFrame_e, h] using FiveSquareFrameWeakClosure.rD_e1
  · have h : sigmaR (2 : Fin 5) = 3 := by decide
    simpa [stdFrame_e, h] using FiveSquareFrameWeakClosure.rD_e2
  · have h : sigmaR (3 : Fin 5) = 2 := by decide
    simpa [stdFrame_e, h] using FiveSquareFrameWeakClosure.rD_e3
  · have h : sigmaR (4 : Fin 5) = 4 := by decide
    simpa [stdFrame_e, h] using FiveSquareFrameWeakClosure.rD_e4

private theorem sD_apply_stdFrame (i : Fin 5) :
    ((FiveSquareFrameWeakClosure.sD : G) : V ≃ₗ[F] V) (stdFrame.e i) =
      stdFrame.e (sigmaS i) := by
  fin_cases i
  · have h : sigmaS (0 : Fin 5) = 2 := by decide
    simpa [stdFrame_e, h] using FiveSquareFrameWeakClosure.sD_e0
  · have h : sigmaS (1 : Fin 5) = 3 := by decide
    simpa [stdFrame_e, h] using FiveSquareFrameWeakClosure.sD_e1
  · have h : sigmaS (2 : Fin 5) = 0 := by decide
    simpa [stdFrame_e, h] using FiveSquareFrameWeakClosure.sD_e2
  · have h : sigmaS (3 : Fin 5) = 1 := by decide
    simpa [stdFrame_e, h] using FiveSquareFrameWeakClosure.sD_e3
  · have h : sigmaS (4 : Fin 5) = 4 := by decide
    simpa [stdFrame_e, h] using FiveSquareFrameWeakClosure.sD_e4

theorem mem_normalizer_frameSigns_of_permutes_stdFrame {g : G} {sigma : Equiv.Perm (Fin 5)}
    (hg : ∀ i, ((g : G) : V ≃ₗ[F] V) (stdFrame.e i) = stdFrame.e (sigma i)) :
    g ∈ Subgroup.normalizer (FiveSquareSignOrbit.frameSigns : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : FiveSquareSignOrbit.frameSigns.map
      (MulAut.conj g).toMonoidHom ≤ FiveSquareSignOrbit.frameSigns := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨S, hSeven, hxval⟩ := mem_frameSigns_iff.mp hx
    refine mem_frameSigns_iff.mpr ⟨S.image sigma, ?_, ?_⟩
    · rwa [Finset.card_image_of_injective _ sigma.injective]
    · change (((MulAut.conj g) x : G) : V ≃ₗ[F] V) =
        signEquiv stdFrame.e (S.image sigma)
      rw [MulAut.conj_apply]
      change ((g : G) : V ≃ₗ[F] V) * ((x : G) : V ≃ₗ[F] V) *
          (((g : G) : V ≃ₗ[F] V))⁻¹ = signEquiv stdFrame.e (S.image sigma)
      rw [hxval]
      exact conj_signEquiv hg S
  have hcard : Nat.card FiveSquareSignOrbit.frameSigns ≤
      Nat.card (FiveSquareSignOrbit.frameSigns.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact Subgroup.eq_of_le_of_card_ge hle hcard

theorem rD_mem_normalizer_frameSigns :
    FiveSquareFrameWeakClosure.rD ∈
      Subgroup.normalizer (FiveSquareSignOrbit.frameSigns : Set G) :=
  mem_normalizer_frameSigns_of_permutes_stdFrame (g := FiveSquareFrameWeakClosure.rD)
    rD_apply_stdFrame

theorem sD_mem_normalizer_frameSigns :
    FiveSquareFrameWeakClosure.sD ∈
      Subgroup.normalizer (FiveSquareSignOrbit.frameSigns : Set G) :=
  mem_normalizer_frameSigns_of_permutes_stdFrame (g := FiveSquareFrameWeakClosure.sD)
    sD_apply_stdFrame

theorem permutationFour_le_normalizer_frameSigns :
    FiveSquareFrameWeakClosure.permutationFour ≤
      Subgroup.normalizer (FiveSquareSignOrbit.frameSigns : Set G) := by
  rw [FiveSquareFrameWeakClosure.permutationFour_def]
  exact sup_le
    (Subgroup.zpowers_le.mpr rD_mem_normalizer_frameSigns)
    (Subgroup.zpowers_le.mpr sD_mem_normalizer_frameSigns)

private theorem e_ne_smul_e0 {i : Fin 5} (hi : i ≠ 0) (c : F) :
    e i ≠ c • e 0 := by
  intro h
  have h' := congrFun h i
  simp [Generic.e_apply, hi] at h'

private theorem frameSigns_apply_e0_eq_smul {x : G}
    (hx : x ∈ FiveSquareSignOrbit.frameSigns) :
    ∃ c : F, ((x : G) : V ≃ₗ[F] V) (e 0) = c • e 0 := by
  obtain ⟨S, -, hxval⟩ := mem_frameSigns_iff.mp hx
  refine ⟨if (0 : Fin 5) ∈ S then (-1 : F) else 1, ?_⟩
  rw [hxval]
  exact signEquiv_apply_basis stdFrame.e S 0

theorem disjoint_frameSigns_permutationFour :
    Disjoint FiveSquareSignOrbit.frameSigns FiveSquareFrameWeakClosure.permutationFour := by
  rw [Subgroup.disjoint_def]
  intro x hxE hxP
  rw [FiveSquareFrameWeakClosure.permutationFour_def] at hxP
  obtain ⟨a, ha, b, hb, hxab⟩ :=
    (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left
      (H := Subgroup.zpowers (FiveSquareFrameWeakClosure.rD))
      (K := Subgroup.zpowers (FiveSquareFrameWeakClosure.sD))
      (FiveSquareFrameWeakClosure.zpowers_sD_le_normalizer_zpowers_rD)).mp hxP
  have ha' := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two
    (FiveSquareFrameWeakClosure.orderOf_rD)).mp ha
  have hb' := (Subgroup.mem_zpowers_iff_of_orderOf_eq_two
    (FiveSquareFrameWeakClosure.orderOf_sD)).mp hb
  obtain ⟨c, hc⟩ := frameSigns_apply_e0_eq_smul hxE
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · rw [hxab]
    simp
  · have hxr : ((x : G) : V ≃ₗ[F] V) (e 0) = e 2 := by
      rw [hxab]
      simpa using FiveSquareFrameWeakClosure.sD_e0
    have heq : e 2 = c • e 0 := by
      rw [← hxr, hc]
    exact (e_ne_smul_e0 (by decide) c heq).elim
  · have hxr : ((x : G) : V ≃ₗ[F] V) (e 0) = e 1 := by
      rw [hxab]
      simpa using FiveSquareFrameWeakClosure.rD_e0
    have heq : e 1 = c • e 0 := by
      rw [← hxr, hc]
    exact (e_ne_smul_e0 (by decide) c heq).elim
  · have hxr : ((x : G) : V ≃ₗ[F] V) (e 0) = e 3 := by
      rw [hxab]
      change ((FiveSquareFrameWeakClosure.rD : G) : V ≃ₗ[F] V)
        (((FiveSquareFrameWeakClosure.sD : G) : V ≃ₗ[F] V) (e 0)) = e 3
      rw [FiveSquareFrameWeakClosure.sD_e0, FiveSquareFrameWeakClosure.rD_e2]
    have heq : e 3 = c • e 0 := by
      rw [← hxr, hc]
    exact (e_ne_smul_e0 (by decide) c heq).elim

theorem card_frameSylow : Nat.card frameSylow = 64 := by
  rw [frameSylow_def,
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      FiveSquareSignOrbit.frameSigns FiveSquareFrameWeakClosure.permutationFour
      permutationFour_le_normalizer_frameSigns disjoint_frameSigns_permutationFour,
    FiveSquareSignOrbit.card_frameSigns, FiveSquareFrameWeakClosure.card_permutationFour]

theorem card_G : Nat.card G = 4680000 := by
  have hmodel := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero
    (G := G) (t := .PSp) (n := 2) (p := 5) (f := 1) (by decide)
    CFSG.ClassicalGroups.Orthogonal.FiveSquareModel.lieModel_derived
  unfold CFSG.Open.StatedClassicalModel at hmodel
  obtain ⟨-, K, instField, instFinite, hK, ⟨e⟩⟩ := hmodel
  let _ : Field K := instField
  let _ : Finite K := instFinite
  have hproj : Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSp 2 K)) =
      CFSG.Open.ordBC 2 5 :=
    CFSG.ClassicalInvolution.card_statedProj_statedSp_eq_ordBC
      (K := K) (n := 2) (p := 5) (f := 1) Nat.prime_five (by decide) hK (by norm_num)
  rw [Nat.card_congr e.toEquiv, hproj, CFSG.Open.ordBC]
  have hprod : (∏ i ∈ Finset.Icc 1 2, (5 ^ (2 * i) - 1)) =
      (5 ^ 2 - 1) * (5 ^ 4 - 1) := by
    rw [Finset.prod_Icc_succ_top (by norm_num : (1 : ℕ) ≤ 2)]
    rw [Finset.prod_Icc_succ_top (by norm_num : (1 : ℕ) ≤ 1)]
    rw [show Finset.Icc (1 : ℕ) 0 = ∅ by decide, Finset.prod_empty, one_mul]
  rw [hprod]
  norm_num

theorem isPGroup_frameSylow : IsPGroup 2 ↥frameSylow :=
  IsPGroup.of_card (n := 6) (by rw [card_frameSylow]; norm_num)

theorem index_frameSylow : frameSylow.index = 73125 := by
  have h := Subgroup.index_mul_card (G := G) (H := frameSylow)
  rw [card_frameSylow, card_G] at h
  have h' : frameSylow.index * 64 = 73125 * 64 := by
    rw [h]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

noncomputable def frameSylowClass : Sylow 2 G :=
  isPGroup_frameSylow.toSylow (by
    rw [index_frameSylow]
    norm_num)

theorem coe_frameSylowClass : (frameSylowClass : Subgroup G) = frameSylow :=
  IsPGroup.toSylow_coe isPGroup_frameSylow (by
    rw [index_frameSylow]
    norm_num)

theorem zD_mem_frameSigns : FiveSquareFrameGeneration.zD ∈ FiveSquareSignOrbit.frameSigns := by
  refine mem_frameSigns_iff.mpr ⟨({0, 1, 2, 3} : Finset (Fin 5)), by decide, ?_⟩
  change (stdFrame.z : V ≃ₗ[F] V) =
    signEquiv stdFrame.e ({0, 1, 2, 3} : Finset (Fin 5))
  exact sign_z.symm

theorem orderOf_zD : orderOf FiveSquareFrameGeneration.zD = 2 := by
  have hzO : orderOf stdFrame.zO = 2 := FiveDimensionalSylow.zO_order stdFrame
  have hz : orderOf ((stdFrame.zO : ↥O) : V ≃ₗ[F] V) = 2 :=
    (orderOf_injective O.subtype O.subtype_injective stdFrame.zO).trans hzO
  have hzG : orderOf ((FiveSquareFrameGeneration.zD : G) : V ≃ₗ[F] V) = 2 := by
    simpa [FiveSquareFrameGeneration.zD, FrameData.zO] using hz
  have h := orderOf_injective
    (Subgroup.subtype (FiveSquareFrameGeneration.derived : Subgroup (V ≃ₗ[F] V)))
    (Subgroup.subtype_injective FiveSquareFrameGeneration.derived)
    FiveSquareFrameGeneration.zD
  exact h.symm.trans hzG

theorem zD_commute_rD :
    FiveSquareFrameGeneration.zD * FiveSquareFrameWeakClosure.rD =
      FiveSquareFrameWeakClosure.rD * FiveSquareFrameGeneration.zD := by
  apply Subtype.ext
  change ((FiveSquareFrameGeneration.zD : G) : V ≃ₗ[F] V) *
      ((FiveSquareFrameWeakClosure.rD : G) : V ≃ₗ[F] V) =
    ((FiveSquareFrameWeakClosure.rD : G) : V ≃ₗ[F] V) *
      ((FiveSquareFrameGeneration.zD : G) : V ≃ₗ[F] V)
  rw [FiveSquareFrameWeakClosure.coe_rD]
  have h := congrArg (fun x : ↥O => (x : V ≃ₗ[F] V))
    (FiveDimensionalSylow.betaO_commute_zO stdFrame
      (FrameData.sigmaO2 (K := F)) (FrameData.sigmaO2 (K := F)))
  simpa [FiveSquareFrameGeneration.zD, FrameData.zO] using h.symm

theorem zD_commute_sD :
    FiveSquareFrameGeneration.zD * FiveSquareFrameWeakClosure.sD =
      FiveSquareFrameWeakClosure.sD * FiveSquareFrameGeneration.zD := by
  apply Subtype.ext
  change ((FiveSquareFrameGeneration.zD : G) : V ≃ₗ[F] V) *
      ((FiveSquareFrameWeakClosure.sD : G) : V ≃ₗ[F] V) =
    ((FiveSquareFrameWeakClosure.sD : G) : V ≃ₗ[F] V) *
      ((FiveSquareFrameGeneration.zD : G) : V ≃ₗ[F] V)
  rw [FiveSquareFrameWeakClosure.coe_sD]
  have hss : (stdFrame.s : V ≃ₗ[F] V) * stdFrame.s = 1 := stdFrame.s_mul_self
  have hs_inv : (stdFrame.s : V ≃ₗ[F] V)⁻¹ = stdFrame.s :=
    inv_eq_of_mul_eq_one_right hss
  have h := congrArg (fun x : ↥O => (x : V ≃ₗ[F] V))
    (FiveDimensionalSylow.sO_conj_zO stdFrame)
  have h' : (stdFrame.s : V ≃ₗ[F] V) * (stdFrame.z : V ≃ₗ[F] V) *
      (stdFrame.s : V ≃ₗ[F] V) = (stdFrame.z : V ≃ₗ[F] V) := by
    simpa [FrameData.sO, FrameData.zO, hs_inv] using h
  calc (stdFrame.z : V ≃ₗ[F] V) * (stdFrame.s : V ≃ₗ[F] V)
      = ((stdFrame.s : V ≃ₗ[F] V) * (stdFrame.z : V ≃ₗ[F] V) *
          (stdFrame.s : V ≃ₗ[F] V)) * (stdFrame.s : V ≃ₗ[F] V) := by
        conv_lhs => rw [← h']
    _ = (stdFrame.s : V ≃ₗ[F] V) * (stdFrame.z : V ≃ₗ[F] V) *
          ((stdFrame.s : V ≃ₗ[F] V) * (stdFrame.s : V ≃ₗ[F] V)) := by group
    _ = (stdFrame.s : V ≃ₗ[F] V) * (stdFrame.z : V ≃ₗ[F] V) := by rw [hss, mul_one]

theorem frameSigns_le_zCentralizer :
    FiveSquareSignOrbit.frameSigns ≤ FiveSquareFrameGeneration.zCentralizer := by
  intro x hx
  rw [FiveSquareFrameGeneration.mem_zCentralizer_iff]
  exact CFSG.Open.IsElemAbelian.comm FiveSquareSignOrbit.isElemAbelian_frameSigns
    hx zD_mem_frameSigns

theorem permutationFour_le_zCentralizer :
    FiveSquareFrameWeakClosure.permutationFour ≤
      FiveSquareFrameGeneration.zCentralizer := by
  rw [FiveSquareFrameWeakClosure.permutationFour_def]
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le, FiveSquareFrameGeneration.mem_zCentralizer_iff]
    exact zD_commute_rD.symm
  · rw [Subgroup.zpowers_le, FiveSquareFrameGeneration.mem_zCentralizer_iff]
    exact zD_commute_sD.symm

theorem frameSylow_le_zCentralizer :
    frameSylow ≤ FiveSquareFrameGeneration.zCentralizer := by
  rw [frameSylow_def]
  exact sup_le frameSigns_le_zCentralizer permutationFour_le_zCentralizer

private abbrev D0 : Subgroup ↥O :=
  CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameSylowOvergroups.D0

private theorem D0_le_specialOrthogonalWithin : D0 ≤ Q.specialOrthogonalWithin := by
  intro x hx
  rw [QuadraticMap.mem_specialOrthogonalWithin_iff]
  have hdet : (LinearEquiv.det.comp O.subtype) x = 1 := by
    have h := Abelianization.commutator_subset_ker (LinearEquiv.det.comp O.subtype) hx
    simpa [MonoidHom.mem_ker] using h
  simpa using hdet

private theorem odd_native : Odd (Nat.card F) := by
  rw [Nat.card_zmod]
  norm_num

private theorem finrank_native : Module.finrank F (Fin 5 → F) = 5 := by
  simp

private theorem fixed_frame_center_card :
    ∃ S0 : Sylow 2 D0, Nat.card (Subgroup.center S0) = 2 := by
  obtain ⟨W, S0, hS0eq, hzP, htP, hzord, htord, htnot, hcenter, hnormal, hcard, hnorm⟩ :=
    FiveDimensionalSylow.fixed_frame_sylow (F := stdFrame) (Q := Q) odd_native
      (Generic.polar_nondegenerate F) finrank_native D0 le_rfl
      D0_le_specialOrthogonalWithin
  refine ⟨S0, ?_⟩
  have hinj : Function.Injective (D0.subtype.comp (S0 : Subgroup D0).subtype) :=
    D0.subtype_injective.comp (S0 : Subgroup D0).subtype_injective
  have hmap : Nat.card ((Subgroup.center S0).map
      (D0.subtype.comp (S0 : Subgroup D0).subtype)) =
      Nat.card (Subgroup.center S0) :=
    Subgroup.card_map_of_injective hinj
  rw [← hmap, hcenter, Nat.card_zpowers, hzord]

theorem card_center_frameSylowClass :
    Nat.card (Subgroup.center frameSylowClass) = 2 := by
  obtain ⟨S0, hS0⟩ := fixed_frame_center_card
  obtain ⟨eS⟩ :=
    CFSG.GroupTheory.WeirSylow.nonempty_sylow_mulEquiv_sylow_of_mulEquiv
      (CFSG.ClassicalGroups.Orthogonal.FiveSquareFrameSylowOvergroups.eD0)
      frameSylowClass S0
  rw [Nat.card_congr (Subgroup.centerCongr eS).toEquiv]
  exact hS0

theorem card_center_frameSylow :
    Nat.card (Subgroup.center frameSylow) = 2 := by
  rw [← coe_frameSylowClass]
  exact card_center_frameSylowClass

theorem zD_mem_frameSylow :
    FiveSquareFrameGeneration.zD ∈ frameSylow :=
  frameSigns_le_frameSylow zD_mem_frameSigns

theorem zD_mem_center_frameSylow :
    (⟨FiveSquareFrameGeneration.zD, zD_mem_frameSylow⟩ : frameSylow) ∈
      Subgroup.center frameSylow := by
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact FiveSquareFrameGeneration.mem_zCentralizer_iff.mp
    (frameSylow_le_zCentralizer y.2)

theorem zpowers_zD_le_center_frameSylow :
    Subgroup.zpowers FiveSquareFrameGeneration.zD ≤
      (Subgroup.center frameSylow).map frameSylow.subtype := by
  rw [Subgroup.zpowers_le]
  exact Subgroup.mem_map.mpr
    ⟨⟨FiveSquareFrameGeneration.zD, zD_mem_frameSylow⟩,
      zD_mem_center_frameSylow, rfl⟩

theorem center_frameSylow_map :
    (Subgroup.center frameSylow).map frameSylow.subtype =
      Subgroup.zpowers FiveSquareFrameGeneration.zD := by
  have hBA : Subgroup.zpowers FiveSquareFrameGeneration.zD ≤
      (Subgroup.center frameSylow).map frameSylow.subtype :=
    zpowers_zD_le_center_frameSylow
  have hAB : (Subgroup.center frameSylow).map frameSylow.subtype ≤
      Subgroup.zpowers FiveSquareFrameGeneration.zD := by
    have hcard : Nat.card ((Subgroup.center frameSylow).map frameSylow.subtype) ≤
        Nat.card (Subgroup.zpowers FiveSquareFrameGeneration.zD) := by
      rw [Subgroup.card_map_of_injective frameSylow.subtype_injective,
        card_center_frameSylow, Nat.card_zpowers, orderOf_zD]
    have heq := Subgroup.eq_of_le_of_card_ge hBA hcard
    simp [heq]
  exact le_antisymm hAB hBA

end CFSG.ClassicalGroups.Orthogonal.FiveSquareSylow
