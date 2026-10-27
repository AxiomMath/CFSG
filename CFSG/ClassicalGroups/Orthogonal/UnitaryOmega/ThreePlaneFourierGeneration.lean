module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureBlockDefs
public import CFSG.ClassicalInvolution.Phan.PhanDn.NormFormType
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviSUThree
import CFSG.ClassicalGroups.Orthogonal.CharTwoReflectGen
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.KLinearOmega
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCommuteAnchor
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.BlockCast
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureEmbed
import CFSG.ClassicalInvolution.Phan.PhanDn.SimpleQn
import CFSG.LocalAnalysis.StandardType.GGOrthRk1PairTriple
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2 CFSG.Timmesfeld.ClassicalOrders
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]

section AnchorFixing

variable {f : ℕ} (E : QuadExt F K (unitaryInvolution K 2 f))

@[expose] noncomputable def normAnchorFixing (m : ℕ) : Subgroup (normOmega E m) :=
  fixingSubgroup (normOmega E m) (Set.range fun w : F × F => (w, (0 : Fin m → K)))

theorem mem_normAnchorFixing_iff {m : ℕ} {g : normOmega E m} :
    g ∈ normAnchorFixing E m ↔
      ∀ w : F × F, g.1 (w, (0 : Fin m → K)) = (w, 0) := by
  simp only [normAnchorFixing, mem_fixingSubgroup_iff, Set.forall_mem_range]
  rfl

theorem normPureBlock_le_normAnchorFixing (m : ℕ) (S : Finset (Fin m)) :
    normPureBlock E m S ≤ normAnchorFixing E m := by
  intro g hg
  rw [mem_normAnchorFixing_iff]
  intro w
  let ψ := LinearEquiv.refl F ((F × F) × (Fin m → K))
  have hS : S.sup (CFSG.RankThree.PartOne.KCOrthogonal.coordPlane ψ) ≤
      CFSG.RankThree.PartOne.KCOrthogonal.coordActive ψ :=
    Finset.sup_le fun i _ => le_iSup _ i
  change g.1 ∈ CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived
    (normHypForm E m) (S.sup (CFSG.RankThree.PartOne.KCOrthogonal.coordPlane ψ)) at hg
  apply CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived_apply_perp hg
  rw [CFSG.RankThree.PartOne.KCOrthogonal.mem_suppPerp]
  intro u hu
  rw [QuadraticMap.polar_comm]
  exact CFSG.RankThree.PartOne.KCOrthogonal.polar_coordAnchor_active ψ
    (normHypForm_apply_coord E m)
    (CFSG.RankThree.PartOne.KCOrthogonal.mem_coordAnchor.mpr ⟨w, rfl⟩) (hS hu)

variable {E} in
private theorem exists_pure_of_anchor (g : normOmega E 3)
    (hg : g ∈ normAnchorFixing E 3) :
    ∃ h : (Fin 3 → K) ≃ₗ[F] (Fin 3 → K), h ∈ orthDerived (Qn E 3) ∧ g.1 = hypExt h := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have hgO : g.1 ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 3) :=
    Subgroup.commutator_le_self _ g.2
  have hfix := (mem_normAnchorFixing_iff E).mp hg
  obtain ⟨h, hh, heq⟩ := exists_hypExt_of_fix (K := F) (W := Fin 3 → K)
    (Q' := Qn E 3) hgO (hfix (1, 0)) (hfix (0, 1))
  have hgω := CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup
    (normHypForm_polarBilin_nondegenerate E 3) g.2
  have heven := (CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mp hgω).2
  rw [heq, finrank_commSpace_hypExt] at heven
  have hnot : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (Qn E 3) := by
    rw [isPlusType_Qn_iff]
    decide
  have hts : ∀ U : Submodule F (Fin 3 → K), Module.finrank F U = 3 →
      ∃ u ∈ U, Qn E 3 u ≠ 0 := by
    intro U hU
    by_contra! hz
    apply hnot
    exact ⟨U, by rw [hU, finrank_Qn E 3], hz⟩
  have hhω : h ∈ CFSG.RankThree.OrthogonalInvolutions.omegaGroup
      (Qn E 3) (Qn_polarBilin_nondegenerate E 3) :=
    CFSG.RankThree.OrthogonalInvolutions.mem_omegaGroup.mpr ⟨hh, heven⟩
  exact ⟨h, CFSG.StandardType.OrthTorus.omegaGroup_le_orthDerived_of_six_extract
    (Qn E 3) (Qn_polarBilin_nondegenerate E 3) (by rw [finrank_Qn E 3]) hts hhω, heq⟩

theorem normPureBlock_univ_three_eq_normAnchorFixing :
    normPureBlock E 3 Finset.univ = normAnchorFixing E 3 := by
  open CFSG.RankThree.PartOne.KCOrthogonal in
  refine le_antisymm (normPureBlock_le_normAnchorFixing E 3 Finset.univ) ?_
  intro g hg
  obtain ⟨t, ht, heq⟩ := exists_pure_of_anchor (E := E) g hg
  let ψ := LinearEquiv.refl F ((F × F) × (Fin 3 → K))
  let U := Finset.univ.sup (CFSG.RankThree.PartOne.KCOrthogonal.coordPlane ψ)
  have hU : U = (LinearMap.inr F (F × F) (Fin 3 → K)).range := by
    apply le_antisymm
    · refine Finset.sup_le fun i _ => ?_
      rintro v hv
      obtain ⟨a, rfl⟩ := CFSG.RankThree.PartOne.KCOrthogonal.mem_coordPlane.mp hv
      exact ⟨Pi.single i a, rfl⟩
    · rintro v ⟨x, rfl⟩
      rw [← Finset.univ_sum_single x, map_sum]
      refine Submodule.sum_mem _ fun i hi => ?_
      exact (show CFSG.RankThree.PartOne.KCOrthogonal.coordPlane ψ i ≤ U from
        Finset.le_sup hi)
        (CFSG.RankThree.PartOne.KCOrthogonal.mem_coordPlane.mpr ⟨x i, rfl⟩)
  let e : (Fin 3 → K) ≃ₗ[F] U :=
    { toFun := fun x => ⟨(0, x), hU.symm ▸ ⟨x, rfl⟩⟩
      invFun := fun u => u.1.2
      left_inv := fun _ => rfl
      right_inv := by
        intro u
        apply Subtype.ext
        obtain ⟨x, hx⟩ : ∃ x : Fin 3 → K, (0, x) = u.1 := by
          have hu : u.1 ∈ (LinearMap.inr F (F × F) (Fin 3 → K)).range := by
            rw [← hU]
            exact u.2
          exact hu
        change (0, u.1.2) = u.1
        rw [← hx]
      map_add' := by intro x y; apply Subtype.ext; simp
      map_smul' := by intro c x; apply Subtype.ext; simp }
  let eQ : (Qn E 3).IsometryEquiv ((normHypForm E 3).comp U.subtype) :=
    { toLinearEquiv := e
      map_app' := by
        intro x
        change normHypForm E 3 (0, x) = Qn E 3 x
        simp only [normHypForm, hypSum_apply, Prod.fst_zero, Prod.snd_zero,
          zero_mul, zero_add] }
  let tU := CFSG.RankThree.PartOne.linConj e t
  have htU : tU ∈ orthDerived ((normHypForm E 3).comp U.subtype) := by
    rw [← CFSG.RankThree.PartOne.map_orthDerived_linConj eQ]
    exact Subgroup.mem_map_of_mem _ ht
  change g.1 ∈ CFSG.RankThree.PartOne.KCOrthogonal.supportedDerived
    (normHypForm E 3) U
  refine CFSG.RankThree.PartOne.KCOrthogonal.mem_supportedDerived.mpr ⟨?_, tU, htU, ?_⟩
  · intro v hv
    have hv2 : v.2 = 0 := by
      apply eq_zero_of_polar_eq_zero (Qn_polarBilin_nondegenerate E 3)
      intro x
      have hp := (CFSG.RankThree.PartOne.KCOrthogonal.mem_suppPerp.mp hv)
        (0, x) (hU.symm ▸ ⟨x, rfl⟩)
      rw [QuadraticMap.polar_comm] at hp
      convert hp using 1
      simp only [QuadraticMap.polar, normHypForm, hypSum_apply, Prod.fst_add,
        Prod.snd_add, add_zero, mul_zero, Prod.fst_zero, Prod.snd_zero,
        zero_add]
      ring
    have hpair : v = (v.1, (0 : Fin 3 → K)) := Prod.ext rfl hv2
    rw [hpair]
    exact (mem_normAnchorFixing_iff E).mp hg _
  · intro a
    obtain ⟨x, hx⟩ : ∃ x : Fin 3 → K, (0, x) = a.1 := by
      have ha : a.1 ∈ (LinearMap.inr F (F × F) (Fin 3 → K)).range := by
        rw [← hU]
        exact a.2
      exact ha
    rw [heq, hypExt_apply]
    change (0, t a.1.2) = (a.1.1, t a.1.2)
    rw [← hx]

end AnchorFixing

variable (E : QuadExt F K (unitaryInvolution K 2 1))

@[expose] def normPlaneSpace (m : ℕ) (i : Fin m) :
    Submodule F ((F × F) × (Fin m → K)) :=
  LinearMap.range ((LinearMap.inr F (F × F) (Fin m → K)).comp
    (LinearMap.single F (fun _ : Fin m => K) i))

@[expose] noncomputable def normDecompositionStabilizer (m : ℕ) : Subgroup (normOmega E m) :=
  normAnchorFixing E m ⊓
    MulAction.stabilizer (normOmega E m) (Set.range (normPlaneSpace (F := F) (K := K) m))

@[expose] noncomputable def threePlaneFourier {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0) : normOmega E 3 :=
  suEmb E 3 (CFSG.AGLEmbedding.fourierElt hσ hs)

theorem threePlaneFourier_mem_normAnchorFixing {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0) :
    threePlaneFourier E hσ hs ∈ normAnchorFixing E 3 := by
  rw [mem_normAnchorFixing_iff]
  intro w
  simp [threePlaneFourier, suEmb_apply]

@[expose] noncomputable def hypExtHom (m : ℕ) :
    ((Fin m → K) ≃ₗ[F] (Fin m → K)) →*
      (((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) where
  toFun := hypExt
  map_one' := by ext p <;> rfl
  map_mul' _ _ := by ext p <;> rfl

namespace NormThreeFourier

variable {E}

omit [Finite K] [CharP K 2] in
private theorem mem_plane_iff {m : ℕ} (i : Fin m)
    (v : (F × F) × (Fin m → K)) :
    v ∈ normPlaneSpace (F := F) (K := K) m i ↔ ∃ a : K, v = (0, Pi.single i a) := by
  change (∃ a : K, (0, Pi.single i a) = v) ↔ ∃ a : K, v = (0, Pi.single i a)
  simp only [eq_comm]

private theorem fix_plane_of_action {m : ℕ} (g : normOmega E m) (i : Fin m)
    (f : K ≃ₗ[F] K)
    (hg : ∀ a : K, g.1 (0, Pi.single i a) = (0, Pi.single i (f a))) :
    g • normPlaneSpace (F := F) (K := K) m i = normPlaneSpace (F := F) (K := K) m i := by
  change (normPlaneSpace (F := F) (K := K) m i).map g.1.toLinearMap =
    normPlaneSpace (F := F) (K := K) m i
  ext v
  constructor
  · rintro ⟨w, hw, hv⟩
    obtain ⟨a, rfl⟩ := (mem_plane_iff i w).mp hw
    exact (mem_plane_iff i v).mpr ⟨f a, hv.symm.trans (hg a)⟩
  · rintro hv
    obtain ⟨a, rfl⟩ := (mem_plane_iff i v).mp hv
    refine ⟨(0, Pi.single i (f.symm a)), (mem_plane_iff i _).mpr ⟨_, rfl⟩, ?_⟩
    change g.1 (0, Pi.single i (f.symm a)) = (0, Pi.single i a)
    simpa only [f.apply_symm_apply] using hg (f.symm a)

private theorem decomp_mem_of_fix_planes {m : ℕ} (g : normOmega E m)
    (hg : g ∈ normAnchorFixing E m)
    (hfix : ∀ i : Fin m, g • normPlaneSpace (F := F) (K := K) m i =
      normPlaneSpace (F := F) (K := K) m i) :
    g ∈ normDecompositionStabilizer E m := by
  refine ⟨hg, ?_⟩
  change g ∈ MulAction.stabilizer (normOmega E m)
    (Set.range (normPlaneSpace (F := F) (K := K) m))
  rw [MulAction.mem_stabilizer_iff]
  ext U
  change (∃ V : Submodule F ((F × F) × (Fin m → K)),
      V ∈ Set.range (normPlaneSpace (F := F) (K := K) m) ∧ g • V = U) ↔
    U ∈ Set.range (normPlaneSpace (F := F) (K := K) m)
  constructor
  · rintro ⟨V, ⟨i, rfl⟩, rfl⟩
    rw [hfix]
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, hfix i⟩

private noncomputable def diagonal {m : ℕ} (a : Fin m → Kˣ) :
    (Fin m → K) ≃ₗ[F] (Fin m → K) :=
  LinearEquiv.piCongrRight fun i => Units.mulLeftLinearEquiv F K (a i)

omit [Finite K] [CharP K 2] in
private theorem diagonal_apply {m : ℕ} (a : Fin m → Kˣ) (v : Fin m → K) (i : Fin m) :
    diagonal (F := F) a v i = (a i : K) * v i := by
  simp [diagonal, LinearEquiv.piCongrRight_apply]

private theorem diagonal_mem_orthogonal {m : ℕ} (a : Fin m → Kˣ)
    (ha : ∀ i, (a i : K) * unitaryInvolution K 2 1 (a i : K) = 1) :
    diagonal (F := F) a ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E m) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  apply (algebraMap F K).injective
  rw [algebraMap_Qn, algebraMap_Qn]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [diagonal_apply, map_mul]
  calc
    (a i : K) * v i *
        (unitaryInvolution K 2 1 (a i : K) * unitaryInvolution K 2 1 (v i)) =
        ((a i : K) * unitaryInvolution K 2 1 (a i : K)) *
          (v i * unitaryInvolution K 2 1 (v i)) := by ring
    _ = v i * unitaryInvolution K 2 1 (v i) := by rw [ha, one_mul]

section SymmetryPairs

variable {R V : Type*} [Field R] [AddCommGroup V] [Module R V]
variable {Q : QuadraticForm R V} {H : Subgroup (V ≃ₗ[R] V)}

private theorem pair_trans {u v w : V}
    (huv : reflect Q u * reflect Q v ∈ H) (hvw : reflect Q v * reflect Q w ∈ H) :
    reflect Q u * reflect Q w ∈ H := by
  have h := H.mul_mem huv hvw
  have heq : (reflect Q u * reflect Q v) * (reflect Q v * reflect Q w) =
      reflect Q u * reflect Q w := by
    rw [mul_assoc, ← mul_assoc (reflect Q v), reflect_mul_self, one_mul]
  rwa [heq] at h

private theorem pair_conj {g : V ≃ₗ[R] V}
    (hg : g ∈ H) (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u v : V}
    (huv : reflect Q u * reflect Q v ∈ H) :
    reflect Q (g u) * reflect Q (g v) ∈ H := by
  have h := H.mul_mem (H.mul_mem hg huv) (H.inv_mem hg)
  have heq : g * (reflect Q u * reflect Q v) * g⁻¹ =
      reflect Q (g u) * reflect Q (g v) := by
    rw [← reflect_conj hgO u, ← reflect_conj hgO v]
    group
  rwa [heq] at h

private theorem pair_symm {u v : V} (h : reflect Q u * reflect Q v ∈ H) :
    reflect Q v * reflect Q u ∈ H := by
  have h' := H.inv_mem h
  simpa only [mul_inv_rev, reflect_inv] using h'

end SymmetryPairs

private theorem coordinate_pairs_of_ne
    (H : Subgroup ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)))
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3))
    (hdiag : ∀ a : Fin 3 → Kˣ, diagonal (F := F) a ∈ H)
    (htau : ∀ i j : Fin 3, i ≠ j → tauAt E i * tauAt E j ∈ H)
    {i j : Fin 3} (hij : i ≠ j) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    reflect (Qn E 3) (Pi.single i a) * reflect (Qn E 3) (Pi.single j b) ∈ H := by
  classical
  let μ : Fin 3 → Kˣ := fun k =>
    if k = i then Units.mk0 a ha else if k = j then Units.mk0 b hb else 1
  have hμi : (μ i : K) = a := by simp [μ]
  have hμj : (μ j : K) = b := by simp [μ, Ne.symm hij]
  have hi : diagonal (F := F) μ (Pi.single i 1) = Pi.single i a := by
    ext k
    by_cases hk : k = i
    · subst k
      simp [diagonal_apply, hμi]
    · simp [diagonal_apply, Pi.single_eq_of_ne hk]
  have hj : diagonal (F := F) μ (Pi.single j 1) = Pi.single j b := by
    ext k
    by_cases hk : k = j
    · subst k
      simp [diagonal_apply, hμj]
    · simp [diagonal_apply, Pi.single_eq_of_ne hk]
  have hbase := htau i j hij
  rw [tauAt_eq_reflect, tauAt_eq_reflect] at hbase
  have h := pair_conj (hdiag μ) (hH (hdiag μ)) hbase
  rwa [hi, hj] at h

private theorem coordinate_pairs
    (H : Subgroup ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)))
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3))
    (hdiag : ∀ a : Fin 3 → Kˣ, diagonal (F := F) a ∈ H)
    (htau : ∀ i j : Fin 3, i ≠ j → tauAt E i * tauAt E j ∈ H)
    (i j : Fin 3) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    reflect (Qn E 3) (Pi.single i a) * reflect (Qn E 3) (Pi.single j b) ∈ H := by
  by_cases hij : i = j
  · subst j
    obtain ⟨k, hki⟩ := exists_ne i
    exact pair_trans
      (coordinate_pairs_of_ne H hH hdiag htau hki.symm ha one_ne_zero)
      (coordinate_pairs_of_ne H hH hdiag htau hki one_ne_zero hb)
  · exact coordinate_pairs_of_ne H hH hdiag htau hij ha hb

private noncomputable def fourier {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0) :
    (Fin 3 → K) ≃ₗ[F] (Fin 3 → K) :=
  suEndN (F := F) (unitaryInvolution K 2 1) 3 (CFSG.AGLEmbedding.fourierElt hσ hs)

private theorem fourier_apply {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0) (v : Fin 3 → K) :
    fourier (F := F) hσ hs v =
      ![v 0 + v 1 + v 2, v 0 + ω * v 1 + ω ^ 2 * v 2,
        v 0 + ω ^ 2 * v 1 + ω * v 2] := by
  change Matrix.mulVec (CFSG.AGLEmbedding.fourierMatThree ω) v = _
  ext i
  fin_cases i <;>
    simp [CFSG.AGLEmbedding.fourierMatThree, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem full_prod_one_preimage {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0)
    (hprim : IsPrimitiveRoot ω 3) (hcube : ∀ a : K, a ≠ 0 → a ^ 3 = 1)
    (v : Fin 3 → K) (hv : ∀ i, v i ≠ 0) (hp : v 0 * v 1 * v 2 = 1) :
    ∃ (i : Fin 3) (a : K), a ≠ 0 ∧ fourier (F := F) hσ hs (Pi.single i a) = v := by
  let b := v 1 * v 0 ^ 2
  have h0 := hcube (v 0) (hv 0)
  have h1 := hcube (v 1) (hv 1)
  have hb3 : b ^ 3 = 1 := by
    calc
      b ^ 3 = v 1 ^ 3 * (v 0 ^ 3) ^ 2 := by dsimp [b]; ring
      _ = 1 := by rw [h0, h1]; norm_num
  have hv1 : v 1 = v 0 * b := by
    calc
      v 1 = v 1 * v 0 ^ 3 := by rw [h0, mul_one]
      _ = v 0 * b := by dsimp [b]; ring
  have hp' : v 0 * v 1 * (v 0 * b ^ 2) = 1 := by
    rw [hv1]
    calc
      v 0 * (v 0 * b) * (v 0 * b ^ 2) = v 0 ^ 3 * b ^ 3 := by ring
      _ = 1 := by rw [h0, hb3, one_mul]
  have hv2 : v 2 = v 0 * b ^ 2 := by
    apply mul_left_cancel₀ (mul_ne_zero (hv 0) (hv 1))
    exact hp.trans hp'.symm
  have hsq : (ω ^ 2) ^ 2 = ω := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by decide, pow_add, hprim.pow_eq_one, pow_one, one_mul]
  obtain ⟨j, hj, hpow⟩ := hprim.eq_pow_of_pow_eq_one hb3
  have hbpow : b = ω ^ j := hpow.symm
  interval_cases j
  · refine ⟨0, v 0, hv 0, ?_⟩
    rw [fourier_apply]
    ext i
    fin_cases i <;> simp [hv1, hv2, hbpow]
  · refine ⟨1, v 0, hv 0, ?_⟩
    rw [fourier_apply]
    ext i
    fin_cases i <;> simp [hv1, hv2, hbpow] <;> ring
  · refine ⟨2, v 0, hv 0, ?_⟩
    rw [fourier_apply]
    ext i
    fin_cases i <;> simp [hv1, hv2, hbpow, hsq] <;> ring

private theorem full_prod_one_pairs {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0)
    (hprim : IsPrimitiveRoot ω 3) (hcube : ∀ a : K, a ≠ 0 → a ^ 3 = 1)
    (H : Subgroup ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)))
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3))
    (hdiag : ∀ a : Fin 3 → Kˣ, diagonal (F := F) a ∈ H)
    (htau : ∀ i j : Fin 3, i ≠ j → tauAt E i * tauAt E j ∈ H)
    (hf : fourier (F := F) hσ hs ∈ H)
    (u v : Fin 3 → K) (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0)
    (hpu : u 0 * u 1 * u 2 = 1) (hpv : v 0 * v 1 * v 2 = 1) :
    reflect (Qn E 3) u * reflect (Qn E 3) v ∈ H := by
  obtain ⟨i, a, ha, hia⟩ := full_prod_one_preimage (F := F) hσ hs hprim hcube u hu hpu
  obtain ⟨j, b, hb, hjb⟩ := full_prod_one_preimage (F := F) hσ hs hprim hcube v hv hpv
  have h := pair_conj hf (hH hf) (coordinate_pairs H hH hdiag htau i j ha hb)
  rwa [hia, hjb] at h

private theorem full_same_prod_pairs {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0)
    (hprim : IsPrimitiveRoot ω 3) (hcube : ∀ a : K, a ≠ 0 → a ^ 3 = 1)
    (H : Subgroup ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)))
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3))
    (hdiag : ∀ a : Fin 3 → Kˣ, diagonal (F := F) a ∈ H)
    (htau : ∀ i j : Fin 3, i ≠ j → tauAt E i * tauAt E j ∈ H)
    (hf : fourier (F := F) hσ hs ∈ H)
    (u v : Fin 3 → K) (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0)
    (hp : u 0 * u 1 * u 2 = v 0 * v 1 * v 2) :
    reflect (Qn E 3) u * reflect (Qn E 3) v ∈ H := by
  let c := u 0 * u 1 * u 2
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (hu 0) (hu 1)) (hu 2)
  let μ : Fin 3 → Kˣ := fun i => if i = 0 then (Units.mk0 c hc)⁻¹ else 1
  let d := diagonal (F := F) μ
  have hd : d ∈ H := hdiag μ
  have hu' : ∀ i, d u i ≠ 0 := by
    intro i
    change diagonal (F := F) μ u i ≠ 0
    rw [diagonal_apply]
    exact mul_ne_zero (Units.ne_zero _) (hu i)
  have hv' : ∀ i, d v i ≠ 0 := by
    intro i
    change diagonal (F := F) μ v i ≠ 0
    rw [diagonal_apply]
    exact mul_ne_zero (Units.ne_zero _) (hv i)
  have hup : d u 0 * d u 1 * d u 2 = 1 := by
    calc
      d u 0 * d u 1 * d u 2 = c⁻¹ * (u 0 * u 1 * u 2) := by
        simp [d, μ, diagonal_apply]
        ring
      _ = 1 := inv_mul_cancel₀ hc
  have hvp : d v 0 * d v 1 * d v 2 = 1 := by
    calc
      d v 0 * d v 1 * d v 2 = c⁻¹ * (v 0 * v 1 * v 2) := by
        simp [d, μ, diagonal_apply]
        ring
      _ = c⁻¹ * (u 0 * u 1 * u 2) := by rw [← hp]
      _ = 1 := inv_mul_cancel₀ hc
  have h := full_prod_one_pairs hσ hs hprim hcube H hH hdiag htau hf
    (d u) (d v) hu' hv' hup hvp
  have h' := pair_conj (H.inv_mem hd) (hH (H.inv_mem hd)) h
  have hund (x : Fin 3 → K) : (d⁻¹) (d x) = x := d.symm_apply_apply x
  simpa only [hund] using h'

private theorem full_pairs {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0)
    (hprim : IsPrimitiveRoot ω 3) (hcube : ∀ a : K, a ≠ 0 → a ^ 3 = 1)
    (H : Subgroup ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)))
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3))
    (hdiag : ∀ a : Fin 3 → Kˣ, diagonal (F := F) a ∈ H)
    (htau : ∀ i j : Fin 3, i ≠ j → tauAt E i * tauAt E j ∈ H)
    (hf : fourier (F := F) hσ hs ∈ H)
    (u v : Fin 3 → K) (hu : ∀ i, u i ≠ 0) (hv : ∀ i, v i ≠ 0) :
    reflect (Qn E 3) u * reflect (Qn E 3) v ∈ H := by
  let c := u 0 * u 1 * u 2
  let d := v 0 * v 1 * v 2
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (hu 0) (hu 1)) (hu 2)
  have hd : d ≠ 0 := mul_ne_zero (mul_ne_zero (hv 0) (hv 1)) (hv 2)
  have hc3 := hcube c hc
  have hd3 := hcube d hd
  let pc : Fin 3 → K := ![1, c, c ^ 2]
  let pd : Fin 3 → K := ![1, d, d ^ 2]
  let rc : Fin 3 → K := ![1, c ^ 2, c ^ 2]
  let rd : Fin 3 → K := ![1, d ^ 2, d ^ 2]
  have hpc : ∀ i, pc i ≠ 0 := by intro i; fin_cases i <;> simp [pc, hc]
  have hpd : ∀ i, pd i ≠ 0 := by intro i; fin_cases i <;> simp [pd, hd]
  have hrc : ∀ i, rc i ≠ 0 := by intro i; fin_cases i <;> simp [rc, hc]
  have hrd : ∀ i, rd i ≠ 0 := by intro i; fin_cases i <;> simp [rd, hd]
  have hpcp : pc 0 * pc 1 * pc 2 = 1 := by
    change 1 * c * c ^ 2 = 1
    calc 1 * c * c ^ 2 = c ^ 3 := by ring
         _ = 1 := hc3
  have hpdp : pd 0 * pd 1 * pd 2 = 1 := by
    change 1 * d * d ^ 2 = 1
    calc 1 * d * d ^ 2 = d ^ 3 := by ring
         _ = 1 := hd3
  have hrcp : rc 0 * rc 1 * rc 2 = c := by
    change 1 * c ^ 2 * c ^ 2 = c
    calc 1 * c ^ 2 * c ^ 2 = c ^ 3 * c := by ring
         _ = c := by rw [hc3, one_mul]
  have hrdp : rd 0 * rd 1 * rd 2 = d := by
    change 1 * d ^ 2 * d ^ 2 = d
    calc 1 * d ^ 2 * d ^ 2 = d ^ 3 * d := by ring
         _ = d := by rw [hd3, one_mul]
  let t := tauAt E (0 : Fin 3) * tauAt E (1 : Fin 3)
  have ht : t ∈ H := htau 0 1 (by decide)
  have htc : t pc = rc := by
    ext i
    fin_cases i <;> simp [t, pc, rc, LinearEquiv.mul_apply, tauAt_apply]
    rfl
  have htd : t pd = rd := by
    ext i
    fin_cases i <;> simp [t, pd, rd, LinearEquiv.mul_apply, tauAt_apply]
    rfl
  have hmiddle := pair_conj ht (hH ht)
    (full_prod_one_pairs hσ hs hprim hcube H hH hdiag htau hf pc pd hpc hpd hpcp hpdp)
  rw [htc, htd] at hmiddle
  have hleft := full_same_prod_pairs hσ hs hprim hcube H hH hdiag htau hf
    u rc hu hrc hrcp.symm
  have hright := full_same_prod_pairs hσ hs hprim hcube H hH hdiag htau hf
    rd v hrd hv hrdp
  exact pair_trans hleft (pair_trans hmiddle hright)

private theorem norm_nonzero (hF : Nat.card F = 2) {a : K} (ha : a ≠ 0) :
    normQuad E a = 1 := by
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (0 : F)).1 hF
  have hn : normQuad E a ≠ 0 := fun h => ha ((normQuad_eq_zero_iff E).mp h)
  exact (huniq _ hn).trans (huniq 1 one_ne_zero).symm

private theorem norm_one_support (hF : Nat.card F = 2) (v : Fin 3 → K)
    (hQ : Qn E 3 v = 1) :
    (∃ (i : Fin 3) (a : K), a ≠ 0 ∧ v = Pi.single i a) ∨ (∀ i, v i ≠ 0) := by
  have : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  rw [Qn_apply, Fin.sum_univ_three] at hQ
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · by_cases h2 : v 2 = 0
      · simp [h0, h1, h2] at hQ
      · left
        refine ⟨2, v 2, h2, ?_⟩
        ext i
        fin_cases i <;> simp_all
    · by_cases h2 : v 2 = 0
      · left
        refine ⟨1, v 1, h1, ?_⟩
        ext i
        fin_cases i <;> simp_all
      · rw [h0, norm_nonzero hF h1, norm_nonzero hF h2] at hQ
        simp [CharTwo.add_self_eq_zero] at hQ
  · by_cases h1 : v 1 = 0
    · by_cases h2 : v 2 = 0
      · left
        refine ⟨0, v 0, h0, ?_⟩
        ext i
        fin_cases i <;> simp_all
      · rw [h1, norm_nonzero hF h0, norm_nonzero hF h2] at hQ
        simp [CharTwo.add_self_eq_zero] at hQ
    · by_cases h2 : v 2 = 0
      · rw [h2, norm_nonzero hF h0, norm_nonzero hF h1] at hQ
        simp [CharTwo.add_self_eq_zero] at hQ
      · right
        intro i
        fin_cases i <;> assumption

private theorem derived_le_of_pairs {R V : Type*} [Field R] [Finite R] [CharP R 2]
    [AddCommGroup V] [Module R V] [FiniteDimensional R V] {Q : QuadraticForm R V}
    (hQ : Q.polarBilin.Nondegenerate) (hd : 6 ≤ Module.finrank R V)
    (H : Subgroup (V ≃ₗ[R] V))
    (hpairs : ∀ u v : V, Q u = 1 → Q v = 1 → reflect Q u * reflect Q v ∈ H) :
    orthDerived Q ≤ H := by
  let S : Set (V ≃ₗ[R] V) := reflect Q '' {v | Q v = 1}
  let P : Subgroup (V ≃ₗ[R] V) := Subgroup.closure
    {g | ∃ u v : V, Q u = 1 ∧ Q v = 1 ∧ g = reflect Q u * reflect Q v}
  have hPH : P ≤ H := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨u, v, hu, hv, rfl⟩
    exact hpairs u v hu hv
  have hPO : P ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨u, v, -, -, rfl⟩
    exact mul_mem (reflect_mem_orthogonalGroup Q u) (reflect_mem_orthogonalGroup Q v)
  have hSO : S ⊆ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨u, -, rfl⟩
    exact reflect_mem_orthogonalGroup Q u
  have hPN : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      ∀ x ∈ P, g * x * g⁻¹ ∈ P := by
    intro g hg x hx
    change x ∈ Subgroup.closure _ at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨u, v, hu, hv, rfl⟩ := hx
      have heq : g * (reflect Q u * reflect Q v) * g⁻¹ =
          reflect Q (g u) * reflect Q (g v) := by
        rw [← reflect_conj hg u, ← reflect_conj hg v]
        group
      rw [heq]
      exact Subgroup.subset_closure ⟨g u, g v,
        by rw [map_of_mem hg, hu], by rw [map_of_mem hg, hv], rfl⟩
    | one => simpa only [mul_one, mul_inv_cancel] using P.one_mem
    | mul a b ha hb iha ihb =>
      have heq : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [heq]
      exact P.mul_mem iha ihb
    | inv a ha iha =>
      have heq : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [heq]
      exact P.inv_mem iha
  have hOP : TauCeti.QuadraticMap.orthogonalGroup Q ≤ Subgroup.closure (S ∪ P) := by
    rw [orthogonalGroup_eq_closure_reflect_of_finite hQ hd]
    exact Subgroup.closure_mono Set.subset_union_left
  have hcomm : ∀ s ∈ S, ∀ t ∈ S, ⁅s, t⁆ ∈ P := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have hp : reflect Q u * reflect Q v ∈ P :=
      Subgroup.subset_closure ⟨u, v, hu, hv, rfl⟩
    rw [commutatorElement_def, reflect_inv, reflect_inv]
    simpa only [mul_assoc] using P.mul_mem hp hp
  exact (commutator_le_of_le_closure hPN hPO hSO hOP hcomm).trans hPH

private theorem all_norm_pairs {ω : K}
    (hF : Nat.card F = 2)
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0)
    (hprim : IsPrimitiveRoot ω 3) (hcube : ∀ a : K, a ≠ 0 → a ^ 3 = 1)
    (H : Subgroup ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)))
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3))
    (hdiag : ∀ a : Fin 3 → Kˣ, diagonal (F := F) a ∈ H)
    (htau : ∀ i j : Fin 3, i ≠ j → tauAt E i * tauAt E j ∈ H)
    (hf : fourier (F := F) hσ hs ∈ H) :
    ∀ u v : Fin 3 → K, Qn E 3 u = 1 → Qn E 3 v = 1 →
      reflect (Qn E 3) u * reflect (Qn E 3) v ∈ H := by
  have hω3 : ω ^ 3 = 1 := hprim.pow_eq_one
  have hω0 : ω ≠ 0 := by intro h; simp [h] at hω3
  let a0 : Fin 3 → K := ![1, 1, 1]
  let b0 : Fin 3 → K := ![1, 1, ω]
  let w0 : Fin 3 → K := ![ω, ω, 1]
  have ha0 : ∀ i, a0 i ≠ 0 := by intro i; fin_cases i <;> simp [a0]
  have hb0 : ∀ i, b0 i ≠ 0 := by intro i; fin_cases i <;> simp [b0, hω0]
  have hw0 : ∀ i, w0 i ≠ 0 := by intro i; fin_cases i <;> simp [w0, hω0]
  have hfa : fourier (F := F) hσ hs a0 = Pi.single 0 1 := by
    rw [fourier_apply]
    ext i
    fin_cases i
    · simp [a0, CharTwo.add_self_eq_zero]
    · simpa [a0] using hs
    · simpa [a0, add_comm, add_left_comm, add_assoc] using hs
  have hfb : fourier (F := F) hσ hs b0 = w0 := by
    rw [fourier_apply]
    ext i
    fin_cases i <;> simp [b0, w0, ← pow_succ, ← pow_two, hω3,
      add_comm, add_left_comm, CharTwo.add_self_eq_zero]
  have hcross := pair_conj hf (hH hf)
    (full_pairs hσ hs hprim hcube H hH hdiag htau hf a0 b0 ha0 hb0)
  rw [hfa, hfb] at hcross
  have hcf : ∀ (i : Fin 3) (a : K), a ≠ 0 → ∀ v : Fin 3 → K,
      (∀ j, v j ≠ 0) → reflect (Qn E 3) (Pi.single i a) * reflect (Qn E 3) v ∈ H := by
    intro i a ha v hv
    exact pair_trans (coordinate_pairs H hH hdiag htau i 0 ha one_ne_zero)
      (pair_trans hcross (full_pairs hσ hs hprim hcube H hH hdiag htau hf w0 v hw0 hv))
  intro u v hu hv
  rcases norm_one_support hF u hu with ⟨i, a, ha, rfl⟩ | hu'
  · rcases norm_one_support hF v hv with ⟨j, b, hb, rfl⟩ | hv'
    · exact coordinate_pairs H hH hdiag htau i j ha hb
    · exact hcf i a ha v hv'
  · rcases norm_one_support hF v hv with ⟨j, b, hb, rfl⟩ | hv'
    · exact pair_symm (hcf j b hb u hu')
    · exact full_pairs hσ hs hprim hcube H hH hdiag htau hf u v hu' hv'

private theorem derived_le_of_generators {ω : K}
    (hF : Nat.card F = 2)
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0)
    (H : Subgroup ((Fin 3 → K) ≃ₗ[F] (Fin 3 → K)))
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3))
    (hdiag : ∀ a : Fin 3 → Kˣ, diagonal (F := F) a ∈ H)
    (htau : ∀ i j : Fin 3, i ≠ j → tauAt E i * tauAt E j ∈ H)
    (hf : fourier (F := F) hσ hs ∈ H) : orthDerived (Qn E 3) ≤ H := by
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := RingHom.charP (algebraMap F K) (algebraMap F K).injective 2
  have hK : Nat.card K = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := K), E.finrank_eq, hF]
    norm_num
  have hKU : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hcube : ∀ a : K, a ≠ 0 → a ^ 3 = 1 := by
    intro a ha
    have h := pow_card_eq_one' (G := Kˣ) (x := Units.mk0 a ha)
    rw [hKU] at h
    simpa using congrArg Units.val h
  have hω3 : ω ^ 3 = 1 := CFSG.AGLEmbedding.cube_eq_one_of_sum hs
  have hω1 : ω ≠ 1 := by
    intro h
    have hh := hs
    rw [h] at hh
    simp [CharTwo.add_self_eq_zero] at hh
  have hprim : IsPrimitiveRoot ω 3 := by
    have : Fact (Nat.Prime 3) := ⟨by decide⟩
    rw [← orderOf_eq_prime hω3 hω1]
    exact IsPrimitiveRoot.orderOf ω
  exact derived_le_of_pairs (Qn_polarBilin_nondegenerate E 3)
    (by rw [finrank_Qn E 3]) H
    (all_norm_pairs hF hσ hs hprim hcube H hH hdiag htau hf)

private theorem exists_diagonal_mem_decomp (hF : Nat.card F = 2) (a : Fin 3 → Kˣ) :
    ∃ g : normOmega E 3, g ∈ normDecompositionStabilizer E 3 ∧
      g.1 = hypExt (diagonal (F := F) a) := by
  have ha : ∀ i, (a i : K) * unitaryInvolution K 2 1 (a i : K) = 1 := by
    intro i
    have h := congrArg (algebraMap F K) (norm_nonzero (E := E) hF (Units.ne_zero (a i)))
    rwa [algebraMap_normQuad, map_one] at h
  have hgO := diagonal_mem_orthogonal (E := E) a ha
  have hKg : ∀ (c : K) (v : Fin 3 → K), diagonal (F := F) a (c • v) =
      c • diagonal (F := F) a v := by
    intro c v
    ext i
    simp [diagonal_apply, Pi.smul_apply, smul_eq_mul]
    ring
  let g : normOmega E 3 := ⟨hypExt (diagonal (F := F) a),
    hypExt_mem_orthDerived_of_kLinear E (by decide : 2 ≤ 3) hgO hKg⟩
  refine ⟨g, decomp_mem_of_fix_planes g ?_ ?_, rfl⟩
  · rw [mem_normAnchorFixing_iff]
    intro w
    change hypExt (diagonal (F := F) a) (w, 0) = (w, 0)
    simp only [hypExt_apply, map_zero]
  · intro i
    apply fix_plane_of_action g i (Units.mulLeftLinearEquiv F K (a i))
    intro x
    change hypExt (diagonal (F := F) a) (0, Pi.single i x) =
      (0, Pi.single i (Units.mulLeftLinearEquiv F K (a i) x))
    rw [hypExt_apply]
    congr 1
    ext j
    by_cases hji : j = i
    · subst j
      simp [diagonal_apply]
    · simp [diagonal_apply, Pi.single_eq_of_ne hji]

private theorem normPerm_conj_tauAt (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (normPerm E le_rfl σ).1 * hypExt (tauAt E i) * (normPerm E le_rfl σ).1⁻¹ =
      hypExt (tauAt E (σ i)) := by
  let P : Equiv.Perm (Fin 3) →*
      (((F × F) × (Fin 3 → K)) ≃ₗ[F] ((F × F) × (Fin 3 → K))) :=
    (normOmega E 3).subtype.comp (normPerm E le_rfl)
  have happ (π : Equiv.Perm (Fin 3)) (v : (F × F) × (Fin 3 → K)) :
      P π v = (v.1, fun k => v.2 (π⁻¹ k)) := normPerm_apply E le_rfl π v
  change P σ * hypExt (tauAt E i) * (P σ)⁻¹ = hypExt (tauAt E (σ i))
  rw [← P.map_inv]
  apply LinearEquiv.ext
  intro v
  simp only [LinearEquiv.mul_apply, happ, hypExt_apply, inv_inv]
  apply Prod.ext
  · rfl
  · ext k
    simp only [tauAt_apply]
    by_cases hk : k = σ i
    · subst k
      simp
    · have hki : σ⁻¹ k ≠ i := by
        intro h
        apply hk
        calc k = σ (σ⁻¹ k) := (σ.apply_symm_apply k).symm
             _ = σ i := by rw [h]
      have hki' : σ.symm k ≠ i := hki
      simp [hk, hki']

private theorem exists_pair_tau_mem_decomp (i j : Fin 3) :
    ∃ g : normOmega E 3, g ∈ normDecompositionStabilizer E 3 ∧
      g.1 = hypExt (tauAt E i * tauAt E j) := by
  let a := hypExt (tauAt E i)
  let p : normOmega E 3 := normPerm E le_rfl (Equiv.swap i j)
  have haO : a ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 3) :=
    hypExt_mem (tauAt_mem_orthogonalGroup E i)
  have hpO : p.1 ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 3) :=
    Subgroup.commutator_le_self _ p.2
  have hc : ⁅a, p.1⁆ ∈ normOmega E 3 := Subgroup.commutator_mem_commutator haO hpO
  have ha2 : a * a = 1 := by
    change hypExtHom (F := F) (K := K) 3 (tauAt E i) *
      hypExtHom (F := F) (K := K) 3 (tauAt E i) = 1
    rw [← map_mul, tauAt_mul_self, map_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_left ha2
  have hconj : p.1 * a * p.1⁻¹ = hypExt (tauAt E j) := by
    simpa only [Equiv.swap_apply_left] using
      normPerm_conj_tauAt (E := E) (Equiv.swap i j) i
  have heq : ⁅a, p.1⁆ = hypExt (tauAt E i * tauAt E j) := by
    rw [commutatorElement_def, hainv]
    calc
      a * p.1 * a * p.1⁻¹ = a * (p.1 * a * p.1⁻¹) := by group
      _ = a * hypExt (tauAt E j) := by rw [hconj]
      _ = hypExt (tauAt E i * tauAt E j) :=
        (map_mul (hypExtHom (F := F) (K := K) 3) _ _).symm
  let g : normOmega E 3 := ⟨⁅a, p.1⁆, hc⟩
  have hg : g.1 = hypExt (tauAt E i * tauAt E j) := heq
  refine ⟨g, decomp_mem_of_fix_planes g ?_ ?_, hg⟩
  · rw [mem_normAnchorFixing_iff]
    intro w
    rw [hg, hypExt_apply, map_zero]
  · intro k
    let f : K ≃ₗ[F] K :=
      (if k = i then E.sigmaEquiv else LinearEquiv.refl F K) *
        (if k = j then E.sigmaEquiv else LinearEquiv.refl F K)
    apply fix_plane_of_action g k f
    intro x
    rw [hg, hypExt_apply]
    congr 1
    ext l
    by_cases hlk : l = k
    · subst l
      simp only [LinearEquiv.mul_apply, tauAt_apply, Pi.single_eq_same]
      by_cases hki : k = i
      · by_cases hkj : k = j
        · simp only [f, if_pos hki, if_pos hkj, LinearEquiv.mul_apply]
          rfl
        · simp only [f, if_pos hki, if_neg hkj, LinearEquiv.mul_apply, LinearEquiv.refl_apply]
          rfl
      · by_cases hkj : k = j
        · simp only [f, if_neg hki, if_pos hkj, LinearEquiv.mul_apply, LinearEquiv.refl_apply]
          rfl
        · simp only [f, if_neg hki, if_neg hkj, LinearEquiv.mul_apply, LinearEquiv.refl_apply]
    · simp [LinearEquiv.mul_apply, tauAt_apply, Pi.single_eq_of_ne hlk]

private theorem hypExt_pullback_le_orthogonal (H : Subgroup (normOmega E 3)) :
    (H.map (normOmega E 3).subtype).comap (hypExtHom (F := F) (K := K) 3) ≤
      TauCeti.QuadraticMap.orthogonalGroup (Qn E 3) := by
  intro t ht
  change hypExt t ∈ H.map (normOmega E 3).subtype at ht
  obtain ⟨g, _, heq⟩ := Subgroup.mem_map.mp ht
  have hgO : g.1 ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E 3) :=
    Subgroup.commutator_le_self _ g.2
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  have hp := map_of_mem hgO ((0 : F × F), v)
  change g.1 = hypExt t at heq
  rw [heq] at hp
  simpa [normHypForm, hypExt_apply, hypSum_apply] using hp

private theorem mem_normBlock_of_hypExt_fixes {S : Finset (Fin 3)} (hS : 2 ≤ S.card)
    (g : normOmega E 3) (t : (Fin 3 → K) ≃ₗ[F] (Fin 3 → K))
    (ht : g.1 = hypExt t)
    (hfix : ∀ v : Fin 3 → K, (∀ i ∈ S, v i = 0) → t v = v) :
    g ∈ normBlock E 3 S := by
  rw [mem_normBlock_iff_fixes_suppPerp E hS]
  intro v hv
  have hz := ((mem_suppPerp_coordSupport_refl_iff E S v).mp hv).2
  rw [ht, hypExt_apply, hfix v.2 hz]

private theorem exists_single_diagonal_mem_pair (hF : Nat.card F = 2)
    (i j : Fin 3) (hij : i ≠ j) (u : Kˣ) :
    ∃ g : normOmega E 3, g ∈ normBlock E 3 {i, j} ⊓ normAnchorFixing E 3 ∧
      g.1 = hypExt (diagonal (F := F) (fun k : Fin 3 => if k = i then u else 1)) := by
  classical
  let a : Fin 3 → Kˣ := fun k => if k = i then u else 1
  obtain ⟨g, hg, heq⟩ := exists_diagonal_mem_decomp (E := E) hF a
  refine ⟨g, ⟨?_, hg.1⟩, heq⟩
  apply mem_normBlock_of_hypExt_fixes (E := E) (by rw [Finset.card_pair hij])
    g (diagonal (F := F) a) heq
  intro v hv
  ext k
  by_cases hki : k = i
  · subst k
    simp [diagonal_apply, a, hv i (by simp)]
  · simp [diagonal_apply, a, hki]

private theorem exists_pair_tau_mem_pair (i j : Fin 3) (hij : i ≠ j) :
    ∃ g : normOmega E 3, g ∈ normBlock E 3 {i, j} ⊓ normAnchorFixing E 3 ∧
      g.1 = hypExt (tauAt E i * tauAt E j) := by
  classical
  obtain ⟨g, hg, heq⟩ := exists_pair_tau_mem_decomp (E := E) i j
  refine ⟨g, ⟨?_, hg.1⟩, heq⟩
  apply mem_normBlock_of_hypExt_fixes (E := E) (by rw [Finset.card_pair hij])
    g (tauAt E i * tauAt E j) heq
  intro v hv
  have hvi : v i = 0 := hv i (by simp)
  have hvj : v j = 0 := hv j (by simp)
  ext k
  by_cases hki : k = i
  · subst k
    simp [LinearEquiv.mul_apply, tauAt_apply, hvi, hij]
  · by_cases hkj : k = j
    · subst k
      simp [LinearEquiv.mul_apply, tauAt_apply, hvj, hij.symm]
    · simp [LinearEquiv.mul_apply, tauAt_apply, hki, hkj]

omit [Finite K] [CharP K 2] in
private theorem diagonal_eq_three_single (a : Fin 3 → Kˣ) :
    diagonal (F := F) a =
      diagonal (F := F) (fun k : Fin 3 => if k = 0 then a 0 else 1) *
      diagonal (F := F) (fun k : Fin 3 => if k = 1 then a 1 else 1) *
      diagonal (F := F) (fun k : Fin 3 => if k = 2 then a 2 else 1) := by
  ext v k
  fin_cases k <;> simp [LinearEquiv.mul_apply, diagonal_apply]

end NormThreeFourier

theorem isSimpleGroup_normAnchorFixing_three (hF : Nat.card F = 2) :
    IsSimpleGroup ↥(normAnchorFixing E 3) := by
  clear hF
  have : IsSimpleGroup (orthDerived (Qn E 3)) :=
    isSimpleGroup_orthDerived_Qn_of_three_le E (by decide : 3 ≤ 3)
  let f := pureEmb E (Function.Embedding.refl (Fin 3))
  have hrange : f.range = normAnchorFixing E 3 := by
    simp only [f, range_pureEmb, Finset.map_refl,
      normPureBlock_univ_three_eq_normAnchorFixing]
  let e := (MonoidHom.ofInjective (f := f)
    (pureEmb_injective E (Function.Embedding.refl (Fin 3)))).trans
      (MulEquiv.subgroupCongr hrange)
  exact e.symm.isSimpleGroup

open NormThreeFourier in
theorem normAnchorFixing_three_eq_sup_fourier (hF : Nat.card F = 2) {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0) :
    normAnchorFixing E 3 = normDecompositionStabilizer E 3 ⊔
      Subgroup.zpowers (threePlaneFourier E hσ hs) := by
  let H := normDecompositionStabilizer E 3 ⊔ Subgroup.zpowers (threePlaneFourier E hσ hs)
  let T := (H.map (normOmega E 3).subtype).comap (hypExtHom (F := F) (K := K) 3)
  have hTO : T ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn E 3) :=
    hypExt_pullback_le_orthogonal (E := E) H
  have hdiag : ∀ a : Fin 3 → Kˣ, diagonal (F := F) a ∈ T := by
    intro a
    obtain ⟨g, hg, heq⟩ := exists_diagonal_mem_decomp (E := E) hF a
    change hypExt (diagonal (F := F) a) ∈ H.map (normOmega E 3).subtype
    exact Subgroup.mem_map.mpr ⟨g,
      (show normDecompositionStabilizer E 3 ≤ H from le_sup_left) hg, heq⟩
  have htau : ∀ i j : Fin 3, i ≠ j → tauAt E i * tauAt E j ∈ T := by
    intro i j _
    obtain ⟨g, hg, heq⟩ := exists_pair_tau_mem_decomp (E := E) i j
    change hypExt (tauAt E i * tauAt E j) ∈ H.map (normOmega E 3).subtype
    exact Subgroup.mem_map.mpr ⟨g,
      (show normDecompositionStabilizer E 3 ≤ H from le_sup_left) hg, heq⟩
  have hf : fourier (F := F) hσ hs ∈ T := by
    change hypExt (fourier (F := F) hσ hs) ∈ H.map (normOmega E 3).subtype
    refine Subgroup.mem_map.mpr ⟨threePlaneFourier E hσ hs,
      (show Subgroup.zpowers (threePlaneFourier E hσ hs) ≤ H from le_sup_right)
        (Subgroup.mem_zpowers _), ?_⟩
    apply LinearEquiv.ext
    intro v
    change (suEmb E 3 (CFSG.AGLEmbedding.fourierElt hσ hs)).1 v =
      hypExt (fourier (F := F) hσ hs) v
    rw [suEmb_apply, hypExt_apply]
    rfl
  have hderived := derived_le_of_generators (E := E) hF hσ hs T hTO hdiag htau hf
  apply le_antisymm
  · intro g hg
    obtain ⟨t, ht, heq⟩ := exists_pure_of_anchor (E := E) g hg
    have ht' := hderived ht
    change hypExt t ∈ H.map (normOmega E 3).subtype at ht'
    obtain ⟨g', hg', heq'⟩ := Subgroup.mem_map.mp ht'
    have hgg : g' = g := Subtype.ext (heq'.trans heq.symm)
    rwa [hgg] at hg'
  · refine sup_le (fun g hg => hg.1) ?_
    exact Subgroup.zpowers_le.mpr (threePlaneFourier_mem_normAnchorFixing E hσ hs)

theorem map_normAnchorFixing_three_eq_sup_fourier {G : Type*} [Group G]
    (κ : normOmega E 3 →* G) (hF : Nat.card F = 2) {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0) :
    (normAnchorFixing E 3).map κ = (normDecompositionStabilizer E 3).map κ ⊔
      Subgroup.zpowers (κ (threePlaneFourier E hσ hs)) := by
  rw [normAnchorFixing_three_eq_sup_fourier E hF hσ hs, Subgroup.map_sup,
    MonoidHom.map_zpowers]

theorem map_normAnchorFixing_three_le {G : Type*} [Group G]
    (κ : normOmega E 3 →* G) (hF : Nat.card F = 2) {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0)
    {A : Subgroup G} (hN : (normDecompositionStabilizer E 3).map κ ≤ A)
    (hFou : κ (threePlaneFourier E hσ hs) ∈ A) : (normAnchorFixing E 3).map κ ≤ A := by
  rw [map_normAnchorFixing_three_eq_sup_fourier E κ hF hσ hs]
  exact sup_le hN (Subgroup.zpowers_le.mpr hFou)

theorem normPureBlock_univ_three_eq_sup_fourier (hF : Nat.card F = 2) {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0) :
    normPureBlock E 3 Finset.univ = normDecompositionStabilizer E 3 ⊔
      Subgroup.zpowers (threePlaneFourier E hσ hs) := by
  rw [normPureBlock_univ_three_eq_normAnchorFixing]
  exact normAnchorFixing_three_eq_sup_fourier E hF hσ hs

theorem map_normPureBlock_univ_three_eq_sup_fourier {G : Type*} [Group G]
    (κ : normOmega E 3 →* G) (hF : Nat.card F = 2) {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0) :
    (normPureBlock E 3 Finset.univ).map κ = (normDecompositionStabilizer E 3).map κ ⊔
      Subgroup.zpowers (κ (threePlaneFourier E hσ hs)) := by
  rw [normPureBlock_univ_three_eq_normAnchorFixing]
  exact map_normAnchorFixing_three_eq_sup_fourier E κ hF hσ hs

theorem map_normPureBlock_univ_three_le {G : Type*} [Group G]
    (κ : normOmega E 3 →* G) (hF : Nat.card F = 2) {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0)
    {A : Subgroup G} (hN : (normDecompositionStabilizer E 3).map κ ≤ A)
    (hFou : κ (threePlaneFourier E hσ hs) ∈ A) :
    (normPureBlock E 3 Finset.univ).map κ ≤ A := by
  rw [normPureBlock_univ_three_eq_normAnchorFixing]
  exact map_normAnchorFixing_three_le E κ hF hσ hs hN hFou

open NormThreeFourier in
theorem map_normAnchorFixing_three_le_of_pairs {G : Type*} [Group G]
    (κ : normOmega E 3 →* G) (hF : Nat.card F = 2) {ω : K}
    (hσ : unitaryInvolution K 2 1 ω = ω ^ 2) (hs : 1 + ω + ω ^ 2 = 0)
    {A : Subgroup G}
    (hP : ∀ S : Finset (Fin 3), S.card = 2 →
      (normBlock E 3 S ⊓ normAnchorFixing E 3).map κ ≤ A)
    (hFou : κ (threePlaneFourier E hσ hs) ∈ A) :
    (normAnchorFixing E 3).map κ ≤ A := by
  classical
  let H := A.comap κ
  let T := (H.map (normOmega E 3).subtype).comap (hypExtHom (F := F) (K := K) 3)
  have hsingle : ∀ i j : Fin 3, i ≠ j → ∀ u : Kˣ,
      diagonal (F := F) (fun k : Fin 3 => if k = i then u else 1) ∈ T := by
    intro i j hij u
    obtain ⟨g, hg, heq⟩ := exists_single_diagonal_mem_pair (E := E) hF i j hij u
    have hgH : g ∈ H := hP {i, j} (Finset.card_pair hij) (Subgroup.mem_map_of_mem κ hg)
    change hypExt (diagonal (F := F) (fun k : Fin 3 => if k = i then u else 1)) ∈
      H.map (normOmega E 3).subtype
    exact Subgroup.mem_map.mpr ⟨g, hgH, heq⟩
  have hdiag : ∀ a : Fin 3 → Kˣ, diagonal (F := F) a ∈ T := by
    intro a
    rw [diagonal_eq_three_single]
    exact mul_mem (mul_mem (hsingle 0 1 (by decide) (a 0))
      (hsingle 1 0 (by decide) (a 1))) (hsingle 2 0 (by decide) (a 2))
  have htau : ∀ i j : Fin 3, i ≠ j → tauAt E i * tauAt E j ∈ T := by
    intro i j hij
    obtain ⟨g, hg, heq⟩ := exists_pair_tau_mem_pair (E := E) i j hij
    have hgH : g ∈ H := hP {i, j} (Finset.card_pair hij) (Subgroup.mem_map_of_mem κ hg)
    change hypExt (tauAt E i * tauAt E j) ∈ H.map (normOmega E 3).subtype
    exact Subgroup.mem_map.mpr ⟨g, hgH, heq⟩
  have hf : fourier (F := F) hσ hs ∈ T := by
    change hypExt (fourier (F := F) hσ hs) ∈ H.map (normOmega E 3).subtype
    refine Subgroup.mem_map.mpr ⟨threePlaneFourier E hσ hs, hFou, ?_⟩
    apply LinearEquiv.ext
    intro v
    change (suEmb E 3 (CFSG.AGLEmbedding.fourierElt hσ hs)).1 v =
      hypExt (fourier (F := F) hσ hs) v
    rw [suEmb_apply, hypExt_apply]
    rfl
  have hderived := derived_le_of_generators (E := E) hF hσ hs T
    (hypExt_pullback_le_orthogonal (E := E) H) hdiag htau hf
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨t, ht, heq⟩ := exists_pure_of_anchor (E := E) g hg
  have ht' := hderived ht
  change hypExt t ∈ H.map (normOmega E 3).subtype at ht'
  obtain ⟨g', hg', heq'⟩ := Subgroup.mem_map.mp ht'
  have hgg : g' = g := Subtype.ext (heq'.trans heq.symm)
  change κ g' ∈ A at hg'
  rwa [hgg] at hg'

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
