module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PureBlockDefs
public import CFSG.ClassicalInvolution.Phan.PhanDn.NormFormType
public import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.RankThree.GF2n.Smith81.OrthE2MinusTwo
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import CFSG.LieType.SeitzGeneration.ExcHigh.SpinFrameToral

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2

open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f))

section CoordExt

variable {k n p : ℕ}

omit [Finite K] [CharP K 2] in
private noncomputable def coordLin (e : Fin k ↪ Fin n)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) :
    (Fin n → K) →ₗ[F] (Fin n → K) where
  toFun x := Function.extend e (g (x ∘ e)) x
  map_add' x y := by
    have h : g ((x + y) ∘ e) = g (x ∘ e) + g (y ∘ e) := by
      rw [show (x + y) ∘ e = (x ∘ e) + (y ∘ e) from rfl, map_add]
    rw [h]
    exact Function.extend_add e (g (x ∘ e)) (g (y ∘ e)) x y
  map_smul' c x := by
    have h : g ((c • x) ∘ e) = c • g (x ∘ e) := by
      rw [show (c • x) ∘ e = c • (x ∘ e) from rfl, map_smul]
    rw [h]
    exact Function.extend_smul c e (g (x ∘ e)) x

omit [Finite K] [CharP K 2] in
private theorem coordLin_apply (e : Fin k ↪ Fin n)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) (x : Fin n → K) :
    coordLin e g x = Function.extend e (g (x ∘ e)) x := rfl

omit [Finite K] [CharP K 2] in
private theorem coordLin_one (e : Fin k ↪ Fin n) :
    coordLin e (1 : (Fin k → K) ≃ₗ[F] (Fin k → K)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change Function.extend e (x ∘ e) x = x
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [e.injective.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ hj]

omit [Finite K] [CharP K 2] in
private theorem coordLin_mul_apply (e : Fin k ↪ Fin n)
    (g g' : (Fin k → K) ≃ₗ[F] (Fin k → K)) (x : Fin n → K) :
    coordLin e g (coordLin e g' x) = coordLin e (g * g') x := by
  change Function.extend e (g ((Function.extend e (g' (x ∘ e)) x) ∘ e))
      (Function.extend e (g' (x ∘ e)) x) =
    Function.extend e ((g * g') (x ∘ e)) x
  rw [Function.extend_comp e.injective]
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [e.injective.extend_apply, e.injective.extend_apply, LinearEquiv.mul_apply]
  · rw [Function.extend_apply' _ _ _ hj, Function.extend_apply' _ _ _ hj,
      Function.extend_apply' _ _ _ hj]

omit [Finite K] [CharP K 2] in
private noncomputable def coordEquiv (e : Fin k ↪ Fin n)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) :
    (Fin n → K) ≃ₗ[F] (Fin n → K) :=
  LinearEquiv.ofLinearMap (coordLin e g) (coordLin e g⁻¹)
    (by
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply, coordLin_mul_apply, mul_inv_cancel, coordLin_one])
    (by
      apply LinearMap.ext
      intro x
      rw [LinearMap.comp_apply, coordLin_mul_apply, inv_mul_cancel, coordLin_one])

omit [Finite K] [CharP K 2] in
noncomputable def coordExt {k n : ℕ} (e : Fin k ↪ Fin n) :
    ((Fin k → K) ≃ₗ[F] (Fin k → K)) →* ((Fin n → K) ≃ₗ[F] (Fin n → K)) where
  toFun g := coordEquiv e g
  map_one' := by
    apply LinearEquiv.ext
    intro x
    change coordLin e 1 x = x
    rw [coordLin_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    change coordLin e (g * h) x = coordLin e g (coordLin e h x)
    rw [← coordLin_mul_apply]

omit [Finite K] [CharP K 2] in
theorem coordExt_apply (e : Fin k ↪ Fin n)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) (x : Fin n → K) :
    coordExt e g x = Function.extend e (g (x ∘ e)) x := by
  change coordEquiv e g x = Function.extend e (g (x ∘ e)) x
  rw [coordEquiv, LinearEquiv.coe_ofLinearMap]
  rfl

omit [Finite K] [CharP K 2] in
private theorem coordExt_apply_of_mem (e : Fin k ↪ Fin n)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) (x : Fin n → K) {i : Fin k} :
    coordExt e g x (e i) = g (x ∘ e) i := by
  rw [coordExt_apply, e.injective.extend_apply]

omit [Finite K] [CharP K 2] in
private theorem coordExt_apply_of_not_mem (e : Fin k ↪ Fin n)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) (x : Fin n → K) {j : Fin n}
    (hj : ¬ ∃ i, e i = j) : coordExt e g x j = x j := by
  rw [coordExt_apply, Function.extend_apply' _ _ _ hj]

omit [Finite K] [CharP K 2] in
private theorem coordExt_apply_of_eq_zero_on_range (e : Fin k ↪ Fin n)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) {x : Fin n → K}
    (hx : ∀ i, x (e i) = 0) : coordExt e g x = x := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [coordExt_apply_of_mem, show (x ∘ e) = 0 from funext hx, map_zero, Pi.zero_apply]
    exact (hx i).symm
  · rw [coordExt_apply_of_not_mem _ _ _ hj]

omit [Finite K] [CharP K 2] in
private theorem coordExt_apply_extendZero (e : Fin k ↪ Fin n)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) (y : Fin k → K) :
    coordExt e g (Function.extend e y 0) = Function.extend e (g y) 0 := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [coordExt_apply_of_mem, Function.extend_comp e.injective, e.injective.extend_apply]
  · rw [coordExt_apply_of_not_mem _ _ _ hj, Function.extend_apply' _ _ _ hj,
      Function.extend_apply' _ _ _ hj]

omit [Finite K] [CharP K 2] in
private theorem coordExt_injective (e : Fin k ↪ Fin n) :
    Function.Injective (coordExt (F := F) (K := K) e) := by
  intro g h hgh
  apply LinearEquiv.ext
  intro y
  funext i
  have h' : coordExt e g (Function.extend e y 0) (e i) =
      coordExt e h (Function.extend e y 0) (e i) := by rw [hgh]
  rwa [coordExt_apply_of_mem, coordExt_apply_of_mem, Function.extend_comp e.injective] at h'

omit [Finite K] [CharP K 2] in
theorem coordExt_trans (e : Fin k ↪ Fin n) (e' : Fin n ↪ Fin p)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) :
    coordExt e' (coordExt e g) = coordExt (e.trans e') g := by
  apply LinearEquiv.ext
  intro x
  rw [coordExt_apply, coordExt_apply, coordExt_apply]
  exact (Function.Injective.extend_comp e.injective e'.injective
    (g ((x ∘ e') ∘ e)) x).symm

theorem coordExt_tauAt (e : Fin k ↪ Fin n) (i : Fin k) :
    coordExt e (tauAt E i) = tauAt E (e i) := by
  apply LinearEquiv.ext
  intro x
  funext j
  by_cases hj : ∃ i0, e i0 = j
  · obtain ⟨i0, rfl⟩ := hj
    rw [coordExt_apply_of_mem, tauAt_apply, tauAt_apply]
    by_cases h : i0 = i
    · subst h
      simp
    · have h' : e i0 ≠ e i := fun hh => h (e.injective hh)
      simp [h, h']
  · rw [coordExt_apply_of_not_mem _ _ _ hj, tauAt_apply]
    have hne : j ≠ e i := fun h => hj ⟨i, h.symm⟩
    simp [hne]

private theorem Qn_extend_eq (e : Fin k ↪ Fin n) (y : Fin k → K) (x : Fin n → K) :
    Qn E n (Function.extend e y x) =
      Qn E k y + ∑ j ∈ (Finset.univ.map e)ᶜ, normQuad E (x j) := by
  rw [Qn_apply, Qn_apply, ← Finset.sum_add_sum_compl (Finset.univ.map e)
    (fun j => normQuad E (Function.extend e y x j))]
  congr 1
  · rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun i _ => by rw [e.injective.extend_apply]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Function.extend_apply' _ _ _ (by simpa using hj)]

omit [Field K] [Finite K] [CharP K 2] in
private theorem extend_comp_self (e : Fin k ↪ Fin n) (x : Fin n → K) :
    Function.extend e (x ∘ e) x = x := by
  funext j
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [e.injective.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ hj]

private theorem Qn_map_sum (e : Fin k ↪ Fin n) (x : Fin n → K) :
    ∑ j ∈ Finset.univ.map e, normQuad E (x j) = Qn E k (x ∘ e) := by
  rw [Qn_apply, Finset.sum_map]
  rfl

theorem coordExt_mem_orthogonalGroup (e : Fin k ↪ Fin n)
    {g : (Fin k → K) ≃ₗ[F] (Fin k → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E k)) :
    coordExt e g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E n) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  have hg' := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg) (x ∘ e)
  have hL : Qn E n (coordExt e g x) =
      Qn E k (g (x ∘ e)) + ∑ j ∈ (Finset.univ.map e)ᶜ, normQuad E (x j) := by
    rw [coordExt_apply, Qn_extend_eq E]
  have hR : Qn E n x =
      Qn E k (x ∘ e) + ∑ j ∈ (Finset.univ.map e)ᶜ, normQuad E (x j) := by
    conv_lhs => rw [← extend_comp_self e x]
    exact Qn_extend_eq E e (x ∘ e) x
  rw [hL, hR, hg']

section Pure

variable {k n p : ℕ}

omit [Finite K] [CharP K 2] in
private noncomputable def hypExtHom (n : ℕ) :
    ((Fin n → K) ≃ₗ[F] (Fin n → K)) →*
      (((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) where
  toFun g := hypExt (K := F) (W := Fin n → K) g
  map_one' := by
    apply LinearEquiv.ext
    intro p
    rw [hypExt_apply]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro p
    rw [LinearEquiv.mul_apply, hypExt_apply, hypExt_apply, hypExt_apply,
      LinearEquiv.mul_apply]

omit [Finite K] [CharP K 2] in
private theorem hypExt_injective (n : ℕ) :
    Function.Injective (fun g : (Fin n → K) ≃ₗ[F] (Fin n → K) =>
      hypExt (K := F) (W := Fin n → K) g) := by
  intro g h hgh
  apply LinearEquiv.ext
  intro y
  have := congrArg (fun f : ((F × F) × (Fin n → K)) ≃ₗ[F]
    ((F × F) × (Fin n → K)) => f (((0, 0), y) : (F × F) × (Fin n → K))) hgh
  simpa [hypExt_apply] using this

noncomputable def qnExtΩ (e : Fin k ↪ Fin n) :
    orthDerived (Qn E k) →* orthDerived (Qn E n) :=
  ((coordExt (F := F) (K := K) e).comp (orthDerived (Qn E k)).subtype).codRestrict
    (orthDerived (Qn E n)) (by
      intro g
      have hmap : (TauCeti.QuadraticMap.orthogonalGroup (Qn E k)).map
          (coordExt (F := F) (K := K) e) ≤
          TauCeti.QuadraticMap.orthogonalGroup (Qn E n) :=
        Subgroup.map_le_iff_le_comap.mpr fun h hh =>
          coordExt_mem_orthogonalGroup E e hh
      have hcomm : (orthDerived (Qn E k)).map (coordExt (F := F) (K := K) e) ≤
          orthDerived (Qn E n) := by
        calc
          (orthDerived (Qn E k)).map (coordExt (F := F) (K := K) e)
              = ⁅(TauCeti.QuadraticMap.orthogonalGroup (Qn E k)).map
                    (coordExt (F := F) (K := K) e),
                  (TauCeti.QuadraticMap.orthogonalGroup (Qn E k)).map
                    (coordExt (F := F) (K := K) e)⁆ := by
                rw [show orthDerived (Qn E k) =
                  ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E k),
                    TauCeti.QuadraticMap.orthogonalGroup (Qn E k)⁆ from rfl,
                  Subgroup.map_commutator]
          _ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E n),
                TauCeti.QuadraticMap.orthogonalGroup (Qn E n)⁆ :=
              Subgroup.commutator_mono hmap hmap
      exact hcomm (Subgroup.mem_map_of_mem _ g.2))

theorem qnExtΩ_apply (e : Fin k ↪ Fin n) (g : orthDerived (Qn E k)) :
    ((qnExtΩ E e g : orthDerived (Qn E n)) :
        (Fin n → K) ≃ₗ[F] (Fin n → K)) =
      coordExt (F := F) (K := K) e (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) := (rfl)

private noncomputable def pureHom (e : Fin k ↪ Fin n) :
    ((Fin k → K) ≃ₗ[F] (Fin k → K)) →*
      (((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) :=
  (hypExtHom (F := F) (K := K) n).comp (coordExt (F := F) (K := K) e)

private theorem pureHom_mem_normOmega (e : Fin k ↪ Fin n)
    {g : (Fin k → K) ≃ₗ[F] (Fin k → K)} (hg : g ∈ orthDerived (Qn E k)) :
    pureHom (F := F) (K := K) e g ∈ normOmega E n := by
  have hmapO : (TauCeti.QuadraticMap.orthogonalGroup (Qn E k)).map
      (pureHom (F := F) (K := K) e) ≤
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E n) :=
    Subgroup.map_le_iff_le_comap.mpr fun h hh =>
      hypExt_mem (Q' := Qn E n) (coordExt_mem_orthogonalGroup E e hh)
  have hcomm : (orthDerived (Qn E k)).map (pureHom (F := F) (K := K) e) ≤
      normOmega E n := by
    calc
      (orthDerived (Qn E k)).map (pureHom (F := F) (K := K) e)
          = ⁅(TauCeti.QuadraticMap.orthogonalGroup (Qn E k)).map
                (pureHom (F := F) (K := K) e),
              (TauCeti.QuadraticMap.orthogonalGroup (Qn E k)).map
                (pureHom (F := F) (K := K) e)⁆ := by
            rw [show orthDerived (Qn E k) =
              ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn E k),
                TauCeti.QuadraticMap.orthogonalGroup (Qn E k)⁆ from rfl,
              Subgroup.map_commutator]
      _ ≤ normOmega E n := Subgroup.commutator_mono hmapO hmapO
  exact hcomm (Subgroup.mem_map_of_mem (pureHom (F := F) (K := K) e) hg)

noncomputable def pureEmb (e : Fin k ↪ Fin n) :
    orthDerived (Qn E k) →* normOmega E n :=
  ((pureHom (F := F) (K := K) e).comp (orthDerived (Qn E k)).subtype).codRestrict
    (normOmega E n) (by
      intro g
      exact pureHom_mem_normOmega E e g.2)

private theorem pureEmb_coe (e : Fin k ↪ Fin n) (g : orthDerived (Qn E k)) :
    ((pureEmb E e g : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) =
      hypExt (K := F) (W := Fin n → K)
        (coordExt (F := F) (K := K) e (g : (Fin k → K) ≃ₗ[F] (Fin k → K))) := rfl

theorem pureEmb_apply (e : Fin k ↪ Fin n) (g : orthDerived (Qn E k))
    (v : (F × F) × (Fin n → K)) :
    ((pureEmb E e g : normOmega E n) :
      ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) v =
      (v.1, coordExt (F := F) (K := K) e g v.2) := by
  have hcoe : ((pureEmb E e g : normOmega E n) :
      ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) =
      hypExt (K := F) (W := Fin n → K)
        (coordExt (F := F) (K := K) e (g : (Fin k → K) ≃ₗ[F] (Fin k → K))) := rfl
  rw [hcoe, hypExt_apply]

theorem pureEmb_injective (e : Fin k ↪ Fin n) : Function.Injective (pureEmb E e) := by
  intro g h hgh
  have h' : hypExt (K := F) (W := Fin n → K)
      (coordExt (F := F) (K := K) e (g : (Fin k → K) ≃ₗ[F] (Fin k → K))) =
      hypExt (K := F) (W := Fin n → K)
        (coordExt (F := F) (K := K) e (h : (Fin k → K) ≃ₗ[F] (Fin k → K))) := by
    have := congrArg (fun z : normOmega E n =>
      ((z : normOmega E n) : ((F × F) × (Fin n → K)) ≃ₗ[F]
        ((F × F) × (Fin n → K)))) hgh
    simpa [pureEmb, pureHom, hypExtHom, MonoidHom.comp_apply] using this
  exact Subtype.ext (coordExt_injective e (hypExt_injective n h'))

section Support

omit [Finite K] [CharP K 2] in
private def planeSupport (S : Finset (Fin n)) : Submodule F ((F × F) × (Fin n → K)) :=
  S.sup (coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))))

omit [Finite K] [CharP K 2] in
private def pureSupport (e : Fin k ↪ Fin n) : Submodule F ((F × F) × (Fin n → K)) :=
  planeSupport (Finset.univ.map e)

omit [Finite K] [CharP K 2] in
private theorem planeSupport_insert {i : Fin n} {S : Finset (Fin n)} :
    planeSupport (insert i S) =
      planeSupport S ⊔ coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i := by
  rw [planeSupport, planeSupport, Finset.sup_insert, sup_comm]

omit [Finite K] [CharP K 2] in
private noncomputable def planeTo (e : Fin k ↪ Fin n) :
    (Fin k → K) →ₗ[F] ((F × F) × (Fin n → K)) where
  toFun y := ((0, 0), Function.extend e y 0)
  map_add' y z := by
    refine Prod.ext ?_ ?_
    · simp
    · simpa using Function.extend_add e y z (0 : Fin n → K) 0
  map_smul' c y := by
    refine Prod.ext ?_ ?_
    · simp
    · simpa using Function.extend_smul c e y (0 : Fin n → K)

omit [Finite K] [CharP K 2] in
private theorem mem_planeSupport_iff (S : Finset (Fin n))
    (v : (F × F) × (Fin n → K)) :
    v ∈ planeSupport S ↔ v.1 = 0 ∧ ∀ j, j ∉ S → v.2 j = 0 := by
  classical
  revert v
  induction S using Finset.induction_on with
  | empty =>
      intro v
      rw [planeSupport, Finset.sup_empty, Submodule.mem_bot]
      constructor
      · intro hv
        subst hv
        exact ⟨rfl, fun j _ => rfl⟩
      · rintro ⟨h1, h2⟩
        refine Prod.ext h1 ?_
        funext j
        exact h2 j (by simp)
  | insert i S hi ih =>
      intro v
      rw [planeSupport_insert, Submodule.mem_sup]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        obtain ⟨ha1, ha2⟩ := (ih a).mp ha
        obtain ⟨c, hc⟩ := mem_coordPlane.mp hb
        rw [← hc]
        refine ⟨by simp [ha1], fun j hj => ?_⟩
        have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self i S)
        have hjS : j ∉ S := fun h => hj (Finset.mem_insert_of_mem h)
        simp [ha2 j hjS, Pi.single_eq_of_ne hji]
      · rintro ⟨hv1, hv2⟩
        have hmem1 : v - ((0, 0), Pi.single i (v.2 i)) ∈ planeSupport S := by
          refine (ih _).mpr ⟨?_, fun j hj => ?_⟩
          · simp [hv1]
          · by_cases hji : j = i
            · subst hji
              simp
            · have hj' : j ∉ insert i S := fun h => by
                rcases Finset.mem_insert.mp h with h1 | h2
                · exact hji h1
                · exact hj h2
              simp [hv2 j hj', Pi.single_eq_of_ne hji]
        have hmem2 : ((0, 0), Pi.single i (v.2 i)) ∈
            coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i :=
          mem_coordPlane.mpr ⟨v.2 i, rfl⟩
        exact ⟨_, hmem1, _, hmem2, by abel⟩

omit [Finite K] [CharP K 2] in
private theorem planeTo_mem (e : Fin k ↪ Fin n) (y : Fin k → K) :
    planeTo (F := F) (K := K) e y ∈ pureSupport (F := F) (K := K) e := by
  refine (mem_planeSupport_iff (Finset.univ.map e) _).mpr ⟨rfl, fun j hj => ?_⟩
  change Function.extend e y 0 j = 0
  rw [Function.extend_apply' _ _ _ (by
    rintro ⟨i, rfl⟩
    exact hj (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩))]
  exact Pi.zero_apply j

omit [Finite K] [CharP K 2] in
private theorem planeTo_mem_iff (e : Fin k ↪ Fin n)
    (v : (F × F) × (Fin n → K)) :
    v ∈ pureSupport (F := F) (K := K) e ↔
      ∃ y, planeTo (F := F) (K := K) e y = v := by
  constructor
  · intro hv
    obtain ⟨h1, h2⟩ := (mem_planeSupport_iff (Finset.univ.map e) v).mp hv
    refine ⟨v.2 ∘ e, ?_⟩
    refine Prod.ext h1.symm ?_
    funext j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      change Function.extend e (v.2 ∘ e) 0 (e i) = v.2 (e i)
      rw [e.injective.extend_apply]
      rfl
    · change Function.extend e (v.2 ∘ e) 0 j = v.2 j
      rw [Function.extend_apply' _ _ _ hj]
      exact (h2 j (by
        intro hmem
        obtain ⟨i, -, hi⟩ := Finset.mem_map.mp hmem
        exact hj ⟨i, hi⟩)).symm
  · rintro ⟨y, rfl⟩
    exact planeTo_mem e y

omit [Finite K] [CharP K 2] in
private theorem planeTo_injective (e : Fin k ↪ Fin n) :
    Function.Injective (planeTo (F := F) (K := K) e) := by
  intro y z hyz
  funext i
  have h := congrArg (fun v : (F × F) × (Fin n → K) => v.2) hyz
  simpa [planeTo, e.injective.extend_apply] using congrFun h (e i)

omit [Finite K] [CharP K 2] in
private noncomputable def planeEquiv (e : Fin k ↪ Fin n) :
    (Fin k → K) ≃ₗ[F] pureSupport (F := F) (K := K) e :=
  LinearEquiv.ofBijective ((planeTo (F := F) (K := K) e).codRestrict
      (pureSupport (F := F) (K := K) e) (planeTo_mem e))
    ⟨fun y z h => planeTo_injective e (Subtype.ext_iff.mp h), fun v => by
      obtain ⟨y, hy⟩ := (planeTo_mem_iff (F := F) (K := K) e v).mp v.2
      exact ⟨y, Subtype.ext hy⟩⟩

private theorem Qn_extend_zero (e : Fin k ↪ Fin n) (y : Fin k → K) :
    Qn E n (Function.extend e y 0) = Qn E k y := by
  rw [Qn_apply, Qn_apply,
    ← Finset.sum_add_sum_compl (Finset.univ.map e)
      (fun j => normQuad E (Function.extend e y 0 j))]
  have hzero : (∑ j ∈ (Finset.univ.map e)ᶜ,
      normQuad E (Function.extend e y 0 j)) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Function.extend_apply' _ _ _ (by simpa using hj), Pi.zero_apply, map_zero]
  rw [hzero, add_zero, Finset.sum_map]
  exact Finset.sum_congr rfl fun i _ => by rw [e.injective.extend_apply]

private theorem planeTo_isometry (e : Fin k ↪ Fin n) (y : Fin k → K) :
    normHypForm E n (planeTo e y) = Qn E k y := by
  change (0 : F) * 0 + Qn E n (Function.extend e y 0) = Qn E k y
  rw [Qn_extend_zero E]
  simp

private noncomputable def planeIsometry (e : Fin k ↪ Fin n) :
    (Qn E k).IsometryEquiv ((normHypForm E n).comp (pureSupport e).subtype) where
  toLinearEquiv := planeEquiv e
  map_app' y := by
    change normHypForm E n (planeTo e y) = Qn E k y
    exact planeTo_isometry E e y

section Regular

private theorem polar_planeSupport_plane (S : Finset (Fin n)) {i : Fin n} (hi : i ∉ S)
    {s : (F × F) × (Fin n → K)} (hs : s ∈ planeSupport S)
    {u : (F × F) × (Fin n → K)}
    (hu : u ∈ coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))) i) :
    polar (normHypForm E n) s u = 0 := by
  classical
  revert s
  induction S using Finset.induction_on with
  | empty =>
      intro s hs
      rw [planeSupport, Finset.sup_empty, Submodule.mem_bot] at hs
      subst hs
      simp
  | insert i0 S hi0 ih =>
      intro s hs
      rw [planeSupport_insert, Submodule.mem_sup] at hs
      obtain ⟨a, ha, b, hb, rfl⟩ := hs
      rw [polar_add_left, ih (fun h => hi (Finset.mem_insert_of_mem h)) ha]
      rw [polar_coordPlane_plane (LinearEquiv.refl F ((F × F) × (Fin n → K)))
        (normHypForm_apply_coord E n)
        (fun h => hi (by rw [← h]; exact Finset.mem_insert_self i0 S)) hb hu, add_zero]

private theorem planeSupport_polarNondegOn (S : Finset (Fin n)) :
    PolarNondegOn (normHypForm E n) (planeSupport S) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [planeSupport, Finset.sup_empty]
      exact CFSG.LieType.SeitzGeneration.ExcHigh.polarNondegOn_bot'
  | insert i S hi ih =>
      rw [planeSupport_insert]
      exact CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup ih
        (coordPlane_polarNondegOn (ψ := LinearEquiv.refl F ((F × F) × (Fin n → K)))
          (hψ := normHypForm_apply_coord E n)
          (hQE := normQuad_polarBilin_nondegenerate E) i)
        (fun s hs u hu => polar_planeSupport_plane E S hi hs hu)

private theorem pureSupport_nondegenerate (e : Fin k ↪ Fin n) :
    (polarBilin ((normHypForm E n).comp (pureSupport e).subtype)).Nondegenerate :=
  CFSG.LieType.SeitzGeneration.OrthBlk.nondegenerate_of_polarNondegOn
    (planeSupport_polarNondegOn E (Finset.univ.map e))

private theorem snd_eq_zero_of_mem_suppPerp (e : Fin k ↪ Fin n)
    {w : (F × F) × (Fin n → K)}
    (hw : w ∈ suppPerp (normHypForm E n) (pureSupport e)) (i : Fin k) :
    w.2 (e i) = 0 := by
  have hmem : ∀ c : K, (((0, 0) : F × F), Pi.single (e i) c) ∈ pureSupport e := by
    intro c
    refine Finset.le_sup (f := coordPlane (LinearEquiv.refl F ((F × F) × (Fin n → K))))
      (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩) ?_
    exact mem_coordPlane.mpr ⟨c, rfl⟩
  have hconv : ∀ c : K, polar (normQuad E) (w.2 (e i)) c = 0 := by
    intro c
    have h := mem_suppPerp.mp hw (((0, 0) : F × F), Pi.single (e i) c) (hmem c)
    rw [polar_hypSum] at h
    have h' : polar (Qn E n) (Pi.single (e i) c) w.2 = 0 := by simpa using h
    rw [polar_comm, polar_Qn_single] at h'
    exact h'
  exact eq_zero_of_polar_eq_zero (normQuad_polarBilin_nondegenerate E) hconv

private theorem hypExt_coordExt_fixes_perp (e : Fin k ↪ Fin n)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) {w : (F × F) × (Fin n → K)}
    (hw : w ∈ suppPerp (normHypForm E n) (pureSupport e)) :
    hypExt (K := F) (W := Fin n → K) (coordExt (F := F) (K := K) e g) w = w := by
  rw [hypExt_apply]
  refine Prod.ext rfl ?_
  exact coordExt_apply_of_eq_zero_on_range e g
    (fun i => snd_eq_zero_of_mem_suppPerp E e hw i)

omit [Finite K] [CharP K 2] in
private theorem hypExt_coordExt_planeTo (e : Fin k ↪ Fin n)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) (y : Fin k → K) :
    hypExt (K := F) (W := Fin n → K) (coordExt (F := F) (K := K) e g)
        (planeTo (F := F) (K := K) e y) =
      planeTo (F := F) (K := K) e (g y) := by
  rw [hypExt_apply]
  refine Prod.ext rfl ?_
  change coordExt (F := F) (K := K) e g (Function.extend e y 0) =
    Function.extend e (g y) 0
  exact coordExt_apply_extendZero e g y

private theorem pureEmb_eq_orthExtend (e : Fin k ↪ Fin n) (g : orthDerived (Qn E k)) :
    ((pureEmb E e g : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) =
      orthExtend (isCompl_suppPerp (polarNondegOn_of_nondegenerate
        (pureSupport_nondegenerate E e)))
        (CFSG.RankThree.PartOne.linConj (planeEquiv e)
          (g : (Fin k → K) ≃ₗ[F] (Fin k → K))) := by
  let hcompl := isCompl_suppPerp (polarNondegOn_of_nondegenerate
    (pureSupport_nondegenerate E e))
  change _ = orthExtend hcompl _
  apply LinearEquiv.ext
  intro v
  obtain ⟨a, ha, w, hw, rfl⟩ := suppExists_add_of_isCompl hcompl v
  rw [map_add, map_add]
  have h1 : ((orthExtend hcompl (CFSG.RankThree.PartOne.linConj (planeEquiv e)
      (g : (Fin k → K) ≃ₗ[F] (Fin k → K)))) a) =
      ((CFSG.RankThree.PartOne.linConj (planeEquiv e)
        (g : (Fin k → K) ≃ₗ[F] (Fin k → K))) ⟨a, ha⟩ :
          (F × F) × (Fin n → K)) := by
    have h := orthExtend_apply hcompl (CFSG.RankThree.PartOne.linConj (planeEquiv e)
      (g : (Fin k → K) ≃ₗ[F] (Fin k → K))) ⟨a, ha⟩
      (⟨0, (suppPerp (normHypForm E n) (pureSupport e)).zero_mem⟩ :
        suppPerp (normHypForm E n) (pureSupport e))
    simpa using h
  have h2 : ((orthExtend hcompl (CFSG.RankThree.PartOne.linConj (planeEquiv e)
      (g : (Fin k → K) ≃ₗ[F] (Fin k → K)))) w) = w := by
    have h := orthExtend_apply hcompl (CFSG.RankThree.PartOne.linConj (planeEquiv e)
      (g : (Fin k → K) ≃ₗ[F] (Fin k → K)))
      (⟨0, (pureSupport e).zero_mem⟩ : pureSupport e) ⟨w, hw⟩
    have h0 : (((CFSG.RankThree.PartOne.linConj (planeEquiv e)
      (g : (Fin k → K) ≃ₗ[F] (Fin k → K)))
      (⟨0, (pureSupport e).zero_mem⟩ : pureSupport e)) :
        (F × F) × (Fin n → K)) = 0 := by simp
    rw [h0, zero_add] at h
    exact h
  rw [h1, h2]
  congr 1
  · obtain ⟨y, hy⟩ := (planeTo_mem_iff (F := F) (K := K) e a).mp ha
    have hs : (⟨a, ha⟩ : pureSupport e) = planeEquiv e y := by
      apply Subtype.ext
      exact hy.symm
    rw [hs, show a = planeTo (F := F) (K := K) e y from hy.symm,
      pureEmb_coe, hypExt_coordExt_planeTo]
    rw [CFSG.RankThree.PartOne.linConj_apply, LinearEquiv.symm_apply_apply]
    rfl
  · exact hypExt_coordExt_fixes_perp E e g hw

theorem range_pureEmb (e : Fin k ↪ Fin n) :
    (pureEmb E e).range = normPureBlock E n (Finset.univ.map e) := by
  have hA := pureSupport_nondegenerate E e
  let hcompl := isCompl_suppPerp (polarNondegOn_of_nondegenerate hA)
  have hext : (orthDerived ((normHypForm E n).comp (pureSupport e).subtype)).map
      (orthExtend hcompl) = supportedDerived (normHypForm E n) (pureSupport e) :=
    map_orthDerived_orthExtend_eq_supportedDerived hcompl
  have hlin : (orthDerived (Qn E k)).map
      (CFSG.RankThree.PartOne.linConj (planeEquiv e)).toMonoidHom =
      orthDerived ((normHypForm E n).comp (pureSupport e).subtype) :=
    CFSG.RankThree.PartOne.map_orthDerived_linConj (planeIsometry E e)
  change (pureEmb E e).range =
    (supportedDerived (normHypForm E n) (pureSupport e)).subgroupOf (normOmega E n)
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := hx
    rw [Subgroup.mem_subgroupOf, pureEmb_eq_orthExtend E e g, ← hext]
    refine Subgroup.mem_map_of_mem _ ?_
    rw [← hlin]
    exact Subgroup.mem_map_of_mem _ g.2
  · intro x hx
    rw [Subgroup.mem_subgroupOf, ← hext] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [← hlin] at hy
    obtain ⟨g, hg, hgx⟩ := Subgroup.mem_map.mp hy
    refine MonoidHom.mem_range.mpr ⟨⟨g, hg⟩, ?_⟩
    apply Subtype.ext
    rw [pureEmb_eq_orthExtend E e ⟨g, hg⟩]
    rw [show CFSG.RankThree.PartOne.linConj (planeEquiv e)
        (⟨g, hg⟩ : orthDerived (Qn E k)) = y from hgx]
    exact hyx

section Functor

theorem pureEmb_comp_qnExtΩ (e : Fin k ↪ Fin n) (e' : Fin n ↪ Fin p) :
    (pureEmb E e').comp (qnExtΩ E e) = pureEmb E (e.trans e') := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  rw [MonoidHom.comp_apply, pureEmb_coe, pureEmb_coe,
    qnExtΩ_apply (F := F) (K := K) E e g, coordExt_trans]

private theorem castEquiv_hypExt (h : n ≤ p)
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
    castEquiv h (hypExt (K := F) (W := Fin n → K) g) =
      hypExt (K := F) (W := Fin p → K)
        (coordExt (F := F) (K := K) (Fin.castLEEmb h) g) := by
  apply LinearEquiv.ext
  intro v
  rw [castEquiv_apply, castLin_apply]
  change ((hypExt (K := F) (W := Fin n → K) g (castRestr h v)).1,
      (fun (j : Fin p) => if hj : (j : ℕ) < n then
        (hypExt (K := F) (W := Fin n → K) g (castRestr h v)).2 ⟨j, hj⟩ else v.2 j)) =
    (v.1, coordExt (F := F) (K := K) (Fin.castLEEmb h) g v.2)
  rw [hypExt_apply]
  refine Prod.ext rfl ?_
  funext j
  change (if hj : (j : ℕ) < n then
      g (castRestr h v).2 ⟨j, hj⟩ else v.2 j) =
    coordExt (F := F) (K := K) (Fin.castLEEmb h) g v.2 j
  by_cases hj : (j : ℕ) < n
  · rw [dif_pos hj]
    have hcast : (Fin.castLEEmb h ⟨j, hj⟩ : Fin p) = j := Fin.ext rfl
    conv_rhs => rw [← hcast]
    rw [coordExt_apply_of_mem]
    rfl
  · rw [dif_neg hj]
    rw [coordExt_apply_of_not_mem _ _ _ (by
      rintro ⟨i, hi⟩
      exact hj (by rw [← hi]; exact i.2))]

theorem normOmegaCast_comp_pureEmb (h : n ≤ p) (e : Fin k ↪ Fin n) :
    (normOmegaCast E h).comp (pureEmb E e) =
      pureEmb E (e.trans (Fin.castLEEmb h)) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  rw [MonoidHom.comp_apply]
  rw [show ((normOmegaCast E h (pureEmb E e g) : normOmega E p) :
      ((F × F) × (Fin p → K)) ≃ₗ[F] ((F × F) × (Fin p → K))) =
      castEquiv h ((pureEmb E e g : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) from
    normOmegaCast_apply E h (pureEmb E e g)]
  rw [pureEmb_coe, pureEmb_coe, castEquiv_hypExt, coordExt_trans]

private theorem normPerm_conj_hypExt (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n))
    (g : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
    (normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) *
        hypExt (K := F) (W := Fin n → K) g *
        ((normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))))⁻¹ =
      hypExt (K := F) (W := Fin n → K)
        (coordExt (F := F) (K := K) σ.toEmbedding g) := by
  have hinv : ((normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
      ((F × F) × (Fin n → K))))⁻¹ =
      (normPerm E hn σ⁻¹ : ((F × F) × (Fin n → K)) ≃ₗ[F]
        ((F × F) × (Fin n → K))) := by
    rw [← Subgroup.coe_inv (H := normOmega E n) (normPerm E hn σ), ← map_inv]
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hinv, normPerm_apply E hn σ⁻¹,
    hypExt_apply, normPerm_apply E hn σ, hypExt_apply]
  refine Prod.ext rfl ?_
  funext j
  change g (fun t => v.2 ((σ⁻¹)⁻¹ t)) (σ⁻¹ j) =
    coordExt (F := F) (K := K) (Equiv.toEmbedding σ) g v.2 j
  have hcoord : (coordExt (F := F) (K := K) (Equiv.toEmbedding σ) g) v.2 j =
      g (v.2 ∘ (Equiv.toEmbedding σ)) (σ⁻¹ j) := by
    conv_lhs => rw [show j = (Equiv.toEmbedding σ) (σ⁻¹ j) from by simp]
    exact coordExt_apply_of_mem (F := F) (K := K) (e := Equiv.toEmbedding σ) (g := g)
      (x := v.2) (i := σ⁻¹ j)
  rw [hcoord]
  rfl

theorem conj_normPerm_comp_pureEmb (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n))
    (e : Fin k ↪ Fin n) :
    (MulAut.conj (normPerm E hn σ)).toMonoidHom.comp (pureEmb E e) =
      pureEmb E (e.trans σ.toEmbedding) := by
  apply MonoidHom.ext
  intro g
  apply Subtype.ext
  have hcoe : ((MulAut.conj (normPerm E hn σ) (pureEmb E e g) : normOmega E n) :
      ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) =
      (normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) *
        (pureEmb E e g : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) *
        ((normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
          ((F × F) × (Fin n → K))))⁻¹ := by
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  change ((MulAut.conj (normPerm E hn σ) (pureEmb E e g) : normOmega E n) :
      ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) =
    ((pureEmb E (e.trans σ.toEmbedding) g : normOmega E n) :
      ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K)))
  rw [hcoe, pureEmb_coe, pureEmb_coe, normPerm_conj_hypExt, coordExt_trans]

theorem map_normPureBlock_normPerm {n : ℕ} (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) :
    (normPureBlock E n S).map (MulAut.conj (normPerm E hn σ)).toMonoidHom =
      normPureBlock E n (S.image σ) := by
  classical
  set e := (S.orderEmbOfFin rfl).toEmbedding with he
  have hS : Finset.univ.map e = S := Finset.map_orderEmbOfFin_univ S rfl
  have hσ : Finset.univ.map (e.trans σ.toEmbedding) = S.image σ := by
    rw [← Finset.map_map, hS, Finset.map_eq_image]
    rfl
  calc
    (normPureBlock E n S).map (MulAut.conj (normPerm E hn σ)).toMonoidHom
        = ((pureEmb E e).range).map (MulAut.conj (normPerm E hn σ)).toMonoidHom := by
            rw [range_pureEmb, hS]
    _ = ((MulAut.conj (normPerm E hn σ)).toMonoidHom.comp (pureEmb E e)).range := by
            rw [MonoidHom.range_comp]
    _ = (pureEmb E (e.trans σ.toEmbedding)).range := by
            rw [conj_normPerm_comp_pureEmb]
    _ = normPureBlock E n (S.image σ) := by
            rw [range_pureEmb, hσ]

theorem map_normPureBlock_normOmegaCast (h : k ≤ n) (S : Finset (Fin k)) :
    (normPureBlock E k S).map (normOmegaCast E h) =
      normPureBlock E n (S.map (Fin.castLEEmb h)) := by
  classical
  set e := (S.orderEmbOfFin rfl).toEmbedding with he
  have hS : Finset.univ.map e = S := Finset.map_orderEmbOfFin_univ S rfl
  have hS' : Finset.univ.map (e.trans (Fin.castLEEmb h)) = S.map (Fin.castLEEmb h) := by
    rw [← Finset.map_map, hS]
  calc
    (normPureBlock E k S).map (normOmegaCast E h)
        = ((pureEmb E e).range).map (normOmegaCast E h) := by
            rw [range_pureEmb, hS]
    _ = ((normOmegaCast E h).comp (pureEmb E e)).range := by
            rw [MonoidHom.range_comp]
    _ = (pureEmb E (e.trans (Fin.castLEEmb h))).range := by
            rw [normOmegaCast_comp_pureEmb]
    _ = normPureBlock E n (S.map (Fin.castLEEmb h)) := by
            rw [range_pureEmb, hS']

section TauConj

omit [Finite K] [CharP K 2] in
private theorem hypExt_mul {n : ℕ} (h₁ h₂ : (Fin n → K) ≃ₗ[F] (Fin n → K)) :
    hypExt (K := F) (W := Fin n → K) h₁ *
        hypExt (K := F) (W := Fin n → K) h₂ =
      hypExt (K := F) (W := Fin n → K) (h₁ * h₂) :=
  (map_mul (hypExtHom (F := F) (K := K) n) h₁ h₂).symm

private theorem hypExt_tauAt_mem_orthogonalGroup (n : ℕ) (j : Fin n) :
    hypExt (K := F) (W := Fin n → K) (tauAt E j) ∈
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E n) :=
  hypExt_mem (Q' := Qn E n) (tauAt_mem_orthogonalGroup E j)

private theorem conj_mem_normOmega_of_mem_orthogonalGroup {n : ℕ}
    {τ : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))}
    (hτ : τ ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E n))
    {x : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))}
    (hx : x ∈ normOmega E n) : τ * x * τ⁻¹ ∈ normOmega E n := by
  have hOmap : (TauCeti.QuadraticMap.orthogonalGroup (normHypForm E n)).map
      (MulAut.conj τ).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E n) := by
    apply le_antisymm
    · rintro y ⟨z, hz, rfl⟩
      exact mul_mem (mul_mem hτ hz) (inv_mem hτ)
    · intro y hy
      refine ⟨τ⁻¹ * y * τ, mul_mem (mul_mem (inv_mem hτ) hy) hτ, ?_⟩
      change (MulAut.conj τ) (τ⁻¹ * y * τ) = y
      rw [MulAut.conj_apply]
      group
  have hcomm : (normOmega E n).map (MulAut.conj τ).toMonoidHom = normOmega E n := by
    rw [show normOmega E n = ⁅TauCeti.QuadraticMap.orthogonalGroup (normHypForm E n),
      TauCeti.QuadraticMap.orthogonalGroup (normHypForm E n)⁆ from rfl,
      Subgroup.map_commutator, hOmap]
  rw [← hcomm]
  exact Subgroup.mem_map_of_mem _ hx

noncomputable def tauConj (n : ℕ) (j : Fin n) : MulAut (normOmega E n) where
  toFun x := ⟨hypExt (K := F) (W := Fin n → K) (tauAt E j) * (x : _ ≃ₗ[F] _) *
      (hypExt (K := F) (W := Fin n → K) (tauAt E j))⁻¹,
    conj_mem_normOmega_of_mem_orthogonalGroup E
      (hypExt_tauAt_mem_orthogonalGroup E n j) x.2⟩
  invFun x := ⟨(hypExt (K := F) (W := Fin n → K) (tauAt E j))⁻¹ * (x : _ ≃ₗ[F] _) *
      hypExt (K := F) (W := Fin n → K) (tauAt E j),
    conj_mem_normOmega_of_mem_orthogonalGroup E
      (inv_mem (hypExt_tauAt_mem_orthogonalGroup E n j)) x.2⟩
  left_inv x := by
    apply Subtype.ext
    dsimp only
    group
  right_inv x := by
    apply Subtype.ext
    dsimp only
    group
  map_mul' x y := by
    apply Subtype.ext
    dsimp only
    simp only [Subgroup.coe_mul]
    group

private theorem tauConj_coe (n : ℕ) (j : Fin n) (x : normOmega E n) :
    ((tauConj E n j x : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) =
      hypExt (K := F) (W := Fin n → K) (tauAt E j) * (x : _ ≃ₗ[F] _) *
        (hypExt (K := F) (W := Fin n → K) (tauAt E j))⁻¹ := rfl

private theorem map_coordAnchor_tauAt (n : ℕ) (j : Fin n) :
    (coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K)))).map
        (hypExt (K := F) (W := Fin n → K) (tauAt E j)).toLinearMap =
      coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K))) := by
  refine le_antisymm ?_ ?_
  · rintro - ⟨v, hv, rfl⟩
    obtain ⟨r, rfl⟩ := mem_coordAnchor.mp hv
    refine mem_coordAnchor.mpr ⟨r, ?_⟩
    simp [hypExt_apply]
  · intro v hv
    obtain ⟨r, rfl⟩ := mem_coordAnchor.mp hv
    refine ⟨(r, 0), mem_coordAnchor.mpr ⟨r, rfl⟩, ?_⟩
    simp [hypExt_apply]

private theorem map_planeSupport_tauAt (n : ℕ) (j : Fin n) (S : Finset (Fin n)) :
    (planeSupport S).map
        (hypExt (K := F) (W := Fin n → K) (tauAt E j)).toLinearMap = planeSupport S := by
  let φ : ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K)) :=
    hypExt (K := F) (W := Fin n → K) (tauAt E j)
  have hφφ : φ * φ = 1 := by
    change hypExt (K := F) (W := Fin n → K) (tauAt E j) *
        hypExt (K := F) (W := Fin n → K) (tauAt E j) = 1
    rw [hypExt_mul, tauAt_mul_self]
    exact map_one (hypExtHom (F := F) (K := K) n)
  have hfst : ∀ v : (F × F) × (Fin n → K), (φ v).1 = v.1 := by
    intro v
    change (hypExt (K := F) (W := Fin n → K) (tauAt E j) v).1 = v.1
    rw [hypExt_apply]
  have hsnd : ∀ (v : (F × F) × (Fin n → K)) (t : Fin n),
      (φ v).2 t = if t = j then unitaryInvolution K 2 f (v.2 t) else v.2 t := by
    intro v t
    change (hypExt (K := F) (W := Fin n → K) (tauAt E j) v).2 t = _
    rw [hypExt_apply]
    change (tauAt E j v.2) t = _
    rw [tauAt_apply]
  have h1 : (planeSupport S).map φ.toLinearMap ≤ planeSupport S := by
    rintro - ⟨v, hv, rfl⟩
    obtain ⟨hv1, hv2⟩ := (mem_planeSupport_iff S v).mp hv
    refine (mem_planeSupport_iff S (φ v)).mpr ⟨by rw [hfst, hv1], fun t ht => ?_⟩
    rw [hsnd]
    by_cases htj : t = j
    · subst t
      rw [if_pos rfl, hv2 j ht, map_zero]
    · rw [if_neg htj, hv2 t ht]
  have h2 : planeSupport S ≤ (planeSupport S).map φ.toLinearMap := by
    intro v hv
    have hw : φ v ∈ planeSupport S :=
      h1 (Submodule.mem_map_of_mem (f := φ.toLinearMap) hv)
    refine Submodule.mem_map.mpr ⟨φ v, hw, ?_⟩
    change φ (φ v) = v
    rw [← LinearEquiv.mul_apply, hφφ]
    rfl
  exact le_antisymm h1 h2

private theorem map_coordSupport_tauAt (n : ℕ) (j : Fin n) (S : Finset (Fin n)) :
    (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S).map
        (hypExt (K := F) (W := Fin n → K) (tauAt E j)).toLinearMap =
      coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S := by
  unfold coordSupport
  change (coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K))) ⊔ planeSupport S).map
      (hypExt (K := F) (W := Fin n → K) (tauAt E j)).toLinearMap =
    coordAnchor (LinearEquiv.refl F ((F × F) × (Fin n → K))) ⊔ planeSupport S
  rw [Submodule.map_sup, map_coordAnchor_tauAt E n j, map_planeSupport_tauAt E n j]

private theorem map_subgroupOf_tauConj (n : ℕ) (j : Fin n)
    (H : Subgroup (((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))))
    (hH : H ≤ normOmega E n)
    (hHmap : H.map (MulAut.conj (hypExt (K := F) (W := Fin n → K) (tauAt E j))).toMonoidHom =
      H) :
    (H.subgroupOf (normOmega E n)).map (tauConj E n j).toMonoidHom =
      H.subgroupOf (normOmega E n) := by
  apply le_antisymm
  · rintro - ⟨y, hy, rfl⟩
    have hyH : (y : _ ≃ₗ[F] _) ∈ H := Subgroup.mem_subgroupOf.mp hy
    have hmem := Subgroup.mem_map_of_mem
      (MulAut.conj (hypExt (K := F) (W := Fin n → K) (tauAt E j))).toMonoidHom hyH
    rw [hHmap] at hmem
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hval : (((MulEquiv.toMonoidHom (tauConj E n j)) y : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) =
        (MulAut.conj (hypExt (K := F) (W := Fin n → K) (tauAt E j))).toMonoidHom
          (y : _ ≃ₗ[F] _) := by
      change ((tauConj E n j y : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) = _
      rw [tauConj_coe]
      change hypExt (K := F) (W := Fin n → K) (tauAt E j) * (y : _ ≃ₗ[F] _) *
          (hypExt (K := F) (W := Fin n → K) (tauAt E j))⁻¹ =
        (MulAut.conj (hypExt (K := F) (W := Fin n → K) (tauAt E j))) (y : _ ≃ₗ[F] _)
      rw [MulAut.conj_apply]
    rw [hval]
    exact hmem
  · intro x hx
    have hxH : (x : _ ≃ₗ[F] _) ∈ H := Subgroup.mem_subgroupOf.mp hx
    have hxmap : (x : _ ≃ₗ[F] _) ∈ H.map
        (MulAut.conj (hypExt (K := F) (W := Fin n → K) (tauAt E j))).toMonoidHom := by
      rw [hHmap]
      exact hxH
    obtain ⟨y, hyH, hyx⟩ := Subgroup.mem_map.mp hxmap
    refine ⟨⟨y, hH hyH⟩, Subgroup.mem_subgroupOf.mpr hyH, ?_⟩
    apply Subtype.ext
    change ((tauConj E n j ⟨y, hH hyH⟩ : normOmega E n) :
      ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) = (x : _ ≃ₗ[F] _)
    rw [tauConj_coe]
    change hypExt (K := F) (W := Fin n → K) (tauAt E j) * (y : _ ≃ₗ[F] _) *
        (hypExt (K := F) (W := Fin n → K) (tauAt E j))⁻¹ = (x : _ ≃ₗ[F] _)
    simp only [MulEquiv.coe_toMonoidHom] at hyx
    rw [MulAut.conj_apply] at hyx
    exact hyx

theorem map_normPureBlock_tauConj {n : ℕ} (j : Fin n) (S : Finset (Fin n)) :
    (normPureBlock E n S).map (tauConj E n j).toMonoidHom = normPureBlock E n S := by
  let H := supportedDerived (normHypForm E n) (planeSupport S)
  have hH : H ≤ normOmega E n :=
    supportedDerived_le_orthDerived_of_regular
      (CFSG.LieType.SeitzGeneration.OrthBlk.nondegenerate_of_polarNondegOn
        (planeSupport_polarNondegOn E S))
  have hHmap : H.map
      (MulAut.conj (hypExt (K := F) (W := Fin n → K) (tauAt E j))).toMonoidHom = H :=
    map_supportedDerived_conj_of_map_eq (hypExt (K := F) (W := Fin n → K) (tauAt E j))
      (hypExt_tauAt_mem_orthogonalGroup E n j) (map_planeSupport_tauAt E n j S)
  change (H.subgroupOf (normOmega E n)).map (tauConj E n j).toMonoidHom =
    H.subgroupOf (normOmega E n)
  exact map_subgroupOf_tauConj E n j H hH hHmap

theorem map_normBlock_tauConj {n : ℕ} (j : Fin n) (S : Finset (Fin n)) :
    (normBlock E n S).map (tauConj E n j).toMonoidHom = normBlock E n S := by
  let H := supportedDerived (normHypForm E n)
    (coordSupport (LinearEquiv.refl F ((F × F) × (Fin n → K))) S)
  have hH : H ≤ normOmega E n :=
    supportedDerived_le_orthDerived_of_regular
      (CFSG.LieType.SeitzGeneration.OrthBlk.nondegenerate_of_polarNondegOn
        (coordSupport_polarNondegOn (ψ := LinearEquiv.refl F ((F × F) × (Fin n → K)))
          (hψ := normHypForm_apply_coord E n)
          (hQ := normHypForm_polarBilin_nondegenerate E n)
          (hQE := normQuad_polarBilin_nondegenerate E) S))
  have hHmap : H.map
      (MulAut.conj (hypExt (K := F) (W := Fin n → K) (tauAt E j))).toMonoidHom = H :=
    map_supportedDerived_conj_of_map_eq (hypExt (K := F) (W := Fin n → K) (tauAt E j))
      (hypExt_tauAt_mem_orthogonalGroup E n j) (map_coordSupport_tauAt E n j S)
  change (H.subgroupOf (normOmega E n)).map (tauConj E n j).toMonoidHom =
    H.subgroupOf (normOmega E n)
  exact map_subgroupOf_tauConj E n j H hH hHmap

private theorem tauAt_mul_coordExt_of_not_mem (e : Fin k ↪ Fin n)
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) {j : Fin n}
    (hj : ¬ ∃ i, e i = j) :
    tauAt E j * coordExt (F := F) (K := K) e g =
      coordExt (F := F) (K := K) e g * tauAt E j := by
  apply LinearEquiv.ext
  intro x
  funext t
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  by_cases ht : t = j
  · subst t
    rw [tauAt_apply, if_pos rfl, coordExt_apply_of_not_mem _ _ _ hj,
      coordExt_apply_of_not_mem _ _ _ hj, tauAt_apply, if_pos rfl]
  · rw [tauAt_apply, if_neg ht]
    by_cases hrange : ∃ i, e i = t
    · obtain ⟨i, rfl⟩ := hrange
      rw [coordExt_apply_of_mem (i := i), coordExt_apply_of_mem (i := i)]
      have hfun : (x ∘ ⇑e) = ((tauAt E j) x) ∘ ⇑e := by
        funext i'
        rw [Function.comp_apply, Function.comp_apply, tauAt_apply,
          if_neg (fun h => hj ⟨i', h⟩)]
      rw [hfun]
    · rw [coordExt_apply_of_not_mem _ _ _ hrange,
        coordExt_apply_of_not_mem _ _ _ hrange]
      rw [tauAt_apply, if_neg ht]

omit [Finite K] [CharP K 2] in
private theorem hypExt_mul_comm {n : ℕ} {h₁ h₂ : (Fin n → K) ≃ₗ[F] (Fin n → K)}
    (h : h₁ * h₂ = h₂ * h₁) :
    hypExt (K := F) (W := Fin n → K) h₁ * hypExt (K := F) (W := Fin n → K) h₂ =
      hypExt (K := F) (W := Fin n → K) h₂ * hypExt (K := F) (W := Fin n → K) h₁ := by
  rw [hypExt_mul, hypExt_mul, h]

theorem tauConj_pureEmb_of_not_mem (e : Fin k ↪ Fin n) {j : Fin n}
    (hj : j ∉ Set.range e) (g : orthDerived (Qn E k)) :
    tauConj E n j (pureEmb E e g) = pureEmb E e g := by
  have hnr : ¬ ∃ i, e i = j := by
    rintro ⟨i, hi⟩
    exact hj (by rw [← hi]; exact Set.mem_range_self i)
  have hcomm := tauAt_mul_coordExt_of_not_mem E e
    (g : (Fin k → K) ≃ₗ[F] (Fin k → K)) hnr
  have hhyp := hypExt_mul_comm hcomm
  apply Subtype.ext
  rw [tauConj_coe, pureEmb_coe]
  change hypExt (K := F) (W := Fin n → K) (tauAt E j) *
      hypExt (K := F) (W := Fin n → K)
        (coordExt (F := F) (K := K) e (g : _ ≃ₗ[F] _)) *
      (hypExt (K := F) (W := Fin n → K) (tauAt E j))⁻¹ =
    hypExt (K := F) (W := Fin n → K)
      (coordExt (F := F) (K := K) e (g : _ ≃ₗ[F] _))
  rw [hhyp]
  group

theorem conj_normPerm_tauConj (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n)) (j : Fin n)
    (x : normOmega E n) :
    MulAut.conj (normPerm E hn σ) (tauConj E n j x) =
      tauConj E n (σ j) (MulAut.conj (normPerm E hn σ) x) := by
  have hamb : (normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
      ((F × F) × (Fin n → K))) *
        hypExt (K := F) (W := Fin n → K) (tauAt E j) *
        (normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
          ((F × F) × (Fin n → K)))⁻¹ =
      hypExt (K := F) (W := Fin n → K) (tauAt E (σ j)) := by
    rw [normPerm_conj_hypExt E hn σ (tauAt E j), coordExt_tauAt]
    rfl
  apply Subtype.ext
  calc ((MulAut.conj (normPerm E hn σ) (tauConj E n j x) : normOmega E n) :
      ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K)))
      = (normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
            ((F × F) × (Fin n → K))) *
          (hypExt (K := F) (W := Fin n → K) (tauAt E j) * (x : _ ≃ₗ[F] _) *
            (hypExt (K := F) (W := Fin n → K) (tauAt E j))⁻¹) *
          (normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
            ((F × F) × (Fin n → K)))⁻¹ := by
        simp only [MulAut.conj_apply, tauConj_coe, Subgroup.coe_mul, Subgroup.coe_inv]
    _ = ((normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
            ((F × F) × (Fin n → K))) *
          hypExt (K := F) (W := Fin n → K) (tauAt E j) *
          (normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
            ((F × F) × (Fin n → K)))⁻¹) *
        ((normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
            ((F × F) × (Fin n → K))) * (x : _ ≃ₗ[F] _) *
          (normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
            ((F × F) × (Fin n → K)))⁻¹) *
        ((normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
            ((F × F) × (Fin n → K))) *
          hypExt (K := F) (W := Fin n → K) (tauAt E j) *
          (normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
            ((F × F) × (Fin n → K)))⁻¹)⁻¹ := by
        group
    _ = hypExt (K := F) (W := Fin n → K) (tauAt E (σ j)) *
        ((normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
            ((F × F) × (Fin n → K))) * (x : _ ≃ₗ[F] _) *
          (normPerm E hn σ : ((F × F) × (Fin n → K)) ≃ₗ[F]
            ((F × F) × (Fin n → K)))⁻¹) *
        (hypExt (K := F) (W := Fin n → K) (tauAt E (σ j)))⁻¹ := by
        rw [hamb]
    _ = ((tauConj E n (σ j) (MulAut.conj (normPerm E hn σ) x) : normOmega E n) :
        ((F × F) × (Fin n → K)) ≃ₗ[F] ((F × F) × (Fin n → K))) := by
        simp only [tauConj_coe, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]

theorem card_normPureBlock_pair (hq : 4 ≤ Nat.card F) {n : ℕ} {i j : Fin n}
    (hij : i ≠ j) :
    Nat.card (normPureBlock E n {i, j}) =
      Nat.card F ^ 2 * (Nat.card F ^ 2 - 1) ^ 2 := by
  have : Finite F := Finite.of_injective (algebraMap F K) (algebraMap F K).injective
  have : CharP F 2 := (algebraMap F K).charP (algebraMap F K).injective 2
  classical
  have hcard : ({i, j} : Finset (Fin n)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hij)]
    simp
  let e : Fin 2 ↪ Fin n := (({i, j} : Finset (Fin n)).orderEmbOfFin hcard).toEmbedding
  have hmap : Finset.univ.map e = ({i, j} : Finset (Fin n)) :=
    Finset.map_orderEmbOfFin_univ _ hcard
  have hcard_range : Nat.card ↥(normPureBlock E n {i, j}) =
      Nat.card (orthDerived (Qn E 2)) := by
    rw [← hmap, ← range_pureEmb E e]
    exact (Nat.card_congr
      (MonoidHom.ofInjective (pureEmb_injective E e)).toEquiv).symm
  have hcard_iso : Nat.card (orthDerived (Qn E 2)) =
      Nat.card (orthDerived (CFSG.LieType.Universal.Spin.quadPlus 2 F)) := by
    obtain ⟨iso⟩ := CFSG.ClassicalInvolution.PhanDn.nonempty_isometryEquiv_quadPlus E
      (n := 2) (by norm_num)
    exact Nat.card_congr
      (CFSG.ClassicalGroups.Orthogonal.commutatorOrthogonalGroupCongr iso).toEquiv
  have hcard_stated : Nat.card (orthDerived (CFSG.LieType.Universal.Spin.quadPlus 2 F)) =
      Nat.card (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus 2 F)) :=
    (Nat.card_congr (CFSG.RankThree.GF2n.Stroth80.statedOmegaMulEquivDerived
      (CFSG.LieType.Universal.Spin.coe_quadPlus 2 F)).toEquiv).symm
  rw [hcard_range, hcard_iso, hcard_stated]
  have hz := CFSG.RankThree.GF2n.Smith81.card_statedOmega_plus_eq_of_two_le
    (K := F) hq (m := 2) (by norm_num)
  have hq2 : (1 : ℤ) ≤ (Nat.card F : ℤ) ^ 2 := by
    have h1 : (1 : ℤ) ≤ (Nat.card F : ℤ) := by exact_mod_cast (by omega : 1 ≤ Nat.card F)
    nlinarith [sq_nonneg ((Nat.card F : ℤ))]
  have hsub : ((Nat.card F : ℤ) ^ 2 - 1) = ((Nat.card F ^ 2 - 1 : ℕ) : ℤ) := by
    have hq1 : 1 ≤ Nat.card F ^ 2 := by
      have h := Nat.one_le_pow' 2 (Nat.card F - 1)
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ Nat.card F)] at h
    rw [Nat.cast_sub (by exact_mod_cast hq1)]
    push_cast
    ring
  apply Nat.cast_injective (R := ℤ)
  rw [hz]
  simp only [Finset.Icc_self, Finset.prod_singleton]
  norm_num only [Nat.reduceSub, Nat.mul_one, Nat.one_mul] at *
  rw [hsub]
  push_cast
  ring

end TauConj

end Functor

end Regular

end Support

end Pure

end CoordExt

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
