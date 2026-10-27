module

public import CFSG.Timmesfeld.Orders.ClassicalHypSum
public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.GH74.Generic.S1.SymBlocksUniCore
import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.KLinearOmega
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.ClassicalGroups.Orthogonal.UnitaryOmega

open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Timmesfeld.ClassicalOrders

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2] {f : ℕ}

section Model

variable (E : QuadExt F K (unitaryInvolution K 2 f))

noncomputable abbrev normHypForm (m : ℕ) : QuadraticForm F ((F × F) × (Fin m → K)) :=
  hypSum (Qn E m)

noncomputable abbrev normOmega (m : ℕ) :
    Subgroup (((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) :=
  CFSG.RankThree.Classical2.orthDerived (normHypForm E m)

theorem normHypForm_polarBilin_nondegenerate (m : ℕ) :
    (QuadraticMap.polarBilin (normHypForm E m)).Nondegenerate :=
  nondegenerate_polarBilin_hypSum (Qn_polarBilin_nondegenerate E m)

end Model

section Cast

variable {k m : ℕ}

@[expose] def castRestr (h : k ≤ m) (v : (F × F) × (Fin m → K)) : (F × F) × (Fin k → K) :=
  (v.1, fun i => v.2 (Fin.castLE h i))

@[expose] noncomputable def castLin (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K))) :
    ((F × F) × (Fin m → K)) →ₗ[F] ((F × F) × (Fin m → K)) where
  toFun v := ((g (castRestr h v)).1,
    fun j => if hj : (j : ℕ) < k then (g (castRestr h v)).2 ⟨j, hj⟩ else v.2 j)
  map_add' v w := by
    have hsum : castRestr h (v + w) = castRestr h v + castRestr h w := rfl
    refine Prod.ext (Prod.ext ?_ ?_) (funext fun j => ?_)
    · simp [hsum, map_add]
    · simp [hsum, map_add]
    · by_cases hj : (j : ℕ) < k <;> simp [hsum, hj, map_add]
  map_smul' c v := by
    have hsmul : castRestr h (c • v) = c • castRestr h v := rfl
    refine Prod.ext (Prod.ext ?_ ?_) (funext fun j => ?_)
    · simp [hsmul, map_smul]
    · simp [hsmul, map_smul]
    · by_cases hj : (j : ℕ) < k <;> simp [hsmul, hj, map_smul]

theorem castLin_apply (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K)))
    (v : (F × F) × (Fin m → K)) :
    castLin h g v = ((g (castRestr h v)).1,
      fun j : Fin m =>
        if hj : (j : ℕ) < k then (g (castRestr h v)).2 ⟨(j : ℕ), hj⟩ else v.2 j) :=
  rfl

theorem castLin_fst (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K)))
    (v : (F × F) × (Fin m → K)) :
    (castLin h g v).1 = (g (castRestr h v)).1 := by
  rw [castLin_apply]

theorem castLin_snd_of_lt (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K)))
    (v : (F × F) × (Fin m → K)) {j : Fin m} (hj : (j : ℕ) < k) :
    (castLin h g v).2 j = (g (castRestr h v)).2 ⟨j, hj⟩ := by
  rw [castLin_apply]
  simp [hj]

theorem castLin_snd_of_not_lt (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K)))
    (v : (F × F) × (Fin m → K)) {j : Fin m} (hj : ¬ (j : ℕ) < k) :
    (castLin h g v).2 j = v.2 j := by
  rw [castLin_apply]
  simp [hj]

theorem castRestr_castLin (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K))) (v : (F × F) × (Fin m → K)) :
    castRestr h (castLin h g v) = g (castRestr h v) := by
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun i => ?_)
  · change (castLin h g v).1.1 = (g (castRestr h v)).1.1
    exact congrArg Prod.fst (castLin_fst h g v)
  · change (castLin h g v).1.2 = (g (castRestr h v)).1.2
    exact congrArg Prod.snd (castLin_fst h g v)
  · change (castLin h g v).2 (Fin.castLE h i) = (g (castRestr h v)).2 i
    rw [castLin_snd_of_lt h g v (by rw [Fin.val_castLE]; exact i.2)]
    congr 1

theorem castLin_comp (h : k ≤ m)
    (g g' : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K))) :
    castLin h (g ∘ₗ g') = castLin h g ∘ₗ castLin h g' := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply]
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun j => ?_)
  · rw [castLin_fst (g := g ∘ₗ g') (v := v),
      castLin_fst (g := g) (v := castLin h g' v), castRestr_castLin]
    rfl
  · rw [castLin_fst (g := g ∘ₗ g') (v := v),
      castLin_fst (g := g) (v := castLin h g' v), castRestr_castLin]
    rfl
  · by_cases hj : (j : ℕ) < k
    · rw [castLin_snd_of_lt (h := h) (g := g ∘ₗ g') (v := v) hj,
        castLin_snd_of_lt (h := h) (g := g) (v := castLin h g' v) hj, castRestr_castLin]
      rfl
    · rw [castLin_snd_of_not_lt (h := h) (g := g ∘ₗ g') (v := v) hj,
        castLin_snd_of_not_lt (h := h) (g := g) (v := castLin h g' v) hj,
        castLin_snd_of_not_lt (h := h) (g := g') (v := v) hj]

theorem castLin_id (h : k ≤ m) :
    castLin h (LinearMap.id : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K))) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun j => ?_)
  · rw [castLin_fst]
    rfl
  · rw [castLin_fst]
    rfl
  · by_cases hj : (j : ℕ) < k
    · rw [castLin_snd_of_lt (h := h) (g := LinearMap.id) (v := v) hj]
      simp only [LinearMap.id_apply, castRestr]
      congr 1
    · rw [castLin_snd_of_not_lt (h := h) (g := LinearMap.id) (v := v) hj]
      rfl

theorem castRestr_refl (v : (F × F) × (Fin m → K)) :
    castRestr (le_refl m) v = v := by
  refine Prod.ext (Prod.ext rfl rfl) (funext fun i => ?_)
  change v.2 (Fin.castLE (le_refl m) i) = v.2 i
  rw [Fin.castLE_rfl]
  rfl

theorem castRestr_surjective (h : k ≤ m) :
    Function.Surjective (castRestr (F := F) (K := K) h) := by
  intro v
  refine ⟨(v.1, fun j : Fin m =>
    if hj : (j : ℕ) < k then v.2 ⟨(j : ℕ), hj⟩ else 0), ?_⟩
  refine Prod.ext (Prod.ext rfl rfl) (funext fun i => ?_)
  change (if hi : ((Fin.castLE h i : Fin m) : ℕ) < k then
    v.2 ⟨((Fin.castLE h i : Fin m) : ℕ), hi⟩ else 0) = v.2 i
  rw [dif_pos (by rw [Fin.val_castLE]; exact i.2)]
  exact congrArg v.2 (Fin.ext (by rw [Fin.val_castLE]))

theorem castRestr_castRestr {l : ℕ} (h₁ : k ≤ l) (h₂ : l ≤ m)
    (v : (F × F) × (Fin m → K)) :
    castRestr h₁ (castRestr h₂ v) = castRestr (h₁.trans h₂) v := by
  refine Prod.ext (Prod.ext rfl rfl) (funext fun i => ?_)
  change v.2 (Fin.castLE h₂ (Fin.castLE h₁ i)) = v.2 (Fin.castLE (h₁.trans h₂) i)
  exact congrArg v.2 (Fin.ext rfl)

theorem castLin_refl (g : ((F × F) × (Fin m → K)) →ₗ[F]
    ((F × F) × (Fin m → K))) :
    castLin (le_refl m) g = g := by
  apply LinearMap.ext
  intro v
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun j => ?_)
  · rw [castLin_fst, castRestr_refl]
  · rw [castLin_fst, castRestr_refl]
  · rw [castLin_snd_of_lt (h := le_refl m) (g := g) (v := v) j.2, castRestr_refl]

theorem castLin_castLin {l : ℕ} (h₁ : k ≤ l) (h₂ : l ≤ m)
    (g : ((F × F) × (Fin k → K)) →ₗ[F] ((F × F) × (Fin k → K))) :
    castLin h₂ (castLin h₁ g) = castLin (h₁.trans h₂) g := by
  apply LinearMap.ext
  intro v
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun j => ?_)
  · rw [castLin_fst (h := h₂) (g := castLin h₁ g) (v := v),
      castLin_fst (h := h₁) (g := g) (v := castRestr h₂ v),
      castLin_fst (h := h₁.trans h₂) (g := g) (v := v), castRestr_castRestr]
  · rw [castLin_fst (h := h₂) (g := castLin h₁ g) (v := v),
      castLin_fst (h := h₁) (g := g) (v := castRestr h₂ v),
      castLin_fst (h := h₁.trans h₂) (g := g) (v := v), castRestr_castRestr]
  · by_cases hj₂ : (j : ℕ) < l
    · by_cases hj₁ : (j : ℕ) < k
      · rw [castLin_snd_of_lt (h := h₂) (g := castLin h₁ g) (v := v) hj₂,
          castLin_snd_of_lt (h := h₁) (g := g) (v := castRestr h₂ v) hj₁,
          castLin_snd_of_lt (h := h₁.trans h₂) (g := g) (v := v) hj₁,
          castRestr_castRestr]
      · rw [castLin_snd_of_lt (h := h₂) (g := castLin h₁ g) (v := v) hj₂,
          castLin_snd_of_not_lt (h := h₁) (g := g) (v := castRestr h₂ v) hj₁,
          castLin_snd_of_not_lt (h := h₁.trans h₂) (g := g) (v := v)
            (by omega)]
        exact congrArg v.2 (Fin.ext rfl)
    · rw [castLin_snd_of_not_lt (h := h₂) (g := castLin h₁ g) (v := v) hj₂,
        castLin_snd_of_not_lt (h := h₁.trans h₂) (g := g) (v := v) (by omega)]

@[expose] noncomputable def castEquiv (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K))) :
    ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)) :=
  LinearEquiv.ofLinearMap (castLin h g.toLinearMap) (castLin h g.symm.toLinearMap)
    (by
      rw [← castLin_comp]
      have h2 : g.toLinearMap ∘ₗ g.symm.toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        intro v
        exact LinearEquiv.apply_symm_apply g v
      rw [h2, castLin_id])
    (by
      rw [← castLin_comp]
      have h1 : g.symm.toLinearMap ∘ₗ g.toLinearMap = LinearMap.id := by
        apply LinearMap.ext
        intro v
        exact LinearEquiv.symm_apply_apply g v
      rw [h1, castLin_id])

theorem castEquiv_apply (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K))) (v : (F × F) × (Fin m → K)) :
    castEquiv h g v = castLin h g.toLinearMap v := by
  rw [castEquiv, LinearEquiv.coe_ofLinearMap]

theorem castEquiv_toLinearMap (h : k ≤ m)
    (g : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K))) :
    (castEquiv h g).toLinearMap = castLin h g.toLinearMap :=
  LinearMap.ext fun v => castEquiv_apply h g v

@[expose] noncomputable def castHom (h : k ≤ m) :
    (((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K))) →*
      (((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) where
  toFun := castEquiv h
  map_one' := by
    apply LinearEquiv.ext
    intro v
    rw [castEquiv_apply]
    have hone : ((1 : ((F × F) × (Fin k → K)) ≃ₗ[F]
        ((F × F) × (Fin k → K))).toLinearMap) = LinearMap.id := rfl
    rw [hone, castLin_id]
    rfl
  map_mul' g g' := by
    apply LinearEquiv.ext
    intro v
    rw [castEquiv_apply]
    have hmul : ((g * g').toLinearMap) = g.toLinearMap ∘ₗ g'.toLinearMap := rfl
    rw [hmul, castLin_comp]
    rfl

variable (E : QuadExt F K (unitaryInvolution K 2 f))

private theorem sum_normQuad_castLE (h : k ≤ m) (x : Fin m → K) :
    (∑ i : Fin k, normQuad E (x (Fin.castLE h i))) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), normQuad E (x j) := by
  refine Finset.sum_bij (fun i _ => Fin.castLE h i) ?_ ?_ ?_ ?_
  · intro i _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [Fin.val_castLE]; exact i.2⟩
  · intro i₁ _ i₂ _ heq
    exact Fin.castLE_injective h heq
  · intro j hj
    refine ⟨⟨(j : ℕ), (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro i _
    rfl

theorem normHypForm_eq_castRestr_add (h : k ≤ m) (v : (F × F) × (Fin m → K)) :
    normHypForm E m v = normHypForm E k (castRestr h v) +
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ (j : ℕ) < k), normQuad E (v.2 j) := by
  simp only [normHypForm, hypSum_apply, Qn_apply]
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun j : Fin m => (j : ℕ) < k) (f := fun j => normQuad E (v.2 j))]
  have hf : (∑ i : Fin k, normQuad E ((castRestr h v).2 i)) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), normQuad E (v.2 j) := by
    change (∑ i : Fin k, normQuad E (v.2 (Fin.castLE h i))) = _
    rw [sum_normQuad_castLE (E := E) h v.2]
  rw [hf]
  simp only [castRestr]
  abel

theorem castEquiv_mem_orthogonalGroup (h : k ≤ m)
    {g : ((F × F) × (Fin k → K)) ≃ₗ[F] ((F × F) × (Fin k → K))}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E k)) :
    castEquiv h g ∈ TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
  have hg' := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg) (castRestr h v)
  rw [castEquiv_apply, normHypForm_eq_castRestr_add (E := E) h v,
    normHypForm_eq_castRestr_add (E := E) h (castLin h g.toLinearMap v)]
  rw [castRestr_castLin]
  have htail : (∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ (j : ℕ) < k),
      normQuad E ((castLin h g.toLinearMap v).2 j)) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => ¬ (j : ℕ) < k),
        normQuad E (v.2 j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [castLin_snd_of_not_lt (h := h) (g := g.toLinearMap) (v := v)
      (Finset.mem_filter.mp hj).2]
  rw [htail]
  have hg'' : (normHypForm E k) (g.toLinearMap (castRestr h v)) =
      (normHypForm E k) (castRestr h v) := hg'
  rw [hg'']

@[expose] noncomputable def normOmegaCast (h : k ≤ m) : normOmega E k →* normOmega E m :=
  ((castHom h).comp (normOmega E k).subtype).codRestrict (normOmega E m) (by
    intro a
    have hmap : (TauCeti.QuadraticMap.orthogonalGroup (normHypForm E k)).map (castHom h) ≤
        TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m) :=
      Subgroup.map_le_iff_le_comap.mpr fun g hg => castEquiv_mem_orthogonalGroup E h hg
    have hcomm : (normOmega E k).map (castHom h) ≤ normOmega E m := by
      calc
        (normOmega E k).map (castHom h)
            = ⁅(TauCeti.QuadraticMap.orthogonalGroup (normHypForm E k)).map (castHom h),
                (TauCeti.QuadraticMap.orthogonalGroup (normHypForm E k)).map (castHom h)⁆ := by
              rw [show normOmega E k = ⁅TauCeti.QuadraticMap.orthogonalGroup (normHypForm E k),
                TauCeti.QuadraticMap.orthogonalGroup (normHypForm E k)⁆ from rfl,
                Subgroup.map_commutator]
        _ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m),
              TauCeti.QuadraticMap.orthogonalGroup (normHypForm E m)⁆ :=
              Subgroup.commutator_mono hmap hmap
    exact hcomm (Subgroup.mem_map_of_mem (castHom h) a.2))

theorem normOmegaCast_apply (h : k ≤ m) (a : normOmega E k) :
    ((normOmegaCast E h a : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) = castEquiv h a :=
  rfl

theorem normOmegaCast_injective (h : k ≤ m) : Function.Injective (normOmegaCast E h) := by
  intro a b hab
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  obtain ⟨w, hw⟩ := castRestr_surjective (F := F) (K := K) h v
  have hab' : ((normOmegaCast E h a : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) w =
      ((normOmegaCast E h b : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) w :=
    congrArg (fun e : normOmega E m =>
      (e : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) w) hab
  rw [normOmegaCast_apply, normOmegaCast_apply] at hab'
  rw [castEquiv_apply, castEquiv_apply] at hab'
  have h := congrArg (castRestr (F := F) (K := K) h) hab'
  rw [castRestr_castLin, castRestr_castLin, hw] at h
  exact h

theorem normOmegaCast_refl (m : ℕ) :
    normOmegaCast E (le_refl m) = MonoidHom.id (normOmega E m) := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  change (castEquiv (le_refl m) (a : ((F × F) × (Fin m → K)) ≃ₗ[F]
    ((F × F) × (Fin m → K)))) v =
      (a : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) v
  rw [castEquiv_apply, castLin_refl]
  rfl

theorem normOmegaCast_comp {l : ℕ} (h₁ : k ≤ l) (h₂ : l ≤ m) :
    (normOmegaCast E h₂).comp (normOmegaCast E h₁) = normOmegaCast E (h₁.trans h₂) := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  rw [MonoidHom.comp_apply]
  change (castEquiv h₂ ((normOmegaCast E h₁ a : normOmega E l) :
    ((F × F) × (Fin l → K)) ≃ₗ[F] ((F × F) × (Fin l → K)))) v =
      (castEquiv (h₁.trans h₂) a) v
  rw [normOmegaCast_apply E h₁ a, castEquiv_apply, castEquiv_apply,
    castEquiv_toLinearMap, castLin_castLin]

@[expose] noncomputable def anchorBlock (h : 2 ≤ m) : Subgroup (normOmega E m) :=
  (normOmegaCast E h).range

end Cast

section Unitary

open CFSG.GH74.Generic.S1.SymBlocksUni
open scoped Matrix

variable (E : QuadExt F K (unitaryInvolution K 2 f)) {m : ℕ}

@[expose] noncomputable def suEmbLin (m : ℕ) :
    SUid (unitaryInvolution K 2 f) m →*
      (((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) where
  toFun g := hypExt (suEndN (F := F) (unitaryInvolution K 2 f) m g)
  map_one' := by
    apply LinearEquiv.ext
    intro p
    simp [hypExt_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro p
    simp [hypExt_apply, LinearEquiv.mul_apply]

private theorem SUid_eq_one_of_lt_two (hm : m < 2) (g : SUid (unitaryInvolution K 2 f) m) :
    g = 1 := by
  have hdet : ((g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K).det = 1 := g.2.1
  obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
  · apply Subtype.ext
    apply Units.ext
    ext i j
    exact i.elim0
  · apply Subtype.ext
    apply Units.ext
    rw [Matrix.det_fin_one] at hdet
    ext i j
    fin_cases i
    fin_cases j
    simpa using hdet

theorem suEmbLin_mem_normOmega (m : ℕ) (g : SUid (unitaryInvolution K 2 f) m) :
    suEmbLin (F := F) m g ∈ normOmega E m := by
  rcases lt_or_ge m 2 with hm | hm
  · rw [SUid_eq_one_of_lt_two hm g, map_one]
    exact one_mem _
  · refine hypExt_mem_orthDerived_of_kLinear E hm (suEndN_mem_orthogonalGroup E m g) ?_
    intro c x
    rw [suEndN_apply, suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def,
      CFSG.ClassicalGroups.Unitary.smul_def]
    exact Matrix.mulVec_smul _ _ _

@[expose] noncomputable def suEmb (m : ℕ) : SUid (unitaryInvolution K 2 f) m →* normOmega E m :=
  (suEmbLin (F := F) m).codRestrict (normOmega E m) (suEmbLin_mem_normOmega E m)

theorem suEmb_apply (m : ℕ) (g : SUid (unitaryInvolution K 2 f) m) (p : (F × F) × (Fin m → K)) :
    ((suEmb E m g : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) p = (p.1, g • p.2) := by
  change hypExt (suEndN (F := F) (unitaryInvolution K 2 f) m g) p = (p.1, g • p.2)
  rw [hypExt_apply, suEndN_apply]

theorem suEmb_injective (m : ℕ) : Function.Injective (suEmb E m) := by
  intro g h hgh
  apply suEndN_injective (F := F) (unitaryInvolution K 2 f) m
  apply LinearEquiv.ext
  intro v
  have hgh' : suEmbLin (F := F) m g = suEmbLin (F := F) m h :=
    congrArg (fun e : normOmega E m =>
      (e : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))) hgh
  have hv := congrArg (fun e : ((F × F) × (Fin m → K)) ≃ₗ[F]
    ((F × F) × (Fin m → K)) => (e ((0, 0), v)).2) hgh'
  simpa [suEmbLin, hypExt_apply] using hv

@[expose] noncomputable def suEquiv (h : UnitaryFieldData 2 f K) (n : ℕ) :
    SUid (unitaryInvolution K 2 f) n ≃* unitarySU 2 f K n :=
  MulEquiv.subgroupCongr (SUid_eq_statedSU (by rw [h.card, ← pow_mul, mul_comm]) n)

@[expose] noncomputable def uniEmb (h : UnitaryFieldData 2 f K) (m : ℕ) :
    unitarySU 2 f K m →* normOmega E m :=
  (suEmb (F := F) E m).comp (suEquiv h m).symm.toMonoidHom

theorem uniEmb_injective (h : UnitaryFieldData 2 f K) (m : ℕ) :
    Function.Injective (uniEmb E h m) := by
  intro a b hab
  exact (suEquiv h m).symm.injective (suEmb_injective E m (by
    simpa [uniEmb, MonoidHom.comp_apply] using hab))

private theorem blkMat_castSucc_mulVec_castSucc {A : Matrix (Fin m) (Fin m) K}
    (x : Fin (m + 1) → K) (a : Fin m) :
    (blkMat (Fin.castSucc) A *ᵥ x) (Fin.castSucc a) =
      (A *ᵥ fun b : Fin m => x (Fin.castSucc b)) a := by
  simp only [Matrix.mulVec_apply, Matrix.row_apply, dotProduct, Fin.sum_univ_castSucc]
  have hlast : blkMat (Fin.castSucc) A (Fin.castSucc a) (Fin.last m) = 0 := by
    rw [blkMat_apply_of_not_mem_right A (Fin.castSucc a)
      (fun y h => Fin.castSucc_ne_last y h.symm)]
    rw [Matrix.one_apply, if_neg (Fin.castSucc_ne_last a)]
  rw [hlast, zero_mul, add_zero]
  exact Finset.sum_congr rfl fun b _ => by
    rw [blkMat_apply_ι (Fin.castSucc_injective m)]

private theorem blkMat_castSucc_mulVec_last {A : Matrix (Fin m) (Fin m) K}
    (x : Fin (m + 1) → K) :
    (blkMat (Fin.castSucc) A *ᵥ x) (Fin.last m) = x (Fin.last m) := by
  simp only [Matrix.mulVec_apply, Matrix.row_apply, dotProduct, Fin.sum_univ_castSucc]
  have hzero : ∀ b : Fin m, blkMat (Fin.castSucc) A (Fin.last m) (Fin.castSucc b) = 0 := by
    intro b
    rw [blkMat_apply_of_not_mem_left A
      (fun y h => Fin.castSucc_ne_last y h.symm) (Fin.castSucc b)]
    rw [Matrix.one_apply, if_neg (fun h => Fin.castSucc_ne_last b h.symm)]
  rw [Finset.sum_eq_zero fun b _ => by rw [hzero b, zero_mul], zero_add]
  rw [blkMat_apply_of_not_mem_left A
    (fun y h => Fin.castSucc_ne_last y h.symm) (Fin.last m)]
  rw [Matrix.one_apply, if_pos rfl, one_mul]

theorem suEmb_blkEmb (m : ℕ) (G : SUid (unitaryInvolution K 2 f) m) :
    suEmb E (m + 1) (blkEmb (unitaryInvolution K 2 f) (Fin.castSucc_injective m) G) =
      normOmegaCast E (Nat.le_succ m) (suEmb E m G) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro p
  rw [suEmb_apply, normOmegaCast_apply, castEquiv_apply, castLin_apply]
  refine Prod.ext ?_ ?_
  · rfl
  · funext j
    simp only [Prod.mk.eta]
    refine Fin.lastCases ?_ (fun a => ?_) j
    · rw [CFSG.ClassicalGroups.Unitary.smul_def, coe_coe_blkEmb, blkMat_castSucc_mulVec_last]
      simp [Fin.val_last]
    · rw [CFSG.ClassicalGroups.Unitary.smul_def, coe_coe_blkEmb,
        blkMat_castSucc_mulVec_castSucc]
      have hj : ((Fin.castSucc a : Fin (m + 1)) : ℕ) < m := a.2
      rw [dif_pos hj]
      have hR : (suEmbLin (F := F) m G (castRestr (Nat.le_succ m) p)).2
          ⟨(Fin.castSucc a : Fin (m + 1)), hj⟩ =
          (((G : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
            fun b : Fin m => p.2 (Fin.castSucc b)) a := by
        change (suEndN (F := F) (unitaryInvolution K 2 f) m G
          (castRestr (Nat.le_succ m) p).2)
            ⟨(Fin.castSucc a : Fin (m + 1)), hj⟩ = _
        rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def]
        rw [show (⟨(Fin.castSucc a : Fin (m + 1)), hj⟩ : Fin m) = a from Fin.ext rfl]
        congr 1
      change (((G : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
        fun b : Fin m => p.2 (Fin.castSucc b)) a =
          ((suEmbLin (F := F) m G) (castRestr (Nat.le_succ m) p)).2
            ⟨(Fin.castSucc a : Fin (m + 1)), hj⟩
      rw [hR]

@[expose] noncomputable def uniCast (h : UnitaryFieldData 2 f K) (m : ℕ) :
    unitarySU 2 f K m →* unitarySU 2 f K (m + 1) :=
  (suEquiv h (m + 1)).toMonoidHom.comp
    ((CFSG.GH74.Generic.S1.SymBlocksUni.blkEmb (unitaryInvolution K 2 f)
      (Fin.castSucc_injective m)).comp (suEquiv h m).symm.toMonoidHom)

theorem uniEmb_uniCast (h : UnitaryFieldData 2 f K) (m : ℕ) (g : unitarySU 2 f K m) :
    uniEmb E h (m + 1) (uniCast h m g) = normOmegaCast E (Nat.le_succ m) (uniEmb E h m g) := by
  simpa only [uniEmb, uniCast, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using suEmb_blkEmb (E := E) m ((suEquiv h m).symm g)

end Unitary

section Galois

open CFSG.LieType.Steinberg

@[expose] noncomputable def galoisRingHom (h : UnitaryFieldData 2 f K) : GaloisField 2 f →+* K :=
  letI := Fintype.ofFinite (GaloisField 2 f)
  letI := Fintype.ofFinite (fixedSubfield K 2 f)
  (fixedSubfield K 2 f).subtype.comp (FiniteField.ringEquivOfCardEq (K := GaloisField 2 f)
    (K' := fixedSubfield K 2 f) (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        GaloisField.card 2 f (by have := h.one_le; omega),
        card_fixedSubfield (by rw [h.card, ← pow_mul, mul_comm])])).toRingHom

@[expose, instance_reducible] noncomputable def galoisAlgebra (h : UnitaryFieldData 2 f K) :
    Algebra (GaloisField 2 f) K :=
  (galoisRingHom h).toAlgebra

theorem galoisQuadExt (h : UnitaryFieldData 2 f K) :
    letI := galoisAlgebra h
    QuadExt (GaloisField 2 f) K (unitaryInvolution K 2 f) := by
  letI := galoisAlgebra h
  exact quadExt_of_card_of_char_two f (GaloisField.card 2 f (by have := h.one_le; omega))
    (by rw [h.card, ← pow_mul, mul_comm])

end Galois

end CFSG.ClassicalGroups.Orthogonal.UnitaryOmega
