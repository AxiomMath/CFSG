module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Involution

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

section Eigen

variable (i : V ≃ₗ[F] V)

@[expose] def plusSp : Submodule F V := Module.End.eigenspace (i : Module.End F V) 1

@[expose] def minusSp : Submodule F V := Module.End.eigenspace (i : Module.End F V) (-1)

variable {i}

theorem mem_plusSp {v : V} : v ∈ plusSp i ↔ i v = v := by
  rw [plusSp, Module.End.mem_eigenspace_iff, one_smul]
  rfl

theorem mem_minusSp {v : V} : v ∈ minusSp i ↔ i v = -v := by
  rw [minusSp, Module.End.mem_eigenspace_iff, neg_one_smul]
  rfl

theorem isCompl_plusSp_minusSp (h2 : (2 : F) ≠ 0) (hii : i * i = 1) :
    IsCompl (plusSp i) (minusSp i) :=
  CFSG.ClassicalInvolution.Models.OrthogonalPairs.isCompl_eigenspace_of_mul_self h2
    (T := (i : Module.End F V)) (LinearMap.ext fun x => by
      simpa using LinearEquiv.congr_fun hii x)

theorem polar_plusSp_minusSp {Q : QuadraticForm F V} (h2 : (2 : F) ≠ 0)
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {x y : V} (hx : x ∈ plusSp i)
    (hy : y ∈ minusSp i) : polar Q x y = 0 := by
  have h := polar_map_of_mem hi x y
  rw [mem_plusSp.mp hx, mem_minusSp.mp hy, polar_neg_right] at h
  have : (2 : F) * polar Q x y = 0 := by linear_combination -h
  exact (mul_eq_zero.mp this).resolve_left h2

end Eigen

section Block

variable {Q : QuadraticForm F V} {i : V ≃ₗ[F] V}

@[expose] noncomputable def projP (i : V ≃ₗ[F] V) : V →ₗ[F] V :=
  (2⁻¹ : F) • (LinearMap.id + (i : V →ₗ[F] V))

@[expose] noncomputable def projM (i : V ≃ₗ[F] V) : V →ₗ[F] V :=
  (2⁻¹ : F) • (LinearMap.id - (i : V →ₗ[F] V))

theorem projP_apply (x : V) : projP i x = (2⁻¹ : F) • (x + i x) := rfl

theorem projM_apply (x : V) : projM i x = (2⁻¹ : F) • (x - i x) := rfl

theorem projP_add_projM (h2 : (2 : F) ≠ 0) (x : V) : projP i x + projM i x = x := by
  rw [projP_apply, projM_apply, ← smul_add, add_add_sub_cancel, ← two_smul F x, smul_smul,
    inv_mul_cancel₀ h2, one_smul]

theorem projP_mem (hii : i * i = 1) (x : V) : projP i x ∈ plusSp i := by
  rw [mem_plusSp, projP_apply, map_smul, map_add]
  have : i (i x) = x := by simpa using LinearEquiv.congr_fun hii x
  rw [this, add_comm]

theorem projM_mem (hii : i * i = 1) (x : V) : projM i x ∈ minusSp i := by
  rw [mem_minusSp, projM_apply, map_smul, map_sub]
  have : i (i x) = x := by simpa using LinearEquiv.congr_fun hii x
  rw [this, smul_sub, smul_sub, neg_sub]

theorem projP_of_mem_plusSp (h2 : (2 : F) ≠ 0) {x : V} (hx : x ∈ plusSp i) : projP i x = x := by
  rw [projP_apply, mem_plusSp.mp hx, ← two_smul F x, smul_smul, inv_mul_cancel₀ h2, one_smul]

theorem projP_of_mem_minusSp {x : V} (hx : x ∈ minusSp i) : projP i x = 0 := by
  rw [projP_apply, mem_minusSp.mp hx, add_neg_cancel, smul_zero]

theorem projM_of_mem_plusSp {x : V} (hx : x ∈ plusSp i) : projM i x = 0 := by
  rw [projM_apply, mem_plusSp.mp hx, sub_self, smul_zero]

theorem projM_of_mem_minusSp (h2 : (2 : F) ≠ 0) {x : V} (hx : x ∈ minusSp i) :
    projM i x = x := by
  rw [projM_apply, mem_minusSp.mp hx, sub_neg_eq_add, ← two_smul F x, smul_smul,
    inv_mul_cancel₀ h2, one_smul]

theorem projP_add_of_mem (h2 : (2 : F) ≠ 0) {u v : V} (hu : u ∈ plusSp i) (hv : v ∈ minusSp i) :
    projP i (u + v) = u := by
  rw [map_add, projP_of_mem_plusSp h2 hu, projP_of_mem_minusSp hv, add_zero]

theorem projM_add_of_mem (h2 : (2 : F) ≠ 0) {u v : V} (hu : u ∈ plusSp i) (hv : v ∈ minusSp i) :
    projM i (u + v) = v := by
  rw [map_add, projM_of_mem_plusSp hu, projM_of_mem_minusSp h2 hv, zero_add]

theorem map_mem_plusSp {g : V ≃ₗ[F] V} (hg : g * i = i * g) {x : V} (hx : x ∈ plusSp i) :
    g x ∈ plusSp i := by
  rw [mem_plusSp]
  have := LinearEquiv.congr_fun hg x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, mem_plusSp.mp hx] at this
  exact this.symm

theorem map_mem_minusSp {g : V ≃ₗ[F] V} (hg : g * i = i * g) {x : V} (hx : x ∈ minusSp i) :
    g x ∈ minusSp i := by
  rw [mem_minusSp]
  have := LinearEquiv.congr_fun hg x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, mem_minusSp.mp hx, map_neg] at this
  exact this.symm

theorem inv_mul_eq_mul_inv_of {g : V ≃ₗ[F] V} (hg : g * i = i * g) : g⁻¹ * i = i * g⁻¹ := by
  calc g⁻¹ * i = g⁻¹ * (i * g) * g⁻¹ := by group
    _ = g⁻¹ * (g * i) * g⁻¹ := by rw [hg]
    _ = i * g⁻¹ := by group

@[expose] noncomputable def blockLin (i g : V ≃ₗ[F] V) : V →ₗ[F] V :=
  (g : V →ₗ[F] V) ∘ₗ projP i + projM i

theorem blockLin_apply (i g : V ≃ₗ[F] V) (x : V) : blockLin i g x = g (projP i x) + projM i x :=
  rfl

theorem blockLin_add (h2 : (2 : F) ≠ 0) (g : V ≃ₗ[F] V) {u v : V} (hu : u ∈ plusSp i)
    (hv : v ∈ minusSp i) : blockLin i g (u + v) = g u + v := by
  rw [blockLin_apply, projP_add_of_mem h2 hu hv, projM_add_of_mem h2 hu hv]

theorem blockLin_mul (h2 : (2 : F) ≠ 0) (hii : i * i = 1) (g : V ≃ₗ[F] V) {g' : V ≃ₗ[F] V}
    (hg' : g' * i = i * g') (x : V) :
    blockLin i (g * g') x = blockLin i g (blockLin i g' x) := by
  have hx := projP_add_projM h2 (i := i) x
  have hP := projP_mem hii (i := i) x
  have hM := projM_mem hii (i := i) x
  rw [blockLin_apply i g' x, blockLin_add h2 g (map_mem_plusSp hg' hP) hM,
    blockLin_apply i (g * g') x]
  rfl

theorem blockLin_one (h2 : (2 : F) ≠ 0) (x : V) : blockLin i 1 x = x := by
  rw [blockLin_apply]
  simpa using projP_add_projM h2 (i := i) x

@[expose] noncomputable def blockEquiv (h2 : (2 : F) ≠ 0) (hii : i * i = 1) (g : V ≃ₗ[F] V)
    (hg : g * i = i * g) : V ≃ₗ[F] V :=
  LinearEquiv.ofLinearMap (blockLin i g) (blockLin i g⁻¹)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← blockLin_mul h2 hii g (inv_mul_eq_mul_inv_of hg), mul_inv_cancel,
        blockLin_one h2]
      rfl)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← blockLin_mul h2 hii g⁻¹ hg, inv_mul_cancel, blockLin_one h2]
      rfl)

theorem blockEquiv_apply (h2 : (2 : F) ≠ 0) (hii : i * i = 1) {g : V ≃ₗ[F] V}
    (hg : g * i = i * g) (x : V) : blockEquiv h2 hii g hg x = g (projP i x) + projM i x :=
  rfl

theorem blockEquiv_apply_add (h2 : (2 : F) ≠ 0) (hii : i * i = 1) {g : V ≃ₗ[F] V}
    (hg : g * i = i * g) {u v : V} (hu : u ∈ plusSp i) (hv : v ∈ minusSp i) :
    blockEquiv h2 hii g hg (u + v) = g u + v :=
  blockLin_add h2 g hu hv

theorem blockEquiv_mul (h2 : (2 : F) ≠ 0) (hii : i * i = 1) {g g' : V ≃ₗ[F] V}
    (hg : g * i = i * g) (hg' : g' * i = i * g') (hgg : (g * g') * i = i * (g * g')) :
    blockEquiv h2 hii (g * g') hgg = blockEquiv h2 hii g hg * blockEquiv h2 hii g' hg' :=
  LinearEquiv.ext fun x => by
    rw [LinearEquiv.mul_apply]
    exact blockLin_mul h2 hii g hg' x

theorem blockEquiv_one (h2 : (2 : F) ≠ 0) (hii : i * i = 1) (h1 : (1 : V ≃ₗ[F] V) * i = i * 1) :
    blockEquiv h2 hii 1 h1 = 1 :=
  LinearEquiv.ext fun x => blockLin_one h2 x

end Block

section Groups

variable (Q : QuadraticForm F V) (i : V ≃ₗ[F] V)

@[expose] def nP : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g * i = i * g ∧
    ∀ v ∈ minusSp i, g v = v}
  mul_mem' := by
    rintro g h ⟨hgO, hgc, hgf⟩ ⟨hhO, hhc, hhf⟩
    refine ⟨mul_mem hgO hhO, ?_, fun v hv => ?_⟩
    · calc g * h * i = g * (h * i) := by group
        _ = g * (i * h) := by rw [hhc]
        _ = (g * i) * h := by group
        _ = (i * g) * h := by rw [hgc]
        _ = i * (g * h) := by group
    · rw [LinearEquiv.mul_apply, hhf v hv, hgf v hv]
  one_mem' := ⟨one_mem _, by simp, fun v _ => rfl⟩
  inv_mem' := by
    rintro g ⟨hgO, hgc, hgf⟩
    refine ⟨inv_mem hgO, inv_mul_eq_mul_inv_of hgc, fun v hv => ?_⟩
    calc g⁻¹ v = g⁻¹ (g v) := by rw [hgf v hv]
      _ = v := LinearEquiv.inv_apply_apply' g v

@[expose] def nM : Subgroup (V ≃ₗ[F] V) where
  carrier := {g | g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g * i = i * g ∧
    ∀ v ∈ plusSp i, g v = v}
  mul_mem' := by
    rintro g h ⟨hgO, hgc, hgf⟩ ⟨hhO, hhc, hhf⟩
    refine ⟨mul_mem hgO hhO, ?_, fun v hv => ?_⟩
    · calc g * h * i = g * (h * i) := by group
        _ = g * (i * h) := by rw [hhc]
        _ = (g * i) * h := by group
        _ = (i * g) * h := by rw [hgc]
        _ = i * (g * h) := by group
    · rw [LinearEquiv.mul_apply, hhf v hv, hgf v hv]
  one_mem' := ⟨one_mem _, by simp, fun v _ => rfl⟩
  inv_mem' := by
    rintro g ⟨hgO, hgc, hgf⟩
    refine ⟨inv_mem hgO, inv_mul_eq_mul_inv_of hgc, fun v hv => ?_⟩
    calc g⁻¹ v = g⁻¹ (g v) := by rw [hgf v hv]
      _ = v := LinearEquiv.inv_apply_apply' g v

variable {Q i}

theorem mem_nP {g : V ≃ₗ[F] V} :
    g ∈ nP Q i ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g * i = i * g ∧
      ∀ v ∈ minusSp i, g v = v := Iff.rfl

theorem mem_nM {g : V ≃ₗ[F] V} :
    g ∈ nM Q i ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ g * i = i * g ∧
      ∀ v ∈ plusSp i, g v = v := Iff.rfl

theorem exists_add_eq (h2 : (2 : F) ≠ 0) (hii : i * i = 1) (x : V) :
    ∃ u ∈ plusSp i, ∃ v ∈ minusSp i, x = u + v :=
  ⟨_, projP_mem hii x, _, projM_mem hii x, (projP_add_projM h2 x).symm⟩

theorem nP_comm_nM (h2 : (2 : F) ≠ 0) (hii : i * i = 1) {g h : V ≃ₗ[F] V} (hg : g ∈ nP Q i)
    (hh : h ∈ nM Q i) : g * h = h * g := by
  obtain ⟨-, hgc, hgf⟩ := hg
  obtain ⟨-, hhc, hhf⟩ := hh
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
  calc (g * h) (u + v) = g (u + h v) := by rw [LinearEquiv.mul_apply, map_add, hhf u hu]
    _ = g u + h v := by rw [map_add, hgf _ (map_mem_minusSp hhc hv)]
    _ = h (g u) + h v := by rw [hhf _ (map_mem_plusSp hgc hu)]
    _ = (h * g) (u + v) := by
      rw [LinearEquiv.mul_apply, map_add g, hgf v hv, map_add h]

theorem eq_one_of_mem_nP_of_mem_nM (h2 : (2 : F) ≠ 0) (hii : i * i = 1) {g : V ≃ₗ[F] V}
    (hg : g ∈ nP Q i) (hg' : g ∈ nM Q i) : g = 1 := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
  rw [map_add, hg.2.2 v hv, hg'.2.2 u hu]
  rfl

theorem nP_le_centralizer : nP Q i ≤ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.mp hh]
  exact hg.2.1.symm

theorem nM_le_centralizer : nM Q i ≤ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.mp hh]
  exact hg.2.1.symm

theorem nP_le_orthogonalGroup : nP Q i ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun _ h => h.1

theorem nM_le_orthogonalGroup : nM Q i ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun _ h => h.1

end Groups

section BlockHom

variable {Q : QuadraticForm F V} {i : V ≃ₗ[F] V}

theorem blockEquiv_mem_nP (h2 : (2 : F) ≠ 0) (hii : i * i = 1)
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {g : V ≃ₗ[F] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg : g * i = i * g) :
    blockEquiv h2 hii g hg ∈ nP Q i := by
  refine ⟨?_, ?_, fun v hv => ?_⟩
  · refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
    rw [blockEquiv_apply_add h2 hii hg hu hv, QuadraticMap.map_add Q, QuadraticMap.map_add Q u v,
      map_of_mem hgO u, polar_plusSp_minusSp h2 hi hu hv,
      polar_plusSp_minusSp h2 hi (map_mem_plusSp hg hu) hv]
  · refine LinearEquiv.ext fun x => ?_
    obtain ⟨u, hu, v, hv, rfl⟩ := exists_add_eq h2 hii x
    have e1 : i (u + v) = u + -v := by
      rw [map_add, mem_plusSp.mp hu, mem_minusSp.mp hv]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, e1,
      blockEquiv_apply_add h2 hii hg hu hv, blockEquiv_apply_add h2 hii hg hu
        (Submodule.neg_mem _ hv), map_add, mem_plusSp.mp (map_mem_plusSp hg hu),
      mem_minusSp.mp hv]
  · have := blockEquiv_apply_add h2 hii hg (Submodule.zero_mem _) hv
    rwa [map_zero, zero_add] at this

@[expose] def negI (i : V ≃ₗ[F] V) : V ≃ₗ[F] V := LinearEquiv.neg F * i

theorem negI_apply (x : V) : negI i x = -(i x) := rfl

theorem plusSp_negI : plusSp (negI i) = minusSp i := by
  ext x
  rw [mem_plusSp, mem_minusSp, negI_apply, neg_eq_iff_eq_neg]

theorem minusSp_negI : minusSp (negI i) = plusSp i := by
  ext x
  simp [mem_plusSp, mem_minusSp, negI_apply]

theorem negI_mul_self (hii : i * i = 1) : negI i * negI i = 1 := by
  refine LinearEquiv.ext fun x => ?_
  have : i (i x) = x := by simpa using LinearEquiv.congr_fun hii x
  simp [negI_apply, this]

theorem negI_mem_orthogonalGroup (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    negI i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [negI_apply, QuadraticMap.map_neg, map_of_mem hi]

theorem mul_negI_comm {g : V ≃ₗ[F] V} (hg : g * i = i * g) : g * negI i = negI i * g := by
  refine LinearEquiv.ext fun x => ?_
  have := LinearEquiv.congr_fun hg x
  simp only [LinearEquiv.mul_apply] at this ⊢
  simp [negI_apply, this]

theorem nM_eq_nP_negI : nM Q i = nP Q (negI i) := by
  ext g
  rw [mem_nM, mem_nP, minusSp_negI]
  refine and_congr_right fun _ => and_congr_left fun _ => ?_
  constructor
  · intro hg
    exact mul_negI_comm hg
  · intro hg
    refine LinearEquiv.ext fun x => ?_
    have := LinearEquiv.congr_fun hg x
    simp only [LinearEquiv.mul_apply, negI_apply, map_neg, neg_inj] at this
    simpa [LinearEquiv.mul_apply] using this

theorem projP_negI (x : V) : projP (negI i) x = projM i x := by
  rw [projP_apply, projM_apply, negI_apply, ← sub_eq_add_neg]

theorem projM_negI (x : V) : projM (negI i) x = projP i x := by
  rw [projP_apply, projM_apply, negI_apply, sub_neg_eq_add]

theorem comm_of_mem_centralizer {g : V ≃ₗ[F] V}
    (hg : g ∈ Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V))) : g * i = i * g :=
  (Subgroup.mem_centralizer_iff.mp hg i (Set.mem_singleton i)).symm

@[expose] noncomputable def blockP (h2 : (2 : F) ≠ 0) (hii : i * i = 1) :
    ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V))) →* (V ≃ₗ[F] V) where
  toFun g := blockEquiv h2 hii g.1 (comm_of_mem_centralizer g.2.2)
  map_one' := blockEquiv_one h2 hii _
  map_mul' g g' := blockEquiv_mul h2 hii (comm_of_mem_centralizer g.2.2)
    (comm_of_mem_centralizer g'.2.2) _

@[expose] noncomputable def blockM (h2 : (2 : F) ≠ 0) (hii : i * i = 1) :
    ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V))) →* (V ≃ₗ[F] V) where
  toFun g := blockEquiv h2 (negI_mul_self hii) g.1 (mul_negI_comm (comm_of_mem_centralizer g.2.2))
  map_one' := blockEquiv_one h2 (negI_mul_self hii) _
  map_mul' g g' := blockEquiv_mul h2 (negI_mul_self hii)
    (mul_negI_comm (comm_of_mem_centralizer g.2.2))
    (mul_negI_comm (comm_of_mem_centralizer g'.2.2)) _

theorem blockP_mem_nP (h2 : (2 : F) ≠ 0) (hii : i * i = 1)
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)))) : blockP h2 hii g ∈ nP Q i :=
  blockEquiv_mem_nP h2 hii hi g.2.1 (comm_of_mem_centralizer g.2.2)

theorem blockM_mem_nM (h2 : (2 : F) ≠ 0) (hii : i * i = 1)
    (hi : i ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)))) : blockM h2 hii g ∈ nM Q i := by
  rw [nM_eq_nP_negI]
  exact blockEquiv_mem_nP h2 (negI_mul_self hii) (negI_mem_orthogonalGroup hi) g.2.1
    (mul_negI_comm (comm_of_mem_centralizer g.2.2))

theorem blockP_mul_blockM (h2 : (2 : F) ≠ 0) (hii : i * i = 1)
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup Q ⊓
      Subgroup.centralizer ({i} : Set (V ≃ₗ[F] V)))) :
    blockP h2 hii g * blockM h2 hii g = g.1 := by
  refine LinearEquiv.ext fun x => ?_
  have hg : (g.1) * i = i * g.1 := comm_of_mem_centralizer g.2.2
  have hP := projP_mem hii (i := i) x
  have hM := projM_mem hii (i := i) x
  have e1 : blockM h2 hii g x = projP i x + g.1 (projM i x) := by
    change g.1 (projP (negI i) x) + projM (negI i) x = _
    rw [projP_negI, projM_negI, add_comm]
  rw [LinearEquiv.mul_apply, e1]
  change blockEquiv h2 hii g.1 hg _ = _
  rw [blockEquiv_apply_add h2 hii hg hP (map_mem_minusSp hg hM), ← map_add,
    projP_add_projM h2]

end BlockHom

end CFSG.ClassicalInvolution.ModelFacts
