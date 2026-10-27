module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverCore
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFourCore

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover

open Matrix CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl
open scoped commutatorElement

section Split

variable {E X : Type*} [Group E] [Group X] {θ : E →* X} (hθ : Function.Surjective θ)
  (hC : θ.ker ≤ Subgroup.center E)

include hθ in
theorem map_derivedComap (R : Subgroup X) [Group.IsPerfect R] :
    ⁅R.comap θ, R.comap θ⁆.map θ = R := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hθ,
    Subgroup.commutator_eq_self]

include hθ in
theorem comap_le_derivedComap_sup (R : Subgroup X) [Group.IsPerfect R] :
    R.comap θ ≤ ⁅R.comap θ, R.comap θ⁆ ⊔ θ.ker := by
  intro h hh
  have hhR : θ h ∈ ⁅R.comap θ, R.comap θ⁆.map θ := by
    rw [map_derivedComap hθ R]
    exact hh
  obtain ⟨f, hf, hfh⟩ := hhR
  have hk : f⁻¹ * h ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfh, inv_mul_cancel]
  have := Subgroup.mul_mem_sup hf hk
  rwa [mul_inv_cancel_left] at this

include hθ hC in
theorem isPerfect_derivedComap (R : Subgroup X) [Group.IsPerfect R] :
    Group.IsPerfect ↥(⁅R.comap θ, R.comap θ⁆ : Subgroup E) :=
  Subgroup.isPerfect_iff.mpr (le_antisymm (Subgroup.commutator_le_self _)
    ((Subgroup.commutator_mono (comap_le_derivedComap_sup hθ R)
      (comap_le_derivedComap_sup hθ R)).trans (BinarySymplecticSix.commutator_sup_le hC)))

include hθ in
theorem exists_derivedComap_cover {Y : Type*} [Group Y] (ι : Y →* X) (hι : Function.Injective ι)
    [Group.IsPerfect ι.range] :
    ∃ θF : ↥(⁅ι.range.comap θ, ι.range.comap θ⁆ : Subgroup E) →* Y, Function.Surjective θF ∧
      ∀ x, ι (θF x) = θ x := by
  set F := ⁅ι.range.comap θ, ι.range.comap θ⁆
  let φ := MonoidHom.ofInjective hι
  let θR : F →* ι.range := (θ.comp F.subtype).codRestrict ι.range fun f =>
    Subgroup.mem_comap.1 (Subgroup.commutator_le_self (ι.range.comap θ) f.2)
  refine ⟨φ.symm.toMonoidHom.comp θR, fun y => ?_, fun x => ?_⟩
  · have hy : ι y ∈ F.map θ := by
      rw [map_derivedComap hθ]
      exact ⟨y, rfl⟩
    obtain ⟨f, hf, hfy⟩ := hy
    refine ⟨⟨f, hf⟩, ?_⟩
    apply φ.injective
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    exact Subtype.ext (by rw [MonoidHom.ofInjective_apply]; exact hfy)
  · have h := congrArg Subtype.val (φ.apply_symm_apply (θR x))
    rw [MonoidHom.ofInjective_apply] at h
    exact h

include hθ hC in
theorem mul_comm_of_derivedComap (R : Subgroup X) [Group.IsPerfect R]
    (hinj : ∀ f ∈ ⁅R.comap θ, R.comap θ⁆, θ f = 1 → f = 1) {x y : E} (hx : θ x ∈ R)
    (hy : θ y ∈ R) (hxy : θ x * θ y = θ y * θ x) : x * y = y * x := by
  have hx' := comap_le_derivedComap_sup hθ R hx
  have hy' := comap_le_derivedComap_sup hθ R hy
  rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hx' hy'
  obtain ⟨f, hf, c, hc, rfl⟩ := hx'
  obtain ⟨f', hf', c', hc', rfl⟩ := hy'
  have hθc : θ c = 1 := hc
  have hθc' : θ c' = 1 := hc'
  rw [map_mul, map_mul, hθc, hθc', mul_one, mul_one] at hxy
  have hff : f * f' = f' * f := by
    have h1 : f * f' * (f' * f)⁻¹ ∈ ⁅R.comap θ, R.comap θ⁆ :=
      mul_mem (mul_mem hf hf') (inv_mem (mul_mem hf' hf))
    have h2 : θ (f * f' * (f' * f)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.1 (hinj _ h1 h2)
  have hcen : ∀ z ∈ θ.ker, ∀ g : E, z * g = g * z := fun z hz g =>
    (Subgroup.mem_center_iff.1 (hC hz) g).symm
  calc f * c * (f' * c') = f * f' * (c * c') := by
        rw [show f * c * (f' * c') = f * (c * f') * c' by group, hcen c hc f']
        group
    _ = f' * f * (c' * c) := by rw [hff, hcen c hc c']
    _ = f' * c' * (f * c) := by
        rw [show f' * f * (c' * c) = f' * (f * c') * c by group, ← hcen c' hc' f]
        group

end Split

variable {K : Type} [Field K]

section Levi

@[expose] def leviSL : SpecialLinearGroup (Fin 3) K →* StatedSp 3 K :=
  leviSp.comp SpecialLinearGroup.toGL

theorem leviSL_injective : Function.Injective (leviSL (K := K)) :=
  BinarySymplecticSix.leviSp_injective.comp SpecialLinearGroup.toGL_injective

instance : Group.IsPerfect (leviSL (K := K)).range :=
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K) (n := 3)
    le_rfl
  Group.IsPerfect.range _

@[expose] def diagConj (t : Fin 3 → Kˣ) (A : SpecialLinearGroup (Fin 3) K) :
    SpecialLinearGroup (Fin 3) K :=
  ⟨(TauCeti.diagGL t : Matrix (Fin 3) (Fin 3) K) * A *
      ((TauCeti.diagGL t)⁻¹ : GL (Fin 3) K), by
    rw [det_mul, det_mul, A.2, mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, det_one]⟩

theorem torusHom_mul_leviSL_mul_inv (t : Fin 3 → Kˣ) (A : SpecialLinearGroup (Fin 3) K) :
    torusHom t * leviSL A * (torusHom t)⁻¹ = leviSL (diagConj t A) := by
  change leviSp (TauCeti.diagGL t) * leviSp (SpecialLinearGroup.toGL A) *
    (leviSp (TauCeti.diagGL t))⁻¹ = leviSp (SpecialLinearGroup.toGL (diagConj t A))
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  exact Units.ext rfl

theorem torusHom_const_commute_leviSL (s : Kˣ) (A : SpecialLinearGroup (Fin 3) K) :
    torusHom (fun _ => s) * leviSL A = leviSL A * torusHom (fun _ => s) := by
  change leviSp (TauCeti.diagGL fun _ => s) * leviSp (SpecialLinearGroup.toGL A) =
    leviSp (SpecialLinearGroup.toGL A) * leviSp (TauCeti.diagGL fun _ => s)
  rw [← map_mul, ← map_mul]
  congr 1
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, TauCeti.diagGL_coe]
  change diagonal (fun _ => (s : K)) * (A : Matrix (Fin 3) (Fin 3) K) =
    (A : Matrix (Fin 3) (Fin 3) K) * diagonal (fun _ => (s : K))
  ext i j
  rw [diagonal_mul, mul_diagonal, mul_comm]

end Levi

@[expose] def symGroup : Subgroup (StatedSp 3 K) where
  carrier := {g | ∃ (B : Matrix (Fin 3) (Fin 3) K) (hB : Bᵀ = B), g = upperUnipotentSp 3 K hB}
  one_mem' := ⟨0, transpose_zero, upperUnipotentSp_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨B, hB, rfl⟩ ⟨B', hB', rfl⟩
    exact ⟨B + B', _, upperUnipotentSp_mul hB hB'⟩
  inv_mem' := by
    rintro _ ⟨B, hB, rfl⟩
    refine ⟨-B, by rw [transpose_neg, hB], ?_⟩
    rw [inv_eq_iff_mul_eq_one, upperUnipotentSp_mul, ← upperUnipotentSp_zero]
    exact upperUnipotentSp_congr 3 _ _ (add_neg_cancel B)

theorem tauCoord_mem_symGroup (i j : Fin 3) (a : K) : tauCoord i j a ∈ symGroup :=
  ⟨_, _, rfl⟩

theorem symGroup_mul_comm {g g' : StatedSp 3 K} (hg : g ∈ symGroup) (hg' : g' ∈ symGroup) :
    g * g' = g' * g := by
  obtain ⟨B, hB, rfl⟩ := hg
  obtain ⟨B', hB', rfl⟩ := hg'
  exact commute_upperUnipotentSp hB hB'

section Cover

variable [CharP K 2] {E : Type*} [Group E] {θ : E →* StatedSp 3 K}
  (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)

omit [CharP K 2] in
include hC in
theorem commutatorElement_mem_center_of_symGroup {x y : E} (hx : θ x ∈ symGroup)
    (hy : θ y ∈ symGroup) : ⁅x, y⁆ ∈ Subgroup.center E :=
  hC (by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact symGroup_mul_comm hx hy)

variable [Finite K] [Finite E] [Group.IsPerfect E]

omit [Finite E] [Group.IsPerfect E] in
include hθ hC in
theorem mul_comm_of_tauCoord_ne (hK : 4 ≤ Nat.card K) {i j k l : Fin 3} (hij : i ≤ j)
    (hkl : k ≤ l) (hne : (i, j) ≠ (k, l)) {x y : E} {a b : K} (hx : θ x = tauCoord i j a)
    (hy : θ y = tauCoord k l b) : x * y = y * x := by
  obtain ⟨r, hr0, hr1⟩ := LinearCover.exists_ne_zero_ne_one_of_three_le (K := K) (by omega)
  obtain ⟨t, htkl, htij⟩ := exists_weight_sep hr0 hr1 hij hkl hne
  obtain ⟨g, hg⟩ := hθ (torusHom t)
  have hyV : θ y ∈ symGroup := by
    rw [hy]
    exact tauCoord_mem_symGroup k l b
  have hcen : ∀ (e : E) (s : K), θ e = tauCoord i j s → ⁅e, y⁆ ∈ Subgroup.center E :=
    fun e s he => commutatorElement_mem_center_of_symGroup hC
      (by rw [he]; exact tauCoord_mem_symGroup i j s) hyV
  have h := SymplecticCoverFour.commutatorElement_eq_one_of_weight hθ hC
    (ψ := fun s => tauCoord i j s) (fun s s' => tauCoord_add i j s s') htij hcen
    (fun s => by rw [hg, torusHom_mul_tauCoord_mul_inv])
    (by rw [hg, hy, torusHom_mul_tauCoord_mul_inv, htkl, one_mul]) hx
  exact commutatorElement_eq_one_iff_mul_comm.1 h

@[expose] def pairMap (p : Fin 3) : Fin 2 → Fin 3 :=
  (![![0, 1], ![0, 2], ![1, 2]] : Fin 3 → Fin 2 → Fin 3) p

theorem pairMap_injective (p : Fin 3) : Function.Injective (pairMap p) := by
  revert p
  decide

theorem exists_pairMap (i j : Fin 3) :
    ∃ p : Fin 3, ∃ i' j' : Fin 2, pairMap p i' = i ∧ pairMap p j' = j := by
  revert i j
  decide

omit [Group.IsPerfect E] in
include hθ hC in
theorem mul_comm_of_tauCoord_same (hK : 4 ≤ Nat.card K) (h2 : IsPGroup 2 θ.ker) {i j : Fin 3}
    {x y : E} {a b : K} (hx : θ x = tauCoord i j a) (hy : θ y = tauCoord i j b) :
    x * y = y * x := by
  obtain ⟨p, i', j', hi, hj⟩ := exists_pairMap i j
  set ι := embedSp (K := K) (pairMap p) (pairMap_injective p)
  have : Group.IsPerfect (StatedSp 2 K) := isPerfect_statedSp_of_four_le hK 2
  have : Group.IsPerfect ι.range := Group.IsPerfect.range _
  set F := ⁅ι.range.comap θ, ι.range.comap θ⁆
  obtain ⟨θF, hθF, hθFι⟩ := exists_derivedComap_cover hθ ι
    (embedSp_injective (pairMap_injective p))
  have hθFker : ∀ z : F, θF z = 1 ↔ θ z = 1 := fun z => by
    rw [← hθFι, ← map_one ι]
    exact (embedSp_injective (pairMap_injective p)).eq_iff.symm
  have : Group.IsPerfect F := isPerfect_derivedComap hθ hC _
  have hcenF : θF.ker ≤ Subgroup.center F := fun z hz => Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (Subgroup.mem_center_iff.mp (hC ((hθFker z).mp hz)) g)
  have h2F : IsPGroup 2 θF.ker := fun z => by
    obtain ⟨n, hn⟩ := h2 ⟨(z : F), (hθFker z).mp z.2⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by
      simpa using congrArg (fun w : θ.ker => (w : E)) hn))⟩
  have hbot := SymplecticCoverFour.ker_eq_bot_of_statedSp hθF hcenF (by omega) h2F
  have hinj : ∀ f ∈ F, θ f = 1 → f = 1 := fun f hf hθf => by
    have hk : (⟨f, hf⟩ : F) ∈ θF.ker := (hθFker _).mpr hθf
    rw [hbot, Subgroup.mem_bot] at hk
    exact congrArg Subtype.val hk
  have hmem : ∀ c : K, tauCoord i j c ∈ ι.range := fun c =>
    ⟨tauCoord i' j' c, by rw [embedSp_tauCoord, hi, hj]⟩
  refine mul_comm_of_derivedComap hθ hC ι.range hinj (by rw [hx]; exact hmem a)
    (by rw [hy]; exact hmem b) ?_
  rw [hx, hy]
  exact symGroup_mul_comm (tauCoord_mem_symGroup i j a) (tauCoord_mem_symGroup i j b)

omit [Group.IsPerfect E] in
include hθ hC in
theorem mul_comm_of_tauCoord (hK : 4 ≤ Nat.card K) (h2 : IsPGroup 2 θ.ker) {i j k l : Fin 3}
    {x y : E} {a b : K} (hx : θ x = tauCoord i j a) (hy : θ y = tauCoord k l b) :
    x * y = y * x := by
  have norm : ∀ (i j : Fin 3) (a : K), ∃ i' j', i' ≤ j' ∧ tauCoord i j a = tauCoord i' j' a :=
    fun i j a => by
      rcases le_total i j with h | h
      · exact ⟨i, j, h, rfl⟩
      · exact ⟨j, i, h, tauCoord_comm i j a⟩
  obtain ⟨i', j', hij, hx'⟩ := norm i j a
  obtain ⟨k', l', hkl, hy'⟩ := norm k l b
  rw [hx'] at hx
  rw [hy'] at hy
  by_cases he : (i', j') = (k', l')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    exact mul_comm_of_tauCoord_same hθ hC hK h2 hx hy
  · exact mul_comm_of_tauCoord_ne hθ hC hK hij hkl he hx hy

omit [Group.IsPerfect E] in
include hθ hC in
theorem mul_comm_of_mem_symGroup (hK : 4 ≤ Nat.card K) (h2 : IsPGroup 2 θ.ker) {x y : E}
    (hx : θ x ∈ symGroup) (hy : θ y ∈ symGroup) : x * y = y * x := by
  set G₀ : Set E := {z | ∃ (i j : Fin 3) (a : K), θ z = tauCoord i j a}
  have hG₀ : G₀.Pairwise Commute := fun z hz w hw _ => by
    obtain ⟨i, j, a, hz⟩ := hz
    obtain ⟨k, l, b, hw⟩ := hw
    exact mul_comm_of_tauCoord hθ hC hK h2 hz hw
  have hle : ∀ z, θ z ∈ symGroup → z ∈ Subgroup.closure G₀ := by
    rintro z ⟨B, hB, hzB⟩
    rw [upperUnipotentSp_eq_prod_tauCoord hB] at hzB
    have hlift : ∀ (i j : Fin 3) (a : K), ∃ w ∈ Subgroup.closure G₀, θ w = tauCoord i j a :=
      fun i j a => by
        obtain ⟨w, hw⟩ := hθ (tauCoord i j a)
        exact ⟨w, Subgroup.subset_closure ⟨i, j, a, hw⟩, hw⟩
    obtain ⟨w₁, hw₁, h₁⟩ := hlift 0 0 (B 0 0)
    obtain ⟨w₂, hw₂, h₂⟩ := hlift 1 1 (B 1 1)
    obtain ⟨w₃, hw₃, h₃⟩ := hlift 2 2 (B 2 2)
    obtain ⟨w₄, hw₄, h₄⟩ := hlift 0 1 (B 0 1)
    obtain ⟨w₅, hw₅, h₅⟩ := hlift 0 2 (B 0 2)
    obtain ⟨w₆, hw₆, h₆⟩ := hlift 1 2 (B 1 2)
    set w := w₁ * w₂ * w₃ * w₄ * w₅ * w₆
    have hw : w ∈ Subgroup.closure G₀ := by
      simp only [w]
      exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem hw₁ hw₂) hw₃) hw₄) hw₅) hw₆
    have hc : w⁻¹ * z ∈ Subgroup.closure G₀ := Subgroup.subset_closure ⟨0, 0, 0, by
      rw [map_mul, map_inv, hzB, tauCoord_zero]
      simp only [w, map_mul, h₁, h₂, h₃, h₄, h₅, h₆, inv_mul_cancel]⟩
    have := mul_mem hw hc
    rwa [mul_inv_cancel_left] at this
  have hcomm : IsMulCommutative (Subgroup.closure G₀) := Subgroup.isMulCommutative_closure hG₀
  have h := hcomm.is_comm.comm (⟨x, hle x hx⟩ : Subgroup.closure G₀) ⟨y, hle y hy⟩
  exact congrArg Subtype.val h

end Cover

end CFSG.LocalAnalysis.ComponentInitial.SymplecticSixCover
