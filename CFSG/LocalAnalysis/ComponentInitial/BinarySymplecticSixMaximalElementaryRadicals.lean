module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixBasisTransport
public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianGeneratorRank
import CFSG.GroupTheory.ElemAbelianClosure

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Matrix Module CFSG.Assembly.LowTwoRank SymplecticFlag SymplecticTorusWeyl
open CFSG.LargeEvenClassification.Helpers
open LinearMap (BilinForm)
open scoped Pointwise

section Elementary

variable {G : Type*} [Group G] {E : Subgroup G}

theorem mul_comm_of_isElementaryAbelian (hE : IsElementaryAbelian 2 E) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hE.toIsMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem mul_self_of_isElementaryAbelian (hE : IsElementaryAbelian 2 E) {x : G} (hx : x ∈ E) :
    x * x = 1 := by
  have := hE
  have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) x hx
  rwa [sq] at h

theorem isElementaryAbelian_of_forall (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hsq : ∀ x ∈ E, x * x = 1) : IsElementaryAbelian 2 E :=
  CFSG.IsElementaryAbelian.two_of_forall_mul_self hcomm hsq

theorem isPGroup_of_mul_self (hsq : ∀ x ∈ E, x * x = 1) : IsPGroup 2 E := fun x =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, sq, hsq x x.2, Subgroup.coe_one])⟩

end Elementary

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {b : BilinForm (ZMod 2) V}

theorem finite_bilinIsometryGroup {n : ℕ} {e : Basis (Fin n ⊕ Fin n) (ZMod 2) V}
    (he : IsSymplecticBasis b e) : Finite (bilinIsometryGroup b) :=
  Finite.of_equiv _ (spCoord he).symm.toEquiv

variable [FiniteDimensional (ZMod 2) V]

theorem exists_isSymplecticBasis (hb : b.IsAlt) (hnd : b.Nondegenerate) {n : ℕ}
    (hV : finrank (ZMod 2) V = 2 * n) :
    ∃ e : Basis (Fin n ⊕ Fin n) (ZMod 2) V, IsSymplecticBasis b e := by
  have h0 : IsTotallyIsotropic b ⊥ := fun x hx y _ => by
    rw [Submodule.mem_bot] at hx
    rw [hx, map_zero, LinearMap.zero_apply]
  obtain ⟨e, he, -⟩ := exists_completeIsotropicFlag hb hnd hV h0
  exact ⟨e, he⟩

theorem pointwiseStabilizer_lagrangian (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) {W : Submodule (ZMod 2) V} (hW : IsTotallyIsotropic b W)
    (hd : finrank (ZMod 2) W = 3) :
    IsElementaryAbelian 2 (pointwiseStabilizer b W) ∧ Nat.card (pointwiseStabilizer b W) = 64 ∧
      Subgroup.centralizer (pointwiseStabilizer b W : Set (bilinIsometryGroup b)) =
        pointwiseStabilizer b W ∧
      Subgroup.normalizer (pointwiseStabilizer b W : Set (bilinIsometryGroup b)) =
        subspaceStabilizer b W ∧
      Function.Surjective (restrictSubspace b W) ∧
      (restrictSubspace b W).ker =
        (pointwiseStabilizer b W).subgroupOf (subspaceStabilizer b W) := by
  obtain ⟨e, he, rfl⟩ := exists_basis_lagrangianOf hb hnd (by rw [hV]) hW hd
  exact ⟨isElementaryAbelian_pointwiseStabilizer_lagrangianOf he,
    (card_pointwiseStabilizer_lagrangianOf he).trans (by norm_num),
    centralizer_pointwiseStabilizer_lagrangianOf he, normalizer_pointwiseStabilizer_lagrangianOf he,
    restrictSubspace_surjective he, ker_restrictSubspace _⟩

theorem exists_quotient_mulEquiv (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) {W : Submodule (ZMod 2) V} (hW : IsTotallyIsotropic b W)
    (hd : finrank (ZMod 2) W = 3) :
    ∃ ψ : subspaceStabilizer b W ⧸ (pointwiseStabilizer b W).subgroupOf (subspaceStabilizer b W) ≃*
        LinearMap.GeneralLinearGroup (ZMod 2) W,
      ∀ (g : subspaceStabilizer b W) (w : W),
        (((ψ (QuotientGroup.mk g : subspaceStabilizer b W ⧸
            (pointwiseStabilizer b W).subgroupOf (subspaceStabilizer b W)) :
          LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w : V) =
          (((g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
            V →ₗ[ZMod 2] V) w := by
  obtain ⟨-, -, -, -, hsurj, hker⟩ := pointwiseStabilizer_lagrangian hb hnd hV hW hd
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj), fun g w => rfl⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_conj_sylow {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
    (P : Sylow 2 (bilinIsometryGroup b)) :
    ∃ s : StatedSp 3 (ZMod 2), ∀ x : bilinIsometryGroup b,
      x ∈ P ↔ s⁻¹ * spCoord he x * s ∈ unipotent 3 (ZMod 2) := by
  have : Finite (bilinIsometryGroup b) := finite_bilinIsometryGroup he
  obtain ⟨U, hU⟩ := exists_sylow_unipotent (K := ZMod 2) 2 3
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq (StatedSp 3 (ZMod 2)) U
    (P.mapSurjective (f := (spCoord he).toMonoidHom) (spCoord he).surjective)
  refine ⟨s, fun x => ?_⟩
  have h1 : spCoord he x ∈ (P : Subgroup (bilinIsometryGroup b)).map (spCoord he).toMonoidHom ↔
      x ∈ P :=
    Subgroup.mem_map_iff_mem (f := (spCoord he).toMonoidHom) (spCoord he).injective
  have h2 : MulAut.conj s • (U : Subgroup (StatedSp 3 (ZMod 2))) =
      (P : Subgroup (bilinIsometryGroup b)).map (spCoord he).toMonoidHom :=
    congrArg (fun Q : Sylow 2 (StatedSp 3 (ZMod 2)) => (Q : Subgroup (StatedSp 3 (ZMod 2)))) hs
  rw [← h1, ← h2, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hU, MulAut.smul_def,
    MulAut.conj_inv_apply]

omit [FiniteDimensional (ZMod 2) V] in
theorem sylow_elementary_le {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)
    (P : Sylow 2 (bilinIsometryGroup b)) :
    ∃ h : bilinIsometryGroup b,
      pointwiseStabilizer b ((lagrangianOf e).map ((h : LinearMap.GeneralLinearGroup (ZMod 2) V) :
        V →ₗ[ZMod 2] V)) ≤ P ∧
      ∀ E : Subgroup (bilinIsometryGroup b), E ≤ P → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
        (∀ x ∈ E, x * x = 1) → Nat.card E ≤ 64 ∧
          (Nat.card E = 64 → E = pointwiseStabilizer b ((lagrangianOf e).map
            ((h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V))) := by
  obtain ⟨s, hs⟩ := exists_conj_sylow he P
  obtain ⟨h, rfl⟩ := (spCoord he).surjective s
  have hR : ∀ x, x ∈ pointwiseStabilizer b ((lagrangianOf e).map
      ((h : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)) ↔
        (spCoord he h)⁻¹ * spCoord he x * spCoord he h ∈ (tauSym 3).range := by
    intro x
    rw [← map_conj_pointwiseStabilizer, Subgroup.mem_map_equiv, MulAut.conj_symm_apply,
      mem_pointwiseStabilizer_iff_spCoord he, map_mul, map_mul, map_inv]
  refine ⟨h, fun x hx => (hs x).2 ?_, fun E hEP hcomm hsq => ?_⟩
  · obtain ⟨B, hB⟩ := (hR x).1 hx
    rw [← hB]
    exact tauSym_mem_unipotent B
  obtain ⟨ψ, hψ⟩ : ∃ ψ : bilinIsometryGroup b →* StatedSp 3 (ZMod 2),
      ∀ x, ψ x = (spCoord he h)⁻¹ * spCoord he x * spCoord he h :=
    ⟨(MulAut.conj (spCoord he h)⁻¹).toMonoidHom.comp (spCoord he).toMonoidHom, fun x => by
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply, inv_inv]⟩
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    rw [hψ, hψ] at hxy
    exact (spCoord he).injective (mul_left_cancel (mul_right_cancel hxy))
  have hEU : E.map ψ ≤ unipotent 3 (ZMod 2) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hψ]
    exact (hs x).1 (hEP hx)
  have hcomm' : ∀ x ∈ E.map ψ, ∀ y ∈ E.map ψ, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hsq' : ∀ x ∈ E.map ψ, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hsq x hx, map_one]
  obtain ⟨h64, heq⟩ := card_le_of_le_unipotent hEU hcomm' hsq'
  rw [Subgroup.card_map_of_injective hψinj] at h64 heq
  refine ⟨h64, fun hE64 => ?_⟩
  ext x
  rw [hR x, ← hψ, ← heq hE64, Subgroup.mem_map_iff_mem hψinj]

theorem card_le_of_elementary (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) {E : Subgroup (bilinIsometryGroup b)}
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 64 ∧ (Nat.card E = 64 → ∃ W : Submodule (ZMod 2) V, IsTotallyIsotropic b W ∧
      finrank (ZMod 2) W = 3 ∧ E = pointwiseStabilizer b W) := by
  obtain ⟨e, he⟩ := exists_isSymplecticBasis hb hnd (n := 3) (by rw [hV])
  obtain ⟨P, hEP⟩ := (isPGroup_of_mul_self hsq).exists_le_sylow
  obtain ⟨h, -, hP⟩ := sylow_elementary_le he P
  obtain ⟨h64, heq⟩ := hP E hEP hcomm hsq
  exact ⟨h64, fun hE64 => ⟨_, isTotallyIsotropic_map h (isTotallyIsotropic_lagrangianOf he),
    by rw [finrank_map_eq, finrank_lagrangianOf], heq hE64⟩⟩

theorem existsUnique_elementary_le_sylow (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (P : Sylow 2 (bilinIsometryGroup b)) :
    ∃! E : Subgroup (bilinIsometryGroup b), E ≤ P ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 64 := by
  obtain ⟨e, he⟩ := exists_isSymplecticBasis hb hnd (n := 3) (by rw [hV])
  obtain ⟨h, hRP, hP⟩ := sylow_elementary_le he P
  obtain ⟨e', he', hW'⟩ := exists_basis_lagrangianOf hb hnd (n := 3) (by rw [hV])
    (isTotallyIsotropic_map h (isTotallyIsotropic_lagrangianOf he))
    (by rw [finrank_map_eq, finrank_lagrangianOf])
  refine ⟨_, ⟨hRP, ?_, ?_⟩, fun E ⟨hEP, hEA, hE64⟩ => (hP E hEP
    (fun x hx y hy => mul_comm_of_isElementaryAbelian hEA hx hy)
    (fun x hx => mul_self_of_isElementaryAbelian hEA hx)).2 hE64⟩
  · rw [hW']
    exact isElementaryAbelian_pointwiseStabilizer_lagrangianOf he'
  · rw [hW']
    exact (card_pointwiseStabilizer_lagrangianOf he').trans (by norm_num)

theorem eq_pointwiseStabilizer_of_six_le_generators (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) {D : Subgroup (bilinIsometryGroup b)}
    (hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hD2 : IsPGroup 2 D)
    (hgen : ∀ S : Finset D, Subgroup.closure (S : Set D) = ⊤ → 6 ≤ S.card) :
    ∃ W : Submodule (ZMod 2) V, IsTotallyIsotropic b W ∧ finrank (ZMod 2) W = 3 ∧
      D = pointwiseStabilizer b W ∧ Nat.card D = 64 := by
  obtain ⟨e, he⟩ := exists_isSymplecticBasis hb hnd (n := 3) (by rw [hV])
  have : Finite (bilinIsometryGroup b) := finite_bilinIsometryGroup he
  let : CommGroup D :=
    { (inferInstance : Group D) with mul_comm := fun x y => Subtype.ext (hcomm x x.2 y y.2) }
  obtain ⟨S, hS, hScard⟩ := pGeneratorRank_generators Nat.prime_two hD2
  have h6 : 6 ≤ pGeneratorRank 2 D := by
    rw [← hScard]
    exact hgen S hS
  unfold pGeneratorRank at h6
  rw [commutative_frattini_card_eq_power_kernel Nat.prime_two hD2] at h6
  have hker : 64 ≤ Nat.card (powMonoidHom 2 : D →* D).ker :=
    (show (64 : ℕ) = 2 ^ 6 by norm_num) ▸ Nat.pow_le_of_le_log Nat.card_pos.ne' h6
  set Ω : Subgroup (bilinIsometryGroup b) := (powMonoidHom 2 : D →* D).ker.map D.subtype with hΩ
  have hΩD : Ω ≤ D := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hΩcard : Nat.card Ω = Nat.card (powMonoidHom 2 : D →* D).ker :=
    Subgroup.card_map_of_injective D.subtype_injective
  have hΩcomm : ∀ x ∈ Ω, ∀ y ∈ Ω, x * y = y * x := fun x hx y hy =>
    hcomm x (hΩD hx) y (hΩD hy)
  have hΩsq : ∀ x ∈ Ω, x * x = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have hx2 : x ^ 2 = 1 := hx
    change ((x * x : D) : bilinIsometryGroup b) = 1
    rw [← sq, hx2, Subgroup.coe_one]
  obtain ⟨h64, heq⟩ := card_le_of_elementary hb hnd hV hΩcomm hΩsq
  have hΩ64 : Nat.card Ω = 64 := by
    rw [hΩcard] at h64 ⊢
    omega
  obtain ⟨W, hW, hWd, hΩW⟩ := heq hΩ64
  have hcent := (pointwiseStabilizer_lagrangian hb hnd hV hW hWd).2.2.1
  have hDR : D ≤ pointwiseStabilizer b W := by
    intro d hd
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, ← hΩW] at hy
    exact hcomm y (hΩD hy) d hd
  have hDeq : D = pointwiseStabilizer b W := le_antisymm hDR (hΩW ▸ hΩD)
  refine ⟨W, hW, hWd, hDeq, ?_⟩
  rw [hDeq, ← hΩW, hΩ64]

omit [FiniteDimensional (ZMod 2) V] in
theorem apply_eq_of_range_sub_one_le (hb : b.IsAlt) (hnd : b.Nondegenerate)
    {f : V →ₗ[ZMod 2] V} (hiso : ∀ x y, b (f x) (f y) = b x y) (hff : ∀ v, f (f v) = v)
    {W : Submodule (ZMod 2) V} (hW : IsTotallyIsotropic b W) (hfW : LinearMap.range (f - 1) ≤ W)
    {w : V} (hw : w ∈ W) : f w = w := by
  have h1 : ∀ v, b ((f - 1) v) w = 0 := fun v => hW _ (hfW ⟨v, rfl⟩) w hw
  have h2 : ∀ v, b ((f - 1) w) v = 0 := by
    intro v
    have hiso' : b (f w) v = b w (f v) := by
      conv_lhs => rw [← hff v]
      exact hiso w (f v)
    have h3 : b ((f - 1) w) v = b w ((f - 1) v) := by
      rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.one_apply, Module.End.one_apply,
        LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hiso']
    rw [h3]
    exact hb.isRefl _ _ (h1 v)
  have h3 := hnd.1 _ h2
  rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h3

theorem exists_lagrangian_mem_pointwiseStabilizer (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (x : bilinIsometryGroup b) (hx : x ^ 2 = 1) :
    ∃ W : Submodule (ZMod 2) V, IsTotallyIsotropic b W ∧ finrank (ZMod 2) W = 3 ∧
      x ∈ pointwiseStabilizer b W := by
  have ha2 : (x : LinearMap.GeneralLinearGroup (ZMod 2) V) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]
  obtain ⟨horth, hle, -⟩ :=
    binary_symplectic_involution_fixed_space_pointwise_stabilizer hnd x.2 ha2 rfl
  have hI : IsTotallyIsotropic b (LinearMap.range
      (((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) - 1)) := by
    intro u hu u' hu'
    have hu0 : u ∈ b.orthogonal (LinearMap.ker
        (((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) - 1)) := by
      rw [horth]
      exact hu
    have hu'0 : u' ∈ b.orthogonal (LinearMap.ker
        (((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) - 1)) := by
      rw [horth]
      exact hu'
    exact hu'0 u (hle hu0)
  obtain ⟨e, he, hIe⟩ := exists_completeIsotropicFlag hb hnd (r := 3) (by rw [hV]) hI
  refine ⟨lagrangianOf e, isTotallyIsotropic_lagrangianOf he, finrank_lagrangianOf,
    fun w hw => ?_⟩
  have hIW : LinearMap.range (((x : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) - 1) ≤ lagrangianOf e := by
    rw [hIe, lagrangianOf, Set.range_comp]
    exact Submodule.span_mono (Set.image_mono (Set.image_subset_range _ _))
  have hff : ∀ v, ((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V)
      (((x : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v) = v := fun v => by
    have h := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) V =>
      (g : V →ₗ[ZMod 2] V) v) ha2
    simpa [sq] using h
  exact apply_eq_of_range_sub_one_le hb hnd x.2 hff (isTotallyIsotropic_lagrangianOf he) hIW hw

theorem exists_conj_pointwiseStabilizer (hb : b.IsAlt) (hnd : b.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) {W W' : Submodule (ZMod 2) V} (hW : IsTotallyIsotropic b W)
    (hd : finrank (ZMod 2) W = 3) (hW' : IsTotallyIsotropic b W')
    (hd' : finrank (ZMod 2) W' = 3) :
    ∃ g : bilinIsometryGroup b,
      W.map ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) = W' ∧
        (pointwiseStabilizer b W).map (MulAut.conj g).toMonoidHom = pointwiseStabilizer b W' := by
  obtain ⟨e, he, rfl⟩ := exists_basis_lagrangianOf hb hnd (n := 3) (by rw [hV]) hW hd
  obtain ⟨e', he', rfl⟩ := exists_basis_lagrangianOf hb hnd (n := 3) (by rw [hV]) hW' hd'
  set φ := e.isometryEquivOfToMatrixEq e' (he.trans he'.symm)
  let g : bilinIsometryGroup b :=
    ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm φ.toLinearEquiv,
      fun x y => φ.map_app y x⟩
  have hgW : (lagrangianOf e).map ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
      V →ₗ[ZMod 2] V) = lagrangianOf e' := by
    rw [lagrangianOf, lagrangianOf, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact e.isometryEquivOfToMatrixEq_apply_basis e' _ (Sum.inl j)
  exact ⟨g, hgW, by rw [map_conj_pointwiseStabilizer, hgW]⟩

theorem binary_symplectic_six_maximal_elementary_and_involution_radicals (hb : b.IsAlt)
    (hnd : b.Nondegenerate) (hV : finrank (ZMod 2) V = 6) :
    (∀ W : Submodule (ZMod 2) V, IsTotallyIsotropic b W → finrank (ZMod 2) W = 3 →
      IsElementaryAbelian 2 (pointwiseStabilizer b W) ∧
        Nat.card (pointwiseStabilizer b W) = 64 ∧
        Subgroup.centralizer (pointwiseStabilizer b W : Set (bilinIsometryGroup b)) =
          pointwiseStabilizer b W ∧
        Subgroup.normalizer (pointwiseStabilizer b W : Set (bilinIsometryGroup b)) =
          subspaceStabilizer b W ∧
        Function.Surjective (restrictSubspace b W) ∧
        (restrictSubspace b W).ker =
          (pointwiseStabilizer b W).subgroupOf (subspaceStabilizer b W) ∧
        ∃ ψ : subspaceStabilizer b W ⧸ (pointwiseStabilizer b W).subgroupOf
            (subspaceStabilizer b W) ≃* LinearMap.GeneralLinearGroup (ZMod 2) W,
          ∀ (g : subspaceStabilizer b W) (w : W),
            (((ψ (QuotientGroup.mk g : subspaceStabilizer b W ⧸
                (pointwiseStabilizer b W).subgroupOf (subspaceStabilizer b W)) :
              LinearMap.GeneralLinearGroup (ZMod 2) W) : W →ₗ[ZMod 2] W) w : V) =
              (((g : bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
                V →ₗ[ZMod 2] V) w) ∧
    (∀ e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V, IsSymplecticBasis b e →
      (∀ g : bilinIsometryGroup b, g ∈ pointwiseStabilizer b (lagrangianOf e) ↔
        ∃ B : Matrix (Fin 3) (Fin 3) (ZMod 2), Bᵀ = B ∧
          LinearMap.toMatrix e e ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) :
            V →ₗ[ZMod 2] V) = fromBlocks 1 B 0 1) ∧
      ∀ (g : subspaceStabilizer b (lagrangianOf e)) (r : bilinIsometryGroup b)
        (B : Matrix (Fin 3) (Fin 3) (ZMod 2)), Bᵀ = B →
        LinearMap.toMatrix e e ((r : LinearMap.GeneralLinearGroup (ZMod 2) V) :
          V →ₗ[ZMod 2] V) = fromBlocks 1 B 0 1 →
        LinearMap.toMatrix e e
            ((((g : bilinIsometryGroup b) * r * (g : bilinIsometryGroup b)⁻¹ :
              bilinIsometryGroup b) : LinearMap.GeneralLinearGroup (ZMod 2) V) :
                V →ₗ[ZMod 2] V) =
          fromBlocks 1 (LinearMap.toMatrix (lagrangianBasis e) (lagrangianBasis e)
              ((restrictSubspace b (lagrangianOf e) g :
                LinearMap.GeneralLinearGroup (ZMod 2) (lagrangianOf e)) :
                  lagrangianOf e →ₗ[ZMod 2] lagrangianOf e) * B *
            (LinearMap.toMatrix (lagrangianBasis e) (lagrangianBasis e)
              ((restrictSubspace b (lagrangianOf e) g :
                LinearMap.GeneralLinearGroup (ZMod 2) (lagrangianOf e)) :
                  lagrangianOf e →ₗ[ZMod 2] lagrangianOf e))ᵀ) 0 1) ∧
    (∀ E : Subgroup (bilinIsometryGroup b), IsElementaryAbelian 2 E →
      Nat.card E ≤ 64 ∧ (Nat.card E = 64 → ∃ W : Submodule (ZMod 2) V,
        IsTotallyIsotropic b W ∧ finrank (ZMod 2) W = 3 ∧ E = pointwiseStabilizer b W)) ∧
    (∀ P : Sylow 2 (bilinIsometryGroup b), ∃! E : Subgroup (bilinIsometryGroup b),
      E ≤ P ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 64) ∧
    (∀ D : Subgroup (bilinIsometryGroup b), (∀ x ∈ D, ∀ y ∈ D, x * y = y * x) →
      IsPGroup 2 D → (∀ S : Finset D, Subgroup.closure (S : Set D) = ⊤ → 6 ≤ S.card) →
      ∃ W : Submodule (ZMod 2) V, IsTotallyIsotropic b W ∧ finrank (ZMod 2) W = 3 ∧
        D = pointwiseStabilizer b W ∧ Nat.card D = 64) ∧
    (∀ x : bilinIsometryGroup b, x ^ 2 = 1 → ∃ W : Submodule (ZMod 2) V,
      IsTotallyIsotropic b W ∧ finrank (ZMod 2) W = 3 ∧ x ∈ pointwiseStabilizer b W) ∧
    (∀ W W' : Submodule (ZMod 2) V, IsTotallyIsotropic b W → finrank (ZMod 2) W = 3 →
      IsTotallyIsotropic b W' → finrank (ZMod 2) W' = 3 →
      ∃ g : bilinIsometryGroup b,
        W.map ((g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) = W' ∧
          (pointwiseStabilizer b W).map (MulAut.conj g).toMonoidHom =
            pointwiseStabilizer b W') := by
  refine ⟨fun W hW hd => ?_, fun e he => ⟨mem_pointwiseStabilizer_iff_toMatrix he,
    fun g r B hB hr => spMatrixOf_spCoord_conj he g hr hB⟩,
    fun E hE => card_le_of_elementary hb hnd hV
      (fun x hx y hy => mul_comm_of_isElementaryAbelian hE hx hy)
      (fun x hx => mul_self_of_isElementaryAbelian hE hx),
    existsUnique_elementary_le_sylow hb hnd hV,
    fun D hcomm hD2 hgen => eq_pointwiseStabilizer_of_six_le_generators hb hnd hV hcomm hD2 hgen,
    exists_lagrangian_mem_pointwiseStabilizer hb hnd hV,
    fun W W' hW hd hW' hd' => exists_conj_pointwiseStabilizer hb hnd hV hW hd hW' hd'⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pointwiseStabilizer_lagrangian hb hnd hV hW hd
  exact ⟨h1, h2, h3, h4, h5, h6, exists_quotient_mulEquiv hb hnd hV hW hd⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
