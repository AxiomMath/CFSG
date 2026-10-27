module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ChainEmbedding
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.DualPieceScalar
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open Module

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]

theorem det_eq_pow_of_forall {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (x : Module.End K N) (a : K) (hx : ∀ m, x m = a • m) :
    LinearMap.det x = a ^ finrank K N := by
  have : x = a • LinearMap.id := LinearMap.ext fun m => by simp [hx]
  rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]

theorem det_eq_of_isoStab [FiniteDimensional K V] (hσ : Function.Surjective σ)
    {B : V →ₛₗ[σ] V →ₗ[K] K} (hB : B.SeparatingLeft) {P : Submodule K V}
    (hP : P ≤ P.orthogonalBilin B) (g : isoStab B P) (μ : K)
    (hμ : ∀ v ∈ P, ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) v = μ • v) :
    LinearMap.det ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      μ ^ finrank K P * LinearMap.det (perpEnd g) * ((σ μ)⁻¹) ^ finrank K P := by
  set e : Module.End K V := ((g : LinearMap.GeneralLinearGroup K V) : Module.End K V) with he
  set Q := P.orthogonalBilin B with hQ
  have he1 : Q ≤ Q.comap e := fun v hv => apply_mem_orthogonalBilin g.2 hv
  have h1 := LinearMap.det_eq_det_mul_det Q e he1
  have he2 : P.comap Q.subtype ≤ (P.comap Q.subtype).comap (e.restrict he1) := by
    intro x hx
    have := (mem_isoStab_mem g.2 (x : V)).mpr hx
    exact this
  have h2 := LinearMap.det_eq_det_mul_det (P.comap Q.subtype) (e.restrict he1) he2
  have hfP : finrank K (P.comap Q.subtype) = finrank K P :=
    (Submodule.comapSubtypeEquivOfLe hP).finrank_eq
  have h3 : LinearMap.det ((e.restrict he1).restrict he2) = μ ^ finrank K P := by
    rw [← hfP]
    refine det_eq_pow_of_forall _ μ fun x => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact hμ _ x.2
  have h4 : LinearMap.det (Q.mapQ Q e he1) = ((σ μ)⁻¹) ^ finrank K P := by
    have hfQ : finrank K (V ⧸ Q) = finrank K P := by
      have a1 := Submodule.finrank_quotient_add_finrank Q
      have a2 : finrank K Q = finrank K V - finrank K P := finrank_orthogonalBilin_eq hσ hB P
      have a3 : finrank K P ≤ finrank K V := Submodule.finrank_le P
      omega
    rw [← hfQ]
    refine det_eq_pow_of_forall _ _ fun q => ?_
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.mapQ_apply]
      show Submodule.Quotient.mk (e x) = (σ μ)⁻¹ • Submodule.Quotient.mk x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      have hF'inv : ∀ v ∈ P,
          ((g⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v ∈ P := by
        intro v hv
        have := (mem_isoStab_mem (inv_mem g.2) v).mpr hv
        exact this
      exact dual_piece_scalar (B := B) (g : LinearMap.GeneralLinearGroup K V) (mem_isoStab_iso g.2)
        (F := ⊥) (F' := P) hF'inv μ (fun v hv => (Submodule.mem_bot K).2 (sub_eq_zero.2 (hμ v hv))) x
        (by
          rw [Submodule.mem_orthogonalBilin]
          intro y hy
          rw [Submodule.mem_bot] at hy
          simp [hy])
  have h5 : (Submodule.mapQ (P.comap Q.subtype) (P.comap Q.subtype) (e.restrict he1) he2) =
      perpEnd g := rfl
  rw [h1, h2, h3, h4, h5]

theorem units_pow_three_of_card_four (hK : Nat.card K = 4) (x : Kˣ) : x ^ 3 = 1 := by
  have hKu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  rw [← hKu]
  exact pow_card_eq_one'

theorem units_eq_one_of_det {μ : Kˣ} (h3 : μ ^ 3 = 1) (hσ : ∀ c : K, σ c = c ^ 2)
    (h : (μ : K) ^ 2 * 1 * ((σ μ)⁻¹) ^ 2 = 1) : μ = 1 := by
  rw [hσ, mul_one] at h
  have h' : μ ^ 2 * ((μ ^ 2)⁻¹) ^ 2 = 1 := by
    apply Units.ext
    simpa using h
  have h2 : μ ^ 2 = 1 := by
    have : (μ ^ 2)⁻¹ = 1 := by
      rw [pow_two ((μ ^ 2)⁻¹)] at h'
      simpa [mul_assoc] using h'
    simpa using this
  have : μ ^ 3 = μ * μ ^ 2 := by rw [pow_succ']
  rw [h2, mul_one, h3] at this
  exact this.symm

section Chain

variable [CharP K 2] [FiniteDimensional K V] {B : V →ₛₗ[σ] V →ₗ[K] K}
  {W : ℕ → Submodule K V} {U : Subgroup (LinearMap.GeneralLinearGroup K V)}

omit [CharP K 2] [FiniteDimensional K V] in
theorem chainHom_snd_eq_perpEnd {s : ℕ} (h : ChainStabData B s W U) (hW0 : W 0 = ⊥)
    (hlt : ∀ j, 1 ≤ j → j ≤ s → W (j - 1) < W j) (hs : 1 ≤ s) (u : U) :
    ((h.chainHom hW0 hlt hs u).2 : Module.End K (perpQuot B (W s))) =
      perpEnd (Subgroup.inclusion (h.le_isoStab hs) u) := by
  refine LinearMap.ext fun q => ?_
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    have hy : ((⟨((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) x,
        apply_mem_orthogonalBilin (h.mem_isoStab hs u.2) x.2⟩ : (W s).orthogonalBilin B) : V) =
        ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) x := rfl
    rw [h.chainHom_snd_spec hW0 hlt hs u x _ hy]
    exact (perpEnd_mk (Subgroup.inclusion (h.le_isoStab hs) u) x _ hy).symm

omit [CharP K 2] [FiniteDimensional K V] in
theorem chainHom_fst_eq_scalOf {s : ℕ} (h : ChainStabData B s W U) (hW0 : W 0 = ⊥)
    (hlt : ∀ j, 1 ≤ j → j ≤ s → W (j - 1) < W j) (hs : 1 ≤ s) (u : U) (i : Fin s) :
    (((h.chainHom hW0 hlt hs u).1 i : Kˣ) : K) = h.scalOf u i :=
  (h.eq_scalOf hlt u i (h.chainHom_fst_spec hW0 hlt hs u i)).symm

omit [CharP K 2] in
theorem det_chainHom_one (hσ : Function.Surjective σ) (hB : B.SeparatingLeft)
    (h : ChainStabData B 1 W U) (hW0 : W 0 = ⊥) (hlt : ∀ j, 1 ≤ j → j ≤ 1 → W (j - 1) < W j)
    (hiso : W 1 ≤ (W 1).orthogonalBilin B) (u : U) :
    LinearMap.det ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) =
      (((h.chainHom hW0 hlt le_rfl u).1 0 : Kˣ) : K) ^ finrank K (W 1) *
        LinearMap.det ((h.chainHom hW0 hlt le_rfl u).2 : Module.End K (perpQuot B (W 1))) *
        ((σ (((h.chainHom hW0 hlt le_rfl u).1 0 : Kˣ) : K))⁻¹) ^ finrank K (W 1) := by
  rw [chainHom_snd_eq_perpEnd h hW0 hlt le_rfl u]
  have := det_eq_of_isoStab hσ hB hiso (Subgroup.inclusion (h.le_isoStab le_rfl) u)
    (((h.chainHom hW0 hlt le_rfl u).1 0 : Kˣ) : K) (fun v hv => by
      have h1 : ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) v -
          (((h.chainHom hW0 hlt le_rfl u).1 0 : Kˣ) : K) • v ∈ W 0 :=
        h.chainHom_fst_spec hW0 hlt le_rfl u 0 v hv
      rw [hW0, Submodule.mem_bot] at h1
      exact sub_eq_zero.1 h1)
  exact this

theorem exists_det_ne_one_chain_one (hK : Nat.card K = 4) (hσ : Function.Surjective σ)
    (hB : B.SeparatingLeft) (hσc : ∀ c : K, σ c = c ^ 2)
    (h : ChainStabData B 1 W U) (hW0 : W 0 = ⊥) (hlt : ∀ j, 1 ≤ j → j ≤ 1 → W (j - 1) < W j)
    (hiso : W 1 ≤ (W 1).orthogonalBilin B) (ha : finrank K (W 1) = 2)
    (hM : finrank K (perpQuot B (W 1)) ≤ 2) (hcard : 27 ∣ Nat.card U) :
    ∃ u ∈ U, LinearMap.det ((u : LinearMap.GeneralLinearGroup K V) : Module.End K V) ≠ 1 := by
  by_contra hall
  push Not at hall
  set θ := h.chainHom hW0 hlt le_rfl with hθ
  have hinj : Function.Injective ((MonoidHom.snd _ _).comp θ) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h2 : (θ u).2 = 1 := hu
    have hdet := det_chainHom_one hσ hB h hW0 hlt hiso u
    rw [hall u u.2, ← hθ, h2, ha] at hdet
    have hμ : (θ u).1 0 = 1 := by
      refine units_eq_one_of_det (units_pow_three_of_card_four hK _) hσc ?_
      have := hdet.symm
      simpa using this
    apply h.chainHom_injective hW0 hlt le_rfl
    refine Prod.ext ?_ ?_
    · funext i
      have : i = 0 := Subsingleton.elim _ _
      subst this
      simpa using hμ
    · simpa using h2
  have hH := three_subgroup_generalLinearGroup hK rfl hM
    ((MonoidHom.snd _ _).comp θ).range (by
      rintro _ ⟨u, rfl⟩
      obtain ⟨k, hk⟩ := h.three u u.2
      refine ⟨k, ?_⟩
      have : u ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
      have h2 : θ (u ^ 3 ^ k) = 1 := by rw [this, map_one]
      rw [map_pow] at h2
      have := congrArg Prod.snd h2
      simpa using this)
  have h1 : Nat.card U ∣ Nat.card ((MonoidHom.snd _ _).comp θ).range :=
    Subgroup.card_dvd_of_injective ((MonoidHom.snd _ _).comp θ).rangeRestrict
      (by
        intro a b hab
        exact hinj (congrArg Subtype.val hab))
  have h2 : 27 ∣ 3 ^ 2 := by
    refine hcard.trans (h1.trans (hH.1.trans ?_))
    exact pow_dvd_pow 3 hM
  omega

end Chain

end CFSG.HardMathSupport.Curtis.UnitaryLevi
