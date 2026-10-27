module

public import CFSG.ClassicalGroups.Orthogonal.SiegelSLAxis
import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Dim4

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelSL

open CFSG.ClassicalGroups.Orthogonal.SiegelRT1 CFSG.HardMathSupport.Kantor79 CFSG.CGT.Timmesfeld75
open CFSG.CGT.T75E QuadraticMap Module Matrix
open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {m' : ℕ} {Qf : QuadraticForm K V} {ρ : SL(m' + 2, K) →* (V ≃ₗ[K] V)}

omit [Finite K] [CharP K 2] in
private theorem single_zero_ne_zero :
    (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) ≠ 0 := by
  intro h
  simpa using congrFun h 0

omit [Finite K] [FiniteDimensional K V] [CharP K 2] in
private theorem ne_zero_of_linearIndependent_pair {c d : Fin (m' + 2) → K}
    (hli : LinearIndependent K ![c, d]) : c ≠ 0 ∧ d ≠ 0 ∧ ∀ μ : K, d ≠ μ • c := by
  rw [LinearIndependent.pair_iff] at hli
  refine ⟨fun h => one_ne_zero (hli 1 0 (by simp [h])).1,
    fun h => one_ne_zero (hli 0 1 (by simp [h])).2, fun μ h => ?_⟩
  have h1 := (hli μ (-1) (by rw [h]; module)).2
  exact one_ne_zero (neg_eq_zero.mp h1)

omit [Finite K] [FiniteDimensional K V] in
private theorem SLSetting.axisInf_center_le_movedSpace (hs : SLSetting Qf ρ)
    {c a : Fin (m' + 2) → K} (h : a ⬝ᵥ c = 0) (hc : c ≠ 0) (ha : a ≠ 0) :
    axisInf ((tvCenterSL c).map ρ) ≤ movedSpace (ρ (tvSL c a h)) :=
  axisInf_le ⟨_, Subgroup.mem_map_of_mem ρ ⟨a, h, rfl⟩,
    fun h1 => not_isLongRootElement_one hs.nondeg (h1 ▸ hs.siegel c a h hc ha), rfl⟩

theorem SLSetting.le_finrank_commutatorSpace_of_isStar (hs : SLSetting Qf ρ)
    (hst : IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ))
    {c : Fin (m' + 2) → K} (hc : c ≠ 0) :
    m' + 2 ≤ finrank K (commutatorSpace ((tvCenterSL c).map ρ)) := by
  have h3 := hs.three_le
  have hstc : IsStar ((tvCenterSL c).map ρ) :=
    (isStar_map_center_iff ρ (by omega) single_zero_ne_zero hc).mp hst
  obtain ⟨hP1, hP⟩ := hs.axisInf_center_of_isStar hc hstc
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hcard : Nat.card K < Nat.card ((tvCenterSL c).map ρ) := by
    rw [hs.card_map_center hc]
    calc Nat.card K = Nat.card K ^ 1 := (pow_one _).symm
      _ < Nat.card K ^ (m' + 2 - 1) := Nat.pow_lt_pow_right hq (by omega)
  obtain ⟨A₁, hA₁, -⟩ := (hs.isSiegelGroup_center c).exists_ne_axes hs.nondeg hcard
  have hle := (hs.isSiegelGroup_center c).card_le_of_star hs.nondeg hP1 hP ⟨A₁, hA₁⟩
  rw [hs.card_map_center hc] at hle
  have := (Nat.pow_le_pow_iff_right hq).mp hle
  omega

theorem SLSetting.two_mul_le_finrank_of_isStar (hs : SLSetting Qf ρ)
    (hst : IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ)) :
    2 * (m' + 2) ≤ finrank K V := by
  have h1 := hs.le_finrank_commutatorSpace_of_isStar hst single_zero_ne_zero
  have hsing := (hs.isSiegelGroup_center (Pi.single (0 : Fin (m' + 2)) (1 : K))
    ).qf_eq_zero_of_mem_commutatorSpace hs.nondeg
  have h2 := two_mul_finrank_le_of_totallySingular hs.nondeg hsing
  omega

omit [Finite K] in
theorem SLSetting.axisInf_inf_eq_bot_of_isStar (hs : SLSetting Qf ρ)
    {c d : Fin (m' + 2) → K} (hli : LinearIndependent K ![c, d]) :
    axisInf ((tvCenterSL c).map ρ) ⊓ axisInf ((tvCenterSL d).map ρ) = ⊥ := by
  obtain ⟨hc, hd, hdc⟩ := ne_zero_of_linearIndependent_pair hli
  obtain ⟨β, hβc, hβd⟩ := exists_dot_of_not_smul hdc
  obtain ⟨γ, hγ, hγc, hγd⟩ := exists_ne_zero_dot_eq_zero_pair hs.three_le c d
  have hβ : β ≠ 0 := fun h => by
    rw [h, zero_dotProduct] at hβd
    exact zero_ne_one hβd
  obtain ⟨-, hinf, -⟩ := hs.not_commute_of_dot hβc hγd hγc (by rw [hβd]; exact one_ne_zero) hc hγ
  exact eq_bot_iff.mpr ((inf_le_inf (hs.axisInf_center_le_movedSpace hβc hc hβ)
    (hs.axisInf_center_le_movedSpace hγd hd hγ)).trans hinf.le)

omit [Finite K] in
theorem SLSetting.polar_eq_zero_of_isStar (hs : SLSetting Qf ρ)
    {c d : Fin (m' + 2) → K} (hli : LinearIndependent K ![c, d]) {x y : V}
    (hx : x ∈ axisInf ((tvCenterSL c).map ρ)) (hy : y ∈ axisInf ((tvCenterSL d).map ρ)) :
    polar Qf x y = 0 := by
  obtain ⟨hc, hd, -⟩ := ne_zero_of_linearIndependent_pair hli
  obtain ⟨γ, hγ, hγc, hγd⟩ := exists_ne_zero_dot_eq_zero_pair hs.three_le c d
  have hsing := (hs.isSiegelGroup_axis γ).qf_eq_zero_of_mem_commutatorSpace hs.nondeg
  have hle : ∀ {e : Fin (m' + 2) → K}, e ≠ 0 → (h : γ ⬝ᵥ e = 0) →
      axisInf ((tvCenterSL e).map ρ) ≤ commutatorSpace ((tvAxisSL γ).map ρ) := fun {e} he h =>
    (hs.axisInf_center_le_movedSpace h he hγ).trans
      (movedSpace_le_commutatorSpace (Subgroup.mem_map_of_mem ρ ⟨e, h, rfl⟩))
  exact polar_eq_zero_of_totallySingular hsing (hle hc hγc hx) (hle hd hγd hy)

omit [Finite K] in
private theorem apply_eq_self_of_involution_of_map_eq {u : V ≃ₗ[K] V} (hu : u * u = 1)
    {P : Submodule K V} (hP : finrank K P = 1) (hmap : P.map (u : V →ₗ[K] V) = P) :
    ∀ v ∈ P, u v = v := by
  obtain ⟨p, hp0, rfl⟩ := exists_ne_zero_span_eq_of_finrank_eq_one hP
  have hup : u p ∈ Submodule.span K {p} := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self p)
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hup
  have hu2 : u (u p) = p := by simpa using congrArg (fun g : V ≃ₗ[K] V => g p) hu
  have hss : s * s = 1 := by
    have h1 : (s * s) • p = (1 : K) • p := by
      calc (s * s) • p = s • (s • p) := mul_smul _ _ _
        _ = s • u p := by rw [hs]
        _ = u (s • p) := (map_smul u s p).symm
        _ = u (u p) := by rw [hs]
        _ = (1 : K) • p := by rw [hu2, one_smul]
    exact smul_left_injective K hp0 h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs1 : s = 1 := by
    have h3 : (s - 1) * (s - 1) = 0 := by linear_combination hss - s * h2 + h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  intro v hv
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, ← hs, hs1, one_smul]

theorem SLSetting.apply_eq_self_of_mulVec_eq (hs : SLSetting Qf ρ)
    (hst : IsStar ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ))
    {g : SL(m' + 2, K)}
    (hg : (g : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ Pi.single 0 1 =
      (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K))
    {v : V} (hv : v ∈ axisInf ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ)) :
    ρ g v = v := by
  obtain ⟨hP1, -⟩ := hs.axisInf_center_of_isStar single_zero_ne_zero hst
  let H : Subgroup SL(m' + 2, K) :=
    { carrier := {x | ∀ w ∈ axisInf ((tvCenterSL (Pi.single (0 : Fin (m' + 2)) (1 : K))).map ρ),
        ρ x w = w}
      one_mem' := fun w _ => by simp
      mul_mem' := fun {a b} ha hb w hw => by rw [map_mul, LinearEquiv.mul_apply, hb w hw, ha w hw]
      inv_mem' := fun {a} ha w hw => by
        calc ρ a⁻¹ w = (ρ a)⁻¹ (ρ a w) := by rw [map_inv, ha w hw]
          _ = w := by simp }
  have hH : ∀ t : SL(m' + 2, K), t * t = 1 →
      (t : Matrix (Fin (m' + 2)) (Fin (m' + 2)) K) *ᵥ Pi.single 0 1 =
        (Pi.single (0 : Fin (m' + 2)) (1 : K) : Fin (m' + 2) → K) → t ∈ H := by
    intro t htt hte
    have hmap := axisInf_map_center_mulVec ρ t (Pi.single (0 : Fin (m' + 2)) (1 : K))
    rw [hte] at hmap
    exact apply_eq_self_of_involution_of_map_eq (by rw [← map_mul, htt, map_one]) hP1 hmap.symm
  exact mem_of_forall_involution_fix (by have := hs.three_le; omega) H hH hg v hv

end CFSG.ClassicalGroups.Orthogonal.SiegelSL
