module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutCommon
public import CFSG.RankThree.PartTwo.KFacts.AutPSL
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartTwo.KFacts CFSG.Assembly.LowTwoRank
open Matrix.GeneralLinearGroup (scalar coe_scalar)

@[expose] noncomputable def ringAutEquivAlgEquiv' (K : Type) [Field K] (p : ℕ)
    [Algebra (ZMod p) K] : (K ≃+* K) ≃* (K ≃ₐ[ZMod p] K) where
  toFun σ := AlgEquiv.ofRingEquiv (f := σ) (by
    intro x
    have h : (σ.toRingHom.comp (algebraMap (ZMod p) K) : ZMod p →+* K) =
        algebraMap (ZMod p) K := RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x)
  invFun σ := σ.toRingEquiv
  left_inv σ := by ext x; rfl
  right_inv σ := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

theorem ringEquiv_pow_eq_one {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hcard : Nat.card K = p ^ f) (σ : K ≃+* K) : σ ^ f = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  have hF : Fintype.card K = p ^ f := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have : CharP K p := charP_of_card_eq_prime_pow hF
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  have hc : Nat.card (K ≃+* K) = f := by
    rw [Nat.card_congr (ringAutEquivAlgEquiv' K p).toEquiv, IsGalois.card_aut_eq_finrank]
    have h1 := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
    rw [ZMod.card, hF] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  rw [← hc]
  exact pow_card_eq_one'

theorem standardFieldGraph_pow_eq_one {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hcard : Nat.card K = p ^ f) {r : MulAut (projectiveSL 3 K)}
    (hr : r ∈ standardFieldGraph 3 K) : r ^ (2 * f) = 1 := by
  obtain ⟨-, -, -, hδδ, -, -, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  have hδ : dualAut 3 K ^ 2 = 1 := by rw [pow_two]; exact hδδ
  unfold standardFieldGraph at hr
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨σ, rfl⟩ | rfl
    · rw [mul_comm, pow_mul, ← map_pow, ringEquiv_pow_eq_one hp hcard σ, map_one, one_pow]
    · rw [pow_mul, hδ, one_pow]
  | one => exact one_pow _
  | mul x y hx hy ihx ihy =>
    have hxm : x ∈ standardFieldGraph 3 K := hx
    have hym : y ∈ standardFieldGraph 3 K := hy
    rw [(standardFieldGraph_commute hxm hym).mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem mem_of_pow_coprime {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {α r : G}
    {k n : ℕ} (hα : α ^ 3 ^ k = 1) (hr : r ^ n = 1) (hn : Nat.Coprime 3 n)
    (h : α * r⁻¹ ∈ N) : α ∈ N := by
  have h1 : QuotientGroup.mk' N α = QuotientGroup.mk' N r := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv] using h
  have h2 : (QuotientGroup.mk' N α) ^ 3 ^ k = 1 := by rw [← map_pow, hα, map_one]
  have h3 : (QuotientGroup.mk' N α) ^ n = 1 := by rw [h1, ← map_pow, hr, map_one]
  have h4 : orderOf (QuotientGroup.mk' N α) ∣ Nat.gcd (3 ^ k) n :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  rw [(Nat.Coprime.pow_left k hn).gcd_eq_one] at h4
  have h5 : QuotientGroup.mk' N α = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  exact (QuotientGroup.eq_one_iff α).1 h5

theorem exists_primitive_cube_root (K : Type) [Field K] [Finite K] (h : 3 ∣ Nat.card K - 1) :
    ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 hd
  refine ⟨g, ?_, ?_⟩
  · have := pow_orderOf_eq_one g
    rw [hg] at this
    simpa using congrArg Units.val this
  · intro h1
    have : g = 1 := Units.ext h1
    rw [this, orderOf_one] at hg
    norm_num at hg

theorem not_three_dvd_of_mod_nine {p f c : ℕ} (hc : c = p ^ f)
    (h : c % 9 = 2 ∨ c % 9 = 4 ∨ c % 9 = 5 ∨ c % 9 = 7) : ¬ 3 ∣ f := by
  rintro ⟨g, rfl⟩
  have h1 : c = (p ^ g) ^ 3 := by rw [hc, ← pow_mul, mul_comm]
  have h2 : (p ^ g) ^ 3 % 9 = ((p ^ g % 9) ^ 3) % 9 := Nat.pow_mod _ _ _
  have h3 : p ^ g % 9 < 9 := Nat.mod_lt _ (by norm_num)
  rw [h1, h2] at h
  generalize p ^ g % 9 = x at h h3
  interval_cases x <;> omega

theorem descend_mem_of_pow_three {K : Type} [Field K] [Finite K]
    (hK : Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7)
    (σ : MulAut (Matrix.SpecialLinearGroup (Fin 3) K)) (k : ℕ) (hσ : σ ^ 3 ^ k = 1) :
    descendAut 3 K σ ∈ linearAutGroup 3 K := by
  have := Fintype.ofFinite K
  obtain ⟨p, hp⟩ : ∃ p, CharP K p := CharP.exists K
  have hpp : p.Prime := CharP.char_is_prime K p
  obtain ⟨f, -, hf⟩ := FiniteField.card K p
  have hcard : Nat.card K = p ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have h3 : ¬ 3 ∣ (f : ℕ) := not_three_dvd_of_mod_nine hcard (by omega)
  have hcop : Nat.Coprime 3 (2 * (f : ℕ)) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · omega
    · exact h3 h
  obtain ⟨A, r, hr, hαr⟩ := exists_conjAut_mul_mem_standardFieldGraph (n := 3) le_rfl
    (descendAut 3 K σ)
  have hnorm : (linearAutGroup 3 K).Normal := (stdPinnedPSL_stable (n := 3) (K := K) le_rfl).normal
  refine mem_of_pow_coprime (linearAutGroup 3 K) (r := r) (k := k) (n := 2 * (f : ℕ)) ?_
    (standardFieldGraph_pow_eq_one hpp hcard hr) hcop ?_
  · rw [← map_pow, hσ, map_one]
  · rw [hαr, mul_inv_cancel_right]
    exact conjAut_mem_linearAutGroup A

theorem sylowCentreInn_statedSL (K : Type) [Field K] [Finite K]
    (hK : Nat.card K % 9 = 4 ∨ Nat.card K % 9 = 7) : SylowCentreInn ↥(StatedSL 3 K) := by
  obtain ⟨ω, hω3, hω1⟩ := exists_primitive_cube_root K (by omega)
  set H : Subgroup (GL (Fin 3) K) := StatedSL 3 K with hH
  let e : Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥H := specialLinearGroupEquivStatedSL 3 K
  have hmemH : ∀ s : Matrix.SpecialLinearGroup (Fin 3) K, Matrix.SpecialLinearGroup.toGL s ∈ H :=
    fun s => by
      rw [hH, statedSL_eq_range_toGL]
      exact ⟨s, rfl⟩
  have he : ∀ s : Matrix.SpecialLinearGroup (Fin 3) K,
      ((e s : ↥H) : GL (Fin 3) K) = Matrix.SpecialLinearGroup.toGL s := fun s => rfl
  let ι : MulAut ↥H →* MulAut (projectiveSL 3 K) :=
    (descendAut 3 K).comp (MulAut.congr e.symm).toMonoidHom
  let D : Subgroup (MulAut ↥H) := (linearAutGroup 3 K).comap ι
  have hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  have hperfH : Group.IsPerfect ↥H :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  refine sylowCentreInn_of_family hω3 hω1 H (hmemH _) (hmemH _) D ?_ ?_ ?_ ?_
    (fun e' h => eq_one_of_scalar_perfect hperfH e' h)
  ·
    rintro _ ⟨m, rfl⟩
    obtain ⟨s, rfl⟩ := e.surjective m
    show ι (MulAut.conj (e s)) ∈ linearAutGroup 3 K
    have h1 : MulAut.congr e.symm (MulAut.conj (e s)) = MulAut.conj s := by
      ext x
      simp [MulAut.congr_apply, map_mul, map_inv]
    have h2 : descendAut 3 K (MulAut.conj s) = MulAut.conj (proj 3 K s) := by
      ext x
      obtain ⟨g, rfl⟩ := proj_surjective 3 K x
      rw [descendAut_proj]
      simp [MulAut.conj_apply, map_mul, map_inv]
    have : ι (MulAut.conj (e s)) = MulAut.conj (proj 3 K s) := by
      show descendAut 3 K (MulAut.congr e.symm (MulAut.conj (e s))) = _
      rw [h1, h2]
    rw [this]
    exact innAut_le_linearAutGroup 3 K ⟨proj 3 K s, rfl⟩
  · intro σ k hσ
    exact descend_mem_of_pow_three hK (MulAut.congr e.symm σ) k
      (by rw [← map_pow, hσ, map_one])
  ·
    intro d hd
    have hd' : ι d ∈ linearAutGroup 3 K := hd
    rw [linearAutGroup_eq_range] at hd'
    obtain ⟨A, hA⟩ := hd'
    refine ⟨A, fun m => ?_⟩
    obtain ⟨s, rfl⟩ := e.surjective m
    have h1 : proj 3 K (MulAut.congr e.symm d s) = proj 3 K
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A s) := by
      have := congrArg (fun φ : MulAut (projectiveSL 3 K) => φ (proj 3 K s)) hA
      simp only [ι, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
      rw [conjAut_proj, descendAut_proj] at this
      exact this.symm
    obtain ⟨c, -, hc⟩ := (QuotientGroup.eq.1 h1 : _ ∈ scalars 3 K)
    set u := MulAut.congr e.symm d s with hu
    set v := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A s
      with hv
    have hu' : u = e.symm (d (e s)) := by simp [hu, MulAut.congr_apply]
    have hdu : d (e s) = e u := by rw [hu', MulEquiv.apply_symm_apply]
    have hz : Matrix.SpecialLinearGroup.toGL (u⁻¹ * v) = scalar (Fin 3) c :=
      Units.ext (by rw [coe_scalar]; exact hc)
    have hv' : Matrix.SpecialLinearGroup.toGL v = A * Matrix.SpecialLinearGroup.toGL s * A⁻¹ :=
      CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation 3 K A s
    rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, hv'] at hz
    refine ⟨c⁻¹, ?_⟩
    rw [hdu, he, he, map_inv]
    rw [hz]
    group
  · intro z hz
    obtain ⟨t, rfl⟩ := e.surjective z
    have ht : t ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply e.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.1 hz (e g)
    obtain ⟨r, hr, hrt⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 ht
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    refine ⟨Units.mk0 r hr0, ?_⟩
    rw [he]
    exact Units.ext (by rw [coe_scalar]; exact hrt.symm)

end CFSG.HardMathSupport.Solomon.Coordinator
