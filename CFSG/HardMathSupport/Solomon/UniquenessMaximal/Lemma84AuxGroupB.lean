module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.LocalAnalysis.GLTheoremB.Defs

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem exists_sylow_invariant {Y : Type*} [Group Y] [Finite Y] {Γ : Type*} [Group Γ] [Finite Γ]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hΓ : IsPGroup p Γ) (ρ : Γ →* MulAut Y)
    (K : Subgroup Y) (hK : ∀ γ, K.map (ρ γ).toMonoidHom = K) (hcop : ¬ p ∣ Nat.card K) :
    ∃ S : Subgroup Y, S ≤ K ∧ IsPGroup q S ∧
      (∀ n : ℕ, q ^ n ∣ Nat.card K → q ^ n ∣ Nat.card S) ∧
      ∀ γ, S.map (ρ γ).toMonoidHom = S := by
  classical
  have hmem : ∀ γ x, x ∈ K → ρ γ x ∈ K := fun γ x hx => by
    rw [← hK γ]; exact ⟨x, hx, rfl⟩
  have hinv : ∀ γ x, ρ γ⁻¹ (ρ γ x) = x := fun γ x => by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have hinv' : ∀ γ x, ρ γ (ρ γ⁻¹ x) = x := fun γ x => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  let φ : Γ →* MulAut K :=
    { toFun := fun γ =>
        { toFun := fun x => ⟨ρ γ x, hmem γ x x.2⟩
          invFun := fun x => ⟨ρ γ⁻¹ x, hmem γ⁻¹ x x.2⟩
          left_inv := fun x => Subtype.ext (hinv γ x)
          right_inv := fun x => Subtype.ext (hinv' γ x)
          map_mul' := fun x y => Subtype.ext (by simp) }
      map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
      map_mul' := fun a b => MulEquiv.ext fun x => Subtype.ext (by simp) }
  have hφ : ∀ γ (x : K), ((φ γ x : K) : Y) = ρ γ x := fun _ _ => rfl
  let _ : MulDistribMulAction Γ K := MulDistribMulAction.compHom K φ
  let _ : MulAction Γ (Sylow q K) := Sylow.pointwiseMulAction
  have hcard : ¬ p ∣ Nat.card (Sylow q K) := by
    intro h
    obtain ⟨Q₁⟩ : Nonempty (Sylow q K) := inferInstance
    exact hcop (h.trans (Q₁.card_dvd_index.trans (Q₁ : Subgroup K).index_dvd_card))
  obtain ⟨Q₀, hQ₀⟩ := hΓ.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q K) hcard
  have hle : ∀ γ, ((Q₀ : Subgroup K).map K.subtype).map (ρ γ).toMonoidHom ≤
      (Q₀ : Subgroup K).map K.subtype := by
    intro γ
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hfix : γ • Q₀ = Q₀ := MulAction.mem_fixedPoints.mp hQ₀ γ
    have hm : γ • y ∈ (Q₀ : Subgroup K) := by
      have h := Subgroup.smul_mem_pointwise_smul y γ (Q₀ : Subgroup K) hy
      rwa [← Sylow.pointwise_smul_def, hfix] at h
    exact ⟨_, hm, (hφ γ y)⟩
  refine ⟨(Q₀ : Subgroup K).map K.subtype, Subgroup.map_subtype_le _, Q₀.isPGroup'.map _,
    fun n hn => ?_, fun γ => le_antisymm (hle γ) ?_⟩
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective K)]
    exact Q₀.pow_dvd_card_of_pow_dvd_card hn
  · intro x hx
    have h1 := hle γ⁻¹ ⟨x, hx, rfl⟩
    exact ⟨_, h1, hinv' γ x⟩

theorem card_le_of_faithful {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hKp : ¬ p ∣ Nat.card K) (hcenter : Subgroup.center K = ⊥)
    (hOut : CFSG.Open.pRank p (⊤ : Subgroup (CFSG.ComponentClassification.OuterAutomorphisms.Outer K)) ≤ 1)
    {A : Type*} [Group A] [Finite A] (hAcomm : ∀ a b : A, a * b = b * a)
    (hApow : ∀ a : A, a ^ p = 1) (f : A →* MulAut K) (hf : Function.Injective f) :
    Nat.card A ≤ p := by
  classical
  have hpg : IsPGroup p A := fun a => ⟨1, by rw [pow_one]; exact hApow a⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := p) (G := A)).1 hpg
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner K)).comp f) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    obtain ⟨κ, hκ⟩ := hx
    have hpow : MulAut.conj (κ ^ p) = 1 := by
      rw [map_pow, hκ, ← map_pow, hApow x, map_one]
    have hz : κ ^ p ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut K => φ g) hpow
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * κ ^ p = (κ ^ p * g * (κ ^ p)⁻¹) * κ ^ p := by rw [h]
        _ = κ ^ p * g := by group
    rw [hcenter, Subgroup.mem_bot] at hz
    have h1 : orderOf κ ∣ p := orderOf_dvd_of_pow_eq_one hz
    have h2 : orderOf κ ∣ Nat.card K := orderOf_dvd_natCard κ
    have h3 : orderOf κ = 1 := by
      rcases (Nat.dvd_prime Fact.out).1 h1 with h | h
      · exact h
      · exact absurd (h ▸ h2) hKp
    have hκ1 : κ = 1 := orderOf_eq_one_iff.1 h3
    rw [hκ1, map_one] at hκ
    exact (Subgroup.mem_bot.2 (hf (by rw [← hκ, map_one])))
  have hle := CFSG.SectionRank.le_pRank_of_injective (G := CFSG.ComponentClassification.OuterAutomorphisms.Outer K)
    (p := p) (Fact.out : p.Prime).one_lt hAcomm hApow ha _ hinj (H := ⊤) le_top
  have : a ≤ 1 := hle.trans hOut
  rw [ha]
  calc p ^ a ≤ p ^ 1 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos this
    _ = p := pow_one p

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
