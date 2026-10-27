module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630I2026Lin
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630I2026Str
public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryAutomorphismEnd

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026

open CFSG.LocalAnalysis.RankThreeTheoremC (smallRankIsQ8D8)

theorem cent_all {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {E : Type} [Group E] [Finite E]
    (hcomm : ∀ a b : E, a * b = b * a) (hexp : ∀ e : E, e ^ q = 1)
    (hcard : Nat.card E = q ^ 4) {S : Subgroup (MulAut E)} {α β γ δ z : MulAut E}
    (hP : QDPres S α β γ δ z) :
    (∀ g : MulAut E, (∀ s ∈ S, g * s = s * g) →
      g ∈ Subgroup.center (MulAut E) ∧ ∃ k : ℕ, ∀ e : E, g e = e ^ k) ∧
    (∀ c ∈ Subgroup.center (MulAut E), c * c = 1 → c = 1 ∨ c = z) := by
  letI : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CFSG.IsElementaryAbelian q E :=
    { toIsMulCommutative := ⟨⟨hcomm⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }
  let ρ := CFSG.SignalizerFunctor.Helpers.elementaryAutomorphismEnd q (GroupType := E)
  have hinj : Function.Injective ρ :=
    CFSG.SignalizerFunctor.Helpers.elementary_automorphism_end_injective q (GroupType := E)
  have happ : ∀ (g : MulAut E) (e : E), ρ g (Additive.ofMul e) = Additive.ofMul (g e) :=
    fun g e => CFSG.SignalizerFunctor.Helpers.elementary_automorphism_end_apply q g _
  haveI : Module.Finite (ZMod q) (Additive E) := Module.Finite.of_finite
  have hfin : Module.finrank (ZMod q) (Additive E) = 4 := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod q) (V := Additive E)
    rw [Nat.card_zmod, Nat.card_congr (Additive.ofMul : E ≃ Additive E).symm, hcard] at h1
    exact (Nat.pow_right_injective hq.two_le h1).symm
  have h2 : (2 : ZMod q) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h')
  have hrel : QDRel (ρ α) (ρ β) (ρ γ) (ρ δ) (ρ z) :=
    { aa := by rw [← map_mul, hP.αα]
      bb := by rw [← map_mul, hP.ββ]
      cc := by rw [← map_mul, hP.γγ]
      dd := by rw [← map_mul, hP.δδ, map_one]
      zz := by rw [← map_mul, hP.zz, map_one]
      ba := by rw [← map_mul, ← map_mul, ← map_mul, hP.βα]
      dc := by rw [← map_mul, ← map_mul, ← map_mul, hP.δγ]
      ac := by rw [← map_mul, ← map_mul, hP.αγ]
      ad := by rw [← map_mul, ← map_mul, hP.αδ]
      bc := by rw [← map_mul, ← map_mul, hP.βγ]
      bd := by rw [← map_mul, ← map_mul, hP.βδ]
      z_ne := fun h => hP.z_ne (hinj (h.trans (map_one ρ).symm)) }
  have hscalar : ∀ g : MulAut E, (∀ s ∈ S, g * s = s * g) → ∃ k : ZMod q, ρ g = k • 1 := by
    intro g hg
    have hc : ∀ x ∈ S, ρ g * ρ x = ρ x * ρ g := fun x hx => by
      rw [← map_mul, ← map_mul, hg x hx]
    exact (hrel.commutant_scalar h2 hfin (ρ g) (hc α hP.α_mem) (hc β hP.β_mem)
      (hc γ hP.γ_mem) (hc δ hP.δ_mem)).2
  have hnt : Nontrivial (Additive E) := by
    rw [← Finite.one_lt_card_iff_nontrivial,
      Nat.card_congr (Additive.ofMul : E ≃ Additive E).symm, hcard]
    exact Nat.one_lt_pow (by norm_num) hq.one_lt
  have hone : ∀ k : ZMod q, k • (1 : Module.End (ZMod q) (Additive E)) = 1 ↔ k = 1 := by
    intro k
    constructor
    · intro h
      obtain ⟨v, hv⟩ := exists_ne (0 : Additive E)
      have h1 := congrArg (fun f : Module.End (ZMod q) (Additive E) => f v) h
      simp only [LinearMap.smul_apply, Module.End.one_apply] at h1
      have h2 : (k - 1) • v = 0 := by rw [sub_smul, h1, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv)
    · rintro rfl
      exact one_smul _ _
  have hcent : ∀ g : MulAut E, (∀ s ∈ S, g * s = s * g) → g ∈ Subgroup.center (MulAut E) := by
    intro g hg
    obtain ⟨k, hk⟩ := hscalar g hg
    rw [Subgroup.mem_center_iff]
    intro h
    apply hinj
    rw [map_mul, map_mul, hk]
    ext v
    simp [Module.End.mul_apply]
  have hpow : ∀ g : MulAut E, (∀ s ∈ S, g * s = s * g) → ∃ k : ℕ, ∀ e : E, g e = e ^ k := by
    intro g hg
    obtain ⟨k, hk⟩ := hscalar g hg
    refine ⟨k.val, fun e => ?_⟩
    apply Additive.ofMul.injective
    rw [← happ, hk, LinearMap.smul_apply, Module.End.one_apply, ofMul_pow,
      ← Nat.cast_smul_eq_nsmul (ZMod q), ZMod.natCast_zmod_val]
  refine ⟨fun g hg => ⟨hcent g hg, hpow g hg⟩, ?_⟩
  intro c hc hcc
  have hcS : ∀ s ∈ S, c * s = s * c := fun s _ => ((Subgroup.mem_center_iff.mp hc) s).symm
  obtain ⟨kc, hkc⟩ := hscalar c hcS
  obtain ⟨kz, hkz⟩ := hscalar z hP.z_central
  have hkc2 : kc * kc = 1 := by
    rw [← hone]
    have := congrArg ρ hcc
    rw [map_mul, map_one, hkc, smul_mul_smul_comm, mul_one] at this
    exact this
  have hkz2 : kz * kz = 1 := by
    rw [← hone]
    have := congrArg ρ hP.zz
    rw [map_mul, map_one, hkz, smul_mul_smul_comm, mul_one] at this
    exact this
  have hkz1 : kz ≠ 1 := by
    intro h
    rw [h, one_smul] at hkz
    exact hP.z_ne (hinj (hkz.trans (map_one ρ).symm))
  have hkzm : kz = -1 := (mul_self_eq_one_iff.mp hkz2).resolve_left hkz1
  rcases mul_self_eq_one_iff.mp hkc2 with h | h
  · left
    apply hinj
    rw [hkc, h, one_smul, map_one]
  · right
    apply hinj
    rw [hkc, hkz, h.trans hkzm.symm]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630.I2026
