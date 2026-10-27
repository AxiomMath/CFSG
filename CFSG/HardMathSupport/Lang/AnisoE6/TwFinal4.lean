module

public import CFSG.HardMathSupport.Lang.AnisoE6.TwPlane4
public import CFSG.HardMathSupport.Lang.AnisoE6.CatBridge
public import CFSG.HardMathSupport.Lang.AnisoE6.FieldEmbed
public import CFSG.LieType.SeitzGeneration.ExcTwistedClasses

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Open CFSG.LieType.SeitzGeneration CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.AGLEmbeddingD2 CFSG.TauCetiBridge TauCeti

set_option linter.unusedSectionVars false


theorem F4_valid4 (q : PrimePower) : (TauCeti.LieTypeIndex.F4 q).Valid := by
  simp

theorem seitzExcAnisotropicTwistedE6Class_four_of_f4
    (hf4 : SeitzExcAnisotropicF4Class 4) : SeitzExcAnisotropicTwistedE6Class 4 := by
  intro d p hp hp2 hpc hD2 E hE hEc hS
  obtain ⟨hinner, ⟨q, hdq⟩, ⟨hp5, q', hdq', -, hord⟩, -, hN⟩ := hS
  obtain ⟨d0, hv⟩ := d
  simp only at hdq hdq'
  subst hdq
  have hqq : q = q' := by simpa using hdq'
  subst hqq
  have hc0 : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have he : orderOf (((q.p ^ q.exponent : ℕ)) : ZMod p) = 4 := by
    rw [← hc0]
    exact hord
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hpq : p ≠ q.p := by simpa using hpc
  obtain ⟨K, _, σ, hK, hσ, ⟨eG⟩⟩ := exists_catEquiv_twistedE6 q hv
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  obtain ⟨k, _, _, hk, hkchar, ⟨eF⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q (F4_valid4 q)
  have hk' : Nat.card k = q.p ^ q.exponent := by rw [hk, hc0]
  obtain ⟨ι⟩ := nonempty_ringHom_of_card_sq (ℓ := q.p) (f := q.exponent) hk' hK
  letI : Algebra k K := ι.toAlgebra
  have hp4dvd : p ∣ Nat.card k ^ 2 + 1 := by
    rw [hk']
    exact dvd_sq_add_one_of_orderOf_eq_four hp he
  have hTΓ : SylowTorus (twistedFixedGroup TwistTag.E6 k (RingHom.id k)) p 2 :=
    (sylowTorus_F4_four k hp (by omega) hp4dvd).of_mulEquiv (e6FixedF4EquivAll k).symm
  have hcl : F4Closing k p q.p := by
    by_cases h2 : q.p = 2 ∧ q.exponent = 1
    · exact f4Closing_of_regime' seitzExcAnisotropicForAt_F4_two q (F4_valid4 q) ⟨q, rfl⟩ hp hp5 (not_isD2SeitzException_F4 hp5 q)
        ⟨hp5, q, rfl, h2.1, h2.2⟩ hpq eF hTΓ
    · exact f4Closing_of_regime' hf4 q (F4_valid4 q) ⟨q, rfl⟩ hp hp5 (not_isD2SeitzException_F4 hp5 q)
        ⟨hp5, q, rfl, h2, hord⟩ hpq eF hTΓ
  have hconj := conj_injective_cat_twistedE6 q hv
  obtain ⟨E₀, hE₀, hE₀c, hE₀m⟩ := exists_map_conj_eq hconj hinner hE hEc
  set E₁ : Subgroup (twistedE6RootGroup K σ) := E₀.map eG.toMonoidHom with hE₁def
  have hE₁ : IsElemAbelian p E₁ :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀ eG.toMonoidHom
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [hE₁def, Subgroup.card_map_of_injective eG.injective, hE₀c]
  have hN₀ : ¬ NormRSub q.p E₀ := by
    intro h
    apply hN
    rw [← hE₀m, normalizesR_iff]
    simpa using h
  have hN₁ : ¬ NormRSub q.p E₁ := fun h => hN₀ (normRSub_of_map_equiv eG h)
  have hmain := closure_centralizers_twistedE6_phi4 σ q.prime_p q.exponent_pos hk' hK hσ hp hp5
    he hcl hE₁ hE₁c hN₁
  have hcl0 : cl E₀ = ⊤ := cl_eq_top_of_map eG E₀ hmain
  rw [PlaneGen, ← hE₀m, planeClosure_map_conj hconj]
  exact hcl0

end CFSG.HardMathSupport.Lang.AnisoE6
