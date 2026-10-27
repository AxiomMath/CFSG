module

public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.Cube
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzCyc.EqTwoRank
public import CFSG.LieType.SeitzGeneration.ExcOuterSplit
public import CFSG.HardMathSupport.Lang.E27.TwistedE6Field

public section

namespace CFSG.AGLEmbedding.SeitzEqTwo

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.Chevalley TauCeti
open CFSG.HardMathSupport.Lang.Coordinator (twisted_E6_field_descent_of_prime_order
  mem_inner_of_mem_inn_sup_diag exists_subfield_card_of_card_eq)
open CFSG.PreuniquenessRankFour.Helpers (elementary_abelian_map)


theorem exists_fixed_plane_twistedE6 {ℓ d p : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hp : p.Prime)
    (hp2 : p ≠ 2) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * (d * p)))
    (σ ε : K ≃+* K) (hσ : ∀ c, σ c = c ^ ℓ ^ (d * p)) (hε : ∀ c, ε c = c ^ ℓ ^ (d * (p + 1)))
    (he : degCountTw (orderOf ((ℓ ^ d : ℕ) : ZMod p)) = 2) :
    ∃ A : Subgroup (twistedE6RootGroup K σ), IsElemAbelian p A ∧ Nat.card A = p ^ 2 ∧
      ∀ a ∈ A, fieldActor (t := TwistTag.E6) σ ε a = a := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h2dp : 1 ≤ 2 * (d * p) := by have := Nat.mul_pos hd hp.pos; omega
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ h2dp hK
  obtain ⟨S, hS⟩ := exists_subfield_card_of_card_eq hℓ hd hp.pos K hK
  have : Finite S := Subtype.finite
  have hS2 : Nat.card S = (ℓ ^ d) ^ 2 := by rw [hS, ← pow_mul, mul_comm]
  have hpowS : ∀ c : S, ∀ k : ℕ, (c : K) ^ ((ℓ ^ (2 * d)) ^ k) = c := by
    intro c k
    have : Fintype S := Fintype.ofFinite S
    have h1 : c ^ (ℓ ^ (2 * d)) = c := by
      have h := FiniteField.pow_card c
      rwa [← Nat.card_eq_fintype_card, hS] at h
    induction k with
    | zero => simp
    | succ k ih =>
      have h2 : (c : K) ^ (ℓ ^ (2 * d)) = c := congrArg Subtype.val h1
      rw [pow_succ, pow_mul, ih, h2]
  obtain ⟨m, hm⟩ := hp.eq_two_or_odd'.resolve_left hp2
  have hεS : ∀ c : S, ε c = c := fun c => by
    rw [hε, show d * (p + 1) = 2 * d * (m + 1) by rw [hm]; ring, pow_mul, hpowS]
  have hσS : ∀ c : S, σ c = (c : K) ^ ℓ ^ d := fun c => by
    rw [hσ, show d * p = 2 * d * m + d by rw [hm]; ring, pow_add, pow_mul, pow_mul, hpowS]
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : S ≃+* S, ∀ c, σ₀ c = c ^ ℓ ^ d := by
    have hbij : Function.Bijective (iterateFrobenius S ℓ d) :=
      ⟨(iterateFrobenius S ℓ d).injective,
        Finite.surjective_of_injective (iterateFrobenius S ℓ d).injective⟩
    exact ⟨RingEquiv.ofBijective _ hbij, fun c => by
      rw [RingEquiv.ofBijective_apply, iterateFrobenius_def]⟩
  have hcomm : ∀ c, σ.toRingHom (S.subtype c) = S.subtype (σ₀.toRingHom c) := fun c => by
    change σ c = ((σ₀ c : S) : K)
    rw [hσS, hσ₀]
    rfl
  have hle := map_baseChangeGL_graphFixedRootGroup_le (t := TwistTag.E6) (ι := S.subtype)
    σ₀.surjective hcomm
  obtain ⟨A₀, hA₀, hA₀c⟩ : ∃ A₀ : Subgroup (twistedE6RootGroup S σ₀),
      IsElemAbelian p A₀ ∧ Nat.card A₀ = p ^ 2 := by
    rcases degCountTw_eq_two he with h3 | h4
    · exact (sylowTorus_twistedE6_three hℓ hd S hS2 σ₀ hσ₀ hp h3).exists_elemAbelian
    · exact (sylowTorus_twistedE6_four hℓ hd S hS2 σ₀ hσ₀ hp h4).exists_elemAbelian
  obtain ⟨ι, hι, hιcoe⟩ : ∃ ι : twistedE6RootGroup S σ₀ →* twistedE6RootGroup K σ,
      Function.Injective ι ∧
        ∀ y, (ι y : ModGL TwistTag.E6.tag K) = baseChangeGL S.subtype (y : ModGL _ S) :=
    ⟨(Subgroup.inclusion hle).comp ((twistedE6RootGroup S σ₀).equivMapOfInjective _
      (baseChangeGL_injective S.subtype)).toMonoidHom,
      (Subgroup.inclusion_injective hle).comp (MulEquiv.injective _), fun _ => rfl⟩
  have hει : ε.toRingHom.comp S.subtype = S.subtype := RingHom.ext fun c => hεS c
  refine ⟨A₀.map ι, elementary_abelian_map p hA₀ ι, by
    rw [Subgroup.card_map_of_injective hι, hA₀c], ?_⟩
  rintro _ ⟨y, -, rfl⟩
  refine Subtype.ext ?_
  rw [coe_fieldActor, hιcoe, units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
    hει]

theorem seitzExcOuterNarrowTwistedE6EqTwo_holds :
    SeitzExcOuterNarrowTwistedE6EqTwo := by
  rintro ⟨d, hv⟩ p hp hp2 - - E hE - ⟨hout, ⟨-, hnar⟩, -, hp5, q, rfl, -, hcnt⟩
  exfalso
  rcases hnar with hR1 | hPR
  · exact SeitzCyc.not_rankLE1_cat_twistedE6_of_eqTwo q hv hp hcnt hR1
  obtain ⟨K, _, σ, hK, hσ, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  have hℓ : q.p.Prime := q.prime_p
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fact p.Prime := ⟨hp⟩
  have hPR' : PlaneRank2 p (E.map (MulAut.congr e).toMonoidHom) := hPR.map_congr e
  have hout' : ¬ E.map (MulAut.congr e).toMonoidHom ≤
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range := by
    intro h
    apply hout
    rw [← map_range_conj_congr e] at h
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.congr e).injective).1 h
  obtain ⟨α, hαE, hα⟩ : ∃ α ∈ E.map (MulAut.congr e).toMonoidHom,
      α ∉ (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range := by
    by_contra h
    push Not at h
    exact hout' fun x hx => h x hx
  have hαp : α ^ p = 1 := (elementary_abelian_map p hE _).2 α hαE
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, hZ, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hη1 : Θ α ≠ 1 := by
    intro h1
    refine hα (mem_inner_of_mem_inn_sup_diag hp hK hσ (fun h => ?_) hcube hαp
      (by rw [← hker]; exact h1))
    have h3 := Nat.le_of_dvd (by norm_num) (h.trans (Nat.gcd_dvd_left 3 _))
    omega
  have hK2 : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨dd, hdd, hdd0, r, ε, hε, ψ, hψ⟩ :=
    twisted_E6_field_descent_of_prime_order hℓ hf K hK2 σ hσ Θ hΘ hp hp2 α hαp hη1
  have hε1 : ε ≠ 1 := by
    intro h1
    have hp1 : 1 < p := hp.one_lt
    obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Lang.E27.exists_pow_ne_self hℓ
      (n := dd * (p + 1)) (N := 2 * q.exponent) (by positivity)
      (by rw [hdd]; nlinarith) K hK2
    exact hc (by rw [← hε, h1]; rfl)
  have hαr : α ^ r ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hψ
    apply hε1
    have h := hΘ (fieldActor σ ε) 1 1 ε (by rw [map_one, map_one, one_mul, one_mul])
    rw [← hψ, map_one] at h
    exact h.symm
  have hαord : orderOf α = p := orderOf_eq_prime hαp fun h => hα ⟨1, by rw [h, map_one]⟩
  have hrp : ¬ p ∣ r := by
    rintro ⟨t, rfl⟩
    exact hαr (by rw [pow_mul, hαp, one_pow])
  obtain ⟨s, hs⟩ := CFSG.RankThree.Chevalley.exists_mul_mod_eq_one hp
    (Nat.pos_of_ne_zero fun h => hrp (Nat.dvd_of_mod_eq_zero h)) (Nat.mod_lt r hp.pos)
  have hrs : r * s % p = s * (r % p) % p := by
    rw [Nat.mul_mod r s, Nat.mul_mod s (r % p), Nat.mod_mod, mul_comm (r % p)]
  have hpow : (α ^ r) ^ s = α := by
    rw [← pow_mul]
    exact CFSG.RankThree.Chevalley.pow_eq_self_of_mod_eq_one hαord (hrs.trans hs)
  have hK' : Nat.card K = q.p ^ (2 * (dd * p)) := by rw [hK2, hdd, mul_comm p dd]
  have hσ' : ∀ c, σ c = c ^ q.p ^ (dd * p) := fun c => by rw [hσ, hdd, mul_comm p dd]
  have hcnt' : degCountTw (orderOf ((q.p ^ dd : ℕ) : ZMod p)) = 2 := by
    have hq : ((q.card : ℕ) : ZMod p) = ((q.p ^ dd : ℕ) : ZMod p) := by
      rw [TauCeti.PrimePower.card_def, hdd, pow_mul']
      exact (Nat.cast_pow _ _).trans (ZMod.pow_card _)
    rw [← hq]
    exact hcnt
  obtain ⟨A, hA, hAc, hfix⟩ :=
    exists_fixed_plane_twistedE6 hℓ hdd0 hp hp2 K hK' σ ε hσ' hε hcnt'
  have hinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hc : g ∈ Subgroup.center (twistedE6RootGroup K σ) := Subgroup.mem_center_iff.2 fun x => by
      have h1 := congrArg (fun φ : MulAut (twistedE6RootGroup K σ) => φ x) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc x * g = g * x * g⁻¹ * g := by rw [h1]
        _ = g * x := by group
    rwa [hZ] at hc
  refine not_rankLE2_sup_of_conj hp hinj ?_ ?_ hA hAc hfix hαE ψ r hψ hPR'
  · rw [← hψ, conj_pow, ← pow_mul, mul_comm, pow_mul, hαp, one_pow, mul_one, mul_inv_cancel]
  · rintro ⟨g, hg⟩
    apply hα
    have hαr' : α ^ r = MulAut.conj (ψ⁻¹ g) := by
      have e1 : α ^ r = ψ⁻¹ * fieldActor σ ε * ψ := by
        rw [← hψ]
        group
      rw [e1, ← hg]
      ext x
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply_self]
    rw [← hpow, hαr', ← map_pow]
    exact ⟨_, rfl⟩

end CFSG.AGLEmbedding.SeitzEqTwo
