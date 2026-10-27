module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwRank
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.S171ExtremalE6

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Tables.T1b
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartTwo.Census.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

theorem exists_lift_of_witnesses {L Q : Type} [Group L] [Group Q] [Finite Q]
    (π : L →* Q) (hπ : Function.Surjective π) (hker : ∀ x, π x = 1 → x ∈ Subgroup.center L)
    (e N : Fin 4 → Q) (f M : Q) (hee : ∀ i j, Commute (e i) (e j))
    (hef : ∀ i, Commute (e i) f) (he3 : ∀ i, e i ^ 3 = 1) (hf3 : f ^ 3 = 1)
    (he1 : ∀ i, e i ≠ 1) (hf1 : f ≠ 1)
    (hNe : ∀ i, N i * e i * (N i)⁻¹ = (e i)⁻¹)
    (hNe' : ∀ i j, i ≠ j → Commute (N i) (e j)) (hNf : ∀ i, Commute (N i) f)
    (hMf : M * f * M⁻¹ = f⁻¹) :
    ∃ R : Subgroup L, IsElemAbelian 3 R ∧ 3 ^ 5 ≤ Nat.card (R.map π) := by
  set g : Option (Fin 4) → Q := fun o => o.elim f e
  set n : Option (Fin 4) → Q := fun o => o.elim M N
  have hg : ∀ i j, g i * g j = g j * g i := by
    rintro (_ | a) (_ | b)
    · rfl
    · exact (hef b).symm.eq
    · exact (hef a).eq
    · exact (hee a b).eq
  have hconj : ∀ {x y : Q}, Commute x y → x * y * x⁻¹ = y := fun h => by
    rw [h.eq, mul_inv_cancel_right]
  have hrel : ∀ i j, (∃ k : ℤ, n i * g j * (n i)⁻¹ = g j * g i ^ k) ∨
      (∃ k : ℤ, n j * g i * (n j)⁻¹ = g i * g j ^ k) := by
    rintro (_ | a) (_ | b)
    · exact .inl ⟨-2, by
        change M * f * M⁻¹ = f * f ^ (-2 : ℤ)
        rw [hMf]
        group⟩
    · exact .inr ⟨0, by
        change N b * f * (N b)⁻¹ = f * e b ^ (0 : ℤ)
        rw [zpow_zero, mul_one]
        exact hconj (hNf b)⟩
    · exact .inl ⟨0, by
        change N a * f * (N a)⁻¹ = f * e a ^ (0 : ℤ)
        rw [zpow_zero, mul_one]
        exact hconj (hNf a)⟩
    · by_cases hab : a = b
      · subst hab
        exact .inl ⟨-2, by
          change N a * e a * (N a)⁻¹ = e a * e a ^ (-2 : ℤ)
          rw [hNe]
          group⟩
      · exact .inl ⟨0, by
          change N a * e b * (N a)⁻¹ = e b * e a ^ (0 : ℤ)
          rw [zpow_zero, mul_one]
          exact hconj (hNe' a b hab)⟩
  obtain ⟨R, hR3, hRc, hRmap⟩ := exists_elemAbelian_of_reflection_lifts' π hπ
    hker g n hg
    (by rintro (_ | a); exacts [hf3, he3 a])
    (by rintro (_ | a); exacts [hMf, hNe a]) hrel
  have hyi : ∀ i, ¬ Commute (N i) (e i) := by
    intro i h
    have h1 : (e i)⁻¹ = e i := by rw [← hNe i]; exact hconj h
    have h2 : e i * e i = 1 := mul_eq_one_iff_eq_inv.2 h1.symm
    have h3 : e i ^ 3 = e i * (e i * e i) := pow_three _
    rw [h2, mul_one, he3 i] at h3
    exact he1 i h3.symm
  have hbig := three_pow_five_le_card_closure e N f (fun i j => hee i j) hef he3 hf3 hf1
    hNe' hNf hyi
  rw [← hRmap] at hbig
  exact ⟨R, ⟨IsMulCommutative.of_comm fun x y => Subtype.ext (hRc x x.2 y y.2), hR3⟩, hbig⟩

section Rank


variable {K : Type} [Field K] [Finite K] (σ : K →+* K) {r : ℕ} [Fact r.Prime] [CharP K r]

theorem exists_lift_twE6 {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ r ^ f + 1)
    (hK : Nat.card K = (r ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (r ^ f))
    {L : Type} [Group L] [Finite ↥(twDerived σ)]
    (π : L →* ↥(twDerived σ)) (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 1 → x ∈ Subgroup.center L) :
    ∃ R : Subgroup L, IsElemAbelian 3 R ∧ 3 ^ 5 ≤ Nat.card (R.map π) := by
  have hr : r.Prime := Fact.out
  have := Fintype.ofFinite K
  obtain ⟨hθ, hk, hq2⟩ := twE6_field σ hr hf hK hσ
  have h3p : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, b, hab⟩ := exists_twParams r
  have hr3 : r ≠ 3 := by
    rintro rfl
    have := (Nat.dvd_add_right (dvd_pow_self 3 (by omega))).1 h3
    omega
  have h3F : (3 : ZMod r) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    have hd := (CharP.cast_eq_zero_iff (ZMod r) r 3).1 h'
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 hd)
  set j : ZMod r →+* K := primeIncl
  have hj : ∀ x, σ (j x) = j x := sigma_primeIncl σ
  have hsq : (r ^ f) ^ 2 - 1 = (r ^ f + 1) * (r ^ f - 1) := by
    rw [← Nat.sq_sub_sq, one_pow]
  have h3K : 3 ∣ Nat.card K - 1 := by rw [hK, hsq]; exact h3.mul_right _
  obtain ⟨ω, hω⟩ := exists_orderOf_units (K := K) h3K
  have hωq : ω ^ (r ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hω ▸ h3)
  have hθω := units_map_eq_inv σ hσ hωq
  have hω1 : ω * Units.map (σ : K →* K) ω = 1 := by rw [hθω, mul_inv_cancel]
  have hω2 : ((ω : K)) ^ 2 ≠ 1 := by
    intro h
    have h' : ω ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hω] at this
    omega
  set ψ := twIsog σ hθ hk
  set A := twA hab
  set e : Fin 4 → ↥(twDerived σ) := fun i => ψ (te6SL2 σ j hj i A)
  set N : Fin 4 → ↥(twDerived σ) := fun i => ψ (te6SL2 σ j hj i twB)
  set fe : ↥(twDerived σ) := ψ (twT05 σ hθ ω)
  set M : ↥(twDerived σ) := ψ (nHat σ (nf 3))
  have hcomm : ∀ i i', i ≠ i' → ∀ B C : SL(2, ZMod r),
      Commute (ψ (te6SL2 σ j hj i B)) (ψ (te6SL2 σ j hj i' C)) := fun i i' hii B C =>
    (show Commute (te6SL2 σ j hj i B) (te6SL2 σ j hj i' C) from
      te6SL2_commute σ j hj hii B C).map ψ
  refine exists_lift_of_witnesses π hπ hker e N fe M
    (fun i i' => ?_) (fun i => ?_) (fun i => ?_) ?_ (fun i => ?_) ?_ (fun i => ?_)
    (fun i i' hii => hcomm i i' hii _ _) (fun i => ?_) ?_
  · by_cases hii : i = i'
    · subst hii; exact Commute.refl _
    · exact hcomm i i' hii _ _
  · exact (twT05_commute_te6SL2 σ hθ j hj hω1 i A).symm.map ψ
  · change ψ (te6SL2 σ j hj i A) ^ 3 = 1
    rw [← map_pow, ← map_pow, twA_pow_three, map_one, map_one]
  · change ψ (twT05 σ hθ ω) ^ 3 = 1
    rw [← map_pow, ← map_pow, ← hω, pow_orderOf_eq_one, map_one, map_one]
  · intro h
    exact twA_ne_one hab h3F
      (te6SL2_central σ j hj i (mem_center_of_twIsog_eq_one σ hθ hk h))
  · intro h
    exact te6Torus_not_mem_center σ hθ hω2 (mem_center_of_twIsog_eq_one σ hθ hk h)
  · have h := congrArg ψ (show te6SL2 σ j hj i twB * te6SL2 σ j hj i A *
        (te6SL2 σ j hj i twB)⁻¹ = (te6SL2 σ j hj i A)⁻¹ by
      rw [← map_inv, ← map_mul, ← map_mul, twB_conj_twA, map_inv])
    simpa only [map_mul, map_inv] using h
  · exact (twT05_commute_te6SL2 σ hθ j hj hω1 i twB).symm.map ψ
  · have h := congrArg ψ (nHat_conj_twT05 σ hθ ω)
    simpa only [map_mul, map_inv] using h

end Rank

section Cat


open CFSG.LieType.SeitzGeneration in
theorem exists_card_map_mk_twE6 {L : Type} [Group L] [Finite L] {q : TauCeti.PrimePower}
    {hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid} (h3 : 3 ∣ q.p ^ q.exponent + 1)
    (e : L ⧸ Subgroup.center L ≃* Cat ⟨.twistedE6 q, hv⟩) :
    ∃ R : Subgroup L, IsElemAbelian 3 R ∧
      3 ^ 5 ≤ Nat.card (R.map (QuotientGroup.mk' (Subgroup.center L))) := by
  classical
  obtain ⟨F, _, σ, hF, hσ, ⟨e'⟩⟩ := exists_catEquiv_twistedE6 q hv
  haveI : Finite F := Nat.finite_of_card_ne_zero (by
    rw [hF]
    exact pow_ne_zero _ (pow_ne_zero _ q.prime_p.ne_zero))
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  haveI : CharP F q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul])
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    exact hσ x
  obtain ⟨-, -, hΓ, -, -⟩ := finite_fixed_root_group_perfect TwistTag.E6 q.prime_p
    q.exponent_pos F hF σ.toRingHom hσ''
  let Φ : L ⧸ Subgroup.center L ≃* ↥(twDerived σ.toRingHom) :=
    (e.trans e').trans (MulEquiv.subgroupCongr hΓ).symm
  have hπs : Function.Surjective (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) :=
    Φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ x, (Φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) x = 1 →
      x ∈ Subgroup.center L := fun x hx => by
    change Φ (QuotientGroup.mk x) = 1 at hx
    rwa [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at hx
  haveI : Finite ↥(twDerived σ.toRingHom) := Subtype.finite
  obtain ⟨R, hR, hcard⟩ := exists_lift_twE6 σ.toRingHom q.exponent_pos h3 hF hσ'' _ hπs hker
  refine ⟨R, hR, ?_⟩
  rwa [← Subgroup.map_map, Subgroup.card_map_of_injective Φ.injective] at hcard

end Cat

end CFSG.LocalAnalysis.GLTheoremA.S171ExtremalE6
