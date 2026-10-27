module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwSetup
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwElts
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TwLift
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6TwTorus

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartTwo.Census.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

section Rank


theorem rootDiagUnit_eq_one_iff {τ : Tag} {K : Type} [Field K] (b : Fin τ.rank → Kˣ) :
    rootDiagUnit τ b = 1 ↔ b = 1 := by
  refine ⟨fun h => funext fun i => ?_, fun h => by rw [h, rootDiagUnit_one]⟩
  have hv := congrArg (fun g : ModGL τ K => (g : Module.End K (RootModule τ K))
    (rootVec τ K (Pi.single i 1))) h
  change rootDiag b (rootVec τ K _) = (1 : Module.End K (RootModule τ K)) (rootVec τ K _) at hv
  rw [rootDiag_rootVec _ (isRoot_single τ i), Module.End.one_apply] at hv
  have hne : rootVec τ K (Pi.single i 1 : Fin τ.rank → ℤ) ≠ 0 := by
    rw [CFSG.LieType.Chevalley.rootVec_eq_single (isRoot_single τ i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h1 : (rootChar b (Pi.single i 1) : K) = 1 := by
    have := hv.trans (one_smul K _).symm
    exact smul_left_injective K hne this
  have e : rootChar b (Pi.single i 1) = b i := by
    have := rootChar_nsmul_single b i 1
    rwa [one_nsmul, pow_one] at this
  rw [e] at h1
  exact Units.ext h1

variable {K : Type} [Field K] [Finite K] (σ : K →+* K) (hθ : ∀ c, σ (σ c) = c)
  (hk : 4 ≤ Nat.card K)

theorem e6IsogenyFixed_twT (s t : Kˣ) :
    e6IsogenyFixed σ (twT05 σ hθ s * twT24 σ hθ t) =
      rootDiagUnit .E6 (fun j => s ^ Tag.cartan .E6 (nd 0) j *
        Units.map (σ : K →* K) s ^ Tag.cartan .E6 (nd 5) j *
          (t ^ Tag.cartan .E6 (nd 2) j * Units.map (σ : K →* K) t ^ Tag.cartan .E6 (nd 4) j)) := by
  change ((e6Isogeny K (e6Data_valid.hm K (nd 0) s *
      e6Data_valid.hm K (nd 5) (Units.map (σ : K →* K) s) *
      (e6Data_valid.hm K (nd 2) t * e6Data_valid.hm K (nd 4) (Units.map (σ : K →* K) t))) :
        ↥(adjointGroup .E6 K)) : ModGL .E6 K) = _
  rw [map_mul, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
    CFSG.StandardType.InnerDiagTwE6.e6Isogeny_hm, CFSG.StandardType.InnerDiagTwE6.e6Isogeny_hm,
    CFSG.StandardType.InnerDiagTwE6.e6Isogeny_hm, CFSG.StandardType.InnerDiagTwE6.e6Isogeny_hm,
    ← rootDiagUnit_mul, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  rfl

theorem cartan_cases_E6 (j : Fin (Tag.rank .E6)) :
    (Tag.cartan .E6 (nd 0) j - Tag.cartan .E6 (nd 5) j = 2 ∧
        Tag.cartan .E6 (nd 2) j - Tag.cartan .E6 (nd 4) j = -1) ∨
      (Tag.cartan .E6 (nd 0) j - Tag.cartan .E6 (nd 5) j = 0 ∧
        Tag.cartan .E6 (nd 2) j - Tag.cartan .E6 (nd 4) j = 0) ∨
      (Tag.cartan .E6 (nd 0) j - Tag.cartan .E6 (nd 5) j = -1 ∧
        Tag.cartan .E6 (nd 2) j - Tag.cartan .E6 (nd 4) j = 2) ∨
      (Tag.cartan .E6 (nd 0) j - Tag.cartan .E6 (nd 5) j = 1 ∧
        Tag.cartan .E6 (nd 2) j - Tag.cartan .E6 (nd 4) j = -2) ∨
      (Tag.cartan .E6 (nd 0) j - Tag.cartan .E6 (nd 5) j = -2 ∧
        Tag.cartan .E6 (nd 2) j - Tag.cartan .E6 (nd 4) j = 1) := by
  fin_cases j <;> decide

theorem twIsog_twT_eq_one_iff {ξ : Kˣ} (hξ : orderOf ξ = 9)
    (hθξ : Units.map (σ : K →* K) ξ = ξ⁻¹) (m n : ℤ) :
    twIsog σ hθ hk (twT05 σ hθ (ξ ^ m) * twT24 σ hθ (ξ ^ n)) = 1 ↔
      (9 : ℤ) ∣ 2 * m - n ∧ (9 : ℤ) ∣ m - 2 * n := by
  have h1 : twIsog σ hθ hk (twT05 σ hθ (ξ ^ m) * twT24 σ hθ (ξ ^ n)) = 1 ↔
      e6IsogenyFixed σ (twT05 σ hθ (ξ ^ m) * twT24 σ hθ (ξ ^ n)) = 1 := by
    rw [← coe_twIsog σ hθ hk]
    exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩
  rw [h1, e6IsogenyFixed_twT]
  refine (rootDiagUnit_eq_one_iff _).trans ?_
  rw [funext_iff]
  have hexp : ∀ j : Fin (Tag.rank .E6), (ξ ^ m) ^ Tag.cartan .E6 (nd 0) j *
      Units.map (σ : K →* K) (ξ ^ m) ^ Tag.cartan .E6 (nd 5) j *
        ((ξ ^ n) ^ Tag.cartan .E6 (nd 2) j *
          Units.map (σ : K →* K) (ξ ^ n) ^ Tag.cartan .E6 (nd 4) j) =
      ξ ^ (m * (Tag.cartan .E6 (nd 0) j - Tag.cartan .E6 (nd 5) j) +
        n * (Tag.cartan .E6 (nd 2) j - Tag.cartan .E6 (nd 4) j)) := by
    intro j
    rw [map_zpow, map_zpow, hθξ, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul, inv_zpow',
      inv_zpow', ← zpow_add, ← zpow_add, ← zpow_add]
    congr 1
    ring
  have hdvd : ∀ e : ℤ, ξ ^ e = 1 ↔ (9 : ℤ) ∣ e := fun e => by
    have h9 : ((orderOf ξ : ℕ) : ℤ) = 9 := by rw [hξ]; rfl
    rw [← h9]
    exact orderOf_dvd_iff_zpow_eq_one.symm
  simp only [Pi.one_apply, hexp, hdvd]
  constructor
  · intro h
    have h0 := h (nd 0)
    have h4 := h (nd 4)
    rw [show Tag.cartan .E6 (nd 0) (nd 0) - Tag.cartan .E6 (nd 5) (nd 0) = 2 by decide,
      show Tag.cartan .E6 (nd 2) (nd 0) - Tag.cartan .E6 (nd 4) (nd 0) = -1 by decide] at h0
    rw [show Tag.cartan .E6 (nd 0) (nd 4) - Tag.cartan .E6 (nd 5) (nd 4) = 1 by decide,
      show Tag.cartan .E6 (nd 2) (nd 4) - Tag.cartan .E6 (nd 4) (nd 4) = -2 by decide] at h4
    exact ⟨by omega, by omega⟩
  · rintro ⟨h0, h4⟩ j
    rcases cartan_cases_E6 j with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
      rw [e1, e2] <;> omega

omit [Finite K] in
theorem twE6_field {r f : ℕ} (hr : r.Prime) (hf : 1 ≤ f) [Fintype K]
    (hK : Nat.card K = (r ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (r ^ f)) :
    (∀ c, σ (σ c) = c) ∧ 4 ≤ Nat.card K ∧ 2 ≤ r ^ f := by
  have hq2 : 2 ≤ r ^ f := hr.two_le.trans (Nat.le_self_pow (by omega) r)
  refine ⟨fun c => ?_, ?_, hq2⟩
  · rw [hσ (σ c), hσ c, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  · rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (r ^ f) ^ 2 := Nat.pow_le_pow_left hq2 2

theorem exists_orderOf_units {d : ℕ} (hd : d ∣ Nat.card K - 1) : ∃ x : Kˣ, orderOf x = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  rw [← Nat.card_units, ← hord] at hd
  exact ⟨g ^ (orderOf g / d), orderOf_pow_orderOf_div (orderOf_pos g).ne' hd⟩

theorem units_map_eq_inv {q : ℕ} (hσ : ∀ c, σ c = c ^ q) {x : Kˣ} (hx : x ^ (q + 1) = 1) :
    Units.map (σ : K →* K) x = x⁻¹ := by
  have h1 : Units.map (σ : K →* K) x = x ^ q :=
    Units.ext (by simp [hσ])
  rw [h1]
  exact eq_inv_of_mul_eq_one_right (by rw [← pow_succ']; exact hx)

variable {r : ℕ} [Fact r.Prime] [CharP K r]

@[expose] noncomputable def primeIncl : ZMod r →+* K := ZMod.castHom (dvd_refl r) K

theorem sigma_primeIncl (x : ZMod r) : σ (primeIncl x) = primeIncl x := by
  rw [← ZMod.natCast_zmod_val x, map_natCast, map_natCast]

theorem six_le_pRank_of_cover_twE6 {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ r ^ f + 1)
    (hK : Nat.card K = (r ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (r ^ f))
    {L : Type} [Group L] [Finite L] [Finite ↥(twDerived σ)]
    (π : L →* ↥(twDerived σ)) (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center L) (hZ : 3 ∣ Nat.card (Subgroup.center L)) :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup L) := by
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
  refine six_le_pRank_of_cover_of_witnesses π hπ hker hZ e N fe M
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

theorem six_le_pRank_twE6 {f : ℕ} (hf : 1 ≤ f) (h9 : 9 ∣ r ^ f + 1)
    (hK : Nat.card K = (r ^ f) ^ 2) (hσ : ∀ c, σ c = c ^ (r ^ f)) [Finite ↥(twDerived σ)] :
    6 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(twDerived σ)) := by
  have hr : r.Prime := Fact.out
  have := Fintype.ofFinite K
  obtain ⟨hθ, hk, hq2⟩ := twE6_field σ hr hf hK hσ
  have h3 : 3 ∣ r ^ f + 1 := (show (3 : ℕ) ∣ 9 by norm_num).trans h9
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
  have h9K : 9 ∣ Nat.card K - 1 := by rw [hK, hsq]; exact h9.mul_right _
  obtain ⟨ξ, hξ⟩ := exists_orderOf_units (K := K) h9K
  have hξq : ξ ^ (r ^ f + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hξ ▸ h9)
  have hθξ := units_map_eq_inv σ hσ hξq
  have hξ1 : ξ * Units.map (σ : K →* K) ξ = 1 := by rw [hθξ, mul_inv_cancel]
  have hξ3 : (ξ ^ 3) * Units.map (σ : K →* K) (ξ ^ 3) = 1 := by
    rw [map_pow, hθξ, inv_pow, mul_inv_cancel]
  set ψ := twIsog σ hθ hk
  set A := twA hab
  set e : Fin 4 → ↥(twDerived σ) := fun i => ψ (te6SL2 σ j hj i A)
  set N : Fin 4 → ↥(twDerived σ) := fun i => ψ (te6SL2 σ j hj i twB)
  set x := twT05 σ hθ ξ
  set y := twT24 σ hθ ξ
  set fe : ↥(twDerived σ) := ψ (twT05 σ hθ (ξ ^ 3))
  set u : ↥(twDerived σ) := ψ (x * y⁻¹)
  have hxy : Commute x y := twT05_commute_twT24 σ hθ ξ ξ
  have h05 : ∀ s t : Kˣ, Commute (twT05 σ hθ s) (twT05 σ hθ t) := fun s t => by
    change twT05 σ hθ s * twT05 σ hθ t = twT05 σ hθ t * twT05 σ hθ s
    rw [← map_mul, ← map_mul, mul_comm]
  have hcomm : ∀ i i', i ≠ i' → ∀ B C : SL(2, ZMod r),
      Commute (ψ (te6SL2 σ j hj i B)) (ψ (te6SL2 σ j hj i' C)) := fun i i' hii B C =>
    (show Commute (te6SL2 σ j hj i B) (te6SL2 σ j hj i' C) from
      te6SL2_commute σ j hj hii B C).map ψ
  have hxu : ∀ i (B : SL(2, ZMod r)), Commute (te6SL2 σ j hj i B) (x * y⁻¹) := fun i B =>
    (twT05_commute_te6SL2 σ hθ j hj hξ1 i B).symm.mul_right
      (twT24_commute_te6SL2 σ hθ j hj hξ1 i B).symm.inv_right
  have hpow : ∀ a c : ℤ, twT05 σ hθ (ξ ^ 3) ^ a * (twT05 σ hθ ξ * (twT24 σ hθ ξ)⁻¹) ^ c =
      twT05 σ hθ (ξ ^ (3 * a + c)) * twT24 σ hθ (ξ ^ (-c)) := by
    intro a c
    have hxy' : Commute (twT05 σ hθ ξ) (twT24 σ hθ ξ)⁻¹ := hxy.inv_right
    rw [map_zpow (twT05 σ hθ) ξ (3 * a + c), map_zpow (twT24 σ hθ) ξ (-c),
      map_pow (twT05 σ hθ) ξ 3, hxy'.mul_zpow, inv_zpow', ← zpow_natCast, ← zpow_mul,
      ← mul_assoc, ← zpow_add]
    norm_num
  have hne : ∀ i, e i ≠ 1 := fun i h =>
    twA_ne_one hab h3F (te6SL2_central σ j hj i (mem_center_of_twIsog_eq_one σ hθ hk h))
  have hNe : ∀ i, N i * e i * (N i)⁻¹ = (e i)⁻¹ := fun i => by
    have h := congrArg ψ (show te6SL2 σ j hj i twB * te6SL2 σ j hj i A *
        (te6SL2 σ j hj i twB)⁻¹ = (te6SL2 σ j hj i A)⁻¹ by
      rw [← map_inv, ← map_mul, ← map_mul, twB_conj_twA, map_inv])
    simpa only [map_mul, map_inv] using h
  have hyi : ∀ i, ¬ Commute (N i) (e i) := by
    intro i h
    have h1 : (e i)⁻¹ = e i := by rw [← hNe i, h.eq, mul_inv_cancel_right]
    have h2 : e i * e i = 1 := mul_eq_one_iff_eq_inv.2 h1.symm
    have h3' : e i ^ 3 = e i * (e i * e i) := pow_three _
    have he3 : e i ^ 3 = 1 := by
      change ψ (te6SL2 σ j hj i A) ^ 3 = 1
      rw [← map_pow, ← map_pow, twA_pow_three, map_one, map_one]
    rw [h2, mul_one, he3] at h3'
    exact hne i h3'.symm
  refine six_le_pRank_of_witnesses e N fe u (fun i i' => ?_) (fun i => ?_) (fun i => ?_) ?_
    (fun i => ?_) ?_ ?_ (fun i i' hii => hcomm i i' hii _ _) (fun i => ?_) (fun i => ?_) hyi ?_
  · by_cases hii : i = i'
    · subst hii; exact Commute.refl _
    · exact hcomm i i' hii _ _
  · exact (twT05_commute_te6SL2 σ hθ j hj hξ3 i A).symm.map ψ
  · exact (hxu i A).map ψ
  · exact ((h05 (ξ ^ 3) ξ).mul_right (twT05_commute_twT24 σ hθ (ξ ^ 3) ξ).inv_right).map ψ
  · change ψ (te6SL2 σ j hj i A) ^ 3 = 1
    rw [← map_pow, ← map_pow, twA_pow_three, map_one, map_one]
  · change ψ (twT05 σ hθ (ξ ^ 3)) ^ 3 = 1
    rw [← map_pow, ← map_pow, ← pow_mul, show 3 * 3 = 9 by norm_num, ← hξ, pow_orderOf_eq_one,
      map_one, map_one]
  · change ψ (x * y⁻¹) ^ 3 = 1
    have h := hpow 0 3
    rw [zpow_zero, one_mul, zpow_ofNat] at h
    rw [← map_pow, h]
    exact (twIsog_twT_eq_one_iff σ hθ hk hξ hθξ _ _).2 ⟨by norm_num, by norm_num⟩
  · exact (twT05_commute_te6SL2 σ hθ j hj hξ3 i twB).symm.map ψ
  · exact (hxu i twB).map ψ
  · intro a c h
    have h' : ψ (twT05 σ hθ (ξ ^ (3 * a + c)) * twT24 σ hθ (ξ ^ (-c))) = 1 := by
      rw [← hpow, map_mul, map_zpow, map_zpow]
      exact h
    obtain ⟨h1, h2⟩ := (twIsog_twT_eq_one_iff σ hθ hk hξ hθξ _ _).1 h'
    exact ⟨by omega, by omega⟩

end Rank

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
