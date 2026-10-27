module

public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Torus
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Lift
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Star

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

set_option linter.unusedSectionVars false


section Frame

variable {L : Type} [Field L] [IsAlgClosed L]

theorem mem_torus_iff (S : LangSetup .E8 L 5) {x : ModGL Tag.E8 L} :
    x ∈ S.D.torus ↔ x ∈ torusGroup Tag.E8 L ∧ S.D.n * S.D.Φ x * S.D.n⁻¹ = x :=
  mem_twistedTorusOf

theorem torus_le_Γ (S : LangSetup .E8 L 5) (hMΓ : S.D.model ≤ S.Γ) : S.D.torus ≤ S.Γ := by
  intro x hx
  refine hMΓ ?_
  rw [LangDatum.mem_model]
  exact ⟨twistedTorusOf_le_adjointGroup _ _ hx, (mem_twistedTorusOf.1 hx).2⟩

theorem exists_lift_Γ (S : LangSetup .E8 L 5) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
    (hMΓ : S.D.model ≤ S.Γ) :
    ∃ v : ↥S.Γ,
      (∀ t : ↥S.Γ, (t : ModGL Tag.E8 L) ∈ S.D.torus →
        ((v * t * v⁻¹ : ↥S.Γ) : ModGL Tag.E8 L) ∈ S.D.torus) ∧
      ((v ^ 5 : ↥S.Γ) : ModGL Tag.E8 L) ∈ S.D.torus ∧
      (v : ModGL Tag.E8 L) ∉ S.D.torus ∧
      ∀ a : Fin Tag.E8.rank → Lˣ,
        rootDiagUnit Tag.E8 a * (v : ModGL Tag.E8 L) = (v : ModGL Tag.E8 L) * rootDiagUnit Tag.E8 a ↔
          z0 ∈ rootCharStabilizer a := by
  have hq2 : 2 ≤ S.D.q := S.hqpow.1.two_le
  obtain ⟨v₀, hv₀C, hv₀F, hv₀N, hv₀5, hv₀n, hv₀c⟩ :=
    exists_fixed_lift hq2 hFr e8PhiFourWeyl z0 w0_mul_z0
  have hstep : ∀ x : ModGL Tag.E8 L, S.D.step x = S.D.n * S.D.Φ x * S.D.n⁻¹ := fun x => by
    simp [LangDatum.step, MulAut.conj_apply]
  have hv₀step : S.D.step v₀ = v₀ := by
    rw [hstep, hΦ, hn]
    exact hv₀F
  have hv₀M : v₀ ∈ S.D.model := by
    rw [LangDatum.mem_model, ← hstep]
    exact ⟨hv₀C, hv₀step⟩
  have hv₀Γ : v₀ ∈ S.Γ := hMΓ hv₀M
  refine ⟨⟨v₀, hv₀Γ⟩, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have ht' := mem_torus_iff S |>.1 ht
    refine (mem_torus_iff S).2 ⟨hv₀N _ ht'.1, ?_⟩
    have hts : S.D.step (t : ModGL Tag.E8 L) = t := by rw [hstep]; exact ht'.2
    have hfix : S.D.step ((v₀ * t * v₀⁻¹ : ModGL Tag.E8 L)) = v₀ * t * v₀⁻¹ := by
      rw [map_mul, map_mul, map_inv, hv₀step, hts]
    rwa [hstep] at hfix
  · have h5 : z0 ^ 5 = 1 := z0_pow_five
    have h5' := hv₀5 h5
    refine (mem_torus_iff S).2 ⟨?_, ?_⟩
    · exact h5'
    · have hfix : S.D.step (v₀ ^ 5) = v₀ ^ 5 := by rw [map_pow, hv₀step]
      rwa [hstep] at hfix
  · intro h
    exact hv₀n z0_ne_one ((mem_torus_iff S).1 h).1
  · exact hv₀c

theorem exists_primitiveRoot_five (S : LangSetup .E8 L 5) : ∃ ζ : Lˣ, IsPrimitiveRoot ζ 5 := by
  have h5 : ((5 : ℕ) : L) ≠ 0 := by
    intro h
    have hcop : IsCoprime ((5 : ℕ) : ℤ) ((S.D.q : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 S.hpq)
    have h1 := hcop.map (Int.castRingHom L)
    simp only [eq_intCast, Int.cast_natCast] at h1
    rw [h, S.hqpow.2] at h1
    exact not_isUnit_zero (isCoprime_zero_left.1 h1)
  haveI : NeZero ((5 : ℕ) : L) := ⟨h5⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 5
  have hu : IsUnit ζ := hζ.isUnit (by norm_num)
  exact ⟨hu.unit, IsPrimitiveRoot.coe_units_iff.1 (by simpa using hζ)⟩

end Frame

theorem exists_starData (q : ℕ) (h5 : 5 ∣ q ^ 2 + 1) :
    ∃ D : StarData, D.Valid ∧ (5 : ℤ) ∣ (q : ℤ) - D.r := by
  have hq : q % 5 = 2 ∨ q % 5 = 3 := by
    have h0 : (q ^ 2 + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    have hsq : (q ^ 2 + 1) % 5 = ((q % 5) ^ 2 + 1) % 5 := by
      simp [Nat.add_mod, Nat.pow_mod]
    rw [hsq] at h0
    have hlt : q % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : q % 5 <;> first | omega | (norm_num at h0)
  rcases hq with hq | hq
  · exact ⟨starData2, starData2_valid, by rw [show starData2.r = 2 from rfl]; omega⟩
  · exact ⟨starData3, starData3_valid, by rw [show starData3.r = 3 from rfl]; omega⟩


section Star

variable {L : Type} [Field L] [IsAlgClosed L]

theorem localDeltaIn_zpowers_eq_bot_of_commute_lift
    (S : LangSetup .E8 L 5) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
    (hw4 : ∀ δ : Fin Tag.E8.rank → ℤ, IsRoot .E8 δ → e8PhiFourWeyl • e8PhiFourWeyl • δ = -δ)
    (hMΓ : S.D.model ≤ S.Γ) (hAlg : S.IsAlgebraic)
    (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
    (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
    (hex : LangComponentsQuasisimple .exc)
    (hinj : Function.Injective (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ))
    (hAK : AnyKindCommute) (hAK3 : AnyKindCommuteThreeFull)
    (hq5 : 5 ∣ S.D.q ^ 2 + 1) (hq3 : 3 ≤ S.D.q) {v : ↥S.Γ}
    (hvc : ∀ a : Fin Tag.E8.rank → Lˣ,
      rootDiagUnit Tag.E8 a * (v : ModGL Tag.E8 L) = (v : ModGL Tag.E8 L) * rootDiagUnit Tag.E8 a ↔
        z0 ∈ rootCharStabilizer a)
    {u : ↥S.Γ} (huT : (u : ModGL Tag.E8 L) ∈ S.D.torus) (hu1 : u ≠ 1) (hu5 : u ^ 5 = 1)
    (hvu : v * u = u * v) {H : Subgroup (MulAut ↥S.Γ)} (hH : innerAut ↥S.Γ ≤ H) :
    localDeltaIn 5 H ((Subgroup.zpowers u).map (MulAut.conj : ↥S.Γ →* MulAut ↥S.Γ)) = ⊥ := by
  classical
  haveI := S.finite_Γ
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_five S
  obtain ⟨D, hD, hDr⟩ := exists_starData S.D.q hq5
  have hz5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hz5' : ζ ^ (5 : ℤ) = 1 := by exact_mod_cast hz5
  have hmem_tor : ∀ e : V8, inE D.r e → rootDiagUnit Tag.E8 (tupE ζ e) ∈ S.D.torus := by
    intro e he
    rw [mem_torus_iff]
    refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
    rw [hΦ, hn]
    refine mem_twistedFixedTuples_iff_conj.1 ((mem_twistedFixedTuples_tupE hζ e w0_smul hFr).2 ?_)
    intro j
    have h1 := dvd_sub (he j) (Dvd.dvd.mul_right hDr (e j))
    have h2 : (∑ i, e i * M0 i j) - D.r * e j - ((S.D.q : ℤ) - D.r) * e j =
        (∑ i, e i * M0 i j) - (S.D.q : ℤ) * e j := by ring
    rw [h2] at h1
    exact h1
  have hinE : ∀ e : V8, rootDiagUnit Tag.E8 (tupE ζ e) ∈ S.D.torus → inE D.r e := by
    intro e he j
    have h0 := (mem_twistedFixedTuples_tupE hζ e w0_smul hFr).1
      (mem_twistedFixedTuples_iff_conj.2 (by
        have := ((mem_torus_iff S).1 he).2
        rwa [hΦ, hn] at this)) j
    have h1 := dvd_add h0 (Dvd.dvd.mul_right hDr (e j))
    have h2 : (∑ i, e i * M0 i j) - (S.D.q : ℤ) * e j + ((S.D.q : ℤ) - D.r) * e j =
        (∑ i, e i * M0 i j) - D.r * e j := by ring
    rw [h2] at h1
    exact h1
  have hpow5 : ∀ e : V8, rootDiagUnit Tag.E8 (tupE ζ e) ^ 5 = 1 := by
    intro e
    rw [rootDiagUnit_pow]
    have : tupE ζ e ^ 5 = 1 := funext fun i => tupE_pow_five hz5 e i
    rw [this, rootDiagUnit_one]
  have hmem_E : ∀ e : V8, inE D.r e → rootDiagUnit Tag.E8 (tupE ζ e) ∈ S.E := by
    intro e he
    exact S.E_all _ (Subgroup.mem_inf.2 ⟨hmem_tor e he, torus_le_Γ S hMΓ (hmem_tor e he)⟩)
      (hpow5 e)
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ((mem_torus_iff S).1 huT).1
  have ha5 : a ^ 5 = 1 := by
    apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E8) (K := L)
    rw [← rootDiagUnit_pow, ← ha, rootDiagUnit_one]
    have h1 := congrArg Subtype.val hu5
    simpa using h1
  obtain ⟨e', he'⟩ := exists_tupE hζ a (fun i => by
    have h1 := congrFun ha5 i
    simpa using h1)
  have hin' : inE D.r e' := hinE e' (by rw [← he', ← ha]; exact huT)
  have hfix' : fixZ e' := by
    have hcomm : rootDiagUnit Tag.E8 a * (v : ModGL Tag.E8 L) =
        (v : ModGL Tag.E8 L) * rootDiagUnit Tag.E8 a := by
      rw [← ha]
      exact (congrArg Subtype.val hvu).symm
    have hst := (hvc a).1 hcomm
    rw [he'] at hst
    exact (mem_rootCharStabilizer_tupE hζ e' z0_smul).1 hst
  obtain ⟨k, hk⟩ := hD.fix e' hin' hfix'
  set aS : Fin Tag.E8.rank → Lˣ := tupE ζ D.e with haS
  have huE : rootDiagUnit Tag.E8 aS ∈ S.E := hmem_E D.e hD.inE_e
  have haS1 : rootDiagUnit Tag.E8 aS ≠ 1 := by
    intro h
    obtain ⟨i, hi⟩ := hD.e_ne
    have h1 : aS = 1 :=
      CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := Tag.E8) (K := L)
        (h.trans rootDiagUnit_one.symm)
    have h2 := congrFun h1 i
    simp only [haS, tupE, Pi.one_apply] at h2
    exact hi (by simpa using (hζ.zpow_eq_one_iff_dvd _).1 h2)
  have hak : a = aS ^ k := by
    funext i
    obtain ⟨m, hm⟩ := hk i
    have h1 : e' i = k * D.e i + 5 * m := by linarith
    have h2 : a i = ζ ^ e' i := by rw [he']; rfl
    show a i = (tupE ζ D.e i) ^ k
    simp only [tupE]
    rw [h2, h1, zpow_add, zpow_mul ζ 5 m, hz5', one_zpow, mul_one, ← zpow_mul, mul_comm]
  set uS : ↥S.Γ := ⟨rootDiagUnit Tag.E8 aS, (S.E_le huE).2⟩ with huS
  have huk : u = uS ^ k := by
    apply Subtype.ext
    rw [ha, hak]
    change rootDiagUnit Tag.E8 (aS ^ k) = (rootDiagUnit Tag.E8 aS) ^ k
    exact map_zpow (rootDiagUnitHom Tag.E8 L) aS k
  have huS5 : uS ^ 5 = 1 := Subtype.ext (by simpa using hpow5 D.e)
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hz : Subgroup.zpowers u = Subgroup.zpowers uS := by
    have hle : Subgroup.zpowers u ≤ Subgroup.zpowers uS := by
      rw [Subgroup.zpowers_le, huk]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers uS) k
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hu5 hu1]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one huS5)
  rw [hz]
  have ha'E := hmem_E D.x hD.inE_x
  have hreg : ∀ γ, IsRoot Tag.E8 γ → rootChar aS γ = 1 → rootChar (tupE ζ D.x) γ ≠ 1 := by
    intro γ hγ h1 h2
    exact hD.x_reg γ (mem_rootsV_iff.2 hγ) ((rootChar_tupE_eq_one_iff hζ D.e γ).1 h1)
      ((rootChar_tupE_eq_one_iff hζ D.x γ).1 h2)
  have hne : ∃ γ, IsRoot Tag.E8 γ ∧ rootChar aS γ = 1 :=
    ⟨D.g ⟨0, by decide⟩, mem_rootsV_iff.1 (hD.g_mem _).1,
      (rootChar_tupE_eq_one_iff hζ D.e _).2 (hD.g_mem _).2⟩
  have hLL : ∀ z ∈ adjointGroup Tag.E8 L, (∀ γ, IsRoot Tag.E8 γ → rootChar aS γ = 1 → ∀ c : L,
      z * pinnedX Tag.E8 L γ c = pinnedX Tag.E8 L γ c * z) → z ^ 5 = 1 := by
    intro z hz hcomm
    exact pow_five_eq_one_of_commute_kernel D hD hζ hz fun γ hγ hdvd c =>
      hcomm γ hγ ((rootChar_tupE_eq_one_iff hζ D.e γ).2 hdvd) c
  have hCom : CommuteAt S aS := by
    by_cases hq4 : 4 ≤ S.D.q
    · exact commuteAt_of_four_le S hAK (by decide) hq4 huE
    · have hq : S.D.q = 3 := by omega
      have hr : D.r = 3 := by
        have h1 := hD.r_cases
        rw [hq] at hDr
        omega
      refine commuteAt_three S hAK3 (Or.inr (Or.inr (Or.inr rfl))) hq huE
        (fun i => two_lt_ncard_componentRoots (fun γ hγ hχ => ?_) i)
      obtain ⟨v', hv', hdvd', hne1, hne2, hform⟩ := hD.adj hr γ (mem_rootsV_iff.2 hγ)
        ((rootChar_tupE_eq_one_iff hζ D.e γ).1 hχ)
      exact ⟨v', mem_rootsV_iff.1 hv', (rootChar_tupE_eq_one_iff hζ D.e v').2 hdvd', hne1, hne2,
        hform⟩
  exact localDeltaIn_zpowers_eq_bot_of_star S hFr hΦ hn hw4 hMΓ hAlg hsub hin hsu htw hex hinj
    huE haS1 ha'E hreg hne hCom hLL hH

end Star

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
