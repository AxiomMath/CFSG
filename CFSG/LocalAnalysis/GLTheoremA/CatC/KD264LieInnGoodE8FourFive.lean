module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangTorus
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Plane
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E8FourAux.Order
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerE8FourFivePBig

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Lattice
  CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Generic

variable {C : Type} [Group C] [Finite C]

theorem PerfectCentralizerPlanes.of_dichotomy {p : ℕ} (hp : p.Prime) (T : Subgroup C)
    (hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (v : C) (hvT : ∀ t ∈ T, v * t * v⁻¹ ∈ T)
    (hvp : v ^ p ∈ T) (hvn : v ∉ T)
    (hord : (Nat.card C).factorization p = (Nat.card T).factorization p + 1)
    (hT : ∀ D₁ : Subgroup C, D₁ ≤ T → (∀ x ∈ D₁, x ^ p = 1) → Nat.card D₁ = p ^ 2 →
      ∃ d ∈ D₁, d ≠ 1 ∧ ∃ R : Subgroup C,
        R ≤ Subgroup.centralizer ({d} : Set C) ∧ ⁅R, R⁆ = R ∧ p ∣ Nat.card R)
    (hstar : ∀ u ∈ T, u ≠ 1 → u ^ p = 1 → (∃ k : ℕ, ¬ p ∣ k ∧ v ^ k * u = u * v ^ k) →
      ∃ R : Subgroup C, R ≤ Subgroup.centralizer ({u} : Set C) ∧ ⁅R, R⁆ = R ∧
        p ∣ Nat.card R) :
    PerfectCentralizerPlanes p C := by
  intro A hA hAcard
  obtain ⟨c, hc⟩ := exists_conj_dichotomy hp T hTc v hvT hvp hvn hord hA.2 hAcard
  rcases hc with hcT | ⟨u, huA, huT, hu1, k, hk, hvu⟩
  · have hw : ∃ d ∈ A.map (MulAut.conj c).toMonoidHom, d ≠ 1 ∧ ∃ R : Subgroup C,
        R ≤ Subgroup.centralizer ({d} : Set C) ∧ ⁅R, R⁆ = R ∧ p ∣ Nat.card R := by
      have hpow : ∀ x ∈ A.map (MulAut.conj c).toMonoidHom, x ^ p = 1 := by
        rintro _ ⟨y, hy, rfl⟩
        rw [← map_pow, hA.2 y hy, map_one]
      have hcard : Nat.card (A.map (MulAut.conj c).toMonoidHom) = p ^ 2 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hAcard]
      exact hT _ (by rintro _ ⟨y, hy, rfl⟩; exact hcT y hy) hpow hcard
    exact exists_good_of_mem_map_conj hw
  · have hpow : (c * u * c⁻¹) ^ p = 1 := by
      rw [conj_pow, hA.2 u huA, mul_one, mul_inv_cancel]
    obtain ⟨R, hRC, hRp, hRd⟩ := hstar (c * u * c⁻¹) huT hu1 hpow ⟨k, hk, hvu⟩
    obtain ⟨R', hR'C, hR'p, hR'd⟩ :=
      exists_perfect_le_centralizer_of_conj (g := c⁻¹) (x := c * u * c⁻¹) ⟨R, hRC, hRp, hRd⟩
    have hx : c⁻¹ * (c * u * c⁻¹) * (c⁻¹)⁻¹ = u := by group
    have hu1' : u ≠ 1 := by
      intro h
      apply hu1
      rw [h, mul_one, mul_inv_cancel]
    exact ⟨u, huA, hu1', R', by rwa [hx] at hR'C, hR'p, hR'd⟩

theorem exists_perfect_le_centralizer_of_quasisimple_le {G : Type*} [Group G]
    {Γ : Subgroup G} {p : ℕ} (hp : p.Prime) {d : Γ} {R : Subgroup G}
    (hR : R ≤ Γ ⊓ Subgroup.centralizer ({(d : G)} : Set G))
    (hRq : CFSG.IsQuasisimple R) (hRnc : ¬ Nat.Coprime p (Nat.card R)) :
    ∃ P : Subgroup Γ, P ≤ Subgroup.centralizer ({d} : Set Γ) ∧ ⁅P, P⁆ = P ∧
      p ∣ Nat.card P := by
  have hRperf : ⁅R, R⁆ = R := by
    haveI : Group.IsPerfect ↥R := hRq.1
    exact Subgroup.commutator_eq_self
  have hRrange : R ≤ Γ.subtype.range := by
    rw [Subgroup.range_subtype]
    exact hR.trans inf_le_left
  have hRcent : R ≤ Subgroup.centralizer ({(Γ.subtype d)} : Set G) := hR.trans inf_le_right
  obtain ⟨P, hPcent, hPperf, hPcard⟩ :=
    exists_perfect_le_centralizer_of_injective Γ.subtype Γ.subtype_injective hRrange hRperf hRcent
  refine ⟨P, hPcent, hPperf, ?_⟩
  rw [hPcard]
  exact (Nat.Prime.dvd_iff_not_coprime hp).mpr hRnc

end Generic


variable {L : Type} [Field L] [IsAlgClosed L]

section StarData

theorem exists_starTup_mem_E (S : LangSetup .E8 L 5) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
    (hMΓ : S.D.model ≤ S.Γ) (hq5 : 5 ∣ S.D.q ^ 2 + 1) :
    ∃ (ζ : Lˣ) (D : StarData), IsPrimitiveRoot ζ 5 ∧ D.Valid ∧
      (∀ e : V8, inE D.r e → rootDiagUnit Tag.E8 (tupE ζ e) ∈ S.E) ∧
      (∀ e : V8, rootDiagUnit Tag.E8 (tupE ζ e) ∈ S.D.torus → inE D.r e) := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_five S
  obtain ⟨D, hD, hDr⟩ := exists_starData S.D.q hq5
  have hz5 : ζ ^ 5 = 1 := hζ.pow_eq_one
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
  exact ⟨ζ, D, hζ, hD, hmem_E, hinE⟩

end StarData

section StarWitness

theorem exists_starWitness (S : LangSetup .E8 L 5) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
    (hMΓ : S.D.model ≤ S.Γ) (hq5 : 5 ∣ S.D.q ^ 2 + 1) {v : ↥S.Γ}
    (hvc : ∀ a : Fin Tag.E8.rank → Lˣ,
      rootDiagUnit Tag.E8 a * (v : ModGL Tag.E8 L) =
        (v : ModGL Tag.E8 L) * rootDiagUnit Tag.E8 a ↔ z0 ∈ rootCharStabilizer a)
    {u : ↥S.Γ} (huT : (u : ModGL Tag.E8 L) ∈ S.D.torus) (hu5 : u ^ 5 = 1)
    (hvu : v * u = u * v) :
    ∃ (a a' : Fin Tag.E8.rank → Lˣ) (γ : Fin Tag.E8.rank → ℤ),
      rootDiagUnit Tag.E8 a = (u : ModGL Tag.E8 L) ∧ rootDiagUnit Tag.E8 a ∈ S.E ∧
        rootDiagUnit Tag.E8 a' ∈ S.E ∧ IsRoot Tag.E8 γ ∧ rootChar a γ = 1 ∧
          rootChar a' γ ≠ 1 := by
  classical
  obtain ⟨ζ, D, hζ, hD, hmem_E, hinE⟩ := exists_starTup_mem_E S hFr hΦ hn hMΓ hq5
  have hz5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hz5' : ζ ^ (5 : ℤ) = 1 := by exact_mod_cast hz5
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
  have hak : a = aS ^ k := by
    funext i
    obtain ⟨m, hm⟩ := hk i
    have h1 : e' i = k * D.e i + 5 * m := by linarith
    have h2 : a i = ζ ^ e' i := by rw [he']; rfl
    show a i = (tupE ζ D.e i) ^ k
    simp only [tupE]
    rw [h2, h1, zpow_add, zpow_mul ζ 5 m, hz5', one_zpow, mul_one, ← zpow_mul, mul_comm]
  have huSE : (u : ModGL Tag.E8 L) ∈ S.E :=
    S.E_all _ (Subgroup.mem_inf.2 ⟨huT, u.2⟩) (by simpa using congrArg Subtype.val hu5)
  have ha'E : rootDiagUnit Tag.E8 (tupE ζ D.x) ∈ S.E := hmem_E D.x hD.inE_x
  let γ : Fin Tag.E8.rank → ℤ := D.g ⟨0, by decide⟩
  have hγ : IsRoot Tag.E8 γ := mem_rootsV_iff.1 (hD.g_mem _).1
  have hχaS : rootChar aS γ = 1 := (rootChar_tupE_eq_one_iff hζ D.e γ).2 (hD.g_mem _).2
  have hχa : rootChar a γ = 1 := by
    rw [hak]
    rw [show rootChar (aS ^ k) γ = rootChar aS γ ^ k from by
      simp only [rootChar, Pi.pow_apply]
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_mul, ← zpow_mul, mul_comm]]
    rw [hχaS, one_zpow]
  have hχa' : rootChar (tupE ζ D.x) γ ≠ 1 := by
    intro h2
    exact hD.x_reg γ (mem_rootsV_iff.2 hγ)
      ((rootChar_tupE_eq_one_iff hζ D.e γ).1 hχaS)
      ((rootChar_tupE_eq_one_iff hζ D.x γ).1 h2)
  exact ⟨a, tupE ζ D.x, γ, ha.symm, ha ▸ huSE, ha'E, hγ, hχa, hχa'⟩

end StarWitness

section StarPerfect

theorem exists_quasisimple_of_commute_lift (S : LangSetup .E8 L 5) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
    (hw4 : ∀ δ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 δ → e8PhiFourWeyl • e8PhiFourWeyl • δ = -δ)
    (hMΓ : S.D.model ≤ S.Γ) (hq5 : 5 ∣ S.D.q ^ 2 + 1) {v : ↥S.Γ}
    (hvc : ∀ a : Fin Tag.E8.rank → Lˣ,
      rootDiagUnit Tag.E8 a * (v : ModGL Tag.E8 L) =
        (v : ModGL Tag.E8 L) * rootDiagUnit Tag.E8 a ↔ z0 ∈ rootCharStabilizer a)
    {u : ↥S.Γ} (huT : (u : ModGL Tag.E8 L) ∈ S.D.torus) (hu1 : u ≠ 1) (hu5 : u ^ 5 = 1)
    (hvu : v * u = u * v) :
    ∃ R : Subgroup (ModGL Tag.E8 L),
      R ≤ S.Γ ⊓ Subgroup.centralizer ({(u : ModGL Tag.E8 L)} : Set (ModGL Tag.E8 L)) ∧
        CFSG.IsQuasisimple R ∧ ¬ Nat.Coprime 5 (Nat.card R) := by
  obtain ⟨a, a', γ, ha, haE, ha'E, hγ, hχa, hχa'⟩ :=
    exists_starWitness S hFr hΦ hn hMΓ hq5 hvc huT hu5 hvu
  have ha1 : rootDiagUnit Tag.E8 a ≠ 1 := by
    rw [ha]
    exact fun h => hu1 (Subtype.ext h)
  let i : KernelComponent (rootCharHom a) := ⟦⟨γ, ⟨hγ, hχa⟩⟩⟧
  have hγi : γ ∈ componentRoots (rootCharHom a) i := ⟨⟨hγ, hχa⟩, rfl⟩
  have hbig := bigComponent_of_star (S := S) hFr hΦ hn (Or.inr (Or.inr (Or.inr rfl)))
    hw4 (by norm_num) hMΓ ha'E hγ hχa hχa' i hγi
  obtain ⟨hsub, hin, hsu, htw, hex⟩ := t1_pieces
  obtain ⟨hLC, -⟩ := hsub Tag.E8 L 5 S a haE ha1 i
  have hLC' : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      S.Γ ⊓ Subgroup.centralizer ({(u : ModGL Tag.E8 L)} : Set (ModGL Tag.E8 L)) := by
    rw [← ha]
    exact hLC
  refine ⟨rationalComponent S.ρ S.Γ (rootCharHom a) i, hLC', ?_, hbig⟩
  cases hkind : twistKind S.ρ (rootCharHom a) i
  · exact hin Tag.E8 L 5 S a haE ha1 i hkind hbig
  · exact hsu Tag.E8 L 5 S a haE ha1 i hkind hbig
  · exact htw Tag.E8 L 5 S a haE ha1 i hkind hbig
  · exact hex Tag.E8 L 5 S a haE ha1 i hkind hbig

theorem exists_perfect_le_centralizer_of_commute_lift (S : LangSetup .E8 L 5) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ S.D.q) (hΦ : S.D.Φ = Units.map (entrywiseHom Fr))
    (hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) L e8PhiFourWeyl)
    (hw4 : ∀ δ : Fin Tag.E8.rank → ℤ, IsRoot Tag.E8 δ → e8PhiFourWeyl • e8PhiFourWeyl • δ = -δ)
    (hMΓ : S.D.model ≤ S.Γ) (hq5 : 5 ∣ S.D.q ^ 2 + 1) {v : ↥S.Γ}
    (hvc : ∀ a : Fin Tag.E8.rank → Lˣ,
      rootDiagUnit Tag.E8 a * (v : ModGL Tag.E8 L) =
        (v : ModGL Tag.E8 L) * rootDiagUnit Tag.E8 a ↔ z0 ∈ rootCharStabilizer a)
    {u : ↥S.Γ} (huT : (u : ModGL Tag.E8 L) ∈ S.D.torus) (hu1 : u ≠ 1) (hu5 : u ^ 5 = 1)
    (hvu : v * u = u * v) :
    ∃ R : Subgroup ↥S.Γ, R ≤ Subgroup.centralizer ({u} : Set ↥S.Γ) ∧ ⁅R, R⁆ = R ∧
      5 ∣ Nat.card R := by
  obtain ⟨R, hRle, hRq, hRnc⟩ :=
    exists_quasisimple_of_commute_lift S hFr hΦ hn hw4 hMΓ hq5 hvc huT hu1 hu5 hvu
  exact exists_perfect_le_centralizer_of_quasisimple_le Nat.prime_five (d := u) hRle hRq hRnc

end StarPerfect

section Torus

theorem exists_perfect_le_centralizer_of_torusPlane (S : LangSetup .E8 L 5)
    (hP : BigAnyPBig S) {D : Subgroup ↥S.Γ}
    (hDT : D ≤ S.D.torus.subgroupOf S.Γ) (hpow : ∀ x ∈ D, x ^ 5 = 1)
    (hcard : Nat.card D = 5 ^ 2) :
    ∃ d ∈ D, d ≠ 1 ∧ ∃ R : Subgroup ↥S.Γ,
      R ≤ Subgroup.centralizer ({d} : Set ↥S.Γ) ∧ ⁅R, R⁆ = R ∧ 5 ∣ Nat.card R := by
  classical
  set D' : Subgroup (ModGL Tag.E8 L) := D.map S.Γ.subtype with hD'
  have hD'T : D' ≤ S.D.torus := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hDT hx)
  have hD'Γ : D' ≤ S.Γ := Subgroup.map_subtype_le D
  have hD'pow : ∀ x ∈ D', x ^ 5 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hpow x hx, map_one]
  have hD'E : D' ≤ S.E := fun x hx =>
    S.E_all x (Subgroup.mem_inf.2 ⟨hD'T hx, hD'Γ hx⟩) (hD'pow x hx)
  have hD'card : Nat.card D' = 5 ^ 2 := by
    rw [hD', Subgroup.card_map_of_injective S.Γ.subtype_injective, hcard]
  obtain ⟨x, hx⟩ := bigComponentSet_nonempty_of_bigAnyPBig S hP hD'E hD'card
  obtain ⟨d', hd'D, hd'1, R, hRle, hRq, hRnc⟩ :=
    exists_quasisimple_of_mem_bigComponentSet S hD'E hx
  obtain ⟨d, hdD, rfl⟩ := hd'D
  exact ⟨d, hdD, fun h => hd'1 (by rw [h]; rfl),
    exists_perfect_le_centralizer_of_quasisimple_le Nat.prime_five (d := d) hRle hRq hRnc⟩

end Torus

section Main

theorem perfectCentralizerPlanes_adjointGroup_E8_four_five (K : Type) [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K ^ 2 + 1) :
    PerfectCentralizerPlanes 5 (adjointGroup Tag.E8 K) := by
  classical
  haveI : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_conjugator_E8 K e8PhiFourWeyl
  have hpq : ¬ 5 ∣ Nat.card K := not_five_dvd_of_dvd_sq_add_one h5
  obtain ⟨S, hS⟩ := exists_langSetup_ofFrobenius (Or.inr (Or.inr (Or.inr rfl)))
    e8PhiFourWeyl K hFr hg0C hg0 Nat.prime_five hpq (Or.inl le_rfl)
  have hFr' : ∀ c : AlgebraicClosure K, Fr c = c ^ S.D.q := by
    intro c
    rw [hS]
    exact hFr c
  have hq : S.D.q = Nat.card K := by rw [hS]; rfl
  have hΦ : S.D.Φ = Units.map (entrywiseHom Fr) := by rw [hS]; rfl
  have hn : S.D.n = canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8PhiFourWeyl := by
    rw [hS]; rfl
  have hMΓ : S.D.model ≤ S.Γ := by
    show S.D.model ≤ S.D.Γ
    rw [hS]
    exact model_le_Γ_ofFrobenius_E8 e8PhiFourWeyl K hFr hg0C hg0
  have hΓ : S.Γ = langModel Tag.E8 K (AlgebraicClosure K) g0 := by
    show S.D.Γ = langModel Tag.E8 K (AlgebraicClosure K) g0
    rw [hS]
    exact Γ_ofFrobenius_eq_langModel_exc (Or.inr (Or.inr (Or.inr rfl))) e8PhiFourWeyl K hFr
      hg0C hg0
  let φ : adjointGroup Tag.E8 K ≃* ↥S.Γ :=
    (langModelMulEquiv Tag.E8 K (AlgebraicClosure K) g0).trans (MulEquiv.subgroupCongr hΓ.symm)
  have hcardΓ : Nat.card ↥S.Γ = Nat.card (adjointGroup Tag.E8 K) :=
    (Nat.card_congr φ.toEquiv).symm
  have hcardT₁ : Nat.card ↥(S.D.torus.subgroupOf S.Γ) = Nat.card ↥S.D.torus :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (torus_le_Γ S hMΓ)).toEquiv
  have hcardT₂ : Nat.card ↥S.D.torus =
      ((wordMat Tag.E8 e8FourWord).charpoly.eval (Nat.card K : ℤ)).natAbs := by
    rw [show S.D.torus = twistedTorus (canonicalRep (coxeterSystem Tag.E8)
      (AlgebraicClosure K) e8PhiFourWeyl) Fr from by rw [hS]; rfl]
    exact card_twistedTorus_E8_four K hFr
  have hcardT : Nat.card ↥(S.D.torus.subgroupOf S.Γ) =
      ((wordMat Tag.E8 e8FourWord).charpoly.eval (Nat.card K : ℤ)).natAbs :=
    hcardT₁.trans hcardT₂
  have hord : (Nat.card ↥S.Γ).factorization 5 =
      (Nat.card ↥(S.D.torus.subgroupOf S.Γ)).factorization 5 + 1 := by
    rw [hcardΓ, hcardT]
    exact factorization_card_adjointE8_eq_torus_add_one K h5
  haveI := S.finite_Γ
  have hP : BigAnyPBig S :=
    bigAnyPBig_of_phi4_of_ne_two (S := S) hFr' hΦ hn (Or.inr (Or.inr (Or.inr rfl)))
      (fun δ _ => e8PhiFourWeyl_sq_smul δ) (by norm_num) hMΓ
  have hT : ∀ D₁ : Subgroup ↥S.Γ, D₁ ≤ S.D.torus.subgroupOf S.Γ →
      (∀ x ∈ D₁, x ^ 5 = 1) → Nat.card D₁ = 5 ^ 2 →
      ∃ d ∈ D₁, d ≠ 1 ∧ ∃ R : Subgroup ↥S.Γ,
        R ≤ Subgroup.centralizer ({d} : Set ↥S.Γ) ∧ ⁅R, R⁆ = R ∧ 5 ∣ Nat.card R :=
    fun D₁ hDT hpow hcard => exists_perfect_le_centralizer_of_torusPlane S hP hDT hpow hcard
  obtain ⟨v, hvT, hvp, hvn, hvc⟩ := exists_lift_Γ S hFr' hΦ hn hMΓ
  let T : Subgroup ↥S.Γ := S.D.torus.subgroupOf S.Γ
  have hTc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    apply Subtype.ext
    exact E8Lift.torusGroup_mul_comm ((mem_torus_iff S).1 (Subgroup.mem_subgroupOf.1 hx)).1
      ((mem_torus_iff S).1 (Subgroup.mem_subgroupOf.1 hy)).1
  have hvT' : ∀ t ∈ T, v * t * v⁻¹ ∈ T := by
    intro t ht
    exact Subgroup.mem_subgroupOf.2 (hvT t (Subgroup.mem_subgroupOf.1 ht))
  have hvp' : v ^ 5 ∈ T := Subgroup.mem_subgroupOf.2 hvp
  have hvn' : v ∉ T := fun h => hvn (Subgroup.mem_subgroupOf.1 h)
  have hq5 : 5 ∣ S.D.q ^ 2 + 1 := by rw [hq]; exact h5
  have hstar : ∀ u ∈ T, u ≠ 1 → u ^ 5 = 1 →
      (∃ k : ℕ, ¬ 5 ∣ k ∧ v ^ k * u = u * v ^ k) →
      ∃ R : Subgroup ↥S.Γ, R ≤ Subgroup.centralizer ({u} : Set ↥S.Γ) ∧ ⁅R, R⁆ = R ∧
        5 ∣ Nat.card R := by
    intro u huT hu1 hu5 hk
    obtain ⟨k, hk5, hvu⟩ := hk
    have h5c : v ^ 5 * u = u * v ^ 5 := hTc _ hvp' _ huT
    have hvu' : v * u = u * v := commute_of_pow_commute Nat.prime_five hk5 hvu h5c
    exact exists_perfect_le_centralizer_of_commute_lift S hFr' hΦ hn
      (fun δ _ => e8PhiFourWeyl_sq_smul δ) hMΓ hq5 hvc (Subgroup.mem_subgroupOf.1 huT) hu1 hu5 hvu'
  have hplanes : PerfectCentralizerPlanes 5 ↥S.Γ :=
    PerfectCentralizerPlanes.of_dichotomy Nat.prime_five T hTc v hvT' hvp' hvn' hord hT hstar
  exact PerfectCentralizerPlanes.of_mulEquiv φ.symm hplanes

end Main

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
