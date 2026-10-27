module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSetup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.BadThreeLang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE
open scoped Matrix MatrixGroups

theorem exists_perfect_le_centralizer_of_injective {G H : Type*} [Group G] [Group H]
    (ψ : G →* H) (hψ : Function.Injective ψ) {x : G} {R : Subgroup H}
    (hRrange : R ≤ ψ.range) (hRperf : ⁅R, R⁆ = R)
    (hRcent : R ≤ Subgroup.centralizer ({ψ x} : Set H)) :
    ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({x} : Set G) ∧ ⁅P, P⁆ = P ∧
      Nat.card P = Nat.card R := by
  refine ⟨R.comap ψ, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hψ
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hRcent (Subgroup.mem_comap.1 hy))
  · apply Subgroup.map_injective hψ
    rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self hRrange, hRperf]
  · rw [← Subgroup.card_map_of_injective hψ (K := R.comap ψ),
      Subgroup.map_comap_eq_self hRrange]

section LangModelRange


theorem range_conj_baseChange_eq_langModel {τ : Tag} {K L : Type} [Field K] [Field L]
    [Algebra K L] (c : adjointGroup τ K) (g0 : ModGL τ L) :
    (((MulAut.conj g0⁻¹).toMonoidHom.comp
        ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype)).comp
      (MulAut.conj c).toMonoidHom).range = langModel τ K L g0 := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj c).surjective,
    Subgroup.map_top, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.range_subtype,
    langModel]

end LangModelRange

section Gamma


theorem Γ_ofFrobenius_eq_langModel_exc {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (w : WeylGroup τ) (K : Type) [Field K]
    [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w) :
    (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).Γ =
      langModel τ K (AlgebraicClosure K) g0 := by
  rw [(langDescent_ofFrobenius hτ w K hFr hg0C hg0).Γ_eq,
    MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

end Gamma

section LangSetupOfFrobenius


theorem exists_langSetup_ofFrobenius {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (w : WeylGroup τ) (K : Type) [Field K]
    [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) {g0 : ModGL τ (AlgebraicClosure K)}
    (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K) (hq : 5 ≤ p ∨ 4 ≤ Nat.card K) :
    ∃ S : LangSetup τ (AlgebraicClosure K) p,
      S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  let D : LangDatum τ (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0
  have hd : LangDescent D 7
      ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
        (adjointGroup τ K).subtype) :=
    langDescent_ofFrobenius hτ w K hFr hg0C hg0
  obtain ⟨ρ, hρ⟩ := frobeniusOnRoots_proved τ (AlgebraicClosure K) D
  have hK0 : ((Nat.card K : ℕ) : AlgebraicClosure K) = 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K)), Nat.card_eq_fintype_card,
      FiniteField.cast_card_eq_zero K, map_zero]
  have hqpow : IsPrimePow D.q ∧ ((D.q : ℕ) : AlgebraicClosure K) = 0 :=
    ⟨by rw [show D.q = Fintype.card K from Nat.card_eq_fintype_card]
        exact FiniteField.isPrimePow_card K, hK0⟩
  exact ⟨D.toSetup p ρ hρ hp hq hqpow hpK hd.finite_model, rfl⟩

end LangSetupOfFrobenius

section LangTorusPlane


theorem exists_perfect_le_centralizer_of_langTorus {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K) (hq : 5 ≤ p ∨ 4 ≤ Nat.card K) {A : Subgroup (adjointGroup τ K)}
    (hApow : ∀ x ∈ A, x ^ p = 1) (hAcard : Nat.card A = p ^ 2) (w : WeylGroup τ)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (c : adjointGroup τ K)
    (hc : ∀ x ∈ A, baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
      (twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
        (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom)
    (hbig : ∀ S : LangSetup τ (AlgebraicClosure K) p,
      S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 →
      ∀ D₁ : Subgroup (ModGL τ (AlgebraicClosure K)), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
        (bigComponentSet S D₁).Nonempty) :
    ∃ x ∈ A, x ≠ 1 ∧ ∃ P : Subgroup (adjointGroup τ K),
      P ≤ Subgroup.centralizer {x} ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P := by
  classical
  let D : LangDatum τ (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0
  have hΓ : D.Γ = langModel τ K (AlgebraicClosure K) g0 :=
    Γ_ofFrobenius_eq_langModel_exc hτ w K hFr hg0C hg0
  obtain ⟨S, hS⟩ := exists_langSetup_ofFrobenius hτ w K hFr hg0C hg0 hp hpK hq
  let ψ : adjointGroup τ K →* ModGL τ (AlgebraicClosure K) :=
    ((MulAut.conj g0⁻¹).toMonoidHom.comp
        ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
          (adjointGroup τ K).subtype)).comp
      (MulAut.conj c).toMonoidHom
  let D₁ : Subgroup (ModGL τ (AlgebraicClosure K)) := A.map ψ
  have hψinj : Function.Injective ψ :=
    (MulAut.conj g0⁻¹).injective.comp
      (((baseChangeGL_injective _).comp (Subgroup.subtype_injective _)).comp
        (MulAut.conj c).injective)
  have hD₁card : Nat.card D₁ = p ^ 2 := by
    change Nat.card (A.map ψ) = p ^ 2
    rw [Subgroup.card_map_of_injective hψinj, hAcard]
  have hD₁T : D₁ ≤ D.torus := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hc x hx
    change MulAut.conj g0⁻¹ (baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K)) ∈ D.torus
    rw [← hyx]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [show MulAut.conj g0⁻¹ (MulAut.conj g0 y) = y by
      simp only [MulAut.conj_apply, inv_inv]
      group]
    exact hy
  have hD₁Γ : D₁ ≤ D.Γ := by
    rw [hΓ]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K),
      ⟨(c * x * c⁻¹ : adjointGroup τ K), (c * x * c⁻¹).2, rfl⟩, rfl⟩
  have hD₁pow : ∀ x ∈ D₁, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hApow x hx, map_one]
  have hD₁E : D₁ ≤ S.E := fun x hx =>
    S.E_all x (by rw [hS]; exact ⟨hD₁T hx, hD₁Γ hx⟩) (hD₁pow x hx)
  obtain ⟨x, hxbig⟩ := hbig S hS D₁ hD₁E hD₁card
  obtain ⟨d, hdD, hd1, R, hRle, hRq, hRnc⟩ :=
    exists_quasisimple_of_mem_bigComponentSet S hD₁E hxbig
  have hSΓ : S.Γ = D.Γ := by
    change S.D.Γ = D.Γ
    rw [hS]
  have hRΓ : R ≤ D.Γ := fun r hr => hSΓ ▸ (Subgroup.mem_inf.1 (hRle hr)).1
  have hRcent : R ≤ Subgroup.centralizer ({d} : Set (ModGL τ (AlgebraicClosure K))) :=
    fun r hr => (Subgroup.mem_inf.1 (hRle hr)).2
  have hRperf : ⁅R, R⁆ = R := by
    haveI : Group.IsPerfect ↥R := hRq.1
    exact Subgroup.commutator_eq_self
  obtain ⟨a, haA, rfl⟩ := hdD
  have hRrange : R ≤ ψ.range := by
    rw [show ψ.range = langModel τ K (AlgebraicClosure K) g0 from
      range_conj_baseChange_eq_langModel c g0, ← hΓ]
    exact hRΓ
  obtain ⟨P, hPcent, hPperf, hPcard⟩ :=
    exists_perfect_le_centralizer_of_injective ψ hψinj hRrange hRperf hRcent
  refine ⟨a, haA, ?_, P, hPcent, hPperf, ?_⟩
  · intro ha1
    exact hd1 (by rw [ha1, map_one])
  · rw [hPcard]
    exact (Nat.Prime.dvd_iff_not_coprime hp).2 hRnc

theorem perfectCentralizerPlanes_adjointGroup_of_langTorus {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K) (hq : 5 ≤ p ∨ 4 ≤ Nat.card K) (W : WeylGroup τ → Prop)
    (htor : ∀ A : Subgroup (adjointGroup τ K), (∀ x ∈ A, x ^ p = 1) → Nat.card A = p ^ 2 →
      ∃ w, W w ∧ ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
        (∀ c, Fr c = c ^ Nat.card K) ∧ ∃ g0 ∈ adjointGroup τ (AlgebraicClosure K),
          Units.map (entrywiseHom Fr) g0 =
            g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
          ∃ c : adjointGroup τ K, ∀ x ∈ A,
            baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
              (twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
                (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom)
    (hbig : ∀ w, W w → ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K)
      (hFr : ∀ c, Fr c = c ^ Nat.card K) (g0 : ModGL τ (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
      (hg0 : Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
      (S : LangSetup τ (AlgebraicClosure K) p),
      S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 →
      ∀ D₁ : Subgroup (ModGL τ (AlgebraicClosure K)), D₁ ≤ S.E → Nat.card D₁ = p ^ 2 →
        (bigComponentSet S D₁).Nonempty) :
    PerfectCentralizerPlanes p (adjointGroup τ K) := by
  intro A hA hAcard
  obtain ⟨w, hW, Fr, hFr, g0, hg0C, hg0, c, hc⟩ := htor A hA.2 hAcard
  exact exists_perfect_le_centralizer_of_langTorus hτ hp hpK hq hA.2 hAcard w hFr hg0C
    hg0 c hc (fun S hS => hbig w hW Fr hFr g0 hg0C hg0 S hS)

theorem perfectCentralizerPlanes_adjointGroup_three {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (htor : LangToralPlane τ 3)
    (K : Type) [Field K] [Finite K]
    (h3 : ¬ 3 ∣ Nat.card K) (h4 : 4 ≤ Nat.card K) :
    PerfectCentralizerPlanes 3 (adjointGroup τ K) := by
  refine perfectCentralizerPlanes_adjointGroup_of_langTorus (W := fun _ => True)
    hτ K Nat.prime_three h3 (Or.inr h4) ?_ ?_
  · intro A hAp hAc
    obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ := htor K h3 A hAp hAc
    exact ⟨w, trivial, Fr, hFr, g0, hg0C, hg0, c, hc⟩
  · intro w _ Fr hFr g0 hg0C hg0 S hS D₁ hD₁ hc
    have hq4 : 4 ≤ S.D.q := by rw [hS]; exact h4
    exact bigComponentSet_nonempty_of_hasBigAnyComponent S
      (hasBigAnyComponent_of_threeBig threeBigComponents_holds S hq4 hD₁ hc)

end LangTorusPlane

section Neg


theorem bigComponentSet_nonempty_neg {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp2 : p ≠ 2) (hpd : p ∣ Nat.card K + 1) (hK4 : 4 ≤ Nat.card K)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {g0 : ModGL τ (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup τ (AlgebraicClosure K))
    (hg0 : Units.map (entrywiseHom Fr) g0 =
      g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (S : LangSetup τ (AlgebraicClosure K) p)
    (hS : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)
    {D₁ : Subgroup (ModGL τ (AlgebraicClosure K))} (hD₁ : D₁ ≤ S.E)
    (hc : Nat.card D₁ = p ^ 2) :
    (bigComponentSet S D₁).Nonempty := by
  have hΓ : (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0).Γ =
      langModel τ K (AlgebraicClosure K) g0 :=
    Γ_ofFrobenius_eq_langModel hτ w K hFr hg0C hg0
  obtain ⟨P, hPΓ, hPH, -⟩ :=
    exists_twistedSL2_rigid_neg hτ hw K (AlgebraicClosure K) hFr hK4 hg0C hg0 hΓ
  refine ⟨rootSL2 τ (AlgebraicClosure K) (Pi.single (0 : Fin τ.rank) 1)
    (conjSL (P 0) (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K))
      (1 : SL2 K))), ?_⟩
  exact mem_bigComponentSet_of_twistedSL2 S hp2 hD₁ hc hK4 hpd 0 (P 0)
    (fun A => by
      change rootSL2 τ (AlgebraicClosure K) (Pi.single (0 : Fin τ.rank) 1)
        (conjSL (P 0) (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) A)) ∈
          S.D.Γ
      rw [hS]
      exact hPΓ 0 A)
    (fun ζ hζ => hPH 0 ζ hζ) 1

end Neg

section NegPlanes


theorem perfectCentralizerPlanes_adjointGroup_neg {τ : Tag} (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8)
    {w : WeylGroup τ} (hw : ∀ u : Fin τ.rank → ℤ, w • u = -u) (K : Type) [Field K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ Nat.card K + 1) (hK4 : 4 ≤ Nat.card K)
    (htor : ∀ A : Subgroup (adjointGroup τ K), (∀ x ∈ A, x ^ p = 1) → Nat.card A = p ^ 2 →
      ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
        ∃ g0 ∈ adjointGroup τ (AlgebraicClosure K),
          Units.map (entrywiseHom Fr) g0 =
            g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
          ∃ c : adjointGroup τ K, ∀ x ∈ A,
            baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
              (twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
                (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom) :
    PerfectCentralizerPlanes p (adjointGroup τ K) := by
  have hpK : ¬ p ∣ Nat.card K :=
    fun h => hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 hpd))
  have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := hτ.imp_right Or.inr
  refine perfectCentralizerPlanes_adjointGroup_of_langTorus (W := fun w' => w' = w)
    hτ' K hp hpK (Or.inr hK4) ?_ ?_
  · intro A hAp hAc
    obtain ⟨Fr, hFr, g0, hg0C, hg0, c, hc⟩ := htor A hAp hAc
    exact ⟨w, rfl, Fr, hFr, g0, hg0C, hg0, c, hc⟩
  · intro w' hw' Fr hFr g0 hg0C hg0 S hS D₁ hD₁ hc
    subst hw'
    exact bigComponentSet_nonempty_neg hτ hw K hp2 hpd hK4 hFr hg0C hg0 S hS hD₁ hc

end NegPlanes

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
