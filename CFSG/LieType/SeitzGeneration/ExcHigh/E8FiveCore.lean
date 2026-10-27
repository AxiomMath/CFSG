module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.KillsRootGroup
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Pilot
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralSevenProved
public import CFSG.LieType.SeitzGeneration.ExcHigh.NativeCond
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch11SecOE5B

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Malle.SeitzCube


section Datum

theorem e8Five_regular_datum {K : Type} [Field K] [Finite K] (hpK : ¬ 5 ∣ Nat.card K)
    {E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1)
    (hE₀c : Nat.card E₀ = 5 ^ 2) (hn : ¬ NormalizesRNative Tag.E8 K E₀) :
    ∃ D : LangPlaneData Tag.E8 K E₀, ∀ α, IsRoot Tag.E8 α → ¬ D.Kills α := by
  obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ :=
    (langToralPlane_of_bar Nat.prime_five planesToralBar_E8_five) K hpK E₀ hE₀p hE₀c
  refine ⟨⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩, fun α hα hk => hn (normalizesRNative_of_unip ?_)⟩
  exact langPlaneKillsRoot_E8 K E₀ ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ α hα hk

theorem normalizesRGroup_of_native {τ : Tag} {K : Type} [Field K]
    {E₀ : Subgroup (adjointGroup τ K)} (h : NormalizesRNative τ K E₀) :
    NormalizesRGroup (ringChar K) E₀ := by
  obtain ⟨R, hR1, hRp, hRn⟩ := h
  exact ⟨R, hR1, hRp, fun x hx => (map_conj_eq_iff_mem_normalizer R x).2 (hRn hx)⟩

end Datum

section Descent

theorem e8_exists_rational_of_lang {K : Type} [Field K] [Finite K]
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (w : WeylGroup Tag.E8) {g g' : ModGL Tag.E8 (AlgebraicClosure K)}
    (hg : g ∈ adjointGroup Tag.E8 (AlgebraicClosure K))
    (hg' : g' ∈ adjointGroup Tag.E8 (AlgebraicClosure K))
    (hgF : Units.map (entrywiseHom Fr) g =
      g * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w)
    (hg'F : Units.map (entrywiseHom Fr) g' =
      g' * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w) :
    ∃ e : adjointGroup Tag.E8 K,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL Tag.E8 K) = g' * g⁻¹ := by
  have hmem : g' * g⁻¹ ∈ adjointGroup Tag.E8 (AlgebraicClosure K) := mul_mem hg' (inv_mem hg)
  have hfix : Units.map (entrywiseHom Fr) (g' * g⁻¹) = g' * g⁻¹ := by
    rw [map_mul, map_inv, hg'F, hgF]
    group
  obtain ⟨e, he, hbe⟩ :=
    Subgroup.mem_map.1 (mem_map_baseChange_of_frobenius_fixed_E8 Fr hFr hmem hfix)
  exact ⟨⟨e, he⟩, hbe⟩

@[expose] def E8FrameDatumAt (K : Type) [Field K] (F : Subgroup (adjointGroup Tag.E8 K))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (w : WeylGroup Tag.E8) : Prop :=
  ∃ g ∈ adjointGroup Tag.E8 (AlgebraicClosure K),
    Units.map (entrywiseHom Fr) g =
      g * canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w ∧
    ∃ h : adjointGroup Tag.E8 K, ∀ y : adjointGroup Tag.E8 K, y ^ 5 = 1 →
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.E8 K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) w)
          (Units.map (entrywiseHom Fr))).map (MulAut.conj g).toMonoidHom →
      h * y * h⁻¹ ∈ F

theorem exists_conj_le_of_frameDatum {K : Type} [Field K] [Finite K]
    {F E₀ : Subgroup (adjointGroup Tag.E8 K)} (hE₀p : ∀ x ∈ E₀, x ^ 5 = 1)
    (D : LangPlaneData Tag.E8 K E₀) (hF : E8FrameDatumAt K F D.Fr D.w) :
    ∃ k : adjointGroup Tag.E8 K, E₀.map (MulAut.conj k).toMonoidHom ≤ F := by
  obtain ⟨g, hg, hgF, h, hh⟩ := hF
  obtain ⟨e, he⟩ := e8_exists_rational_of_lang D.Fr D.hFr D.w D.hg0C hg D.hg0 hgF
  refine ⟨h * e * D.c, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hmap : (MulAut.conj (h * e * D.c)).toMonoidHom x =
      h * (e * (D.c * x * D.c⁻¹) * e⁻¹) * h⁻¹ := by
    show (h * e * D.c) * x * (h * e * D.c)⁻¹ = _
    group
  rw [hmap]
  refine hh _ ?_ ?_
  · rw [conj_pow, conj_pow, hE₀p x hx]
    group
  · obtain ⟨t, ht, htb⟩ := Subgroup.mem_map.1 (D.hc x hx)
    refine Subgroup.mem_map.2 ⟨t, ht, ?_⟩
    have htb' : D.g0 * t * D.g0⁻¹ =
        baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((D.c * x * D.c⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K) := htb
    show g * t * g⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((e * (D.c * x * D.c⁻¹) * e⁻¹ : adjointGroup Tag.E8 K) : ModGL Tag.E8 K)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, he,
      ← htb']
    group

end Descent

end CFSG.LieType.SeitzGeneration.ExcHigh
