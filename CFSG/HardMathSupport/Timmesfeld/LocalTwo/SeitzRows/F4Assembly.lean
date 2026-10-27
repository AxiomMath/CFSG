module

public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows.F4ThreeEven
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.ExcInnerBase
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinear
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin

public section

namespace CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows

open Subgroup CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Chevalley.F4Weyl CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2 CFSG.LieType.SeitzGeneration
  CFSG.TauCetiBridge
open scoped commutatorElement

set_option linter.unusedSectionVars false


theorem f4_innerPlaneBalance_of_actor_of_coord {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (w : WeylGroup Tag.F4)
    (hcoord : ∀ F : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, F c = c ^ Nat.card K) →
      ∀ P : Subgroup (adjointGroup Tag.F4 K), IsPGroup p P →
      ∃ g ∈ adjointGroup Tag.F4 (AlgebraicClosure K),
        g⁻¹ * Units.map (entrywiseHom F) g =
          canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w ∧
        ∀ y ∈ P, ∃ x ∈ torusGroup Tag.F4 (AlgebraicClosure K) ⊓ conjEntrywiseImage K g⁻¹,
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL Tag.F4 K) = g * x * g⁻¹)
    (hact : ∀ F : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, F c = c ^ Nat.card K) →
      ∀ g : ModGL Tag.F4 (AlgebraicClosure K), g ∈ adjointGroup Tag.F4 (AlgebraicClosure K) →
      g⁻¹ * Units.map (entrywiseHom F) g =
        canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w →
      ∀ x ∈ torusGroup Tag.F4 (AlgebraicClosure K) ⊓ conjEntrywiseImage K g⁻¹, orderOf x = p →
        {α | IsRoot Tag.F4 α ∧ torusRootChar x α = 1}.Nonempty →
      ∀ x₁ : adjointGroup Tag.F4 K,
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₁ : ModGL Tag.F4 K) = g * x * g⁻¹ →
          F4FourActorAt K (AlgebraicClosure K) p g x x₁) :
    InnerPlaneBalance p (adjointGroup Tag.F4 K) := by
  classical
  intro E hEin hE hcard H hH
  have : Fact p.Prime := ⟨hp⟩
  have hinj := mulAut_conj_injective_adjointGroup (τ := Tag.F4) (K := K)
  obtain ⟨F, hF⟩ := exists_ringHom_pow_card K (AlgebraicClosure K)
  set Ω := AlgebraicClosure K with hΩ
  set P : Subgroup (adjointGroup Tag.F4 K) := E.comap
    (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)) with hP
  have hPmap : P.map (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)) =
      E := Subgroup.map_comap_eq_self hEin
  have hPcard : Nat.card P = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hinj, hPmap, hcard]
  have hPpow : ∀ y ∈ P, y ^ p = 1 := fun y hy => by
    apply hinj
    rw [map_pow, map_one]
    exact hE.2 _ hy
  obtain ⟨g, hg, hgn, hc⟩ := hcoord F hF P (IsPGroup.of_card hPcard)
  have hPT : ∀ y ∈ P, g⁻¹ * baseChangeGL (algebraMap K Ω) (y : ModGL Tag.F4 K) * g ∈
      torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹ := fun y hy => by
    obtain ⟨x, hx, hxy⟩ := hc y hy
    rw [hxy, show g⁻¹ * (g * x * g⁻¹) * g = x by group]
    exact hx
  have hbi : ∀ i : Fin Tag.F4.rank, ∃ b ∈ P, b ≠ 1 ∧
      torusRootChar (g⁻¹ * baseChangeGL (algebraMap K Ω) (b : ModGL Tag.F4 K) * g)
        (Pi.single i 1) = 1 := fun i => by
    let χ : P →* Ωˣ :=
      { toFun := fun y => Units.mk0 (torusRootChar (g⁻¹ * baseChangeGL (algebraMap K Ω)
            (((y : adjointGroup Tag.F4 K)) : ModGL Tag.F4 K) * g) (Pi.single i 1))
          (torusRootChar_ne_zero (torusGroup_le_diagonalGroup (hPT y y.2).1) _)
        map_one' := by
          apply Units.ext
          simp only [Subgroup.coe_one, map_one, mul_one, inv_mul_cancel, Units.val_mk0,
            Units.val_one]
          exact torusRootChar_one _
        map_mul' := fun a b => by
          apply Units.ext
          simp only [Subgroup.coe_mul, map_mul, Units.val_mk0, Units.val_mul]
          rw [show g⁻¹ * (baseChangeGL (algebraMap K Ω)
              ((a : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) *
                baseChangeGL (algebraMap K Ω)
                  ((b : adjointGroup Tag.F4 K) : ModGL Tag.F4 K)) * g =
              (g⁻¹ * baseChangeGL (algebraMap K Ω)
                ((a : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g) *
              (g⁻¹ * baseChangeGL (algebraMap K Ω)
                ((b : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g) by group]
          exact torusRootChar_mul (torusGroup_le_diagonalGroup (hPT a a.2).1)
            (torusGroup_le_diagonalGroup (hPT b b.2).1) _ }
    obtain ⟨a, ha1, hχa⟩ := exists_ne_one_map_eq_one_of_card_sq hp
      (fun a => Subtype.ext (by simpa using hPpow a a.2)) hPcard χ
    refine ⟨a, a.2, fun h => ha1 (Subtype.ext h), ?_⟩
    have h1 := congrArg Units.val hχa
    simpa [χ] using h1
  choose b hbP hb1 hbχ using hbi
  have hbx : ∀ i, ∃ x ∈ torusGroup Tag.F4 Ω ⊓ conjEntrywiseImage K g⁻¹,
      baseChangeGL (algebraMap K Ω) ((b i : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
        g * x * g⁻¹ := fun i => hc (b i) (hbP i)
  choose x hxT hxb using hbx
  have hbE : ∀ i, MulAut.conj (b i) ∈ E := fun i => hbP i
  set ι' : adjointGroup Tag.F4 K →* ModGL Tag.F4 Ω :=
    (baseChangeGL (algebraMap K Ω)).comp (adjointGroup Tag.F4 K).subtype with hι'
  have hι'inj : Function.Injective ι' :=
    (baseChangeGL_injective (τ := Tag.F4) (algebraMap K Ω)).comp Subtype.val_injective
  have hxe : ∀ i, g⁻¹ * baseChangeGL (algebraMap K Ω) ((b i : adjointGroup Tag.F4 K) :
      ModGL Tag.F4 K) * g = x i := fun i => by
    rw [hxb i]
    group
  have hxp : ∀ i, orderOf (x i) = p := fun i => by
    have hbp : orderOf (b i) = p := orderOf_eq_prime (hPpow _ (hbP i)) (hb1 i)
    rw [show x i = (MulAut.conj g⁻¹).toMonoidHom (ι' (b i)) by
        rw [← hxe i]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        rfl,
      orderOf_injective _ (MulAut.conj g⁻¹).injective, orderOf_injective ι' hι'inj, hbp]
  have hne : ∀ i, {α | IsRoot Tag.F4 α ∧ torusRootChar (x i) α = 1}.Nonempty := fun i =>
    ⟨Pi.single i 1, isRoot_single Tag.F4 i, by rw [← hxe i]; exact hbχ i⟩
  have hA := fun i => hact F hF g hg hgn (x i) (hxT i) (hxp i) (hne i) (b i) (hxb i)
  refine eq_bot_iff.2 fun z hz => ?_
  have hzi : ∀ i, ∃ c ∈ centralizer ({b i} : Set (adjointGroup Tag.F4 K)) ⊓
      centralizer ((⁅centralizer ({b i} : Set (adjointGroup Tag.F4 K)),
        centralizer ({b i} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup (adjointGroup Tag.F4 K)) :
          Set (adjointGroup Tag.F4 K)), z = MulAut.conj c := fun i => by
    obtain ⟨hq, hpR, hinn, -⟩ := hA i
    obtain ⟨hzb, hzR⟩ := fixes_of_mem_localDeltaIn hp hinj hH hz (hbE i) (hb1 i) hq hpR
    exact hinn z hzb hzR
  choose c hcmem hcz using hzi
  have hcc : ∀ i, c i = c 0 := fun i => hinj ((hcz i).symm.trans (hcz 0))
  have hy1 : g⁻¹ * baseChangeGL (algebraMap K Ω) ((c 0 : adjointGroup Tag.F4 K) :
      ModGL Tag.F4 K) * g = 1 := by
    refine eq_one_of_torusRootChar_single Ω ((hA 0).2.2.2 (c 0) (hcmem 0)).1 fun i => ?_
    have hmem : c 0 ∈ centralizer ({b i} : Set (adjointGroup Tag.F4 K)) ⊓
        centralizer ((⁅centralizer ({b i} : Set (adjointGroup Tag.F4 K)),
          centralizer ({b i} : Set (adjointGroup Tag.F4 K))⁆ : Subgroup
            (adjointGroup Tag.F4 K)) : Set (adjointGroup Tag.F4 K)) := hcc i ▸ hcmem i
    exact ((hA i).2.2.2 (c 0) hmem).2 (Pi.single i 1)
      ⟨isRoot_single Tag.F4 i, by rw [← hxe i]; exact hbχ i⟩
  have hc1 : c 0 = 1 := by
    apply hι'inj
    rw [map_one]
    change baseChangeGL (algebraMap K Ω) ((c 0 : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) = 1
    calc baseChangeGL (algebraMap K Ω) ((c 0 : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) =
          g * (g⁻¹ * baseChangeGL (algebraMap K Ω)
            ((c 0 : adjointGroup Tag.F4 K) : ModGL Tag.F4 K) * g) * g⁻¹ := by group
      _ = 1 := by rw [hy1]; group
  rw [hcz 0, hc1, map_one]
  exact one_mem _

theorem dvd_sq_add_self_add_one_of_orderOf_eq_three {p n : ℕ} (hp : p.Prime)
    (h : orderOf ((n : ℕ) : ZMod p) = 3) : p ∣ n ^ 2 + n + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ((n : ℕ) : ZMod p) ^ 3 = 1 := by
    rw [← h]
    exact pow_orderOf_eq_one _
  have h2 : ((n : ℕ) : ZMod p) ≠ 1 := fun h' => by
    rw [h', orderOf_one] at h
    omega
  have h3 : (((n : ℕ) : ZMod p) - 1) * (((n : ℕ) : ZMod p) ^ 2 + ((n : ℕ) : ZMod p) + 1) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h3 with h4 | h4
  · exact absurd (sub_eq_zero.1 h4) h2
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    exact h4

section Three


theorem innerPlaneBalance_adjointF4_three (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1) :
    InnerPlaneBalance p (adjointGroup Tag.F4 K) := by
  obtain ⟨ℓ, f, hℓ, -, hf, hK⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_char_card K
  refine f4_innerPlaneBalance_of_actor_of_coord hp hp3 (f4Coxeter ^ 4) ?_ ?_
  · intro F hF P hP
    exact exists_lang_torus_coordinates_three_six K (AlgebraicClosure K) F hF
      (Or.inl ⟨rfl, rfl, hpd⟩) hp hp3 P hP
  · intro F hF g hg hgn x hx hxp hne x₁ hx₁
    by_cases h2 : ℓ = 2
    · subst h2
      exact f4ThreeActor_even K (AlgebraicClosure K) F hf hK hF hp hp3 hpd hg hgn hx hxp hne hx₁
    · exact f4ThreeActor_odd K (AlgebraicClosure K) F hℓ h2 hf hK hF hp hp3 hpd hg hgn hx hxp hne
        hx₁

end Three

section TauCeti


theorem innerPlaneBalance_catF4_of_orderOf_three (q : TauCeti.PrimePower)
    (hv : (excIndex .F4 q).Valid) {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (he : orderOf ((q.card : ℕ) : ZMod p) = 3) :
    InnerPlaneBalance p (CatT ⟨excIndex .F4 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.f4 q hv
  have hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by
    rw [hK]
    exact dvd_sq_add_self_add_one_of_orderOf_eq_three hp he
  exact InnerPlaneBalance.of_mulEquiv e (innerPlaneBalance_adjointF4_three K hp (by omega) hpd)

theorem innerPlaneBalanceAt_F4_three : InnerPlaneBalanceAt .F4 3 :=
  fun q hv _ hp hp7 _ _ he => innerPlaneBalance_catF4_of_orderOf_three q hv hp hp7 he

end TauCeti


end CFSG.HardMathSupport.Timmesfeld.LocalTwo.SeitzRows
