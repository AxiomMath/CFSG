module

public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Defs

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcHighThree

set_option linter.unusedSectionVars false

section Toral


theorem nonempty_langPlaneData_of_toral {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hpK : ¬ p ∣ Nat.card K) (A : Subgroup (adjointGroup Tag.E8 K))
    (hAp : ∀ x ∈ A, x ^ p = 1)
    (htor : ∃ g ∈ adjointGroup Tag.E8 (AlgebraicClosure K), ∀ x ∈ A,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL Tag.E8 K) * g ∈
        torusGroup Tag.E8 (AlgebraicClosure K)) :
    Nonempty (LangPlaneData Tag.E8 K A) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have : CharP K (ringChar K) := ringChar.charP K
  set ℓ := ringChar K with hℓdef
  have hq : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have he : 1 ≤ (f : ℕ) := f.pos
  set L := AlgebraicClosure K with hLdef
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hpq : Nat.Coprime p (ℓ ^ (f : ℕ)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (hq ▸ hpK)
  set ι : K →+* L := algebraMap K L with hι
  obtain ⟨g, hgG, hg⟩ := htor
  have hT : ∀ x : A, g⁻¹ * baseChangeGL ι (x : ModGL Tag.E8 K) * g ∈ torusGroup Tag.E8 L :=
    fun x => hg _ x.2
  choose a ha using fun x : A => exists_rootDiagUnit_eq_of_mem_torusGroup (hT x)
  have hexp : ∀ (x : A) i, a x i ^ p = 1 := by
    intro x
    have h1 : rootDiagUnit Tag.E8 (a x ^ p) = rootDiagUnit Tag.E8 1 := by
      have : rootDiagUnit Tag.E8 (a x ^ p) = rootDiagUnit Tag.E8 (a x) ^ p :=
        ((rootDiagUnitHom Tag.E8 L).map_pow (a x) p)
      rw [this, ← ha x, rootDiagUnit_one]
      calc (g⁻¹ * baseChangeGL ι (x : ModGL Tag.E8 K) * g) ^ p
          = g⁻¹ * (baseChangeGL ι (x : ModGL Tag.E8 K)) ^ p * g := by
            have := conj_pow (a := g⁻¹) (b := baseChangeGL ι (x : ModGL Tag.E8 K)) (i := p)
            rwa [inv_inv] at this
        _ = 1 := by
            rw [← map_pow]
            have : (x : ModGL Tag.E8 K) ^ p = 1 := congrArg Subtype.val (hAp x x.2)
            rw [this, map_one]
            group
    have h2 : a x ^ p = 1 := CFSG.LieType.Chevalley.rootDiagUnit_injective h1
    exact fun i => congrFun h2 i
  have hFix : ∀ y : ModGL Tag.E8 K,
      entrywiseFrobGL Tag.E8 L ℓ (f : ℕ) (baseChangeGL ι y) = baseChangeGL ι y := by
    intro y
    have hcomp : (iterateFrobenius L ℓ (f : ℕ)).comp ι = ι := by
      refine RingHom.ext fun c => ?_
      change (iterateFrobenius L ℓ f) (ι c) = ι c
      rw [iterateFrobenius_def, ← map_pow]
      congr 1
      rw [← hf]
      exact FiniteField.pow_card c
    rw [entrywiseFrobGL, CFSG.LieType.Chevalley.units_map_entrywiseHom_eq_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomp]
  have hn : ∀ x : A, (g⁻¹ * entrywiseFrobGL Tag.E8 L ℓ (f : ℕ) g) *
      entrywiseFrobGL Tag.E8 L ℓ (f : ℕ) (rootDiagUnit Tag.E8 (a x)) *
      (g⁻¹ * entrywiseFrobGL Tag.E8 L ℓ (f : ℕ) g)⁻¹ = rootDiagUnit Tag.E8 (a x) := by
    intro x
    rw [← ha x, map_mul, map_mul, map_inv, hFix x]
    group
  obtain ⟨w', z, hz, hlang⟩ := exists_lang_datum_of_plane ℓ (f : ℕ) he hpq a hexp hgG hn
  have hzC := familyGroup_le_familyCentralizer (K := L) a hz
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 hzC
  have hu : entrywiseFrobGL Tag.E8 L ℓ (f : ℕ) (g * z) =
      (g * z) * canonicalRep (coxeterSystem Tag.E8) L w' := inv_mul_eq_iff_eq_mul.1 hlang
  refine ⟨⟨w', iterateFrobenius L ℓ (f : ℕ), fun c => ?_, g * z, mul_mem hgG hzG, hu, 1, ?_⟩⟩
  · rw [iterateFrobenius_def, hq]
  · intro x hx
    set xA : A := ⟨x, hx⟩ with hxA
    set d := rootDiagUnit Tag.E8 (a xA) with hd
    have hzd : z⁻¹ * d * z = d := by
      have := hzcomm xA
      rw [← hd, mul_inv_eq_iff_eq_mul] at this
      calc z⁻¹ * d * z = z⁻¹ * (d * z) := by group
        _ = z⁻¹ * (z * d) := by rw [this]
        _ = d := by group
    have ht : (g * z)⁻¹ * baseChangeGL ι (x : ModGL Tag.E8 K) * (g * z) = d := by
      calc (g * z)⁻¹ * baseChangeGL ι (x : ModGL Tag.E8 K) * (g * z)
          = z⁻¹ * (g⁻¹ * baseChangeGL ι (x : ModGL Tag.E8 K) * g) * z := by group
        _ = d := by rw [ha xA, hzd]
    refine ⟨(g * z)⁻¹ * baseChangeGL ι (x : ModGL Tag.E8 K) * (g * z), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_twistedTorusOf, ht]
      refine ⟨rootDiagUnit_mem_torusGroup _, ?_⟩
      have hfx : entrywiseFrobGL Tag.E8 L ℓ (f : ℕ) (baseChangeGL ι (x : ModGL Tag.E8 K)) =
          baseChangeGL ι (x : ModGL Tag.E8 K) := hFix _
      have hFd : entrywiseFrobGL Tag.E8 L ℓ (f : ℕ) d =
          (canonicalRep (coxeterSystem Tag.E8) L w')⁻¹ * d *
            canonicalRep (coxeterSystem Tag.E8) L w' := by
        rw [← ht, map_mul, map_mul, map_inv, hfx, hu]
        group
      change canonicalRep (coxeterSystem Tag.E8) L w' * entrywiseFrobGL Tag.E8 L ℓ (f : ℕ) d *
        (canonicalRep (coxeterSystem Tag.E8) L w')⁻¹ = d
      rw [hFd]
      group
    · change (g * z) * ((g * z)⁻¹ * baseChangeGL ι (x : ModGL Tag.E8 K) * (g * z)) *
        (g * z)⁻¹ = baseChangeGL ι ((1 * x * 1⁻¹ : ↥(adjointGroup Tag.E8 K)) : ModGL Tag.E8 K)
      simp only [one_mul, inv_one, mul_one]
      group

end Toral

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
