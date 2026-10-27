module

public import CFSG.RankThree.PartOne.KE8F.Stab5
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveSylowGroup
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSE8Five

namespace Four

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE8F CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley Matrix

set_option linter.unusedSectionVars false


section Count

variable {L : Type} [Field L] {Fr : L →+* L} {q : ℕ}

theorem exists_finset_torsion_commute_aux (hFr : ∀ c, Fr c = c ^ q) {ζ : Lˣ}
    (hζ : orderOf ζ = 5) (B : (Fin 4 → ZMod 5) → Fin Tag.E8.rank → ZMod 5)
    (hB : ∀ z : Fin Tag.E8.rank → ZMod 5, e8Vt5 *ᵥ z = (q : ZMod 5) • z →
      z = B ![z 4, z 5, z 6, z 7])
    (hBcard : Set.ncard {a : Fin 4 → ZMod 5 | cTrans *ᵥ B a = B a} ≤ 5)
    {y : ModGL .E8 L} (hy : y ∈ monomialSubgroup .E8 L) {w : WeylGroup .E8}
    (hyw : weylQuotientHom .E8 L ⟨y, hy⟩ = w) (hw : w ∈ Subgroup.zpowers cElt) (hw1 : w ≠ 1) :
    ∃ s : Finset (ModGL .E8 L), s.card ≤ 5 ∧
      ∀ a ∈ (fixedCharTuples e8P4V Fr).map (rootDiagUnitHom .E8 L),
        a ^ 5 = 1 → a * y = y * a → a ∈ s := by
  classical
  set Fixed : Set (Fin 4 → ZMod 5) := {a : Fin 4 → ZMod 5 | cTrans *ᵥ B a = B a} with hFixed
  have hfin : Fixed.Finite := Set.toFinite _
  let Dg : (Fin 4 → ZMod 5) → ModGL .E8 L := fun a' =>
    rootDiagUnit .E8 (fun i => ζ ^ (B a' i).val)
  refine ⟨hfin.toFinset.image Dg, Finset.card_image_le.trans ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card Fixed hfin]
    exact hBcard
  intro a ha ha5 hcomm
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
  have hprim : IsPrimitiveRoot (ζ : L) 5 :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hζ)
  have hb5 : ∀ i, b i ^ 5 = 1 := by
    have h1 : rootDiagUnit .E8 (b ^ 5) = 1 := by
      have hpow : rootDiagUnit .E8 b ^ 5 = rootDiagUnit .E8 (b ^ 5) :=
        ((rootDiagUnitHom .E8 L).map_pow b 5).symm
      rw [← hpow]
      exact ha5
    have h2 : b ^ 5 = 1 := rootDiagUnit_injective (h1.trans rootDiagUnit_one.symm)
    exact fun i => congrFun h2 i
  have hexp : ∀ i, ∃ n : ℕ, b i = ζ ^ n := fun i => by
    have hi : ((b i : Lˣ) : L) ^ 5 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hb5 i, Units.val_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hi
    exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩
  choose e he using hexp
  set z : Fin Tag.E8.rank → ZMod 5 := fun i => (e i : ZMod 5) with hz
  have hzeig : e8Vt5 *ᵥ z = (q : ZMod 5) • z :=
    eigen_of_fixedChar hFr hζ hb he (fun i => rfl)
  have hconj : y * rootDiagUnit .E8 b * y⁻¹ = rootDiagUnit .E8 b := by
    have h1 : y * rootDiagUnit .E8 b = rootDiagUnit .E8 b * y := hcomm.symm
    rw [h1]
    group
  have hact := CFSG.HardMathSupport.Timmesfeld.Tables.T1b.monomial_conj_rootDiagUnit
    (⟨y, hy⟩ : monomialSubgroup .E8 L) b
  rw [hyw] at hact
  have heq : CFSG.HardMathSupport.Timmesfeld.Tables.T1b.weylAct w b = b :=
    rootDiagUnit_injective (hact.symm.trans hconj)
  have hchar : ∀ u, rootChar b (w⁻¹ • u) = rootChar b u := fun u => by
    have := congrArg (fun b' => rootChar b' u) heq
    simpa [CFSG.HardMathSupport.Timmesfeld.Tables.T1b.rootChar_weylAct] using this
  have hstab : w⁻¹ ∈ dualWeylStabilizer z := fun u =>
    (rootChar_eq_rootChar_iff hζ e b he (w⁻¹ • u) u).1 (hchar u)
  have hwz : w ∈ dualWeylStabilizer z := by simpa using inv_mem hstab
  have hcz : cTrans *ᵥ z = z := cTrans_mulVec_eq_self hw hw1 hwz
  have hz4 : z = B ![z 4, z 5, z 6, z 7] := hB z hzeig
  have hmem : ![z 4, z 5, z 6, z 7] ∈ Fixed := by
    show cTrans *ᵥ B ![z 4, z 5, z 6, z 7] = B ![z 4, z 5, z 6, z 7]
    rw [← hz4]
    exact hcz
  refine Finset.mem_image.2 ⟨_, hfin.mem_toFinset.2 hmem, ?_⟩
  show rootDiagUnit .E8 (fun i => ζ ^ (B ![z 4, z 5, z 6, z 7] i).val) = rootDiagUnit .E8 b
  rw [← hz4]
  congr 1
  funext i
  rw [he i]
  show ζ ^ ((e i : ZMod 5)).val = ζ ^ e i
  rw [ZMod.val_natCast, ← hζ, pow_mod_orderOf]

theorem exists_finset_torsion_commute (hFr : ∀ c, Fr c = c ^ q)
    (hq5 : (q : ZMod 5) = 2 ∨ (q : ZMod 5) = 3) {ζ : Lˣ} (hζ : orderOf ζ = 5)
    {y : ModGL .E8 L} (hy : y ∈ monomialSubgroup .E8 L) {w : WeylGroup .E8}
    (hyw : weylQuotientHom .E8 L ⟨y, hy⟩ = w) (hw : w ∈ Subgroup.zpowers cElt) (hw1 : w ≠ 1) :
    ∃ s : Finset (ModGL .E8 L), s.card ≤ 5 ∧
      ∀ a ∈ (fixedCharTuples e8P4V Fr).map (rootDiagUnitHom .E8 L),
        a ^ 5 = 1 → a * y = y * a → a ∈ s := by
  rcases hq5 with h | h
  · exact exists_finset_torsion_commute_aux hFr hζ eigTwo
      (fun z hz => eig_param2 (by rw [← h]; exact hz)) fixed_ncard_two hy hyw hw hw1
  · exact exists_finset_torsion_commute_aux hFr hζ eigThree
      (fun z hz => eig_param3 (by rw [← h]; exact hz)) fixed_ncard_three hy hyw hw hw1

end Count

section SylowCount

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] {ℓ f : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ] {F : E8P4Frame0 K L ℓ f} {m : ModGL .E8 L}

theorem ncard_sylow_fixed_le (hm : IsLift F m) {ζ : Lˣ} (hζ : orderOf ζ = 5)
    (hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ Nat.card K)
    (hq5 : ((Nat.card K : ℕ) : ZMod 5) = 2 ∨ ((Nat.card K : ℕ) : ZMod 5) = 3)
    (y : sylowGrp F m) (hy : sylowRho hm y ≠ 1) :
    Set.ncard {a : sylowGrp F m | sylowRho hm a = 1 ∧ a ^ 5 = 1 ∧ a * y = y * a} ≤ 5 := by
  obtain ⟨s, hs, hmem⟩ := exists_finset_torsion_commute (Fr := iterateFrobenius L ℓ f) hFr hq5 hζ
    (sylowGrp_le_monomial hm y.2) (sylowRho_apply hm y).symm (sylowRho_mem_zpowers hm y) hy
  have hsub : Subtype.val '' {a : sylowGrp F m | sylowRho hm a = 1 ∧ a ^ 5 = 1 ∧ a * y = y * a} ⊆
      (s : Set (ModGL .E8 L)) := by
    rintro _ ⟨a, ⟨ha1, ha5, hac⟩, rfl⟩
    refine hmem a ?_ ?_ ?_
    · have := (sylowRho_eq_one_iff hm a).1 ha1
      rwa [F.hT] at this
    · simpa using congrArg Subtype.val ha5
    · exact congrArg Subtype.val hac
  calc Set.ncard {a : sylowGrp F m | sylowRho hm a = 1 ∧ a ^ 5 = 1 ∧ a * y = y * a}
      = Set.ncard (Subtype.val '' {a : sylowGrp F m |
          sylowRho hm a = 1 ∧ a ^ 5 = 1 ∧ a * y = y * a}) :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ ≤ Set.ncard (s : Set (ModGL .E8 L)) := Set.ncard_le_ncard hsub s.finite_toSet
    _ = s.card := Set.ncard_coe_finset s
    _ ≤ 5 := hs

end SylowCount

end Four

end KSE8Five

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
