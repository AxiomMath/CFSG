module

public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CH

open CFSG.Open
open scoped MatrixGroups

section Lift

theorem nonempty_equiv_quotient_of_odd_ker {L S : Type} [Group L] [Finite L] [Group S]
    (φ : L →* S) (hφ : Function.Surjective φ) (hodd : Odd (Nat.card φ.ker))
    (e : S ≃* SL(2, ZMod 3)) :
    Nonempty (L ⧸ classicalInvolutionOddCore L ≃* SL(2, ZMod 3)) := by
  have : Finite S := Finite.of_surjective φ hφ
  have hOS : classicalInvolutionOddCore S = ⊥ := by
    have h1 := CFSG.ComponentClassification.OddCore.equiv_invariant e
    have h2 : componentClassificationOddCore SL(2, ZMod 3) = ⊥ := componentOddCore_sl2Three
    rw [h2] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h1
  have hle : φ.ker ≤ classicalInvolutionOddCore L :=
    CFSG.ComponentClassification.OddCore.maximal L φ.ker φ.normal_ker hodd
  have hge : classicalInvolutionOddCore L ≤ φ.ker := by
    have hN : ((classicalInvolutionOddCore L).map φ).Normal :=
      Subgroup.Normal.map inferInstance φ hφ
    have hNodd : Odd (Nat.card ((classicalInvolutionOddCore L).map φ)) :=
      (CFSG.ComponentClassification.OddCore.odd_card L).of_dvd_nat
        (Subgroup.card_map_dvd (classicalInvolutionOddCore L) φ)
    have h1 : (classicalInvolutionOddCore L).map φ ≤ classicalInvolutionOddCore S :=
      CFSG.ComponentClassification.OddCore.maximal S _ hN hNodd
    rw [hOS, le_bot_iff] at h1
    intro x hx
    have h2 : φ x ∈ (classicalInvolutionOddCore L).map φ := ⟨x, hx, rfl⟩
    rw [h1] at h2
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp h2)
  have heq : classicalInvolutionOddCore L = φ.ker := le_antisymm hge hle
  exact ⟨(QuotientGroup.quotientMulEquivOfEq heq).trans
    ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).trans e)⟩

end Lift

section Layer

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_zpowers_of_pow_four {t : X} (h : t ^ 4 = 1) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  have h4 : orderOf t ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one (by norm_num [h])
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
  exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])

theorem exists_mem_centralizer_lift {w : X} (hw : w ^ 4 = 1)
    {y : X ⧸ classicalInvolutionOddCore X}
    (hy : y ∈ Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore X) w} :
      Set (X ⧸ classicalInvolutionOddCore X))) :
    ∃ x ∈ Subgroup.centralizer ({w} : Set X),
      QuotientGroup.mk' (classicalInvolutionOddCore X) x = y := by
  have hP : IsPGroup 2 (Subgroup.zpowers w) := isPGroup_zpowers_of_pow_four hw
  have : Fact (IsPGroup 2 (Subgroup.zpowers w)) := ⟨hP⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (classicalInvolutionOddCore X)) :=
    CFSG.ComponentClassification.OddCore.odd_card X
  have hcop : Nat.Coprime 2 (Nat.card (classicalInvolutionOddCore X)) :=
    Nat.coprime_two_left.mpr hodd
  have h := CFSG.centralizer_map_quotient_eq_map_centralizer 2 (Subgroup.zpowers w)
    (classicalInvolutionOddCore X) inferInstance hcop
  have hz : ∀ {G : Type} [Group G] (a : G), Subgroup.centralizer (Subgroup.zpowers a : Set G) =
      Subgroup.centralizer ({a} : Set G) := fun a => by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hmap : (Subgroup.zpowers w).map (QuotientGroup.mk' (classicalInvolutionOddCore X)) =
      Subgroup.zpowers (QuotientGroup.mk' (classicalInvolutionOddCore X) w) :=
    MonoidHom.map_zpowers _ _
  simp only [hmap, hz] at h
  rw [h] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨x, hx, hxy⟩

@[expose] def layerOf (w : X) (Lb : Subgroup (X ⧸ classicalInvolutionOddCore X)) : Subgroup X :=
  Subgroup.centralizer ({w} : Set X) ⊓ Lb.comap (QuotientGroup.mk' (classicalInvolutionOddCore X))

theorem mem_layerOf_iff {w x : X} {Lb : Subgroup (X ⧸ classicalInvolutionOddCore X)} :
    x ∈ layerOf w Lb ↔ x ∈ Subgroup.centralizer ({w} : Set X) ∧
      QuotientGroup.mk' (classicalInvolutionOddCore X) x ∈ Lb := Iff.rfl

theorem layerOf_le_centralizer (w : X) (Lb : Subgroup (X ⧸ classicalInvolutionOddCore X)) :
    layerOf w Lb ≤ Subgroup.centralizer ({w} : Set X) := inf_le_left

theorem normal_layerOf {w : X} {Lb : Subgroup (X ⧸ classicalInvolutionOddCore X)}
    (hLn : ∀ x ∈ Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore X) w} :
      Set (X ⧸ classicalInvolutionOddCore X)), ∀ y ∈ Lb, x * y * x⁻¹ ∈ Lb) :
    ((layerOf w Lb).subgroupOf (Subgroup.centralizer ({w} : Set X))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (layerOf_le_centralizer w Lb)]
  intro h k hh hk
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hh.1) (Subgroup.inv_mem _ hk), ?_⟩
  have hkc : QuotientGroup.mk' (classicalInvolutionOddCore X) k ∈ Subgroup.centralizer
      ({QuotientGroup.mk' (classicalInvolutionOddCore X) w} :
        Set (X ⧸ classicalInvolutionOddCore X)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hk]
  have := hLn _ hkc _ hh.2
  simpa [map_mul, map_inv] using this

theorem nonempty_equiv_layerOf {w : X} (hw : w ^ 4 = 1)
    {Lb : Subgroup (X ⧸ classicalInvolutionOddCore X)}
    (hLc : Lb ≤ Subgroup.centralizer ({QuotientGroup.mk' (classicalInvolutionOddCore X) w} :
      Set (X ⧸ classicalInvolutionOddCore X)))
    (hLiso : Nonempty (Lb ≃* SL(2, ZMod 3))) :
    Nonempty (↥(layerOf w Lb) ⧸ classicalInvolutionOddCore ↥(layerOf w Lb) ≃*
      SL(2, ZMod 3)) := by
  obtain ⟨e⟩ := hLiso
  let φ0 : ↥(layerOf w Lb) →* (X ⧸ classicalInvolutionOddCore X) :=
    (QuotientGroup.mk' (classicalInvolutionOddCore X)).comp (layerOf w Lb).subtype
  let φ : ↥(layerOf w Lb) →* Lb := φ0.codRestrict Lb (fun x => x.2.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨b, hb⟩
    obtain ⟨x, hx, hxb⟩ := exists_mem_centralizer_lift hw (hLc hb)
    exact ⟨⟨x, hx, Subgroup.mem_comap.mpr (by rw [hxb]; exact hb)⟩, Subtype.ext hxb⟩
  have hodd : Odd (Nat.card φ.ker) := by
    have hle : φ.ker.map (layerOf w Lb).subtype ≤ classicalInvolutionOddCore X := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : QuotientGroup.mk' (classicalInvolutionOddCore X) (x : X) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.ker_mk' _).le (MonoidHom.mem_ker.mpr h1)
    have hc : Nat.card (φ.ker.map (layerOf w Lb).subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
    rw [← hc]
    exact (CFSG.ComponentClassification.OddCore.odd_card X).of_dvd_nat
      (Subgroup.card_dvd_of_le hle)
  exact nonempty_equiv_quotient_of_odd_ker φ hφ hodd e

end Layer

end CFSG.ClassicalInvolution.Q3.Q3CH
