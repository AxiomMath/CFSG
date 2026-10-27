module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BU8Mod
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GFldUniMark
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3UniRec
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265F3Lift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265BU8

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.S265 CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (FieldKind)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.BalanceLp (statedProjEquivPrimeFormP)
open scoped commutatorElement

theorem qUConcl_of_u8 {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x b : Ω}
    (cfg : QUCfg 3 S B T x b) (hF : FieldOn 3 b S) {labK : GLALabel}
    (hkind : FieldKind (PSimple 3 S) labK (indAut 3 S b hF.1))
    (hlab : labK = ⟨.twA, 4, 3⟩ ∨ labK = ⟨.twA, 5, 3⟩) (hB : 3 ^ 5 ≤ Nat.card B)
    (hTB : ¬ (⁅T, B⁆ : Subgroup Ω) ≤ Subgroup.centralizer (S : Set Ω)) : QUConcl 3 S B x b := by
  classical
  have hp := cfg.prime
  haveI := Fact.mk hp
  haveI := cfg.normal
  have hnorm : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g => by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hq : CFSG.Open.IsQuasisimple (PQuot 3 S) := isQuasisimple_pQuot_of_glaPComponent hp cfg.comp
  have hcen : Subgroup.center (PSimple 3 S) = ⊥ := Y10F.center_centerQuot_eq_bot hq
  obtain ⟨r, hr, rfl⟩ : ∃ r, (r = 4 ∨ r = 5) ∧ labK = ⟨.twA, r, 3⟩ := by
    rcases hlab with h | h
    · exact ⟨4, Or.inl rfl, h⟩
    · exact ⟨5, Or.inr rfl, h⟩
  obtain ⟨K, _, _, d, τ, hτ, hτq, hKcard, -, -, -, hrank, -, A, σ, u, e, hA, heu, hu, hσ⟩ :=
    Y10GFldUniMark.fieldKind_unitary_data hcen (Or.inl rfl) hkind
  obtain rfl : d = r + 1 := hrank.symm
  have h : UnitaryFieldData 2 3 K := ⟨Nat.prime_two, by norm_num, hKcard.trans (by norm_num)⟩
  have hd3 : 3 ≤ r + 1 := by omega
  have hq3 : ¬(r + 1 = 3 ∧ 2 ^ 3 = 2) := fun h' => by have := h'.1; omega
  have hαD := S265F3.congr_not_mem_primeFormD h hd3 hq3 hτq hA hσ e heu hu
  obtain ⟨e', he'⟩ : ∃ e' : PSimple 3 S ≃* primeFormP h (idGram K (r + 1)),
      e' = e.trans (statedProjEquivPrimeFormP h (by omega : 1 ≤ r + 1)) := ⟨_, rfl⟩
  rw [← he'] at hαD
  have hinv : chevAut 3 S ⟨b, hF.1⟩ = (indAut 3 S b hF.1)⁻¹ := by
    have h' : indAut 3 S b hF.1 = (chevAut 3 S ⟨b, hF.1⟩)⁻¹ := by
      rw [indAut, ← map_inv]
      rfl
    rw [h', inv_inv]
  have hβD : MulAut.congr e' (chevAut 3 S ⟨b, hF.1⟩) ∉ primeFormD h (idGram K (r + 1)) := by
    rw [hinv, map_inv, inv_mem_iff]
    exact hαD
  have hβ3 : chevAut 3 S ⟨b, hF.1⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 S hF.1 (cfg.elem.2 b cfg.hb)
  let Φ : Ω →* MulAut (PSimple 3 S) := (chevAut 3 S).comp ((MonoidHom.id Ω).codRestrict _ hnorm)
  have hΦ : ∀ g, Φ g = chevAut 3 S ⟨g, hnorm g⟩ := fun g => rfl
  have hkerB : (Φ.domRestrict B).ker.map B.subtype ≤ Subgroup.zpowers x := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 : chevAut 3 S ⟨(g : Ω), hnorm g⟩ = 1 := hg
    exact (cfg.centB g g.2).1 ((chevAut_eq_one_iff hp cfg.comp (hnorm g)).1 h1)
  have hxord : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (cfg.elem.2 x cfg.xB) cfg.x1
  have hk3 : Nat.card (Φ.domRestrict B).ker ≤ 3 := by
    rw [← Subgroup.card_map_of_injective B.subtype_injective]
    exact (Subgroup.card_le_of_le hkerB).trans hxord.le
  have hcardB := Subgroup.card_ker_mul_card_range (Φ.domRestrict B)
  rw [MonoidHom.domRestrict_range] at hcardB
  have h81 : 81 ≤ Nat.card (B.map Φ) := by
    have h2 : Nat.card ↥B ≤ 3 * Nat.card (B.map Φ) := by
      rw [← hcardB]
      exact Nat.mul_le_mul_right _ hk3
    omega
  have hTB2 : IsPGroup 2 (⁅T, B⁆ : Subgroup Ω) :=
    cfg.two.to_le (Subgroup.le_normalizer_iff_commutator_le_left.1 cfg.bnorm)
  obtain ⟨g₀, hg₀, hg₀S⟩ := SetLike.not_le_iff_exists.1 hTB
  have hΦg₀ : Φ g₀ ≠ 1 := fun h1 => hg₀S ((centMod_iff_centralizer cfg.core (hnorm g₀)).1
    ((chevAut_eq_one_iff hp cfg.comp (hnorm g₀)).1 h1))
  haveI : IsCyclic (K ≃+* K) := by
    obtain ⟨σ₀, -, -, htop, -⟩ := finite_field_automorphism_fixed_field_cardinality h.prime
      (by have := h.one_le; omega) h.card
    exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ₀, htop⟩
  have hff : ∀ g ∈ (⁅T, B⁆ : Subgroup Ω),
      MulAut.congr e' (Φ g) ∈ primeFormD h (idGram K (r + 1)) := by
    have hker := ker_primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := r + 1)) hd3 hq3
    let χ : Ω →* (K ≃+* K) :=
      (primeFormFieldFactor h (isPrimeFormGram_idGram (K := K) (n := r + 1)) hd3 hq3).comp
        ((MulAut.congr e').toMonoidHom.comp Φ)
    have hle : (⁅T, B⁆ : Subgroup Ω) ≤ χ.ker := by
      rw [Subgroup.commutator_le]
      intro t _ c _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact IsCyclic.isMulCommutative.is_comm.comm _ _
    intro g hg
    rw [← hker]
    exact hle hg
  have hcomm : ∀ g ∈ B, ∀ g' ∈ B, g * g' = g' * g := fun g hg g' hg' =>
    congrArg Subtype.val (cfg.elem.1.is_comm.comm ⟨g, hg⟩ ⟨g', hg'⟩)
  obtain ⟨_, ⟨e₀, he₀B, rfl⟩, hcβ, hlay⟩ :=
    exists_layer_of_u8_model h (by omega) e' hβ3 hβD (B.map Φ)
    (by
      rintro _ ⟨g, hg, rfl⟩
      rw [← map_pow, cfg.elem.2 g hg, map_one])
    (by
      rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
      rw [← map_mul, ← map_mul, hcomm g hg g' hg'])
    (by
      rintro _ ⟨g, hg, rfl⟩
      show Φ b * Φ g = Φ g * Φ b
      rw [← map_mul, ← map_mul, hcomm b cfg.hb g hg])
    h81 ((⁅T, B⁆ : Subgroup Ω).map Φ) (hTB2.map Φ)
    (fun h0 => hΦg₀ ((Subgroup.eq_bot_iff_forall _).1 h0 _ ⟨g₀, hg₀, rfl⟩))
    (by
      rintro _ ⟨g, hg, rfl⟩
      exact hff g hg)
    (by
      rintro _ ⟨c, hc, rfl⟩ _ ⟨g, hg, rfl⟩
      exact ⟨c * g * c⁻¹, (Subgroup.mem_normalizer_iff.1
        (Subgroup.normalizer_commutator_ge_right T B hc) g).1 hg,
        by rw [map_mul, map_mul, map_inv]⟩)
  have hΦx : Φ x = 1 := by
    rw [hΦ, chevAut_eq_one_iff hp cfg.comp]
    exact (cfg.centB x cfg.xB).2 (Subgroup.mem_zpowers x)
  have hDle : Dgrp b x ≤ (Subgroup.zpowers (Φ b)).comap Φ := by
    rw [dgrp_eq]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, hΦx]
      exact Subgroup.one_mem _
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap]
      exact Subgroup.mem_zpowers _
  have he₀D : e₀ ∉ Dgrp b x := fun hm => hcβ (hDle hm)
  have hne := S265F3.glaPLayer_inf_cx_ne_bot_of_fix hp cfg.core hF.1 (hnorm e₀) hlay
  have hSx : S ≤ Subgroup.centralizer ({x} : Set Ω) := fun s _ =>
    Subgroup.mem_centralizer_singleton_iff.2 (cfg.xcen s)
  exact Or.inl (S265F3.exists_e3_of_layer hp cfg.elem cfg.xB cfg.x1 hSx cfg.hb cfg.hbx he₀B he₀D
    hne)

end CFSG.LocalAnalysis.GLTheoremA.S265BU8

end
