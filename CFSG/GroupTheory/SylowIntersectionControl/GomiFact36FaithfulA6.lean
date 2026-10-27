module

import CFSG.Quasithin.H13.A6Realize
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K534Gen
import CFSG.Quasithin.Background.F918Z0AuxLin
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.LocalAnalysis

variable {W : Type} [CommGroup W]

private theorem autUnit_injective_fag [Module (ZMod 2) (Additive W)] :
    Function.Injective (MatModel.autUnit (V := W)) := by
  intro g h gh
  ext w
  have h1 : (MatModel.autUnit g : Module.End (ZMod 2) (Additive W)) =
      (MatModel.autUnit h : Module.End (ZMod 2) (Additive W)) :=
    congrArg (fun u : (Module.End (ZMod 2) (Additive W))ˣ =>
      (u : Module.End (ZMod 2) (Additive W))) gh
  have h2 := congrArg (fun f : Module.End (ZMod 2) (Additive W) => f (Additive.ofMul w)) h1
  rw [MatModel.autUnit_apply, MatModel.autUnit_apply] at h2
  simpa using Additive.ofMul.injective h2

private theorem nontrivial_of_isIrrSec_fag {L : Subgroup (MulAut W)}
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤) : Nontrivial W := by
  rcases subsingleton_or_nontrivial W with h | h
  · have : Subsingleton W := h
    exact absurd (Subgroup.ext fun x => by simp [Subsingleton.elim x 1]) (ne_of_lt hirr.1)
  · exact h

private theorem card_eq_pow_finrank_fag [Finite W] [Module (ZMod 2) (Additive W)] :
    Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) :=
  ((FiniteField.pow_finrank_eq_natCard 2 (Additive W)).trans
    (Nat.card_congr Additive.toMul)).symm

private theorem card_fixV_eq_card_fixedSub_fag [Module (ZMod 2) (Additive W)]
    (A : Subgroup (MulAut W)) :
    Nat.card ↥(fixV A) =
      Nat.card ↥(CommutingFactor.fixedSub (A.map (MatModel.autUnit (V := W)))) := by
  refine Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun w => ?_)
  rw [mem_fixV, CommutingFactor.mem_fixedSub]
  constructor
  · intro h a' ha'
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
    rw [MatModel.autUnit_apply]
    simpa only [toMul_ofMul] using congrArg Additive.ofMul (h a ha)
  · intro h a ha
    have h' := h (MatModel.autUnit a) (Subgroup.mem_map_of_mem (MatModel.autUnit (V := W)) ha)
    rw [MatModel.autUnit_apply] at h'
    simpa using Additive.ofMul.injective h'

private theorem irrSup_fag {L A : Subgroup (MulAut W)}
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤) :
    ∀ U : Subgroup W, (∀ g ∈ A ⊔ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  exact hirr.2 U (fun l u hu => hU (l : MulAut W) (Subgroup.mem_sup_right l.2) u hu) bot_le le_top

private theorem map_le_normalizer_fag [Module (ZMod 2) (Additive W)] {L A : Subgroup (MulAut W)}
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    A.map (MatModel.autUnit (V := W)) ≤ Subgroup.normalizer
      ((L.map (MatModel.autUnit (V := W)) :
        Subgroup (Module.End (ZMod 2) (Additive W))ˣ) : Set _) :=
  (Subgroup.map_mono hAL).trans (Subgroup.le_normalizer_map (MatModel.autUnit (V := W)))

private theorem map_ne_bot_fag [Module (ZMod 2) (Additive W)] {A : Subgroup (MulAut W)}
    (hA : A ≠ ⊥) : A.map (MatModel.autUnit (V := W)) ≠ ⊥ :=
  fun hb => hA ((Subgroup.map_eq_bot_iff_of_injective A (autUnit_injective_fag)).mp hb)

private theorem map_sq_one_fag [Module (ZMod 2) (Additive W)] {A : Subgroup (MulAut W)}
    (hAe : IsElemAbelian2 A) :
    ∀ a ∈ A.map (MatModel.autUnit (V := W)), a ^ 2 = 1 := by
  obtain ⟨-, hsq⟩ := hAe
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, hsq a ha, map_one]

private theorem add_le_of_shortGen_fag {n f r m : ℕ} (hn : 3 ≤ n) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (hmr : m * r ≤ 6) (hle : n ≤ m * (n - f)) : r + f ≤ n + 1 := by
  have hnf : 1 ≤ n - f := by
    rcases Nat.eq_zero_or_pos (n - f) with h0 | hpos
    · rw [h0, Nat.mul_zero] at hle
      omega
    · exact hpos
  rcases Nat.lt_or_ge 2 r with hr | hr
  · have hr3' : r = 3 := by omega
    rw [hr3'] at hmr ⊢
    have hm2 : m ≤ 2 := by omega
    have h1 : m * (n - f) ≤ 2 * (n - f) := Nat.mul_le_mul_right _ hm2
    have hnf2 : 2 ≤ n - f := by
      have h2 := hle.trans h1
      omega
    omega
  · omega

private theorem five_le_card_fag [Finite W] {L : Subgroup (MulAut W)}
    (h360 : 360 ≤ Nat.card ↥L) : 5 ≤ Nat.card W := by
  by_contra h
  have h4 : Nat.card W ≤ 4 := by omega
  have hinj : Function.Injective (fun l : ↥L => (l : MulAut W).toEquiv) := by
    intro l l' hll
    exact Subtype.ext (MulEquiv.toEquiv_injective hll)
  have hle : Nat.card ↥L ≤ Nat.card (Equiv.Perm W) := Nat.card_le_card_of_injective _ hinj
  have hfac : Nat.card (Equiv.Perm W) = Nat.factorial (Nat.card W) := Nat.card_perm
  have h24 : Nat.factorial (Nat.card W) ≤ 24 := (Nat.factorial_le h4).trans (by norm_num)
  have hfact : 360 ≤ Nat.factorial (Nat.card W) := h360.trans (hle.trans (le_of_eq hfac))
  omega

private theorem three_le_finrank_fag [Finite W] [Module (ZMod 2) (Additive W)]
    (h5 : 5 ≤ Nat.card W) : 3 ≤ Module.finrank (ZMod 2) (Additive W) := by
  by_contra h
  have h2 : Module.finrank (ZMod 2) (Additive W) ≤ 2 := by omega
  have hcard := card_eq_pow_finrank_fag (W := W)
  have hle : 2 ^ Module.finrank (ZMod 2) (Additive W) ≤ 4 :=
    (Nat.pow_le_pow_right (by norm_num) h2).trans (by norm_num)
  omega

private theorem cost_lt_fag [Finite W] [Module (ZMod 2) (Additive W)]
    {A : Subgroup (MulAut W)} (hn : 3 ≤ Module.finrank (ZMod 2) (Additive W))
    (hgen : ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      Module.finrank (ZMod 2) (Additive W) ≤ m * (Module.finrank (ZMod 2) (Additive W) -
        Module.finrank (ZMod 2) ↥(CommutingFactor.fixedSub
          (A.map (MatModel.autUnit (V := W)))))) :
    Nat.card A * Nat.card ↥(fixV A) < 4 * Nat.card W := by
  obtain ⟨r, m, hcard, hr1, hr3, hmr, hle⟩ := hgen
  have hfix := card_fixV_eq_card_fixedSub_fag (W := W) A
  have hfc : Nat.card ↥(CommutingFactor.fixedSub (A.map (MatModel.autUnit (V := W)))) =
      2 ^ Module.finrank (ZMod 2) ↥(CommutingFactor.fixedSub
        (A.map (MatModel.autUnit (V := W)))) :=
    (FiniteField.pow_finrank_eq_natCard 2 ↥(CommutingFactor.fixedSub
      (A.map (MatModel.autUnit (V := W))))).symm
  have hWc := card_eq_pow_finrank_fag (W := W)
  have harith : r + Module.finrank (ZMod 2) ↥(CommutingFactor.fixedSub
      (A.map (MatModel.autUnit (V := W)))) ≤ Module.finrank (ZMod 2) (Additive W) + 1 :=
    add_le_of_shortGen_fag hn hr1 hr3 hmr hle
  have hlt : 2 ^ (r + Module.finrank (ZMod 2) ↥(CommutingFactor.fixedSub
        (A.map (MatModel.autUnit (V := W))))) <
      2 ^ (Module.finrank (ZMod 2) (Additive W) + 2) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  calc Nat.card A * Nat.card ↥(fixV A)
      = 2 ^ r * 2 ^ Module.finrank (ZMod 2) ↥(CommutingFactor.fixedSub
          (A.map (MatModel.autUnit (V := W)))) := by rw [hcard, hfix, hfc]
    _ = 2 ^ (r + Module.finrank (ZMod 2) ↥(CommutingFactor.fixedSub
          (A.map (MatModel.autUnit (V := W))))) := (pow_add _ _ _).symm
    _ < 2 ^ (Module.finrank (ZMod 2) (Additive W) + 2) := hlt
    _ = 4 * Nat.card W := by rw [hWc, pow_add]; ring

private theorem shortGen_alt_fag [Finite W] [Module (ZMod 2) (Additive W)]
    {L A : Subgroup (MulAut W)} (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A) (hA : A ≠ ⊥)
    (eY : ↥(L.map (MatModel.autUnit (V := W))) ≃* ↥(alternatingGroup (Fin 6))) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      Module.finrank (ZMod 2) (Additive W) ≤ m * (Module.finrank (ZMod 2) (Additive W) -
        Module.finrank (ZMod 2) ↥(CommutingFactor.fixedSub
          (A.map (MatModel.autUnit (V := W))))) := by
  have : Nontrivial (Additive W) := nontrivial_of_isIrrSec_fag (W := W) hirr
  have hirr' := MatModel.irr_units (D := A) (X := L) (irrSup_fag (L := L) (A := A) hirr)
  have hAN := map_le_normalizer_fag (L := L) (A := A) hAL
  have hA1 := map_ne_bot_fag (A := A) hA
  have hAe' := hAe
  have hA2 := map_sq_one_fag (A := A) hAe
  obtain ⟨hcomm, -⟩ := hAe'
  have hAc := MatModel.comm_units (D := A) (X := A) hcomm
  obtain ⟨r, m, hcard, hr1, hr3, hmr, hdim⟩ :=
    CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.a6_short_gen (S := Additive W)
      hirr' hAN eY hA1 hAc hA2
  exact ⟨r, m, (Subgroup.card_map_of_injective (K := A) (f := MatModel.autUnit (V := W))
    (autUnit_injective_fag)).symm.trans hcard, hr1, hr3, hmr, hdim⟩

private theorem shortGen_threeA6_fag [Finite W] [Module (ZMod 2) (Additive W)]
    {L A : Subgroup (MulAut W)} (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A) (hA : A ≠ ⊥)
    (hq : CFSG.Open.IsQuasisimple ↥(L.map (MatModel.autUnit (V := W))))
    (hZ : Nat.card (Subgroup.center ↥(L.map (MatModel.autUnit (V := W)))) = 3)
    (e6 : ↥(L.map (MatModel.autUnit (V := W))) ⧸
        Subgroup.center ↥(L.map (MatModel.autUnit (V := W))) ≃*
      ↥(alternatingGroup (Fin 6))) :
    ∃ r m : ℕ, Nat.card A = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      Module.finrank (ZMod 2) (Additive W) ≤ m * (Module.finrank (ZMod 2) (Additive W) -
        Module.finrank (ZMod 2) ↥(CommutingFactor.fixedSub
          (A.map (MatModel.autUnit (V := W))))) := by
  have : Nontrivial (Additive W) := nontrivial_of_isIrrSec_fag (W := W) hirr
  have hirr' := MatModel.irr_units (D := A) (X := L) (irrSup_fag (L := L) (A := A) hirr)
  have hAN := map_le_normalizer_fag (L := L) (A := A) hAL
  have hA1 := map_ne_bot_fag (A := A) hA
  have hAe' := hAe
  have hA2 := map_sq_one_fag (A := A) hAe
  obtain ⟨hcomm, -⟩ := hAe'
  have hAc := MatModel.comm_units (D := A) (X := A) hcomm
  obtain ⟨r, m, hcard, hr1, hr3, hmr, hdim⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.K534Proof.q3a6_short_gen (S := Additive W)
      hirr' hAN hq hZ e6 hA1 hAc hA2
  exact ⟨r, m, (Subgroup.card_map_of_injective (K := A) (f := MatModel.autUnit (V := W))
    (autUnit_injective_fag)).symm.trans hcard, hr1, hr3, hmr, hdim⟩

theorem card_mul_card_fixV_lt_of_alternatingNatural [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L A : Subgroup (MulAut W)} (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A) (hA : A ≠ ⊥)
    (hnat : AlternatingNatural L ⊤ ⊥ 6) : Nat.card A * Nat.card ↥(fixV A) < 4 * Nat.card W := by
  have hne : Nonempty (↥L ≃* ↥(alternatingGroup (Fin 6))) :=
    H13.A6.nonempty_mulEquiv_of_realizes (H13.A6.altDn_faithful (by norm_num)) hnat
  obtain ⟨eL⟩ := hne
  have : Module (ZMod 2) (Additive W) := MatModel.z2Mod hW
  have hΦ := autUnit_injective_fag (W := W)
  have h360 : 360 ≤ Nat.card ↥L := by
    rw [Nat.card_congr eL.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hn := three_le_finrank_fag (W := W) (five_le_card_fag (L := L) h360)
  have eY : ↥(L.map (MatModel.autUnit (V := W))) ≃* ↥(alternatingGroup (Fin 6)) :=
    (Subgroup.equivMapOfInjective L (MatModel.autUnit (V := W)) hΦ).symm.trans eL
  exact cost_lt_fag (W := W) hn (shortGen_alt_fag (W := W) hirr hAL hAe hA eY)

theorem card_mul_card_fixV_lt_of_tripleA6Six [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L A : Subgroup (MulAut W)} (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup W) ⊤)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut W))) (hAe : IsElemAbelian2 A) (hA : A ≠ ⊥)
    (hnat : TripleA6Six L ⊤ ⊥) : Nat.card A * Nat.card ↥(fixV A) < 4 * Nat.card W := by
  obtain ⟨K, instK, instKfin, Γ₀, -, -, hhat, -, hreal⟩ := hnat
  have hne : Nonempty (↥L ≃* ↥Γ₀) :=
    H13.A6.nonempty_mulEquiv_of_realizes (FFModel.nat_faithful Γ₀) hreal
  obtain ⟨eL⟩ := hne
  obtain ⟨e6⟩ := hhat.2.2
  have hqΓ : CFSG.Open.IsQuasisimple ↥Γ₀ := ⟨hhat.1.1.commutator_eq_top, hhat.1.2.1⟩
  have : Module (ZMod 2) (Additive W) := MatModel.z2Mod hW
  have hΦ := autUnit_injective_fag (W := W)
  let Y : Subgroup (Module.End (ZMod 2) (Additive W))ˣ := L.map (MatModel.autUnit (V := W))
  have h360 : 360 ≤ Nat.card ↥L := by
    have h1 : Nat.card ↥L = Nat.card ↥Γ₀ := Nat.card_congr eL.toEquiv
    have h2 : Nat.card (↥Γ₀ ⧸ Subgroup.center ↥Γ₀) = 360 := by
      rw [Nat.card_congr e6.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    rw [h1, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Γ₀), h2,
      hhat.2.1]
    norm_num
  have hn := three_le_finrank_fag (W := W) (five_le_card_fag (L := L) h360)
  have eY : ↥Y ≃* ↥Γ₀ :=
    (Subgroup.equivMapOfInjective L (MatModel.autUnit (V := W)) hΦ).symm.trans eL
  have hqY : CFSG.Open.IsQuasisimple ↥Y := CFSG.Open.IsQuasisimple.of_mulEquiv eY hqΓ
  have hZY : Nat.card (Subgroup.center ↥Y) = 3 := by
    have hmap : (Subgroup.center ↥Y).map (eY : ↥Y →* ↥Γ₀) = Subgroup.center ↥Γ₀ :=
      Subgroup.map_center_eq eY
    have hc := Subgroup.card_map_of_injective (K := Subgroup.center ↥Y)
      (f := (eY : ↥Y →* ↥Γ₀)) eY.injective
    rw [hmap] at hc
    exact hc.symm.trans hhat.2.1
  have he6 : ↥Y ⧸ Subgroup.center ↥Y ≃* ↥(alternatingGroup (Fin 6)) :=
    (QuotientGroup.congr (Subgroup.center ↥Y) (Subgroup.center ↥Γ₀) eY
      (Subgroup.map_center_eq eY)).trans e6
  exact cost_lt_fag (W := W) hn (shortGen_threeA6_fag (W := W) hirr hAL hAe hA hqY hZY he6)

end CFSG.GroupTheory
