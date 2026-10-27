module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.Defs
public import Certificates.Certificate272020
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711Pf2Om0Inv
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Q3.Q3TLTO8Inputs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.EvenSporadicStandard.Co3Std.CentT

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.Certificates.Native
open CFSG.EvenSmallLie.OmegaEight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om0
open CFSG.ClassicalInvolution.Q3.O8
open CFSG.ClassicalInvolution.O8Data

section Certified

private theorem mem_fixedSubgroup_iff {G : Type*} [Group G] {α : MulAut G} {s : G} :
    s ∈ fixedSubgroup α ↔ α s = s := Iff.rfl

private theorem fixedSubgroup_conj_aux {G : Type*} [Group G] (s : G) :
    fixedSubgroup (MulAut.conj s) = Subgroup.centralizer ({s} : Set G) := by
  ext x
  rw [mem_fixedSubgroup_iff, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * s = s * x * s⁻¹ * s := by rw [h]
      _ = s * x := by group
  · intro h
    rw [← h, mul_inv_cancel_right]

private theorem conj_eq_one_iff_mem_center {G : Type*} [Group G] (q : G) :
    MulAut.conj q = 1 ↔ q ∈ Subgroup.center G := by
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun f : MulAut G => f x) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at hx
    calc x * q = (q * x * q⁻¹) * q := by rw [hx]
      _ = q * x := by group
  · intro h
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply]
    rw [← Subgroup.mem_center_iff.1 h x]
    group

private theorem center_eq_bot_of_mulEquiv_aux {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : Subgroup.center T = ⊥) : Subgroup.center S = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hz' : e z ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro y
    rw [← e.apply_symm_apply y, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz]
  rw [h, Subgroup.mem_bot] at hz'
  exact e.injective (hz'.trans (map_one e).symm)

private theorem card_centralizer_mulEquiv_aux {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (u : K) : Nat.card (Subgroup.centralizer ({e u} : Set L)) =
      Nat.card (Subgroup.centralizer ({u} : Set K)) := by
  have h : (Subgroup.centralizer ({u} : Set K)).map e.toMonoidHom =
      Subgroup.centralizer ({e u} : Set L) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← map_mul, ← map_mul, hz]
    · intro hy
      refine ⟨e.symm y, e.injective ?_, e.apply_symm_apply y⟩
      rw [map_mul, map_mul, e.apply_symm_apply, hy]
  rw [← h, Subgroup.card_map_of_injective e.injective]

private theorem card_centralizer_xOm_eq (i : Fin 3) :
    Nat.card (centralizer ({xOm i} : Set omegaT)) =
      Nat.card (CFSG.Sporadic.Schreier.centralizerIn omegaT (mainPerm i)) := by
  have h : (centralizer ({xOm i} : Set omegaT)).map omegaT.subtype =
      CFSG.Sporadic.Schreier.centralizerIn omegaT (mainPerm i) := by
    ext y
    simp only [Subgroup.mem_map, CFSG.Sporadic.Schreier.mem_centralizerIn,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, congrArg Subtype.val hz⟩
    · rintro ⟨hy, hc⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hc, rfl⟩
  rw [← h]
  exact (Subgroup.card_map_of_injective omegaT.subtype_injective).symm

private theorem card_centralizerIn_mainPerm_zero :
    Nat.card (CFSG.Sporadic.Schreier.centralizerIn omegaT (mainPerm 0)) = 110592 :=
  Certificates.certificate272020.2.1

private theorem card_centralizerIn_mainPerm_one :
    Nat.card (CFSG.Sporadic.Schreier.centralizerIn omegaT (mainPerm 1)) = 46080 :=
  Certificates.certificate272020.2.2.1

private theorem card_centralizerIn_mainPerm_two :
    Nat.card (CFSG.Sporadic.Schreier.centralizerIn omegaT (mainPerm 2)) = 3072 :=
  Certificates.certificate272020.2.2.2

theorem o8_card {Q : Type} [Group Q] (hQ : LieModel Q .POmegaPlus 4 2 1) :
    Nat.card Q = 174182400 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hQ
  exact (Nat.card_congr e.toEquiv).trans card_omegaT

theorem o8_card_mulAut {Q : Type} [Group Q] (hQ : LieModel Q .POmegaPlus 4 2 1) :
    Nat.card (MulAut Q) = 6 * Nat.card Q := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hQ
  calc Nat.card (MulAut Q) = Nat.card (MulAut omegaT) :=
        Nat.card_congr (MulAut.congr e).toEquiv
    _ = 6 * Nat.card Q := by rw [card_mulAut_omegaT, o8_card hQ]

theorem o8_center {Q : Type} [Group Q] (hQ : LieModel Q .POmegaPlus 4 2 1) :
    center Q = ⊥ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hQ
  exact center_eq_bot_of_mulEquiv_aux e center_omegaT

theorem o8_card_centralizer {Q : Type} [Group Q] (hQ : LieModel Q .POmegaPlus 4 2 1) {g : Q}
    (hg2 : g * g = 1) (hg1 : g ≠ 1) :
    Nat.card (centralizer ({g} : Set Q)) = 110592 ∨
      Nat.card (centralizer ({g} : Set Q)) = 46080 ∨
      Nat.card (centralizer ({g} : Set Q)) = 3072 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_omegaT hQ
  have ht2 : e g * e g = 1 := by rw [← map_mul, hg2, map_one]
  have ht1 : e g ≠ 1 := fun h => hg1 (e.injective (by rw [h, map_one]))
  obtain ⟨i, α, hα⟩ := om0_h1 (e g) ht2 ht1
  have hQcard : Nat.card (centralizer ({g} : Set Q)) =
      Nat.card (centralizer ({xOm i} : Set omegaT)) := by
    rw [← card_centralizer_mulEquiv_aux e g, ← hα]
    exact (card_centralizer_mulEquiv_aux α (e g)).symm
  rw [hQcard, card_centralizer_xOm_eq i]
  fin_cases i
  · exact Or.inl card_centralizerIn_mainPerm_zero
  · exact Or.inr (Or.inl card_centralizerIn_mainPerm_one)
  · exact Or.inr (Or.inr card_centralizerIn_mainPerm_two)

theorem o8_fixed_large (hO : O8Plus2OuterInvolutions) {Q : Type} [Group Q] [Finite Q]
    (hQ : LieModel Q .POmegaPlus 4 2 1) (σ : MulAut Q) (hσ : σ * σ = 1) :
    4 < Nat.card (fixedSubgroup σ) := by
  by_cases hinner : ∃ q : Q, σ = MulAut.conj q
  · obtain ⟨q, rfl⟩ := hinner
    rw [fixedSubgroup_conj_aux]
    have hqq : q * q = 1 := by
      have hconj : MulAut.conj (q * q) = 1 := by rw [map_mul]; exact hσ
      have hmem : q * q ∈ Subgroup.center Q := (conj_eq_one_iff_mem_center (q * q)).1 hconj
      rw [o8_center hQ] at hmem
      exact Subgroup.mem_bot.1 hmem
    by_cases hq1 : q = 1
    · subst hq1
      have htop : Subgroup.centralizer ({1} : Set Q) = ⊤ := by
        ext x
        simp [Subgroup.mem_centralizer_singleton_iff]
      rw [htop, Subgroup.card_top, o8_card hQ]
      norm_num
    · rcases o8_card_centralizer hQ hqq hq1 with h | h | h <;> rw [h] <;> norm_num
  · exact hO Q hQ σ hσ (fun q hq => hinner ⟨q, hq⟩)

end Certified

end CFSG.EvenSporadicStandard.Co3Std.CentT
