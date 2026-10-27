module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023Facts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem rho_conjQ (L : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (y : PQuot 3 L) : rho L ⟨g, hg⟩ (lemma102_conjQ 3 hg y) = y := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  rw [lemma102_conjQ_mk]
  exact rho_mk' L hg _ l (by rw [lemma102_conjHomL_val]; group)

theorem conjQ_rho (L : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (y : PQuot 3 L) : lemma102_conjQ 3 hg (rho L ⟨g, hg⟩ y) = y := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
  have hl' : g * (l : G) * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hg (l : G)).1 l.2
  rw [rho_mk' L hg l ⟨g * l * g⁻¹, hl'⟩ rfl, lemma102_conjQ_mk]
  congr 1
  apply Subtype.ext
  rw [lemma102_conjHomL_val]
  group

theorem centCard2_eq_of_rho (L : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    centCard2 3 L g = twoPart (Nat.card {y : PQuot 3 L // rho L ⟨g, hg⟩ y = y}) := by
  rw [lemma102_centCard2_eq_fixSub 3 hg]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  show lemma102_conjQ 3 hg y = y ↔ rho L ⟨g, hg⟩ y = y
  constructor
  · intro h
    calc rho L ⟨g, hg⟩ y = rho L ⟨g, hg⟩ (lemma102_conjQ 3 hg y) := by rw [h]
      _ = y := rho_conjQ L hg y
  · intro h
    calc lemma102_conjQ 3 hg y = lemma102_conjQ 3 hg (rho L ⟨g, hg⟩ y) := by rw [h]
      _ = y := conjQ_rho L hg y

structure StarOut (B : Subgroup G) (x : G) (L : Subgroup G) (ψ : MulAut (PQuot 3 L)) : Prop where
  ex : ∃ (S T : Subgroup G) (sb : G) (hsb : sb ∈ Subgroup.normalizer (L : Set G)),
    S ≤ Subgroup.normalizer (L : Set G) ∧ IsElemAbelian 3 S ∧ x ∈ S ∧ Nat.card S = Nat.card B ∧
    sb ∈ S ∧ rho L ⟨sb, hsb⟩ = ψ ∧
    T ≤ cx x ∧ IsPGroup 2 T ∧ S ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, S⁆ : Subgroup G) ≠ ⊥ ∧
    IsEmpty (T ≃* QuaternionGroup 2)

theorem final_of_starOut {B : Subgroup G} {x : G} {L : Subgroup G} (hBmax : GLAIsBmax 3 B)
    (hx1 : x ≠ 1) (hL : GLAPComponent 3 (cx x) L) {ψ : MulAut (PQuot 3 L)}
    (hψ : ψ ∉ innerAutS (PQuot 3 L))
    (hψc : twoPart (Nat.card {y : PQuot 3 L // ψ y = y}) = Nat.sqrt (card2 3 L))
    (hout : StarOut B x L ψ) :
    ∃ (B' : Subgroup G) (b : G), IsSTriple 3 B' x L ∧ B' ≤ Subgroup.normalizer (L : Set G) ∧
      b ∈ B' ∧ b ∉ Subgroup.zpowers x ∧ NonInner 3 b L ∧
      centCard2 3 L b = Nat.sqrt (card2 3 L) := by
  obtain ⟨S, T, sb, hsb, hSL, hSel, hxS, hcard, hsbS, hρ, hTx, hT2, hST, hTc, hTQ⟩ := hout.ex
  have hTne : T ≠ ⊥ := by
    rintro rfl
    exact hTc (Subgroup.commutator_bot_left S)
  have hxcent : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.1 (hL.1 hl)
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _ hxcent
  refine ⟨S, sb, ⟨⟨hSel, ?_, T, hTne, hT2, hST⟩, ⟨hxS, hx1, T, hTx, hT2, hST, hTc, fun _ => hTQ⟩, hL⟩,
    hSL, hsbS, ?_, ⟨hsb, fun h => hψ ?_⟩, ?_⟩
  · rw [hcard]
    exact hBmax.2.1
  · intro h
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
    have hx : rho L ⟨x, hxN⟩ = 1 :=
      (rho_eq_one_iff L hxN).2 (centMod_iff.1 (centMod_of_mem_centralizer hxcent))
    have e : (⟨sb, hsb⟩ : ↥(Subgroup.normalizer (L : Set G))) = ⟨x, hxN⟩ ^ n :=
      Subtype.ext (by simp [hn])
    have h1 : ψ = 1 := by rw [← hρ, e, map_zpow, hx, one_zpow]
    exact hψ (h1 ▸ (innerAutS (PQuot 3 L)).one_mem)
  · rw [← hρ]
    exact (inducesInnerMod_iff_barAut_mem_inner hsb).1 h
  · rw [centCard2_eq_of_rho L hsb, hρ]
    exact hψc

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
