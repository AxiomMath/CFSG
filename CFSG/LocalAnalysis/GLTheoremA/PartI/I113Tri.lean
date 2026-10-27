module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_Triple
import CFSG.Quasithin.Background.F918V5GComp
import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I113

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.ComponentBalance

set_option linter.unusedSectionVars false

variable {Q : Type} [Group Q] [Finite Q]

theorem not_commute_of_isComponentOf {M' : Subgroup Q} (h : IsComponentOf M' ⊤) :
    ¬ ∀ u ∈ M', ∀ w ∈ M', u * w = w * u := by
  intro hc
  have hq := h.2.2
  have hnt : Nontrivial ↥M' := isQuasisimple_nontrivial hq
  have h1 : commutator ↥M' = ⊤ := hq.1
  have h2 : commutator ↥M' = ⊥ := by
    rw [commutator, eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hc a.1 a.2 b.1 b.2)
  rw [h1] at h2
  obtain ⟨a, ha⟩ := exists_ne (1 : ↥M')
  have : a ∈ (⊥ : Subgroup ↥M') := h2 ▸ Subgroup.mem_top a
  exact ha (Subgroup.mem_bot.1 this)

structure Triple3 (B M : Subgroup Q) (c : Q) : Prop where
  elem : IsElemAbelian 3 B
  comp : IsComponentOf M ⊤
  mem : c ∈ B
  not_mem : c ∉ Subgroup.normalizer (M : Set Q)
  index : (Subgroup.normalizer (M : Set Q)).relIndex B = 3

namespace Triple3

variable {B M : Subgroup Q} {c : Q} (T : Triple3 B M c)

include T

theorem comm_B {a b : Q} (ha : a ∈ B) (hb : b ∈ B) : a * b = b * a := by
  have := T.elem.1.is_comm.comm (⟨a, ha⟩ : B) ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem pow_three_mem : c ^ 3 ∈ Subgroup.normalizer (M : Set Q) := by
  set N := Subgroup.normalizer (M : Set Q)
  have : (N.subgroupOf B).Normal := ⟨fun n hn g => by
    have : ((g * n * g⁻¹ : B) : Q) = (n : Q) := by
      have h := T.comm_B g.2 n.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h]; group
    rw [Subgroup.mem_subgroupOf, this]
    exact hn⟩
  have h := Subgroup.pow_index_mem (N.subgroupOf B) (⟨c, T.mem⟩ : B)
  have hi : (N.subgroupOf B).index = 3 := T.index
  rw [hi, Subgroup.mem_subgroupOf] at h
  exact h

theorem pow_two_not_mem : c ^ 2 ∉ Subgroup.normalizer (M : Set Q) := by
  intro h
  apply T.not_mem
  have : c = c ^ 3 * (c ^ 2)⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ T.pow_three_mem (Subgroup.inv_mem _ h)

theorem conj1_ne : GLBConj c M ≠ M := fun h => T.not_mem (mem_normalizer_iff_gLBConj_eq.2 h)

theorem conj2_ne : GLBConj (c ^ 2) M ≠ M := fun h =>
  T.pow_two_not_mem (mem_normalizer_iff_gLBConj_eq.2 h)

theorem conj21_ne : GLBConj (c ^ 2) M ≠ GLBConj c M := by
  intro h
  have h1 := congrArg (GLBConj c⁻¹) h
  rw [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one,
    show c ^ 2 * c⁻¹ = c by group] at h1
  exact T.conj1_ne h1

theorem comp_conj (g : Q) : IsComponentOf (GLBConj g M) ⊤ := isComponentOf_gLBConj T.comp g

theorem comm_of_ne {g h : Q} (hne : GLBConj g M ≠ GLBConj h M) :
    ∀ u ∈ GLBConj g M, ∀ w ∈ GLBConj h M, u * w = w * u := by
  rcases CFSG.Quasithin.F918V5G.isComponentOf_eq_or_commute (T.comp_conj g) (T.comp_conj h) with
    h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem conj_le_K {g : Q} (hg : g ∈ B) : GLBConj g M ≤ t113K B M :=
  le_iSup₂_of_le g hg le_rfl

theorem L_le_K : M ≤ t113K B M := by
  have := T.conj_le_K (g := 1) B.one_mem
  rwa [gLBConj_one] at this

theorem centralizes_K {z : Q} (hz : z ∈ B) (hc : ∀ l ∈ M, l * z = z * l) :
    ∀ k ∈ t113K B M, k * z = z * k := by
  have hle : t113K B M ≤ Subgroup.centralizer ({z} : Set Q) := by
    refine iSup₂_le fun g hg w hw => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hl : Commute z (g * w * g⁻¹) := (hc _ (mem_gLBConj.1 hw)).symm
    have hg' : Commute z g := T.comm_B hz hg
    have : Commute z (g⁻¹ * (g * w * g⁻¹) * g) := (hg'.inv_right.mul_right hl).mul_right hg'
    have e : g⁻¹ * (g * w * g⁻¹) * g = w := by group
    rw [e] at this
    exact this.eq.symm
  intro k hk
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hk)

theorem B0_comm_K {b : Q} (hb : b ∈ t113B0 B M) : ∀ k ∈ t113K B M, k * b = b * k :=
  Subgroup.mem_centralizer_iff.1 hb.2

theorem B0_mem_A {b : Q} (hb : b ∈ t113B0 B M) : b ∈ t113A B M := by
  refine ⟨?_, hb.1⟩
  refine t113_mem_normalizer_of_commute fun j hj => ?_
  exact (T.B0_comm_K hb j (T.L_le_K hj)).symm

theorem rho_apply (a : ↥(t113A B M)) (l : ↥M) :
    ((t113Rho B M a l : ↥M) : Q) = (a : Q) * l * (a : Q)⁻¹ := rfl

theorem rho_eq_one_iff (a : ↥(t113A B M)) :
    t113Rho B M a = 1 ↔ (a : Q) ∈ t113B0 B M := by
  constructor
  · intro h
    have hc : ∀ l ∈ M, l * (a : Q) = (a : Q) * l := by
      intro l hl
      have := congrArg (fun f : MulAut ↥M => ((f ⟨l, hl⟩ : ↥M) : Q)) h
      have e : ((t113Rho B M a ⟨l, hl⟩ : ↥M) : Q) = (a : Q) * l * (a : Q)⁻¹ := rfl
      simp only [MulAut.one_apply] at this
      rw [e] at this
      calc l * (a : Q) = ((a : Q) * l * (a : Q)⁻¹) * (a : Q) := by rw [this]
        _ = (a : Q) * l := by group
    exact ⟨a.2.2, Subgroup.mem_centralizer_iff.2 (T.centralizes_K a.2.2 hc)⟩
  · intro h
    ext l
    rw [T.rho_apply, MulAut.one_apply]
    have := T.B0_comm_K h (l : Q) (T.L_le_K l.2)
    calc (a : Q) * (l : Q) * (a : Q)⁻¹ = ((l : Q) * a) * (a : Q)⁻¹ := by rw [this]
      _ = l := by group

theorem map_ker_rho : (t113Rho B M).ker.map (t113A B M).subtype = t113B0 B M := by
  ext z
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (T.rho_eq_one_iff a).1 ha
  · intro hz
    exact ⟨⟨z, T.B0_mem_A hz⟩, (T.rho_eq_one_iff _).2 hz, rfl⟩

theorem card_ker_rho : Nat.card (t113Rho B M).ker = Nat.card (t113B0 B M) := by
  rw [← T.map_ker_rho]
  exact (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm

theorem card_A : Nat.card B = 3 * Nat.card (t113A B M) := by
  have h := Subgroup.relIndex_mul_card (H := Subgroup.normalizer (M : Set Q)) (K := B)
  rw [T.index] at h
  exact h.symm

theorem card_B : Nat.card B = 3 * Nat.card (t113H B M) * Nat.card (t113B0 B M) := by
  have h := Subgroup.card_ker_mul_card_range (t113Rho B M)
  rw [T.card_ker_rho] at h
  rw [T.card_A, ← h]
  unfold t113H
  ring

theorem H_elem : IsElemAbelian 3 (t113H B M) := by
  refine ⟨⟨⟨fun α β => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha⟩ := α.2
    obtain ⟨b, hb⟩ := β.2
    apply Subtype.ext
    show (α : MulAut ↥M) * β = β * α
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact T.comm_B a.2.2 b.2.2
  · intro α hα
    obtain ⟨a, rfl⟩ := hα
    rw [← map_pow]
    have : a ^ 3 = 1 := by
      apply Subtype.ext
      exact T.elem.2 _ a.2.2
    rw [this, map_one]

theorem B0_elem : IsElemAbelian 3 (t113B0 B M) :=
  t113_elemAbelian_of_le T.elem inf_le_left

theorem comm01 : ∀ u ∈ M, ∀ w ∈ GLBConj c M, u * w = w * u := by
  have := T.comm_of_ne (g := 1) (h := c) (by rw [gLBConj_one]; exact T.conj1_ne.symm)
  simpa only [gLBConj_one] using this

theorem comm02 : ∀ u ∈ M, ∀ w ∈ GLBConj (c ^ 2) M, u * w = w * u := by
  have := T.comm_of_ne (g := 1) (h := c ^ 2) (by rw [gLBConj_one]; exact T.conj2_ne.symm)
  simpa only [gLBConj_one] using this

theorem comm12 : ∀ u ∈ GLBConj c M, ∀ w ∈ GLBConj (c ^ 2) M, u * w = w * u :=
  T.comm_of_ne (g := c) (h := c ^ 2) T.conj21_ne.symm

theorem conj1_mem {y : Q} (hy : y ∈ M) : c⁻¹ * y * c ∈ GLBConj c M := by
  rw [mem_gLBConj]
  simpa [mul_assoc] using hy

theorem conj2_mem {y : Q} (hy : y ∈ M) : (c ^ 2)⁻¹ * y * c ^ 2 ∈ GLBConj (c ^ 2) M := by
  rw [mem_gLBConj]
  simpa [mul_assoc] using hy

theorem commute_conj {g f y : Q} (hg : g ∈ B) (hf : f ∈ B) (hfy : f * y = y * f) :
    f * (g⁻¹ * y * g) = (g⁻¹ * y * g) * f := by
  have hc : Commute f g := T.comm_B hf hg
  have : Commute f (g⁻¹ * y * g) := (hc.inv_right.mul_right hfy).mul_right hc
  exact this.eq

end Triple3

end CFSG.LocalAnalysis.GLTheoremA.I113
