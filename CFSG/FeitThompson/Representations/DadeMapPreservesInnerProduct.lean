module

public import CFSG.FeitThompson.Representations.DadeMapWellDefinedLinear
import CFSG.FeitThompson.Representations.DadeSupportPacketCount
import CFSG.FeitThompson.Representations.DadeSupportPacketsLocalClasses

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open ComplexConjugate

variable {G : Type*} [Group G] {L : Subgroup G} {A : Set G} {H : G → Subgroup G}

theorem natCard_inf_centralizer_eq_of_conj [Finite G] (L : Subgroup G) {a b l : G}
    (hl : l ∈ L) (hab : l * a * l⁻¹ = b) :
    Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set G))
      = Nat.card ↥(L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have hclass : {c : G | ∃ m ∈ L, m * a * m⁻¹ = c} = {c : G | ∃ m ∈ L, m * b * m⁻¹ = c} := by
    ext c
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m * l⁻¹, mul_mem hm (inv_mem hl), by rw [← hab]; group⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m * l, mul_mem hm hl, by rw [← hab]; group⟩
  have ha := ncard_setOf_conj_mul_natCard_inf_centralizer L a
  have hb := ncard_setOf_conj_mul_natCard_inf_centralizer L b
  rw [hclass] at ha
  have hne : {c : G | ∃ m ∈ L, m * b * m⁻¹ = c}.ncard ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hb
    exact Nat.card_pos.ne' hb.symm
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (ha.trans hb.symm)

namespace IsDadeData

theorem natCard_mul_sum_eq_natCard_mul_sum [Fintype G] (hD : IsDadeData L A H) {w : G → ℂ}
    (hw0 : ∀ ⦃x : G⦄, x ∉ totalDadeSupport A H → w x = 0)
    (hwD : ∀ ⦃a : G⦄, a ∈ A → ∀ ⦃x : G⦄, x ∈ dadeSupport H a → w x = w a)
    {S : Finset G} (hS : ∀ a : G, a ∈ S ↔ a ∈ A) :
    (Nat.card ↥L : ℂ) * ∑ x : G, w x = (Nat.card G : ℂ) * ∑ a ∈ S, w a := by
  classical
  set c : G → ℂ := fun a => (Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set G)) : ℂ) with hc
  have hswap : ∑ a ∈ S, ∑ _x ∈ (dadeSupport H a).toFinset, c a * w a
      = ∑ x : G, ∑ a ∈ S.filter (fun a => x ∈ dadeSupport H a), c a * w a := by
    refine Finset.sum_comm' ?_
    intro a x
    simp
  have h1 : ∀ a ∈ S, ∑ _x ∈ (dadeSupport H a).toFinset, c a * w a = (Nat.card G : ℂ) * w a := by
    intro a ha
    have haA := (hS a).1 ha
    have hmul := hD.ncard_dadeSupport_mul_natCard_inf_centralizer haA
    rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card']
    calc ((dadeSupport H a).ncard : ℂ) * (c a * w a)
        = (((dadeSupport H a).ncard *
            Nat.card ↥(L ⊓ Subgroup.centralizer ({a} : Set G)) : ℕ) : ℂ) * w a := by
          simp only [hc]; push_cast; ring
      _ = (Nat.card G : ℂ) * w a := by rw [hmul]
  have h2 : ∀ x : G, ∑ a ∈ S.filter (fun a => x ∈ dadeSupport H a), c a * w a
      = (Nat.card ↥L : ℂ) * w x := by
    intro x
    by_cases hx : x ∈ totalDadeSupport A H
    · obtain ⟨a₀, ha₀, hxa₀⟩ := mem_totalDadeSupport_iff.1 hx
      have hset : ((S.filter (fun a => x ∈ dadeSupport H a) : Finset G) : Set G)
          = {b : G | ∃ l ∈ L, l * a₀ * l⁻¹ = b} := by
        ext b
        simp only [Finset.coe_filter, Set.mem_ofPred_eq, hS]
        constructor
        · rintro ⟨hbA, hxb⟩
          obtain ⟨l, hl, hlb⟩ :=
            hD.exists_conj_of_dadeSupport_inter_nonempty hbA ha₀ ⟨x, hxb, hxa₀⟩
          exact ⟨l⁻¹, inv_mem hl, by rw [← hlb]; group⟩
        · rintro ⟨l, hl, rfl⟩
          refine ⟨hD.conj_mem ha₀ hl, ?_⟩
          rw [hD.dadeSupport_conj ha₀ hl]
          exact hxa₀
      have hterm : ∀ b ∈ S.filter (fun a => x ∈ dadeSupport H a), c b * w b = c a₀ * w a₀ := by
        intro b hb
        have hbA : b ∈ A := (hS b).1 (Finset.mem_filter.1 hb).1
        have hxb : x ∈ dadeSupport H b := (Finset.mem_filter.1 hb).2
        obtain ⟨l, hl, hlb⟩ : ∃ l ∈ L, l * a₀ * l⁻¹ = b := by
          have hmem : b ∈ ((S.filter (fun a => x ∈ dadeSupport H a) : Finset G) : Set G) := hb
          rw [hset] at hmem
          exact hmem
        have hwb : w b = w a₀ := by rw [← hwD hbA hxb, hwD ha₀ hxa₀]
        have hcb : c b = c a₀ := by
          simp only [hc]
          exact congrArg _ (natCard_inf_centralizer_eq_of_conj L hl hlb).symm
        rw [hwb, hcb]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
      have hcard : (S.filter (fun a => x ∈ dadeSupport H a)).card
          = {b : G | ∃ l ∈ L, l * a₀ * l⁻¹ = b}.ncard := by
        rw [← Set.ncard_coe_finset, hset]
      rw [hcard]
      have horb := ncard_setOf_conj_mul_natCard_inf_centralizer L a₀
      calc ({b : G | ∃ l ∈ L, l * a₀ * l⁻¹ = b}.ncard : ℂ) * (c a₀ * w a₀)
          = (({b : G | ∃ l ∈ L, l * a₀ * l⁻¹ = b}.ncard *
              Nat.card ↥(L ⊓ Subgroup.centralizer ({a₀} : Set G)) : ℕ) : ℂ) * w a₀ := by
            simp only [hc]; push_cast; ring
        _ = (Nat.card ↥L : ℂ) * w x := by rw [horb, hwD ha₀ hxa₀]
    · have hempty : S.filter (fun a => x ∈ dadeSupport H a) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 ?_
        intro a ha hxa
        exact hx (dadeSupport_subset_totalDadeSupport ((hS a).1 ha) hxa)
      rw [hempty, Finset.sum_empty, hw0 hx, mul_zero]
  calc (Nat.card ↥L : ℂ) * ∑ x : G, w x
      = ∑ x : G, (Nat.card ↥L : ℂ) * w x := Finset.mul_sum _ _ _
    _ = ∑ x : G, ∑ a ∈ S.filter (fun a => x ∈ dadeSupport H a), c a * w a :=
        Finset.sum_congr rfl fun x _ => (h2 x).symm
    _ = ∑ a ∈ S, ∑ _x ∈ (dadeSupport H a).toFinset, c a * w a := hswap.symm
    _ = ∑ a ∈ S, (Nat.card G : ℂ) * w a := Finset.sum_congr rfl h1
    _ = (Nat.card G : ℂ) * ∑ a ∈ S, w a := (Finset.mul_sum _ _ _).symm

end IsDadeData

section Isometry

variable [Fintype G] [Fintype ↥L]

theorem cfInner_dadeMap (hD : IsDadeData L A H) (f h : dadeDomain L A) :
    cfInner ((dadeMap hD f : classFun G) : G → ℂ) ((dadeMap hD h : classFun G) : G → ℂ)
      = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ) := by
  classical
  set F : ↥L → ℂ := fun y => (f : ↥L → ℂ) y * conj ((h : ↥L → ℂ) y) with hF
  set w : G → ℂ := fun x => ((dadeMap hD f : classFun G) : G → ℂ) x *
    conj (((dadeMap hD h : classFun G) : G → ℂ) x) with hw
  have hw0 : ∀ ⦃x : G⦄, x ∉ totalDadeSupport A H → w x = 0 := by
    intro x hx
    simp [hw, dadeMap_eq_zero_of_notMem hD f hx]
  have hwval : ∀ (a : G) (ha : a ∈ A), ∀ x ∈ dadeSupport H a,
      w x = F ⟨a, hD.mem_of_mem ha⟩ := by
    intro a ha x hx
    simp only [hw, hF, dadeMap_apply_of_mem_dadeSupport hD f ha hx,
      dadeMap_apply_of_mem_dadeSupport hD h ha hx]
  have hwD : ∀ ⦃a : G⦄, a ∈ A → ∀ ⦃x : G⦄, x ∈ dadeSupport H a → w x = w a := by
    intro a ha x hx
    rw [hwval a ha x hx, hwval a ha a (self_mem_dadeSupport H a)]
  set T : Finset ↥L := {y : ↥L | (y : G) ∈ A} with hT
  set S : Finset G := T.image ((↑) : ↥L → G) with hSdef
  have hS : ∀ a : G, a ∈ S ↔ a ∈ A := by
    intro a
    simp only [hSdef, Finset.mem_image, hT, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro ha; exact ⟨⟨a, hD.mem_of_mem ha⟩, ha, rfl⟩
  have hSsum : ∑ a ∈ S, w a = ∑ y : ↥L, F y := by
    rw [hSdef, Finset.sum_image (fun x _ y _ hxy => Subtype.ext hxy)]
    refine Eq.trans (Finset.sum_congr rfl ?_) (Finset.sum_subset (Finset.subset_univ T) ?_)
    · intro y hy
      have hyA : (y : G) ∈ A := by simpa [hT] using hy
      exact hwval _ hyA _ (self_mem_dadeSupport H _)
    · intro y _ hy
      have hyA : (y : G) ∉ A := by simpa [hT] using hy
      simp [hF, dadeDomain.apply_eq_zero f.2 hyA]
  have key := hD.natCard_mul_sum_eq_natCard_mul_sum hw0 hwD hS
  rw [hSsum] at key
  have hGne : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hLne : (Nat.card ↥L : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  rw [cfInner_def, cfInner_def]
  change (Nat.card G : ℂ)⁻¹ * ∑ x : G, w x = (Nat.card ↥L : ℂ)⁻¹ * ∑ y : ↥L, F y
  field_simp
  linear_combination key

theorem cfInner_self_dadeMap (hD : IsDadeData L A H) (f : dadeDomain L A) :
    cfInner ((dadeMap hD f : classFun G) : G → ℂ) ((dadeMap hD f : classFun G) : G → ℂ)
      = cfInner (f : ↥L → ℂ) (f : ↥L → ℂ) :=
  cfInner_dadeMap hD f f

end Isometry

end CFSG.FeitThompson

end
