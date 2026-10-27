module

public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.HardMathSupport.Meierfrankenfeld.Proving.PerfectCommutator

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15OffenderLift

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.HardMathSupport.Meierfrankenfeld.Proving
open scoped commutatorElement

structure InnerCtx {K : Type*} [Group K] (L B : Subgroup K) : Prop where
  normalizes : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ ∈ L
  quasi : CFSG.Open.IsQuasisimple ↥L
  hZ : ∀ z ∈ L, (∀ k ∈ L, k * z = z * k) → z ^ 3 = 1
  sq : ∀ b ∈ B, b * b = 1
  comm : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b
  top : L ⊔ B = ⊤

namespace InnerCtx

variable {K : Type*} [Group K] {L B : Subgroup K} (h : InnerCtx L B)

include h

theorem inv_eq {b : K} (hb : b ∈ B) : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h.sq b hb)

theorem normal_L : L.Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← h.top]
  refine sup_le Subgroup.le_normalizer fun b hb => ?_
  rw [Subgroup.mem_normalizer_iff]
  intro l
  refine ⟨h.normalizes b hb l, fun hl => ?_⟩
  have e1 := h.normalizes b hb _ hl
  have e2 : b * (b * l * b⁻¹) * b⁻¹ = l := by
    calc b * (b * l * b⁻¹) * b⁻¹ = (b * b) * l * (b * b)⁻¹ := by group
      _ = l := by rw [h.sq b hb]; group
  rwa [e2] at e1

end InnerCtx

section Rep

variable {K Z : Type*} [Group K] [AddCommGroup Z] [Module (ZMod 2) Z]
  (κ : Representation (ZMod 2) K Z)

theorem repMulApply (g k : K) (z : Z) : κ (g * k) z = κ g (κ k z) := by
  rw [map_mul]
  rfl

theorem repApplyInv (g : K) (z : Z) : κ g (κ g⁻¹ z) = z := by
  rw [← repMulApply, mul_inv_cancel, map_one]
  rfl

theorem repInvApply (g : K) (z : Z) : κ g⁻¹ (κ g z) = z := by
  rw [← repMulApply, inv_mul_cancel, map_one]
  rfl

theorem zmod_two_add_self (z : Z) : z + z = 0 := by
  rw [← two_smul (ZMod 2) z]
  have : (2 : ZMod 2) = 0 := rfl
  rw [this, zero_smul]

theorem kappa_eq_one_of_central [Nontrivial Z]
    (hirr : ∀ W : Submodule (ZMod 2) Z, (∀ k : K, ∀ z ∈ W, κ k z ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : K} (hc : ∀ k : K, c * k = k * c) (hc2 : c * c = 1) (z : Z) : κ c z = z := by
  let W : Submodule (ZMod 2) Z :=
    { carrier := {w | κ c w = w}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_add, hx, hy]
      zero_mem' := map_zero _
      smul_mem' := fun a x hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [map_smul, hx] }
  have hW : ∀ k : K, ∀ w ∈ W, κ k w ∈ W := by
    intro k w hw
    show κ c (κ k w) = κ k w
    rw [← repMulApply, hc k, repMulApply]
    exact congrArg (κ k) hw
  rcases hirr W hW with hbot | htop
  · exfalso
    obtain ⟨z0, hz0⟩ := exists_ne (0 : Z)
    have h1 : κ c z0 + z0 ∈ W := by
      show κ c (κ c z0 + z0) = κ c z0 + z0
      rw [map_add, ← repMulApply, hc2, map_one]
      exact add_comm _ _
    rw [hbot, Submodule.mem_bot] at h1
    have h2 : κ c z0 = z0 :=
      (eq_neg_of_add_eq_zero_left h1).trans (neg_eq_of_add_eq_zero_right (zmod_two_add_self z0))
    have h3 : z0 ∈ W := h2
    rw [hbot, Submodule.mem_bot] at h3
    exact hz0 h3
  · have : z ∈ W := by rw [htop]; exact Submodule.mem_top
    exact this

end Rep

section Fix

variable {K Z : Type*} [Group K] [AddCommGroup Z] [Module (ZMod 2) Z] {L : Subgroup K}

theorem commute_of_fix (hq : CFSG.Open.IsQuasisimple ↥L) (κ : Representation (ZMod 2) K Z)
    (Y : Submodule (ZMod 2) Z) (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, κ l y ≠ y) {x : K} (hx : x ∈ L) (hxY : ∀ y ∈ Y, κ x y = y) :
    ∀ k ∈ L, x * k = k * x := by
  let C : Subgroup ↥L :=
    { carrier := {g | ∀ y ∈ Y, κ (g : K) y = y}
      one_mem' := fun y _ => by simp
      mul_mem' := fun {a b} ha hb y hy => by
        show κ ((a : K) * (b : K)) y = y
        rw [repMulApply, hb y hy, ha y hy]
      inv_mem' := fun {a} ha y hy => by
        have h1 : κ (a : K) (κ (a : K)⁻¹ y) = κ (a : K)⁻¹ y :=
          ha _ (hY _ (L.inv_mem a.2) y hy)
        rw [repApplyInv] at h1
        exact h1.symm }
  have hCn : C.Normal :=
    ⟨fun a ha g y hy => by
      show κ ((g : K) * (a : K) * (g : K)⁻¹) y = y
      have h1 : κ (g : K)⁻¹ y ∈ Y := hY _ (L.inv_mem g.2) y hy
      rw [repMulApply, repMulApply, ha _ h1, repApplyInv]⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hq C with hle | htop
  · have hmem : (⟨x, hx⟩ : ↥L) ∈ C := hxY
    have hc := Subgroup.mem_center_iff.mp (hle hmem)
    intro k hk
    exact (congrArg Subtype.val (hc ⟨k, hk⟩)).symm
  · exfalso
    obtain ⟨l, hl, y, hy, hne⟩ := hnt
    have : (⟨l, hl⟩ : ↥L) ∈ C := by rw [htop]; exact Subgroup.mem_top _
    exact hne (this y hy)

theorem centralizes_of_fix [L.Normal] (hq : CFSG.Open.IsQuasisimple ↥L)
    (κ : Representation (ZMod 2) K Z) (Y : Submodule (ZMod 2) Z)
    (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y) (hnt : ∃ l ∈ L, ∃ y ∈ Y, κ l y ≠ y) {c : K}
    (hc : ∀ y ∈ Y, κ c y = y) : c ∈ Subgroup.centralizer (L : Set K) := by
  have hperf : ⁅L, L⁆ = L := by
    rw [← Subgroup.map_subtype_commutator, hq.1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let J : Subgroup K :=
    { carrier := {j | ∀ y ∈ Y, κ j y = y}
      one_mem' := fun y _ => by simp
      mul_mem' := fun {a b} ha hb y hy => by
        show κ (a * b) y = y
        rw [repMulApply, hb y hy, ha y hy]
      inv_mem' := fun {a} ha y hy => by
        have h1 := repInvApply κ a y
        rw [ha y hy] at h1
        exact h1 }
  have hLJ : ⁅L, J⁆ ≤ Subgroup.centralizer (L : Set K) := by
    rw [Subgroup.commutator_le]
    intro l hl j hj
    have hmem : ⁅l, j⁆ ∈ L := by
      have : ⁅l, j⁆ = l * (j * l⁻¹ * j⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [this]
      exact L.mul_mem hl (‹L.Normal›.conj_mem l⁻¹ (L.inv_mem hl) j)
    have hfix : ∀ y ∈ Y, κ ⁅l, j⁆ y = y := by
      intro y hy
      have h1 : κ j⁻¹ y = y := J.inv_mem hj y hy
      have h2 : κ l⁻¹ y ∈ Y := hY _ (L.inv_mem hl) y hy
      have h3 : κ j (κ l⁻¹ y) = κ l⁻¹ y := hj _ h2
      rw [commutatorElement_def, repMulApply, repMulApply, repMulApply, h1, h3, repApplyInv]
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (commute_of_fix hq κ Y hY hnt hmem hfix k hk).symm
  exact le_centralizer_of_isPerfect hperf (Subgroup.commutator_eq_bot_iff_le_centralizer.2 hLJ) hc

end Fix

namespace InnerCtx

variable {K Z : Type*} [Group K] [AddCommGroup Z] [Module (ZMod 2) Z] {L B : Subgroup K}
  (h : InnerCtx L B) (κ : Representation (ZMod 2) K Z)

include h

theorem centralizes_of_fix' (Y : Submodule (ZMod 2) Z) (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, κ l y ≠ y) {c : K} (hc : ∀ y ∈ Y, κ c y = y) :
    c ∈ Subgroup.centralizer (L : Set K) := by
  haveI := h.normal_L
  exact centralizes_of_fix h.quasi κ Y hY hnt hc

theorem central_of_centralizes {b : K} (hb : b ∈ B) (hcen : b ∈ Subgroup.centralizer (L : Set K)) :
    ∀ k : K, b * k = k * b := by
  have hL : L ≤ Subgroup.centralizer ({b} : Set K) := fun l hl => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ((Subgroup.mem_centralizer_iff.mp hcen) l hl).symm
  have hB : B ≤ Subgroup.centralizer ({b} : Set K) := fun c hc => by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h.comm x hb c hc
  have htop : (⊤ : Subgroup K) ≤ Subgroup.centralizer ({b} : Set K) := by
    rw [← h.top]
    exact sup_le hL hB
  intro k
  exact (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top k))) b (Set.mem_singleton b)

theorem kappa_eq_one_of_fix [Nontrivial Z]
    (hirr : ∀ W : Submodule (ZMod 2) Z, (∀ k : K, ∀ z ∈ W, κ k z ∈ W) → W = ⊥ ∨ W = ⊤)
    (Y : Submodule (ZMod 2) Z) (hY : ∀ l ∈ L, ∀ y ∈ Y, κ l y ∈ Y)
    (hnt : ∃ l ∈ L, ∃ y ∈ Y, κ l y ≠ y) {b : K} (hb : b ∈ B) (hbY : ∀ y ∈ Y, κ b y = y)
    (z : Z) : κ b z = z :=
  kappa_eq_one_of_central κ hirr
    (h.central_of_centralizes hb (h.centralizes_of_fix' κ Y hY hnt hbY)) (h.sq b hb) z

theorem conjAgree_of_kappa_eq (hnt : ∃ l ∈ L, ∃ z, κ l z ≠ z) {b l : K}
    (hbl : ∀ z, κ b z = κ l z) : ConjAgree L b l := by
  have hc : l⁻¹ * b ∈ Subgroup.centralizer (L : Set K) := by
    refine h.centralizes_of_fix' κ ⊤ (fun _ _ _ _ => Submodule.mem_top) ?_ (c := l⁻¹ * b) ?_
    · obtain ⟨l, hl, z, hz⟩ := hnt
      exact ⟨l, hl, z, Submodule.mem_top, hz⟩
    · intro y _
      rw [repMulApply, hbl, repInvApply]
  intro k hk
  have hck : (l⁻¹ * b) * k * (l⁻¹ * b)⁻¹ = k := by
    have := (Subgroup.mem_centralizer_iff.mp hc) k hk
    rw [← this]
    group
  calc b * k * b⁻¹ = l * ((l⁻¹ * b) * k * (l⁻¹ * b)⁻¹) * l⁻¹ := by group
    _ = l * k * l⁻¹ := by rw [hck]

end InnerCtx

structure ChiefData {K Z : Type*} [Group K] [AddCommGroup Z] [Module (ZMod 2) Z]
    (L B : Subgroup K) (κ : Representation (ZMod 2) K Z) : Prop where
  nontrivial : Nontrivial Z
  irr : ∀ W : Submodule (ZMod 2) Z, (∀ k : K, ∀ z ∈ W, κ k z ∈ W) → W = ⊥ ∨ W = ⊤
  hL : ∃ l ∈ L, ∃ z, κ l z ≠ z
  quad : ∀ a ∈ B, ∀ b ∈ B, ∀ z, κ b (κ a z - z) = κ a z - z
  budget : Nat.card Z * Nat.card ↥(B ⊓ MonoidHom.ker κ) ≤
    Nat.card ↥B * Nat.card {z : Z // ∀ b ∈ B, κ b z = z}

end CFSG.LocalAnalysis.RankThreeUC.S15
