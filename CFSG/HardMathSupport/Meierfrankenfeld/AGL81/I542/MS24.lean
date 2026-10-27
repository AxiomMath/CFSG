module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open scoped commutatorElement

variable {G : Type*} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem rep_apply_inv_apply (ρ : Representation (ZMod 2) G W) (g : G) (v : W) :
    ρ g (ρ g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl

theorem rep_inv_apply_apply (ρ : Representation (ZMod 2) G W) (g : G) (v : W) :
    ρ g⁻¹ (ρ g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl

@[expose] def fixCen (ρ : Representation (ZMod 2) G W) (K B : Subgroup G) :
    Submodule (ZMod 2) W where
  carrier := {v | ∀ c ∈ B, (∀ k ∈ K, c * k = k * c) → ρ c v = v}
  add_mem' {u v} hu hv c hc hcK := by rw [map_add, hu c hc hcK, hv c hc hcK]
  zero_mem' c _ _ := map_zero _
  smul_mem' a v hv c hc hcK := by rw [map_smul, hv c hc hcK]

theorem fixCen_invariant (ρ : Representation (ZMod 2) G W) (K B : Subgroup G) {k : G}
    (hk : k ∈ K) {v : W} (hv : v ∈ fixCen ρ K B) : ρ k v ∈ fixCen ρ K B := by
  intro c hc hcK
  have h := hcK k hk
  calc ρ c (ρ k v) = ρ (c * k) v := by rw [map_mul, Module.End.mul_apply]
    _ = ρ (k * c) v := by rw [h]
    _ = ρ k (ρ c v) := by rw [map_mul, Module.End.mul_apply]
    _ = ρ k v := by rw [hv c hc hcK]

theorem ms24 (ρ : Representation (ZMod 2) G W) {K B : Subgroup G} {U : Submodule (ZMod 2) W}
    (hUK : GeneralFF.IsInvariant ρ K U) (hUB : GeneralFF.IsInvariant ρ B U) (hKB : ⁅K, B⁆ = K)
    (hUU : commOn ρ K U = U) (hq : IsQuadraticOn ρ B U) :
    ∀ b ∈ B, (∀ k ∈ K, b * k = k * b) → ∀ u ∈ U, ρ b u = u := by
  set F := fixCen ρ K B with hF
  have hQF : ∀ w ∈ commOn ρ B U, w ∈ F := fun w hw c hc _ => mem_fixSub.1 (hq hw) c hc
  have hinF : ∀ b ∈ B, ∀ w ∈ U, ρ b w - w ∈ F := fun b hb w hw =>
    hQF _ (Submodule.subset_span ⟨b, hb, w, hw, rfl⟩)
  have hgen : ∀ k ∈ K, ∀ b ∈ B, ∀ u ∈ U, ρ ⁅k, b⁆ u - u ∈ F := by
    intro k hk b hb u hu
    have e : ρ ⁅k, b⁆ u - u = ρ k (ρ b (ρ k⁻¹ (ρ b⁻¹ u)) - ρ k⁻¹ (ρ b⁻¹ u)) -
        (ρ b (ρ b⁻¹ u) - ρ b⁻¹ u) := by
      rw [commutatorElement_def]
      simp only [map_mul, Module.End.mul_apply, map_sub]
      rw [rep_apply_inv_apply ρ k, rep_apply_inv_apply ρ b]
      abel
    rw [e]
    have hv' : ρ b⁻¹ u ∈ U := hUB b⁻¹ (B.inv_mem hb) u hu
    have hw : ρ k⁻¹ (ρ b⁻¹ u) ∈ U := hUK k⁻¹ (K.inv_mem hk) _ hv'
    exact F.sub_mem (fixCen_invariant ρ K B hk (hinF b hb _ hw)) (hinF b hb _ hv')
  let S : Subgroup G :=
    { carrier := {g | g ∈ K ∧ ∀ u ∈ U, ρ g u - u ∈ F}
      mul_mem' := fun {a b} ha hb => ⟨K.mul_mem ha.1 hb.1, fun u hu => by
        have e : ρ (a * b) u - u = ρ a (ρ b u - u) + (ρ a u - u) := by
          simp only [map_mul, Module.End.mul_apply, map_sub]; abel
        rw [e]
        exact F.add_mem (fixCen_invariant ρ K B ha.1 (hb.2 u hu)) (ha.2 u hu)⟩
      one_mem' := ⟨K.one_mem, fun u _ => by simp⟩
      inv_mem' := fun {a} ha => ⟨K.inv_mem ha.1, fun u hu => by
        have e : ρ a⁻¹ u - u = -ρ a⁻¹ (ρ a u - u) := by
          rw [map_sub, rep_inv_apply_apply ρ a]; abel
        rw [e]
        exact F.neg_mem (fixCen_invariant ρ K B (K.inv_mem ha.1) (ha.2 u hu))⟩ }
  have hKS : K ≤ S := by
    have h : ⁅K, B⁆ ≤ S := by
      rw [Subgroup.commutator_le]
      intro k hk b hb
      refine ⟨?_, hgen k hk b hb⟩
      have := Subgroup.commutator_mem_commutator hk hb
      rwa [hKB] at this
    rwa [hKB] at h
  have hcom : commOn ρ K U ≤ F := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, u, hu, rfl⟩
    exact (hKS hk).2 u hu
  intro b hb hbK u hu
  have : u ∈ commOn ρ K U := by rw [hUU]; exact hu
  exact hcom this b hb hbK

theorem isInvariant_commOn_top (ρ : Representation (ZMod 2) G W) {K B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer K) : GeneralFF.IsInvariant ρ B (commOn ρ K ⊤) := by
  intro b hb u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, v, -, rfl⟩ := hx
    have hkK : b * k * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hBN hb) k).1 hk
    have e : ρ b (ρ k v - v) = ρ (b * k * b⁻¹) (ρ b v) - ρ b v := by
      simp only [map_mul, Module.End.mul_apply, map_sub]
      rw [rep_inv_apply_apply ρ b]
    rw [e]
    exact Submodule.subset_span ⟨_, hkK, _, Submodule.mem_top, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem ms24_comm (ρ : Representation (ZMod 2) G W) {K B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer K) (hKB : ⁅K, B⁆ = K)
    (hUU : commOn ρ K (commOn ρ K ⊤) = commOn ρ K ⊤)
    (hq : IsQuadraticOn ρ B (commOn ρ K ⊤)) :
    ∀ b ∈ B, (∀ k ∈ K, b * k = k * b) → ∀ u ∈ commOn ρ K ⊤, ρ b u = u := by
  refine ms24 ρ (U := commOn ρ K ⊤) ?_ (isInvariant_commOn_top ρ hBN) hKB hUU hq
  exact isInvariant_commOn_top ρ (Subgroup.le_normalizer (H := K))

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
