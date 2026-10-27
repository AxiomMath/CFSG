module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Tactic.Ring.RingNF

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.GLTheoremA

section Klein

variable {L : Type*} [AddCommGroup L] [Module (ZMod 3) L]

def fixSp (t : L →ₗ[ZMod 3] L) : Submodule (ZMod 3) L := LinearMap.ker (t - LinearMap.id)

def negSp (t : L →ₗ[ZMod 3] L) : Submodule (ZMod 3) L := LinearMap.ker (t + LinearMap.id)

theorem mem_fixSp {t : L →ₗ[ZMod 3] L} {x : L} : x ∈ fixSp t ↔ t x = x := by
  simp [fixSp, LinearMap.mem_ker, sub_eq_zero]

theorem mem_negSp {t : L →ₗ[ZMod 3] L} {x : L} : x ∈ negSp t ↔ t x = -x := by
  simp [negSp, LinearMap.mem_ker, add_eq_zero_iff_eq_neg]

theorem eq_zero_of_two_smul {x : L} (h : (2 : ZMod 3) • x = 0) : x = 0 := by
  have h22 : (2 : ZMod 3) * 2 = 1 := by decide
  have : x = (2 : ZMod 3) • ((2 : ZMod 3) • x) := by rw [smul_smul, h22, one_smul]
  rw [this, h, smul_zero]

theorem card_split [Finite L] (t : L →ₗ[ZMod 3] L) (ht : ∀ x, t (t x) = x)
    (W : Submodule (ZMod 3) L) (hW : ∀ x ∈ W, t x ∈ W) :
    Nat.card W = Nat.card (W ⊓ fixSp t : Submodule (ZMod 3) L) *
      Nat.card (W ⊓ negSp t : Submodule (ZMod 3) L) := by
  classical
  have h22 : (2 : ZMod 3) * 2 = 1 := by decide
  let f : (↥(W ⊓ fixSp t) × ↥(W ⊓ negSp t)) → W := fun p =>
    ⟨p.1.1 + p.2.1, W.add_mem p.1.2.1 p.2.2.1⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
      have h' : a + b = a' + b' := congrArg Subtype.val h
      have hta : t a = a := mem_fixSp.1 ha.2
      have hta' : t a' = a' := mem_fixSp.1 ha'.2
      have htb : t b = -b := mem_negSp.1 hb.2
      have htb' : t b' = -b' := mem_negSp.1 hb'.2
      have hd : a - a' = b' - b := by
        calc a - a' = (a + b) - (a' + b') + (b' - b) := by abel
          _ = b' - b := by rw [h', sub_self, zero_add]
      have hd1 : t (a - a') = a - a' := by rw [map_sub, hta, hta']
      have hd2 : t (a - a') = -(a - a') := by rw [hd, map_sub, htb, htb']; abel
      have hz : (2 : ZMod 3) • (a - a') = 0 := by
        rw [two_smul]
        have : a - a' = -(a - a') := hd1.symm.trans hd2
        nth_rewrite 1 [this]
        abel
      have h0 : a - a' = 0 := eq_zero_of_two_smul hz
      have haa : a = a' := sub_eq_zero.1 h0
      have hbb : b = b' := by
        have : b' - b = 0 := hd ▸ h0
        exact (sub_eq_zero.1 this).symm
      subst haa; subst hbb; rfl
    · rintro ⟨x, hx⟩
      have hx1 : t x ∈ W := hW x hx
      refine ⟨(⟨(2 : ZMod 3) • (x + t x), ?_, ?_⟩, ⟨(2 : ZMod 3) • (x - t x), ?_, ?_⟩), ?_⟩
      · exact W.smul_mem _ (W.add_mem hx hx1)
      · rw [SetLike.mem_coe, mem_fixSp, map_smul, map_add, ht, add_comm]
      · exact W.smul_mem _ (W.sub_mem hx hx1)
      · rw [SetLike.mem_coe, mem_negSp, map_smul, map_sub, ht, ← smul_neg, neg_sub]
      · refine Subtype.ext ?_
        change (2 : ZMod 3) • (x + t x) + (2 : ZMod 3) • (x - t x) = x
        rw [← smul_add, show x + t x + (x - t x) = x + x by abel, ← two_smul (ZMod 3) x, smul_smul, h22,
          one_smul]
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem card_eq_fix_mul_neg [Finite L] (t : L →ₗ[ZMod 3] L) (ht : ∀ x, t (t x) = x) :
    Nat.card L = Nat.card (fixSp t) * Nat.card (negSp t) := by
  have h := card_split t ht ⊤ (fun x _ => Submodule.mem_top)
  rw [top_inf_eq, top_inf_eq] at h
  rw [← h]
  exact (Nat.card_congr (Submodule.topEquiv (R := ZMod 3) (M := L)).toEquiv).symm

theorem klein_card [Finite L] (t₁ t₂ : L →ₗ[ZMod 3] L) (h₁ : ∀ x, t₁ (t₁ x) = x)
    (h₂ : ∀ x, t₂ (t₂ x) = x) (hc : ∀ x, t₁ (t₂ x) = t₂ (t₁ x)) :
    Nat.card (fixSp t₁) * Nat.card (fixSp t₂) * Nat.card (fixSp (t₁ * t₂)) =
      Nat.card L * Nat.card (fixSp t₁ ⊓ fixSp t₂ : Submodule (ZMod 3) L) ^ 2 := by
  have hL := card_eq_fix_mul_neg t₁ h₁
  have hs2 := card_split t₁ h₁ (fixSp t₂) (fun x hx => by
    rw [mem_fixSp] at hx ⊢; rw [← hc, hx])
  have hs3 := card_split t₁ h₁ (fixSp (t₁ * t₂)) (fun x hx => by
    rw [mem_fixSp, Module.End.mul_apply] at hx
    rw [mem_fixSp, Module.End.mul_apply, ← hc, hx])
  have e1 : (fixSp (t₁ * t₂) ⊓ fixSp t₁ : Submodule (ZMod 3) L) = fixSp t₂ ⊓ fixSp t₁ := by
    ext x
    simp only [Submodule.mem_inf, mem_fixSp, Module.End.mul_apply]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨?_, h'⟩
      have h3 := hc x
      rw [h'] at h3
      exact h3.symm.trans h
    · rintro ⟨h, h'⟩; exact ⟨by rw [h, h'], h'⟩
  have e2 : (fixSp (t₁ * t₂) ⊓ negSp t₁ : Submodule (ZMod 3) L) = negSp t₂ ⊓ negSp t₁ := by
    ext x
    simp only [Submodule.mem_inf, mem_fixSp, mem_negSp, Module.End.mul_apply]
    constructor
    · rintro ⟨h, h'⟩
      refine ⟨?_, h'⟩
      have : t₁ (t₂ x) = x := h
      have h3 : t₂ x = t₁ x := by
        have := congrArg t₁ this
        rwa [h₁] at this
      rw [h3, h']
    · rintro ⟨h, h'⟩
      refine ⟨?_, h'⟩
      rw [h, map_neg, h']; simp
  have hs4 := card_split t₂ h₂ (negSp t₁) (fun x hx => by
    rw [mem_negSp] at hx ⊢; rw [hc, hx, map_neg])
  rw [e1, e2] at hs3
  have hcomm12 : (fixSp t₂ ⊓ fixSp t₁ : Submodule (ZMod 3) L) = fixSp t₁ ⊓ fixSp t₂ := inf_comm _ _
  have hcomm34 : (negSp t₁ ⊓ negSp t₂ : Submodule (ZMod 3) L) = negSp t₂ ⊓ negSp t₁ := inf_comm _ _
  have hcomm5 : (negSp t₁ ⊓ fixSp t₂ : Submodule (ZMod 3) L) = fixSp t₂ ⊓ negSp t₁ := inf_comm _ _
  rw [hcomm12] at hs2 hs3
  rw [hcomm34] at hs4
  rw [hcomm5] at hs4
  calc Nat.card (fixSp t₁) * Nat.card (fixSp t₂) * Nat.card (fixSp (t₁ * t₂))
      = Nat.card (fixSp t₁) * ((Nat.card (fixSp t₁ ⊓ fixSp t₂ : Submodule (ZMod 3) L) *
          Nat.card (fixSp t₂ ⊓ negSp t₁ : Submodule (ZMod 3) L)) *
          (Nat.card (fixSp t₁ ⊓ fixSp t₂ : Submodule (ZMod 3) L) *
          Nat.card (negSp t₂ ⊓ negSp t₁ : Submodule (ZMod 3) L))) := by rw [hs2, hs3]; ring
    _ = Nat.card (fixSp t₁) * (Nat.card (fixSp t₁ ⊓ fixSp t₂ : Submodule (ZMod 3) L) ^ 2 *
          Nat.card (negSp t₁)) := by rw [hs4]; ring
    _ = _ := by rw [hL]; ring

theorem card_sq_of_anticomm [Finite L] (t : L →ₗ[ZMod 3] L) (ht : ∀ x, t (t x) = x)
    (y : L ≃ₗ[ZMod 3] L) (hy : ∀ x, y (t x) = -(t (y x))) :
    Nat.card (fixSp t) ^ 2 = Nat.card L := by
  have hL := card_eq_fix_mul_neg t ht
  have hFN : Nat.card (fixSp t) = Nat.card (negSp t) := by
    let g : fixSp t → negSp t := fun x => ⟨y x.1, by
      rw [mem_negSp]
      have h1 := hy x.1
      rw [mem_fixSp.1 x.2] at h1
      calc t (y x.1) = -(-(t (y x.1))) := (neg_neg _).symm
        _ = -(y x.1) := by rw [← h1]⟩
    have hg : Function.Bijective g := by
      constructor
      · intro a b h
        exact Subtype.ext (y.injective (congrArg Subtype.val h))
      · rintro ⟨z, hz⟩
        have hz' : t z = -z := mem_negSp.1 hz
        refine ⟨⟨y.symm z, ?_⟩, Subtype.ext (by simp [g])⟩
        rw [mem_fixSp]
        apply y.injective
        have h1 := hy (y.symm z)
        rw [LinearEquiv.apply_symm_apply] at h1
        have h2 : y (t (y.symm z)) = -(t z) := by
          have : y (t (y.symm z)) = -(t (y (y.symm z))) := hy (y.symm z)
          rwa [LinearEquiv.apply_symm_apply] at this
        rw [h2, hz', neg_neg, LinearEquiv.apply_symm_apply]
    exact Nat.card_congr (Equiv.ofBijective g hg)
  rw [hL, ← hFN]; ring

theorem card_fix_klein_le [Finite L] (t₁ t₂ : L →ₗ[ZMod 3] L) (h₁ : ∀ x, t₁ (t₁ x) = x)
    (h₂ : ∀ x, t₂ (t₂ x) = x) (hc : ∀ x, t₁ (t₂ x) = t₂ (t₁ x))
    (c₁ : Nat.card (fixSp t₁) ^ 2 ≤ Nat.card L) (c₂ : Nat.card (fixSp t₂) ^ 2 ≤ Nat.card L)
    (c₃ : Nat.card (fixSp (t₁ * t₂)) ^ 2 ≤ Nat.card L) :
    Nat.card (fixSp t₁ ⊓ fixSp t₂ : Submodule (ZMod 3) L) ^ 4 ≤ Nat.card L := by
  have h := klein_card t₁ t₂ h₁ h₂ hc
  have hpos : 0 < Nat.card L := Nat.card_pos
  have hsq : (Nat.card (fixSp t₁) * Nat.card (fixSp t₂) * Nat.card (fixSp (t₁ * t₂))) ^ 2 ≤
      Nat.card L ^ 3 := by
    calc (Nat.card (fixSp t₁) * Nat.card (fixSp t₂) * Nat.card (fixSp (t₁ * t₂))) ^ 2
        = Nat.card (fixSp t₁) ^ 2 * Nat.card (fixSp t₂) ^ 2 * Nat.card (fixSp (t₁ * t₂)) ^ 2 := by ring
      _ ≤ Nat.card L * Nat.card L * Nat.card L := Nat.mul_le_mul (Nat.mul_le_mul c₁ c₂) c₃
      _ = Nat.card L ^ 3 := by ring
  rw [h] at hsq
  have h2 : Nat.card L ^ 2 * (Nat.card (fixSp t₁ ⊓ fixSp t₂ : Submodule (ZMod 3) L) ^ 4) ≤
      Nat.card L ^ 2 * Nat.card L := by
    calc Nat.card L ^ 2 * (Nat.card (fixSp t₁ ⊓ fixSp t₂ : Submodule (ZMod 3) L) ^ 4)
        = (Nat.card L * Nat.card (fixSp t₁ ⊓ fixSp t₂ : Submodule (ZMod 3) L) ^ 2) ^ 2 := by ring
      _ ≤ Nat.card L ^ 3 := hsq
      _ = Nat.card L ^ 2 * Nat.card L := by ring
  exact Nat.le_of_mul_le_mul_left h2 (pow_pos hpos 2)

end Klein

end CFSG.LocalAnalysis.GLTheoremA
