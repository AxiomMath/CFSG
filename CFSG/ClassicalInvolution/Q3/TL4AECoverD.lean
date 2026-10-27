module

public import CFSG.ClassicalInvolution.Q3.TL4AECoverB
public import CFSG.ClassicalInvolution.Q3.TL4D1AE3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {n : ℕ}

theorem conjSub_yBar_memBar (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    conjSub (yBar α h) (memBar α h b) = memBar α h b := by
  have hy2 : (yBar α h)⁻¹ = yBar α h * yBar α h := by
    rw [inv_eq_iff_mul_eq_one, ← yBar_pow_three α h, pow_succ, pow_two, mul_assoc]
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have e : x = yBar α h * ((yBar α h)⁻¹ * x * yBar α h) * (yBar α h)⁻¹ := by group
    rw [e]
    exact yBar_conj_mem_memBar α h b _ hx
  · intro hx
    have e : (yBar α h)⁻¹ * x * yBar α h =
        yBar α h * (yBar α h * x * (yBar α h)⁻¹) * (yBar α h)⁻¹ := by
      rw [show yBar α h * (yBar α h * x * (yBar α h)⁻¹) * (yBar α h)⁻¹ =
        (yBar α h * yBar α h) * x * (yBar α h * yBar α h)⁻¹ by group, ← hy2, inv_inv]
    rw [e]
    exact yBar_conj_mem_memBar α h b _ (yBar_conj_mem_memBar α h b x hx)

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {k : ℕ}

theorem subgroupOf_le_commutator (I : AEIdent P k) (hk : 5 ≤ k)
    (h8 : ∀ L ∈ P, Nat.card ↥L = 8)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    {L : Subgroup G} (hL : L ∈ P) : L.subgroupOf (pSpan P) ≤ commutator ↥(pSpan P) := by
  obtain ⟨α, h, b, hlab⟩ := I.label L hL
  have hyr : yBar α h ∈ I.φ.range := by
    rw [I.range_eq]
    exact yBar_mem α h
  obtain ⟨y, hy⟩ := hyr
  have hyL : conjSub (y : G) L = L := by
    refine hinj _ (hconj L hL y y.2) L hL ?_
    rw [map_conjSub_eq, hy, hlab, conjSub_yBar_memBar]
  set D := commutator ↥(pSpan P) ⊓ L.subgroupOf (pSpan P) with hD
  have hgen : memBar α h b ≤ D.map I.φ := by
    refine (memBar_le_closure_yBar α h b).trans ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    rw [← hlab] at hm
    obtain ⟨l', hl', rfl⟩ := hm
    refine ⟨l' * y * l'⁻¹ * y⁻¹, ⟨?_, ?_⟩, by rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy]⟩
    · rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    · have hl'' : (l' : G) ∈ L := hl'
      show l' * y * l'⁻¹ * y⁻¹ ∈ L.subgroupOf (pSpan P)
      rw [Subgroup.mem_subgroupOf]
      have h1 : (y : G) * (l' : G)⁻¹ * (y : G)⁻¹ ∈ L := by
        rw [← hyL]
        exact conj_mem_conjSub (L.inv_mem hl'')
      have h2 := L.mul_mem hl'' h1
      simpa [mul_assoc] using h2
  intro l hl
  have hφl : I.φ l ∈ memBar α h b := by
    rw [← hlab]
    exact ⟨l, hl, rfl⟩
  obtain ⟨d, ⟨hdc, hdL⟩, hde⟩ := hgen hφl
  have hdl : (d : G) = l := I.injOn hk hL (h8 L hL) hlab (Subgroup.mem_subgroupOf.mp hdL)
    (Subgroup.mem_subgroupOf.mp hl) hde
  rw [show l = d from (Subtype.ext hdl).symm]
  exact hdc

theorem isPerfect_pSpan (I : AEIdent P k) (hk : 5 ≤ k)
    (h8 : ∀ L ∈ P, Nat.card ↥L = 8)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L') :
    Group.IsPerfect ↥(pSpan P) := by
  refine ⟨eq_top_iff.mpr fun x _ => ?_⟩
  have hle : pSpan P ≤ (commutator ↥(pSpan P)).map (pSpan P).subtype := by
    refine pSpan_le fun L hL l hl => ?_
    have hlX : l ∈ pSpan P := le_pSpan hL hl
    refine ⟨⟨l, hlX⟩, subgroupOf_le_commutator I hk h8 hconj hinj hL ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr hl
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show y = x from Subtype.ext hyx] at hy

end CFSG.ClassicalInvolution.Q3.TL4.AECov
