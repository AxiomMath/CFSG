module

public import CFSG.ClassicalInvolution.Q3.TL4AECoverA
public import CFSG.ClassicalInvolution.Q3.TL3T10

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.AECov

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

variable {G : Type} [Group G] {P : Set (Subgroup G)} {k : ℕ}

theorem map_conjSub_eq (I : AEIdent P k) (L : Subgroup G) (x : ↥(pSpan P)) :
    ((conjSub (x : G) L).subgroupOf (pSpan P)).map I.φ =
      conjSub (I.φ x) ((L.subgroupOf (pSpan P)).map I.φ) := by
  ext m
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_conjSub_iff] at hy
    rw [mem_conjSub_iff]
    refine ⟨x⁻¹ * y * x, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · intro hm
    rw [mem_conjSub_iff] at hm
    obtain ⟨y, hy, hye⟩ := hm
    refine ⟨x * y * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · show (x : G) * y * (x : G)⁻¹ ∈ conjSub (x : G) L
      exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hy)
    · rw [map_mul, map_mul, map_inv, hye]
      group

variable [Finite G]

theorem comm_of_isUniqueInvolution (I : AEIdent P k) (hk : 5 ≤ k)
    (h8 : ∀ L ∈ P, Nat.card ↥L = 8)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    (htwin : ∀ (α : Finset (Fin k)) (h : α.card = 4), ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = memBar α h true →
      (L'.subgroupOf (pSpan P)).map I.φ = memBar α h false →
      ∀ u u' : G, IsUniqueInvolution L u → IsUniqueInvolution L' u' → u = u')
    {L L' : Subgroup G} (hL : L ∈ P) (hL' : L' ∈ P) {u u' : G}
    (hu : IsUniqueInvolution L u) (hu' : IsUniqueInvolution L' u') : u * u' = u' * u := by
  obtain ⟨α, h, b, hlab⟩ := I.label L hL
  obtain ⟨β, h', c, hlab'⟩ := I.label L' hL'
  have hu'X : u' ∈ pSpan P := le_pSpan hL' hu'.mem
  have hMP : conjSub u' L ∈ P := hconj L hL u' hu'X
  have hz' : I.φ ⟨u', hu'X⟩ = zBar β h' := I.map_eq_zBar hk hL' (h8 L' hL') hlab' hu'
  have hlabM : ((conjSub u' L).subgroupOf (pSpan P)).map I.φ =
      conjSub (mkQ k (zOf (emb β h'))) (memBar α h b) := by
    have e := map_conjSub_eq I L ⟨u', hu'X⟩
    rw [hz', hlab] at e
    exact e
  have hzM : IsUniqueInvolution (conjSub u' L) (u' * u * u'⁻¹) := hu.conj u'
  have key : u' * u * u'⁻¹ = u := by
    rcases conjSub_memBar_of_perm_eq_one (zOf_perm (emb β h')) α h b with h1 | h1 <;>
      rw [h1] at hlabM <;> cases b
    · exact htwin α h _ hMP L hL hlabM hlab _ u hzM hu
    · have hML := hinj _ hMP L hL (hlabM.trans hlab.symm)
      rw [hML] at hzM
      exact hzM.eq hu
    · have hML := hinj _ hMP L hL (hlabM.trans hlab.symm)
      rw [hML] at hzM
      exact hzM.eq hu
    · exact (htwin α h L hL _ hMP hlab hlabM u _ hu hzM).symm
  calc u * u' = u' * u * u'⁻¹ * u' := by rw [key]
    _ = u' * u := by group

@[expose] def zSpan (P : Set (Subgroup G)) : Subgroup ↥(pSpan P) :=
  Subgroup.closure {x | ∃ L ∈ P, IsUniqueInvolution L (x : G)}

omit [Finite G] in
theorem zSpan_normal (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) : (zSpan P).Normal := by
  refine ⟨fun a ha x => ?_⟩
  induction ha using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨L, hL, hgL⟩ := hg
    refine Subgroup.subset_closure ⟨conjSub (x : G) L, hconj L hL x x.2, ?_⟩
    exact hgL.conj (x : G)
  | one => simp
  | mul a b _ _ iha ihb =>
    have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ iha ihb
  | inv a _ ih =>
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ih

omit [Finite G] in
theorem zSpan_elem
    (hcomm : ∀ L ∈ P, ∀ L' ∈ P, ∀ u u' : G, IsUniqueInvolution L u →
      IsUniqueInvolution L' u' → u * u' = u' * u) :
    ∀ a ∈ zSpan P, ∀ b ∈ zSpan P, a * b = b * a ∧ a * a = 1 := by
  set S : Set ↥(pSpan P) := {x | ∃ L ∈ P, IsUniqueInvolution L (x : G)} with hS
  have hgen : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a ⟨L, hL, ha⟩ b ⟨L', hL', hb⟩
    exact Subtype.ext (hcomm L hL L' hL' _ _ ha hb)
  have h1 : ∀ a ∈ S, ∀ b ∈ zSpan P, a * b = b * a := by
    intro a ha b hb
    induction hb using Subgroup.closure_induction with
    | mem g hg => exact hgen a ha g hg
    | one => rw [mul_one, one_mul]
    | mul x y _ _ ihx ihy =>
      rw [← mul_assoc, ihx, mul_assoc, ihy, mul_assoc]
    | inv x _ ih =>
      calc a * x⁻¹ = x⁻¹ * (x * a) * x⁻¹ := by group
        _ = x⁻¹ * (a * x) * x⁻¹ := by rw [ih]
        _ = x⁻¹ * a := by group
  have h2 : ∀ a ∈ zSpan P, ∀ b ∈ zSpan P, a * b = b * a := by
    intro a ha b hb
    induction ha using Subgroup.closure_induction with
    | mem g hg => exact h1 g hg b hb
    | one => rw [mul_one, one_mul]
    | mul x y _ _ ihx ihy =>
      rw [mul_assoc, ihy, ← mul_assoc, ihx, mul_assoc]
    | inv x _ ih =>
      calc x⁻¹ * b = x⁻¹ * (b * x) * x⁻¹ := by group
        _ = x⁻¹ * (x * b) * x⁻¹ := by rw [ih]
        _ = b * x⁻¹ := by group
  have h3 : ∀ a ∈ zSpan P, a * a = 1 := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨L, -, hgL⟩ := hg
      exact Subtype.ext hgL.sq
    | one => rw [mul_one]
    | mul x y hx hy ihx ihy =>
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [h2 y hy x hx]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy, mul_one]
    | inv x _ ih =>
      rw [← mul_inv_rev, ih, inv_one]
  exact fun a ha b hb => ⟨h2 a ha b hb, h3 a ha⟩

end CFSG.ClassicalInvolution.Q3.TL4.AECov
