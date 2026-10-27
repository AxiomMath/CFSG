module

public import CFSG.ClassicalInvolution.Q3.TL3T49
public import CFSG.ClassicalInvolution.Q3.TL3T37
public import CFSG.ClassicalInvolution.Q3.TL3T44

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr

variable {k n : ℕ}

theorem embW_ofPerm (c : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin k)) :
    embW c (ofPerm σ) = ofPerm (embWPerm c σ) := by
  classical
  refine Wr.ext (funext fun x => ?_) rfl
  show embWVec c (0 : Fin k → ZMod 2) x = 0
  unfold embWVec
  split <;> rfl

theorem embWPerm_eq_extPerm (c : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin k)) :
    embWPerm c σ = TC.Thin.Amalg.extPerm c σ := by
  refine Equiv.ext fun x => ?_
  by_cases hx : x ∈ Set.range c
  · obtain ⟨i, rfl⟩ := hx
    rw [embWPerm_apply, TC.Thin.Amalg.extPerm_apply_mem]
  · rw [embWPerm_of_not_mem c σ hx, TC.Thin.Amalg.extPerm_apply_not_mem c σ hx]

theorem subQ_ofPerm (c : Fin k ↪ Fin n) (σ : Equiv.Perm (Fin k)) :
    subQ c (ofPerm σ) = mkQ n (ofPerm (TC.Thin.Amalg.extPerm c σ)) := by
  rw [subQ_apply, embW_ofPerm, embWPerm_eq_extPerm]

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal Amalg

variable {G : Type} [Group G] [Finite G] {P Q : Set (Subgroup G)} {n k : ℕ}

theorem exists_lift_pow_three {H W : Type*} [Group H] [Group W] (ψ : H →* W)
    (hk : IsPGroup 2 ψ.ker) (x : H) (hx : ψ x ^ 3 = 1) : ∃ t : H, ψ t = ψ x ∧ t ^ 3 = 1 := by
  have h3 : x ^ 3 ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hx]
  obtain ⟨a, ha⟩ := hk ⟨x ^ 3, h3⟩
  have ha' : x ^ (3 * 2 ^ a) = 1 := by
    have := congrArg Subtype.val ha
    rw [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [pow_mul]
    exact this
  have h4 : 4 ^ a % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  refine ⟨x ^ (4 ^ a), ?_, ?_⟩
  · rw [map_pow, ← Nat.div_add_mod (4 ^ a) 3, h4, pow_add, pow_mul, hx, one_pow, one_mul, pow_one]
  · rw [← pow_mul, show 4 ^ a * 3 = (3 * 2 ^ a) * 2 ^ a by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring, pow_mul, ha', one_pow]

omit [Finite G] in
theorem SubHyp.isPGroup_ker_pre {I : AEIdent P n} {c : Fin k ↪ Fin n} (h : SubHyp I Q c)
    (hk2 : IsPGroup 2 I.φ.ker) : IsPGroup 2 h.pre.ker := by
  have hle : h.pre.ker ≤ I.φ.ker.comap (Subgroup.inclusion h.span_le) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    have := h.subQ_pre x
    rw [hx, map_one, θ_apply] at this
    exact this.symm
  exact (hk2.comap_of_injective _ (Subgroup.inclusion_injective h.span_le)).to_le hle

theorem SubHyp.exists_lift {I : AEIdent P n} {c : Fin k ↪ Fin n} (h : SubHyp I Q c)
    (hk : 5 ≤ k) (hk2 : IsPGroup 2 I.φ.ker) {σ : Equiv.Perm (Fin k)}
    (hσ : σ ∈ alternatingGroup (Fin k)) (h3 : σ ^ 3 = 1) :
    ∃ t : ↥(pSpan Q), h.pre t = ofPerm σ ∧ t ^ 3 = 1 := by
  have hr : mkQ k (ofPerm σ) ∈ ((I.restrict hk h).φ).range := by
    rw [(I.restrict hk h).range_eq]
    exact mem_aeModel_ofPerm hσ
  obtain ⟨x, hx⟩ := hr
  rw [AEIdent.restrict_apply] at hx
  have hσ4 : σ ^ 4 = σ := by rw [pow_succ, h3, one_mul]
  have hx4 : h.pre (x ^ 4) = ofPerm σ := by
    rcases mkQ_eq_iff.mp hx with h1 | h1
    · rw [map_pow, show h.pre x = ofPerm σ from (inv_mul_eq_one.mp h1), ofPerm_pow, hσ4]
    · have e : h.pre x = ofPerm σ * allOnes k := by
        have : ofPerm σ = h.pre x * allOnes k := by rw [← h1]; group
        rw [this, mul_assoc, allOnes_mul_self, mul_one]
      have hc : Commute (ofPerm σ) (allOnes k) := (allOnes_comm _).symm
      have ha4 : allOnes k ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, sq, allOnes_mul_self, one_mul]
      rw [map_pow, e, hc.mul_pow, ofPerm_pow, hσ4, ha4, mul_one]
  obtain ⟨t, ht, ht3⟩ := exists_lift_pow_three h.pre (h.isPGroup_ker_pre hk2) (x ^ 4)
    (by rw [hx4, ofPerm_pow, h3, ofPerm_one])
  exact ⟨t, ht.trans hx4, ht3⟩

theorem AEIdent.section_mem_restrict (I : AEIdent P n) (hk : 5 ≤ k) (hk2 : IsPGroup 2 I.φ.ker)
    {c : Fin k ↪ Fin n} (h : SubHyp I Q c) {s : alternatingGroup (Fin n) →* ↥(pSpan P)}
    (hs : ∀ σ, I.φ (s σ) = mkQ n (ofPerm (σ : Equiv.Perm (Fin n))))
    (σ : alternatingGroup (Fin k)) : ((s (altExt c σ) : ↥(pSpan P)) : G) ∈ pSpan Q := by
  set S : Subgroup (alternatingGroup (Fin k)) :=
    ((pSpan Q).subgroupOf (pSpan P)).comap (s.comp (altExt c)) with hS
  have hall : S = ⊤ := by
    rw [eq_top_iff, ← closure_range_carmichaelCycle (by omega : 3 ≤ k), Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    have hj3 : carmichaelPerm j ^ 3 = 1 := congrArg Subtype.val (carmichaelCycle_pow_three j)
    obtain ⟨t, ht, ht3⟩ := h.exists_lift hk hk2 (carmichaelPerm_mem j) hj3
    have he : I.φ ⟨(t : G), h.span_le t.2⟩ = I.φ (s (altExt c (carmichaelCycle j))) := by
      rw [← AEIdent.subQ_pre h t, ht, subQ_ofPerm, hs, altExt_coe]
      rfl
    have h1 : (⟨(t : G), h.span_le t.2⟩ : ↥(pSpan P)) ^ 3 ^ 1 = 1 := by
      rw [pow_one]
      exact Subtype.ext (by
        have := congrArg Subtype.val ht3
        rw [Subgroup.coe_pow, Subgroup.coe_one] at this
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact this)
    have h2 : s (altExt c (carmichaelCycle j)) ^ 3 ^ 1 = 1 := by
      rw [pow_one, ← map_pow, ← map_pow, carmichaelCycle_pow_three, map_one, map_one]
    have heq := I.eq_of_map_eq_of_pow hk2 h1 h2 he
    show (s.comp (altExt c)) (carmichaelCycle j) ∈ (pSpan Q).subgroupOf (pSpan P)
    rw [MonoidHom.comp_apply, ← heq, Subgroup.mem_subgroupOf]
    exact t.2
  have hσ : σ ∈ S := by rw [hall]; exact Subgroup.mem_top σ
  exact Subgroup.mem_subgroupOf.mp hσ

omit [Finite G] in
theorem AEIdent.pre_section (I : AEIdent P n) {c : Fin k ↪ Fin n} (h : SubHyp I Q c)
    {s : alternatingGroup (Fin n) →* ↥(pSpan P)}
    (hs : ∀ σ, I.φ (s σ) = mkQ n (ofPerm (σ : Equiv.Perm (Fin n))))
    (σ : alternatingGroup (Fin k)) (hq : ((s (altExt c σ) : ↥(pSpan P)) : G) ∈ pSpan Q) :
    h.pre ⟨_, hq⟩ = ofPerm (σ : Equiv.Perm (Fin k)) := by
  apply subQ_injective c h.miss
  rw [AEIdent.subQ_pre h, subQ_ofPerm, ← altExt_coe, ← hs]

omit [Finite G] in
theorem AEIdent.conjSub_eq_of_map_comm (I : AEIdent P n)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    {L : Subgroup G} (hL : L ∈ P) (g : ↥(pSpan P))
    (hg : ∀ y ∈ (L.subgroupOf (pSpan P)).map I.φ, I.φ g * y = y * I.φ g) :
    conjSub (g : G) L = L := by
  refine hinj _ (hconj L hL g g.2) L hL ?_
  rw [TL4.AECov.map_conjSub_eq I L g]
  exact conjSub_eq_of_comm hg

theorem AEIdent.comm_member (I : AEIdent P n) (hn : 5 ≤ n) (h8 : ∀ L ∈ P, Nat.card ↥L = 8)
    (hconj : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P)
    (hinj : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    {L : Subgroup G} (hL : L ∈ P) (g : ↥(pSpan P))
    (hg : ∀ y ∈ (L.subgroupOf (pSpan P)).map I.φ, I.φ g * y = y * I.φ g) :
    ∀ l ∈ L, (g : G) * l = l * g := by
  have hnorm := I.conjSub_eq_of_map_comm hconj hinj hL g hg
  intro l hl
  obtain ⟨α, hα, b, hlab⟩ := I.label L hL
  have hxl : (g : G) * l * (g : G)⁻¹ ∈ L := by
    rw [← hnorm]
    exact conj_mem_conjSub hl
  have hcm : (g : G) * l * (g : G)⁻¹ * l⁻¹ ∈ L := L.mul_mem hxl (L.inv_mem hl)
  have hlP : l ∈ pSpan P := le_pSpan hL hl
  have he : I.φ ⟨(g : G) * l * (g : G)⁻¹ * l⁻¹, le_pSpan hL hcm⟩ =
      I.φ ⟨1, le_pSpan hL L.one_mem⟩ := by
    have e1 : (⟨(g : G) * l * (g : G)⁻¹ * l⁻¹, le_pSpan hL hcm⟩ : ↥(pSpan P)) =
        g * ⟨l, hlP⟩ * g⁻¹ * ⟨l, hlP⟩⁻¹ := rfl
    have e2 : (⟨1, le_pSpan hL L.one_mem⟩ : ↥(pSpan P)) = 1 := rfl
    rw [e1, e2, map_one, map_mul, map_mul, map_mul, map_inv, map_inv,
      hg _ (I.mem_map hL hl)]
    group
  have h1 := phi_injOn I.φ hn hL (h8 L hL) hlab hcm L.one_mem he
  calc (g : G) * l = ((g : G) * l * (g : G)⁻¹ * l⁻¹) * l * g := by group
    _ = l * g := by rw [h1, one_mul]

end CFSG.ClassicalInvolution.Q3.TC.Thin
