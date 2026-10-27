module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Escape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingLemma34Shapes

public section

namespace CFSG.ComponentClassification.AschbacherStrongEmbedding

namespace Lemma34

open CFSG.Open CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

structure EscapeChoice (A₁ A₂ : Subgroup G) (a t g : G) : Prop where
  not_mem : g ∉ overlapClosure A₁ A₂
  conj_eq : g⁻¹ * a * g = t
  centralizer_le : Subgroup.centralizer ({t} : Set G) ≤ rightConjugate (overlapClosure A₁ A₂) g

@[expose] def EscapeRechoice (S : Sylow 2 G) (A₁ A₂ : Subgroup G) (a t : G) : Prop :=
  ∀ V : Subgroup G, IsPGroup 2 V → V ≤ Subgroup.centralizer ({t} : Set G) →
    ∃ g : G, EscapeChoice A₁ A₂ a t g ∧ V ≤ rightConjugate (S : Subgroup G) g

theorem exists_conj_le_of_sylow_subgroupOf {K T₀ V : Subgroup G} (P : Sylow 2 K)
    (hP : (P : Subgroup K) = T₀.subgroupOf K) (hVK : V ≤ K) (hV : IsPGroup 2 V) :
    ∃ c ∈ K, ∀ x ∈ V, c⁻¹ * x * c ∈ T₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV' : IsPGroup 2 (V.subgroupOf K) :=
    hV.comap_of_injective K.subtype K.subtype_injective
  obtain ⟨Q, hQ⟩ := hV'.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq K P Q
  refine ⟨(c : G), c.property, fun x hx => ?_⟩
  have hxQ : (⟨x, hVK hx⟩ : K) ∈ (Q : Subgroup K) := hQ hx
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hP] at hxQ
  change ((MulAut.conj c)⁻¹ • (⟨x, hVK hx⟩ : K) : K) ∈ T₀.subgroupOf K at hxQ
  rw [Subgroup.mem_subgroupOf] at hxQ
  simpa only [MulAut.smul_def, MulAut.conj_inv_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    using hxQ

theorem EscapeChoice.rechoice {a t g : G} (hc : EscapeChoice A₁ A₂ a t g)
    (hP : ∃ P : Sylow 2 (Subgroup.centralizer ({t} : Set G)),
      (P : Subgroup _) = (rightConjugate (S : Subgroup G) g).subgroupOf
        (Subgroup.centralizer ({t} : Set G))) :
    EscapeRechoice S A₁ A₂ a t := by
  obtain ⟨P, hP⟩ := hP
  intro V hV hVC
  obtain ⟨c, hcC, hcV⟩ := exists_conj_le_of_sylow_subgroupOf P hP hVC hV
  set H := overlapClosure A₁ A₂ with hHdef
  have hcH : g * c * g⁻¹ ∈ H := (mem_rightConjugate_iff _ _ _).mp (hc.centralizer_le hcC)
  refine ⟨g * c⁻¹, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro hmem
    apply hc.not_mem
    have := H.mul_mem hcH hmem
    rwa [show g * c * g⁻¹ * (g * c⁻¹) = g by group] at this
  · have hct : c * t = t * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
    rw [show (g * c⁻¹)⁻¹ * a * (g * c⁻¹) = c * (g⁻¹ * a * g) * c⁻¹ by group, hc.conj_eq, hct,
      mul_inv_cancel_right]
  · intro x hx
    rw [mem_rightConjugate_iff]
    have hxH : g * x * g⁻¹ ∈ H := (mem_rightConjugate_iff _ _ _).mp (hc.centralizer_le hx)
    have := H.mul_mem (H.mul_mem (H.inv_mem hcH) hxH) hcH
    rwa [show (g * c * g⁻¹)⁻¹ * (g * x * g⁻¹) * (g * c * g⁻¹) = g * c⁻¹ * x * (g * c⁻¹)⁻¹ by
      group] at this
  · intro x hx
    rw [mem_rightConjugate_iff]
    have := (mem_rightConjugate_iff _ _ _).mp (hcV x hx)
    rwa [show g * (c⁻¹ * x * c) * g⁻¹ = g * c⁻¹ * x * (g * c⁻¹)⁻¹ by group] at this

omit [Finite G] in
theorem inv_not_mem_rightConjugate {H : Subgroup G} {g : G} (hg : g ∉ H) :
    g⁻¹ ∉ rightConjugate H g := by
  rw [mem_rightConjugate_iff, mul_inv_cancel, one_mul]
  exact fun h => hg (H.inv_mem_iff.mp h)

theorem Hyp.escape_swap (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁) {a t g : G}
    (hc : EscapeChoice A₁ A₂ a t g) (ha : a ∈ A₁) (ha1 : a ≠ 1)
    (htS : t ∈ (S : Subgroup G)) :
    rightConjugate A₁ t = A₂ ∧ rightConjugate A₂ t = A₁ := by
  have h' := h.swap_of_conj h12 h21 (Or.inl ha) ha1 hc.not_mem (hc.conj_eq ▸ htS)
  rwa [hc.conj_eq] at h'

theorem Hyp.choice_swap (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁) {a t g : G}
    (hc : EscapeChoice A₁ A₂ a t g) {y : G} (hy : y ∈ (A₁ : Set G) ∪ A₂) (hy1 : y ≠ 1)
    (hyT : y ∈ rightConjugate (S : Subgroup G) g) :
    rightConjugate (rightConjugate A₁ g) y = rightConjugate A₂ g ∧
      rightConjugate (rightConjugate A₂ g) y = rightConjugate A₁ g := by
  have hB := h.conj g
  have hB12 : ¬ rightConjugate A₁ g ≤ rightConjugate A₂ g := by
    rwa [rightConjugate_le_rightConjugate_iff]
  have hB21 : ¬ rightConjugate A₂ g ≤ rightConjugate A₁ g := by
    rwa [rightConjugate_le_rightConjugate_iff]
  have hbU : g⁻¹ * y * g ∈ (rightConjugate A₁ g : Set G) ∪ rightConjugate A₂ g := by
    rcases hy with hy | hy
    · exact Or.inl (mem_rightConjugate_conj hy)
    · exact Or.inr (mem_rightConjugate_conj hy)
  have hb1 : g⁻¹ * y * g ≠ 1 := by
    intro h1
    apply hy1
    calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hg : g⁻¹ ∉ overlapClosure (rightConjugate A₁ g) (rightConjugate A₂ g) := by
    rw [overlapClosure_conj]
    exact inv_not_mem_rightConjugate hc.not_mem
  have heq : (g⁻¹)⁻¹ * (g⁻¹ * y * g) * g⁻¹ = y := by group
  have hS : (g⁻¹)⁻¹ * (g⁻¹ * y * g) * g⁻¹ ∈ (conjSylow S g : Subgroup G) := by
    rw [heq, coe_conjSylow]
    exact hyT
  have := hB.swap_of_conj hB12 hB21 hbU hb1 hg hS
  rwa [heq] at this

theorem Hyp.choice_not_le (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁) {a t g : G}
    (hc : EscapeChoice A₁ A₂ a t g) {X : Subgroup G} (hXU : (X : Set G) ⊆ (A₁ : Set G) ∪ A₂)
    (hX4 : 4 ≤ Nat.card X) (hXH : X ≤ rightConjugate (overlapClosure A₁ A₂) g) : False := by
  have hX := h.fixesOnly_of_card h12 h21 hXU hX4
  apply hc.not_mem
  have hginv : g⁻¹ ∈ overlapClosure A₁ A₂ := by
    refine hX g⁻¹ fun x hx => ?_
    rw [inv_inv]
    exact (mem_rightConjugate_iff _ _ _).mp (hXH hx)
  exact (overlapClosure A₁ A₂).inv_mem_iff.mp hginv

theorem Hyp.choice_not_le_conj (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁)
    {a t g : G} (hc : EscapeChoice A₁ A₂ a t g) {X : Subgroup G}
    (hXU : (X : Set G) ⊆ (rightConjugate A₁ g : Set G) ∪ rightConjugate A₂ g)
    (hX4 : 4 ≤ Nat.card X) (hXH : X ≤ overlapClosure A₁ A₂) : False := by
  have hB := h.conj g
  have hB12 : ¬ rightConjugate A₁ g ≤ rightConjugate A₂ g := by
    rwa [rightConjugate_le_rightConjugate_iff]
  have hB21 : ¬ rightConjugate A₂ g ≤ rightConjugate A₁ g := by
    rwa [rightConjugate_le_rightConjugate_iff]
  have hX := hB.fixesOnly_of_card hB12 hB21 hXU hX4
  rw [overlapClosure_conj] at hX
  apply hc.not_mem
  have hgH : g ∈ rightConjugate (overlapClosure A₁ A₂) g := by
    refine hX g fun x hx => ?_
    rw [mem_rightConjugate_iff]
    simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hXH hx
  rw [mem_rightConjugate_iff, mul_inv_cancel_right] at hgH
  exact hgH

theorem Hyp.choice_mem_of_conj (h : Hyp S A₁ A₂) {a t g : G} (hc : EscapeChoice A₁ A₂ a t g)
    (ha : a ∈ A₁) (ht1 : t ≠ 1) {k : G}
    (hkT : k⁻¹ * t * k ∈ rightConjugate (S : Subgroup G) g)
    (hkN : k⁻¹ * t * k ∈ Subgroup.normalizer (rightConjugate A₁ g : Set G) ∨
      k⁻¹ * t * k ∈ Subgroup.normalizer (rightConjugate A₂ g : Set G)) :
    k ∈ rightConjugate (overlapClosure A₁ A₂) g := by
  have hB := h.conj g
  have htB : t ∈ (rightConjugate A₁ g : Set G) ∪ rightConjugate A₂ g :=
    Or.inl (hc.conj_eq ▸ mem_rightConjugate_conj ha)
  have hkT' : k⁻¹ * t * k ∈ (conjSylow S g : Subgroup G) := by rw [coe_conjSylow]; exact hkT
  have := mem_overlapClosure_of_union htB ht1 (hB.conj_mem_of_mem_normalizer htB hkT' hkN)
  rwa [overlapClosure_conj] at this

omit [Finite G] in
theorem rightConjugate_mul_self_of_mem_pairStabilizer {B₁ B₂ : Subgroup G} {y : G}
    (hy : y ∈ pairStabilizer B₁ B₂) : rightConjugate B₁ (y * y) = B₁ := by
  rw [← rightConjugate_mul]
  rcases hy with ⟨h₁, -⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₁]
  · rw [h₁, h₂]

omit [Finite G] in
theorem rightConjugate_inf_eq (A B : Subgroup G) (g : G) :
    rightConjugate (A ⊓ B) g = rightConjugate A g ⊓ rightConjugate B g :=
  Subgroup.map_inf A B _ (MulAut.conj g⁻¹).injective

theorem three_le_card_of_mem {P : Subgroup G} {x y : G} (hx : x ∈ P) (hy : y ∈ P)
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) : 3 ≤ Nat.card P := by
  have hsub : ({1, x, y} : Set G) ⊆ (P : Set G) := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact P.one_mem
    · exact hx
    · exact hy
  have h3 : ({1, x, y} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [Ne.symm hx1, Ne.symm hy1]),
      Set.ncard_pair hxy]
  calc 3 = ({1, x, y} : Set G).ncard := h3.symm
    _ ≤ (P : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card P := (Nat.card_coe_set_eq _).symm

theorem Hyp.escape_center (h : Hyp S A₁ A₂) (h12 : ¬ A₁ ≤ A₂) (h21 : ¬ A₂ ≤ A₁) {a t g : G}
    (hc : EscapeChoice A₁ A₂ a t g) (ha : a ∈ A₁) (ha1 : a ≠ 1)
    (htS : t ∈ (S : Subgroup G)) (hI : A₁ ⊓ A₂ ≠ ⊥) :
    ∃ z ∈ A₁ ⊓ A₂, z ≠ 1 ∧ z * z = 1 ∧ Commute t z ∧
      ∀ p ∈ A₁ ⊓ A₂, Commute t p → p = 1 ∨ p = z := by
  obtain ⟨hs₁, hs₂⟩ := h.escape_swap h12 h21 hc ha ha1 htS
  have hIS : A₁ ⊓ A₂ ≤ (S : Subgroup G) := inf_le_left.trans h.le_one
  have hnorm : t ∈ Subgroup.normalizer ((A₁ ⊓ A₂ : Subgroup G) : Set G) := by
    rw [← rightConjugate_eq_self_iff, rightConjugate_inf_eq, hs₁, hs₂, inf_comm]
  obtain ⟨z, hzI, hz1, hzt⟩ := exists_commute_of_mem_normalizer S.isPGroup' hIS hI htS hnorm
  set P := A₁ ⊓ A₂ ⊓ Subgroup.centralizer ({t} : Set G) with hPdef
  have hmemP : ∀ {p : G}, p ∈ A₁ ⊓ A₂ → Commute t p → p ∈ P := by
    intro p hp hpt
    exact ⟨hp, Subgroup.mem_centralizer_singleton_iff.mpr hpt.eq.symm⟩
  have hP2 : Nat.card P ≤ 2 := by
    refine card_le_two_of_lt_four (S.isPGroup'.to_le (inf_le_left.trans hIS)) ?_
    by_contra hcon
    refine h.choice_not_le h12 h21 hc (X := P) (fun x hx => ?_) (not_lt.mp hcon)
      (fun x hx => hc.centralizer_le (Subgroup.mem_inf.mp hx).2)
    exact Or.inl (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
  have hfix : ∀ p ∈ A₁ ⊓ A₂, Commute t p → p = 1 ∨ p = z := by
    intro p hp hpt
    by_contra hcon
    rw [not_or] at hcon
    have := three_le_card_of_mem (hmemP hzI hzt) (hmemP hp hpt) hz1 hcon.1 (Ne.symm hcon.2)
    omega
  have hzz : z * z = 1 := by
    rcases hfix (z * z) ((A₁ ⊓ A₂).mul_mem hzI hzI) (hzt.mul_right hzt) with h1 | h1
    · exact h1
    · exact absurd (mul_left_cancel (h1.trans (mul_one z).symm)) hz1
  exact ⟨z, hzI, hz1, hzz, hzt, hfix⟩

end Lemma34

end CFSG.ComponentClassification.AschbacherStrongEmbedding
