module

public import CFSG.GH74.E2.BoxStd
public import CFSG.GH74.E2.LocalLeaves

public section

namespace CFSG.GH74.E2.Box

open Subgroup CFSG.GH74.GLS

variable {G : Type} [Group G]

@[expose] def ConjOf (K M : Subgroup G) : Prop := ∃ g : G, M = conjugate K g

theorem ConjOf.refl (K : Subgroup G) : ConjOf K K := ⟨1, (conj_one K).symm⟩

theorem ConjOf.trans {K M N : Subgroup G} (h1 : ConjOf K M) (h2 : ConjOf M N) : ConjOf K N := by
  obtain ⟨g, rfl⟩ := h1
  obtain ⟨h, rfl⟩ := h2
  exact ⟨g * h, (Box.conj_mul K g h).symm⟩

theorem ConjOf.conj {K M : Subgroup G} (h : ConjOf K M) (g : G) : ConjOf K (conjugate M g) :=
  h.trans ⟨g, rfl⟩

structure CommPair (K A B : Subgroup G) : Prop where
  convA : ConjOf K A
  convB : ConjOf K B
  compB : IsCompIn (centralizer (A : Set G)) B
  compA : IsCompIn (centralizer (B : Set G)) A

theorem CommPair.symm {K A B : Subgroup G} (h : CommPair K A B) : CommPair K B A :=
  ⟨h.convB, h.convA, h.compA, h.compB⟩

theorem CommPair.conj {K A B : Subgroup G} (h : CommPair K A B) (g : G) :
    CommPair K (conjugate A g) (conjugate B g) := by
  refine ⟨h.convA.conj g, h.convB.conj g, ?_, ?_⟩
  · have := AS16.isCompIn_conj h.compB g
    rwa [AS16.conjugate_centralizer] at this
  · have := AS16.isCompIn_conj h.compA g
    rwa [AS16.conjugate_centralizer] at this

theorem CommPair.commute {K A B : Subgroup G} (h : CommPair K A B) :
    ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx _ hy =>
  mem_centralizer_iff.1 (h.compB.1 hy) x hx

theorem exists_ne_one_of_quasisimple {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    ∃ x : Q, x ≠ 1 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, b, hab⟩ := h.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [hcon a', hcon b']

theorem swapGrp_le_normalizer (A B : Subgroup G) :
    swapGrp A B ≤ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro g hg
  rw [← AS16.conjugate_eq_self_iff]
  have : conjugate (A ⊔ B) g = conjugate A g ⊔ conjugate B g := Subgroup.map_sup _ _ _
  rw [this]
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]

section Fin

variable [Finite G]

structure Setup (K : Subgroup G) : Prop where
  hyp : Hyp G
  d0 : K0Data
  d3 : K0Data3
  comp : ComponentList
  m11 : M11Tables
  shape : ShapeLM ↥K
  term : TermComp K
  quasi : CFSG.IsQuasisimple ↥K

theorem Setup.shape_of {K M : Subgroup G} (S : Setup K) (h : ConjOf K M) : ShapeLM ↥M := by
  obtain ⟨g, rfl⟩ := h
  exact shapeLM_conj S.shape g

theorem Setup.term_of {K M : Subgroup G} (S : Setup K) (h : ConjOf K M) : TermComp M := by
  obtain ⟨g, rfl⟩ := h
  exact S.term.conj g

theorem Setup.quasi_of {K M : Subgroup G} (S : Setup K) (h : ConjOf K M) :
    CFSG.IsQuasisimple ↥M := by
  obtain ⟨g, rfl⟩ := h
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupMap (MulAut.conj g⁻¹) K)
    S.quasi

theorem Setup.centerFree_of {K M : Subgroup G} (S : Setup K) (h : ConjOf K M) :
    ∀ x ∈ M, (∀ y ∈ M, x * y = y * x) → x = 1 :=
  (lmData S.d0 S.d3 (S.shape_of h)).1

theorem Setup.rank_of {K M : Subgroup G} (S : Setup K) (h : ConjOf K M) :
    ∃ A : Subgroup G, A ≤ M ∧ IsPGroup 2 ↥A ∧ 2 ≤ Group.rank ↥A :=
  (lmData S.d0 S.d3 (S.shape_of h)).2

theorem Setup.unique {K L M1 M2 : Subgroup G} (S : Setup K) (hL : ConjOf K L)
    (h1 : ConjOf K M1) (h2 : ConjOf K M2) (c1 : IsCompIn (centralizer (L : Set G)) M1)
    (c2 : IsCompIn (centralizer (L : Set G)) M2) : M1 = M2 := by
  obtain ⟨gL, rfl⟩ := hL
  obtain ⟨g1, rfl⟩ := h1
  obtain ⟨g2, rfl⟩ := h2
  have hsh : ShapeLM ↥(conjugate K gL) := shapeLM_conj S.shape gL
  have e : ∀ g : G, conjugate K g = conjugate (conjugate K gL) (gL⁻¹ * g) := fun g => by
    rw [← Box.conj_mul, mul_inv_cancel_left]
  exact conj_comp_eq S.hyp S.d0 S.d3 hsh c1 c2 (g1 := gL⁻¹ * g1) (g2 := gL⁻¹ * g2) (e g1) (e g2)

theorem Setup.invol_unique {K L1 L2 : Subgroup G} (S : Setup K) {y : G} (hy : orderOf y = 2)
    (h1 : ConjOf K L1) (h2 : ConjOf K L2) (c1 : y ∈ centralizer (L1 : Set G))
    (c2 : y ∈ centralizer (L2 : Set G)) : L1 = L2 := by
  have k1 : IsCompCen y L1 := S.term_of h1 y c1 hy
  have k2 : IsCompCen y L2 := S.term_of h2 y c2 hy
  exact ((S.comp G S.hyp y hy L1 k1).2 L2 k2).symm

theorem CommPair.ne {K A B : Subgroup G} (S : Setup K) (h : CommPair K A B) : A ≠ B := by
  intro heq
  obtain ⟨zA, P, hPA, -, hrP⟩ := lmData S.d0 S.d3 (S.shape_of h.convA)
  have hAbot : A = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    refine zA x hx fun y hy => ?_
    exact (h.commute y hy x (heq ▸ hx)).symm
  have hPbot : P = ⊥ := le_bot_iff.1 (hAbot ▸ hPA)
  have : Group.rank ↥P = 0 := by
    rw [Subgroup.rank_congr hPbot]
    exact Group.rank_eq_zero _
  omega

theorem CommPair.uniqB {K A B M : Subgroup G} (S : Setup K) (h : CommPair K A B)
    (hM : ConjOf K M) (c : IsCompIn (centralizer (A : Set G)) M) : M = B :=
  S.unique h.convA hM h.convB c h.compB

theorem CommPair.fix {K A B : Subgroup G} (S : Setup K) (h : CommPair K A B) {g : G}
    (hg : conjugate A g = A) : conjugate B g = B := by
  refine h.uniqB S (h.convB.conj g) ?_
  have := AS16.isCompIn_conj h.compB g
  rwa [AS16.conjugate_centralizer, hg] at this

theorem CommPair.swap {K A B : Subgroup G} (S : Setup K) (h : CommPair K A B) {g : G}
    (hg : conjugate A g = B) : conjugate B g = A := by
  have h1 : IsCompIn (centralizer (B : Set G)) (conjugate B g) := by
    have := AS16.isCompIn_conj h.compB g
    rwa [AS16.conjugate_centralizer, hg] at this
  exact S.unique h.convB (h.convB.conj g) h.convA h1 h.compA

theorem CommPair.mem_swapGrp {K A B : Subgroup G} (S : Setup K) (h : CommPair K A B) {g : G}
    (hg : conjugate A g = A ∨ conjugate A g = B) : g ∈ swapGrp A B := by
  rcases hg with hg | hg
  · exact Or.inl ⟨hg, h.fix S hg⟩
  · exact Or.inr ⟨hg, h.swap S hg⟩

variable {K A B : Subgroup G}

theorem CommPair.centerFree_D (S : Setup K) (h : CommPair K A B) :
    ∀ x ∈ A ⊔ B, (∀ y ∈ A ⊔ B, x * y = y * x) → x = 1 := by
  intro x hx hc
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute h.commute hx
  have ha1 : a = 1 := by
    refine S.centerFree_of h.convA a ha fun y hy => ?_
    have hx := hc y (Subgroup.mem_sup_left hy)
    have hby := h.commute y hy b hb
    have h5 : (a * y) * b = (y * a) * b := by
      calc (a * y) * b = a * (y * b) := by group
        _ = a * (b * y) := by rw [hby]
        _ = (a * b) * y := by group
        _ = y * (a * b) := hx
        _ = (y * a) * b := by group
    exact mul_right_cancel h5
  have hb1 : b = 1 := by
    refine S.centerFree_of h.convB b hb fun y hy => ?_
    have hx := hc y (Subgroup.mem_sup_right hy)
    have hay := h.commute a ha y hy
    have h5 : a * (b * y) = a * (y * b) := by
      calc a * (b * y) = (a * b) * y := by group
        _ = y * (a * b) := hx
        _ = (y * a) * b := by group
        _ = (a * y) * b := by rw [← hay]
        _ = a * (y * b) := by group
    exact mul_left_cancel h5
  rw [ha1, hb1, mul_one]

omit [Finite G] in
theorem CommPair.normal_subgroupOf (h : CommPair K A B) :
    (A.subgroupOf (A ⊔ B)).Normal := by
  refine ⟨fun x hx d => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute h.commute d.2
  have hbx := h.commute x hx b hb
  have : ((d * x * d⁻¹ : ↥(A ⊔ B)) : G) = a * (x : G) * a⁻¹ := by
    show (d : G) * x * (d : G)⁻¹ = _
    rw [hab, mul_inv_rev]
    calc a * b * (x : G) * (b⁻¹ * a⁻¹) = a * (b * x) * b⁻¹ * a⁻¹ := by group
      _ = a * (x * b) * b⁻¹ * a⁻¹ := by rw [← hbx]
      _ = a * x * a⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hx) (Subgroup.inv_mem _ ha)

theorem CommPair.isCompIn_left (S : Setup K) (h : CommPair K A B) : IsCompIn (A ⊔ B) A := by
  have hAD : A ≤ A ⊔ B := le_sup_left
  refine ⟨hAD, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAD).symm
      (S.quasi_of h.convA)
  · have := h.normal_subgroupOf
    exact Subgroup.Normal.isSubnormal ‹_›

theorem CommPair.isCompIn_right (S : Setup K) (h : CommPair K A B) : IsCompIn (A ⊔ B) B := by
  have := h.symm.isCompIn_left S
  rwa [sup_comm] at this

theorem CommPair.comps_of_D (S : Setup K) (h : CommPair K A B) {M : Subgroup G}
    (hM : IsCompIn (A ⊔ B) M) : M = A ∨ M = B := by
  by_contra hne
  push Not at hne
  have hMA : ⁅M, A⁆ = ⊥ := (AS16.isCompIn_commute hM (h.isCompIn_left S)).resolve_left hne.1
  have hMB : ⁅M, B⁆ = ⊥ := (AS16.isCompIn_commute hM (h.isCompIn_right S)).resolve_left hne.2
  have hMA' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hMA
  have hMB' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hMB
  have hq : CFSG.IsQuasisimple ↥M :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hM.1) hM.2.1
  obtain ⟨⟨x, hx⟩, hx1⟩ := exists_ne_one_of_quasisimple hq
  apply hx1
  apply Subtype.ext
  show x = 1
  refine h.centerFree_D S x (hM.1 hx) fun y hy => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute h.commute hy
  have e1 : a * x = x * a := mem_centralizer_iff.1 (hMA' hx) a ha
  have e2 : b * x = x * b := mem_centralizer_iff.1 (hMB' hx) b hb
  calc x * (a * b) = (x * a) * b := by group
    _ = (a * x) * b := by rw [e1]
    _ = a * (x * b) := by group
    _ = a * (b * x) := by rw [e2]
    _ = a * b * x := by group

end Fin

end CFSG.GH74.E2.Box
