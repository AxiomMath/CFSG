module

public import CFSG.LocalAnalysis.ComponentInitial.FactorwiseFixedLayer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open scoped commutatorElement Pointwise

section General

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf_of_commute [Finite G] {A B : Subgroup G}
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  let μ : A × B →* G := MonoidHom.noncommCoprod A.subtype B.subtype fun x y => hAB x x.2 y y.2
  have hμ : ∀ p, μ p = (p.1 : G) * p.2 := fun p => rfl
  have hrange : μ.range = A ⊔ B := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      rw [hμ]
      exact mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)
    · intro g hg
      have hset : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) := by
        refine Subgroup.coe_mul_of_left_le_normalizer_right _ _ ?_
        refine le_trans ?_ (centralizer_le_normalizer _)
        intro x hx
        rw [mem_centralizer_iff]
        intro y hy
        exact (hAB x hx y hy).symm
      have hg' : g ∈ (A : Set G) * (B : Set G) := by rw [← hset]; exact hg
      obtain ⟨x, hx, y, hy, rfl⟩ := hg'
      exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  let e : μ.ker ≃ ↥(A ⊓ B) :=
    { toFun := fun p => ⟨(p : A × B).1, Subgroup.mem_inf.2 ⟨(p : A × B).1.2, by
        have h : ((p : A × B).1 : G) * (p : A × B).2 = 1 := p.2
        rw [eq_inv_of_mul_eq_one_left h]
        exact inv_mem (p : A × B).2.2⟩⟩
      invFun := fun z => ⟨(⟨z, (Subgroup.mem_inf.1 z.2).1⟩, ⟨(z : G)⁻¹,
        inv_mem (Subgroup.mem_inf.1 z.2).2⟩), by
          change (z : G) * (z : G)⁻¹ = 1
          exact mul_inv_cancel _⟩
      left_inv := fun p => by
        have h : ((p : A × B).1 : G) * (p : A × B).2 = 1 := p.2
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact Subtype.ext (eq_inv_of_mul_eq_one_right h).symm
      right_inv := fun z => rfl }
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup μ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange μ).toEquiv, hrange, Nat.card_prod,
    Nat.card_congr e] at h1
  exact h1.symm

end General

section Diagonal

variable {H : Type*} [Group H] [Finite H] {a : H} {L : Subgroup H}

omit [Finite H] in
theorem isComponent_conjSub {N : Subgroup H} (hN : CFSG.IsComponent N) (g : H) :
    CFSG.IsComponent (conjSub g N) :=
  (isComponent_map_iff (MulAut.conj g) N).2 hN

theorem commutator_conjSub_eq_bot (hL : CFSG.IsComponent L) (hLa : conjSub a⁻¹ L ≠ L) :
    ⁅L, conjSub a⁻¹ L⁆ = ⊥ := by
  rcases CFSG.LocalCores.distinct_components_commute hL (isComponent_conjSub hL a⁻¹) with h | h
  · exact absurd h.symm hLa
  · exact h

omit [Finite H] in
theorem assembly_isQuasisimple_of_isComponent {N : Subgroup H} (hN : CFSG.IsComponent N) :
    CFSG.Assembly.IsQuasisimple N :=
  (AssemblyBPredicates.isQuasisimple_iff_native N).2 hN.1

variable (hL : CFSG.IsComponent L) (hLa : conjSub a⁻¹ L ≠ L)

include hL hLa in
theorem not_le_centralizer_diag :
    ¬ L ≤ centralizer ((swapDiag (commutator_conjSub_eq_bot hL hLa)).range : Set H) := by
  set hAB := commutator_conjSub_eq_bot hL hLa
  intro h
  apply not_le_centralizer_self_of_isQuasisimple (assembly_isQuasisimple_of_isComponent hL)
  intro y hy
  rw [mem_centralizer_iff]
  intro x hx
  have h1 := mem_centralizer_iff.1 (h hy) (swapDiag hAB ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
  rw [swapDiag_apply] at h1
  have h2 := commute_of_commutator_conj_eq_bot hAB hy (conj_mem_conjSub (t := a) hx)
  have h3 : x * y * (a⁻¹ * x * a) = y * x * (a⁻¹ * x * a) := by
    calc x * y * (a⁻¹ * x * a) = x * (y * (a⁻¹ * x * a)) := by group
      _ = x * ((a⁻¹ * x * a) * y) := by rw [h2]
      _ = y * (x * (a⁻¹ * x * a)) := by rw [← mul_assoc, h1]
      _ = y * x * (a⁻¹ * x * a) := by group
  exact mul_right_cancel h3

include hL hLa in
theorem not_le_centralizer_diag' :
    ¬ conjSub a⁻¹ L ≤ centralizer ((swapDiag (commutator_conjSub_eq_bot hL hLa)).range : Set H) := by
  set hAB := commutator_conjSub_eq_bot hL hLa
  intro h
  apply not_le_centralizer_self_of_isQuasisimple
    (assembly_isQuasisimple_of_isComponent (isComponent_conjSub hL a⁻¹))
  intro y hy
  rw [mem_centralizer_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hxa : (MulAut.conj a⁻¹).toMonoidHom x = a⁻¹ * x * a := by simp
  rw [hxa]
  have h1 := mem_centralizer_iff.1 (h hy) (swapDiag hAB ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
  rw [swapDiag_apply] at h1
  have h2 := commute_of_commutator_conj_eq_bot hAB hx hy
  have h3 : x * ((a⁻¹ * x * a) * y) = x * (y * (a⁻¹ * x * a)) := by
    calc x * ((a⁻¹ * x * a) * y) = x * (a⁻¹ * x * a) * y := by group
      _ = y * (x * (a⁻¹ * x * a)) := h1
      _ = (y * x) * (a⁻¹ * x * a) := by group
      _ = (x * y) * (a⁻¹ * x * a) := by rw [h2]
      _ = x * (y * (a⁻¹ * x * a)) := by group
  exact mul_left_cancel h3

include hL hLa in
theorem eq_or_eq_of_not_le_centralizer_diag {N : Subgroup H} (hN : CFSG.IsComponent N)
    (hNJ : ¬ N ≤ centralizer ((swapDiag (commutator_conjSub_eq_bot hL hLa)).range : Set H)) :
    N = L ∨ N = conjSub a⁻¹ L := by
  set hAB := commutator_conjSub_eq_bot hL hLa
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  have hc1 := (CFSG.LocalCores.distinct_components_commute hN hL).resolve_left h1
  have hc2 := (CFSG.LocalCores.distinct_components_commute hN
    (isComponent_conjSub hL a⁻¹)).resolve_left h2
  apply hNJ
  intro k hk
  rw [mem_centralizer_iff]
  rintro _ ⟨x, rfl⟩
  rw [swapDiag_apply]
  have e1 := commute_of_commutator_eq_bot hc1 hk x.2
  have e2 := commute_of_commutator_eq_bot hc2 hk (conj_mem_conjSub (t := a) x.2)
  calc (x : H) * (a⁻¹ * x * a) * k = x * ((a⁻¹ * x * a) * k) := by group
    _ = x * (k * (a⁻¹ * x * a)) := by rw [e2]
    _ = (x * k) * (a⁻¹ * x * a) := by group
    _ = (k * x) * (a⁻¹ * x * a) := by rw [e1]
    _ = k * (x * (a⁻¹ * x * a)) := by group

include hL hLa in
theorem conjSub_mem_pair {N : Subgroup H} (hN : N = L ∨ N = conjSub a⁻¹ L) {g : H}
    (hg : g ∈ centralizer ((swapDiag (commutator_conjSub_eq_bot hL hLa)).range : Set H)) :
    conjSub g N = L ∨ conjSub g N = conjSub a⁻¹ L := by
  set J := (swapDiag (commutator_conjSub_eq_bot hL hLa)).range
  have hNc : CFSG.IsComponent N := by
    rcases hN with rfl | rfl
    · exact hL
    · exact isComponent_conjSub hL a⁻¹
  have hNJ : ¬ N ≤ centralizer (J : Set H) := by
    rcases hN with rfl | rfl
    · exact not_le_centralizer_diag hL hLa
    · exact not_le_centralizer_diag' hL hLa
  refine eq_or_eq_of_not_le_centralizer_diag hL hLa (isComponent_conjSub hNc g) fun h => hNJ ?_
  have hJ : conjSub g⁻¹ J = J :=
    conjSub_eq_of_mem_normalizer (centralizer_le_normalizer _ (inv_mem hg))
  have h1 : conjSub g⁻¹ (conjSub g N) ≤ conjSub g⁻¹ (centralizer (J : Set H)) := map_mono h
  rwa [conjSub_inv_conjSub, conjSub_centralizer, hJ] at h1

include hL hLa in
theorem centralizer_diag_inf_normalizer_le :
    centralizer ((swapDiag (commutator_conjSub_eq_bot hL hLa)).range : Set H) ⊓
        normalizer (L : Set H) ≤ centralizer ((L ⊔ conjSub a⁻¹ L : Subgroup H) : Set H) := by
  set hAB := commutator_conjSub_eq_bot hL hLa
  set J := (swapDiag hAB).range
  set X := centralizer (J : Set H) ⊓ normalizer (L : Set H)
  have hfixLa : ∀ g ∈ X, conjSub g (conjSub a⁻¹ L) = conjSub a⁻¹ L := by
    intro g hg
    have hgL : conjSub g L = L := conjSub_eq_of_mem_normalizer hg.2
    rcases conjSub_mem_pair hL hLa (Or.inr rfl) hg.1 with h | h
    · exfalso
      apply hLa
      have := congrArg (conjSub g⁻¹) (h.trans hgL.symm)
      rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
    · exact h
  have hcomm : ∀ x ∈ L, ∀ g ∈ X, ⁅x, g⁆ ∈ L ⊓ conjSub a⁻¹ L := by
    intro x hx g hg
    have hgL : conjSub g L = L := conjSub_eq_of_mem_normalizer hg.2
    have hgLa := hfixLa g hg
    have hx' : x⁻¹ ∈ L := inv_mem hx
    have hgx : g * x⁻¹ * g⁻¹ ∈ L := by
      rw [← hgL]; exact ⟨x⁻¹, hx', rfl⟩
    have hxa : a⁻¹ * x⁻¹ * a ∈ conjSub a⁻¹ L := conj_mem_conjSub hx'
    have hgxa : g * (a⁻¹ * x⁻¹ * a) * g⁻¹ ∈ conjSub a⁻¹ L := by
      rw [← hgLa]; exact ⟨_, hxa, rfl⟩
    have hJ : g * (x⁻¹ * (a⁻¹ * x⁻¹ * a)) * g⁻¹ = x⁻¹ * (a⁻¹ * x⁻¹ * a) := by
      have h1 := mem_centralizer_iff.1 hg.1 (swapDiag hAB ⟨x⁻¹, hx'⟩) ⟨⟨x⁻¹, hx'⟩, rfl⟩
      rw [swapDiag_apply] at h1
      rw [← h1]
      group
    have hkey : ⁅x, g⁆ = (a⁻¹ * x⁻¹ * a) * (g * (a⁻¹ * x⁻¹ * a) * g⁻¹)⁻¹ := by
      have h2 : (g * x⁻¹ * g⁻¹) * (g * (a⁻¹ * x⁻¹ * a) * g⁻¹) = x⁻¹ * (a⁻¹ * x⁻¹ * a) := by
        rw [← hJ]; group
      rw [commutatorElement_def]
      calc x * g * x⁻¹ * g⁻¹ = x * (g * x⁻¹ * g⁻¹) := by group
        _ = x * (x⁻¹ * (a⁻¹ * x⁻¹ * a) * (g * (a⁻¹ * x⁻¹ * a) * g⁻¹)⁻¹) := by
          rw [← h2]; group
        _ = (a⁻¹ * x⁻¹ * a) * (g * (a⁻¹ * x⁻¹ * a) * g⁻¹)⁻¹ := by group
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [show ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) by rw [commutatorElement_def]; group]
      exact mul_mem hx hgx
    · rw [hkey]
      exact mul_mem hxa (inv_mem hgxa)
  have hLX : ⁅L, X⁆ ≤ centralizer (L : Set H) := by
    rw [Subgroup.commutator_le]
    intro x hx g hg
    have h := Subgroup.mem_inf.1 (hcomm x hx g hg)
    rw [mem_centralizer_iff]
    intro y hy
    exact (commute_of_commutator_eq_bot hAB hy h.2)
  have hLX' : ⁅L, X⁆ = ⊥ := perfect_double_commutator
    (commutator_self_of_isQuasisimple (assembly_isQuasisimple_of_isComponent hL))
    (Subgroup.commutator_eq_bot_iff_le_centralizer.2 hLX)
  have hXL : X ≤ centralizer (L : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact hLX')
  intro g hg
  have hgL := hXL hg
  have hgLa : ∀ y ∈ conjSub a⁻¹ L, g * y = y * g := by
    rintro _ ⟨x, hx, rfl⟩
    have hxa : (MulAut.conj a⁻¹).toMonoidHom x = a⁻¹ * x * a := by simp
    rw [hxa]
    have h1 := mem_centralizer_iff.1 hg.1 (swapDiag hAB ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩
    rw [swapDiag_apply] at h1
    have h2 := mem_centralizer_iff.1 hgL x hx
    have h3 : x * ((a⁻¹ * x * a) * g) = x * (g * (a⁻¹ * x * a)) := by
      calc x * ((a⁻¹ * x * a) * g) = x * (a⁻¹ * x * a) * g := by group
        _ = g * (x * (a⁻¹ * x * a)) := h1
        _ = (g * x) * (a⁻¹ * x * a) := by group
        _ = (x * g) * (a⁻¹ * x * a) := by rw [h2]
        _ = x * (g * (a⁻¹ * x * a)) := by group
    exact (mul_left_cancel h3).symm
  have hle : L ⊔ conjSub a⁻¹ L ≤ centralizer ({g} : Set H) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [mem_centralizer_iff]; rintro _ rfl
      exact (mem_centralizer_iff.1 hgL y hy).symm
    · rw [mem_centralizer_iff]; rintro _ rfl
      exact hgLa y hy
  rw [mem_centralizer_iff]
  intro y hy
  exact (mem_centralizer_iff.1 (hle hy) g rfl).symm

theorem diagonal_component_centralizer_index_two (ha : orderOf a = 2) :
    let La := conjSub a⁻¹ L
    let M := L ⊔ La
    let J := (swapDiag (commutator_conjSub_eq_bot hL hLa)).range
    let CJ := centralizer (J : Set H)
    let CM := centralizer (M : Set H)
    (J : Set H) = {g | ∃ x ∈ L, x * (a⁻¹ * x * a) = g} ∧
      (∀ g ∈ CJ, (conjSub g L = L ∧ conjSub g La = La) ∨
        (conjSub g L = La ∧ conjSub g La = L)) ∧
      {g | g ∈ CJ ∧ conjSub g L = L} = (CM : Set H) ∧
      (a ∈ CJ ∧ conjSub a L = La ∧ conjSub a La = L ∧ a ∉ CM) ∧
      CM ≤ CJ ∧ (CM.subgroupOf CJ).Normal ∧ CM ⊓ zpowers a = ⊥ ∧ CM ⊔ zpowers a = CJ ∧
      CM.relIndex CJ = 2 ∧ CJ ⊓ normalizer (L : Set H) = CM ∧
      M ⊓ CJ = (center M).map M.subtype ∧
      (∀ A : Subgroup H, A ≤ CJ → IsElementaryAbelian 2 A → a ∈ A →
        (A ⊓ CM).relIndex A = 2 ∧
        ∀ B : Subgroup H, B ≤ La → IsElementaryAbelian 2 B → A ⊓ CM ⊓ La ≤ B →
          A ⊓ CM ⊔ B ≤ centralizer (L : Set H) ∧ IsElementaryAbelian 2 ↥(A ⊓ CM ⊔ B) ∧
          Nat.card ↥(A ⊓ CM ⊔ B) =
            Nat.card A * Nat.card B / (2 * Nat.card ↥(A ⊓ CM ⊓ La))) := by
  intro La M J CJ CM
  set hAB := commutator_conjSub_eq_bot hL hLa
  have ha' : a⁻¹ = a := inv_eq_self_of_orderOf_eq_two ha
  have hinj : ∀ (g : H) {X Y : Subgroup H}, conjSub g X = conjSub g Y → X = Y := fun g X Y h => by
    have := congrArg (conjSub g⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  have hpair : ∀ g ∈ CJ, (conjSub g L = L ∧ conjSub g La = La) ∨
      (conjSub g L = La ∧ conjSub g La = L) := by
    intro g hg
    have h1 := conjSub_mem_pair hL hLa (Or.inl rfl) hg
    have h2 := conjSub_mem_pair hL hLa (Or.inr rfl) hg
    rcases h1 with h1 | h1
    · refine Or.inl ⟨h1, h2.resolve_left fun h => hLa (hinj g (h.trans h1.symm))⟩
    · refine Or.inr ⟨h1, h2.resolve_right fun h => hLa (hinj g (h1.trans h.symm)).symm⟩
  have hLM : L ≤ M := le_sup_left
  have hJM : J ≤ M := by
    rintro _ ⟨x, rfl⟩
    exact swapDiag_mem_sup hAB x
  have hCMCJ : CM ≤ CJ := Subgroup.centralizer_le hJM
  have hCMN : CM ≤ normalizer (L : Set H) :=
    (Subgroup.centralizer_le hLM).trans (centralizer_le_normalizer _)
  have hker : CJ ⊓ normalizer (L : Set H) = CM :=
    le_antisymm (centralizer_diag_inf_normalizer_le hL hLa) (le_inf hCMCJ hCMN)
  have hkerset : {g | g ∈ CJ ∧ conjSub g L = L} = (CM : Set H) := by
    ext g
    rw [← hker]
    constructor
    · rintro ⟨hg, hgL⟩
      exact ⟨hg, mem_normalizer_of_conjSub_le (le_of_eq hgL)
        (le_of_eq (by rw [← hgL, conjSub_inv_conjSub]; exact hgL.symm))⟩
    · rintro ⟨hg, hgN⟩
      exact ⟨hg, conjSub_eq_of_mem_normalizer hgN⟩
  have haCJ : a ∈ CJ := by
    rw [mem_centralizer_iff]
    rintro _ ⟨x, rfl⟩
    exact (mem_centralizer_iff.1 (swapDiag_mem_centralizer hAB ha' x) a rfl).symm
  have haL : conjSub a L = La := by
    show conjSub a L = conjSub a⁻¹ L
    rw [ha']
  have haLa : conjSub a La = L := conjSub_conjSub_inv a L
  have haCM : a ∉ CM := fun h => hLa (by
    rw [ha']
    exact conjSub_eq_of_mem_normalizer (hCMN h))
  have hxor : ∀ b ∈ CJ, Xor (b * a ∈ CM) (b ∈ CM) := by
    intro b hb
    by_cases hbM : b ∈ CM
    · refine Or.inr ⟨hbM, fun hba => haCM ?_⟩
      have := mul_mem (inv_mem hbM) hba
      rwa [inv_mul_cancel_left] at this
    · refine Or.inl ⟨?_, hbM⟩
      have hbL : conjSub b L ≠ L := fun h => hbM (by
        rw [← SetLike.mem_coe, ← hkerset]; exact ⟨hb, h⟩)
      rcases hpair b hb with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 hbL
      · rw [← SetLike.mem_coe, ← hkerset]
        refine ⟨mul_mem hb haCJ, ?_⟩
        rw [conjSub_mul, haL, h2]
  have hindex : CM.relIndex CJ = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haCJ⟩, fun b => ?_⟩
    exact hxor b b.2
  have hnormal : (CM.subgroupOf CJ).Normal := Subgroup.normal_of_index_eq_two hindex
  have hinf : CM ⊓ zpowers a = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxM, k, rfl⟩ := Subgroup.mem_inf.1 hx
    rw [mem_bot]
    have hk : a ^ k = a ^ (k % 2) := by
      have h0 := zpow_mod_orderOf a k
      rw [ha, Nat.cast_ofNat] at h0
      exact h0.symm
    change a ^ k ∈ CM at hxM
    show a ^ k = 1
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [hk, h, zpow_zero]
    · rw [hk, h, zpow_one] at hxM
      exact absurd hxM haCM
  have hsup : CM ⊔ zpowers a = CJ := by
    apply le_antisymm (sup_le hCMCJ ((zpowers_le).2 haCJ))
    intro b hb
    rcases hxor b hb with ⟨hba, -⟩ | ⟨hbM, -⟩
    · have : b = b * a * a⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left hba) (mem_sup_right (inv_mem (mem_zpowers a)))
    · exact mem_sup_left hbM
  have hMN : M ≤ normalizer (L : Set H) := sup_le le_normalizer
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.1
      (by rw [commutator_comm]; exact hAB)).trans (centralizer_le_normalizer _))
  have hcenter : M ⊓ CJ = (center M).map M.subtype := by
    ext m
    constructor
    · intro hm
      obtain ⟨hmM, hmJ⟩ := Subgroup.mem_inf.1 hm
      have hmC : m ∈ CM := by rw [← hker]; exact ⟨hmJ, hMN hmM⟩
      refine Subgroup.mem_map.2 ⟨⟨m, hmM⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.1 hmC y y.2)
    · rintro ⟨z, hz, rfl⟩
      refine Subgroup.mem_inf.2 ⟨z.2, ?_⟩
      rw [mem_centralizer_iff]
      intro j hj
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨j, hJM hj⟩)
  have hA : ∀ A : Subgroup H, A ≤ CJ → IsElementaryAbelian 2 A → a ∈ A →
      (A ⊓ CM).relIndex A = 2 ∧
      ∀ B : Subgroup H, B ≤ La → IsElementaryAbelian 2 B → A ⊓ CM ⊓ La ≤ B →
        A ⊓ CM ⊔ B ≤ centralizer (L : Set H) ∧ IsElementaryAbelian 2 ↥(A ⊓ CM ⊔ B) ∧
        Nat.card ↥(A ⊓ CM ⊔ B) =
          Nat.card A * Nat.card B / (2 * Nat.card ↥(A ⊓ CM ⊓ La)) := by
    intro A hAJ hAel haA
    have hA0 : (A ⊓ CM).relIndex A = 2 := by
      rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
      refine ⟨⟨a, haA⟩, fun b => ?_⟩
      have h := hxor b (hAJ b.2)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨⟨mul_mem b.2 haA, h1⟩, fun h => h2 h.2⟩
      · exact Or.inr ⟨⟨b.2, h1⟩, fun h => h2 h.2⟩
    refine ⟨hA0, fun B hBLa hBel hAB0 => ?_⟩
    have hA0C : A ⊓ CM ≤ centralizer (B : Set H) :=
      inf_le_right.trans (Subgroup.centralizer_le (hBLa.trans le_sup_right))
    have hcomm : ∀ x ∈ A ⊓ CM, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
      (mem_centralizer_iff.1 (hA0C hx) y hy).symm
    have hBL : B ≤ centralizer (L : Set H) := hBLa.trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rw [commutator_comm]; exact hAB))
    have hle : A ⊓ CM ⊔ B ≤ centralizer (L : Set H) :=
      sup_le (inf_le_right.trans (Subgroup.centralizer_le hLM)) hBL
    have hsq : ∀ g ∈ A ⊓ CM ⊔ B, g ^ 2 = 1 := by
      intro g hg
      have hset : ((A ⊓ CM ⊔ B : Subgroup H) : Set H) =
          ((A ⊓ CM : Subgroup H) : Set H) * (B : Set H) := by
        refine Subgroup.coe_mul_of_left_le_normalizer_right _ _ ?_
        exact hA0C.trans (centralizer_le_normalizer _)
      have hg' : g ∈ ((A ⊓ CM : Subgroup H) : Set H) * (B : Set H) := by rw [← hset]; exact hg
      obtain ⟨x, hx, y, hy, rfl⟩ := hg'
      have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x (Subgroup.mem_inf.1 hx).1
      have hy2 : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian y hy
      rw [(show Commute x y from hcomm x hx y hy).mul_pow, hx2, hy2, one_mul]
    have hA0ab : A ⊓ CM ≤ centralizer ((A ⊓ CM : Subgroup H) : Set H) := by
      rw [Subgroup.le_centralizer_iff_isMulCommutative]
      refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
      show (x : H) * y = y * x
      exact congrArg Subtype.val (hAel.is_comm.comm (⟨x, (Subgroup.mem_inf.1 x.2).1⟩ : A)
        ⟨y, (Subgroup.mem_inf.1 y.2).1⟩)
    have hBab : B ≤ centralizer (B : Set H) :=
      (Subgroup.le_centralizer_iff_isMulCommutative).2 hBel.toIsMulCommutative
    have hab : A ⊓ CM ⊔ B ≤ centralizer ((A ⊓ CM ⊔ B : Subgroup H) : Set H) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.le_centralizer_iff]
        exact sup_le hA0ab (Subgroup.le_centralizer_iff.1 hA0C)
      · rw [Subgroup.le_centralizer_iff]
        exact sup_le hA0C hBab
    have hel : IsElementaryAbelian 2 ↥(A ⊓ CM ⊔ B) :=
      { toIsMulCommutative := (Subgroup.le_centralizer_iff_isMulCommutative).1 hab
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
          Subtype.ext (by simpa using hsq g g.2) }
    refine ⟨hle, hel, ?_⟩
    have hcard := card_sup_mul_card_inf_of_commute hcomm
    have hinfB : A ⊓ CM ⊓ B = A ⊓ CM ⊓ La :=
      le_antisymm (inf_le_inf_left _ hBLa) (le_inf inf_le_left hAB0)
    rw [hinfB] at hcard
    have hA2 : Nat.card ↥(A ⊓ CM) * 2 = Nat.card A := by
      have h0 := Subgroup.relIndex_mul_card (H := A ⊓ CM) (K := A)
      rw [inf_eq_left.2 inf_le_left, hA0] at h0
      rw [mul_comm]
      exact h0
    have hpos : 0 < 2 * Nat.card ↥(A ⊓ CM ⊓ La) := Nat.mul_pos two_pos Nat.card_pos
    refine (Nat.div_eq_of_eq_mul_left hpos ?_).symm
    rw [← hA2]
    calc Nat.card ↥(A ⊓ CM) * 2 * Nat.card B
        = 2 * (Nat.card ↥(A ⊓ CM) * Nat.card B) := by ring
      _ = 2 * (Nat.card ↥(A ⊓ CM ⊔ B) * Nat.card ↥(A ⊓ CM ⊓ La)) := by rw [hcard]
      _ = Nat.card ↥(A ⊓ CM ⊔ B) * (2 * Nat.card ↥(A ⊓ CM ⊓ La)) := by ring
  refine ⟨?_, hpair, hkerset, ⟨haCJ, haL, haLa, haCM⟩, hCMCJ, hnormal, hinf, hsup, hindex,
    hker, hcenter, hA⟩
  ext g
  simp only [J, MonoidHom.coe_range, Set.mem_range, Set.mem_ofPred_eq, Subtype.exists,
    swapDiag_apply, exists_prop]

end Diagonal

end CFSG.LocalAnalysis.ComponentInitial
