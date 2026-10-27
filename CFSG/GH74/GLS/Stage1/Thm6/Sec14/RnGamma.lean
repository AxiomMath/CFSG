module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.NoFusion
public import CFSG.GH74.GLS.Stage1.Thm6.Sec14.RnKlein
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b CFSG.GH74.GLS.Stage1.Thm6.Sec14
open scoped commutatorElement

section Gamma

variable {Y : Type} [Group Y] [Finite Y]

noncomputable def actF (V : Subgroup Y) (e : Pt V ≃ Fin 3) :
    ↥(Subgroup.normalizer (V : Set Y)) →* Equiv.Perm (Fin 3) :=
  (Equiv.permCongrHom e).toMonoidHom.comp (actPtHom V)

omit [Finite Y] in
theorem actF_apply (V : Subgroup Y) (e : Pt V ≃ Fin 3) (g : ↥(Subgroup.normalizer (V : Set Y)))
    (v : Pt V) : actF V e g (e v) = e (actPt V g v) := by
  simp [actF, actPtHom, Equiv.permCongrHom, Equiv.permCongr_apply]

omit [Finite Y] in
theorem actF_eq_iff (V : Subgroup Y) (e : Pt V ≃ Fin 3) (g : ↥(Subgroup.normalizer (V : Set Y)))
    (v w : Pt V) : actF V e g (e v) = e w ↔ (g : Y) * v.1 * (g : Y)⁻¹ = w.1 := by
  rw [actF_apply, e.apply_eq_iff_eq, Subtype.ext_iff]
  rfl

omit [Finite Y] in
theorem mem_normalizer_iff_Hconj {V : Subgroup Y} {g : Y} :
    g ∈ Subgroup.normalizer (V : Set Y) ↔ Hconj g V = V := by
  constructor
  · intro hg
    ext a
    rw [mem_Hconj]
    exact (Subgroup.mem_normalizer_iff.1 hg a).symm
  · intro hg
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have := congrArg (fun K : Subgroup Y => a ∈ K) hg
    simp only [mem_Hconj, eq_iff_iff] at this
    exact this.symm

omit [Finite Y] in
theorem pow_relIndex_mem {M A : Subgroup Y} (_hAM : A ≤ M)
    (hN : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) {m : Y} (hm : m ∈ M) :
    m ^ A.relIndex M ∈ A := by
  have : (A.subgroupOf M).Normal := ⟨fun n hn g => by
    have := hN (g : Y) g.2 (n : Y) hn
    simpa [Subgroup.mem_subgroupOf] using this⟩
  have h1 : (QuotientGroup.mk (⟨m, hm⟩ : ↥M) : ↥M ⧸ A.subgroupOf M) ^ Nat.card (↥M ⧸ A.subgroupOf M) = 1 :=
    pow_card_eq_one'
  have h2 : (A.subgroupOf M).index = Nat.card (↥M ⧸ A.subgroupOf M) := Subgroup.index_eq_card _
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
  have h3 : A.relIndex M = Nat.card (↥M ⧸ A.subgroupOf M) := h2
  rw [h3]
  have := h1
  simpa [Subgroup.mem_subgroupOf] using this

theorem perm3_involution_fixed : ∀ τ : Equiv.Perm (Fin 3), τ * τ = 1 → ∃ j, τ j = j := by decide

structure Ctx16 (T A A₁ A₂ : Subgroup Y) : Prop where
  sylow : IsSylow2In T ⊤
  le : A ≤ T
  idx : A.relIndex T = 2
  elem : IsElemAb2 A
  card : Nat.card A = 16
  cent : ∀ w ∈ T, w ∉ A → Nat.card ↥(A ⊓ Subgroup.centralizer ({w} : Set Y)) = 4
  le₁ : A₁ ≤ A
  le₂ : A₂ ≤ A
  card₁ : Nat.card A₁ = 4
  card₂ : Nat.card A₂ = 4
  disj : A₁ ⊓ A₂ = ⊥
  inv : ∀ g ∈ Subgroup.normalizer (A : Set Y),
    (g ∈ Subgroup.normalizer (A₁ : Set Y) ∧ g ∈ Subgroup.normalizer (A₂ : Set Y)) ∨
      (Hconj g A₁ = A₂ ∧ Hconj g A₂ = A₁)
  Tinv : ∀ t ∈ T, t ∈ Subgroup.normalizer (A₁ : Set Y) ∧ t ∈ Subgroup.normalizer (A₂ : Set Y)

namespace Ctx16

variable {T A A₁ A₂ : Subgroup Y} (h : Ctx16 T A A₁ A₂)
include h

omit [Finite Y] in
theorem comm_A {a b : Y} (ha : a ∈ A) (hb : b ∈ A) : a * b = b * a := (h.elem a ha).2 b hb

theorem sup_eq : A₁ ⊔ A₂ = A := by
  have hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb =>
    h.comm_A (h.le₁ ha) (h.le₂ hb)
  have hcard := card_sup_of_commute hc h.disj
  exact Subgroup.eq_of_le_of_card_ge (sup_le h.le₁ h.le₂) (by
    rw [hcard, h.card₁, h.card₂, h.card])

theorem decomp {α : Y} (hα : α ∈ A) : ∃ a ∈ A₁, ∃ b ∈ A₂, α = a * b := by
  have hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb =>
    h.comm_A (h.le₁ ha) (h.le₂ hb)
  have : α ∈ A₁ ⊔ A₂ := by rw [h.sup_eq]; exact hα
  exact mem_sup_of_commute hc this

omit [Finite Y] in
theorem uniq {a b c d : Y} (ha : a ∈ A₁) (hb : b ∈ A₁) (hc : c ∈ A₂) (hd : d ∈ A₂)
    (e : a * c = b * d) : a = b ∧ c = d := by
  have h1 : b⁻¹ * a ∈ A₁ ⊓ A₂ := by
    refine Subgroup.mem_inf.2 ⟨A₁.mul_mem (A₁.inv_mem hb) ha, ?_⟩
    have : b⁻¹ * a = d * c⁻¹ := by
      calc b⁻¹ * a = b⁻¹ * (a * c) * c⁻¹ := by group
        _ = b⁻¹ * (b * d) * c⁻¹ := by rw [e]
        _ = d * c⁻¹ := by group
    rw [this]; exact A₂.mul_mem hd (A₂.inv_mem hc)
  rw [h.disj, Subgroup.mem_bot] at h1
  have hab : a = b := by
    have := mul_eq_one_iff_eq_inv.1 h1
    simpa using this.symm
  refine ⟨hab, ?_⟩
  rw [hab] at e
  exact mul_left_cancel e

omit [Finite Y] in
theorem nrm_le {g : Y} (hg : g ∈ Subgroup.normalizer (A : Set Y)) :
    g ∈ Subgroup.normalizer (A₁ : Set Y) ∧ g ∈ Subgroup.normalizer (A₂ : Set Y) := by
  by_contra hcon
  have hsw : Hconj g A₁ = A₂ ∧ Hconj g A₂ = A₁ := (h.inv g hg).resolve_left hcon
  set Nrm := Subgroup.normalizer (A : Set Y) with hNrm
  set Q := Nrm ⊓ Subgroup.normalizer (A₁ : Set Y) with hQ
  have hTN : T ≤ Nrm := fun t ht => mem_normalizer_of_mem h.le h.idx ht
  have hTQ : T ≤ Q := fun t ht => Subgroup.mem_inf.2 ⟨hTN ht, (h.Tinv t ht).1⟩
  have hQN : Q ≤ Nrm := inf_le_left
  have hne : A₁ ≠ A₂ := by
    intro e
    have h1 : A₁ ⊓ A₂ = A₁ := by rw [← e]; exact inf_idem A₁
    have hd := h.disj
    rw [h1] at hd
    have := h.card₁
    rw [hd, Subgroup.card_bot] at this
    omega
  have hg1 : g ∉ Subgroup.normalizer (A₁ : Set Y) := by
    intro h1
    have := (mem_normalizer_iff_Hconj).1 h1
    exact hne (this.symm.trans hsw.1)
  have hidx : Q.relIndex Nrm = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨g, hg, fun b hb => ?_⟩
    by_cases hbQ : b ∈ Q
    · refine Or.inr ⟨hbQ, fun hbg => ?_⟩
      have hgQ : g ∈ Q := by
        have := Q.mul_mem (Q.inv_mem hbQ) hbg
        simpa using this
      exact hg1 (Subgroup.mem_inf.1 hgQ).2
    · refine Or.inl ⟨?_, hbQ⟩
      have hb1 : b ∉ Subgroup.normalizer (A₁ : Set Y) := fun h1 => hbQ (Subgroup.mem_inf.2 ⟨hb, h1⟩)
      have hbsw : Hconj b A₁ = A₂ ∧ Hconj b A₂ = A₁ := (h.inv b hb).resolve_left (fun h' => hb1 h'.1)
      refine Subgroup.mem_inf.2 ⟨Nrm.mul_mem hb hg, ?_⟩
      rw [mem_normalizer_iff_Hconj, ← Hconj_mul, hbsw.1, hsw.2]
  have hrel := Subgroup.relIndex_mul_relIndex T Q Nrm hTQ hQN
  have hdvd : 2 ∣ T.relIndex Nrm := by rw [← hrel, hidx]; exact Dvd.intro_left _ rfl
  exact (isSylow2In_of_le h.sylow hTN).2.2 hdvd

noncomputable def Xi (e₁ : Pt A₁ ≃ Fin 3) (e₂ : Pt A₂ ≃ Fin 3) :
    ↥(Subgroup.normalizer (A : Set Y)) →* B3 :=
  ((actF A₁ e₁).comp (Subgroup.inclusion (fun _ hg => (h.nrm_le hg).1))).prod
    ((actF A₂ e₂).comp (Subgroup.inclusion (fun _ hg => (h.nrm_le hg).2)))

variable (e₁ : Pt A₁ ≃ Fin 3) (e₂ : Pt A₂ ≃ Fin 3)

theorem Xi_fst_eq_iff (g : ↥(Subgroup.normalizer (A : Set Y))) (v w : Pt A₁) :
    (Xi h e₁ e₂ g).1 (e₁ v) = e₁ w ↔ (g : Y) * v.1 * (g : Y)⁻¹ = w.1 :=
  actF_eq_iff A₁ e₁ _ v w

theorem Xi_snd_eq_iff (g : ↥(Subgroup.normalizer (A : Set Y))) (v w : Pt A₂) :
    (Xi h e₁ e₂ g).2 (e₂ v) = e₂ w ↔ (g : Y) * v.1 * (g : Y)⁻¹ = w.1 :=
  actF_eq_iff A₂ e₂ _ v w

theorem fst_one_cent {g : ↥(Subgroup.normalizer (A : Set Y))} (hg : (Xi h e₁ e₂ g).1 = 1) :
    ∀ a ∈ A₁, (g : Y) * a * (g : Y)⁻¹ = a := by
  intro a ha
  by_cases ha1 : a = 1
  · subst ha1; simp
  · have := (Xi_fst_eq_iff h e₁ e₂ g ⟨a, ha, ha1⟩ ⟨a, ha, ha1⟩).1 (by rw [hg]; rfl)
    exact this

theorem snd_one_cent {g : ↥(Subgroup.normalizer (A : Set Y))} (hg : (Xi h e₁ e₂ g).2 = 1) :
    ∀ a ∈ A₂, (g : Y) * a * (g : Y)⁻¹ = a := by
  intro a ha
  by_cases ha1 : a = 1
  · subst ha1; simp
  · have := (Xi_snd_eq_iff h e₁ e₂ g ⟨a, ha, ha1⟩ ⟨a, ha, ha1⟩).1 (by rw [hg]; rfl)
    exact this

theorem cent_of_Xi_eq_one {g : ↥(Subgroup.normalizer (A : Set Y))} (hg : Xi h e₁ e₂ g = 1) :
    (g : Y) ∈ Subgroup.centralizer (A : Set Y) := by
  have h1 : (Xi h e₁ e₂ g).1 = 1 := by rw [hg]; rfl
  have h2 : (Xi h e₁ e₂ g).2 = 1 := by rw [hg]; rfl
  rw [Subgroup.mem_centralizer_iff]
  intro α hα
  obtain ⟨a, ha, b, hb, rfl⟩ := h.decomp hα
  have ea := fst_one_cent h e₁ e₂ h1 a ha
  have eb := snd_one_cent h e₁ e₂ h2 b hb
  calc a * b * (g : Y) = (g : Y) * ((g : Y)⁻¹ * (a * b) * (g : Y)) := by group
    _ = (g : Y) * (a * b) := by
      congr 1
      have e1 : (g : Y)⁻¹ * a * (g : Y) = a := by
        have := congrArg (fun y => (g : Y)⁻¹ * y * (g : Y)) ea
        simpa [mul_assoc] using this.symm
      have e2 : (g : Y)⁻¹ * b * (g : Y) = b := by
        have := congrArg (fun y => (g : Y)⁻¹ * y * (g : Y)) eb
        simpa [mul_assoc] using this.symm
      calc (g : Y)⁻¹ * (a * b) * (g : Y) = ((g : Y)⁻¹ * a * (g : Y)) * ((g : Y)⁻¹ * b * (g : Y)) := by
            group
        _ = a * b := by rw [e1, e2]

theorem Xi_eq_one_of_cent {g : ↥(Subgroup.normalizer (A : Set Y))}
    (hg : (g : Y) ∈ Subgroup.centralizer (A : Set Y)) : Xi h e₁ e₂ g = 1 := by
  have hc : ∀ a ∈ A, (g : Y) * a * (g : Y)⁻¹ = a := by
    intro a ha
    have := Subgroup.mem_centralizer_iff.1 hg a ha
    calc (g : Y) * a * (g : Y)⁻¹ = (a * (g : Y)) * (g : Y)⁻¹ := by rw [← this]
      _ = a := by group
  apply Prod.ext
  · refine Equiv.ext fun j => ?_
    obtain ⟨v, rfl⟩ := e₁.surjective j
    have := (Xi_fst_eq_iff h e₁ e₂ g v v).2 (hc v.1 (h.le₁ v.2.1))
    simpa using this
  · refine Equiv.ext fun j => ?_
    obtain ⟨v, rfl⟩ := e₂.surjective j
    have := (Xi_snd_eq_iff h e₁ e₂ g v v).2 (hc v.1 (h.le₂ v.2.1))
    simpa using this


theorem cent_big {V W : Subgroup Y} (hVA : V ≤ A) (hWA : W ≤ A) (hV : Nat.card V = 4)
    (hVW : V ⊓ W = ⊥) {s : Y} (hsV : ∀ v ∈ V, s * v * s⁻¹ = v) {w : Y} (hwW : w ∈ W) (hw1 : w ≠ 1)
    (hsw : s * w * s⁻¹ = w) : 8 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer ({s} : Set Y)) := by
  have hwA : w ∈ A := hWA hwW
  have hw2 : w * w = 1 := (h.elem w hwA).1
  have hc : ∀ a ∈ V, ∀ b ∈ Subgroup.zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hbA : w ^ m ∈ A := A.zpow_mem hwA m
    exact h.comm_A (hVA ha) hbA
  have hd : V ⊓ Subgroup.zpowers w = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxV := (Subgroup.mem_inf.1 hx).1
    have hxz := (Subgroup.mem_inf.1 hx).2
    have hxW : x ∈ W := by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hxz
      exact W.zpow_mem hwW m
    have : x ∈ V ⊓ W := Subgroup.mem_inf.2 ⟨hxV, hxW⟩
    rw [hVW] at this
    exact this
  have hcard : Nat.card ↥(V ⊔ Subgroup.zpowers w) = 8 := by
    rw [card_sup_of_commute hc hd, hV, card_zpowers_of_sq hw2 hw1]
  have hle : V ⊔ Subgroup.zpowers w ≤ A ⊓ Subgroup.centralizer ({s} : Set Y) := by
    refine sup_le ?_ ?_
    · intro v hv
      refine Subgroup.mem_inf.2 ⟨hVA hv, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have := hsV v hv
      calc h' * v = (h' * v * h'⁻¹) * h' := by group
        _ = v * h' := by rw [this]
    · intro x hx
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      refine Subgroup.mem_inf.2 ⟨A.zpow_mem hwA m, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h' hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hcomm : h' * w = w * h' := by
        calc h' * w = (h' * w * h'⁻¹) * h' := by group
          _ = w * h' := by rw [hsw]
      exact (Commute.zpow_right (show Commute h' w from hcomm) m).eq
  have := Subgroup.card_le_of_le hle
  omega

def sN {s : Y} (hs : s ∈ T) : ↥(Subgroup.normalizer (A : Set Y)) :=
  ⟨s, mem_normalizer_of_mem h.le h.idx hs⟩

omit [Finite Y] in
theorem mul_self_mem_A {s : Y} (hs : s ∈ T) : s * s ∈ A := by
  have hidx : (A.subgroupOf T).index = 2 := h.idx
  have := Subgroup.mul_self_mem_of_index_two hidx ⟨s, hs⟩
  exact this

theorem Xi_sq {s : Y} (hs : s ∈ T) :
    (Xi h e₁ e₂ (sN h hs)) * (Xi h e₁ e₂ (sN h hs)) = 1 := by
  rw [← map_mul]
  apply Xi_eq_one_of_cent h e₁ e₂
  show s * s ∈ Subgroup.centralizer (A : Set Y)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact h.comm_A ha (h.mul_self_mem_A hs)

theorem Xi_fst_ne_one {s : Y} (hs : s ∈ T) (hsA : s ∉ A) : (Xi h e₁ e₂ (sN h hs)).1 ≠ 1 := by
  intro h1
  have hsq := congrArg Prod.snd (Xi_sq h e₁ e₂ hs)
  have hsq' : (Xi h e₁ e₂ (sN h hs)).2 * (Xi h e₁ e₂ (sN h hs)).2 = 1 := by simpa using hsq
  obtain ⟨j, hj⟩ := perm3_involution_fixed _ hsq'
  obtain ⟨v₀, rfl⟩ := e₂.surjective j
  have hfix := (Xi_snd_eq_iff h e₁ e₂ (sN h hs) v₀ v₀).1 hj
  have hbig := h.cent_big h.le₁ h.le₂ h.card₁ h.disj (s := s)
    (fun a ha => fst_one_cent h e₁ e₂ h1 a ha) v₀.2.1 v₀.2.2 hfix
  have := h.cent s hs hsA
  omega

theorem Xi_snd_ne_one {s : Y} (hs : s ∈ T) (hsA : s ∉ A) : (Xi h e₁ e₂ (sN h hs)).2 ≠ 1 := by
  intro h1
  have hsq := congrArg Prod.fst (Xi_sq h e₁ e₂ hs)
  have hsq' : (Xi h e₁ e₂ (sN h hs)).1 * (Xi h e₁ e₂ (sN h hs)).1 = 1 := by simpa using hsq
  obtain ⟨j, hj⟩ := perm3_involution_fixed _ hsq'
  obtain ⟨v₀, rfl⟩ := e₁.surjective j
  have hfix := (Xi_fst_eq_iff h e₁ e₂ (sN h hs) v₀ v₀).1 hj
  have hbig := h.cent_big h.le₂ h.le₁ h.card₂ (by rw [inf_comm]; exact h.disj) (s := s)
    (fun a ha => snd_one_cent h e₁ e₂ h1 a ha) v₀.2.1 v₀.2.2 hfix
  have := h.cent s hs hsA
  omega

theorem trans_fst
    (hfus : ∀ a ∈ A, ∀ b ∈ A, ∀ g : Y, g⁻¹ * a * g = b →
      ∃ n ∈ Subgroup.normalizer (A : Set Y), n⁻¹ * a * n = b)
    {w₁ w₂ : Y} (hw₁ : w₁ ∈ A₁) (hw₂ : w₂ ∈ A₂)
    (hconj : ∀ v ∈ A, v ≠ 1 → (v ∈ A₁ ∨ v ∈ A₂) → ∃ g : Y, g * v * g⁻¹ = w₁ ∨ g * v * g⁻¹ = w₂)
    (hw₁1 : w₁ ≠ 1) (j : Fin 3) :
    ∃ n : ↥(Subgroup.normalizer (A : Set Y)),
      (Xi h e₁ e₂ n).1 (e₁ ⟨w₁, hw₁, hw₁1⟩) = j := by
  set v : Pt A₁ := e₁.symm j with hv
  obtain ⟨g, hg⟩ := hconj v.1 (h.le₁ v.2.1) v.2.2 (Or.inl v.2.1)
  have key : ∀ w ∈ A, g * v.1 * g⁻¹ = w →
      ∃ n ∈ Subgroup.normalizer (A : Set Y), n⁻¹ * v.1 * n = w := by
    intro w hw hgw
    refine hfus v.1 (h.le₁ v.2.1) w hw g⁻¹ ?_
    simpa using hgw
  rcases hg with hg | hg
  · obtain ⟨n, hn, hnv⟩ := key w₁ (h.le₁ hw₁) hg
    refine ⟨⟨n, hn⟩, ?_⟩
    have : (⟨n, hn⟩ : ↥(Subgroup.normalizer (A : Set Y))) = ⟨n, hn⟩ := rfl
    have e : n * w₁ * n⁻¹ = v.1 := by
      calc n * w₁ * n⁻¹ = n * (n⁻¹ * v.1 * n) * n⁻¹ := by rw [hnv]
        _ = v.1 := by group
    have := (Xi_fst_eq_iff h e₁ e₂ ⟨n, hn⟩ ⟨w₁, hw₁, hw₁1⟩ v).2 e
    rw [this, hv, Equiv.apply_symm_apply]
  · exfalso
    obtain ⟨n, hn, hnv⟩ := key w₂ (h.le₂ hw₂) hg
    have e : n * w₂ * n⁻¹ = v.1 := by
      calc n * w₂ * n⁻¹ = n * (n⁻¹ * v.1 * n) * n⁻¹ := by rw [hnv]
        _ = v.1 := by group
    have h2 : n ∈ Subgroup.normalizer (A₂ : Set Y) := (h.nrm_le hn).2
    have hv2 : v.1 ∈ A₂ := by
      rw [← e]
      exact (Subgroup.mem_normalizer_iff.1 h2 w₂).1 hw₂
    have : v.1 ∈ A₁ ⊓ A₂ := Subgroup.mem_inf.2 ⟨v.2.1, hv2⟩
    rw [h.disj, Subgroup.mem_bot] at this
    exact v.2.2 this

theorem trans_snd
    (hfus : ∀ a ∈ A, ∀ b ∈ A, ∀ g : Y, g⁻¹ * a * g = b →
      ∃ n ∈ Subgroup.normalizer (A : Set Y), n⁻¹ * a * n = b)
    {w₁ w₂ : Y} (hw₁ : w₁ ∈ A₁) (hw₂ : w₂ ∈ A₂)
    (hconj : ∀ v ∈ A, v ≠ 1 → (v ∈ A₁ ∨ v ∈ A₂) → ∃ g : Y, g * v * g⁻¹ = w₁ ∨ g * v * g⁻¹ = w₂)
    (hw₂1 : w₂ ≠ 1) (j : Fin 3) :
    ∃ n : ↥(Subgroup.normalizer (A : Set Y)),
      (Xi h e₁ e₂ n).2 (e₂ ⟨w₂, hw₂, hw₂1⟩) = j := by
  set v : Pt A₂ := e₂.symm j with hv
  obtain ⟨g, hg⟩ := hconj v.1 (h.le₂ v.2.1) v.2.2 (Or.inr v.2.1)
  have key : ∀ w ∈ A, g * v.1 * g⁻¹ = w →
      ∃ n ∈ Subgroup.normalizer (A : Set Y), n⁻¹ * v.1 * n = w := by
    intro w hw hgw
    refine hfus v.1 (h.le₂ v.2.1) w hw g⁻¹ ?_
    simpa using hgw
  rcases hg with hg | hg
  · exfalso
    obtain ⟨n, hn, hnv⟩ := key w₁ (h.le₁ hw₁) hg
    have e : n * w₁ * n⁻¹ = v.1 := by
      calc n * w₁ * n⁻¹ = n * (n⁻¹ * v.1 * n) * n⁻¹ := by rw [hnv]
        _ = v.1 := by group
    have h1 : n ∈ Subgroup.normalizer (A₁ : Set Y) := (h.nrm_le hn).1
    have hv1 : v.1 ∈ A₁ := by
      rw [← e]
      exact (Subgroup.mem_normalizer_iff.1 h1 w₁).1 hw₁
    have : v.1 ∈ A₁ ⊓ A₂ := Subgroup.mem_inf.2 ⟨hv1, v.2.1⟩
    rw [h.disj, Subgroup.mem_bot] at this
    exact v.2.2 this
  · obtain ⟨n, hn, hnv⟩ := key w₂ (h.le₂ hw₂) hg
    refine ⟨⟨n, hn⟩, ?_⟩
    have e : n * w₂ * n⁻¹ = v.1 := by
      calc n * w₂ * n⁻¹ = n * (n⁻¹ * v.1 * n) * n⁻¹ := by rw [hnv]
        _ = v.1 := by group
    have := (Xi_snd_eq_iff h e₁ e₂ ⟨n, hn⟩ ⟨w₂, hw₂, hw₂1⟩ v).2 e
    rw [this, hv, Equiv.apply_symm_apply]

omit [Finite Y] in
theorem coe_sN_mul {s : Y} (hs : s ∈ T) (n : ↥(Subgroup.normalizer (A : Set Y))) :
    ((sN h hs * n * (sN h hs)⁻¹ * n⁻¹ : ↥(Subgroup.normalizer (A : Set Y))) : Y) =
      ⁅s, (n : Y)⁆ := by
  simp [sN, commutatorElement_def]

theorem comm_trick {s : Y} (hs : s ∈ T) (n : ↥(Subgroup.normalizer (A : Set Y)))
    (hn3 : (Xi h e₁ e₂ n) ^ 3 = 1)
    (hσ : Xi h e₁ e₂ (sN h hs) * Xi h e₁ e₂ n * (Xi h e₁ e₂ (sN h hs))⁻¹ = (Xi h e₁ e₂ n)⁻¹) :
    ∃ m : ↥(Subgroup.normalizer (A : Set Y)), (m : Y) ∈ commutator Y ∧
      Xi h e₁ e₂ m = Xi h e₁ e₂ n := by
  refine ⟨sN h hs * n * (sN h hs)⁻¹ * n⁻¹, ?_, ?_⟩
  · rw [coe_sN_mul]
    show ⁅s, (n : Y)⁆ ∈ (⁅(⊤ : Subgroup Y), (⊤ : Subgroup Y)⁆)
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · simp only [map_mul, map_inv]
    rw [hσ]
    set γ := Xi h e₁ e₂ n
    have h1 : γ⁻¹ = γ ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', hn3]
    calc γ⁻¹ * γ⁻¹ = γ ^ 2 * γ ^ 2 := by rw [h1]
      _ = γ ^ 3 * γ := by group
      _ = γ := by rw [hn3, one_mul]

theorem cube_of_mem_comm (hAc : A ≤ commutator Y) (hSyl : IsSylow2In A (commutator Y))
    (n : ↥(Subgroup.normalizer (A : Set Y))) (hn : (n : Y) ∈ commutator Y) :
    (Xi h e₁ e₂ n) ^ 3 = 1 := by
  set M := commutator Y ⊓ Subgroup.normalizer (A : Set Y) with hM
  have hAM : A ≤ M := le_inf hAc Subgroup.le_normalizer
  have hMN : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A := fun m hm a ha =>
    (Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 hm).2 a).1 ha
  have hnM : (n : Y) ∈ M := Subgroup.mem_inf.2 ⟨hn, n.2⟩
  have hpow := pow_relIndex_mem hAM hMN hnM
  set u := A.relIndex M with hu
  have hu2 : ¬ 2 ∣ u := by
    have hrel := Subgroup.relIndex_mul_relIndex A M (commutator Y) hAM inf_le_left
    intro h2
    exact hSyl.2.2 (hrel ▸ Dvd.dvd.mul_right h2 _)
  have h1 : (Xi h e₁ e₂ n) ^ u = 1 := by
    rw [← map_pow]
    apply Xi_eq_one_of_cent h e₁ e₂
    show (n : Y) ^ u ∈ Subgroup.centralizer (A : Set Y)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact h.comm_A ha hpow
  have h6 : (Xi h e₁ e₂ n) ^ 6 = 1 := B3_exp _
  have hgcd := pow_gcd_eq_one.2 ⟨h6, h1⟩
  have hg3 : Nat.gcd 6 u ∣ 3 := by
    have hg6 : Nat.gcd 6 u ∣ 6 := Nat.gcd_dvd_left 6 u
    have hgu : Nat.gcd 6 u ∣ u := Nat.gcd_dvd_right 6 u
    have hle : Nat.gcd 6 u ≤ 6 := Nat.le_of_dvd (by norm_num) hg6
    have hodd : ¬ 2 ∣ Nat.gcd 6 u := fun h2 => hu2 (h2.trans hgu)
    interval_cases hgg : Nat.gcd 6 u <;> simp_all
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one hgcd).trans hg3)

theorem dichotomy (hAc : A ≤ commutator Y) (hSyl : IsSylow2In A (commutator Y))
    (hfus : ∀ a ∈ A, ∀ b ∈ A, ∀ g : Y, g⁻¹ * a * g = b →
      ∃ n ∈ Subgroup.normalizer (A : Set Y), n⁻¹ * a * n = b)
    {w₁ w₂ : Y} (hw₁ : w₁ ∈ A₁) (hw₂ : w₂ ∈ A₂) (hw₁1 : w₁ ≠ 1) (hw₂1 : w₂ ≠ 1)
    (hconj : ∀ v ∈ A, v ≠ 1 → (v ∈ A₁ ∨ v ∈ A₂) →
      ∃ g : Y, g * v * g⁻¹ = w₁ ∨ g * v * g⁻¹ = w₂) :
    (∃ x₃ ∈ commutator Y ⊓ Subgroup.normalizer (A : Set Y),
        (∀ α ∈ A, α ≠ 1 → x₃ * α * x₃⁻¹ ≠ α) ∧ x₃ ^ 3 ∈ Subgroup.centralizer (A : Set Y) ∧
        ∀ n ∈ commutator Y ⊓ Subgroup.normalizer (A : Set Y),
          ∃ c ∈ commutator Y ⊓ Subgroup.centralizer (A : Set Y), ∃ k : ℕ, n = c * x₃ ^ k) ∨
    (∀ α ∈ A, ∀ β ∈ A, α ≠ 1 → α ∉ A₁ → α ∉ A₂ → β ≠ 1 → β ∉ A₁ → β ∉ A₂ →
        ∃ n ∈ commutator Y ⊓ Subgroup.normalizer (A : Set Y), n * α * n⁻¹ = β) := by
  classical
  obtain ⟨e₁⟩ : Nonempty (Pt A₁ ≃ Fin 3) := ⟨Finite.equivFinOfCardEq (card_Pt h.card₁)⟩
  obtain ⟨e₂⟩ : Nonempty (Pt A₂ ≃ Fin 3) := ⟨Finite.equivFinOfCardEq (card_Pt h.card₂)⟩
  obtain ⟨s, hsT, hsA⟩ : ∃ s, s ∈ T ∧ s ∉ A := by
    by_contra hcon
    have h1 : A.relIndex T = 1 := Subgroup.relIndex_eq_one.2 (fun t ht => by
      by_contra hn; exact hcon ⟨t, ht, hn⟩)
    have := h.idx
    omega
  set σ := Xi h e₁ e₂ (sN h hsT) with hσdef
  have hσ1 : σ.1 ≠ 1 := Xi_fst_ne_one h e₁ e₂ hsT hsA
  have hσ2 : σ.2 ≠ 1 := Xi_snd_ne_one h e₁ e₂ hsT hsA
  have hσsq := Xi_sq h e₁ e₂ hsT
  have hσ1' : σ.1 * σ.1 = 1 := by simpa using congrArg Prod.fst hσsq
  have hσ2' : σ.2 * σ.2 = 1 := by simpa using congrArg Prod.snd hσsq
  set Γ := (Xi h e₁ e₂).range with hΓ
  have htr1 : ∀ j : Fin 3, ∃ γ ∈ Γ, γ.1 (e₁ ⟨w₁, hw₁, hw₁1⟩) = j := by
    intro j
    obtain ⟨n, hn⟩ := trans_fst h e₁ e₂ hfus hw₁ hw₂ hconj hw₁1 j
    exact ⟨Xi h e₁ e₂ n, ⟨n, rfl⟩, hn⟩
  have htr2 : ∀ j : Fin 3, ∃ γ ∈ Γ, γ.2 (e₂ ⟨w₂, hw₂, hw₂1⟩) = j := by
    intro j
    obtain ⟨n, hn⟩ := trans_snd h e₁ e₂ hfus hw₁ hw₂ hconj hw₂1 j
    exact ⟨Xi h e₁ e₂ n, ⟨n, rfl⟩, hn⟩
  obtain ⟨hinvσ, γ₀, hγ₀Γ, hγ₀3, hγ₀1, hγ₀2⟩ :=
    fl_main Γ σ hσ1 hσ2 hσ1' hσ2' _ _ htr1 htr2
  set MN : Subgroup ↥(Subgroup.normalizer (A : Set Y)) :=
    (commutator Y).subgroupOf (Subgroup.normalizer (A : Set Y)) with hMN
  set Γ₀ : Subgroup B3 := MN.map (Xi h e₁ e₂) with hΓ₀
  have hΓ₀3 : ∀ γ ∈ Γ₀, γ ^ 3 = 1 := by
    intro γ hγ
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hγ
    exact cube_of_mem_comm h e₁ e₂ hAc hSyl n hn
  have hγ₀Γ₀ : γ₀ ∈ Γ₀ := by
    obtain ⟨n, hn⟩ := hγ₀Γ
    obtain ⟨m, hmc, hm⟩ := comm_trick h e₁ e₂ hsT n (by rw [hn]; exact hγ₀3)
      (by rw [hn]; exact hinvσ γ₀ hγ₀3)
    exact Subgroup.mem_map.2 ⟨m, hmc, by rw [hm, hn]⟩
  rcases fl_dichotomy Γ₀ hΓ₀3 γ₀ hγ₀Γ₀ hγ₀1 with hI | hII
  · left
    obtain ⟨n₀, hn₀, hn₀γ⟩ := Subgroup.mem_map.1 hγ₀Γ₀
    have hn₀c : (n₀ : Y) ∈ commutator Y := hn₀
    refine ⟨(n₀ : Y), Subgroup.mem_inf.2 ⟨hn₀c, n₀.2⟩, ?_, ?_, ?_⟩
    · intro α hα hα1 hfix
      obtain ⟨a, ha, b, hb, rfl⟩ := h.decomp hα
      have h1 : (n₀ : Y) ∈ Subgroup.normalizer (A₁ : Set Y) := (h.nrm_le n₀.2).1
      have h2 : (n₀ : Y) ∈ Subgroup.normalizer (A₂ : Set Y) := (h.nrm_le n₀.2).2
      have ha' : (n₀ : Y) * a * (n₀ : Y)⁻¹ ∈ A₁ := (Subgroup.mem_normalizer_iff.1 h1 a).1 ha
      have hb' : (n₀ : Y) * b * (n₀ : Y)⁻¹ ∈ A₂ := (Subgroup.mem_normalizer_iff.1 h2 b).1 hb
      have hsplit : ((n₀ : Y) * a * (n₀ : Y)⁻¹) * ((n₀ : Y) * b * (n₀ : Y)⁻¹) = a * b := by
        calc ((n₀ : Y) * a * (n₀ : Y)⁻¹) * ((n₀ : Y) * b * (n₀ : Y)⁻¹)
            = (n₀ : Y) * (a * b) * (n₀ : Y)⁻¹ := by group
          _ = a * b := hfix
      obtain ⟨ea, eb⟩ := h.uniq ha' ha hb' hb hsplit
      have hγ1 : γ₀.1 ≠ 1 := hγ₀1
      have hγ2 : γ₀.2 ≠ 1 := hγ₀2
      have hγ13 : γ₀.1 ^ 3 = 1 := by simpa using congrArg Prod.fst hγ₀3
      have hγ23 : γ₀.2 ^ 3 = 1 := by simpa using congrArg Prod.snd hγ₀3
      have ha1 : a = 1 := by
        by_contra ha1
        have := (Xi_fst_eq_iff h e₁ e₂ n₀ ⟨a, ha, ha1⟩ ⟨a, ha, ha1⟩).2 ea
        rw [hn₀γ] at this
        exact perm3_fpf γ₀.1 hγ13 hγ1 _ this
      have hb1 : b = 1 := by
        by_contra hb1
        have := (Xi_snd_eq_iff h e₁ e₂ n₀ ⟨b, hb, hb1⟩ ⟨b, hb, hb1⟩).2 eb
        rw [hn₀γ] at this
        exact perm3_fpf γ₀.2 hγ23 hγ2 _ this
      apply hα1
      rw [ha1, hb1, one_mul]
    · have := cent_of_Xi_eq_one h e₁ e₂ (g := n₀ ^ 3) (by rw [map_pow, hn₀γ, hγ₀3])
      simpa using this
    · intro n hn
      have hnN : n ∈ Subgroup.normalizer (A : Set Y) := (Subgroup.mem_inf.1 hn).2
      have hnc : n ∈ commutator Y := (Subgroup.mem_inf.1 hn).1
      set nN : ↥(Subgroup.normalizer (A : Set Y)) := ⟨n, hnN⟩
      have hnMN : nN ∈ MN := hnc
      have hmem : Xi h e₁ e₂ nN ∈ Γ₀ := Subgroup.mem_map.2 ⟨nN, hnMN, rfl⟩
      have hk : ∃ k : ℕ, Xi h e₁ e₂ nN = γ₀ ^ k := by
        rcases hI _ hmem with e | e | e
        · exact ⟨0, by rw [e]; simp⟩
        · exact ⟨1, by rw [e]; simp⟩
        · exact ⟨2, e⟩
      obtain ⟨k, hk⟩ := hk
      refine ⟨n * ((n₀ : Y) ^ k)⁻¹, Subgroup.mem_inf.2 ⟨?_, ?_⟩, k, ?_⟩
      · exact (commutator Y).mul_mem hnc ((commutator Y).inv_mem ((commutator Y).pow_mem hn₀c k))
      · have hc : (n * ((n₀ : Y) ^ k)⁻¹) ∈ Subgroup.normalizer (A : Set Y) :=
          (Subgroup.normalizer (A : Set Y)).mul_mem hnN
            ((Subgroup.normalizer (A : Set Y)).inv_mem
              ((Subgroup.normalizer (A : Set Y)).pow_mem n₀.2 k))
        have := cent_of_Xi_eq_one h e₁ e₂ (g := ⟨n * ((n₀ : Y) ^ k)⁻¹, hc⟩) (by
          have e : (⟨n * ((n₀ : Y) ^ k)⁻¹, hc⟩ : ↥(Subgroup.normalizer (A : Set Y))) = nN * (n₀ ^ k)⁻¹ := rfl
          rw [e, map_mul, map_inv, map_pow, hk, hn₀γ, mul_inv_cancel])
        exact this
      · group
  · right
    intro α hα β hβ hα1 hαA₁ hαA₂ hβ1 hβA₁ hβA₂
    obtain ⟨a, ha, b, hb, rfl⟩ := h.decomp hα
    obtain ⟨a', ha', b', hb', rfl⟩ := h.decomp hβ
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact hαA₂ (by simpa using hb)
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact hαA₁ (by simpa using ha)
    have ha1' : a' ≠ 1 := by
      rintro rfl
      exact hβA₂ (by simpa using hb')
    have hb1' : b' ≠ 1 := by
      rintro rfl
      exact hβA₁ (by simpa using ha')
    obtain ⟨c₁, hc₁, hc₁a⟩ := perm3_cycle (e₁ ⟨a, ha, ha1⟩) (e₁ ⟨a', ha', ha1'⟩)
    obtain ⟨c₂, hc₂, hc₂b⟩ := perm3_cycle (e₂ ⟨b, hb, hb1⟩) (e₂ ⟨b', hb', hb1'⟩)
    have hε3 : ((c₁, c₂) : B3) ^ 3 = 1 := Prod.ext hc₁ hc₂
    obtain ⟨n, hn, hnε⟩ := Subgroup.mem_map.1 (hII _ hε3)
    have hn1 : (Xi h e₁ e₂ n).1 (e₁ ⟨a, ha, ha1⟩) = e₁ ⟨a', ha', ha1'⟩ := by
      rw [hnε]; exact hc₁a
    have hn2 : (Xi h e₁ e₂ n).2 (e₂ ⟨b, hb, hb1⟩) = e₂ ⟨b', hb', hb1'⟩ := by
      rw [hnε]; exact hc₂b
    have e1 := (Xi_fst_eq_iff h e₁ e₂ n _ _).1 hn1
    have e2 := (Xi_snd_eq_iff h e₁ e₂ n _ _).1 hn2
    refine ⟨(n : Y), Subgroup.mem_inf.2 ⟨hn, n.2⟩, ?_⟩
    calc (n : Y) * (a * b) * (n : Y)⁻¹ = ((n : Y) * a * (n : Y)⁻¹) * ((n : Y) * b * (n : Y)⁻¹) := by
          group
      _ = a' * b' := by rw [e1, e2]

end Ctx16

end Gamma

end CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn
