module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftFamilyBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftLayerStruct

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.QuasithinUnique.Setup.Offender CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique
  CFSG.Quasithin.B6 CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups LinearAlgebra.Projectivization commutatorElement Pointwise
open Projectivization

universe v

section Vocab

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def IsOffender (H E : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  E ≤ H ∧ E ≠ ⊥ ∧ CFSG.IsElementaryAbelian 2 E ∧
    Nat.card V ≤ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E

theorem IsMinOffender.isOffender {H A : Subgroup (V ≃ₗ[ZMod 2] V)} (h : IsMinOffender H A) :
    IsOffender H A := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

@[expose] def IsInternalProduct {G : Type*} [Group G] (E : Subgroup G) (s : Finset (Subgroup G)) :
    Prop :=
  s.SupIndep id ∧ E = s.sup id ∧ ∀ A ∈ s, ∀ A' ∈ s, ∀ a ∈ A, ∀ a' ∈ A', a * a' = a' * a

theorem conjSub_commutator (L A : Subgroup (V ≃ₗ[ZMod 2] V)) (g : V ≃ₗ[ZMod 2] V) :
    ⁅conjSub g L, conjSub g A⁆ = conjSub g ⁅L, A⁆ := by
  show ⁅L.map (MulAut.conj g).toMonoidHom, A.map (MulAut.conj g).toMonoidHom⁆ =
    ⁅L, A⁆.map (MulAut.conj g).toMonoidHom
  rw [Subgroup.map_commutator]

end Vocab

section Commute

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commute {A D : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a) {x : G} (hx : x ∈ A ⊔ D) :
    ∃ a ∈ A, ∃ d ∈ D, x = a * d := by
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro d
    have hc : ∀ d ∈ D, a * d * a⁻¹ = d := fun d hd => by rw [hcomm a ha d hd]; group
    constructor
    · intro hd
      rw [hc d hd]
      exact hd
    · intro hd
      have h2 : a⁻¹ * (a * d * a⁻¹) * a = d := by group
      rw [← h2]
      have hinv : ∀ d' ∈ D, a⁻¹ * d' * a = d' := fun d' hd' => by
        have := hcomm a ha d' hd'
        calc a⁻¹ * d' * a = a⁻¹ * (d' * a) := by group
          _ = a⁻¹ * (a * d') := by rw [this]
          _ = d' := by group
      rw [hinv _ hd]
      exact hd
  have hset : ((A ⊔ D : Subgroup G) : Set G) = (A : Set G) * (D : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAD
  have hx' : x ∈ ((A ⊔ D : Subgroup G) : Set G) := hx
  rw [hset] at hx'
  obtain ⟨a, ha, d, hd, rfl⟩ := hx'
  exact ⟨a, ha, d, hd, rfl⟩

theorem supIndep_insert_of_commute [DecidableEq (Subgroup G)] {s : Finset (Subgroup G)}
    {A : Subgroup G} (hs : s.SupIndep id) (hA : A ∉ s) (hdisj : Disjoint A (s.sup id))
    (hcomm : ∀ A₁ ∈ insert A s, ∀ A₂ ∈ insert A s, ∀ a ∈ A₁, ∀ a' ∈ A₂, a * a' = a' * a) :
    (insert A s).SupIndep id := by
  rw [Finset.supIndep_iff_disjoint_erase]
  intro i hi
  rcases Finset.mem_insert.1 hi with rfl | his
  · rw [Finset.erase_insert hA]
    exact hdisj
  · have hne : A ≠ i := fun h => hA (h ▸ his)
    rw [Finset.erase_insert_of_ne hne, Finset.sup_insert]
    have hYA : ∀ a ∈ A, ∀ y ∈ (s.erase i).sup id, a * y = y * a := by
      have : (s.erase i).sup id ≤ Subgroup.centralizer (A : Set G) :=
        Finset.sup_le fun B hB z hz => Subgroup.mem_centralizer_iff.2 fun a ha =>
          hcomm A (Finset.mem_insert_self _ _) B
            (Finset.mem_insert_of_mem (Finset.mem_of_mem_erase hB)) a ha z hz
      intro a ha y hy
      exact Subgroup.mem_centralizer_iff.1 (this hy) a ha
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hxi, hxAY⟩
    obtain ⟨a, ha, y, hy, rfl⟩ := exists_mul_of_mem_sup_of_commute hYA hxAY
    have hxs : a * y ∈ s.sup id := (Finset.le_sup (f := id) his) hxi
    have hys : y ∈ s.sup id := (Finset.sup_mono (f := id) (Finset.erase_subset i s)) hy
    have hamem : a ∈ s.sup id := by
      have := Subgroup.mul_mem _ hxs (Subgroup.inv_mem _ hys)
      simpa using this
    have ha1 : a = 1 := Subgroup.mem_bot.1 (hdisj.le_bot ⟨ha, hamem⟩)
    subst ha1
    rw [one_mul] at hxi ⊢
    exact (Finset.supIndep_iff_disjoint_erase.1 hs i his).le_bot ⟨hxi, hy⟩

end Commute

section Generic

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_minOffender_le {H E : Subgroup (V ≃ₗ[ZMod 2] V)} (h : IsOffender H E) :
    ∃ A, A ≤ E ∧ IsMinOffender H A := by
  obtain ⟨hEH, hEne, hEel, hEoff⟩ := h
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  have : Nontrivial ↥E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne
  let ρ : ↥E →* (V ≃ₗ[ZMod 2] V) := (MonoidHom.id (V ≃ₗ[ZMod 2] V)).comp E.subtype
  have e2 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E ⊤
  rw [map_subtype_top] at e2
  have hρ : Nat.card V ≤ weight ρ ⊤ := by
    rw [e2]
    exact hEoff
  obtain ⟨B, hBbot, hwB, -, hstrict, hel⟩ := exists_maxWeight_minimalSubgroup ρ hρ
  have e1 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E B
  refine ⟨B.map E.subtype, Subgroup.map_subtype_le B,
    ⟨(Subgroup.map_subtype_le B).trans hEH, ?_, ?_, ?_, ?_⟩⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective B E.subtype_injective]
    exact hBbot
  · exact isElementaryAbelian_of_mulEquiv
      (show ↥(B.map E.subtype) ≃* ↥B from
        (B.equivMapOfInjective E.subtype E.subtype_injective).symm)
      (hel 2 hEel)
  · have h1 : Nat.card V ≤ weight ρ B := hρ.trans hwB
    rw [← e1]
    exact h1
  · intro D hD0 hDlt
    have hDE : D ≤ E := hDlt.le.trans (Subgroup.map_subtype_le B)
    have hDeq : (D.subgroupOf E).map E.subtype = D := Subgroup.map_subgroupOf_eq_of_le hDE
    have hD1 : ⊥ < D.subgroupOf E := by
      rw [bot_lt_iff_ne_bot]
      intro h0
      have : D = ⊥ := by rw [← hDeq, h0, Subgroup.map_bot]
      exact (bot_lt_iff_ne_bot.1 hD0) this
    have hD2 : D.subgroupOf E < B := by
      rw [← Subgroup.map_lt_map_iff_of_injective E.subtype_injective, hDeq]
      exact hDlt
    have h3 := hstrict _ hD1 hD2
    have e3 := weight_comp_subtype (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E (D.subgroupOf E)
    rw [hDeq] at e3
    have h4 : weight ρ (D.subgroupOf E) = weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) D := e3
    have h5 : weight ρ B = weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) (B.map E.subtype) := e1
    rw [h4, h5] at h3
    exact h3

theorem split_offender {A E : Subgroup (V ≃ₗ[ZMod 2] V)} (hAE : A ≤ E)
    (hEel : CFSG.IsElementaryAbelian 2 E)
    (hAw : weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A = Nat.card V)
    (hEw : weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) E = Nat.card V)
    {W : Submodule (ZMod 2) V} (hV : W ⊔ fixGL A = ⊤)
    (hfaith : ∀ a ∈ A, (∀ w ∈ W, a w = w) → a = 1)
    (hact : ∀ e ∈ E, ∃ a ∈ A, ∀ w ∈ W, e w = a w) :
    ∃ D : Subgroup (V ≃ₗ[ZMod 2] V), D ≤ E ∧ A ⊓ D = ⊥ ∧ E = A ⊔ D ∧
      (∀ d ∈ D, ∀ w ∈ W, d w = w) ∧ weight (MonoidHom.id (V ≃ₗ[ZMod 2] V)) D = Nat.card V := by
  classical
  let D : Subgroup (V ≃ₗ[ZMod 2] V) := E ⊓ centSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) W
  have hDE : D ≤ E := inf_le_left
  have hAD : A ⊓ D = ⊥ := by
    rw [eq_bot_iff]
    rintro a ⟨haA, haE, haW⟩
    exact Subgroup.mem_bot.2 (hfaith a haA fun w hw => haW w hw)
  have hED : E = A ⊔ D := by
    apply le_antisymm
    · intro e he
      obtain ⟨a, haA, hae⟩ := hact e he
      have hd : a⁻¹ * e ∈ D := by
        refine ⟨E.mul_mem (E.inv_mem (hAE haA)) he, fun w hw => ?_⟩
        show (a⁻¹ * e) w = w
        rw [LinearEquiv.mul_apply, hae w hw]
        exact ρ_inv_apply (MonoidHom.id (V ≃ₗ[ZMod 2] V)) a w
      have hee : e = a * (a⁻¹ * e) := by group
      rw [hee]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haA) (Subgroup.mem_sup_right hd)
    · exact sup_le hAE hDE
  have hcomm : ∀ a ∈ A, ∀ d ∈ D, a * d = d * a := fun a ha d hd =>
    congrArg Subtype.val (hEel.1.1.1 ⟨a, hAE ha⟩ ⟨d, hDE hd⟩)
  have hDW : W ≤ fixSub (MonoidHom.id (V ≃ₗ[ZMod 2] V)) D := fun w hw d hd => hd.2 w hw
  obtain ⟨-, -, h3⟩ := fixed_codimensions_add (MonoidHom.id (V ≃ₗ[ZMod 2] V)) A D hcomm W hDW hV
  refine ⟨D, hDE, hAD, hED, fun d hd w hw => hd.2 w hw, ?_⟩
  have hdisj : Disjoint A D := disjoint_iff.2 hAD
  refine (h3 hdisj).2 hAw ?_
  rw [← hED]
  exact hEw

@[expose] def OffenderSplit (H : Subgroup (V ≃ₗ[ZMod 2] V)) : Prop :=
  ∀ A E : Subgroup (V ≃ₗ[ZMod 2] V), IsMinOffender H A → A ≤ E → IsOffender H E →
    ∃ D : Subgroup (V ≃ₗ[ZMod 2] V), D ≤ E ∧ A ⊓ D = ⊥ ∧ E = A ⊔ D ∧ (D = ⊥ ∨ IsOffender H D)

theorem offender_internal_product {H : Subgroup (V ≃ₗ[ZMod 2] V)} (hsplit : OffenderSplit H)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hE : IsOffender H E) :
    ∃ s : Finset (Subgroup (V ≃ₗ[ZMod 2] V)), s.Nonempty ∧ (∀ A ∈ s, IsMinOffender H A) ∧
      IsInternalProduct E s := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv
  suffices h : ∀ m : ℕ, ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), Nat.card E = m → IsOffender H E →
      ∃ s : Finset (Subgroup (V ≃ₗ[ZMod 2] V)), s.Nonempty ∧ (∀ A ∈ s, IsMinOffender H A) ∧
        IsInternalProduct E s from h _ E rfl hE
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro E hm hE
    obtain ⟨A, hAE, hA⟩ := exists_minOffender_le hE
    obtain ⟨D, hDE, hAD, hED, hD⟩ := hsplit A E hA hAE hE
    have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hE.2.2.1.1.1.1 ⟨x, hx⟩ ⟨y, hy⟩)
    rcases hD with rfl | hDoff
    · refine ⟨{A}, Finset.singleton_nonempty _, ?_, Finset.supIndep_singleton _ _, ?_, ?_⟩
      · intro A' hA'
        rw [Finset.mem_singleton] at hA'
        rw [hA']
        exact hA
      · rw [Finset.sup_singleton]
        exact hED.trans (sup_bot_eq A)
      · intro A1 h1 A2 h2 a ha a' ha'
        rw [Finset.mem_singleton] at h1 h2
        subst h1
        subst h2
        exact hcommE a (hAE ha) a' (hAE ha')
    · have hDne : D ≠ E := by
        intro hDE'
        apply hA.2.1
        rw [← hAD, eq_comm, inf_eq_left]
        rw [hDE']
        exact hAE
      have hlt : Nat.card D < m := by
        rw [← hm]
        refine lt_of_le_of_ne (Subgroup.card_le_of_le hDE) fun hcard => hDne ?_
        exact Subgroup.eq_of_le_of_card_ge hDE hcard.symm.le
      obtain ⟨s', hne, hs', hsup, hDsup, hcomm'⟩ := ih (Nat.card D) hlt D rfl hDoff
      have hsE : ∀ A1 ∈ s', A1 ≤ E := fun A1 h1 =>
        (Finset.le_sup (f := id) h1).trans (hDsup ▸ hDE)
      have hcommAll : ∀ A₁ ∈ insert A s', ∀ A₂ ∈ insert A s', ∀ a ∈ A₁, ∀ a' ∈ A₂,
          a * a' = a' * a := by
        intro A1 h1 A2 h2 a ha a' ha'
        have hA1 : A1 ≤ E := by
          rcases Finset.mem_insert.1 h1 with rfl | h1
          · exact hAE
          · exact hsE A1 h1
        have hA2 : A2 ≤ E := by
          rcases Finset.mem_insert.1 h2 with rfl | h2
          · exact hAE
          · exact hsE A2 h2
        exact hcommE a (hA1 ha) a' (hA2 ha')
      have hAs' : A ∉ s' := by
        intro hAs
        have hAD' : A ≤ D := by
          rw [hDsup]
          exact Finset.le_sup (f := id) hAs
        apply hA.2.1
        rw [← hAD, eq_comm, inf_eq_left]
        exact hAD'
      refine ⟨insert A s', Finset.insert_nonempty _ _, ?_,
        supIndep_insert_of_commute hsup hAs' ?_ hcommAll, ?_, hcommAll⟩
      · intro A1 h1
        rcases Finset.mem_insert.1 h1 with rfl | h1
        · exact hA
        · exact hs' A1 h1
      · rw [← hDsup]
        exact disjoint_iff.2 hAD
      · rw [Finset.sup_insert, ← hDsup]
        exact hED

end Generic

section Normalizer

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H T : Subgroup (V ≃ₗ[ZMod 2] V)} {n r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Finite V] in
theorem mem_normalizer_of_commute (ctx : FamilyCtx H T n F r Lc) {A : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hA : IsMinOffender H A) {i : Fin r} (hmove : ⁅Lc i, A⁆ ≠ ⊥) {e : V ≃ₗ[ZMod 2] V}
    (heH : e ∈ H) (hcomm : ∀ a ∈ A, e * a = a * e) :
    e ∈ Subgroup.normalizer (Lc i : Set (V ≃ₗ[ZMod 2] V)) := by
  obtain ⟨-, i', -, huniq, -⟩ := ctx.layer.offender A hA
  have huniq' : ∀ j, ⁅Lc j, A⁆ ≠ ⊥ → j = i := fun j hj =>
    (huniq j hj).trans (huniq i hmove).symm
  obtain ⟨j, hj⟩ := ctx.hLc.perm heH i
  have hjj : conjSub e (Lc i) = Lc j := hj
  have hconjA : conjSub e A = A := by
    ext x
    rw [mem_conjSub]
    constructor
    · intro hx
      have h1 : e * (e⁻¹ * x * e) = (e⁻¹ * x * e) * e := hcomm _ hx
      have h2 : x = e⁻¹ * x * e := by
        calc x = (e * (e⁻¹ * x * e)) * e⁻¹ := by group
          _ = ((e⁻¹ * x * e) * e) * e⁻¹ := by rw [h1]
          _ = e⁻¹ * x * e := by group
      exact h2.symm ▸ hx
    · intro hx
      have h1 : e⁻¹ * x * e = x := by
        have h3 := hcomm x hx
        calc e⁻¹ * x * e = e⁻¹ * (x * e) := by group
          _ = e⁻¹ * (e * x) := by rw [h3]
          _ = x := by group
      rw [h1]
      exact hx
  have hjmove : ⁅Lc j, A⁆ ≠ ⊥ := by
    intro hbot
    apply hmove
    rw [← hjj, ← hconjA, conjSub_commutator] at hbot
    exact (conjSub e).injective (hbot.trans (conjSub e).map_bot.symm)
  have hji : j = i := huniq' j hjmove
  rw [hji] at hjj
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := mem_conjSub (g := e) (X := Lc i) (x := e * x * e⁻¹)
  rw [hjj] at h1
  have e2 : e⁻¹ * (e * x * e⁻¹) * e = x := by group
  rw [e2] at h1
  exact h1.symm

end Normalizer

end CFSG.QuasithinUnique.Setup.Lift
