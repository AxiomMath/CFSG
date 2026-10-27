module

public import CFSG.LocalAnalysis.OddStandard.ThmCTAut
public import CFSG.LocalAnalysis.OddStandard.ThmCTFacts

public section

namespace CFSG.OddStandard.ThmC.T

open CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open scoped commutatorElement

structure TAmbient {G : Type*} [Group G] (S Z A B : Subgroup G) : Prop where
  Z_le_A : Z ≤ A
  Z_le_B : Z ≤ B
  A_le_S : A ≤ S
  B_le_S : B ≤ S
  card_S : Nat.card S = 64
  card_Z : Nat.card Z = 4
  card_A : Nat.card A = 16
  card_B : Nat.card B = 16
  A_ne_B : A ≠ B
  mem_Z : ∀ g : G, g ∈ Z ↔ g ∈ S ∧ ∀ s ∈ S, g * s = s * g
  Z_sq : ∀ z ∈ Z, z * z = 1
  comm_mem_Z : ∀ x ∈ S, ∀ y ∈ S, x * y * x⁻¹ * y⁻¹ ∈ Z
  sq_mem_Z : ∀ x ∈ S, x * x ∈ Z
  A_abel : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x
  B_abel : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x
  A_sq : ∀ x ∈ A, x * x = 1
  B_sq : ∀ x ∈ B, x * x = 1
  AB_le_Z : ∀ x, x ∈ A → x ∈ B → x ∈ Z
  A_norm : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A
  B_norm : ∀ s ∈ S, ∀ b ∈ B, s * b * s⁻¹ ∈ B
  invol : ∀ x ∈ S, x * x = 1 → x ∈ A ∨ x ∈ B
  cent_A : ∀ a ∈ A, a ∉ Z → ∀ s ∈ S, s * a = a * s → s ∈ A
  cent_B : ∀ b ∈ B, b ∉ Z → ∀ s ∈ S, s * b = b * s → s ∈ B
  cent_not_A : ∀ s ∈ S, s ∉ A → ∀ a ∈ A, a * s = s * a → a ∈ Z
  cent_not_B : ∀ s ∈ S, s ∉ B → ∀ b ∈ B, b * s = s * b → b ∈ Z
  normal_dich : ∀ N : Subgroup G, N ≤ S → (∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) →
    N ≤ Z ∨ Z ≤ N
  elemAb_le : ∀ E : Subgroup G, E ≤ S → (∀ x ∈ E, x * x = 1) →
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → E ≤ A ∨ E ≤ B
  extremal : ∀ z ∈ Z, z ≠ 1 → ∀ a ∈ S, a ∉ Z → ∃ s ∈ S, ∃ t ∈ S,
    s * a * s⁻¹ * a⁻¹ ∈ Subgroup.zpowers z ∧ t * a * t⁻¹ * a⁻¹ ∈ Subgroup.zpowers z ∧
      s * t * s⁻¹ * t⁻¹ ∉ Subgroup.zpowers z
  diag : ∀ g : G, g ∈ Subgroup.normalizer (S : Set G) → (∀ z ∈ Z, g * z * g⁻¹ = z) →
    (∀ a ∈ A, g * a * g⁻¹ ∈ A) → (∀ b ∈ B, g * b * g⁻¹ ∈ B) →
    (∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ Z) ∨
      ((∀ s ∈ S, g * s * g⁻¹ * s⁻¹ ∈ Z → s ∈ Z) ∧
        ∀ s ∈ S, g ^ 3 * s * (g ^ 3)⁻¹ * s⁻¹ ∈ Z)

section Equiv

variable {P : Type*} [Group P] (e : P ≃* Tc)

include e

theorem mem_zpowers_equiv_iff (x z : P) :
    x ∈ Subgroup.zpowers z ↔ e x ∈ Subgroup.zpowers (e z) := by
  have h : (Subgroup.zpowers z).map e.toMonoidHom = Subgroup.zpowers (e z) :=
    MonoidHom.map_zpowers e.toMonoidHom z
  rw [← h, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

theorem extremal_of_equiv {z a : P} (hz : z ∈ Subgroup.center P) (hz1 : z ≠ 1)
    (ha : a ∉ Subgroup.center P) :
    ∃ s t : P, ⁅s, a⁆ ∈ Subgroup.zpowers z ∧ ⁅t, a⁆ ∈ Subgroup.zpowers z ∧
      ⁅s, t⁆ ∉ Subgroup.zpowers z := by
  have hz' : e z ∈ Subgroup.center Tc := (mem_center_equiv_iff e z).1 hz
  have hz1' : e z ≠ 1 := fun h => hz1 (e.injective (by rw [h, map_one]))
  have ha' : e a ∉ Subgroup.center Tc := fun h => ha ((mem_center_equiv_iff e a).2 h)
  obtain ⟨s, t, h1, h2, h3⟩ := extremal_tc hz' hz1' ha'
  refine ⟨e.symm s, e.symm t, ?_, ?_, ?_⟩
  · rw [mem_zpowers_equiv_iff e, map_commutatorElement, MulEquiv.apply_symm_apply]
    exact h1
  · rw [mem_zpowers_equiv_iff e, map_commutatorElement, MulEquiv.apply_symm_apply]
    exact h2
  · rw [mem_zpowers_equiv_iff e, map_commutatorElement, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    exact h3

theorem diag_of_equiv (φ : P ≃* P) (hZ : ∀ z ∈ Subgroup.center P, φ z = z)
    (hA : ∀ x, (e x).b = 0 → (e (φ x)).b = 0) (hB : ∀ x, (e x).a = 0 → (e (φ x)).a = 0) :
    (∀ s, φ s * s⁻¹ ∈ Subgroup.center P) ∨
      ((∀ s, φ s * s⁻¹ ∈ Subgroup.center P → s ∈ Subgroup.center P) ∧
        ∀ s, φ (φ (φ s)) * s⁻¹ ∈ Subgroup.center P) := by
  let ψ : Tc ≃* Tc := e.symm.trans (φ.trans e)
  have hψ : ∀ s : P, ψ (e s) = e (φ s) := fun s => by simp [ψ]
  have hψ' : ∀ y : Tc, ψ y = e (φ (e.symm y)) := fun y => rfl
  have key := diag_tc ψ
    (fun z hz => by
      have h1 : e.symm z ∈ Subgroup.center P := by
        rw [mem_center_equiv_iff e, MulEquiv.apply_symm_apply]; exact hz
      rw [hψ', hZ _ h1, MulEquiv.apply_symm_apply])
    (fun x hx => by
      rw [hψ']
      have := hA (e.symm x) (by rw [MulEquiv.apply_symm_apply]; exact hx)
      exact this)
    (fun x hx => by
      rw [hψ']
      have := hB (e.symm x) (by rw [MulEquiv.apply_symm_apply]; exact hx)
      exact this)
  have hc : ∀ s : P, ψ (e s) * (e s)⁻¹ ∈ Subgroup.center Tc ↔ φ s * s⁻¹ ∈ Subgroup.center P := by
    intro s
    rw [hψ, ← map_inv, ← map_mul, ← mem_center_equiv_iff e]
  have hc3 : ∀ s : P, ψ (ψ (ψ (e s))) * (e s)⁻¹ ∈ Subgroup.center Tc ↔
      φ (φ (φ s)) * s⁻¹ ∈ Subgroup.center P := by
    intro s
    rw [hψ, hψ, hψ, ← map_inv, ← map_mul, ← mem_center_equiv_iff e]
  rcases key with h | ⟨h1, h2⟩
  · left
    intro s
    exact (hc s).1 (h (e s))
  · right
    refine ⟨fun s hs => ?_, fun s => (hc3 s).1 (h2 (e s))⟩
    exact (mem_center_equiv_iff e s).2 (h1 (e s) ((hc s).2 hs))

end Equiv


section Ambient

variable {G : Type*} [Group G]

@[expose] def conjEquiv (S : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    S ≃* S where
  toFun s := ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg s).1 s.2⟩
  invFun s := ⟨g⁻¹ * s * g, (Subgroup.mem_normalizer_iff.1 hg _).2 (by
    rw [show g * (g⁻¹ * (s : G) * g) * g⁻¹ = s by group]
    exact s.2)⟩
  left_inv s := Subtype.ext (by simp [mul_assoc])
  right_inv s := Subtype.ext (by simp [mul_assoc])
  map_mul' s t := Subtype.ext (by simp [mul_assoc])

theorem coe_conjEquiv (S : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (S : Set G))
    (s : S) : ((conjEquiv S hg s : S) : G) = g * s * g⁻¹ := rfl

theorem mem_map_subtype_iff {S : Subgroup G} {H : Subgroup S} {x : G} (hx : x ∈ S) :
    x ∈ H.map S.subtype ↔ (⟨x, hx⟩ : S) ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hh
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem coe_mem_zpowers_iff {S : Subgroup G} (z x : S) :
    (x : G) ∈ Subgroup.zpowers (z : G) ↔ x ∈ Subgroup.zpowers z := by
  have h : (Subgroup.zpowers z).map S.subtype = Subgroup.zpowers (z : G) :=
    MonoidHom.map_zpowers S.subtype z
  rw [← h]
  exact Subgroup.mem_map_iff_mem S.subtype_injective


theorem IsT.exists_tAmbient {S : Subgroup G} (hS : IsT S) :
    ∃ Z A B : Subgroup G, TAmbient S Z A B := by
  obtain ⟨e⟩ := hS.nonempty_equiv
  have hAB := isTwoE16_of_equiv e
  set A' : Subgroup S := A.comap e.toMonoidHom with hA'
  set B' : Subgroup S := B.comap e.toMonoidHom with hB'
  have := hAB.normal_left
  have := hAB.normal_right
  have hmemA' : ∀ x : S, x ∈ A' ↔ (e x).b = 0 := fun x => Iff.rfl
  have hmemB' : ∀ x : S, x ∈ B' ↔ (e x).a = 0 := fun x => Iff.rfl
  refine ⟨(Subgroup.center S).map S.subtype, A'.map S.subtype, B'.map S.subtype, ?_⟩
  have hZmem : ∀ g : G, g ∈ (Subgroup.center S).map S.subtype ↔
      g ∈ S ∧ ∀ s ∈ S, g * s = s * g := by
    intro g
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, fun s hs => ?_⟩
      have := Subgroup.mem_center_iff.1 hz ⟨s, hs⟩
      exact (congrArg Subtype.val this).symm
    · rintro ⟨hg, hcomm⟩
      exact ⟨⟨g, hg⟩, Subgroup.mem_center_iff.2 fun s => Subtype.ext (hcomm s s.2).symm, rfl⟩
  have hZsq : ∀ z ∈ (Subgroup.center S).map S.subtype, z * z = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    exact congrArg Subtype.val (IsT.sq_eq_one_of_mem_center hS hz)
  have hcentA : ∀ a ∈ A'.map S.subtype, a ∉ (Subgroup.center S).map S.subtype →
      ∀ s ∈ S, s * a = a * s → s ∈ A'.map S.subtype := by
    rintro _ ⟨a, ha, rfl⟩ haZ s hs hsa
    have haZ' : a ∉ Subgroup.center S := fun h => haZ ⟨a, h, rfl⟩
    have hc := hAB.centralizer_left a ha haZ'
    have hmem : (⟨s, hs⟩ : S) ∈ Subgroup.centralizer ({a} : Set S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hsa
    rw [hc] at hmem
    exact ⟨⟨s, hs⟩, hmem, rfl⟩
  have hcentB : ∀ b ∈ B'.map S.subtype, b ∉ (Subgroup.center S).map S.subtype →
      ∀ s ∈ S, s * b = b * s → s ∈ B'.map S.subtype := by
    rintro _ ⟨b, hb, rfl⟩ hbZ s hs hsb
    have hbZ' : b ∉ Subgroup.center S := fun h => hbZ ⟨b, h, rfl⟩
    have hc := hAB.centralizer_right b hb hbZ'
    have hmem : (⟨s, hs⟩ : S) ∈ Subgroup.centralizer ({b} : Set S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hsb
    rw [hc] at hmem
    exact ⟨⟨s, hs⟩, hmem, rfl⟩
  refine
    { Z_le_A := Subgroup.map_mono ((le_of_eq hAB.inf_eq.symm).trans inf_le_left)
      Z_le_B := Subgroup.map_mono ((le_of_eq hAB.inf_eq.symm).trans inf_le_right)
      A_le_S := Subgroup.map_subtype_le _
      B_le_S := Subgroup.map_subtype_le _
      card_S := IsT.card_eq hS
      card_Z := (Subgroup.card_map_of_injective S.subtype_injective).trans
        (IsT.card_center hS)
      card_A := (Subgroup.card_map_of_injective S.subtype_injective).trans hAB.card_left
      card_B := (Subgroup.card_map_of_injective S.subtype_injective).trans hAB.card_right
      A_ne_B := fun h => hAB.ne (Subgroup.map_injective S.subtype_injective h)
      mem_Z := hZmem
      Z_sq := hZsq
      comm_mem_Z := fun x hx y hy => ⟨⁅(⟨x, hx⟩ : S), ⟨y, hy⟩⁆,
        IsT.commutator_mem_center hS _ _, rfl⟩
      sq_mem_Z := fun x hx => ⟨(⟨x, hx⟩ : S) * ⟨x, hx⟩, IsT.sq_mem_center hS _, rfl⟩
      A_abel := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (hAB.comm_left a ha b hb)
      B_abel := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (hAB.comm_right a ha b hb)
      A_sq := by
        rintro _ ⟨a, ha, rfl⟩
        exact congrArg Subtype.val (hAB.sq_left a ha)
      B_sq := by
        rintro _ ⟨a, ha, rfl⟩
        exact congrArg Subtype.val (hAB.sq_right a ha)
      AB_le_Z := by
        rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
        have : b = a := Subtype.ext hba
        subst this
        refine ⟨b, ?_, rfl⟩
        rw [← hAB.inf_eq]
        exact ⟨ha, hb⟩
      A_norm := by
        rintro s hs _ ⟨a, ha, rfl⟩
        exact ⟨(⟨s, hs⟩ : S) * a * (⟨s, hs⟩ : S)⁻¹, hAB.normal_left.conj_mem a ha _, rfl⟩
      B_norm := by
        rintro s hs _ ⟨a, ha, rfl⟩
        exact ⟨(⟨s, hs⟩ : S) * a * (⟨s, hs⟩ : S)⁻¹, hAB.normal_right.conj_mem a ha _, rfl⟩
      invol := by
        intro x hx hsq
        rcases (hAB.sq_iff ⟨x, hx⟩).1 (Subtype.ext hsq) with h | h
        · exact Or.inl ⟨_, h, rfl⟩
        · exact Or.inr ⟨_, h, rfl⟩
      cent_A := hcentA
      cent_B := hcentB
      cent_not_A := by
        intro s hs hsA a ha hcomm
        by_contra haZ
        exact hsA (hcentA a ha haZ s hs hcomm.symm)
      cent_not_B := by
        intro s hs hsB b hb hcomm
        by_contra hbZ
        exact hsB (hcentB b hb hbZ s hs hcomm.symm)
      normal_dich := by
        intro N hNS hNinv
        have hN' : (N.subgroupOf S).Normal := ⟨fun n hn t => by
          rw [Subgroup.mem_subgroupOf] at hn ⊢
          exact hNinv t t.2 n hn⟩
        rcases IsT.normal_dichotomy hS hN' with h | h
        · left
          intro n hn
          exact ⟨_, h (Subgroup.mem_subgroupOf.2 hn : (⟨n, hNS hn⟩ : S) ∈ N.subgroupOf S), rfl⟩
        · right
          rintro _ ⟨z, hz, rfl⟩
          exact Subgroup.mem_subgroupOf.1 (h hz)
      elemAb_le := by
        intro E hES hsq _
        have hE' : ∀ x ∈ E.subgroupOf S, x * x = 1 := fun x hx => Subtype.ext (hsq x hx)
        rcases hAB.le_or (E.subgroupOf S) hE' with h | h
        · left
          intro x hx
          exact ⟨⟨x, hES hx⟩, h (Subgroup.mem_subgroupOf.2 hx), rfl⟩
        · right
          intro x hx
          exact ⟨⟨x, hES hx⟩, h (Subgroup.mem_subgroupOf.2 hx), rfl⟩
      extremal := by
        rintro _ ⟨z, hz, rfl⟩ hz1 a ha haZ
        have haZ' : (⟨a, ha⟩ : S) ∉ Subgroup.center S := fun h => haZ ⟨_, h, rfl⟩
        have hz1' : z ≠ 1 := fun h => hz1 (by rw [h]; rfl)
        obtain ⟨s, t, h1, h2, h3⟩ := extremal_of_equiv e hz hz1' haZ'
        refine ⟨s, s.2, t, t.2, ?_, ?_, ?_⟩
        · exact (coe_mem_zpowers_iff z ⁅s, (⟨a, ha⟩ : S)⁆).2 h1
        · exact (coe_mem_zpowers_iff z ⁅t, (⟨a, ha⟩ : S)⁆).2 h2
        · intro h
          exact h3 ((coe_mem_zpowers_iff z ⁅s, t⁆).1 h)
      diag := by
        intro g hg hZg hAg hBg
        have hZ' : ∀ z ∈ Subgroup.center S, conjEquiv S hg z = z := by
          intro z hz
          apply Subtype.ext
          rw [coe_conjEquiv]
          exact hZg z ⟨z, hz, rfl⟩
        have hA'' : ∀ x : S, (e x).b = 0 → (e (conjEquiv S hg x)).b = 0 := by
          intro x hx
          have hxA : (x : G) ∈ A'.map S.subtype := ⟨x, hx, rfl⟩
          have h2 : conjEquiv S hg x ∈ A' :=
            (mem_map_subtype_iff (conjEquiv S hg x).2).1 (hAg x hxA)
          exact h2
        have hB'' : ∀ x : S, (e x).a = 0 → (e (conjEquiv S hg x)).a = 0 := by
          intro x hx
          have hxB : (x : G) ∈ B'.map S.subtype := ⟨x, hx, rfl⟩
          have h2 : conjEquiv S hg x ∈ B' :=
            (mem_map_subtype_iff (conjEquiv S hg x).2).1 (hBg x hxB)
          exact h2
        rcases diag_of_equiv e (conjEquiv S hg) hZ' hA'' hB'' with h | ⟨h1, h2⟩
        · left
          intro s hs
          exact ⟨_, h ⟨s, hs⟩, rfl⟩
        · right
          refine ⟨fun s hs hsZ => ?_, fun s hs => ?_⟩
          · have hc : conjEquiv S hg ⟨s, hs⟩ * (⟨s, hs⟩ : S)⁻¹ ∈ Subgroup.center S :=
              (mem_map_subtype_iff (conjEquiv S hg ⟨s, hs⟩ * (⟨s, hs⟩ : S)⁻¹).2).1 hsZ
            exact ⟨_, h1 _ hc, rfl⟩
          · have heq : g ^ 3 * s * (g ^ 3)⁻¹ * s⁻¹ = ((conjEquiv S hg (conjEquiv S hg
                (conjEquiv S hg ⟨s, hs⟩)) * (⟨s, hs⟩ : S)⁻¹ : S) : G) := by
              have h3 : g ^ 3 = g * g * g := by rw [pow_succ, pow_two]
              simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjEquiv]
              rw [h3]
              group
            rw [heq]
            exact ⟨_, h2 ⟨s, hs⟩, rfl⟩ }

end Ambient

end CFSG.OddStandard.ThmC.T
