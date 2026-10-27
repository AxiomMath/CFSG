module

public import CFSG.Certificates.Kernel.PermCent.SylowReps

public section

namespace CFSG.KC.Tits8074

open Subgroup

section Group

variable {X : Type*} [Group X] [Finite X]

theorem conj_of_center {p : ℕ} [Fact p.Prime] {S : Subgroup X}
    (hS : Nat.card S = p ^ (Nat.card X).factorization p) {z : X} (hzS : z ∈ S) (hz1 : z ≠ 1)
    (hzc : ∀ t ∈ S, z * t = t * z) (hZ : ∀ c ∈ S, (∀ t ∈ S, c * t = t * c) → c = 1 ∨ c = z)
    (σ : MulAut X) : IsConj z (σ z) := by
  let K : Subgroup X := S.map σ.toMonoidHom
  have hK : Nat.card K = Nat.card S := Subgroup.card_map_of_injective σ.injective
  have hKp : IsPGroup p K := IsPGroup.of_card (hK.trans hS)
  obtain ⟨Q, hQ⟩ := hKp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X (Sylow.ofCard S hS) Q
  have hKQ : K = Q := Subgroup.eq_of_le_of_card_ge hQ (by rw [Sylow.card_eq_multiplicity, hK, hS])
  have hmemQ : ∀ x : X, x ∈ (Q : Subgroup X) ↔ g⁻¹ * x * g ∈ S := by
    intro x
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Sylow.coe_ofCard]
    have e : (MulAut.conj g)⁻¹ • x = g⁻¹ * x * g := by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]
    rw [e]
  have hσz : σ z ∈ (Q : Subgroup X) := by
    rw [← hKQ]
    exact ⟨z, hzS, rfl⟩
  have hyS : g⁻¹ * σ z * g ∈ S := (hmemQ _).1 hσz
  have hyc : ∀ t ∈ S, g⁻¹ * σ z * g * t = t * (g⁻¹ * σ z * g) := by
    intro t ht
    have ht' : g * t * g⁻¹ ∈ K := by
      rw [hKQ, hmemQ]
      simpa [mul_assoc] using ht
    obtain ⟨t', ht'S, e⟩ := ht'
    change σ t' = g * t * g⁻¹ at e
    have e2 : σ z * σ t' = σ t' * σ z := by rw [← map_mul, ← map_mul, hzc t' ht'S]
    rw [e] at e2
    calc g⁻¹ * σ z * g * t = g⁻¹ * (σ z * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * σ z) * g := by rw [e2]
      _ = t * (g⁻¹ * σ z * g) := by group
  rcases hZ _ hyS hyc with h | h
  · have h1 : σ z = 1 := by
      have := congrArg (fun y => g * y * g⁻¹) h
      simpa [mul_assoc] using this
    exact absurd (σ.injective (h1.trans (map_one σ).symm)) hz1
  · refine isConj_iff.2 ⟨g, ?_⟩
    calc g * z * g⁻¹ = g * (g⁻¹ * σ z * g) * g⁻¹ := by rw [h]
      _ = σ z := by group

theorem conj_of_sylow {T : Subgroup X} {k m : ℕ} (hT : Nat.card T = 3 ^ k)
    (hX : Nat.card X = 3 ^ k * m) (hm : ¬ 3 ∣ m) {b : X} (hTb : ∀ x ∈ T, x = 1 ∨ IsConj b x)
    (hb : b ^ (3 ^ k) = 1) (hb1 : b ≠ 1) (σ : MulAut X) : IsConj b (σ b) := by
  have hΦ : ∀ g ∈ (⊤ : Subgroup X), ∀ x ∈ (⊤ : Subgroup X),
      (fun y => y = 1 ∨ IsConj b y) (g * x * g⁻¹) → (fun y => y = 1 ∨ IsConj b y) x := by
    rintro g - x - (h | h)
    · left
      have := congrArg (fun y => g⁻¹ * y * g) h
      simpa [mul_assoc] using this
    · right
      exact h.trans (isConj_iff.2 ⟨g⁻¹, by group⟩)
  have h := CFSG.KC.SylowReps.forall_of_sylow ⊤ T Nat.prime_three le_top hT
    (by rw [Subgroup.card_top]; exact hX) hm (fun y => y = 1 ∨ IsConj b y) hΦ hTb (σ b)
    (mem_top _) (by rw [← map_pow, hb, map_one])
  rcases h with h | h
  · exact absurd (σ.injective (h.trans (map_one σ).symm)) hb1
  · exact h

theorem mulAut_card_mul_le {a b z : X} (hgen : closure ({a, b} : Set X) = ⊤) (haz : IsConj z a)
    (hbσ : ∀ σ : MulAut X, IsConj b (σ b)) (hzσ : ∀ σ : MulAut X, IsConj z (σ z))
    (hab : (a * b) ^ 13 = 1) {H : Subgroup X} (hH : ∀ x ∈ H, x * b = b * x) :
    Nat.card (MulAut X) * Nat.card H ≤
      {x : X | IsConj z x ∧ (x * b) ^ 13 = 1}.ncard * Nat.card X := by
  classical
  let B : Set X := {y | IsConj b y}
  let Y : Set X := {x | IsConj z x ∧ (x * b) ^ 13 = 1}
  have hch : ∀ y : B, ∃ h : X, h * b * h⁻¹ = y := fun y => isConj_iff.1 y.2
  let ch : B → X := fun y => (hch y).choose
  have hchs : ∀ y : B, ch y * b * (ch y)⁻¹ = y := fun y => (hch y).choose_spec
  have hY : ∀ σ : MulAut X, (ch ⟨σ b, hbσ σ⟩)⁻¹ * σ a * ch ⟨σ b, hbσ σ⟩ ∈ Y := by
    intro σ
    set h := ch ⟨σ b, hbσ σ⟩
    have hh : h * b * h⁻¹ = σ b := hchs ⟨σ b, hbσ σ⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨c, hc⟩ := isConj_iff.1 haz
      have h1 : IsConj (σ z) (σ a) :=
        isConj_iff.2 ⟨σ c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩
      exact (hzσ σ).trans (h1.trans (isConj_iff.2 ⟨h⁻¹, by group⟩))
    · have e : h⁻¹ * σ a * h * b = h⁻¹ * σ (a * b) * h⁻¹⁻¹ := by
        rw [map_mul, ← hh]
        group
      rw [e, conj_pow, ← map_pow, hab, map_one]
      group
  let F : MulAut X → B × Y := fun σ =>
    (⟨σ b, hbσ σ⟩, ⟨(ch ⟨σ b, hbσ σ⟩)⁻¹ * σ a * ch ⟨σ b, hbσ σ⟩, hY σ⟩)
  have hF : Function.Injective F := by
    intro σ τ e
    simp only [F, Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    have e2' := congrArg Subtype.val e2
    simp only at e2'
    rw [e1] at e2'
    have ea : σ a = τ a := by
      have := congrArg (fun y => ch ⟨τ b, hbσ τ⟩ * y * (ch ⟨τ b, hbσ τ⟩)⁻¹) e2'
      simpa [mul_assoc] using this
    have eb : σ b = τ b := congrArg Subtype.val e1
    have hm : σ.toMonoidHom = τ.toMonoidHom := by
      refine MonoidHom.eq_of_eqOn_dense hgen ?_
      intro x hx
      rcases hx with rfl | rfl
      · exact ea
      · exact eb
    exact MulEquiv.ext fun x => DFunLike.congr_fun hm x
  have hcard : Nat.card (MulAut X) ≤ Nat.card B * Nat.card Y := by
    rw [← Nat.card_prod]
    exact Nat.card_le_card_of_injective F hF
  have hB : B.ncard * Nat.card (centralizer ({b} : Set X)) = Nat.card X := by
    have hset : conjugatesOf b = B := rfl
    rw [← hset, ← Subgroup.index_centralizer_eq_ncard, Subgroup.index_mul_card]
  have hHC : Nat.card H ≤ Nat.card (centralizer ({b} : Set X)) := by
    refine Subgroup.card_le_of_le fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hH x hx
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hcard
  calc Nat.card (MulAut X) * Nat.card H
      ≤ (B.ncard * Y.ncard) * Nat.card (centralizer ({b} : Set X)) := Nat.mul_le_mul hcard hHC
    _ = Y.ncard * Nat.card X := by rw [← hB]; ring

end Group

theorem mulAut_card_mul_le_of_le {G : Type*} [Group G] (A : Subgroup G) [Finite A] {a b z : G}
    (ha : a ∈ A) (hb : b ∈ A) (hz : z ∈ A) (hgen : A = closure ({a, b} : Set G))
    (S : Subgroup G) (hSA : S ≤ A) (hS : Nat.card S = 2 ^ (Nat.card A).factorization 2)
    (hzS : z ∈ S) (hz1 : z ≠ 1) (hzc : ∀ t ∈ S, z * t = t * z)
    (hZ : ∀ c ∈ S, (∀ t ∈ S, c * t = t * c) → c = 1 ∨ c = z)
    (haz : ∃ g ∈ A, g * z * g⁻¹ = a)
    (T : Subgroup G) (hTA : T ≤ A) {k m : ℕ} (hT : Nat.card T = 3 ^ k)
    (hA : Nat.card A = 3 ^ k * m) (hm : ¬ 3 ∣ m)
    (hTb : ∀ x ∈ T, x = 1 ∨ ∃ g ∈ A, g * b * g⁻¹ = x) (hb3 : b ^ (3 ^ k) = 1) (hb1 : b ≠ 1)
    (H : Subgroup G) (hHA : H ≤ A) (hHb : ∀ x ∈ H, x * b = b * x) (hab : (a * b) ^ 13 = 1) :
    Nat.card (MulAut A) * Nat.card H ≤
      {x : G | (∃ g ∈ A, g * z * g⁻¹ = x) ∧ (x * b) ^ 13 = 1}.ncard * Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a' : A := ⟨a, ha⟩
  let b' : A := ⟨b, hb⟩
  let z' : A := ⟨z, hz⟩
  have hgen' : closure ({a', b'} : Set A) = ⊤ := by
    subst hgen
    refine Eq.trans ?_ (Subgroup.closure_closure_coe_preimage (k := {a, b}))
    congr 1
    ext ⟨g, hg⟩
    simp [a', b', Subtype.ext_iff]
  have hcardS : Nat.card (S.subgroupOf A) = Nat.card S :=
    Nat.card_congr (subgroupOfEquivOfLe hSA).toEquiv
  have hcardT : Nat.card (T.subgroupOf A) = Nat.card T :=
    Nat.card_congr (subgroupOfEquivOfLe hTA).toEquiv
  have hcardH : Nat.card (H.subgroupOf A) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hHA).toEquiv
  have hzσ : ∀ σ : MulAut A, IsConj z' (σ z') := by
    refine conj_of_center (p := 2) (S := S.subgroupOf A) (hcardS.trans hS)
      (Subgroup.mem_subgroupOf.2 hzS) (fun h => hz1 (congrArg Subtype.val h)) ?_ ?_
    · intro t ht
      exact Subtype.ext (hzc t (Subgroup.mem_subgroupOf.1 ht))
    · intro c hc hcc
      rcases hZ c (Subgroup.mem_subgroupOf.1 hc) (fun t ht =>
        congrArg Subtype.val (hcc ⟨t, hSA ht⟩ (Subgroup.mem_subgroupOf.2 ht))) with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  have hbσ : ∀ σ : MulAut A, IsConj b' (σ b') := by
    refine conj_of_sylow (T := T.subgroupOf A) (hcardT.trans hT) hA hm ?_
      (Subtype.ext (by simpa using hb3)) (fun h => hb1 (congrArg Subtype.val h))
    intro x hx
    rcases hTb x (Subgroup.mem_subgroupOf.1 hx) with h | ⟨g, hg, e⟩
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext (by simpa using e)⟩)
  have haz' : IsConj z' a' := by
    obtain ⟨g, hg, e⟩ := haz
    exact isConj_iff.2 ⟨⟨g, hg⟩, Subtype.ext (by simpa using e)⟩
  have h := mulAut_card_mul_le hgen' haz' hbσ hzσ (Subtype.ext (by simpa using hab))
    (H := H.subgroupOf A) (fun x hx => Subtype.ext (hHb x (Subgroup.mem_subgroupOf.1 hx)))
  rw [hcardH] at h
  refine h.trans (Nat.mul_le_mul_right _ ?_)
  have himg : Subtype.val '' {x : A | IsConj z' x ∧ (x * b') ^ 13 = 1} ⊆
      {x : G | (∃ g ∈ A, g * z * g⁻¹ = x) ∧ (x * b) ^ 13 = 1} := by
    rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
    obtain ⟨g, e⟩ := isConj_iff.1 hx1
    refine ⟨⟨g, g.2, by simpa using congrArg Subtype.val e⟩, ?_⟩
    simpa using congrArg Subtype.val hx2
  have hfin : {x : G | (∃ g ∈ A, g * z * g⁻¹ = x) ∧ (x * b) ^ 13 = 1}.Finite := by
    refine (Set.toFinite (A : Set G)).subset ?_
    rintro _ ⟨⟨g, hg, rfl⟩, -⟩
    exact A.mul_mem (A.mul_mem hg hz) (A.inv_mem hg)
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  exact Set.ncard_le_ncard himg hfin

end CFSG.KC.Tits8074

end
