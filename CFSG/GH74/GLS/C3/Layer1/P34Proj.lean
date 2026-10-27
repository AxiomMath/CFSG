module

public import CFSG.GH74.GLS.C3.Layer1.P34Cfg

public section

namespace CFSG.GH74.GLS.C3.Layer1.P34

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X]

theorem W_le_normalizer_of {Q W : Subgroup X} (hQW : ∀ w ∈ W, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q) :
    W ≤ normalizer (Q : Set X) := fun w hw => by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha; exact hQW w hw a ha
  · intro ha
    have := hQW w⁻¹ (W.inv_mem hw) _ ha
    simpa [mul_assoc] using this

theorem exists_retraction {Q W : Subgroup X}
    (hQW : ∀ w ∈ W, ∀ q ∈ Q, w * q * w⁻¹ ∈ Q) (hinf : Q ⊓ W = ⊥) :
    ∃ π : ↥(Q ⊔ W) →* X, (∀ y, π y ∈ W) ∧ (∀ y : ↥(Q ⊔ W), (y : X) ∈ W → π y = (y : X)) ∧
      (∀ y : ↥(Q ⊔ W), π y = 1 ↔ (y : X) ∈ Q) ∧ (∀ y : ↥(Q ⊔ W), (π y)⁻¹ * (y : X) ∈ Q) := by
  have hWN : W ≤ normalizer (Q : Set X) := W_le_normalizer_of hQW
  set M : Subgroup X := Q ⊔ W with hM
  have hWM : W ≤ M := le_sup_right
  have hQM : Q ≤ M := le_sup_left
  have hMN : M ≤ normalizer (Q : Set X) := sup_le le_normalizer hWN
  have hnormal : (Q.subgroupOf M).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.1 (hMN g.2) (n : X)).1 hn
    simpa using this⟩
  let φ₀ : ↥W →* ↥M ⧸ Q.subgroupOf M :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hWM)
  have hinj : Function.Injective φ₀ := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : ((Subgroup.inclusion hWM w : ↥M) : X) ∈ Q := by
      have := (QuotientGroup.eq_one_iff _).1 hw
      exact (Subgroup.mem_subgroupOf.1 this)
    have h2 : (w : X) ∈ Q ⊓ W := ⟨h1, w.2⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hsurj : Function.Surjective φ₀ := by
    intro y
    induction y using QuotientGroup.induction_on with | H y => ?_
    have hy : (y : X) ∈ ((Q ⊔ W : Subgroup X) : Set X) := y.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Q W hWN] at hy
    obtain ⟨q, hq, w, hw, hqw⟩ := hy
    refine ⟨⟨w, hw⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hWM ⟨w, hw⟩) : ↥M ⧸ Q.subgroupOf M) =
      QuotientGroup.mk y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    show (w : X)⁻¹ * (y : X) ∈ Q
    have e : (w : X)⁻¹ * (y : X) = w⁻¹ * q * w := by
      have hqw' : q * w = (y : X) := hqw
      rw [← hqw']; group
    rw [e]
    have := hQW w⁻¹ (W.inv_mem hw) q hq
    simpa using this
  let e : ↥W ≃* (↥M ⧸ Q.subgroupOf M) := MulEquiv.ofBijective φ₀ ⟨hinj, hsurj⟩
  let π : ↥M →* X := W.subtype.comp (e.symm.toMonoidHom.comp (QuotientGroup.mk' (Q.subgroupOf M)))
  have hπy : ∀ y : ↥M, π y = ((e.symm (QuotientGroup.mk y) : ↥W) : X) := fun y => rfl
  refine ⟨π, fun y => ?_, fun y hy => ?_, fun y => ?_, fun y => ?_⟩
  · rw [hπy]; exact (e.symm (QuotientGroup.mk y)).2
  · rw [hπy]
    have : (QuotientGroup.mk y : ↥M ⧸ Q.subgroupOf M) = e ⟨(y : X), hy⟩ := rfl
    rw [this, MulEquiv.symm_apply_apply]
  · rw [hπy]
    constructor
    · intro h1
      have h2 : e.symm (QuotientGroup.mk y) = 1 := Subtype.ext h1
      have h3 : (QuotientGroup.mk y : ↥M ⧸ Q.subgroupOf M) = 1 := by
        have := congrArg e h2
        simpa using this
      exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h3)
    · intro h1
      have h3 : (QuotientGroup.mk y : ↥M ⧸ Q.subgroupOf M) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 h1)
      rw [h3, map_one]
      rfl
  · rw [hπy]
    set w := e.symm (QuotientGroup.mk y) with hw
    have h1 : φ₀ w = QuotientGroup.mk y := by
      have := e.apply_symm_apply (QuotientGroup.mk y)
      exact this
    have h2 : (QuotientGroup.mk (Subgroup.inclusion hWM w) : ↥M ⧸ Q.subgroupOf M) =
        QuotientGroup.mk y := h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
    exact h2

theorem card_mul_inf [Finite X] (A B : Subgroup X) :
    Nat.card ↥((A : Set X) * (B : Set X)) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have h1 := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient B (A : Set X)
  have himg : Nat.card ↥((A : Set X).image ((↑) : X → X ⧸ B)) = B.relIndex A := by
    have horb : MulAction.orbit ↥A ((1 : X) : X ⧸ B) = (A : Set X).image ((↑) : X → X ⧸ B) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨(a : X), a.2, by simp [Subgroup.smul_def]⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, by simp [Subgroup.smul_def]⟩
    have hstab : MulAction.stabilizer ↥A ((1 : X) : X ⧸ B) = B.subgroupOf A := by
      ext a
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
      have : (a • ((1 : X) : X ⧸ B)) = ((a : X) : X ⧸ B) := by
        simp [Subgroup.smul_def]
      rw [this, QuotientGroup.eq]
      constructor
      · intro h
        have := B.inv_mem h
        simpa using this
      · intro h
        have := B.inv_mem h
        simpa using this
    have := MulAction.index_stabilizer ↥A ((1 : X) : X ⧸ B)
    rw [hstab] at this
    rw [← horb, Nat.card_coe_set_eq, ← this]
    rfl
  have h2 := Subgroup.relIndex_mul_card (H := B) (K := A)
  rw [inf_comm B A] at h2
  rw [h1, himg]
  calc Nat.card ↥B * B.relIndex A * Nat.card ↥(A ⊓ B)
      = Nat.card ↥B * (B.relIndex A * Nat.card ↥(A ⊓ B)) := by ring
    _ = Nat.card ↥A * Nat.card ↥B := by rw [h2]; ring

theorem IsDihedralGE8.of_equiv {A B : Subgroup X} (hB : IsDihedralGE8 B) (e : ↥A ≃* ↥B) :
    IsDihedralGE8 A := by
  obtain ⟨n, hn, ⟨f⟩⟩ := hB
  exact ⟨n, hn, ⟨e.trans f⟩⟩

@[expose] def Aof {M : Subgroup X} (π : ↥M →* X) (B : Subgroup X) : Subgroup X :=
  (π.comp (B.subgroupOf M).subtype).range

theorem mem_Aof {M B : Subgroup X} {π : ↥M →* X} {y : X} :
    y ∈ Aof π B ↔ ∃ b : ↥M, (b : X) ∈ B ∧ π b = y := by
  unfold Aof
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨(b : ↥M), Subgroup.mem_subgroupOf.1 b.2, hb⟩
  · rintro ⟨b, hb, hy⟩
    exact ⟨⟨b, Subgroup.mem_subgroupOf.2 hb⟩, hy⟩

theorem Aof_mono {M B B' : Subgroup X} {π : ↥M →* X} (h : B ≤ B') : Aof π B ≤ Aof π B' := by
  intro y hy
  obtain ⟨b, hb, rfl⟩ := mem_Aof.1 hy
  exact mem_Aof.2 ⟨b, h hb, rfl⟩

theorem card_Aof_le [Finite X] {M B : Subgroup X} (π : ↥M →* X) (hBM : B ≤ M) :
    Nat.card ↥(Aof π B) ≤ Nat.card ↥B := by
  have h1 : Nat.card ↥(Aof π B) ≤ Nat.card ↥(B.subgroupOf M) := by
    unfold Aof
    exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have h2 : Nat.card ↥(B.subgroupOf M) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
  omega

theorem card_Aof_of_inj [Finite X] {M B : Subgroup X} (π : ↥M →* X) (hBM : B ≤ M)
    (hinj : ∀ y y' : ↥M, (y : X) ∈ B → (y' : X) ∈ B → π y = π y' → y = y') :
    Nat.card ↥(Aof π B) = Nat.card ↥B := by
  have hinj' : Function.Injective (π.comp (B.subgroupOf M).subtype) := by
    intro a b hab
    have := hinj a.1 b.1 (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2) hab
    exact Subtype.ext this
  have h1 : Nat.card ↥(Aof π B) = Nat.card ↥(B.subgroupOf M) := by
    unfold Aof
    exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm
  have h2 : Nat.card ↥(B.subgroupOf M) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
  omega

theorem isDihedralGE8_Aof [Finite X] {M B : Subgroup X} (π : ↥M →* X) (hBM : B ≤ M)
    (hinj : ∀ y y' : ↥M, (y : X) ∈ B → (y' : X) ∈ B → π y = π y' → y = y')
    (hB : IsDihedralGE8 B) : IsDihedralGE8 (Aof π B) := by
  have hinj' : Function.Injective (π.comp (B.subgroupOf M).subtype) := by
    intro a b hab
    have := hinj a.1 b.1 (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2) hab
    exact Subtype.ext this
  refine IsDihedralGE8.of_equiv hB ?_
  unfold Aof
  exact (MonoidHom.ofInjective hinj').symm.trans (Subgroup.subgroupOfEquivOfLe hBM)

theorem inj_of_card_Aof [Finite X] {M B : Subgroup X} (π : ↥M →* X) (hBM : B ≤ M)
    (hcard : Nat.card ↥(Aof π B) = Nat.card ↥B) :
    ∀ y y' : ↥M, (y : X) ∈ B → (y' : X) ∈ B → π y = π y' → y = y' := by
  intro y y' hy hy' hyy'
  have h2 : Nat.card ↥(B.subgroupOf M) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
  have hsurj : Function.Surjective ((π.comp (B.subgroupOf M).subtype).rangeRestrict) :=
    MonoidHom.rangeRestrict_surjective _
  have hbij : Function.Bijective ((π.comp (B.subgroupOf M).subtype).rangeRestrict) :=
    hsurj.bijective_of_nat_card_le (by
      show Nat.card ↥(B.subgroupOf M) ≤ Nat.card ↥(Aof π B)
      omega)
  have := hbij.1 (a₁ := ⟨y, Subgroup.mem_subgroupOf.2 hy⟩) (a₂ := ⟨y', Subgroup.mem_subgroupOf.2 hy'⟩)
    (Subtype.ext hyy')
  exact congrArg (fun a : ↥(B.subgroupOf M) => (a : ↥M)) this

theorem isDihedralGE8_conj {A : Subgroup X} (hA : IsDihedralGE8 A) (e : X) :
    IsDihedralGE8 (CFSG.Quasithin.conjSubgroup A e) :=
  IsDihedralGE8.of_equiv hA
    (Subgroup.equivMapOfInjective A (MulAut.conj e⁻¹).toMonoidHom (MulAut.conj e⁻¹).injective).symm

theorem conjSubgroup_sup (A B : Subgroup X) (e : X) :
    CFSG.Quasithin.conjSubgroup (A ⊔ B) e =
      CFSG.Quasithin.conjSubgroup A e ⊔ CFSG.Quasithin.conjSubgroup B e :=
  Subgroup.map_sup _ _ _

end CFSG.GH74.GLS.C3.Layer1.P34
