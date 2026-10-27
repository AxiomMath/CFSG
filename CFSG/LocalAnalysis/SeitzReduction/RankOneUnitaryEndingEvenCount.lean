module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingEvenAction
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingEvenFaithful
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingEvenField
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryEndingEvenCenter

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Counting

variable {G : Type*} [Group G]

theorem card_le_card_mul_card_of_fiber [Finite G] {S : Set G} {D : Subgroup G} {β : Type*}
    [Finite β] (π : G → β) (hπ : ∀ y ∈ S, ∀ y' ∈ S, π y = π y' → y⁻¹ * y' ∈ D) :
    Nat.card S ≤ Nat.card β * Nat.card D := by
  classical
  have hrep : ∀ b : β, ∃ r : G, (∃ y ∈ S, π y = b) → r ∈ S ∧ π r = b := by
    intro b
    by_cases hb : ∃ y ∈ S, π y = b
    · obtain ⟨y, hy, hyb⟩ := hb
      exact ⟨y, fun _ => ⟨hy, hyb⟩⟩
    · exact ⟨1, fun h => absurd h hb⟩
  choose r hr using hrep
  let F : S → β × D := fun y =>
    (π y, ⟨(r (π y))⁻¹ * y, by
      obtain ⟨h1, h2⟩ := hr (π y) ⟨y, y.2, rfl⟩
      exact hπ _ h1 _ y.2 h2⟩)
  have hF : Function.Injective F := by
    intro y y' h
    have h1 : π y = π y' := congrArg Prod.fst h
    have h2 : (r (π y))⁻¹ * (y : G) = (r (π y'))⁻¹ * y' := congrArg (fun p => (p.2 : G)) h
    rw [h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  calc Nat.card S ≤ Nat.card (β × D) := Nat.card_le_card_of_injective F hF
    _ = Nat.card β * Nat.card D := Nat.card_prod _ _

theorem card_mul_card_le_card_mul_card_inf [Finite G] {A Y U : Subgroup G} (hAU : A ≤ U)
    (hYU : Y ≤ U) : Nat.card A * Nat.card Y ≤ Nat.card U * Nat.card (Y ⊓ A : Subgroup G) := by
  have h1 := Y.relIndex_mul_card (K := A)
  have h2 := Y.relIndex_mul_card (K := U)
  have hYU' : Y ⊓ U = Y := inf_eq_left.mpr hYU
  rw [hYU'] at h2
  have hne : Y.relIndex U ≠ 0 := by
    show (Y.subgroupOf U).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have h3 : Y.relIndex A ≤ Y.relIndex U := relIndex_le_of_le_right hAU hne
  calc Nat.card A * Nat.card Y = Y.relIndex A * Nat.card (Y ⊓ A : Subgroup G) * Nat.card Y := by
        rw [h1]
    _ ≤ Y.relIndex U * Nat.card (Y ⊓ A : Subgroup G) * Nat.card Y := by gcongr
    _ = Nat.card U * Nat.card (Y ⊓ A : Subgroup G) := by rw [← h2]; ring

theorem card_le_card_mul_card_of_forall_eq_mul [Finite G] {A B C : Set G}
    (h : ∀ w ∈ C, ∃ a ∈ A, ∃ b ∈ B, w = a * b) : Nat.card C ≤ Nat.card A * Nat.card B := by
  classical
  have h' : ∀ w : C, ∃ p : A × B, (w : G) = p.1 * p.2 := fun w => by
    obtain ⟨a, ha, b, hb, e⟩ := h w w.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), e⟩
  choose F hF using h'
  have hinj : Function.Injective F := fun w w' e => Subtype.ext (by rw [hF w, hF w', e])
  calc Nat.card C ≤ Nat.card (A × B) := Nat.card_le_card_of_injective F hinj
    _ = Nat.card A * Nat.card B := Nat.card_prod _ _

end Counting

section Triv

variable {G : Type*} [Group G]

@[expose] def commCenterSubgroup (U : Subgroup G) (y : G) : Subgroup G where
  carrier := {w | w ∈ U ∧ y * w * y⁻¹ * w⁻¹ ∈ U ⊓ centralizer (U : Set G)}
  mul_mem' := by
    rintro w w' ⟨hw, h1⟩ ⟨hw', h2⟩
    refine ⟨mul_mem hw hw', ?_⟩
    have e : y * (w * w') * y⁻¹ * (w * w')⁻¹ =
        (y * w * y⁻¹ * w⁻¹) * (w * (y * w' * y⁻¹ * w'⁻¹) * w⁻¹) := by group
    have h3 : w * (y * w' * y⁻¹ * w'⁻¹) * w⁻¹ = y * w' * y⁻¹ * w'⁻¹ := by
      rw [mem_centralizer_iff.mp (mem_inf.mp h2).2 w hw, mul_inv_cancel_right]
    rw [e, h3]
    exact mul_mem h1 h2
  one_mem' := ⟨one_mem _, by
    rw [mul_one, mul_inv_cancel, inv_one, mul_one]
    exact one_mem _⟩
  inv_mem' := by
    rintro w ⟨hw, h1⟩
    refine ⟨inv_mem hw, ?_⟩
    have hz := inv_mem h1
    have e : y * w⁻¹ * y⁻¹ * w⁻¹⁻¹ = w⁻¹ * ((y * w * y⁻¹ * w⁻¹)⁻¹ * w) := by group
    rw [e, ← mem_centralizer_iff.mp (mem_inf.mp hz).2 w hw, inv_mul_cancel_left]
    exact hz

theorem commCenterSubgroup_le (U : Subgroup G) (y : G) : commCenterSubgroup U y ≤ U :=
  fun _ hw => hw.1

theorem forall_comm_mem_center_of_mul_left {U Y : Subgroup G} {y y' : G}
    (hy : y ∈ normalizer (U : Set G))
    (h : ∀ a ∈ Y, y * y' * a * (y * y')⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G))
    (h' : ∀ a ∈ Y, y' * a * y'⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G)) :
    ∀ a ∈ Y, y * a * y⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G) := by
  intro a ha
  have e : y * a * y⁻¹ * a⁻¹ =
      (y * (y' * a * y'⁻¹ * a⁻¹) * y⁻¹)⁻¹ * (y * y' * a * (y * y')⁻¹ * a⁻¹) := by group
  rw [e]
  exact mul_mem (inv_mem (conj_mem_center_of_mem_normalizer hy (h' a ha))) (h a ha)

theorem forall_comm_mem_center_of_mul_right {U Y : Subgroup G} {y y' : G}
    (hy : y ∈ normalizer (U : Set G))
    (h : ∀ a ∈ Y, y * y' * a * (y * y')⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G))
    (h' : ∀ a ∈ Y, y * a * y⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G)) :
    ∀ a ∈ Y, y' * a * y'⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G) := by
  intro a ha
  have e : y' * a * y'⁻¹ * a⁻¹ =
      y⁻¹ * ((y * y' * a * (y * y')⁻¹ * a⁻¹) * (y * a * y⁻¹ * a⁻¹)⁻¹) * y⁻¹⁻¹ := by group
  rw [e]
  exact conj_mem_center_of_mem_normalizer (inv_mem hy) (mul_mem (h a ha) (inv_mem (h' a ha)))

theorem mem_centralizerModCenter_of_forall {U Y₁ Y₂ : Subgroup G} (hY : Y₁ ⊔ Y₂ = U)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) {y : G} (hyU : y ∈ normalizer (U : Set G))
    (h₁ : ∀ a ∈ Y₁, y * a * y⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G))
    (h₂ : ∀ b ∈ Y₂, y * b * y⁻¹ * b⁻¹ ∈ U ⊓ centralizer (U : Set G)) :
    y ∈ centralizerModCenter U := by
  refine ⟨hyU, fun w hw => ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm (hY ▸ hw)
  have haU : a ∈ U := hY ▸ mem_sup_left ha
  have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
      (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
  have h3 : a * (y * b * y⁻¹ * b⁻¹) * a⁻¹ = y * b * y⁻¹ * b⁻¹ := by
    rw [mem_centralizer_iff.mp (mem_inf.mp (h₂ b hb)).2 a haU, mul_inv_cancel_right]
  rw [e, h3]
  exact mul_mem (h₁ a ha) (h₂ b hb)

theorem exists_mul_of_comm_mem_center {U Y₁ Y₂ : Subgroup G} (hY : Y₁ ⊔ Y₂ = U)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) {y : G}
    (hy₁ : y ∈ normalizer ((U ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G))
    (hy₂ : y ∈ normalizer ((U ⊓ centralizer (Y₁ : Set G) : Subgroup G) : Set G)) {w : G}
    (hw : w ∈ U) (h : y * w * y⁻¹ * w⁻¹ ∈ U ⊓ centralizer (U : Set G)) :
    ∃ a ∈ Y₁, ∃ b ∈ Y₂, w = a * b ∧ y * a * y⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G) ∧
      y * b * y⁻¹ * b⁻¹ ∈ U ⊓ centralizer (U : Set G) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_eq_of_mem_sup_of_commute hcomm (hY ▸ hw)
  have haU : a ∈ U := hY ▸ mem_sup_left ha
  have hbU : b ∈ U := hY ▸ mem_sup_right hb
  have haM : a ∈ U ⊓ centralizer (Y₂ : Set G) :=
    mem_inf.mpr ⟨haU, mem_centralizer_iff.mpr fun b' hb' => (hcomm a ha b' hb').symm⟩
  have hbM : b ∈ U ⊓ centralizer (Y₁ : Set G) :=
    mem_inf.mpr ⟨hbU, mem_centralizer_iff.mpr fun a' ha' => hcomm a' ha' b hb⟩
  have hm₁ : y * a * y⁻¹ * a⁻¹ ∈ U ⊓ centralizer (Y₂ : Set G) :=
    mul_mem ((mem_normalizer_iff.mp hy₁ a).mp haM) (inv_mem haM)
  have hm₂ : y * b * y⁻¹ * b⁻¹ ∈ U ⊓ centralizer (Y₁ : Set G) :=
    mul_mem ((mem_normalizer_iff.mp hy₂ b).mp hbM) (inv_mem hbM)
  have h3 : a * (y * b * y⁻¹ * b⁻¹) * a⁻¹ = y * b * y⁻¹ * b⁻¹ := by
    rw [mem_centralizer_iff.mp (mem_inf.mp hm₂).2 a ha, mul_inv_cancel_right]
  have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ = (y * a * y⁻¹ * a⁻¹) * (y * b * y⁻¹ * b⁻¹) := by
    rw [← h3]
    group
  rw [e] at h
  have hZM : ∀ z ∈ U ⊓ centralizer (U : Set G), z ∈ U ⊓ centralizer (Y₁ : Set G) := fun z hz =>
    mem_inf.mpr ⟨(mem_inf.mp hz).1, centralizer_le (show (Y₁ : Set G) ⊆ U from
      fun x hx => hY ▸ mem_sup_left hx) (mem_inf.mp hz).2⟩
  have h4 : y * a * y⁻¹ * a⁻¹ ∈ U ⊓ centralizer (Y₁ : Set G) := by
    have := mul_mem (hZM _ h) (inv_mem hm₂)
    rwa [mul_inv_cancel_right] at this
  have hcen : ∀ z ∈ U ⊓ centralizer (Y₂ : Set G), z ∈ U ⊓ centralizer (Y₁ : Set G) →
      z ∈ U ⊓ centralizer (U : Set G) := by
    intro z hz₂ hz₁
    refine mem_inf.mpr ⟨(mem_inf.mp hz₂).1, mem_centralizer_iff.mpr fun x hx => ?_⟩
    exact (commute_of_mem_sup_of_commute_factors hcomm
      (fun a' ha' => (mem_centralizer_iff.mp (mem_inf.mp hz₁).2 a' ha').symm)
      (fun b' hb' => (mem_centralizer_iff.mp (mem_inf.mp hz₂).2 b' hb').symm) (hY ▸ hx)).symm
  have h5 := hcen _ hm₁ h4
  refine ⟨a, ha, b, hb, rfl, h5, ?_⟩
  have := mul_mem (inv_mem h5) h
  rwa [inv_mul_cancel_left] at this

theorem mem_centralizer_of_comm_mem_center {U Y₁ Y₂ : Subgroup G} (hY : Y₁ ⊔ Y₂ = U)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) {y : G}
    (hsw : (U ⊓ centralizer (Y₂ : Set G)).map (MulAut.conj y).toMonoidHom =
      U ⊓ centralizer (Y₁ : Set G)) {a : G} (ha : a ∈ Y₁)
    (h : y * a * y⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G)) : a ∈ centralizer (Y₁ : Set G) := by
  have haU : a ∈ U := hY ▸ mem_sup_left ha
  have haM : a ∈ U ⊓ centralizer (Y₂ : Set G) :=
    mem_inf.mpr ⟨haU, mem_centralizer_iff.mpr fun b' hb' => (hcomm a ha b' hb').symm⟩
  have h1 : y * a * y⁻¹ ∈ U ⊓ centralizer (Y₁ : Set G) := by
    rw [← hsw]
    exact ⟨a, haM, by simp [MulAut.conj_apply]⟩
  refine mem_centralizer_iff.mpr fun c hc => ?_
  have hcU : c ∈ U := hY ▸ mem_sup_left hc
  have h2 : c * (y * a * y⁻¹) = (y * a * y⁻¹) * c := mem_centralizer_iff.mp (mem_inf.mp h1).2 c hc
  have h3 : c * (y * a * y⁻¹ * a⁻¹) = (y * a * y⁻¹ * a⁻¹) * c :=
    mem_centralizer_iff.mp (mem_inf.mp h).2 c hcU
  have e : y * a * y⁻¹ = (y * a * y⁻¹ * a⁻¹) * a := by group
  rw [e] at h2
  have h4 : (y * a * y⁻¹ * a⁻¹) * (c * a) = (y * a * y⁻¹ * a⁻¹) * (a * c) := by
    calc (y * a * y⁻¹ * a⁻¹) * (c * a) = ((y * a * y⁻¹ * a⁻¹) * c) * a := by group
      _ = (c * (y * a * y⁻¹ * a⁻¹)) * a := by rw [← h3]
      _ = c * (y * a * y⁻¹ * a⁻¹ * a) := by group
      _ = y * a * y⁻¹ * a⁻¹ * a * c := h2
      _ = (y * a * y⁻¹ * a⁻¹) * (a * c) := by group
  exact mul_left_cancel h4

end Triv

section Coords

variable {G : Type*} [Group G]

theorem forall_comm_mem_center_inv_mul_of_not {E : Type*} [Field E] [CharP E 2] [Finite E]
    {σ : E →+* E} {q : ℕ} (hσq : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2)
    (hF : Nat.card {x : E // σ x = x} = q) {U U' Y₁ Y₂ : Subgroup G} {u₁ v₁ : G → E}
    (hc₁ : U3RootCoords Y₁ σ u₁ v₁) (hY : Y₁ ⊔ Y₂ = U) (hinf : Y₁ ⊓ Y₂ = ⊥)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a)
    (hU'U : U' ≤ normalizer (U : Set G)) (hUU' : U ≤ normalizer (U' : Set G))
    (hinv : ∀ x ∈ U, x * x = 1 → x ∈ centralizer (U : Set G))
    (hsq : ∀ x ∈ U, x * x ∈ centralizer (U : Set G))
    (hU' : ∀ a ∈ U', ∀ b ∈ U', a * b * a⁻¹ * b⁻¹ * (a * b * a⁻¹ * b⁻¹) = 1)
    {y y' : G} (hy : y ∈ U') (hy' : y' ∈ U')
    (hyM : y ∈ normalizer ((U ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G))
    (hy'M : y' ∈ normalizer ((U ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G))
    (hnt : ¬ ∀ a ∈ Y₁, y * a * y⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G))
    (hnt' : ¬ ∀ a ∈ Y₁, y' * a * y'⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G)) :
    ∀ a ∈ Y₁, y⁻¹ * y' * a * (y⁻¹ * y')⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G) := by
  have hσσ := NormInvolution.sigma_sigma σ hσq hE
  obtain ⟨ω, hω⟩ := NormInvolution.exists_sigma_ne σ hE hF
  have hY₁U : Y₁ ≤ U := hY ▸ le_sup_left
  obtain ⟨φ, hφadd, hφφ, hφN, hφ⟩ := exists_isometry_of_mem_normalizer hσq hE hF hc₁ hY hinf
    hcomm (hU'U hy) hyM fun w hw => sq_comm_mem_center hU'U hUU' hinv hsq hU' hy hw
  obtain ⟨φ', hφ'add, -, hφ'N, hφ'⟩ := exists_isometry_of_mem_normalizer hσq hE hF hc₁ hY hinf
    hcomm (hU'U hy') hy'M fun w hw => sq_comm_mem_center hU'U hUU' hinv hsq hU' hy' hw
  have hne : ∃ x, φ x ≠ x := by
    by_contra hall
    push Not at hall
    exact hnt fun a ha => (hφ a ha a ha).mpr (hall (u₁ a)).symm
  have hne' : ∃ x, φ' x ≠ x := by
    by_contra hall
    push Not at hall
    exact hnt' fun a ha => (hφ' a ha a ha).mpr (hall (u₁ a)).symm
  have hfix : ∀ x, φ' (φ x + x) = φ x + x := by
    intro x
    obtain ⟨a, ha, rfl⟩ := hc₁.u_surj x
    obtain ⟨a', ha', ha'e⟩ := hc₁.u_surj (φ (u₁ a))
    have h1 : y * a * y⁻¹ * a'⁻¹ ∈ U ⊓ centralizer (U : Set G) := (hφ a ha a' ha').mpr ha'e
    have hcY : a' * a⁻¹ ∈ Y₁ := mul_mem ha' (inv_mem ha)
    have hcu : u₁ (a' * a⁻¹) = φ (u₁ a) + u₁ a := by
      rw [hc₁.mul_u _ ha' _ (inv_mem ha), hc₁.u_inv ha, ha'e, CharTwo.neg_eq]
    have h2 := comm_mem_center_of_mem_inf hU'U hinv hU' hy'
      (comm_mem_inf_of_mem hU'U hUU' hy (hY₁U ha))
    have h3 : y' * (a' * a⁻¹) * y'⁻¹ * (a' * a⁻¹)⁻¹ ∈ U ⊓ centralizer (U : Set G) := by
      have e : y' * (a' * a⁻¹) * y'⁻¹ * (a' * a⁻¹)⁻¹ =
          (y' * (y * a * y⁻¹ * a'⁻¹) * y'⁻¹)⁻¹ *
            (y' * (y * a * y⁻¹ * a⁻¹) * y'⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹) *
              (y * a * y⁻¹ * a'⁻¹) := by group
      rw [e]
      exact mul_mem (mul_mem (inv_mem (conj_mem_center_of_mem_normalizer (hU'U hy') h1)) h2) h1
    have h4 := (hφ' _ hcY _ hcY).mp h3
    rw [hcu] at h4
    exact h4.symm
  have heq := NormIsometry.eq_of_fixes_image σ hσσ hω hφadd hφ'add hφN hφ'N hφφ hfix hne hne'
  intro a ha
  obtain ⟨a', ha', ha'e⟩ := hc₁.u_surj (φ (u₁ a))
  have h1 := (hφ a ha a' ha').mpr ha'e
  have h2 := (hφ' a ha a' ha').mpr (by rw [ha'e, heq])
  have e : y⁻¹ * y' * a * (y⁻¹ * y')⁻¹ * a⁻¹ =
      y⁻¹ * ((y' * a * y'⁻¹ * a'⁻¹) * (y * a * y⁻¹ * a'⁻¹)⁻¹) * y⁻¹⁻¹ := by group
  rw [e]
  exact conj_mem_center_of_mem_normalizer (inv_mem (hU'U hy)) (mul_mem h2 (inv_mem h1))

theorem card_inf_commCenterSubgroup_le_of_not {E : Type*} [Field E] [CharP E 2] [Finite E]
    {σ : E →+* E} {q : ℕ} (hσq : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2)
    (hF : Nat.card {x : E // σ x = x} = q) {U Y₁ Y₂ : Subgroup G} {u₁ v₁ : G → E}
    (hc₁ : U3RootCoords Y₁ σ u₁ v₁) (hY : Y₁ ⊔ Y₂ = U) (hinf : Y₁ ⊓ Y₂ = ⊥)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) {y : G} (hyU : y ∈ normalizer (U : Set G))
    (hyM : y ∈ normalizer ((U ⊓ centralizer (Y₂ : Set G) : Subgroup G) : Set G))
    (hyy : ∀ w ∈ U, y * y * w * (y * y)⁻¹ * w⁻¹ ∈ U ⊓ centralizer (U : Set G))
    (hnt : ¬ ∀ a ∈ Y₁, y * a * y⁻¹ * a⁻¹ ∈ U ⊓ centralizer (U : Set G)) :
    Nat.card (Y₁ ⊓ commCenterSubgroup U y : Subgroup G) ≤ q * q := by
  have hσσ := NormInvolution.sigma_sigma σ hσq hE
  obtain ⟨φ, hφadd, -, hφN, hφ⟩ :=
    exists_isometry_of_mem_normalizer hσq hE hF hc₁ hY hinf hcomm hyU hyM hyy
  have hne : ∃ x, φ x ≠ x := by
    by_contra hall
    push Not at hall
    exact hnt fun a ha => (hφ a ha a ha).mpr (hall (u₁ a)).symm
  choose sec hsecY hsecu using hc₁.u_surj
  have hmem : ∀ a : (Y₁ ⊓ commCenterSubgroup U y : Subgroup G), (a : G) ∈ Y₁ ∧
      y * a * y⁻¹ * (a : G)⁻¹ ∈ U ⊓ centralizer (U : Set G) := fun a =>
    ⟨(mem_inf.mp a.2).1, ((mem_inf.mp a.2).2).2⟩
  have hu0 : ∀ a : (Y₁ ⊓ commCenterSubgroup U y : Subgroup G),
      u₁ ((sec (u₁ a))⁻¹ * a) = 0 := fun a => by
    rw [hc₁.u_mul_inv (hsecY _) (hmem a).1, hsecu, sub_self]
  let Fm : (Y₁ ⊓ commCenterSubgroup U y : Subgroup G) →
      {x : E // φ x = x} × {x : E // σ x = x} := fun a =>
    (⟨u₁ a, ((hφ a (hmem a).1 a (hmem a).1).mp (hmem a).2).symm⟩,
      ⟨v₁ ((sec (u₁ a))⁻¹ * a), hc₁.sigma_v_of_u_eq_zero
        (mul_mem (inv_mem (hsecY _)) (hmem a).1) (hu0 a)⟩)
  have hFm : Function.Injective Fm := by
    intro a b hab
    have h1 : u₁ a = u₁ b := congrArg (fun p => (p.1 : E)) hab
    have h2 : v₁ ((sec (u₁ a))⁻¹ * a) = v₁ ((sec (u₁ b))⁻¹ * b) :=
      congrArg (fun p => (p.2 : E)) hab
    rw [h1] at h2
    have h3 := hu0 a
    rw [h1] at h3
    have h4 := hc₁.inj _ (mul_mem (inv_mem (hsecY _)) (hmem a).1) _
      (mul_mem (inv_mem (hsecY _)) (hmem b).1) (by rw [h3, hu0 b]) h2
    exact Subtype.ext (mul_left_cancel h4)
  calc Nat.card (Y₁ ⊓ commCenterSubgroup U y : Subgroup G)
      ≤ Nat.card ({x : E // φ x = x} × {x : E // σ x = x}) :=
        Nat.card_le_card_of_injective Fm hFm
    _ = Nat.card {x : E // φ x = x} * Nat.card {x : E // σ x = x} := Nat.card_prod _ _
    _ ≤ q * q := by
        rw [hF]
        exact Nat.mul_le_mul_right q
          ((NormIsometry.card_fixed_le σ hσσ hφadd hφN hne).trans hF.le)

theorem card_inf_commCenterSubgroup_le_of_swap {E : Type*} [Field E] [CharP E 2] [Finite E]
    {σ : E →+* E} {q : ℕ} (hE : Nat.card E = q ^ 2)
    (hF : Nat.card {x : E // σ x = x} = q) {U Y₁ Y₂ : Subgroup G} {u₁ v₁ : G → E}
    (hc₁ : U3RootCoords Y₁ σ u₁ v₁) (hY : Y₁ ⊔ Y₂ = U)
    (hcomm : ∀ a ∈ Y₁, ∀ b ∈ Y₂, a * b = b * a) {y : G}
    (hsw : (U ⊓ centralizer (Y₂ : Set G)).map (MulAut.conj y).toMonoidHom =
      U ⊓ centralizer (Y₁ : Set G)) :
    Nat.card (Y₁ ⊓ commCenterSubgroup U y : Subgroup G) ≤ q := by
  obtain ⟨ω, hω⟩ := NormInvolution.exists_sigma_ne σ hE hF
  have hu0 : ∀ a : (Y₁ ⊓ commCenterSubgroup U y : Subgroup G), u₁ a = 0 := fun a =>
    hc₁.u_eq_zero_of_comm ⟨ω, hω⟩ (mem_inf.mp a.2).1 fun z hz =>
      (mem_centralizer_iff.mp (mem_centralizer_of_comm_mem_center hY hcomm hsw
        (mem_inf.mp a.2).1 ((mem_inf.mp a.2).2).2) z hz).symm
  let Fm : (Y₁ ⊓ commCenterSubgroup U y : Subgroup G) → {x : E // σ x = x} := fun a =>
    ⟨v₁ a, hc₁.sigma_v_of_u_eq_zero (mem_inf.mp a.2).1 (hu0 a)⟩
  have hFm : Function.Injective Fm := fun a b hab => Subtype.ext
    (hc₁.inj _ (mem_inf.mp a.2).1 _ (mem_inf.mp b.2).1 (by rw [hu0 a, hu0 b])
      (congrArg Subtype.val hab))
  exact (Nat.card_le_card_of_injective Fm hFm).trans hF.le

end Coords

end CFSG.SeitzReduction.RankOne
