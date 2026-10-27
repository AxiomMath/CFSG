module

public import CFSG.LargeExtraspecial.AS35LInvB
public import CFSG.LargeExtraspecial.AS35LLocal
public import CFSG.LargeExtraspecial.AS35LAut
public import CFSG.LargeExtraspecial.AS35JThreeT
public import CFSG.Fischer.Classification.Unitary.Mu

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35L

open Subgroup CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification
  CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

structure IsTClass {L : Type} [Group L] (D : Set L) : Prop where
  gen : closure D = ⊤
  nonempty : D.Nonempty
  cls : ∀ a ∈ D, ∀ b ∈ D, ∃ g : L, g * a * g⁻¹ = b
  conj : ∀ g : L, ∀ a ∈ D, g * a * g⁻¹ ∈ D
  inv : ∀ a ∈ D, a * a = 1
  three : ∀ a ∈ D, ∀ b ∈ D, orderOf (a * b) ∈ ({1, 2, 3} : Set ℕ)

theorem exists_mk_eq {L : Type} [Group L] {k : ℕ} (ψ : L ⧸ center L ≃* PG (k + 2))
    (c : PG (k + 2)) : ∃ g : L, ψ (QuotientGroup.mk g) = c := by
  obtain ⟨q, rfl⟩ := ψ.surjective c
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨g, rfl⟩

theorem pg_facts {k : ℕ} (hk : 2 ≤ k) :
    center (PG (k + 2)) = ⊥ ∧ IsSimpleGroup (_root_.commutator (PG (k + 2))) ∧
      ∃ x y : _root_.commutator (PG (k + 2)), x * y ≠ y * x := by
  have hm : 4 ≤ k + 2 := by omega
  have hcomm : _root_.commutator (PG (k + 2)) = ⊤ := commutator_PG hm
  refine ⟨center_PG hm, ?_, ?_⟩
  · have := isSimpleGroup_PG hm
    exact ((MulEquiv.subgroupCongr hcomm).trans Subgroup.topEquiv).isSimpleGroup
  · obtain ⟨a, b, -, -, -, -, hab⟩ := exists_tq_not_commute hm
    exact ⟨⟨tq a, hcomm ▸ mem_top _⟩, ⟨tq b, hcomm ▸ mem_top _⟩,
      fun h => hab (congrArg Subtype.val h)⟩

namespace IsTClass

variable {L : Type} [Group L] {D : Set L} (hD : IsTClass D) {k : ℕ} (hk : 2 ≤ k)
  (ψ : L ⧸ center L ≃* PG (k + 2))
include hD hk ψ

theorem exists_orderOf_eq_three : ∃ a ∈ D, ∃ b ∈ D, orderOf (a * b) = 3 := by
  by_contra! hall
  have hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
    intro x hx y hy
    rcases hD.three x hx y hy with h | h | h
    · exact AS35J.commute_of_orderOf_mul_le_two (hD.inv x hx) (hD.inv y hy) (Or.inl h)
    · exact AS35J.commute_of_orderOf_mul_le_two (hD.inv x hx) (hD.inv y hy) (Or.inr h)
    · exact absurd h (hall x hx y hy)
  have hc1 : closure D ≤ centralizer D := by
    rw [closure_le]
    intro x hx
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro y hy
    exact hcomm y hy x hx
  rw [← centralizer_closure, hD.gen] at hc1
  have hZ : ∀ x : L, x ∈ center L := fun x =>
    mem_center_iff.2 fun y => (mem_centralizer_iff.1 (hc1 (mem_top x)) y (mem_top y))
  have h1 : ∀ c : PG (k + 2), c = 1 := by
    intro c
    obtain ⟨g, rfl⟩ := exists_mk_eq ψ c
    rw [(QuotientGroup.eq_one_iff g).2 (hZ g), map_one]
  have hk2 : 2 ≤ k + 2 := by omega
  exact tq_ne_one (by omega) (isoVec_ne_zero hk2) (isoVec_isotropic hk2) (h1 _)

theorem mk_injOn {a b : L} (ha : a ∈ D) (hb : b ∈ D)
    (h : (QuotientGroup.mk a : L ⧸ center L) = QuotientGroup.mk b) : a = b := by
  by_contra hne
  have hu : a⁻¹ * b ∈ center L := QuotientGroup.eq.mp h
  have hu1 : a⁻¹ * b ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  have hab : a * b = b * a := by
    have h1 := mem_center_iff.1 hu a
    calc a * b = a * (a * (a⁻¹ * b)) * a⁻¹ * a := by group
      _ = a * ((a⁻¹ * b) * a) * a⁻¹ * a := by rw [h1]
      _ = b * a := by group
  have hu2 : (a⁻¹ * b) ^ 2 = 1 := by
    rw [pow_two, inv_eq_of_mul_eq_one_right (hD.inv a ha)]
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = 1 := by rw [← mul_assoc, hD.inv a ha, one_mul, hD.inv b hb]
  obtain ⟨e₁, he₁, e₂, he₂, h3⟩ := hD.exists_orderOf_eq_three hk ψ
  obtain ⟨g, hg⟩ := hD.cls a ha e₂ he₂
  have heu : e₂ * (a⁻¹ * b) ∈ D := by
    have h1 := hD.conj g b hb
    have h2 : g * b * g⁻¹ = e₂ * (a⁻¹ * b) := by
      calc g * b * g⁻¹ = g * a * ((a⁻¹ * b) * g⁻¹) := by group
        _ = g * a * (g⁻¹ * (a⁻¹ * b)) := by rw [mem_center_iff.mp hu g⁻¹]
        _ = (g * a * g⁻¹) * (a⁻¹ * b) := by group
        _ = e₂ * (a⁻¹ * b) := by rw [hg]
    rwa [h2] at h1
  have hcomm : Commute (e₁ * e₂) (a⁻¹ * b) := mem_center_iff.mp hu (e₁ * e₂)
  have h6 : orderOf (e₁ * (e₂ * (a⁻¹ * b))) = 6 := by
    rw [← mul_assoc, hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by
      rw [h3, orderOf_eq_prime hu2 hu1]; norm_num), h3, orderOf_eq_prime hu2 hu1]
  have h7 := hD.three e₁ he₁ _ heu
  rw [h6] at h7
  simp at h7

theorem mem_DG {a : L} (ha : a ∈ D) : ψ (QuotientGroup.mk a) ∈ DG (k + 2) := by
  have hm : 3 ≤ k + 2 := by omega
  set f : L →* PG (k + 2) := ψ.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hf
  have hfx : ∀ x, f x = ψ (QuotientGroup.mk x) := fun _ => rfl
  refine mem_DG_of_orderOf_mul_conj hm ?_ fun c => ?_
  · refine orderOf_eq_prime ?_ fun h1 => ?_
    · rw [sq, ← hfx, ← map_mul, hD.inv a ha, map_one]
    ·
      obtain ⟨e₁, he₁, e₂, he₂, h3⟩ := hD.exists_orderOf_eq_three hk ψ
      have haZ : a ∈ center L := by
        rw [← QuotientGroup.eq_one_iff]
        exact ψ.injective (by rw [h1, map_one])
      have hb : ∀ b ∈ D, b = a := by
        intro b hb
        obtain ⟨g, hg⟩ := hD.cls a ha b hb
        rw [← hg, mem_center_iff.1 haZ g, mul_inv_cancel_right]
      rw [hb e₁ he₁, hb e₂ he₂, hD.inv a ha, orderOf_one] at h3
      exact absurd h3 (by norm_num)
  · obtain ⟨g, rfl⟩ := exists_mk_eq ψ c
    rw [show ψ (QuotientGroup.mk a) * (ψ (QuotientGroup.mk g) * ψ (QuotientGroup.mk a) *
      (ψ (QuotientGroup.mk g))⁻¹) = f (a * (g * a * g⁻¹)) by
        rw [map_mul, map_mul, map_mul, map_inv]; rfl]
    have hdvd := orderOf_map_dvd f (a * (g * a * g⁻¹))
    rcases hD.three a ha _ (hD.conj g a ha) with h | h | h <;> rw [h] at hdvd
    · exact Or.inl (Nat.dvd_one.mp hdvd)
    · rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')

theorem exists_eq {f : PG (k + 2)} (hf : f ∈ DG (k + 2)) :
    ∃ a ∈ D, ψ (QuotientGroup.mk a) = f := by
  have hm : 3 ≤ k + 2 := by omega
  obtain ⟨a₀, ha₀⟩ := hD.nonempty
  obtain ⟨w, hw0, hw, hwa⟩ := hD.mem_DG hk ψ ha₀
  rw [DG_eq_isConj hm hw0 hw] at hf
  obtain ⟨c, rfl⟩ := isConj_iff.1 (show IsConj (tq w) f from hf)
  obtain ⟨g, rfl⟩ := exists_mk_eq ψ c
  refine ⟨g * a₀ * g⁻¹, hD.conj g a₀ ha₀, ?_⟩
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
    map_inv, hwa]

theorem commute_iff {a b : L} (ha : a ∈ D) (hb : b ∈ D) :
    a * b = b * a ↔
      ψ (QuotientGroup.mk a) * ψ (QuotientGroup.mk b) =
        ψ (QuotientGroup.mk b) * ψ (QuotientGroup.mk a) := by
  constructor
  · intro h
    rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  · intro h
    rw [← map_mul, ← map_mul] at h
    rcases AS35J.commute_or_mk_eq_of_mk_commute hD.inv hD.three ha hb (ψ.injective h) with
      h' | h'
    · exact h'
    · rw [hD.mk_injOn hk ψ ha hb h']

theorem exists_lift_centralizer {d : L} (hd : d ∈ D) {c : PG (k + 2)}
    (hc : c * ψ (QuotientGroup.mk d) = ψ (QuotientGroup.mk d) * c) :
    ∃ g : L, g * d * g⁻¹ = d ∧ ψ (QuotientGroup.mk g) = c := by
  obtain ⟨g, rfl⟩ := exists_mk_eq ψ c
  refine ⟨g, hD.mk_injOn hk ψ (hD.conj g d hd) hd (ψ.injective ?_), rfl⟩
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
    map_inv, hc, mul_inv_cancel_right]

theorem mk_eq_one_or_eq_of_normalized {d : L} (hd : d ∈ D) {W : Subgroup L}
    (hW2 : ∀ w ∈ W, w * w = 1) (hdW : d ∈ W)
    (hWn : ∀ g : L, g * d * g⁻¹ = d → ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    ∀ w ∈ W, ψ (QuotientGroup.mk w) = 1 ∨ ψ (QuotientGroup.mk w) = ψ (QuotientGroup.mk d) := by
  set f : L →* PG (k + 2) := ψ.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hf
  have hfx : ∀ x, f x = ψ (QuotientGroup.mk x) := fun _ => rfl
  have key := eq_one_or_eq_of_normalized_DG hk (hD.mem_DG hk ψ hd) (W := W.map f)
    (by
      rintro _ ⟨w, hw, rfl⟩
      rw [← map_mul, hW2 w hw, map_one])
    ⟨d, hdW, rfl⟩
    (by
      rintro c hc _ ⟨w, hw, rfl⟩
      obtain ⟨g, hgd, rfl⟩ := hD.exists_lift_centralizer hk ψ hd hc
      exact ⟨g * w * g⁻¹, hWn g hgd w hw, by rw [map_mul, map_mul, map_inv]; rfl⟩)
  intro w hw
  exact key (f w) ⟨w, hw, rfl⟩

theorem eq_or_eq_conj_of_fix {d : L} (hd : d ∈ D) (β : L ≃* L) (hβD : ∀ a ∈ D, β a ∈ D)
    (hβd : β d = d) (hβC : ∀ a ∈ D, a * d = d * a → β a = a) :
    (∀ a ∈ D, β a = a) ∨ ∀ a ∈ D, β a = d * a * d := by
  obtain ⟨hZ, hS, hna⟩ := pg_facts hk
  set β' : L ⧸ center L ≃* L ⧸ center L :=
    QuotientGroup.congr (center L) (center L) β (Subgroup.map_center_eq β) with hβ'
  set γ : MulAut (PG (k + 2)) := ψ.symm.trans (β'.trans ψ) with hγ
  have hγmk : ∀ a : L, γ (ψ (QuotientGroup.mk a)) = ψ (QuotientGroup.mk (β a)) := by
    intro a
    rw [hγ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply, hβ',
      QuotientGroup.congr_mk]
  have hγE : ∀ e ∈ DG (k + 2), γ e ∈ DG (k + 2) := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := hD.exists_eq hk ψ he
    rw [hγmk]
    exact hD.mem_DG hk ψ (hβD a ha)
  have hγd : γ (ψ (QuotientGroup.mk d)) = ψ (QuotientGroup.mk d) := by rw [hγmk, hβd]
  have hγS : ∀ f ∈ LocalClass (DG (k + 2)) (ψ (QuotientGroup.mk d)), γ f = f := by
    rintro f ⟨hf, hfd, hfc⟩
    obtain ⟨a, ha, rfl⟩ := hD.exists_eq hk ψ hf
    have had : a * d = d * a := (hD.commute_iff hk ψ ha hd).2 hfc
    rw [hγmk, hβC a ha had]
  rcases mulAut_eq_one_or_conj_of_fix (pair_DG (by omega)) hZ hS hna
      (tripleProperty_DG hk) (hD.mem_DG hk ψ hd) γ hγE hγd hγS with h | h
  · left
    intro a ha
    refine hD.mk_injOn hk ψ (hβD a ha) ha (ψ.injective ?_)
    rw [← hγmk, h, MulAut.one_apply]
  · right
    intro a ha
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right (hD.inv d hd)
    have hdad : d * a * d ∈ D := by
      have := hD.conj d a ha
      rwa [hdinv] at this
    refine hD.mk_injOn hk ψ (hβD a ha) hdad (ψ.injective ?_)
    have hinv : (ψ (QuotientGroup.mk d))⁻¹ = ψ (QuotientGroup.mk d) := by
      rw [← map_inv, ← QuotientGroup.mk_inv, hdinv]
    rw [← hγmk, h, MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul,
      map_mul, hinv]

end IsTClass

end CFSG.LargeExtraspecial.AS35L
