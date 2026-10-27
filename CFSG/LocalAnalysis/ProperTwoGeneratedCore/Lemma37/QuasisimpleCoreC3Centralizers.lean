module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3QuotientCent

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

namespace PartC

variable (Z : Subgroup G) [Z.Normal]

omit [Z.Normal] in
theorem card_of_mem_iff (hc : PartC T Q P₁ e u) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) :
    Nat.card Z = 2 := by
  have hset : (Z : Set G) = {1, e} := by
    ext x
    simp only [SetLike.mem_coe, hZ, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [show Nat.card Z = (Z : Set G).ncard from Nat.card_coe_set_eq _, hset,
    Set.ncard_pair hc.centralElt_ne_one.symm]

theorem card_map_mul_two (hc : PartC T Q P₁ e u) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e)
    {K : Subgroup G} (hZK : Z ≤ K) :
    Nat.card (K.map (QuotientGroup.mk' Z)) * 2 = Nat.card K := by
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk', ← hc.card_of_mem_iff Z hZ]
  have := Subgroup.relIndex_mul_card Z K
  rwa [inf_eq_left.mpr hZK] at this

theorem card_quaternionGroup_two : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem card_map_right (hc : PartC T Q P₁ e u) (φ : P₁ ≃* QuaternionGroup 2)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) : Nat.card (P₁.map (QuotientGroup.mk' Z)) = 4 := by
  have h := hc.card_map_mul_two Z hZ (K := P₁) fun x hx => by
    rcases (hZ x).mp hx with rfl | rfl
    exacts [P₁.one_mem, hc.mem_right]
  rw [Nat.card_congr φ.toEquiv, card_quaternionGroup_two] at h
  omega

theorem dihedralTwo_prod_mul_comm :
    ∀ a b : DihedralGroup 2 × DihedralGroup 2, a * b = b * a := by
  decide

theorem mul_comm_of_mem_map_sup (hc : PartC T Q P₁ e u) (φ : P₁ ≃* QuaternionGroup 2)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {a b : G ⧸ Z}
    (ha : a ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z)) (hb : b ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z)) :
    a * b = b * a := by
  obtain ⟨θ⟩ := hc.nonempty_map_sup_mulEquiv Z φ hZ
  have h1 : (⟨a, ha⟩ : ((Q ⊔ P₁).map (QuotientGroup.mk' Z) : Subgroup (G ⧸ Z))) * ⟨b, hb⟩ =
      ⟨b, hb⟩ * ⟨a, ha⟩ :=
    θ.injective (by rw [map_mul, map_mul, dihedralTwo_prod_mul_comm])
  simpa using congrArg Subtype.val h1

omit [Z.Normal] in
theorem relIndex_map_eq_two [Z.Normal] {K L : Subgroup G} (hZK : Z ≤ K) {x : G} (hxL : x ∈ L)
    (hxK : x ∉ K) (h : ∀ s ∈ L, s ∉ K → s * x ∈ K) :
    (K.map (QuotientGroup.mk' Z)).relIndex (L.map (QuotientGroup.mk' Z)) = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨(x : G ⧸ Z), Subgroup.mem_map_of_mem _ hxL⟩, fun b => ?_⟩
  obtain ⟨b, hb⟩ := b
  obtain ⟨s, hsL, rfl⟩ := Subgroup.mem_map.mp hb
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, QuotientGroup.mk'_apply,
    ← QuotientGroup.mk_mul, mk_mem_map_iff_of_le Z hZK]
  by_cases hs : s ∈ K
  · exact Or.inr ⟨hs, fun h' => hxK (by simpa using K.mul_mem (K.inv_mem hs) h')⟩
  · exact Or.inl ⟨h s hsL hs, hs⟩

omit [Z.Normal] in
theorem mk_eq_one_of_commute [Z.Normal] (hc : PartC T Q P₁ e u)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {A B : Subgroup G} (hZA : Z ≤ A)
    (hAB : ∀ x ∈ A, x ∈ B → x = 1 ∨ x = e) {s p : G} (hp : p ∈ A) (hsp : s * p * s⁻¹ ∈ B)
    (hcomm : (p : G ⧸ Z) * (s : G ⧸ Z) = (s : G ⧸ Z) * (p : G ⧸ Z)) : (p : G ⧸ Z) = 1 := by
  have key : ((s * p * s⁻¹ : G) : G ⧸ Z) = (p : G ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hcomm,
      mul_inv_cancel_right]
  have hδ := QuotientGroup.eq.mp key.symm
  have hspA : s * p * s⁻¹ ∈ A := by
    rw [show s * p * s⁻¹ = p * (p⁻¹ * (s * p * s⁻¹)) by group]
    exact A.mul_mem hp (hZA hδ)
  rw [QuotientGroup.eq_one_iff, hZ]
  rcases hAB _ hspA hsp with h1 | h1
  · left
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact h1
  · right
    rw [← hc.conj_centralElt s] at h1
    exact mul_left_cancel (mul_right_cancel h1)

end PartC

namespace CaseC3

variable (Z : Subgroup G) [Z.Normal]

theorem map_sup_inf_centralizer_le (h : CaseC3 T Q P₁ e u y)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {s : G} (hsT : s ∈ T) (hsW : s ∉ Q ⊔ P₁) :
    (Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(s : G ⧸ Z)} ≤
      (Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(y : G ⧸ Z)} := by
  obtain ⟨φ⟩ := h.quaternion_right
  have hc := h.partC
  have hsy : s * y ∈ Q ⊔ P₁ := by
    have := hc.inv_mul_mem s⁻¹ (T.inv_mem hsT) y h.mem
      (fun h' => hsW (by simpa using (Q ⊔ P₁).inv_mem h')) h.not_mem
    rwa [inv_inv] at this
  intro w hw
  obtain ⟨hwW, hwC⟩ := Subgroup.mem_inf.mp hw
  refine Subgroup.mem_inf.mpr ⟨hwW, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff] at hwC ⊢
  have hwc : Commute w ((s * y : G) : G ⧸ Z) :=
    hc.mul_comm_of_mem_map_sup Z φ hZ hwW (Subgroup.mem_map_of_mem _ hsy)
  have hws : Commute w (s : G ⧸ Z) := hwC
  have hy : (y : G ⧸ Z) = (s : G ⧸ Z)⁻¹ * ((s * y : G) : G ⧸ Z) := by
    rw [QuotientGroup.mk_mul]
    group
  rw [hy]
  exact (hws.inv_right.mul_right hwc).eq

theorem card_map_sup_inf_centralizer_le_of_swap (h : CaseC3 T Q P₁ e u y)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {s : G} (hs : ∀ p ∈ P₁, s * p * s⁻¹ ∈ Q) :
    Nat.card ((Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(s : G ⧸ Z)} :
      Subgroup (G ⧸ Z)) ≤ 4 := by
  obtain ⟨φ⟩ := h.quaternion_right
  have hc := h.partC
  set B := (Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(s : G ⧸ Z)} with hB
  set P := P₁.map (QuotientGroup.mk' Z) with hP
  have hZP : Z ≤ P₁ := fun x hx => by
    rcases (hZ x).mp hx with rfl | rfl
    exacts [P₁.one_mem, hc.mem_right]
  have hPB : P ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxB⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hxP
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxB).2
    exact Subgroup.mem_bot.mpr (hc.mk_eq_one_of_commute Z hZ hZP
      (fun x hx hx' => hc.mem_inf x hx' hx) hp (hs p hp) hcomm)
  have h1 := Subgroup.relIndex_mul_card P B
  rw [hPB, Subgroup.card_bot, mul_one] at h1
  have hPW : P ≤ (Q ⊔ P₁).map (QuotientGroup.mk' Z) := Subgroup.map_mono le_sup_right
  have h3 : P.relIndex ((Q ⊔ P₁).map (QuotientGroup.mk' Z)) = 4 := by
    have h4 := Subgroup.relIndex_mul_card P ((Q ⊔ P₁).map (QuotientGroup.mk' Z))
    rw [inf_eq_left.mpr hPW, hc.card_map_right Z φ hZ, hc.card_map_sup Z φ hZ] at h4
    omega
  have h2 : P.relIndex B ≤ P.relIndex ((Q ⊔ P₁).map (QuotientGroup.mk' Z)) :=
    Subgroup.relIndex_le_of_le_right inf_le_left (by rw [h3]; norm_num)
  omega

theorem card_map_sup_inf_inf_le_two (h : CaseC3 T Q P₁ e u y)
    (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {s₁ s₂ : G} (hs₁T : s₁ ∈ T) (hs₁W : s₁ ∉ Q ⊔ P₁)
    (hs₂P : ∀ p ∈ P₁, s₂ * p * s₂⁻¹ ∈ Q) (hs₂Q : ∀ q ∈ Q, s₂ * q * s₂⁻¹ ∈ P₁) :
    Nat.card ((Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(s₁ : G ⧸ Z)} ⊓
      Subgroup.centralizer {(s₂ : G ⧸ Z)} : Subgroup (G ⧸ Z)) ≤ 2 := by
  have hc := h.partC
  obtain ⟨v, hvQ, hvv, hyv, hvfix⟩ := h.exists_inv_conj_left
  set B := (Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓ Subgroup.centralizer {(s₁ : G ⧸ Z)} ⊓
    Subgroup.centralizer {(s₂ : G ⧸ Z)} with hB
  have hZP : Z ≤ P₁ := fun x hx => by
    rcases (hZ x).mp hx with rfl | rfl
    exacts [P₁.one_mem, hc.mem_right]
  have hZQ : Z ≤ Q := fun x hx => by
    rcases (hZ x).mp hx with rfl | rfl
    exacts [Q.one_mem, hc.mem_left]
  have hsub : (B : Set (G ⧸ Z)) ⊆ {1, (u : G ⧸ Z) * (v : G ⧸ Z)} := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hx3 := h.map_sup_inf_centralizer_le Z hZ hs₁T hs₁W hx1
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hx2
    rcases (h.mem_map_sup_inf_centralizer_iff Z hZ hvQ hvv hyv hvfix x).mp hx3 with
      rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl (hc.mk_eq_one_of_commute Z hZ hZP (fun x hx hx' => hc.mem_inf x hx' hx)
        hc.self_mem (hs₂P u hc.self_mem) hcomm)
    · exact Or.inl (hc.mk_eq_one_of_commute Z hZ hZQ hc.mem_inf hvQ (hs₂Q v hvQ) hcomm)
    · exact Or.inr rfl
  rw [show Nat.card B = (B : Set (G ⧸ Z)).ncard from Nat.card_coe_set_eq _]
  calc (B : Set (G ⧸ Z)).ncard ≤ ({1, (u : G ⧸ Z) * (v : G ⧸ Z)} : Set (G ⧸ Z)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({(u : G ⧸ Z) * (v : G ⧸ Z)} : Set (G ⧸ Z)).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

end CaseC3

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
