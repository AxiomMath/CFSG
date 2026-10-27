module

public import CFSG.GH74.E2.Cl2Rank
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GroupTheory.AlternatingFive

private lemma center_eq_bot_of_mulEquiv_alternatingGroup {G : Type*} [Group G] {L : Subgroup G}
    (e : ↥L ≃* ↥(alternatingGroup (Fin 5))) : Subgroup.center ↥L = ⊥ := by
  have hmap : Subgroup.map e.toMonoidHom (Subgroup.center ↥L) =
      Subgroup.center ↥(alternatingGroup (Fin 5)) := Subgroup.map_center_eq e
  rw [alternatingGroup.center_eq_bot (α := Fin 5) (by norm_num)] at hmap
  exact (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center ↥L) e.injective).mp hmap

private lemma conj_mem_of_mem_sup_of_mem_left {G : Type*} [Group G] {L₁ L₂ : Subgroup G}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    {x : G} (hx : x ∈ L₁ ⊔ L₂) {l : G} (hl : l ∈ L₁) :
    x * l * x⁻¹ ∈ L₁ := by
  obtain ⟨u, hu, v, hv, rfl⟩ :=
    (CFSG.GH74.E2.mem_sup_iff_of_commute hcomm).mp hx
  have hvl : v * l = l * v := (hcomm l hl v hv).symm
  have hcalc : u * v * l * (u * v)⁻¹ = u * l * u⁻¹ := by
    rw [mul_inv_rev]
    calc u * v * l * (v⁻¹ * u⁻¹) = u * (v * l) * v⁻¹ * u⁻¹ := by group
      _ = u * (l * v) * v⁻¹ * u⁻¹ := by rw [hvl]
      _ = u * l * u⁻¹ := by group
  rw [hcalc]
  exact L₁.mul_mem (L₁.mul_mem hu hl) (L₁.inv_mem hu)

private lemma inf_of_simple_eq_bot_or_le {G : Type*} [Group G] {K L X : Subgroup G}
    (hLX : L ≤ X) (hKn : ∀ k ∈ K, ∀ x ∈ X, x * k * x⁻¹ ∈ K) [IsSimpleGroup ↥L] :
    K ⊓ L = ⊥ ∨ L ≤ K := by
  let N : Subgroup ↥L := (K ⊓ L).subgroupOf L
  have hN : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hKn (n : G) hn.1 (g : G) (hLX g.2),
      L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · left
    rw [eq_bot_iff]
    intro z hz
    have hzN : (⟨z, hz.2⟩ : ↥L) ∈ N := by
      rw [Subgroup.mem_subgroupOf]
      exact hz
    rw [hbot] at hzN
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hzN)
  · right
    exact (le_inf_iff.mp ((Subgroup.subgroupOf_eq_top).mp htop)).1

private lemma commute_left_of_mem_normalizer {G : Type*} [Group G] {K L X : Subgroup G}
    (hKX : K ≤ X) (hLX : L ≤ X)
    (hKn : ∀ k ∈ K, ∀ x ∈ X, x * k * x⁻¹ ∈ K)
    (hLn : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ ∈ L)
    (hKinf : K ⊓ L = ⊥) {k : G} (hk : k ∈ K) :
    ∀ l ∈ L, k * l = l * k := by
  intro l hl
  have hcK : k * l * k⁻¹ * l⁻¹ ∈ K := by
    have h2 : l * k⁻¹ * l⁻¹ ∈ K := hKn k⁻¹ (K.inv_mem hk) l (hLX hl)
    simpa [mul_assoc] using K.mul_mem hk h2
  have h3 : k * l * k⁻¹ ∈ L := hLn k (hKX hk) l hl
  have hcL : k * l * k⁻¹ * l⁻¹ ∈ L := L.mul_mem h3 (L.inv_mem hl)
  have hc : k * l * k⁻¹ * l⁻¹ ∈ K ⊓ L := ⟨hcK, hcL⟩
  rw [hKinf, Subgroup.mem_bot] at hc
  calc k * l = (k * l * k⁻¹ * l⁻¹) * (l * k) := by group
    _ = l * k := by rw [hc, one_mul]

private lemma eq_of_le_of_forall_conj_mem_of_isSimpleGroup {G : Type*} [Group G]
    {K L : Subgroup G} (hLK : L ≤ K) [IsSimpleGroup ↥K] (hLne : L ≠ ⊥)
    (hLn : ∀ k ∈ K, ∀ l ∈ L, k * l * k⁻¹ ∈ L) : K = L := by
  have hN : (L.subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hLn (g : G) g.2 (n : G) hn⟩
  refine le_antisymm ?_ hLK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf K) with hbot | htop
  · exfalso
    have hinf : L ⊓ K = ⊥ := disjoint_iff.mp ((Subgroup.subgroupOf_eq_bot).mp hbot)
    rw [inf_of_le_left hLK] at hinf
    exact hLne hinf
  · exact (Subgroup.subgroupOf_eq_top).mp htop

theorem eq_one_of_mem_sup_of_forall_commute {G : Type*} [Group G] {L₁ L₂ : Subgroup G}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    (hZ₁ : Subgroup.center ↥L₁ = ⊥) (hZ₂ : Subgroup.center ↥L₂ = ⊥)
    {k : G} (hk : k ∈ L₁ ⊔ L₂)
    (hk₁ : ∀ l ∈ L₁, k * l = l * k) (hk₂ : ∀ l ∈ L₂, k * l = l * k) :
    k = 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (CFSG.GH74.E2.mem_sup_iff_of_commute hcomm).mp hk
  have hacomm : ∀ l ∈ L₁, a * l = l * a := by
    intro l hl
    have h1 : a * b * l = l * a * b := by
      have hkl := hk₁ l hl
      rw [← hab] at hkl
      simpa only [mul_assoc] using hkl
    have hbl : b * l = l * b := (hcomm l hl b hb).symm
    have h2 : (a * l) * b = (l * a) * b := by
      calc (a * l) * b = a * (l * b) := by group
        _ = a * (b * l) := by rw [hbl]
        _ = a * b * l := by group
        _ = l * a * b := h1
        _ = (l * a) * b := by group
    exact mul_right_cancel h2
  have hbcomm : ∀ l ∈ L₂, b * l = l * b := by
    intro l hl
    have h1 : a * b * l = l * a * b := by
      have hkl := hk₂ l hl
      rw [← hab] at hkl
      simpa only [mul_assoc] using hkl
    have hal : a * l = l * a := hcomm a ha l hl
    have h2 : a * (b * l) = a * (l * b) := by
      calc a * (b * l) = a * b * l := by group
        _ = l * a * b := h1
        _ = (l * a) * b := by group
        _ = (a * l) * b := by rw [hal]
        _ = a * (l * b) := by group
    exact mul_left_cancel h2
  have haZ : a = 1 := by
    have hmem : (⟨a, ha⟩ : ↥L₁) ∈ Subgroup.center ↥L₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hacomm (g : G) g.2).symm
    rw [hZ₁, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  have hbZ : b = 1 := by
    have hmem : (⟨b, hb⟩ : ↥L₂) ∈ Subgroup.center ↥L₂ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hbcomm (g : G) g.2).symm
    rw [hZ₂, Subgroup.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  rw [← hab, haZ, hbZ]
  simp

theorem eq_bot_of_normal_of_inf_eq_bot {G : Type*} [Group G] {L₁ L₂ K : Subgroup G}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    (h₁ : Nonempty (↥L₁ ≃* ↥(alternatingGroup (Fin 5))))
    (h₂ : Nonempty (↥L₂ ≃* ↥(alternatingGroup (Fin 5))))
    (hK : K ≤ L₁ ⊔ L₂) (hKn : ∀ k ∈ K, ∀ x ∈ L₁ ⊔ L₂, x * k * x⁻¹ ∈ K)
    (hK₁ : K ⊓ L₁ = ⊥) (hK₂ : K ⊓ L₂ = ⊥) : K = ⊥ := by
  obtain ⟨e₁⟩ := h₁
  obtain ⟨e₂⟩ := h₂
  have hZ₁ : Subgroup.center ↥L₁ = ⊥ := center_eq_bot_of_mulEquiv_alternatingGroup e₁
  have hZ₂ : Subgroup.center ↥L₂ = ⊥ := center_eq_bot_of_mulEquiv_alternatingGroup e₂
  have hL₁n : ∀ x ∈ L₁ ⊔ L₂, ∀ l ∈ L₁, x * l * x⁻¹ ∈ L₁ :=
    fun x hx l hl => conj_mem_of_mem_sup_of_mem_left hcomm hx hl
  have hL₂n : ∀ x ∈ L₁ ⊔ L₂, ∀ l ∈ L₂, x * l * x⁻¹ ∈ L₂ := by
    intro x hx l hl
    exact conj_mem_of_mem_sup_of_mem_left
      (L₁ := L₂) (L₂ := L₁) (fun y hy z hz => (hcomm z hz y hy).symm)
      (by simpa [sup_comm] using hx) hl
  have key : ∀ k ∈ K, k = 1 := by
    intro k hk
    have hk₁ := commute_left_of_mem_normalizer hK le_sup_left hKn hL₁n hK₁ hk
    have hk₂ := commute_left_of_mem_normalizer hK le_sup_right hKn hL₂n hK₂ hk
    exact eq_one_of_mem_sup_of_forall_commute hcomm hZ₁ hZ₂ (hK hk) hk₁ hk₂
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  exact key k hk

theorem map_conj_eq_or_eq_of_normalizes {G : Type*} [Group G] {L₁ L₂ : Subgroup G}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    (h₁ : Nonempty (↥L₁ ≃* ↥(alternatingGroup (Fin 5))))
    (h₂ : Nonempty (↥L₂ ≃* ↥(alternatingGroup (Fin 5))))
    {a : G} (ha : a ∈ Subgroup.normalizer ((L₁ ⊔ L₂ : Subgroup G) : Set G)) :
    L₁.map (MulAut.conj a).toMonoidHom = L₁ ∨
      L₁.map (MulAut.conj a).toMonoidHom = L₂ := by
  let e₁ := h₁.some
  let e₂ := h₂.some
  let φ : G ≃* G := MulAut.conj a
  let X : Subgroup G := L₁ ⊔ L₂
  let K : Subgroup G := L₁.map φ.toMonoidHom
  change K = L₁ ∨ K = L₂
  have hXmap : X.map φ.toMonoidHom = X := by
    have h := Subgroup.mem_normalizer_iff_map_conj_eq.mp ha
    simpa [X, φ] using h
  haveI : IsSimpleGroup ↥L₁ := e₁.isSimpleGroup
  haveI : IsSimpleGroup ↥L₂ := e₂.isSimpleGroup
  haveI : IsSimpleGroup ↥K := by
    have eK : ↥L₁ ≃* ↥K :=
      Subgroup.equivMapOfInjective L₁ φ.toMonoidHom φ.injective
    exact eK.symm.isSimpleGroup
  have hL₁ne : L₁ ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L₁).mp inferInstance
  have hL₂ne : L₂ ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L₂).mp inferInstance
  have hL₁n : ∀ x ∈ X, ∀ l ∈ L₁, x * l * x⁻¹ ∈ L₁ :=
    fun x hx l hl => conj_mem_of_mem_sup_of_mem_left hcomm hx hl
  have hL₂n : ∀ x ∈ X, ∀ l ∈ L₂, x * l * x⁻¹ ∈ L₂ := by
    intro x hx l hl
    exact conj_mem_of_mem_sup_of_mem_left
      (L₁ := L₂) (L₂ := L₁) (fun y hy z hz => (hcomm z hz y hy).symm)
      (by simpa [X, sup_comm] using hx) hl
  have hKle : K ≤ X := by
    change L₁.map φ.toMonoidHom ≤ X
    calc L₁.map φ.toMonoidHom ≤ X.map φ.toMonoidHom := Subgroup.map_mono le_sup_left
      _ = X := hXmap
  have hKnX : ∀ k ∈ K, ∀ x ∈ X, x * k * x⁻¹ ∈ K := by
    intro k hk x hx
    change x * k * x⁻¹ ∈ L₁.map φ.toMonoidHom
    have hk' : k ∈ L₁.map φ.toMonoidHom := hk
    obtain ⟨l, hl, rfl⟩ := hk'
    have hx' : φ.symm x ∈ X := by
      have hy : φ (φ.symm x) ∈ X.map φ.toMonoidHom := by
        rw [hXmap]
        simpa using hx
      exact (Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) (K := X) φ.injective).mp hy
    have hm : φ.symm x * l * (φ.symm x)⁻¹ ∈ L₁ := hL₁n (φ.symm x) hx' l hl
    have hmap : φ (φ.symm x * l * (φ.symm x)⁻¹) ∈ L₁.map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem φ.toMonoidHom hm
    have hmap' : φ (φ.symm x * l * (φ.symm x)⁻¹) = x * φ.toMonoidHom l * x⁻¹ := by
      simp
    rw [← hmap']
    exact hmap
  have hKinf₁ : K ⊓ L₁ = ⊥ ∨ L₁ ≤ K :=
    inf_of_simple_eq_bot_or_le (show L₁ ≤ X from le_sup_left) hKnX
  have hKinf₂ : K ⊓ L₂ = ⊥ ∨ L₂ ≤ K :=
    inf_of_simple_eq_bot_or_le (show L₂ ≤ X from le_sup_right) hKnX
  have hKne : K ≠ ⊥ := by
    intro hbot
    apply hL₁ne
    have hmapbot : L₁.map φ.toMonoidHom = ⊥ := hbot
    exact (Subgroup.map_eq_bot_iff_of_injective L₁ φ.injective).mp hmapbot
  rcases hKinf₁ with hK₁ | hL₁K
  · rcases hKinf₂ with hK₂ | hL₂K
    · exact absurd (eq_bot_of_normal_of_inf_eq_bot hcomm h₁ h₂ hKle hKnX hK₁ hK₂) hKne
    · right
      exact eq_of_le_of_forall_conj_mem_of_isSimpleGroup hL₂K hL₂ne
        (fun k hk l hl => hL₂n k (hKle hk) l hl)
  · left
    exact eq_of_le_of_forall_conj_mem_of_isSimpleGroup hL₁K hL₁ne
      (fun k hk l hl => hL₁n k (hKle hk) l hl)

end CFSG.GroupTheory.AlternatingFive
