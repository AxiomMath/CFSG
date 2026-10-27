module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Residual
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.ComponentClassification.SolAltLit

open CFSG Subgroup

variable {G : Type*} [Group G]

theorem mem_conjugate_iff_conj {H : Subgroup G} {g x : G} :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

theorem conjugate_centralizer_conj (g y : G) :
    conjugate (centralizer ({g * y * g⁻¹} : Set G)) g = centralizer ({y} : Set G) := by
  ext x
  rw [mem_conjugate_iff_conj, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  have e1 : g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := by group
  have e2 : g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
  rw [e1, e2]
  constructor
  · intro h
    exact mul_left_cancel (mul_right_cancel h)
  · intro h
    rw [h]

theorem isComponent_subgroupOf_conjugate {A B : Subgroup G} (hAB : A ≤ B)
    (hA : IsComponent (A.subgroupOf B)) (g : G) :
    IsComponent ((conjugate A g).subgroupOf (conjugate B g)) := by
  let φ : G ≃* G := MulAut.conj g⁻¹
  let e : ↥B ≃* ↥(conjugate B g) := MulEquiv.subgroupMap φ B
  have h := LocalCores.isComponent_map_mulEquiv e hA
  convert h using 2
  ext ⟨x, hx⟩
  simp only [mem_subgroupOf, mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, hAB ha⟩, ha, rfl⟩
  · rintro ⟨⟨b, hb⟩, hbA, hbx⟩
    refine ⟨b, hbA, ?_⟩
    have := congrArg Subtype.val hbx
    exact this

theorem commutator_eq_bot_of_subgroupOf {A B C : Subgroup G} (hA : A ≤ C) (hB : B ≤ C)
    (h : ⁅A.subgroupOf C, B.subgroupOf C⁆ = ⊥) : ⁅A, B⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer] at h ⊢
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  have hmem := h (show (⟨a, hA ha⟩ : C) ∈ A.subgroupOf C from ha)
  rw [mem_centralizer_iff] at hmem
  exact congrArg Subtype.val (hmem ⟨b, hB hb⟩ hb)

theorem mem_normalizer_of_conjugate_eq {L : Subgroup G} {g : G} (h : conjugate L g = L) :
    g ∈ normalizer (L : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  rw [← mem_conjugate_iff_conj, h]

theorem conjugate_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (h : g ∈ normalizer (H : Set G)) : conjugate H g = H := by
  ext x
  rw [mem_conjugate_iff_conj]
  exact ((mem_normalizer_iff.1 h) x).symm

variable [Finite G]

theorem isStandardSubgroup_of_nonembedded {L : Subgroup G} (hq : IsQuasisimple L) {t : G}
    (ht : orderOf t = 2) (htL : L ≤ centralizer ({t} : Set G))
    (hne : ∀ y : G, orderOf y = 2 → L ≤ centralizer ({y} : Set G) →
      IsComponent (L.subgroupOf (centralizer ({y} : Set G))))
    (hcomm : ∀ g : G, ⁅L, conjugate L g⁆ ≠ ⊥) : IsStandardSubgroup L := by
  set C := centralizer (L : Set G) with hC
  have key : ∀ g : G, 2 ∣ Nat.card ↥(C ⊓ conjugate C g) → conjugate L g = L := by
    intro g h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 h2
    set y : G := (a : G) with hya
    have hyC : y ∈ C := (Subgroup.mem_inf.1 a.2).1
    have hyCg : y ∈ conjugate C g := (Subgroup.mem_inf.1 a.2).2
    have hy2 : orderOf y = 2 := by
      rw [hya, Subgroup.orderOf_coe, ha]
    set y' := g * y * g⁻¹ with hy'
    have hy'C : y' ∈ C := mem_conjugate_iff_conj.1 hyCg
    have hy'2 : orderOf y' = 2 := by
      have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      rw [hy', h, hy2]
    have hLy : L ≤ centralizer ({y} : Set G) := fun l hl =>
      mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hyC) l hl)
    have hLy' : L ≤ centralizer ({y'} : Set G) := fun l hl =>
      mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hy'C) l hl)
    have hLgy : conjugate L g ≤ centralizer ({y} : Set G) := by
      rw [← conjugate_centralizer_conj g y]
      intro x hx
      rw [mem_conjugate_iff_conj] at hx ⊢
      exact hLy' hx
    have hc1 := hne y hy2 hLy
    have hc2 : IsComponent ((conjugate L g).subgroupOf (centralizer ({y} : Set G))) := by
      have := isComponent_subgroupOf_conjugate hLy' (hne y' hy'2 hLy') g
      rwa [conjugate_centralizer_conj g y] at this
    rcases LocalCores.distinct_components_commute hc1 hc2 with heq | hbot
    · have h3 := Subgroup.subgroupOf_inj.1 heq
      rw [inf_eq_left.2 hLy, inf_eq_left.2 hLgy] at h3
      exact h3.symm
    · exact absurd (commutator_eq_bot_of_subgroupOf hLy hLgy hbot) (hcomm g)
  have htC : t ∈ C := mem_centralizer_iff.2 fun l hl => mem_centralizer_singleton_iff.1 (htL hl)
  have h2C : 2 ∣ Nat.card C := by
    have h := orderOf_dvd_natCard (⟨t, htC⟩ : C)
    rwa [Subgroup.orderOf_mk, ht] at h
  have hNC : normalizer (C : Set G) ≤ normalizer (L : Set G) := fun g hg =>
    mem_normalizer_of_conjugate_eq (key g (by rwa [conjugate_eq_of_mem_normalizer hg, inf_idem]))
  refine ⟨hq, even_iff_two_dvd.2 h2C, fun g hg => ?_,
    le_antisymm hNC (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer L), hcomm⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  exact hg (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer L
    (mem_normalizer_of_conjugate_eq (key g (even_iff_two_dvd.1 hodd))))

end CFSG.ComponentClassification.SolAltLit
