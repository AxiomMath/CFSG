module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.O2Bound

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma isShape_centralizer_of_mem_outA {G : Type} [Group G] {a z a₁ : G}
    (hOrb : GzOrbitFacts a z) (ha₁z : a₁ ∈ Gx z) (ha₁Q : a₁ ∉ Qz z) (ha₁ : IsConj a a₁) :
    IsShapeTwoTwoTimesTwoFourA5
      ↥(Subgroup.centralizer ({(⟨a₁, ha₁z⟩ : ↥(Gx z))} : Set ↥(Gx z))) := by
  let C := ↥(Gx z)
  let t : C := ⟨a₁, ha₁z⟩
  let X : Subgroup C := Subgroup.centralizer ({t} : Set C)
  have hmap : X.map (Gx z).subtype = Gxy z a₁ := by
    rw [Gxy_eq_inf]
    ext g
    constructor
    · intro hg
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [← hyg]; exact y.2
      · rw [mem_Gx]
        have hy' : y * t = t * y := Subgroup.mem_centralizer_singleton_iff.mp hy
        have hcoe := congrArg (fun u : C => (u : G)) hy'
        rw [← hyg]
        exact hcoe.symm
    · intro hg
      rw [Subgroup.mem_inf] at hg
      refine Subgroup.mem_map.mpr ⟨⟨g, hg.1⟩, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact (mem_Gx.mp hg.2).symm
  have hiso : Nonempty (↥X ≃* ↥(Gxy z a₁)) :=
    ⟨(Subgroup.equivMapOfInjective X (Gx z).subtype (Gx z).subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)⟩
  obtain ⟨Y, hY, hshape, ⟨e⟩⟩ := hOrb.shape_outA a₁ ha₁z ha₁Q ha₁
  exact ⟨Y, hY, hshape, ⟨hiso.some.trans e⟩⟩

private lemma isPGroup_sup_zpowers {C : Type} [Group C] [Finite C] {Q : Subgroup C} [Q.Normal]
    (hQ : IsPGroup 2 ↥Q) {t : C} (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) :
    IsPGroup 2 ↥(Q ⊔ Subgroup.zpowers t) := by
  have hz : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, orderOf_eq_prime ht2 ht1]
    norm_num
  exact IsPGroup.to_sup_of_normal_left hQ hz

private lemma normalizes_sup_zpowers {C : Type} [Group C] {Q X : Subgroup C} [Q.Normal]
    {t : C} (hXt : ∀ g ∈ X, g * t = t * g) :
    ∀ g ∈ X, ∀ p ∈ (Q ⊔ Subgroup.zpowers t) ⊓ X,
      g * p * g⁻¹ ∈ (Q ⊔ Subgroup.zpowers t) ⊓ X := by
  intro g hg p hp
  rw [Subgroup.mem_inf] at hp ⊢
  refine ⟨?_, ?_⟩
  · have hQmap : Q.map (MulAut.conj g) = Q := by
      rw [← Subgroup.mem_normalizer_iff_map_conj_eq]
      rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : Q.Normal)]
      exact Subgroup.mem_top g
    have hzmap : (Subgroup.zpowers t).map (MulAut.conj g) = Subgroup.zpowers t := by
      rw [MonoidHom.map_zpowers]
      congr 1
      change g * t * g⁻¹ = t
      rw [hXt g hg]
      group
    have hmap : (Q ⊔ Subgroup.zpowers t).map (MulAut.conj g) = Q ⊔ Subgroup.zpowers t := by
      rw [Subgroup.map_sup, hQmap, hzmap]
    have hmem : (MulAut.conj g) p ∈ (Q ⊔ Subgroup.zpowers t).map (MulAut.conj g) :=
      Subgroup.mem_map.mpr ⟨p, hp.1, rfl⟩
    rw [hmap] at hmem
    exact hmem
  · exact X.mul_mem (X.mul_mem hg hp.2) (X.inv_mem hg)

theorem gz9_card_inf_centralizer_le {G : Type} [Group G] [Finite G] {a z : G}
    (h : IsF5Type a z) (hOrb : GzOrbitFacts a z) {a₁ : G} (ha₁z : a₁ ∈ Gx z)
    (ha₁Q : a₁ ∉ Qz z) (ha₁ : IsConj a a₁) :
    Nat.card ↥(CFSG.pCore 2 ↥(Gx z) ⊓
      Subgroup.centralizer ({(⟨a₁, ha₁z⟩ : ↥(Gx z))} : Set ↥(Gx z))) ≤ 2 ^ 5 := by
  classical
  let Q : Subgroup ↥(Gx z) := CFSG.pCore 2 ↥(Gx z)
  let t : ↥(Gx z) := ⟨a₁, ha₁z⟩
  let X : Subgroup ↥(Gx z) := Subgroup.centralizer ({t} : Set ↥(Gx z))
  let P : Subgroup ↥(Gx z) := (Q ⊔ Subgroup.zpowers t) ⊓ X
  let R : Subgroup ↥(Gx z) := Q ⊓ X
  change Nat.card ↥R ≤ 2 ^ 5
  have ha2 : a ^ 2 = 1 := by
    rw [← h.orderOf_a]
    exact pow_orderOf_eq_one a
  have ha₁sq : a₁ ^ 2 = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp ha₁
    rw [← hc, conj_pow, ha2]
    simp
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    change (t : G) ^ 2 = 1
    exact ha₁sq
  have ht1 : t ≠ 1 := by
    intro ht
    have htQ : t ∈ Q := by rw [ht]; exact Subgroup.one_mem Q
    exact ha₁Q (Subgroup.mem_map.mpr ⟨t, htQ, rfl⟩)
  have hX : IsShapeTwoTwoTimesTwoFourA5 ↥X :=
    isShape_centralizer_of_mem_outA hOrb ha₁z ha₁Q ha₁
  have hQp : IsPGroup 2 ↥Q := CFSG.pCore_isPGroup
  have hQT2 : IsPGroup 2 ↥(Q ⊔ Subgroup.zpowers t) := isPGroup_sup_zpowers hQp ht2 ht1
  have hP2 : IsPGroup 2 ↥P := hQT2.to_le inf_le_left
  have hnorm : ∀ g ∈ X, ∀ p ∈ P, g * p * g⁻¹ ∈ P :=
    normalizes_sup_zpowers (Q := Q) (X := X) (t := t)
      (fun g hg => Subgroup.mem_centralizer_singleton_iff.mp hg)
  have hPcard : Nat.card ↥P ≤ 64 :=
    card_le_of_normal_isPGroup hX P inf_le_right hnorm hP2
  have hRP : R ≤ P := by
    intro x hx
    rw [Subgroup.mem_inf] at hx ⊢
    exact ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  have htP : t ∈ P := by
    rw [Subgroup.mem_inf]
    exact ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers t),
      Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have htR : t ∉ R := by
    intro ht
    rw [Subgroup.mem_inf] at ht
    exact ha₁Q (Subgroup.mem_map.mpr ⟨t, ht.1, rfl⟩)
  have hRne : Nat.card ↥R ≠ Nat.card ↥P := by
    intro hcard
    have hEq : R = P := Subgroup.eq_of_le_of_card_ge hRP (le_of_eq hcard.symm)
    have : t ∈ R := by rw [hEq]; exact htP
    exact htR this
  have hle : Nat.card ↥R ≤ Nat.card ↥P := Subgroup.card_le_of_le hRP
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hRP
  have hk2 : 2 ≤ k := by
    by_contra h
    push_neg at h
    interval_cases k
    · rw [hk, mul_zero] at hle
      omega
    · exact hRne (by rw [hk, mul_one])
  have h2R : 2 * Nat.card ↥R ≤ Nat.card ↥P := by
    rw [hk]
    calc 2 * Nat.card ↥R = Nat.card ↥R * 2 := Nat.mul_comm _ _
      _ ≤ Nat.card ↥R * k := Nat.mul_le_mul_left _ hk2
  have h32 : Nat.card ↥R ≤ 32 := by
    have h64 : 2 * Nat.card ↥R ≤ 64 := le_trans h2R hPcard
    omega
  simpa using h32

end CFSG.EvenSporadicStandard.HNRecog.Section3
