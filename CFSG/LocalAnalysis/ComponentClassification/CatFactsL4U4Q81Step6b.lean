module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Join

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup

namespace Q81

variable {G : Type} [Group G]

abbrev conjSub (A : Subgroup G) (g : G) : Subgroup G := A.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {A : Subgroup G} {g x : G} : x ∈ conjSub A g ↔ g⁻¹ * x * g ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show g⁻¹ * (g * a * g⁻¹) * g = a by group]
  · intro h
    exact ⟨_, h, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

theorem conjSub_conjSub (A : Subgroup G) (g h : G) :
    conjSub (conjSub A g) h = conjSub A (h * g) := by
  ext x
  rw [mem_conjSub, mem_conjSub, mem_conjSub]
  rw [show g⁻¹ * (h⁻¹ * x * h) * g = (h * g)⁻¹ * x * (h * g) by group]

theorem centerIn_conjSub (A : Subgroup G) (g : G) :
    centerIn (conjSub A g) = conjSub (centerIn A) g := by
  ext x
  rw [mem_conjSub, mem_centerIn, mem_centerIn, mem_conjSub]
  constructor
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, fun y hy => ?_⟩
    have h1 := hxc (g * y * g⁻¹) (by rw [mem_conjSub]; rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by
      group])
    calc g⁻¹ * x * g * y = g⁻¹ * (x * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * x) * g := by rw [h1]
      _ = y * (g⁻¹ * x * g) := by group
  · rintro ⟨hx, hxc⟩
    refine ⟨hx, fun y hy => ?_⟩
    rw [mem_conjSub] at hy
    have h1 := hxc _ hy
    calc x * y = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = y * x := by group

variable [Finite G]

omit [Finite G] in
theorem isComponent_conj {A : Subgroup G} (hA : IsComponent A) (g : G) :
    IsComponent (conjSub A g) :=
  LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hA

theorem conj_commute {A : Subgroup G} (hA : IsComponent A) (g h : G)
    (hne : conjSub A g ≠ conjSub A h) : conjSub A g ≤ centralizer (conjSub A h : Set G) := by
  rcases LocalCores.distinct_components_commute (isComponent_conj hA g) (isComponent_conj hA h)
    with h1 | h1
  · exact absurd h1 hne
  · exact commutator_eq_bot_iff_le_centralizer.mp h1

omit [Finite G] in
theorem join_normal (A : Subgroup G) : (⨆ g : G, conjSub A g).Normal := by
  refine ⟨fun n hn h => ?_⟩
  have hle : (⨆ g : G, conjSub A g).map (MulAut.conj h).toMonoidHom ≤ ⨆ g : G, conjSub A g := by
    rw [Subgroup.map_iSup]
    exact iSup_le fun g => (conjSub_conjSub A g h).le.trans (le_iSup (fun g => conjSub A g) _)
  exact hle ⟨n, hn, rfl⟩

omit [Finite G] in
theorem centerJoin_normal (A : Subgroup G) : (⨆ g : G, centerIn (conjSub A g)).Normal := by
  refine ⟨fun n hn h => ?_⟩
  have hle : (⨆ g : G, centerIn (conjSub A g)).map (MulAut.conj h).toMonoidHom ≤
      ⨆ g : G, centerIn (conjSub A g) := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun g => ?_
    have h1 : (centerIn (conjSub A g)).map (MulAut.conj h).toMonoidHom =
        centerIn (conjSub A (h * g)) := by
      rw [centerIn_conjSub, centerIn_conjSub]
      exact conjSub_conjSub (centerIn A) g h
    rw [h1]
    exact le_iSup (fun g => centerIn (conjSub A g)) _
  exact hle ⟨n, hn, rfl⟩

omit [Finite G] in
theorem iSup_eq_biSup_univ {ι : Type*} [Fintype ι] (f : ι → Subgroup G) :
    (⨆ i, f i) = ⨆ i ∈ (Finset.univ : Finset ι), f i := by
  simp

theorem mem_centerJoin_of_central {A : Subgroup G} (hA : IsComponent A) {x : G}
    (hx : x ∈ ⨆ g : G, conjSub A g) (hxc : ∀ y ∈ ⨆ g : G, conjSub A g, x * y = y * x) :
    x ∈ ⨆ g : G, centerIn (conjSub A g) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  rw [iSup_eq_biSup_univ] at hx hxc ⊢
  exact mem_iSup_center_of_central (fun g => conjSub A g) Finset.univ
    (fun g _ h _ hne => conj_commute hA g h hne) hx hxc

theorem centerJoin_le_centralizer {A : Subgroup G} (hA : IsComponent A) :
    (⨆ g : G, centerIn (conjSub A g)) ≤ centralizer (A : Set G) := by
  refine iSup_le fun g => ?_
  by_cases hg : conjSub A g = A
  · rw [hg]
    intro x hx
    exact mem_centralizer_iff.mpr fun y hy => ((mem_centerIn.mp hx).2 y hy).symm
  · have h1 := conj_commute hA g 1 (by
      rw [show conjSub A 1 = A by ext x; rw [mem_conjSub]; simp]
      exact hg)
    rw [show conjSub A 1 = A by ext x; rw [mem_conjSub]; simp] at h1
    exact fun x hx => h1 (mem_centerIn.mp hx).1

theorem isElemTwo_of_card_le_two {Z : Subgroup G} (hZ : Nat.card Z ≤ 2) : GrSLit.IsElemTwo Z := by
  have hsq : ∀ x ∈ Z, x * x = 1 := by
    intro x hx
    have h1 : orderOf (⟨x, hx⟩ : Z) ∣ Nat.card Z := orderOf_dvd_natCard _
    have h2 : orderOf (⟨x, hx⟩ : Z) ≤ 2 := (Nat.le_of_dvd Nat.card_pos h1).trans hZ
    have h3 : orderOf (⟨x, hx⟩ : Z) ∣ 2 := by
      interval_cases h : orderOf (⟨x, hx⟩ : Z)
      · exact absurd h (orderOf_pos _).ne'
      · exact one_dvd 2
      · exact dvd_refl 2
    have h4 := orderOf_dvd_iff_pow_eq_one.mp h3
    have h5 : x ^ 2 = 1 := by simpa using congrArg Subtype.val h4
    rwa [sq] at h5
  refine ⟨fun a ha b hb => ?_, hsq⟩
  have hab := hsq (a * b) (mul_mem ha hb)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_left (hsq a ha)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (hsq b hb)
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_left hab).symm
    _ = b * a := by rw [_root_.mul_inv_rev, hai, hbi]

theorem isElemTwo_centerJoin {A : Subgroup G} (hA : IsComponent A)
    (hZ : Nat.card ↥(center ↥A) ≤ 2) : GrSLit.IsElemTwo (⨆ g : G, centerIn (conjSub A g)) := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  have hcard : ∀ g : G, Nat.card ↥(centerIn (conjSub A g)) ≤ 2 := by
    intro g
    rw [centerIn_conjSub, card_map_of_injective (MulAut.conj g).injective, centerIn,
      card_map_of_injective A.subtype_injective]
    exact hZ
  rw [iSup_eq_biSup_univ]
  refine isElemTwo_iSup (fun g => centerIn (conjSub A g)) Finset.univ
    (fun g _ => isElemTwo_of_card_le_two (hcard g)) fun g _ h _ => ?_
  by_cases hgh : conjSub A g = conjSub A h
  · rw [hgh]
    intro x hx
    exact mem_centralizer_iff.mpr fun y hy =>
      ((mem_centerIn.mp hx).2 y (mem_centerIn.mp hy).1).symm
  · intro x hx
    exact mem_centralizer_iff.mpr fun y hy =>
      mem_centralizer_iff.mp (conj_commute hA g h hgh (mem_centerIn.mp hx).1) y
        (mem_centerIn.mp hy).1

theorem mem_centralizer_of_card_le_two {Z : Subgroup G} (hZ : Nat.card Z ≤ 2) {y : G}
    (hy : y ∈ normalizer (Z : Set G)) : y ∈ centralizer (Z : Set G) := by
  rw [mem_centralizer_iff]
  intro x hx
  have hyx : y * x * y⁻¹ ∈ Z := (mem_normalizer_iff.mp hy x).mp hx
  by_cases hx1 : x = 1
  · rw [hx1, mul_one, one_mul]
  have hyx1 : y * x * y⁻¹ ≠ 1 := fun h => hx1 (by
    calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
      _ = 1 := by rw [h]; group)
  have hne : (⟨x, hx⟩ : Z) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  by_contra hc
  have hne' : (⟨y * x * y⁻¹, hyx⟩ : Z) ≠ ⟨x, hx⟩ := fun h => hc (by
    have h1 : y * x * y⁻¹ = x := congrArg Subtype.val h
    calc x * y = (y * x * y⁻¹) * y := by rw [h1]
      _ = y * x := by group)
  have h3 : 3 ≤ Nat.card Z := by
    classical
    let _ : Fintype Z := Fintype.ofFinite Z
    rw [Nat.card_eq_fintype_card]
    have hsub : ({1, ⟨x, hx⟩, ⟨y * x * y⁻¹, hyx⟩} : Finset Z).card ≤ Fintype.card Z :=
      Finset.card_le_univ _
    have hc3 : ({1, ⟨x, hx⟩, ⟨y * x * y⁻¹, hyx⟩} : Finset Z).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hne.symm,
          show (1 : Z) ≠ ⟨y * x * y⁻¹, hyx⟩ from fun h => hyx1 (congrArg Subtype.val h).symm]),
        Finset.card_pair hne'.symm]
    omega
  omega

theorem mem_centralizer_centerJoin {A : Subgroup G} (hZ : Nat.card ↥(center ↥A) ≤ 2) {y : G}
    (hy : ∀ g : G, y ∈ normalizer (conjSub A g : Set G)) :
    (⨆ g : G, centerIn (conjSub A g)) ≤ centralizer ({y} : Set G) := by
  refine iSup_le fun g => ?_
  have hcard : Nat.card ↥(centerIn (conjSub A g)) ≤ 2 := by
    rw [centerIn_conjSub, card_map_of_injective (MulAut.conj g).injective, centerIn,
      card_map_of_injective A.subtype_injective]
    exact hZ
  have hyN : y ∈ normalizer ((centerIn (conjSub A g) : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have hyA := mem_normalizer_iff.mp (hy g)
    constructor
    · intro hx
      obtain ⟨hxA, hxc⟩ := mem_centerIn.mp hx
      refine mem_centerIn.mpr ⟨(hyA x).mp hxA, fun a ha => ?_⟩
      have ha' : y⁻¹ * a * y ∈ conjSub A g := by
        have := (mem_normalizer_iff.mp (inv_mem (hy g)) a).mp ha
        rwa [inv_inv] at this
      have h1 := hxc _ ha'
      calc y * x * y⁻¹ * a = y * (x * (y⁻¹ * a * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * a * y) * x) * y⁻¹ := by rw [h1]
        _ = a * (y * x * y⁻¹) := by group
    · intro hx
      obtain ⟨hxA, hxc⟩ := mem_centerIn.mp hx
      refine mem_centerIn.mpr ⟨(hyA x).mpr hxA, fun a ha => ?_⟩
      have h1 := hxc (y * a * y⁻¹) ((hyA a).mp ha)
      have h2 : y * (x * a) * y⁻¹ = y * (a * x) * y⁻¹ := by
        calc y * (x * a) * y⁻¹ = y * x * y⁻¹ * (y * a * y⁻¹) := by group
          _ = y * a * y⁻¹ * (y * x * y⁻¹) := h1
          _ = y * (a * x) * y⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h2)
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (mem_centralizer_iff.mp (mem_centralizer_of_card_le_two hcard hyN) x hx)

end Q81

end CFSG.ComponentClassification.HarrisLit
