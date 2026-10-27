module

public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

def centMod (X Y : Subgroup G) (g : G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ g * x * g⁻¹ * x⁻¹ ∈ Y}

private lemma le_normalizer_of_commutator_le {X Y : Subgroup G} (hYX : Y ≤ X)
    (hXX : ⁅X, X⁆ ≤ Y) : X ≤ Subgroup.normalizer (Y : Set G) := by
  rw [Subgroup.le_normalizer_iff_commutator_le_right]
  exact (Subgroup.commutator_mono le_rfl hYX).trans hXX

theorem mem_centMod_iff {X Y : Subgroup G} (hYX : Y ≤ X) (hXX : ⁅X, X⁆ ≤ Y) {g : G}
    {x : G} : x ∈ centMod X Y g ↔ x ∈ X ∧ g * x * g⁻¹ * x⁻¹ ∈ Y := by
  have hXN : X ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_of_commutator_le hYX hXX
  have hconjY : ∀ a ∈ X, ∀ b ∈ Y, a * b * a⁻¹ ∈ Y := by
    intro a ha b hb
    exact (Subgroup.mem_normalizer_iff.mp (hXN ha) b).mp hb
  let S : Set G := {x | x ∈ X ∧ g * x * g⁻¹ * x⁻¹ ∈ Y}
  let C : Subgroup G :=
    { carrier := S
      mul_mem' := by
        intro a b ha hb
        rcases ha with ⟨haX, ha⟩
        rcases hb with ⟨hbX, hb⟩
        refine ⟨X.mul_mem haX hbX, ?_⟩
        have hb' : a * (g * b * g⁻¹ * b⁻¹) * a⁻¹ ∈ Y := hconjY a haX _ hb
        rw [show g * (a * b) * g⁻¹ * (a * b)⁻¹ =
          (g * a * g⁻¹ * a⁻¹) * (a * (g * b * g⁻¹ * b⁻¹) * a⁻¹) by group]
        exact Y.mul_mem ha hb'
      one_mem' := ⟨X.one_mem, by simp⟩
      inv_mem' := by
        intro a ha
        rcases ha with ⟨haX, ha⟩
        refine ⟨X.inv_mem haX, ?_⟩
        have h := hconjY a⁻¹ (X.inv_mem haX) (g * a * g⁻¹ * a⁻¹)⁻¹ (Y.inv_mem ha)
        have hid : a⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ =
            g * a⁻¹ * g⁻¹ * (a⁻¹)⁻¹ := by group
        rwa [hid] at h }
  have hC : centMod X Y g = C := by
    refine le_antisymm ?_ ?_
    · exact (Subgroup.closure_le C).mpr (fun x hx => hx)
    · exact Subgroup.subset_closure
  rw [hC]
  exact Iff.rfl

theorem centMod_le (X Y : Subgroup G) (g : G) : centMod X Y g ≤ X :=
  (Subgroup.closure_le X).mpr (fun x hx => hx.1)

theorem le_centMod {X Y : Subgroup G} (hYX : Y ≤ X) (hXX : ⁅X, X⁆ ≤ Y) {g : G}
    (hgY : g ∈ Subgroup.normalizer (Y : Set G)) : Y ≤ centMod X Y g := by
  intro y hy
  rw [mem_centMod_iff hYX hXX]
  exact ⟨hYX hy, Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hgY y).mp hy) (Y.inv_mem hy)⟩

theorem inf_centMod_le_mul {X Y : Subgroup G} (hYX : Y ≤ X) (hXX : ⁅X, X⁆ ≤ Y) {g₁ g₂ : G}
    (hg₁Y : g₁ ∈ Subgroup.normalizer (Y : Set G))
    (hg₂Y : g₂ ∈ Subgroup.normalizer (Y : Set G)) :
    centMod X Y g₁ ⊓ centMod X Y g₂ ≤ centMod X Y (g₁ * g₂) := by
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hx₁, hx₂⟩ := hx
  rw [mem_centMod_iff hYX hXX] at hx₁
  rw [mem_centMod_iff hYX hXX] at hx₂
  rw [mem_centMod_iff hYX hXX]
  refine ⟨hx₁.1, ?_⟩
  have h₁ : g₁ * (g₂ * x * g₂⁻¹ * x⁻¹) * g₁⁻¹ ∈ Y :=
    (Subgroup.mem_normalizer_iff.mp hg₁Y _).mp hx₂.2
  rw [show g₁ * g₂ * x * (g₁ * g₂)⁻¹ * x⁻¹ =
    (g₁ * (g₂ * x * g₂⁻¹ * x⁻¹) * g₁⁻¹) * (g₁ * x * g₁⁻¹ * x⁻¹) by group]
  exact Y.mul_mem h₁ hx₁.2

private lemma commutator_inv_mem_of_commutator_mem {Y : Subgroup G} {h x : G}
    (hhY : h ∈ Subgroup.normalizer (Y : Set G)) (hx : h * x * h⁻¹ * x⁻¹ ∈ Y) :
    h⁻¹ * x * h * x⁻¹ ∈ Y := by
  have hzy : h * (h⁻¹ * x * h * x⁻¹) * h⁻¹ ∈ Y := by
    rw [show h * (h⁻¹ * x * h * x⁻¹) * h⁻¹ = (h * x * h⁻¹ * x⁻¹)⁻¹ by group]
    exact Y.inv_mem hx
  exact (Subgroup.mem_normalizer_iff.mp hhY _).mpr hzy

theorem centMod_inv {X Y : Subgroup G} (hYX : Y ≤ X) (hXX : ⁅X, X⁆ ≤ Y) {g : G}
    (hgY : g ∈ Subgroup.normalizer (Y : Set G)) :
    centMod X Y g⁻¹ = centMod X Y g := by
  have hgY' : g⁻¹ ∈ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normalizer (Y : Set G)).inv_mem hgY
  apply le_antisymm
  · intro x hx
    rw [mem_centMod_iff hYX hXX] at hx
    rw [mem_centMod_iff hYX hXX]
    exact ⟨hx.1, by simpa using commutator_inv_mem_of_commutator_mem hgY' hx.2⟩
  · intro x hx
    rw [mem_centMod_iff hYX hXX] at hx
    rw [mem_centMod_iff hYX hXX]
    exact ⟨hx.1, by simpa using commutator_inv_mem_of_commutator_mem hgY hx.2⟩

theorem centMod_mul_of_forall_of_normalizer {X Y : Subgroup G} (hYX : Y ≤ X)
    (hXX : ⁅X, X⁆ ≤ Y) {g c : G} (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    (hcY : c ∈ Subgroup.normalizer (Y : Set G))
    (hc : ∀ x ∈ X, c * x * c⁻¹ * x⁻¹ ∈ Y) :
    centMod X Y (g * c) = centMod X Y g := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxX, hxcomm⟩ := (mem_centMod_iff hYX hXX).mp hx
    have h1 : g * (c * x * c⁻¹ * x⁻¹) * g⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hgY _).mp (hc x hxX)
    rw [show g * c * x * (g * c)⁻¹ * x⁻¹ =
      (g * (c * x * c⁻¹ * x⁻¹) * g⁻¹) * (g * x * g⁻¹ * x⁻¹) by group] at hxcomm
    exact (mem_centMod_iff hYX hXX).mpr
      ⟨hxX, (Subgroup.mul_mem_cancel_left Y h1).mp hxcomm⟩
  · intro hx
    obtain ⟨hxX, hxcomm⟩ := (mem_centMod_iff hYX hXX).mp hx
    have h1 : g * (c * x * c⁻¹ * x⁻¹) * g⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hgY _).mp (hc x hxX)
    refine (mem_centMod_iff hYX hXX).mpr ⟨hxX, ?_⟩
    rw [show g * c * x * (g * c)⁻¹ * x⁻¹ =
      (g * (c * x * c⁻¹ * x⁻¹) * g⁻¹) * (g * x * g⁻¹ * x⁻¹) by group]
    exact Y.mul_mem h1 hxcomm

theorem commutator_le_of_forall_centralizes {X Y L : Subgroup G}
    (h : ∀ l ∈ L, ∀ x ∈ X, l * x * l⁻¹ * x⁻¹ ∈ Y) : ⁅X, L⁆ ≤ Y := by
  rw [Subgroup.commutator_le]
  intro x hx l hl
  have h1 : ⁅l, x⁆ ∈ Y := h l hl x hx
  have h2 : ⁅x, l⁆ = ⁅l, x⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [h2]
  exact Y.inv_mem h1

private lemma mem_centMod_conj_iff {X Y : Subgroup G} (hYX : Y ≤ X) (hXX : ⁅X, X⁆ ≤ Y)
    {g m : G} (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    (hmX : m ∈ Subgroup.normalizer (X : Set G))
    (hmY : m ∈ Subgroup.normalizer (Y : Set G)) {x : G} :
    x ∈ centMod X Y (m * g * m⁻¹) ↔
      x ∈ (centMod X Y g).map (MulAut.conj m).toMonoidHom := by
  have hmX' : m⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).inv_mem hmX
  constructor
  · intro hx
    rw [mem_centMod_iff hYX hXX] at hx
    have hyX : m⁻¹ * x * m ∈ X := by
      simpa using (Subgroup.mem_normalizer_iff.mp hmX' x).mp hx.1
    have hyY : g * (m⁻¹ * x * m) * g⁻¹ * (m⁻¹ * x * m)⁻¹ ∈ Y := by
      have h : m * (g * (m⁻¹ * x * m) * g⁻¹ * (m⁻¹ * x * m)⁻¹) * m⁻¹ ∈ Y := by
        rw [show m * (g * (m⁻¹ * x * m) * g⁻¹ * (m⁻¹ * x * m)⁻¹) * m⁻¹ =
          m * g * m⁻¹ * x * (m * g * m⁻¹)⁻¹ * x⁻¹ by group]
        exact hx.2
      exact (Subgroup.mem_normalizer_iff.mp hmY _).mpr h
    refine Subgroup.mem_map.mpr ⟨m⁻¹ * x * m, ?_, ?_⟩
    · rw [mem_centMod_iff hYX hXX]
      exact ⟨hyX, hyY⟩
    · change m * (m⁻¹ * x * m) * m⁻¹ = x
      group
  · intro hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_centMod_iff hYX hXX] at hy
    rw [mem_centMod_iff hYX hXX]
    refine ⟨(Subgroup.mem_normalizer_iff.mp hmX y).mp hy.1, ?_⟩
    have h : m * (g * y * g⁻¹ * y⁻¹) * m⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hmY _).mp hy.2
    simpa [MulAut.conj_apply, mul_assoc] using h

theorem centMod_conj {X Y : Subgroup G} (hYX : Y ≤ X) (hXX : ⁅X, X⁆ ≤ Y) {g : G}
    (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    {m : G} (hmX : m ∈ Subgroup.normalizer (X : Set G))
    (hmY : m ∈ Subgroup.normalizer (Y : Set G)) :
    centMod X Y (m * g * m⁻¹) = (centMod X Y g).map (MulAut.conj m).toMonoidHom := by
  ext x
  exact mem_centMod_conj_iff hYX hXX hgY hmX hmY

theorem relIndex_centMod_conj {X Y : Subgroup G} (hYX : Y ≤ X) (hXX : ⁅X, X⁆ ≤ Y) {g : G}
    (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    {m : G} (hmX : m ∈ Subgroup.normalizer (X : Set G))
    (hmY : m ∈ Subgroup.normalizer (Y : Set G)) :
    (centMod X Y (m * g * m⁻¹)).relIndex X = (centMod X Y g).relIndex X := by
  have hXmap : X.map (MulAut.conj m).toMonoidHom = X :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hmX
  rw [centMod_conj hYX hXX hgY hmX hmY]
  calc
    ((centMod X Y g).map (MulAut.conj m).toMonoidHom).relIndex X =
        ((centMod X Y g).map (MulAut.conj m).toMonoidHom).relIndex
          (X.map (MulAut.conj m).toMonoidHom) := by rw [hXmap]
    _ = (centMod X Y g).relIndex X :=
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj m).injective

private lemma zpowers_mk'_eq_top_of_cyclic {T T₀ : Subgroup G} [hT0 : (T₀.subgroupOf T).Normal]
    (hT₀T : T₀ ≤ T)
    (hTN : T ≤ Subgroup.normalizer (T₀ : Set G)) {g₀ : G} (hg₀ : g₀ ∈ T)
    (hcyc : T ≤ T₀ ⊔ Subgroup.zpowers g₀) :
    Subgroup.zpowers (QuotientGroup.mk' (T₀.subgroupOf T) ⟨g₀, hg₀⟩) = ⊤ := by
  let T0 : Subgroup T := T₀.subgroupOf T
  haveI hT0N : T0.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T).mpr hTN
  let gT : T := ⟨g₀, hg₀⟩
  let q : T ⧸ T0 := QuotientGroup.mk' T0 gT
  rw [eq_top_iff]
  intro y _
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective T0 y
  have hsupT : (T₀ ⊔ Subgroup.zpowers g₀).subgroupOf T =
      T0 ⊔ (Subgroup.zpowers g₀).subgroupOf T :=
    Subgroup.subgroupOf_sup hT₀T (Subgroup.zpowers_le_of_mem hg₀)
  have ht : t ∈ T0 ⊔ (Subgroup.zpowers g₀).subgroupOf T := by
    rw [← hsupT]
    exact Subgroup.mem_subgroupOf.mpr (hcyc t.2)
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp ht
  have hbG : (b : G) ∈ Subgroup.zpowers g₀ := Subgroup.mem_subgroupOf.mp hb
  have ht_eq : t = a * b := hab.symm
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbG
  have hb_eq : b = gT ^ k := Subtype.ext hk.symm
  have ha1 : QuotientGroup.mk' T0 a = 1 := by
    simpa [QuotientGroup.coe_mk'] using (QuotientGroup.eq_one_iff (x := a)).mpr ha
  have hcalc : QuotientGroup.mk' T0 t = QuotientGroup.mk' T0 (gT ^ k) := by
    calc
      QuotientGroup.mk' T0 t = QuotientGroup.mk' T0 (a * b) := by rw [ht_eq]
      _ = QuotientGroup.mk' T0 a * QuotientGroup.mk' T0 b := map_mul _ _ _
      _ = QuotientGroup.mk' T0 b := by rw [ha1, one_mul]
      _ = QuotientGroup.mk' T0 (gT ^ k) := by rw [hb_eq]
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨k, by simpa [q] using hcalc.symm⟩

private lemma exists_generator_of_cyclic_section {X T T₀ : Subgroup G}
    [hT0 : (T₀.subgroupOf T).Normal] (hXT : X ≤ T)
    (hT₀T : T₀ ≤ T) (hTN : T ≤ Subgroup.normalizer (T₀ : Set G)) {g₀ : G} (hg₀ : g₀ ∈ T)
    (hcyc : T ≤ T₀ ⊔ Subgroup.zpowers g₀) :
    ∃ x₀ : T, x₀ ∈ X.subgroupOf T ∧ ∀ x : X, ∃ k : ℤ,
      QuotientGroup.mk' (T₀.subgroupOf T) ⟨x, hXT x.2⟩ =
        (QuotientGroup.mk' (T₀.subgroupOf T) x₀) ^ k := by
  classical
  let T0 : Subgroup T := T₀.subgroupOf T
  haveI hT0N : T0.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T).mpr hTN
  have hqtop : Subgroup.zpowers (QuotientGroup.mk' T0 ⟨g₀, hg₀⟩) = ⊤ :=
    zpowers_mk'_eq_top_of_cyclic hT₀T hTN hg₀ hcyc
  let S : Subgroup (T ⧸ T0) := (X.subgroupOf T).map (QuotientGroup.mk' T0)
  obtain ⟨i, hi⟩ := Subgroup.exists_zpowers_eq_of_zpowers_eq_top hqtop S
  have hqi : (QuotientGroup.mk' T0 ⟨g₀, hg₀⟩) ^ i ∈ S := by
    rw [← hi]
    exact Subgroup.mem_zpowers _
  obtain ⟨x₀, hx₀, hx₀eq⟩ := Subgroup.mem_map.mp hqi
  refine ⟨x₀, hx₀, ?_⟩
  intro x
  have hxS : QuotientGroup.mk' T0 ⟨x, hXT x.2⟩ ∈ S :=
    Subgroup.mem_map.mpr ⟨⟨x, hXT x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
  rw [← hi] at hxS
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxS
  refine ⟨k, ?_⟩
  calc
    QuotientGroup.mk' T0 ⟨x, hXT x.2⟩ =
        ((QuotientGroup.mk' T0 ⟨g₀, hg₀⟩) ^ i) ^ k := hk.symm
    _ = (QuotientGroup.mk' T0 x₀) ^ k := by rw [← hx₀eq]

private lemma exists_decomp_of_generator {X T T₀ : Subgroup G}
    [hT0 : (T₀.subgroupOf T).Normal] (hXT : X ≤ T)
    (hTN : T ≤ Subgroup.normalizer (T₀ : Set G)) {x₀ : T}
    (hx₀ : x₀ ∈ X.subgroupOf T)
    (hgen : ∀ x : X, ∃ k : ℤ,
      QuotientGroup.mk' (T₀.subgroupOf T) ⟨x, hXT x.2⟩ =
        (QuotientGroup.mk' (T₀.subgroupOf T) x₀) ^ k) :
    ∀ x ∈ X, ∃ (k : ℤ) (t : G), t ∈ X ⊓ T₀ ∧ x = t * (x₀ : G) ^ k := by
  intro x hxX
  obtain ⟨k, hk⟩ := hgen ⟨x, hxX⟩
  let T0 : Subgroup T := T₀.subgroupOf T
  have heq : ((⟨x, hXT hxX⟩ : T) : T ⧸ T0) = ((x₀ ^ k) : T ⧸ T0) := by
    simpa [T0, QuotientGroup.coe_mk'] using hk
  have hmemT0 : (⟨x, hXT hxX⟩ : T)⁻¹ * x₀ ^ k ∈ T0 := QuotientGroup.eq.mp heq
  have hmemG : x⁻¹ * (x₀ : G) ^ k ∈ T₀ := by
    simpa [T0] using (Subgroup.mem_subgroupOf.mp hmemT0)
  let t : G := x * ((x₀ : G) ^ k)⁻¹
  have htT₀ : t ∈ T₀ := by
    have hinv : (x⁻¹ * (x₀ : G) ^ k)⁻¹ ∈ T₀ := T₀.inv_mem hmemG
    have hconj : x * (x⁻¹ * (x₀ : G) ^ k)⁻¹ * x⁻¹ ∈ T₀ :=
      (Subgroup.mem_normalizer_iff.mp (hTN (hXT hxX)) _).mp hinv
    have hid : x * (x⁻¹ * (x₀ : G) ^ k)⁻¹ * x⁻¹ = t := by
      rw [mul_inv_rev, inv_inv]
      dsimp [t]
      group
    rwa [hid] at hconj
  have hx₀X : (x₀ : G) ∈ X := Subgroup.mem_subgroupOf.mp hx₀
  have htX : t ∈ X := X.mul_mem hxX (X.inv_mem (X.zpow_mem hx₀X k))
  exact ⟨k, t, ⟨htX, htT₀⟩, by dsimp [t]; group⟩

private theorem relIndex_sup_inf_dvd_two {X Y T T₀ : Subgroup G} (hXT : X ≤ T)
    (hT₀T : T₀ ≤ T) (hTN : T ≤ Subgroup.normalizer (T₀ : Set G)) {g₀ : G} (hg₀ : g₀ ∈ T)
    (hcyc : T ≤ T₀ ⊔ Subgroup.zpowers g₀) (hsq : ∀ x ∈ X, x * x ∈ Y) :
    ((X ⊓ T₀) ⊔ Y).relIndex X ∣ 2 := by
  classical
  haveI hT0N : (T₀.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T).mpr hTN
  obtain ⟨x₀, hx₀, hgen⟩ := exists_generator_of_cyclic_section hXT hT₀T hTN hg₀ hcyc
  have hdecomp := exists_decomp_of_generator hXT hTN hx₀ hgen
  have hx₀X : (x₀ : G) ∈ X := Subgroup.mem_subgroupOf.mp hx₀
  refine (Subgroup.relIndex_dvd_two_iff).mpr ⟨(x₀ : G), hx₀X, ?_⟩
  intro b hbX
  obtain ⟨k, t, ht, rfl⟩ := hdecomp b hbX
  have hx₀sq : (x₀ : G) ^ 2 ∈ Y := by simpa [pow_two] using hsq (x₀ : G) hx₀X
  have hT0leM : X ⊓ T₀ ≤ (X ⊓ T₀) ⊔ Y := le_sup_left
  have hYleM : Y ≤ (X ⊓ T₀) ⊔ Y := le_sup_right
  rcases Int.even_or_odd' k with ⟨j, hj | hj⟩
  · right
    rw [hj]
    have hpow : (x₀ : G) ^ (2 * j) = ((x₀ : G) ^ 2) ^ j := by
      rw [zpow_mul]
      norm_num
    rw [hpow]
    exact Subgroup.mul_mem ((X ⊓ T₀) ⊔ Y) (hT0leM ht) (hYleM (Y.zpow_mem hx₀sq j))
  · left
    rw [hj]
    have hpow : (x₀ : G) ^ (2 * j + 1) * (x₀ : G) = ((x₀ : G) ^ 2) ^ (j + 1) := by
      rw [← zpow_add_one, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, zpow_mul]
      norm_num
    rw [mul_assoc, hpow]
    exact Subgroup.mul_mem ((X ⊓ T₀) ⊔ Y) (hT0leM ht)
      (hYleM (Y.zpow_mem hx₀sq (j + 1)))

theorem relIndex_centMod_le_two {X Y T T₀ : Subgroup G} (hYX : Y ≤ X)
    (hXX : ⁅X, X⁆ ≤ Y) (hXT : X ≤ T) (hT₀T : T₀ ≤ T)
    (hTN : T ≤ Subgroup.normalizer (T₀ : Set G)) {g₀ : G} (hg₀ : g₀ ∈ T)
    (hcyc : T ≤ T₀ ⊔ Subgroup.zpowers g₀) (hsq : ∀ x ∈ X, x * x ∈ Y)
    {g : G} (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    (hv : ∀ x ∈ X ⊓ T₀, g * x * g⁻¹ * x⁻¹ ∈ Y) :
    (centMod X Y g).relIndex X ≤ 2 := by
  have h1 : X ⊓ T₀ ≤ centMod X Y g := by
    intro x hx
    rw [mem_centMod_iff hYX hXX]
    exact ⟨hx.1, hv x hx⟩
  have h2 : Y ≤ centMod X Y g := le_centMod hYX hXX hgY
  have hM : (X ⊓ T₀) ⊔ Y ≤ centMod X Y g := sup_le h1 h2
  have hdvd : (centMod X Y g).relIndex X ∣ 2 :=
    (Subgroup.relIndex_dvd_of_le_left (L := X) hM).trans
      (relIndex_sup_inf_dvd_two hXT hT₀T hTN hg₀ hcyc hsq)
  exact Nat.le_of_dvd (by norm_num) hdvd

private lemma commutator_eq_one_of_odd_pow {H : Type*} [Group H] {q x : H} {m : ℕ}
    (hm : Odd m) (hc : Commute q ⁅q, x⁆) (h2 : ⁅q, x⁆ ^ 2 = 1)
    (hm1 : ⁅q ^ m, x⁆ = 1) : ⁅q, x⁆ = 1 := by
  have h : ⁅q, x⁆ ^ m = 1 := by
    rw [Commute.commutatorElement_pow_left hc, hm1]
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at h
  exact h

private lemma commutator_mem_of_odd_pow_quotient {X Y W K : Subgroup G}
    [hYKN : (Y.subgroupOf K).Normal] (hWX : W ≤ X)
    (hsq : ∀ x ∈ X, x * x ∈ Y) {g a x : G} (hgK : g ∈ K) (hXK : X ≤ K) (hYK : Y ≤ K)
    (hKNY : K ≤ Subgroup.normalizer (Y : Set G))
    (hW : ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ Y) (haW : a ∈ W) (hxX : x ∈ X)
    (ha : a = g * x * g⁻¹ * x⁻¹) {m : ℕ} (hm : Odd m)
    (hgm : ∀ y ∈ X, g ^ m * y * (g ^ m)⁻¹ * y⁻¹ ∈ Y) :
    (QuotientGroup.mk' (Y.subgroupOf K)) ⟨a, hXK (hWX haW)⟩ = 1 := by
  let YK : Subgroup K := Y.subgroupOf K
  haveI hYKN' : YK.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).mpr hKNY
  let gK : K := ⟨g, hgK⟩
  let xK : K := ⟨x, hXK hxX⟩
  let aK : K := ⟨a, hXK (hWX haW)⟩
  let qg : K ⧸ YK := QuotientGroup.mk' YK gK
  let qx : K ⧸ YK := QuotientGroup.mk' YK xK
  let qa : K ⧸ YK := QuotientGroup.mk' YK aK
  have hqa : ⁅qg, qx⁆ = qa := by
    rw [← map_commutatorElement (QuotientGroup.mk' YK) gK xK]
    exact congrArg _ (Subtype.ext (by simp [aK, gK, xK, ha, commutatorElement_def]))
  have hcomm : Commute qg ⁅qg, qx⁆ := by
    rw [hqa, ← commutatorElement_eq_one_iff_commute,
      ← map_commutatorElement (QuotientGroup.mk' YK) gK aK, QuotientGroup.coe_mk',
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [aK, commutatorElement_def] using hW a haW
  have h2 : (⁅qg, qx⁆) ^ 2 = 1 := by
    rw [hqa, show ((QuotientGroup.mk' YK) aK) ^ 2 =
        (QuotientGroup.mk' YK) (aK ^ 2) from (map_pow _ _ _).symm,
      QuotientGroup.coe_mk', QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [aK, pow_two] using hsq a (hWX haW)
  have hqm : ⁅qg ^ m, qx⁆ = 1 := by
    rw [show qg ^ m = (QuotientGroup.mk' YK) (gK ^ m) by simp [qg],
      ← map_commutatorElement (QuotientGroup.mk' YK) (gK ^ m) xK, QuotientGroup.coe_mk',
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa [commutatorElement_def] using hgm x hxX
  have ha1 : ⁅qg, qx⁆ = 1 := commutator_eq_one_of_odd_pow hm hcomm h2 hqm
  rw [hqa] at ha1
  exact ha1

theorem pow_commutator_mem_of_commutator_mem {Y P : Subgroup G} {g : G}
    (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    (h : ∀ p ∈ P, g * p * g⁻¹ * p⁻¹ ∈ Y) (n : ℕ) :
    ∀ p ∈ P, g ^ n * p * (g ^ n)⁻¹ * p⁻¹ ∈ Y := by
  induction n with
  | zero =>
    intro p _
    simp
  | succ n ih =>
    intro p hp
    have hgY' : g ^ n ∈ Subgroup.normalizer (Y : Set G) :=
      (Subgroup.normalizer (Y : Set G)).pow_mem hgY n
    have h1 : g ^ n * (g * p * g⁻¹ * p⁻¹) * (g ^ n)⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp hgY' _).mp (h p hp)
    rw [show g ^ (n + 1) * p * (g ^ (n + 1))⁻¹ * p⁻¹ =
      (g ^ n * (g * p * g⁻¹ * p⁻¹) * (g ^ n)⁻¹) *
        (g ^ n * p * (g ^ n)⁻¹ * p⁻¹) by
      rw [pow_succ]
      group]
    exact Y.mul_mem h1 (ih p hp)

theorem commutator_mem_of_odd_pow {X Y W : Subgroup G} (hWX : W ≤ X) (hYX : Y ≤ X)
    (hXX : ⁅X, X⁆ ≤ Y) (hsq : ∀ x ∈ X, x * x ∈ Y) {g : G}
    (hgY : g ∈ Subgroup.normalizer (Y : Set G))
    (hW : ∀ w ∈ W, g * w * g⁻¹ * w⁻¹ ∈ Y)
    (hXW : ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ W) {m : ℕ} (hm : Odd m)
    (hgm : ∀ x ∈ X, g ^ m * x * (g ^ m)⁻¹ * x⁻¹ ∈ Y) :
    ∀ x ∈ X, g * x * g⁻¹ * x⁻¹ ∈ Y := by
  intro x hxX
  let K : Subgroup G := Subgroup.closure ({g} ∪ (X : Set G))
  have hgK : g ∈ K := Subgroup.subset_closure (Set.mem_union_left _ (Set.mem_singleton g))
  have hXK : X ≤ K := fun y hy => Subgroup.subset_closure (Set.mem_union_right _ hy)
  have hYK : Y ≤ K := hYX.trans hXK
  have hXNY : X ≤ Subgroup.normalizer (Y : Set G) := le_normalizer_of_commutator_le hYX hXX
  have hKNY : K ≤ Subgroup.normalizer (Y : Set G) := by
    refine (Subgroup.closure_le (Subgroup.normalizer (Y : Set G))).mpr ?_
    intro y hy
    rcases hy with hy | hy
    · rw [Set.mem_singleton_iff] at hy
      simpa [hy] using hgY
    · exact hXNY hy
  haveI hYKN : (Y.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYK).mpr hKNY
  let a : G := g * x * g⁻¹ * x⁻¹
  have haW : a ∈ W := hXW x hxX
  have hqa : (QuotientGroup.mk' (Y.subgroupOf K)) ⟨a, hXK (hWX haW)⟩ = 1 :=
    commutator_mem_of_odd_pow_quotient hWX hsq hgK hXK hYK hKNY hW haW hxX rfl hm hgm
  have hmem : (⟨a, hXK (hWX haW)⟩ : K) ∈ Y.subgroupOf K :=
    (QuotientGroup.eq_one_iff (x := (⟨a, hXK (hWX haW)⟩ : K))).mp hqa
  exact Subgroup.mem_subgroupOf.mp hmem

private lemma perm_pow_twentyFour_eq_one {α : Type*} [Finite α] (σ : Equiv.Perm α)
    (h : Nat.card α ≤ 4) : σ ^ 24 = 1 := by
  have h1 : orderOf σ ∣ Nat.card (Equiv.Perm α) := orderOf_dvd_natCard σ
  rw [Nat.card_perm] at h1
  have h2 : Nat.factorial (Nat.card α) ∣ 24 := by
    have h4 : Nat.factorial 4 = 24 := by decide
    rw [← h4]
    exact Nat.factorial_dvd_factorial h
  exact (orderOf_dvd_iff_pow_eq_one).mp (h1.trans h2)

private lemma natCard_quotient_subgroupOf_le_four {X W : Subgroup G}
    (h4 : W.relIndex X ≤ 4) : Nat.card (X ⧸ W.subgroupOf X) ≤ 4 := by
  have hidx : (W.subgroupOf X).index = W.relIndex X := by
    rw [← Subgroup.relIndex_top_right (H := W.subgroupOf X), ← Subgroup.subgroupOf_self X]
    exact Subgroup.relIndex_subgroupOf (H := W) (K := X) (L := X) le_rfl
  rw [← Subgroup.index_eq_card, hidx]
  exact h4

private lemma exists_conj_perm {X W : Subgroup G} [hWN : (W.subgroupOf X).Normal]
    (hWX : W ≤ X) (hXXW : ⁅X, X⁆ ≤ W)
    {g : G} (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) :
    ∃ π : Equiv.Perm (X ⧸ W.subgroupOf X),
      (∀ u : X, π (QuotientGroup.mk' (W.subgroupOf X) u) =
        QuotientGroup.mk' (W.subgroupOf X) (X.normalizerMonoidHom ⟨g, hgX⟩ u)) ∧
      ∀ (k : ℕ) (u : X), (π ^ k) (QuotientGroup.mk' (W.subgroupOf X) u) =
        QuotientGroup.mk' (W.subgroupOf X) ((X.normalizerMonoidHom ⟨g, hgX⟩ ^ k) u) := by
  classical
  have hXW : X ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (Subgroup.commutator_mono le_rfl hWX).trans hXXW
  haveI hWN' : (W.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWX).mpr hXW
  let θ : MulAut X := X.normalizerMonoidHom ⟨g, hgX⟩
  have hθW : (W.subgroupOf X).map θ.toMonoidHom = W.subgroupOf X := by
    ext u
    rw [Subgroup.mem_map_equiv]
    have hsymm : ((θ.symm u : X) : G) = g⁻¹ * (u : G) * g :=
      Subgroup.normalizerMonoidHom_apply_symm_apply_coe X ⟨g, hgX⟩ u
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hsymm]
    exact (Subgroup.mem_normalizer_iff''.mp hgW (u : G)).symm
  let π : Equiv.Perm (X ⧸ W.subgroupOf X) :=
    (QuotientGroup.congr (W.subgroupOf X) (W.subgroupOf X) θ hθW).toEquiv
  have hπ : ∀ u : X, π (QuotientGroup.mk' (W.subgroupOf X) u) =
      QuotientGroup.mk' (W.subgroupOf X) (θ u) :=
    fun u => QuotientGroup.congr_mk _ _ _ _ u
  refine ⟨π, hπ, ?_⟩
  intro k
  induction k with
  | zero => intro u; simp
  | succ k ih =>
    intro u
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, ih, hπ, MulAut.mul_apply]

private lemma normalizerMonoidHom_pow_apply_coe {X : Subgroup G} {g : G}
    (hgX : g ∈ Subgroup.normalizer (X : Set G)) (k : ℕ) (u : X) :
    (((X.normalizerMonoidHom ⟨g, hgX⟩) ^ k) u : G) = g ^ k * (u : G) * (g ^ k)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', MulAut.mul_apply, Subgroup.normalizerMonoidHom_apply_apply_coe, ih]
    group

theorem pow_twentyFour_mem_of_relIndex_le_four [Finite G] {X W : Subgroup G} (hWX : W ≤ X)
    (hXXW : ⁅X, X⁆ ≤ W) {g : G} (hgX : g ∈ Subgroup.normalizer (X : Set G))
    (hgW : g ∈ Subgroup.normalizer (W : Set G)) (h4 : W.relIndex X ≤ 4) :
    ∀ x ∈ X, g ^ 24 * x * (g ^ 24)⁻¹ * x⁻¹ ∈ W := by
  classical
  have hXW : X ≤ Subgroup.normalizer (W : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    exact (Subgroup.commutator_mono le_rfl hWX).trans hXXW
  haveI hWN : (W.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWX).mpr hXW
  obtain ⟨π, hπ, hπpow⟩ := exists_conj_perm hWX hXXW hgX hgW
  have hπ24 : π ^ 24 = 1 :=
    perm_pow_twentyFour_eq_one π (natCard_quotient_subgroupOf_le_four h4)
  intro x hxX
  let θ : MulAut X := X.normalizerMonoidHom ⟨g, hgX⟩
  let xX : X := ⟨x, hxX⟩
  have hfix : (π ^ 24) (QuotientGroup.mk' (W.subgroupOf X) xX) =
      QuotientGroup.mk' (W.subgroupOf X) xX := by
    simp [hπ24]
  have hfix' : QuotientGroup.mk' (W.subgroupOf X) ((θ ^ 24) xX) =
      QuotientGroup.mk' (W.subgroupOf X) xX := by
    rw [← hπpow 24 xX]
    exact hfix
  have hmem : ((θ ^ 24) xX)⁻¹ * xX ∈ W.subgroupOf X := QuotientGroup.eq.mp hfix'
  have hu : (((θ ^ 24) xX : X) : G) = g ^ 24 * x * (g ^ 24)⁻¹ := by
    dsimp [θ, xX]
    rw [normalizerMonoidHom_pow_apply_coe hgX 24 xX]
  have hmemG : (((θ ^ 24) xX : X) : G)⁻¹ * x ∈ W := by
    simpa using (Subgroup.mem_subgroupOf.mp hmem)
  have hux : (((θ ^ 24) xX : X) : G) * x⁻¹ ∈ W := by
    have h1 : ((((θ ^ 24) xX : X) : G)⁻¹ * x)⁻¹ ∈ W := W.inv_mem hmemG
    have h2 : x * ((((θ ^ 24) xX : X) : G)⁻¹ * x)⁻¹ * x⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hXW hxX) _).mp h1
    have hid : x * ((((θ ^ 24) xX : X) : G)⁻¹ * x)⁻¹ * x⁻¹ =
        (((θ ^ 24) xX : X) : G) * x⁻¹ := by
      rw [mul_inv_rev, inv_inv]
      group
    rwa [hid] at h2
  rw [← hu]
  exact hux

end CFSG.GroupTheory
