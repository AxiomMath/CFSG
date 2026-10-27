module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingConjugacy
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs

public section

namespace CFSG.ComponentClassification.AschbacherToolkit

namespace Bender

open CFSG.Open
open scoped commutatorElement

variable {X : Type*} [Group X]

@[expose] def sylowCenter (T : Subgroup X) : Subgroup X :=
  T ⊓ Subgroup.centralizer (T : Set X)

theorem mem_sylowCenter {T : Subgroup X} {z : X} :
    z ∈ sylowCenter T ↔ z ∈ T ∧ ∀ t ∈ T, t * z = z * t := by
  rw [sylowCenter, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem sylowCenter_le (T : Subgroup X) : sylowCenter T ≤ T := inf_le_left

@[expose] def NestedAt (T : Subgroup X) : Prop :=
  ∀ A₁ A₂ : Subgroup X, A₁ ≤ T → A₂ ≤ T → ⁅A₁, A₂⁆ = ⊥ →
    (∀ a ∈ (A₁ : Set X) ∪ A₂, ∀ x : X, x⁻¹ * a * x ∈ T → x⁻¹ * a * x ∈ (A₁ : Set X) ∪ A₂) →
      A₁ ≤ A₂ ∨ A₂ ≤ A₁

theorem NestedAt.map_mulEquiv {Y : Type*} [Group Y] {T : Subgroup X} (h : NestedAt T)
    (e : X ≃* Y) : NestedAt (T.map e.toMonoidHom) := by
  intro B₁ B₂ hB₁ hB₂ hc hcl
  let A₁ := B₁.map e.symm.toMonoidHom
  let A₂ := B₂.map e.symm.toMonoidHom
  have hmapA₁ : A₁.map e.toMonoidHom = B₁ := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id B₁
    ext y
    simp
  have hmapA₂ : A₂.map e.toMonoidHom = B₂ := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id B₂
    ext y
    simp
  have hmemB : ∀ (B : Subgroup Y) (x : X), x ∈ B.map e.symm.toMonoidHom ↔ e x ∈ B := by
    intro B x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, hx, by simp⟩
  have hmemT : ∀ x : X, x ∈ T ↔ e x ∈ T.map e.toMonoidHom := by
    intro x
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x', hx', hxx'⟩
      have : x' = x := e.injective hxx'
      rwa [← this]
  have hA₁ : A₁ ≤ T := fun x hx => (hmemT x).mpr (hB₁ ((hmemB B₁ x).mp hx))
  have hA₂ : A₂ ≤ T := fun x hx => (hmemT x).mpr (hB₂ ((hmemB B₂ x).mp hx))
  have hcA : ⁅A₁, A₂⁆ = ⊥ := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_commutator, hmapA₁, hmapA₂, hc, Subgroup.map_bot]
  have hclA : ∀ a ∈ (A₁ : Set X) ∪ A₂, ∀ x : X, x⁻¹ * a * x ∈ T →
      x⁻¹ * a * x ∈ (A₁ : Set X) ∪ A₂ := by
    intro a ha x hx
    have ha' : e a ∈ (B₁ : Set Y) ∪ B₂ := by
      rcases ha with ha | ha
      · exact Or.inl ((hmemB B₁ a).mp ha)
      · exact Or.inr ((hmemB B₂ a).mp ha)
    have hx' : (e x)⁻¹ * e a * e x ∈ T.map e.toMonoidHom := by
      have := (hmemT _).mp hx
      simpa using this
    have h2 := hcl (e a) ha' (e x) hx'
    have h3 : (e x)⁻¹ * e a * e x = e (x⁻¹ * a * x) := by simp
    rw [h3] at h2
    rcases h2 with h2 | h2
    · exact Or.inl ((hmemB B₁ _).mpr h2)
    · exact Or.inr ((hmemB B₂ _).mpr h2)
  rcases h A₁ A₂ hA₁ hA₂ hcA hclA with hle | hle
  · left
    rw [← hmapA₁, ← hmapA₂]
    exact Subgroup.map_mono hle
  · right
    rw [← hmapA₁, ← hmapA₂]
    exact Subgroup.map_mono hle

theorem NestedAt.conj {T : Subgroup X} (h : NestedAt T) (g : X) :
    NestedAt (T.map (MulAut.conj g).toMonoidHom) := by
  have := h.map_mulEquiv (MulAut.conj g)
  exact this

theorem nestedAt_of_one_sylow [Finite X] (R : Sylow 2 X) (h : NestedAt (R : Subgroup X))
    (T : Sylow 2 X) : NestedAt (T : Subgroup X) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R T
  have hT : (T : Subgroup X) = (R : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  rw [hT]
  exact h.conj g

theorem isStronglyEmbedded_of_fusion [Finite X] {M : Subgroup X}
    (hM : fusionStronglyEmbedded M) : CFSG.BenderSuzuki.IsStronglyEmbedded M := by
  apply CFSG.BenderSuzuki.isStronglyEmbedded_of_parity
  refine ⟨hM.1, hM.2.1, fun g hg => ?_⟩
  have hg' : g⁻¹ ∉ M := fun h => hg (by simpa using M.inv_mem h)
  simpa using hM.2.2 g⁻¹ hg'

theorem normalizer_transitive_center [Finite X] {T : Subgroup X}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer (T : Set X)))
    (hZ : ∀ z ∈ sylowCenter T, z ^ 2 = 1) {z₁ z₂ : X} (hz₁ : z₁ ∈ sylowCenter T)
    (hz₂ : z₂ ∈ sylowCenter T) (h₁ : z₁ ≠ 1) (h₂ : z₂ ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (T : Set X), n⁻¹ * z₁ * n = z₂ := by
  have hM := isStronglyEmbedded_of_fusion hSE
  have hmem : ∀ z ∈ sylowCenter T, z ∈ Subgroup.normalizer (T : Set X) := fun z hz =>
    Subgroup.le_normalizer (sylowCenter_le T hz)
  obtain ⟨g, hg, hgz⟩ := hM.involutions_conjugate_in (hmem z₁ hz₁) ⟨h₁, hZ z₁ hz₁⟩
    (hmem z₂ hz₂) ⟨h₂, hZ z₂ hz₂⟩
  exact ⟨g, hg, hgz⟩

theorem nested_of_le_center [Finite X] {T : Subgroup X}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer (T : Set X)))
    (hZ : ∀ z ∈ sylowCenter T, z ^ 2 = 1) {A₁ A₂ : Subgroup X}
    (h₁ : A₁ ≤ sylowCenter T) (h₂ : A₂ ≤ sylowCenter T)
    (hcl : ∀ a ∈ (A₁ : Set X) ∪ A₂, ∀ x : X, x⁻¹ * a * x ∈ T →
      x⁻¹ * a * x ∈ (A₁ : Set X) ∪ A₂) :
    A₁ ≤ A₂ ∨ A₂ ≤ A₁ := by
  by_cases hbot : A₁ ⊔ A₂ = ⊥
  · left
    have : A₁ = ⊥ := eq_bot_iff.mpr (le_sup_left.trans hbot.le)
    rw [this]
    exact bot_le
  obtain ⟨a, haU, ha1⟩ : ∃ a ∈ (A₁ : Set X) ∪ A₂, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hbot
    rw [eq_bot_iff, sup_le_iff]
    exact ⟨fun x hx => hcon x (Or.inl hx), fun x hx => hcon x (Or.inr hx)⟩
  have haZ : a ∈ sylowCenter T := by
    rcases haU with h | h
    · exact h₁ h
    · exact h₂ h
  have hZsub : ((sylowCenter T : Subgroup X) : Set X) ⊆ (A₁ : Set X) ∪ A₂ := by
    intro z hz
    by_cases hz1 : z = 1
    · rw [hz1]
      exact Or.inl A₁.one_mem
    obtain ⟨n, hn, hnz⟩ := normalizer_transitive_center hSE hZ haZ hz ha1 hz1
    have hmemT : n⁻¹ * a * n ∈ T := by
      rw [hnz]
      exact sylowCenter_le T hz
    have := hcl a haU n hmemT
    rwa [hnz] at this
  rcases SubgroupClass.subset_union.mp hZsub with hle | hle
  · right
    exact h₂.trans hle
  · left
    exact h₁.trans hle

theorem nestedAt_of_abelian [Finite X] {T : Subgroup X}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer (T : Set X)))
    (hZ : ∀ z ∈ sylowCenter T, z ^ 2 = 1) (hab : T ≤ sylowCenter T) : NestedAt T :=
  fun _ _ h₁ h₂ _ hcl => nested_of_le_center hSE hZ (h₁.trans hab) (h₂.trans hab) hcl

theorem eq_of_le_mul_center {T A : Subgroup X} (hAT : A ≤ T)
    (hcov : ∀ t ∈ T, ∃ a ∈ A, ∃ z ∈ sylowCenter T, t = a * z)
    (hZT : sylowCenter T ≤ ⁅T, T⁆) : A = T := by
  apply le_antisymm hAT
  have hcomm : ⁅T, T⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro t ht t' ht'
    obtain ⟨a, ha, z, hz, rfl⟩ := hcov t ht
    obtain ⟨a', ha', z', hz', rfl⟩ := hcov t' ht'
    have hzc := (mem_sylowCenter.mp hz).2
    have hz'c := (mem_sylowCenter.mp hz').2
    have h1 : ⁅a * z, a' * z'⁆ = ⁅a, a'⁆ := by
      have e1 : a' * z = z * a' := hzc a' (hAT ha')
      have e2 : a * z' = z' * a := hz'c a (hAT ha)
      have e3 : z * z' = z' * z := hz'c z (sylowCenter_le T hz)
      simp only [commutatorElement_def]
      calc a * z * (a' * z') * (a * z)⁻¹ * (a' * z')⁻¹
          = a * (z * a') * z' * z⁻¹ * a⁻¹ * z'⁻¹ * a'⁻¹ := by group
        _ = a * (a' * z) * z' * z⁻¹ * a⁻¹ * z'⁻¹ * a'⁻¹ := by rw [e1]
        _ = a * a' * (z * z') * z⁻¹ * a⁻¹ * z'⁻¹ * a'⁻¹ := by group
        _ = a * a' * (z' * z) * z⁻¹ * a⁻¹ * z'⁻¹ * a'⁻¹ := by rw [e3]
        _ = a * a' * z' * a⁻¹ * z'⁻¹ * a'⁻¹ := by group
        _ = a * a' * (z' * a⁻¹) * z'⁻¹ * a'⁻¹ := by group
        _ = a * a' * (a⁻¹ * z') * z'⁻¹ * a'⁻¹ := by
          have e4 : z' * a⁻¹ = a⁻¹ * z' := by
            calc z' * a⁻¹ = a⁻¹ * (a * z') * a⁻¹ := by group
              _ = a⁻¹ * (z' * a) * a⁻¹ := by rw [e2]
              _ = a⁻¹ * z' := by group
          rw [e4]
        _ = a * a' * a⁻¹ * a'⁻¹ := by group
    rw [h1, commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha ha') (A.inv_mem ha)) (A.inv_mem ha')
  intro t ht
  obtain ⟨a, ha, z, hz, rfl⟩ := hcov t ht
  exact A.mul_mem ha (hcomm (hZT hz))

@[expose] def mulCenter (T A : Subgroup X) (hA : A ≤ T) : Subgroup X where
  carrier := {t | ∃ a ∈ A, ∃ z ∈ sylowCenter T, t = a * z}
  mul_mem' := by
    rintro _ _ ⟨a, ha, z, hz, rfl⟩ ⟨a', ha', z', hz', rfl⟩
    refine ⟨a * a', A.mul_mem ha ha', z * z', (sylowCenter T).mul_mem hz hz', ?_⟩
    have e1 : a' * z = z * a' := (mem_sylowCenter.mp hz).2 a' (hA ha')
    calc a * z * (a' * z') = a * (z * a') * z' := by group
      _ = a * (a' * z) * z' := by rw [e1]
      _ = a * a' * (z * z') := by group
  one_mem' := ⟨1, A.one_mem, 1, (sylowCenter T).one_mem, by group⟩
  inv_mem' := by
    rintro _ ⟨a, ha, z, hz, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, z⁻¹, (sylowCenter T).inv_mem hz, ?_⟩
    have e1 : a⁻¹ * z⁻¹ = z⁻¹ * a⁻¹ :=
      (mem_sylowCenter.mp ((sylowCenter T).inv_mem hz)).2 a⁻¹ (T.inv_mem (hA ha))
    rw [mul_inv_rev, e1]

theorem mem_mulCenter {T A : Subgroup X} {hA : A ≤ T} {t : X} :
    t ∈ mulCenter T A hA ↔ ∃ a ∈ A, ∃ z ∈ sylowCenter T, t = a * z :=
  Iff.rfl

theorem nestedAt_of_coset_transitive [Finite X] {T : Subgroup X}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer (T : Set X)))
    (hZ : ∀ z ∈ sylowCenter T, z ^ 2 = 1) (hZT : sylowCenter T ≤ ⁅T, T⁆)
    (htrans : ∀ x ∈ T, x ∉ sylowCenter T → ∀ y ∈ T, y ∉ sylowCenter T →
      ∃ n ∈ Subgroup.normalizer (T : Set X), n⁻¹ * x * n * y⁻¹ ∈ sylowCenter T) :
    NestedAt T := by
  intro A₁ A₂ h₁ h₂ _ hcl
  by_cases hcen : A₁ ≤ sylowCenter T ∧ A₂ ≤ sylowCenter T
  · exact nested_of_le_center hSE hZ hcen.1 hcen.2 hcl
  obtain ⟨x, hxU, hxZ⟩ : ∃ x ∈ (A₁ : Set X) ∪ A₂, x ∉ sylowCenter T := by
    by_contra hcon
    push Not at hcon
    exact hcen ⟨fun y hy => hcon y (Or.inl hy), fun y hy => hcon y (Or.inr hy)⟩
  have hxT : x ∈ T := by
    rcases hxU with h | h
    · exact h₁ h
    · exact h₂ h
  have hcov : ((T : Subgroup X) : Set X) ⊆
      (mulCenter T A₁ h₁ : Set X) ∪ (mulCenter T A₂ h₂ : Set X) := by
    intro y hy
    by_cases hyZ : y ∈ sylowCenter T
    · exact Or.inl ⟨1, A₁.one_mem, y, hyZ, by group⟩
    obtain ⟨n, hn, hnz⟩ := htrans x hxT hxZ y hy hyZ
    have hwT : n⁻¹ * x * n ∈ T := by
      have hn' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn)) x
      rw [inv_inv] at hn'
      exact hn'.mp hxT
    have hw := hcl x hxU n hwT
    set w := n⁻¹ * x * n with hwdef
    set z := w * y⁻¹ with hzdef
    have hy1 : y = z⁻¹ * w := by
      rw [hzdef]
      group
    have hcomm : z⁻¹ * w = w * z⁻¹ :=
      ((mem_sylowCenter.mp ((sylowCenter T).inv_mem hnz)).2 w hwT).symm
    have hy_eq : y = w * z⁻¹ := hy1.trans hcomm
    rcases hw with hw | hw
    · exact Or.inl ⟨w, hw, z⁻¹, (sylowCenter T).inv_mem hnz, hy_eq⟩
    · exact Or.inr ⟨w, hw, z⁻¹, (sylowCenter T).inv_mem hnz, hy_eq⟩
  rcases SubgroupClass.subset_union.mp hcov with hle | hle
  · have hA : A₁ = T := eq_of_le_mul_center h₁ (fun t ht => mem_mulCenter.mp (hle ht)) hZT
    right
    rw [hA]
    exact h₂
  · have hA : A₂ = T := eq_of_le_mul_center h₂ (fun t ht => mem_mulCenter.mp (hle ht)) hZT
    left
    rw [hA]
    exact h₁

theorem nestedAt_of_mulEquiv [Finite X] {Y : Type*} [Group Y] (e : X ≃* Y)
    (hY : ∀ T : Sylow 2 Y, NestedAt (T : Subgroup Y)) (T : Sylow 2 X) :
    NestedAt (T : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (hY (T.mapSurjective (f := e.toMonoidHom) e.surjective)).map_mulEquiv e.symm
  have h' : NestedAt (((T : Subgroup X).map e.toMonoidHom).map e.symm.toMonoidHom) := h
  rw [Subgroup.map_map] at h'
  convert h'
  ext x
  simp

theorem map_center_eq_sylowCenter (T : Subgroup X) :
    (Subgroup.center T).map T.subtype = sylowCenter T := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine mem_sylowCenter.mpr ⟨w.2, fun t ht => ?_⟩
    have := Subgroup.mem_center_iff.mp hw ⟨t, ht⟩
    exact congrArg Subtype.val this
  · intro hz
    obtain ⟨hzT, hzc⟩ := mem_sylowCenter.mp hz
    refine ⟨⟨z, hzT⟩, Subgroup.mem_center_iff.mpr fun t => Subtype.ext (hzc t t.2), rfl⟩

theorem benderBorel_sylowCenter {q k : ℕ} (h : fusionBenderBorel X q k) (T : Sylow 2 X) :
    fusionStronglyEmbedded (Subgroup.normalizer ((T : Subgroup X) : Set X)) ∧
      (∀ z ∈ sylowCenter (T : Subgroup X), z ^ 2 = 1) ∧
      Nat.card (sylowCenter (T : Subgroup X)) = q ∧ Nat.card (T : Subgroup X) = q ^ k := by
  obtain ⟨hSE, -, hZ2, hZcard, hTcard⟩ := h T
  refine ⟨hSE, ?_, ?_, hTcard⟩
  · intro z hz
    rw [← map_center_eq_sylowCenter] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact congrArg Subtype.val (hZ2 w hw)
  · rw [← map_center_eq_sylowCenter,
      Subgroup.card_map_of_injective (T : Subgroup X).subtype_injective]
    exact hZcard

end Bender

end CFSG.ComponentClassification.AschbacherToolkit
