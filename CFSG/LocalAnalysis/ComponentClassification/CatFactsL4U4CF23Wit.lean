module

public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TCReduce

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup CFSG.ComponentClassification.RestrictedStd
open CFSG.ComponentClassification.OddClassSelector (NoTightWitness)
open CFSG.ComponentClassification.CatFactsSp4 (TCWitness isComponent_map_subgroupOf)
open scoped commutatorElement

theorem mem_centralizer_of_comm_commutator {X : Type*} [Group X] {F : Subgroup X}
    (hF : ⁅F, F⁆ = F) {g : X} (hgN : g ∈ normalizer (F : Set X))
    (hc : ∀ j ∈ F, ∀ y ∈ F, (j⁻¹ * g⁻¹ * j * g) * y = y * (j⁻¹ * g⁻¹ * j * g)) :
    g ∈ centralizer (F : Set X) := by
  have hmem : ∀ j ∈ F, j⁻¹ * g⁻¹ * j * g ∈ F := by
    intro j hj
    have h1 : g⁻¹ * j * g ∈ F := by
      have := (mem_normalizer_iff.1 (inv_mem hgN) j).1 hj
      simpa using this
    have h2 := mul_mem (inv_mem hj) h1
    simpa [mul_assoc] using h2
  let φ : F →* F :=
    { toFun := fun j => ⟨(j : X)⁻¹ * g⁻¹ * j * g, hmem j j.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        change ((a : X) * b)⁻¹ * g⁻¹ * (a * b) * g =
          ((a : X)⁻¹ * g⁻¹ * a * g) * ((b : X)⁻¹ * g⁻¹ * b * g)
        have hcb := hc a a.2 (b : X)⁻¹ (inv_mem b.2)
        calc ((a : X) * b)⁻¹ * g⁻¹ * (a * b) * g =
            (b : X)⁻¹ * ((a : X)⁻¹ * g⁻¹ * a * g) * (g⁻¹ * b * g) := by group
          _ = ((a : X)⁻¹ * g⁻¹ * a * g) * (b : X)⁻¹ * (g⁻¹ * b * g) := by rw [← hcb]
          _ = ((a : X)⁻¹ * g⁻¹ * a * g) * ((b : X)⁻¹ * g⁻¹ * b * g) := by group }
  have hcomm : ⁅F, F⁆ ≤ φ.ker.map F.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : F), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    exact hc a ha _ (φ ⟨b, hb⟩).2
  rw [mem_centralizer_iff]
  intro j hj
  rw [← hF] at hj
  obtain ⟨y, hy, rfl⟩ := hcomm hj
  have h1 : (y : X)⁻¹ * g⁻¹ * y * g = 1 := congrArg Subtype.val hy
  have h2 : g⁻¹ * y * g = y := by
    calc g⁻¹ * y * g = y * ((y : X)⁻¹ * g⁻¹ * y * g) := by group
      _ = y := by rw [h1, mul_one]
  calc (y : X) * g = g * (g⁻¹ * y * g) := by group
    _ = g * y := by rw [h2]

theorem false_of_tcWitness {P : Type} [Group P] [Finite P] {φ : MulAut P}
    {X : Subgroup P} (hXq : IsQuasisimple X) (hXφ : ∀ x ∈ X, φ x = x)
    (hw : TCWitness φ X) (hnt : NoTightWitness X) : False := by
  obtain ⟨t₀, ht₀2, ht₀1, hφt, htX, M₀, hM₀t, hM₀, hM₀φ, hXM⟩ := hw
  set M₁ := M₀.map φ.toMonoidHom with hM₁
  set C := centralizer ({t₀} : Set P) with hC
  have hto : orderOf t₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht₀2) ht₀1
  have hNX : ∀ g ∈ C, g ∈ normalizer (X : Set P) := fun g hg =>
    hnt t₀ g hto (fun x hx => (htX x hx).symm) (mem_centralizer_singleton_iff.mp hg)
  have hCφ : C.map φ.toMonoidHom = C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, hC, mem_centralizer_singleton_iff] at hx
      rw [hC, mem_centralizer_singleton_iff]
      change φ x * t₀ = t₀ * φ x
      rw [← hφt, ← map_mul, ← map_mul, hx]
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      rw [hC, mem_centralizer_singleton_iff] at hy
      rw [SetLike.mem_coe, hC, mem_centralizer_singleton_iff]
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hφt]
      exact hy
  have hM₁t : M₁ ≤ C := by
    rw [← hCφ]
    exact map_mono hM₀t
  have hM₁ : IsComponent (M₁.subgroupOf C) := by
    have h := isComponent_map_subgroupOf φ hM₀t hM₀
    rwa [hCφ] at h
  have hcomm01 : ∀ a ∈ M₀, ∀ b ∈ M₁, a * b = b * a := by
    rcases LocalCores.distinct_components_commute hM₀ hM₁ with h | h
    · exfalso
      apply hM₀φ
      have h' := congrArg (fun H : Subgroup C => H.map C.subtype) h
      simp only [subgroupOf_map_subtype, inf_eq_left.mpr hM₀t, inf_eq_left.mpr hM₁t] at h'
      exact h'.symm
    · intro a ha b hb
      have h1 : ⁅(⟨a, hM₀t ha⟩ : C), (⟨b, hM₁t hb⟩ : C)⁆ ∈ (⊥ : Subgroup C) :=
        h ▸ commutator_mem_commutator (show (⟨a, hM₀t ha⟩ : C) ∈ M₀.subgroupOf C from ha)
          (show (⟨b, hM₁t hb⟩ : C) ∈ M₁.subgroupOf C from hb)
      rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact congrArg Subtype.val h1
  have hXN0 : ∀ x ∈ X, x ∈ normalizer (M₀ : Set P) := by
    have hle : M₀ ⊔ M₁ ≤ normalizer (M₀ : Set P) := by
      refine sup_le le_normalizer fun b hb => ?_
      rw [mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        rw [← hcomm01 a ha b hb, mul_inv_cancel_right]
        exact ha
      · intro ha
        have e : a = b⁻¹ * (b * a * b⁻¹) * b := by group
        rw [e, mul_assoc, hcomm01 _ ha b hb, ← mul_assoc, inv_mul_cancel, one_mul]
        exact ha
    exact fun x hx => hle (hXM hx)
  have hperf : ⁅X, X⁆ = X := Subgroup.isPerfect_iff.1 hXq.1
  have hnontriv : Nontrivial X := LocalCores.isQuasisimple_nontrivial hXq
  have hnotcomm : ¬ ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro h
    have hab : ∀ a b : X, a * b = b * a := fun a b => Subtype.ext (h a a.2 b b.2)
    exact @Group.IsPerfect.not_isSolvable X _ hnontriv hXq.1 (Group.isSolvable_of_comm hab)
  have hnorm : ((X ⊓ M₀).subgroupOf X).Normal := by
    constructor
    intro y hy x
    rw [mem_subgroupOf] at hy ⊢
    obtain ⟨hyX, hyM⟩ := mem_inf.mp hy
    refine mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem (mul_mem x.2 hyX) (inv_mem x.2)
    · exact (mem_normalizer_iff.mp (hXN0 x x.2) y).mp hyM
  rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hXq hnorm.isSubnormal
    with htop | hcen
  ·
    apply hnotcomm
    have hXM₀ : ∀ x ∈ X, x ∈ M₀ := fun x hx => by
      have : (⟨x, hx⟩ : X) ∈ (X ⊓ M₀).subgroupOf X := htop ▸ mem_top _
      exact (mem_inf.mp (mem_subgroupOf.mp this)).2
    intro x hx y hy
    have hyM₁ : y ∈ M₁ := ⟨y, hXM₀ y hy, hXφ y hy⟩
    exact hcomm01 x (hXM₀ x hx) y hyM₁
  ·
    have hcent0 : ∀ m ∈ M₀, m ∈ centralizer (X : Set P) := by
      intro m hm
      refine mem_centralizer_of_comm_commutator hperf
        (hNX m (hM₀t hm)) ?_
      intro j hj y hy
      have hcX : j⁻¹ * m⁻¹ * j * m ∈ X := by
        have h1 : m⁻¹ * j * m ∈ X := by
          have := (mem_normalizer_iff.mp (inv_mem (hNX m (hM₀t hm))) j).mp hj
          simpa using this
        have h2 := mul_mem (inv_mem hj) h1
        simpa [mul_assoc] using h2
      have hcM : j⁻¹ * m⁻¹ * j * m ∈ M₀ := by
        have h1 : j⁻¹ * m⁻¹ * j ∈ M₀ := by
          have := (mem_normalizer_iff.mp (inv_mem (hXN0 j hj)) m⁻¹).mp (inv_mem hm)
          simpa [mul_assoc] using this
        exact mul_mem h1 hm
      have hz := hcen (show (⟨_, hcX⟩ : X) ∈ (X ⊓ M₀).subgroupOf X from
        mem_subgroupOf.mpr (mem_inf.mpr ⟨hcX, hcM⟩))
      have h3 := congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)
      exact h3.symm
    have hcent1 : ∀ m ∈ M₁, m ∈ centralizer (X : Set P) := by
      rintro _ ⟨m, hm, rfl⟩
      rw [mem_centralizer_iff]
      intro x hx
      have h1 := mem_centralizer_iff.mp (hcent0 m hm) x hx
      change x * φ m = φ m * x
      rw [← hXφ x hx, ← map_mul, ← map_mul, h1]
    apply hnotcomm
    intro x hx y hy
    have hle : M₀ ⊔ M₁ ≤ centralizer (X : Set P) := sup_le hcent0 hcent1
    exact (mem_centralizer_iff.mp (hle (hXM hy)) x hx)

theorem isComponentOf_of_cf23 {G : Type} [Group G] {N J : Subgroup G} {α : G}
    (hJN : J ≤ N) (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G)))) :
    CFSG.Assembly.IsComponentOf J (N ⊓ centralizer {α}) :=
  LocalAnalysis.ComponentInitial.isComponentOf_of_le
    ((LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJα).mpr hJ)
    (le_inf hJN hJα) inf_le_right

theorem smallSource_of_cf23 {G : Type} [Group G] {J : Subgroup G}
    (h : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p f) ∨
      Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)))
    (hZ : Odd (Nat.card (center ↥J))) : SmallSource J := by
  rcases h with ⟨p, f, hp, hp2, hf, h5, hm⟩ | h7
  · exact Or.inl ⟨p, f, hp, hp2, hf, h5, hm, hZ⟩
  · exact Or.inr (Or.inl ⟨h7, hZ⟩)

end CFSG.ComponentClassification.GSThmB.CF23I
