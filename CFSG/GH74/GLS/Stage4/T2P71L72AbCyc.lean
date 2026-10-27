module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GH74.GLS.Stage4.Rest.L72

open scoped Pointwise

@[expose] def AbCyc (T : Type) [Group T] : Prop :=
  ∃ (E : Subgroup T) (_ : E.Normal), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ IsCyclic (T ⧸ E)

theorem AbCyc.of_injective {A B : Type} [Group A] [Group B] (f : A →* B) (hf : Function.Injective f) :
    AbCyc B → AbCyc A := by
  rintro ⟨E, hE, hab, hcyc⟩
  have := hE
  refine ⟨E.comap f, inferInstance, ?_, ?_⟩
  · intro x hx y hy
    apply hf
    rw [map_mul, map_mul]
    exact hab _ hx _ hy
  · let g : A ⧸ E.comap f →* B ⧸ E := QuotientGroup.map (E.comap f) E f le_rfl
    have hg : Function.Injective g := by
      rw [injective_iff_map_eq_one]
      intro x hx
      induction x using QuotientGroup.induction_on with
      | H a =>
        have : f a ∈ E := by simpa [g, QuotientGroup.eq_one_iff] using hx
        exact (QuotientGroup.eq_one_iff a).2 this
    exact isCyclic_of_injective g hg

theorem AbCyc.of_surjective {A B : Type} [Group A] [Group B] (f : A →* B) (hf : Function.Surjective f) :
    AbCyc A → AbCyc B := by
  rintro ⟨E, hE, hab, hcyc⟩
  have := hE
  have : (E.map f).Normal := Subgroup.Normal.map hE f hf
  refine ⟨E.map f, inferInstance, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hab x hx y hy]
  · let g : A ⧸ E →* B ⧸ E.map f := QuotientGroup.map E (E.map f) f (Subgroup.le_comap_map f E)
    have hg : Function.Surjective g := by
      intro b
      induction b using QuotientGroup.induction_on with
      | H b =>
        obtain ⟨a, rfl⟩ := hf b
        exact ⟨QuotientGroup.mk a, rfl⟩
    exact isCyclic_of_surjective g hg

theorem AbCyc.of_pSubgroup {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : AbCyc ↥(P : Subgroup G)) (T : Subgroup G) (hT : IsPGroup p ↥T) : AbCyc ↥T := by
  obtain ⟨Q, hQ⟩ := hT.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have h : MulAut.conj g • (P : Subgroup G) = (Q : Subgroup G) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  have e : ↥(P : Subgroup G) ≃* ↥(Q : Subgroup G) :=
    (Subgroup.equivSMul (MulAut.conj g) (P : Subgroup G)).trans (MulEquiv.subgroupCongr h)
  have hQ' : AbCyc ↥(Q : Subgroup G) := AbCyc.of_surjective e.toMonoidHom e.surjective hP
  exact AbCyc.of_injective (Subgroup.inclusion hQ) (Subgroup.inclusion_injective hQ) hQ'

theorem AbCyc.of_section {Y X : Type} [Group Y] [Finite Y] [Group X] (π : Y →* X)
    (hπ : Function.Surjective π) (hY : ∀ T : Subgroup Y, IsPGroup 3 ↥T → AbCyc ↥T)
    (V : Subgroup X) (hV : IsPGroup 3 ↥V) : AbCyc ↥V := by
  have : Finite X := Finite.of_surjective π hπ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 Y) := inferInstance
  let S₁ : Sylow 3 X := T.mapSurjective hπ
  have h1 : AbCyc ↥(T : Subgroup Y) := hY _ T.isPGroup'
  have h2 : AbCyc ↥(S₁ : Subgroup X) := by
    have hS : (S₁ : Subgroup X) = (T : Subgroup Y).map π := Sylow.coe_mapSurjective hπ T
    rw [hS]
    exact AbCyc.of_surjective (π.subgroupMap (T : Subgroup Y)) (π.subgroupMap_surjective _) h1
  exact AbCyc.of_pSubgroup S₁ h2 V hV

theorem exists_abelian_index_le_three {K : Type} [Group K] [Finite K] (P : Subgroup K)
    (hΩ : Subgroup.closure {x : K | x ∈ P ∧ x ^ 3 = 1} = P) (hP : AbCyc ↥P) :
    ∃ B : Subgroup K, B ≤ P ∧ (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) ∧ Nat.card ↥P ≤ 3 * Nat.card ↥B := by
  obtain ⟨E, hE, hab, hcyc⟩ := hP
  have := hE
  refine ⟨E.map P.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact x.2
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hab x hx y hy)
  · have hB : Nat.card ↥(E.map P.subtype) = Nat.card ↥E :=
      Subgroup.card_map_of_injective P.subtype_injective
    rw [hB]
    have hcomm : ∀ a b : ↥P ⧸ E, a * b = b * a := fun a b =>
      (IsCyclic.commGroup (α := ↥P ⧸ E)).mul_comm a b
    let S3 : Subgroup (↥P ⧸ E) :=
      { carrier := {q | q ^ 3 = 1}
        mul_mem' := fun {a b} ha hb => by
          have ha' : a ^ 3 = 1 := ha
          have hb' : b ^ 3 = 1 := hb
          show (a * b) ^ 3 = 1
          rw [(show Commute a b from hcomm a b).mul_pow, ha', hb', mul_one]
        one_mem' := one_pow 3
        inv_mem' := fun {a} ha => by
          have ha' : a ^ 3 = 1 := ha
          show a⁻¹ ^ 3 = 1
          rw [inv_pow, ha', inv_one] }
    let S4 : Subgroup K := (S3.comap (QuotientGroup.mk' E)).map P.subtype
    have hsub : {x : K | x ∈ P ∧ x ^ 3 = 1} ⊆ S4 := by
      rintro x ⟨hxP, hx3⟩
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      show (QuotientGroup.mk (⟨x, hxP⟩ : ↥P) : ↥P ⧸ E) ^ 3 = 1
      rw [← QuotientGroup.mk_pow]
      have : (⟨x, hxP⟩ : ↥P) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
      rw [this]; rfl
    have hPS4 : P ≤ S4 := by
      rw [← hΩ]; exact (Subgroup.closure_le S4).2 hsub
    have hexp : ∀ q : ↥P ⧸ E, q ^ 3 = 1 := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H x =>
        obtain ⟨x', hx', hxx'⟩ := hPS4 x.2
        have : x' = x := Subtype.ext hxx'
        subst this
        exact hx'
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (hexp g)
    have hcard : Nat.card (↥P ⧸ E) = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    have hle3 : Nat.card (↥P ⧸ E) ≤ 3 := by
      rw [hcard]; exact Nat.le_of_dvd (by norm_num) h3
    have hPE := Subgroup.card_eq_card_quotient_mul_card_subgroup E
    calc Nat.card ↥P = Nat.card (↥P ⧸ E) * Nat.card ↥E := hPE
      _ ≤ 3 * Nat.card ↥E := Nat.mul_le_mul_right _ hle3

end CFSG.GH74.GLS.Stage4.Rest.L72
