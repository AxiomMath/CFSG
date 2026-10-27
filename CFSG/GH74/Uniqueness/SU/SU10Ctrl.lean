module

public import CFSG.GH74.Uniqueness.SU.SU8Stmts

public section

namespace CFSG.GH74.Uniqueness.SU.SU10

open Subgroup CFSG.GH74.Uniqueness.SU.SU8

variable {G : Type} [Group G]

theorem isElemAbelian_omegaOne {X : Subgroup G}
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * a = 1 → b * b = 1 → a * b = b * a) :
    Open.IsElemAbelian 2 (omegaOne X) := by
  set s : Set G := {g : G | g ∈ X ∧ g * g = 1} with hs
  have hs_comm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a := fun a ha b hb => hcomm a ha.1 b hb.1 ha.2 hb.2
  have h1 : ∀ x ∈ omegaOne X, ∀ b ∈ s, x * b = b * x := by
    intro x hx b hb
    have hle : omegaOne X ≤ centralizer ({b} : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      intro a ha
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hs_comm a ha b hb
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have h2 : ∀ x ∈ omegaOne X, ∀ y ∈ omegaOne X, x * y = y * x := by
    intro x hx y hy
    have hle : omegaOne X ≤ centralizer ({x} : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      intro b hb
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact (h1 x hx b hb).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hy)).symm
  rw [SU1.isElemAbelian_iff]
  refine ⟨h2, ?_⟩
  intro x hx
  have hx2 : x * x = 1 := by
    induction hx using Subgroup.closure_induction with
    | mem g hg => exact hg.2
    | one => simp
    | mul a b ha hb iha ihb =>
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [h2 b hb a ha]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [iha, ihb, one_mul]
    | inv a ha iha =>
      calc a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
        _ = 1 := by rw [iha, inv_one]
  rw [sq]
  exact hx2

theorem omegaOne_map (e : G ≃* G) (X : Subgroup G) :
    omegaOne (X.map e.toMonoidHom) = (omegaOne X).map e.toMonoidHom := by
  unfold omegaOne
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hg⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    apply e.injective
    simpa using hg
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    simp [← map_mul, hx2]

theorem omegaOne_le (X : Subgroup G) : omegaOne X ≤ X :=
  (Subgroup.closure_le _).mpr fun _ hg => hg.1

theorem card_omegaOne_conj (g : G) (X : Subgroup G) :
    Nat.card (omegaOne (X.map (MulAut.conj g).toMonoidHom)) = Nat.card (omegaOne X) := by
  rw [omegaOne_map, Subgroup.card_map_of_injective (MulAut.conj g).injective]

section Finite

variable [Finite G]

theorem omegaOne_eq_of_le (S S₁ : Sylow 2 G)
    (hcomm : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * a = 1 → b * b = 1 → a * b = b * a)
    (hle : omegaOne (S : Subgroup G) ≤ (S₁ : Subgroup G)) :
    omegaOne (S₁ : Subgroup G) = omegaOne (S : Subgroup G) := by
  have hel := isElemAbelian_omegaOne hcomm
  have hsq : ∀ a ∈ omegaOne (S : Subgroup G), a * a = 1 := fun a ha => by
    have := (SU1.isElemAbelian_iff.mp hel).2 a ha
    rwa [sq] at this
  have hle' : omegaOne (S : Subgroup G) ≤ omegaOne (S₁ : Subgroup G) := fun a ha =>
    Subgroup.subset_closure ⟨hle ha, hsq a ha⟩
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G S S₁
  have hS₁ : (S₁ : Subgroup G) = (S : Subgroup G).map (MulAut.conj x).toMonoidHom := by
    rw [← hx, Sylow.coe_subgroup_smul]
    rfl
  have hcard : Nat.card (omegaOne (S₁ : Subgroup G)) = Nat.card (omegaOne (S : Subgroup G)) := by
    rw [hS₁]
    exact card_omegaOne_conj x _
  exact (Subgroup.eq_of_le_of_card_ge hle' hcard.le).symm


theorem exists_pGroup_containing_conj {C A B : Subgroup G} (hA : IsPGroup 2 A) (hB : IsPGroup 2 B)
    (hAC : A ≤ C) (hBC : B ≤ C) :
    ∃ U : Subgroup G, IsPGroup 2 U ∧ U ≤ C ∧ A ≤ U ∧ ∃ c ∈ C, ∀ z ∈ B, c * z * c⁻¹ ∈ U := by
  obtain ⟨Q₁, hQ₁⟩ := (hA.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨Q₂, hQ₂⟩ := (hB.comap_subtype (K := C)).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C Q₂ Q₁
  refine ⟨(Q₁ : Subgroup C).map C.subtype, Q₁.isPGroup'.map _, Subgroup.map_subtype_le _, ?_, c,
    c.2, ?_⟩
  · intro a ha
    exact ⟨⟨a, hAC ha⟩, hQ₁ ha, rfl⟩
  · intro z hz
    have hmem : MulAut.conj c • (⟨z, hBC hz⟩ : C) ∈ ((c • Q₂ : Sylow 2 C) : Subgroup C) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ (hQ₂ hz)
    rw [hc] at hmem
    exact ⟨_, hmem, by simp [MulAut.smul_def]⟩

theorem exists_mem_normalizer_omegaOne (S : Sylow 2 G)
    (hcomm : ∀ a ∈ (S : Subgroup G), ∀ b ∈ (S : Subgroup G), a * a = 1 → b * b = 1 → a * b = b * a)
    {a b g : G} (ha : a ∈ omegaOne (S : Subgroup G)) (hb : b ∈ omegaOne (S : Subgroup G))
    (hab : g * a * g⁻¹ = b) :
    ∃ n ∈ normalizer ((omegaOne (S : Subgroup G) : Subgroup G) : Set G), n * a * n⁻¹ = b := by
  have hel := isElemAbelian_omegaOne hcomm
  have hAcomm := (SU1.isElemAbelian_iff.mp hel).1
  have hsq : ∀ x ∈ omegaOne (S : Subgroup G), x * x = 1 := fun x hx => by
    have := (SU1.isElemAbelian_iff.mp hel).2 x hx
    rwa [sq] at this
  have hAp : IsPGroup 2 (omegaOne (S : Subgroup G)) := S.isPGroup'.to_le (omegaOne_le _)
  have hAC : omegaOne (S : Subgroup G) ≤ centralizer ({b} : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hAcomm x hx b hb
  have hA'C : (omegaOne (S : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤
      centralizer ({b} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxa := hAcomm x hx a ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hab]
    calc g * x * g⁻¹ * (g * a * g⁻¹) = g * (x * a) * g⁻¹ := by group
      _ = g * (a * x) * g⁻¹ := by rw [hxa]
      _ = g * a * g⁻¹ * (g * x * g⁻¹) := by group
  obtain ⟨U, hU2, -, hAU, c, hcC, hcU⟩ := exists_pGroup_containing_conj hAp
    (hAp.map (MulAut.conj g).toMonoidHom) hAC hA'C
  obtain ⟨S₁, hUS₁⟩ := hU2.exists_le_sylow
  have hAS₁ : omegaOne (S : Subgroup G) ≤ (S₁ : Subgroup G) := hAU.trans hUS₁
  have hΩ := omegaOne_eq_of_le S S₁ hcomm hAS₁
  have hconjle : ∀ x ∈ omegaOne (S : Subgroup G), c * g * x * (c * g)⁻¹ ∈ omegaOne (S : Subgroup G) := by
    intro x hx
    have h1 : c * (g * x * g⁻¹) * c⁻¹ ∈ U := hcU _ ⟨x, hx, rfl⟩
    have h2 : c * g * x * (c * g)⁻¹ = c * (g * x * g⁻¹) * c⁻¹ := by group
    rw [h2, ← hΩ]
    refine Subgroup.subset_closure ⟨hUS₁ h1, ?_⟩
    have hg2 : (c * g * x * (c * g)⁻¹) * (c * g * x * (c * g)⁻¹) = 1 := by
      calc (c * g * x * (c * g)⁻¹) * (c * g * x * (c * g)⁻¹) = (c * g) * (x * x) * (c * g)⁻¹ := by
            group
        _ = 1 := by rw [hsq x hx]; group
    rwa [h2] at hg2
  refine ⟨c * g, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    have hmapeq : (omegaOne (S : Subgroup G)).map (MulAut.conj (c * g)).toMonoidHom =
        omegaOne (S : Subgroup G) := by
      refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective
        (MulAut.conj (c * g)).injective).ge
      rintro _ ⟨x, hx, rfl⟩
      exact hconjle x hx
    constructor
    · intro hy
      have : (c * g) * y * (c * g)⁻¹ ∈ (omegaOne (S : Subgroup G)).map (MulAut.conj (c * g)).toMonoidHom :=
        ⟨y, hy, rfl⟩
      rwa [hmapeq] at this
    · intro hy
      rw [← hmapeq] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      have : x = y := (MulAut.conj (c * g)).injective hxy
      rwa [← this]
  · have hcb : (c : G) * b = b * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
    calc c * g * a * (c * g)⁻¹ = c * (g * a * g⁻¹) * c⁻¹ := by group
      _ = c * b * c⁻¹ := by rw [hab]
      _ = b := by rw [hcb]; group

end Finite

end CFSG.GH74.Uniqueness.SU.SU10
