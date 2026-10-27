module

public import CFSG.LargeExtraspecial.S63CD4Iso
public import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoSylow

public section

namespace CFSG.GF2Type.Smith1980Orth

open CFSG.Quasithin CFSG.Open CFSG.AGLEmbedding.D4Two

private theorem map_comm_and_pow {p : ℕ} {G H : Type*} [Group G] [Group H] (f : G →* H)
    {E : Subgroup G} (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hp : ∀ x ∈ E, x ^ p = 1) :
    (∀ x ∈ E.map f, ∀ y ∈ E.map f, x * y = y * x) ∧ ∀ x ∈ E.map f, x ^ p = 1 := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hp x hx, map_one]

theorem card_le_nine_of_elementary_trialityGroup8
    (hG : Nat.card trialityGroup8 = 211341312) (E : Subgroup trialityGroup8)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (h3 : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hle, hcard, hrank⟩ := sylowGroup_facts
  have hv : (Nat.card trialityGroup8).factorization 3 = 4 := by
    rw [hG]
    have h : (211341312 : ℕ) = 3 ^ 4 * 2609152 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp only [Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same]
    rw [Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hS : Nat.card (sylowGroup.subgroupOf trialityGroup8) =
      3 ^ (Nat.card trialityGroup8).factorization 3 := by
    rw [hv, ← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using h3 x.1 x.2)⟩
  obtain ⟨Q, hEQ⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq trialityGroup8 Q (Sylow.ofCard _ hS)
  have hQ : ((g • Q : Sylow 3 trialityGroup8) : Subgroup trialityGroup8) =
      (Q : Subgroup trialityGroup8).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hconj : E.map (MulAut.conj g).toMonoidHom ≤ sylowGroup.subgroupOf trialityGroup8 := by
    have := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hEQ
    rw [← hQ, hg] at this
    exact this
  let φ : trialityGroup8 →* GL (Fin 8) GF8 :=
    trialityGroup8.subtype.comp (MulAut.conj g).toMonoidHom
  have hφ : Function.Injective φ :=
    Subgroup.subtype_injective _ |>.comp (MulAut.conj g).injective
  have hEφ : E.map φ ≤ sylowGroup := by
    rw [show E.map φ = (E.map (MulAut.conj g).toMonoidHom).map trialityGroup8.subtype from
      (Subgroup.map_map _ _ _).symm]
    exact Subgroup.map_le_iff_le_comap.mpr hconj
  obtain ⟨hc, hp⟩ := map_comm_and_pow φ hcomm h3
  have := hrank (E.map φ) hEφ ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hp⟩
  rw [Subgroup.card_map_of_injective hφ] at this
  simpa using this

theorem not_lieModel_trialityD4_of_elementary
    {G : Type} [Group G] [Finite G] (E : Subgroup G)
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (h3 : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 27) : ¬ CFSG.Blueprint.LieModel G .trialityD4 0 2 1 := by
  intro hL
  obtain ⟨e⟩ := CFSG.LargeExtraspecial.S63.nonempty_equiv_trialityGroup8 G hL
  have hG : Nat.card G = ordTrialityD4 2 :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
      (hL.chevalleyExceptionalModel (by decide))
  have hT : Nat.card trialityGroup8 = 211341312 := by
    rw [← Nat.card_congr e.toEquiv, hG]
    decide
  obtain ⟨hc, hp⟩ := map_comm_and_pow e.toMonoidHom hcomm h3
  have := card_le_nine_of_elementary_trialityGroup8 hT (E.map e.toMonoidHom) hc hp
  rw [Subgroup.card_map_of_injective e.injective, hcard] at this
  norm_num at this

end CFSG.GF2Type.Smith1980Orth
