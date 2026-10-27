module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGA5
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ComponentClassification.FooteLit.KG

open CFSG Subgroup CFSG.ComponentClassification.Foote5
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.Sporadic.Schreier

theorem noFooteComponent_of_not_three_dvd {G : Type} [Group G] [Finite G]
    (h : ∀ t : G, orderOf t = 2 → ¬ 3 ∣ Nat.card ↥(centralizer ({t} : Set G))) :
    NoFooteComponent G := by
  rintro L ⟨⟨t, ht2, hLC, -⟩, hfam, -⟩
  obtain ⟨hsm, hdvd⟩ := isSmallOrder_card_quot hfam
  exact h t ht2 ((three_dvd_of_isSmallOrder hsm).trans (hdvd.trans (Subgroup.card_dvd_of_le hLC)))

theorem statedClassicalModel_of_lieModel_psl {X : Type} [Group X] {n p f : ℕ}
    (h : LieModel X .PSL n p f) : StatedClassicalModel X .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem not_three_dvd_of_lieModel_psl_two_two {G : Type} [Group G] [Finite G] {e : ℕ}
    (hm : LieModel G .PSL 2 2 e) (t : G) (ht : orderOf t = 2) :
    ¬ 3 ∣ Nat.card ↥(centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hadm, K, _, _, hK, ⟨φ⟩⟩ := statedClassicalModel_of_lieModel_psl hm
  let ψ : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 e) :=
    φ.trans (ClassicalModels.statedLinearModelEquivGaloisPSL K 2 2 e hadm.2.1 hK)
  have hψ : orderOf (ψ t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  have hP := Walter.psl2_centralizer_isPGroup_of_charTwo hψ
  have e₁ : ↥(centralizer ({t} : Set G)) ≃* ↥(centralizer ({ψ t} : Set _)) :=
    ((centralizer ({t} : Set G)).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr (map_centralizer_equiv ψ t))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hP.of_equiv e₁.symm)
  rw [hk]
  intro h3
  have := Nat.le_of_dvd two_pos (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem noFooteComponent_of_lieModel_psl_two_two {G : Type} [Group G] [Finite G] {e : ℕ}
    (hm : LieModel G .PSL 2 2 e) : NoFooteComponent G :=
  noFooteComponent_of_not_three_dvd (not_three_dvd_of_lieModel_psl_two_two hm)

theorem footeKnownSmall_L28 (G : Type) [Group G] [Finite G] (hm : LieModel G .PSL 2 2 3) :
    FooteKnownSmall G :=
  FooteKnownSmall.of_no (noFooteComponent_of_lieModel_psl_two_two hm)

theorem footeKnownSmall_L216 (G : Type) [Group G] [Finite G] (hm : LieModel G .PSL 2 2 4) :
    FooteKnownSmall G :=
  FooteKnownSmall.of_no (noFooteComponent_of_lieModel_psl_two_two hm)

theorem map_conj_inf_centralizer_l34 {c : Equiv.Perm (Fin 42)}
    (hc : c ∈ PSL3Four.R) (r : Equiv.Perm (Fin 42)) :
    (PSL3Four.S ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 42)))).map (MulAut.conj c).toMonoidHom =
      PSL3Four.S ⊓ centralizer ({c * r * c⁻¹} : Set (Equiv.Perm (Fin 42))) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨w, ⟨hwS, hw⟩, rfl⟩
    refine ⟨PSL3Four.conj_mem_S hc hwS, ?_⟩
    calc c * w * c⁻¹ * (c * r * c⁻¹) = c * (w * r) * c⁻¹ := by group
      _ = c * (r * w) * c⁻¹ := by rw [hw]
      _ = c * r * c⁻¹ * (c * w * c⁻¹) := by group
  · rintro ⟨hyS, hy⟩
    refine ⟨c⁻¹ * y * c, ⟨PSL3Four.conj_mem_S' hc ?_, ?_⟩, by group⟩
    · rwa [show c * (c⁻¹ * y * c) * c⁻¹ = y by group]
    · calc c⁻¹ * y * c * r = c⁻¹ * (y * (c * r * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * r * c⁻¹) * y) * c := by rw [hy]
        _ = r * (c⁻¹ * y * c) := by group

theorem card_centralizer_of_lieModel_l34 {G : Type} [Group G]
    (hm : LieModel G .PSL 3 2 2) (t : G) (ht : orderOf t = 2) :
    Nat.card ↥(centralizer ({t} : Set G)) = 64 := by
  obtain ⟨θ⟩ := PSL3Four.nonempty_equiv_of_stated G (statedClassicalModel_of_lieModel_psl hm)
  obtain ⟨-, -, -, -, -, hinv, -, -, -, -, -, -, hout, hC1, -⟩ := PSL3Four.involution_enumeration
  set y : Equiv.Perm (Fin 42) := ((θ t : PSL3Four.S) : Equiv.Perm (Fin 42)) with hydef
  have hyS : y ∈ PSL3Four.S := (θ t).2
  let x : PSL3Four.R := ⟨y, PSL3Four.S_le_R hyS⟩
  have hx2 : orderOf x = 2 := by
    rw [← Subgroup.orderOf_coe x]
    change orderOf ((θ t : PSL3Four.S) : Equiv.Perm (Fin 42)) = 2
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ht]
  have hc : Nat.card ↥(centralizer ({t} : Set G)) =
      Nat.card ↥(PSL3Four.S ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 42)))) := by
    rw [← Subgroup.card_map_of_injective (f := θ.toMonoidHom) θ.injective,
      map_centralizer_equiv θ t,
      ← Subgroup.card_map_of_injective (f := PSL3Four.S.subtype) PSL3Four.S.subtype_injective,
      map_centralizer_subtype]
    rfl
  rcases (hinv x).1 hx2 with h1 | h2 | h3 | h4
  · obtain ⟨c, hcR, he⟩ := PSL3Four.eq_conj_of_isConj h1
    have hyc : y = c * PSL3Four.r₁ * c⁻¹ := he
    rw [hc, hyc, ← map_conj_inf_centralizer_l34 hcR PSL3Four.r₁,
      Subgroup.card_map_of_injective (MulAut.conj c).injective, inf_comm]
    exact hC1
  · exact absurd hyS (hout x (Or.inl h2))
  · exact absurd hyS (hout x (Or.inr (Or.inl h3)))
  · exact absurd hyS (hout x (Or.inr (Or.inr h4)))

theorem footeKnownSmall_L34 (G : Type) [Group G] [Finite G]
    (hm : LieModel G .PSL 3 2 2) : FooteKnownSmall G :=
  FooteKnownSmall.of_no (noFooteComponent_of_not_three_dvd fun t ht => by
    rw [card_centralizer_of_lieModel_l34 hm t ht]
    norm_num)

theorem card_of_lieModel_sz8 {G : Type} [Group G]
    (hm : LieModel G .twistedB2 0 2 3) : Nat.card G = 29120 := by
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, -, a, -, K, _, _, hf, hK, ⟨e⟩⟩
  · simp [classicalTags] at ht
  · simp [chevalleyExceptionalTags] at ht
  · simp [reeTitsTags] at ht
  · have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hf]
    rw [Nat.card_congr e.toEquiv, LieType.Ree.suzuki_order hK', ← hf]
    norm_num

theorem footeKnownSmall_Sz8 (G : Type) [Group G] [Finite G]
    (hm : LieModel G .twistedB2 0 2 3) : FooteKnownSmall G :=
  FooteKnownSmall.of_no (noFooteComponent_of_not_three_dvd fun t _ h => by
    have h' := h.trans (Subgroup.card_subgroup_dvd_card _)
    rw [card_of_lieModel_sz8 hm] at h'
    norm_num at h')

end CFSG.ComponentClassification.FooteLit.KG
