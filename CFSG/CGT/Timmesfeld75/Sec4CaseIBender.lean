module

public import CFSG.CGT.Timmesfeld75.BenderInputsBasic
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.Models.BenderSuzuki
public import CFSG.CGT.Timmesfeld75.WeaklyClosed

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.BenderSuzuki CFSG.Open

section Psu3

theorem fusionBenderBorel_of_psu3 {B : Type*} [Group B] {f : ℕ} (hf : 2 ≤ f)
    (e : B ≃* PSU3Model f) : fusionBenderBorel B (2 ^ f) 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmodel : PSU3Model f = PSU3 2 f := CFSG.Models.benderPSU3Model_eq_psu3 f
  let e' : B ≃* PSU3 2 f := e.trans (MulEquiv.subgroupCongr hmodel)
  have : Finite (PSU3 2 f) := by
    have : Finite (Matrix.ProjGenLinGroup (Fin 3) (GaloisField 2 (2 * f))) :=
      Finite.of_surjective
        (Matrix.ProjGenLinGroup.mk : GL (Fin 3) (GaloisField 2 (2 * f)) →* _)
        (QuotientGroup.mk'_surjective _)
    rw [← hmodel]
    infer_instance
  have : Finite B := Finite.of_equiv _ e'.symm.toEquiv
  exact (bender_psu3_borel_full f hf).map_mulEquiv e'.symm

end Psu3

section Count

variable {B : Type*} [Group B] [Finite B]

theorem inf_sylow_eq_bot (hK : IsBenderGroup B) {Q Q' : Sylow 2 B} (hne : Q ≠ Q') :
    (Q : Subgroup B) ⊓ (Q' : Subgroup B) = ⊥ := by
  by_contra hbot
  have hnt : Nontrivial ↥((Q : Subgroup B) ⊓ (Q' : Subgroup B)) :=
    (Subgroup.nontrivial_iff_ne_bot _).2 hbot
  have hP : IsPGroup 2 ↥((Q : Subgroup B) ⊓ (Q' : Subgroup B)) :=
    Q.isPGroup'.to_inf_left
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card ↥((Q : Subgroup B) ⊓ (Q' : Subgroup B)) := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    have hpos : n ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hn
      exact (Finite.one_lt_card_iff_nontrivial.2 hnt).ne' hn
    rw [hn]
    exact dvd_pow_self 2 hpos
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hvQ : (v : B) ∈ (Q : Subgroup B) := (v.2).1
  have hvQ' : (v : B) ∈ (Q' : Subgroup B) := (v.2).2
  have hv2 : orderOf (v : B) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact hv
  have hvv : (v : B) * (v : B) = 1 := by
    have := pow_orderOf_eq_one (v : B)
    rw [hv2] at this
    simpa [pow_two] using this
  have hv1 : (v : B) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hv2
    exact absurd hv2 (by decide)
  have hC : Subgroup.centralizer ({(v : B)} : Set B) ≤ Subgroup.normalizer (Q : Set B) :=
    centralizer_le_normalizer_of_isBenderGroup hK Q hvQ hvv hv1
  have hQ'C : (Q' : Subgroup B) ≤ Subgroup.centralizer ({(v : B)} : Set B) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.2
      ((CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q' hvQ' hvv y
        hy).eq.symm)
  have hle : (Q' : Subgroup B) ≤ (Q : Subgroup B) :=
    le_of_isPGroup_of_le_normalizer Q'.isPGroup' Q (hQ'C.trans hC)
  exact hne (Sylow.ext (Q'.is_maximal' Q.isPGroup' hle))

omit [Finite B] in
theorem coe_smul_sylow (g : B) (Q : Sylow 2 B) :
    ((g • Q : Sylow 2 B) : Subgroup B) = conjSubgroup g (Q : Subgroup B) := by
  ext x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_conjSubgroup]
  rfl

theorem exists_card_conj_gt (hK : IsBenderGroup B) {q k : ℕ} (hB : fusionBenderBorel B q k)
    {A : Subgroup B} (hA : IsElemAbelian 2 A) (hAq : Nat.card A = q) (hq : 1 < q) :
    q ^ k < Set.ncard {C : Subgroup B | ∃ g : B, C = conjSubgroup g A} := by
  obtain ⟨Q, hAQ⟩ := (isPGroup_two_of_isElemAbelian hA).exists_le_sylow
  have hAbot : A ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hAq
    omega
  obtain ⟨g, hg⟩ : ∃ g : B, g ∉ Subgroup.normalizer (Q : Set B) := by
    by_contra hall
    have hall' : ∀ x : B, x ∈ Subgroup.normalizer (Q : Set B) := fun x => by
      by_contra hx
      exact hall ⟨x, hx⟩
    exact (hB Q).1.1 (eq_top_iff.2 fun x _ => hall' x)
  have hAle : ∀ x : B, conjSubgroup x A ≤ ((x • Q : Sylow 2 B) : Subgroup B) := fun x => by
    rw [coe_smul_sylow]
    exact Subgroup.map_mono hAQ
  have hbot : ∀ x : B, conjSubgroup x A ≠ ⊥ := fun x h => hAbot (by
    have := congrArg (fun C : Subgroup B => Nat.card C) h
    simp only [card_conjSubgroup, Subgroup.card_bot] at this
    exact Subgroup.eq_bot_of_card_eq A this)
  let φ : ↥(Q : Subgroup B) → Subgroup B := fun u => conjSubgroup ((u : B) * g) A
  have hQ'ne : ∀ u : ↥(Q : Subgroup B), (((u : B) * g) • Q : Sylow 2 B) ≠ Q := by
    intro u h
    have h1 := Sylow.smul_eq_iff_mem_normalizer.1 h
    apply hg
    have hu : (u : B) ∈ Subgroup.normalizer (Q : Set B) := Subgroup.le_normalizer u.2
    have := (Subgroup.normalizer (Q : Set B)).mul_mem ((Subgroup.normalizer _).inv_mem hu) h1
    simpa [mul_assoc] using this
  have hgQ : (g • Q : Sylow 2 B) ≠ Q := fun h => hg (Sylow.smul_eq_iff_mem_normalizer.1 h)
  have hinj : Function.Injective φ := by
    intro u u' huu'
    have hQ12 : (((u : B) * g) • Q : Sylow 2 B) = (((u' : B) * g) • Q : Sylow 2 B) := by
      by_contra hne
      have hI := inf_sylow_eq_bot hK hne
      apply hbot ((u : B) * g)
      rw [eq_bot_iff, ← hI]
      exact le_inf (hAle _) (by
        have : conjSubgroup ((u : B) * g) A = conjSubgroup ((u' : B) * g) A := huu'
        rw [this]
        exact hAle _)
    have h1 : (u : B) • (g • Q : Sylow 2 B) = (u' : B) • (g • Q : Sylow 2 B) := by
      rw [← mul_smul, ← mul_smul]
      exact hQ12
    have h2 : ((u : B)⁻¹ * (u' : B)) • (g • Q : Sylow 2 B) = (g • Q : Sylow 2 B) := by
      rw [mul_smul, ← h1, inv_smul_smul]
    have h3 : (u : B)⁻¹ * (u' : B) ∈ Subgroup.normalizer ((g • Q : Sylow 2 B) : Set B) :=
      Sylow.smul_eq_iff_mem_normalizer.1 h2
    have h4 : (u : B)⁻¹ * (u' : B) ∈ (Q : Subgroup B) := Q.mul_mem (Q.inv_mem u.2) u'.2
    have hP : IsPGroup 2 ↥((Q : Subgroup B) ⊓
        Subgroup.normalizer ((g • Q : Sylow 2 B) : Set B)) := Q.isPGroup'.to_inf_left
    have h5 : (Q : Subgroup B) ⊓ Subgroup.normalizer ((g • Q : Sylow 2 B) : Set B) ≤
        ((g • Q : Sylow 2 B) : Subgroup B) :=
      le_of_isPGroup_of_le_normalizer hP (g • Q) inf_le_right
    have h6 : (u : B)⁻¹ * (u' : B) ∈ (Q : Subgroup B) ⊓ ((g • Q : Sylow 2 B) : Subgroup B) :=
      ⟨h4, h5 ⟨h4, h3⟩⟩
    rw [inf_sylow_eq_bot hK hgQ.symm, Subgroup.mem_bot, inv_mul_eq_one] at h6
    exact Subtype.ext h6
  have hnotA : A ∉ Set.range φ := by
    rintro ⟨u, hu⟩
    have hA1 : A ≤ ((((u : B) * g) • Q : Sylow 2 B) : Subgroup B) := by
      have := hAle ((u : B) * g)
      rwa [show conjSubgroup ((u : B) * g) A = A from hu] at this
    have hI := inf_sylow_eq_bot hK (hQ'ne u).symm
    exact hAbot (by rw [eq_bot_iff, ← hI]; exact le_inf hAQ hA1)
  have hsub : insert A (Set.range φ) ⊆ {C : Subgroup B | ∃ x : B, C = conjSubgroup x A} := by
    rintro C (rfl | ⟨u, rfl⟩)
    · exact ⟨1, (conjSubgroup_one C).symm⟩
    · exact ⟨_, rfl⟩
  have hfin : ({C : Subgroup B | ∃ x : B, C = conjSubgroup x A}).Finite := Set.toFinite _
  have hcard : (insert A (Set.range φ)).ncard = Nat.card ↥(Q : Subgroup B) + 1 := by
    rw [Set.ncard_insert_of_notMem hnotA, ← Set.image_univ,
      Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
  calc q ^ k = Nat.card ↥(Q : Subgroup B) := ((hB Q).2.2.2.2).symm
    _ < Nat.card ↥(Q : Subgroup B) + 1 := Nat.lt_succ_self _
    _ = (insert A (Set.range φ)).ncard := hcard.symm
    _ ≤ _ := Set.ncard_le_ncard hsub hfin

end Count

end CFSG.CGT.Timmesfeld75
