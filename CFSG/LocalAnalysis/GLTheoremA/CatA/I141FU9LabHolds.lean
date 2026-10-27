module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIAut
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSeitzB2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

theorem u9_exists_quotEquiv_apply_of_perfect_central {J K : Type} [Group J] [Group K] (φ : J →* K)
    (hφ : Function.Surjective φ) (hperf : Group.IsPerfect J) (hker : φ.ker ≤ Subgroup.center J) :
    ∃ ι : (J ⧸ Subgroup.center J) ≃* (K ⧸ Subgroup.center K),
      ∀ x : J, ι (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := by
  let ψ : J →* K ⧸ Subgroup.center K := (QuotientGroup.mk' (Subgroup.center K)).comp φ
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hφ
  have hψker : ψ.ker = Subgroup.center J := by
    apply le_antisymm
    · intro x hx
      have hxK : φ x ∈ Subgroup.center K := by
        have h1 : QuotientGroup.mk' (Subgroup.center K) (φ x) = 1 := hx
        exact (QuotientGroup.eq_one_iff _).mp h1
      apply CFSG.LocalAnalysis.GLTheoremA.Y10F.mem_center_of_commutators_central' hperf
      intro y
      apply hker
      simp only [MonoidHom.mem_ker, map_mul, map_inv]
      have h := Subgroup.mem_center_iff.mp hxK (φ y)
      calc φ x * φ y * (φ x)⁻¹ * (φ y)⁻¹ = φ y * φ x * (φ x)⁻¹ * (φ y)⁻¹ := by rw [← h]
        _ = 1 := by group
    · intro x hx
      have hc : φ x ∈ Subgroup.center K := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨y, rfl⟩ := hφ g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
      exact (QuotientGroup.eq_one_iff _).mpr hc
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψ), fun x => rfl⟩

theorem u9_exists_pSimple_equiv_centerQuot {A B : Type} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ}
    (hp : p.Prime) (hA : CFSG.Open.IsQuasisimple (A ⧸ GLAPPrimeCore p A))
    (hB : CFSG.Open.IsQuasisimple B) (hB' : Nontrivial (B ⧸ GLAPPrimeCore p B))
    (π : A →* B) (hπ : Function.Surjective π) :
    ∃ ι : ((A ⧸ GLAPPrimeCore p A) ⧸ Subgroup.center (A ⧸ GLAPPrimeCore p A)) ≃*
        (B ⧸ Subgroup.center B),
      ∀ a : A, ι (QuotientGroup.mk (QuotientGroup.mk a)) = QuotientGroup.mk (π a) := by
  have hne : GLAPPrimeCore p B ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (B ⧸ GLAPPrimeCore p B) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton (B ⧸ GLAPPrimeCore p B) ‹_›
  have hO : GLAPPrimeCore p B ≤ Subgroup.center B :=
    le_center_of_normal_of_isQuasisimple hB inferInstance hne
  have hker : (pQuotMapOfSurjective hp π hπ).ker ≤ Subgroup.center (A ⧸ GLAPPrimeCore p A) :=
    ker_pQuotMapOfSurjective_le_center hp π hπ hA hB'
  obtain ⟨ι₁, h₁⟩ := u9_exists_quotEquiv_apply_of_perfect_central (pQuotMapOfSurjective hp π hπ)
    (pQuotMapOfSurjective_surjective hp π hπ) ⟨hA.1⟩ hker
  obtain ⟨ι₂, h₂⟩ := u9_exists_quotEquiv_apply_of_perfect_central
    (QuotientGroup.mk' (GLAPPrimeCore p B)) (QuotientGroup.mk'_surjective _) ⟨hB.1⟩
    (by rw [QuotientGroup.ker_mk']; exact hO)
  refine ⟨ι₁.trans ι₂.symm, fun a => ?_⟩
  rw [MulEquiv.trans_apply, h₁, MulEquiv.symm_apply_eq]
  exact (h₂ (π a)).symm

private theorem unitary_label_of_markTag {lab : GLALabel}
    (hP : CFSG.StandardType.markTag lab = .PSU ∧ CFSG.StandardType.markRank lab = 3 ∧
      CFSG.StandardType.markChar lab = 2) : lab.tag = .twA := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨h1, h2, h3⟩ := hP
  cases t
  case twA => rfl
  case D | twD =>
    simp only [CFSG.StandardType.markTag, CFSG.StandardType.markRank] at h1 h2
    split_ifs at h1 h2 <;> first | omega | exact absurd h1 (by decide)
  all_goals simp [CFSG.StandardType.markTag, CFSG.StandardType.markRank,
    CFSG.StandardType.markChar] at h1 h2 h3 ⊢

private theorem primePower_p_eq_two_of_card_eight {q : TauCeti.PrimePower} (h : q.card = 8) :
    q.p = 2 := by
  rw [TauCeti.PrimePower.card_def] at h
  have h1 : q.p ∣ 2 ^ 3 := by
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← h]
    exact dvd_pow_self q.p (Nat.pos_iff_ne_zero.mp q.exponent_pos)
  exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow h1)

private theorem mem_of_mem_ggInndiag {R : Type} [Group R] {I : Set (MulAut R)}
    (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I)
    (hinn : ∀ r : R, MulAut.conj r ∈ I) {φ : MulAut R}
    (h : φ ∈ CFSG.StandardType.ggInndiag R I) : φ ∈ I := by
  let Isub : Subgroup (MulAut R) :=
    { carrier := I
      mul_mem' := fun {φ ψ} hφ hψ => hmul φ hφ ψ hψ
      one_mem' := by simpa using hinn 1
      inv_mem' := fun {φ} hφ => hinv φ hφ }
  have : CFSG.StandardType.ggInndiag R I ≤ Isub := by
    refine sup_le ?_ ?_
    · rintro _ ⟨r, rfl⟩
      exact hinn r
    · exact (Subgroup.closure_le Isub).2 fun φ hφ => hφ
  exact this h

section Final


theorem u9_innDiagOn_of_indAut_mem_innAutDerived
    {Γ : Type} [Group Γ] {J : Subgroup Γ} {a : Γ}
    (haJ : a ∈ Subgroup.normalizer (J : Set Γ)) (hq : CFSG.Open.IsQuasisimple (PQuot 3 J))
    (hJU : catalogIs (PSimple 3 J) S9.isU3eight)
    (h : MI.indAut 3 J a haJ ∈ innAutDerived (PSimple 3 J)) :
    S10.InnDiagOn 3 (Subgroup.zpowers a) J := by
  refine ⟨Subgroup.zpowers_le.2 haJ, ?_⟩
  obtain ⟨q, hv, hq8, ⟨e⟩⟩ := CatB.lieIndex_isU3eight hJU
  have hp2 := primePower_p_eq_two_of_card_eight hq8
  have hLM : CFSG.Blueprint.LieModel (PSimple 3 J) CFSG.Open.StatedLieTag.PSU 3 2 q.exponent := by
    have h1 := CFSG.Models.lieModel_twistedA 2 q hv e
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ = 2 :=
      (TauCeti.LieTypeIndex.characteristic_twistedA 2 q).trans hp2
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA 2 q, hv⟩ =
        q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
    rw [hc, hf] at h1
    exact CFSG.Models.LieModel.toBlueprint (by decide) h1
  obtain ⟨hX, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hLM
  obtain ⟨R₀, _, I₀, F₀, -, -, -, hP⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  have htag := unitary_label_of_markTag ⟨hP.1, hP.2.1, hP.2.2.1⟩
  have hnd : ¬ MI.DerivedLab lab := by
    rintro (h | h) <;> rw [htag] at h <;> exact absurd h (by decide)
  have hcomm : MI.CAll lab
      (CFSG.StandardType.LargeEvenSimpleGuard CFSG.StandardType.GGInndiagCommEq) :=
    (MI.canonAll_iff_legacyAll hlab hnd _).2
      (CFSG.StandardType.largeEvenLabelAll_inndiagComm_unitary hlab (Or.inl htag))
  have hbody := MI.canonRawInn' Nat.prime_three (by norm_num) hlab
  refine ⟨hX, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_
    ((hbody.and hcomm) _ hraw)⟩
  rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hb, hc⟩
  refine ⟨hs, hna, θ, fun a' ha' => ?_⟩
  obtain ⟨hmul, hinv, hinn, -⟩ := hb hs hna
  have hEq : CFSG.StandardType.ggInndiag R I = CFSG.StandardType.ggInndiagComm R := hc hs hna
  have ha'N : a' ∈ Subgroup.normalizer (J : Set Γ) := Subgroup.zpowers_le.2 haJ ha'
  refine ⟨MulAut.congr θ (MI.indAut 3 J a' ha'N), ?_, (MI.induces_indRel_iff ha'N θ).2 rfl⟩
  apply mem_of_mem_ggInndiag hmul hinv hinn
  rw [hEq, CFSG.StandardType.ggInndiagComm_eq_innAutDerived,
    CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr]
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
  have e' : MI.indAut 3 J (a ^ k) ha'N = (MI.indAut 3 J a haJ) ^ k := by
    unfold MI.indAut
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simp [zpow_neg, inv_zpow])
  rw [e']
  exact Subgroup.zpow_mem _ h k

end Final

end CFSG.LocalAnalysis.GLTheoremA.I141F
