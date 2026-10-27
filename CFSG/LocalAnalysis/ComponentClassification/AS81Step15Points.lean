module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Points
public import CFSG.LocalAnalysis.ComponentClassification.AS81L34Transport
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourReduce
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step13

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard

variable {G : Type} [Group G] [Finite G]

section Conj

variable {A : Subgroup G} (g : G)

@[expose] noncomputable def rightConjugateEquiv : ↥(rightConjugate A g) ≃* ↥A :=
  (A.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm

@[expose] noncomputable def rightConjugateQuotEquiv :
    rankTwoQuot (rightConjugate A g) ≃* rankTwoQuot A :=
  QuotientGroup.congr (center _) (center _) (rightConjugateEquiv g)
    (Subgroup.map_center_eq (rightConjugateEquiv g))

omit [Finite G] in
theorem isQuasisimple_rightConjugate (hq : CFSG.Open.IsQuasisimple ↥A) :
    CFSG.Open.IsQuasisimple ↥(rightConjugate A g) := by
  refine ⟨?_, ?_⟩
  · have : Group.IsPerfect ↥A := (Group.isPerfect_def).2 hq.1
    exact (Group.isPerfect_def).1 (Group.IsPerfect.ofSurjective
      (f := (rightConjugateEquiv g).symm.toMonoidHom) (rightConjugateEquiv g).symm.surjective)
  · have := hq.2
    exact (rightConjugateQuotEquiv g).isSimpleGroup

omit [Finite G] in
theorem typeL34_rightConjugate (hL : TypeL34 (rankTwoQuot A)) :
    TypeL34 (rankTwoQuot (rightConjugate A g)) :=
  RankTwoL3Four.statedClassicalModel_of_mulEquiv (rightConjugateQuotEquiv g) hL

omit [Finite G] in
theorem card_center_rightConjugate :
    Nat.card (center ↥(rightConjugate A g)) = Nat.card (center ↥A) :=
  Nat.card_congr (Subgroup.centerCongr (rightConjugateEquiv g)).toEquiv

end Conj

theorem inf_eq_bot_of_odd_center {A R : Subgroup G} (hRA : R ≤ centralizer (A : Set G))
    (hR : IsPGroup 2 R) (hodd : Odd (Nat.card (center ↥A))) : R ⊓ A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  rintro x ⟨hxR, hxA⟩
  rw [mem_bot]
  have hxZ : (⟨x, hxA⟩ : ↥A) ∈ center ↥A := mem_center_iff.mpr fun a =>
    Subtype.ext (mem_centralizer_iff.mp (hRA hxR) a a.2)
  have h1 : orderOf x ∣ Nat.card (center ↥A) := by
    have := orderOf_dvd_natCard (⟨⟨x, hxA⟩, hxZ⟩ : ↥(center ↥A))
    simpa [Subgroup.orderOf_mk] using this
  have h2 : IsPGroup 2 (zpowers x) := hR.to_le (zpowers_le.mpr hxR)
  exact eq_one_of_isPGroup_zpowers_of_odd h2 (hodd.of_dvd_nat h1)

section Frame

variable {A R : Subgroup G} {g : G} {E F : Subgroup G}

omit [Finite G] in
theorem pointsIn_rightConjugate (R E : Subgroup G) (g : G) :
    pointsIn (rightConjugate R g) E = pointsIn R E := by
  ext Q
  constructor
  · rintro ⟨hQE, x, rfl⟩
    exact ⟨hQE, g * x, rightConjugate_mul R g x⟩
  · rintro ⟨hQE, x, rfl⟩
    refine ⟨hQE, g⁻¹ * x, ?_⟩
    rw [rightConjugate_mul, mul_inv_cancel_left]

theorem le_sup_of_frame {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) : E ≤ rightConjugate A g ⊔ rightConjugate R g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstd := hF.base.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hKg : rightConjugate (centralizer (A : Set G)) g =
      centralizer (rightConjugate A g : Set G) := AschbacherTheorem3.rightConjugate_centralizer A g
  have hRg : IsSylowOf 2 (rightConjugate R g) (centralizer (rightConjugate A g : Set G)) :=
    hKg ▸ AschbacherTheorem3.isSylowOf_rightConjugate hF.sylowR g
  have hRge : IsElemAbelian 2 (rightConjugate R g) := AS76b.isElemAbelian_rightConjugate hF.elemR g
  have hRgE : rightConjugate R g ≤ E := by
    have := hF.inf_eq ▸ (le_sup_right : rightConjugate R g ≤ R ⊔ rightConjugate R g)
    exact this.trans inf_le_left
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hR1 : R ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hF.sylowR hKte.1
  have hRg1 : rightConjugate R g ≠ ⊥ := by
    intro h
    apply hR1
    rw [← Subgroup.card_eq_one, ← rightConjugate_card R g, h, Subgroup.card_bot]
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hRg1
  have hKgte : TightlyEmbedded (centralizer (rightConjugate A g : Set G)) :=
    hKg ▸ RankTwoSporadic.tightlyEmbedded_rightConjugate' hKte g
  have hNKg : normalizer (centralizer (rightConjugate A g : Set G) : Set G) =
      normalizer (rightConjugate A g : Set G) := by
    rw [← hKg, ← AschbacherTheorem3.rightConjugate_normalizer, hNK,
      AschbacherTheorem3.rightConjugate_normalizer]
  have hEN : E ≤ normalizer (rightConjugate A g : Set G) := by
    intro e he
    rw [← hNKg]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hKgte (hRg.le x.2)
      (fun h => hx1 (Subtype.ext h)) (hRge.2 _ x.2) (hcomm e he _ (hRgE x.2))
  have hAgperf : commutator ↥(rightConjugate A g) = ⊤ :=
    (isQuasisimple_rightConjugate g hstd.1).1
  obtain ⟨e₀⟩ := PSL3Four.nonempty_equiv_of_stated (↥A ⧸ center ↥A) hL
  have hle := le_sup_centralizer_of_sixteen_le hE16 hAgperf
    ((rightConjugateQuotEquiv g).trans e₀) hRg hEN hF.elemE
    (by rw [rightConjugate_card, hF.cardR, hF.cardE])
  refine le_sup_of_le_sup_normalizer hRg (isPGroup_two_of_isElemAbelian hF.elemE)
    (fun e he => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun r hr =>
      hcomm r (hRgE hr) e he)) hle

theorem step15_points (h11 : Step11) {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) (hF : Frame G A A R g E F)
    (hL : TypeL34 (rankTwoQuot A)) (hodd : Odd (Nat.card (center ↥A))) :
    (∀ e ∈ E, e ∉ A → ∃ Q ∈ pointsIn R E, e ∈ Q) ∧
      (∀ Q₁ ∈ pointsIn R E, ∀ Q₂ ∈ pointsIn R E, Q₁ ≠ Q₂ → Q₁ ⊓ Q₂ = ⊥) ∧
      Nat.card (pointsIn R E) = 16 ∧
      (∀ Q ∈ pointsIn R E, Q ≠ R → ∃ n ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G),
        Q = rightConjugate (rightConjugate R g) n⁻¹) ∧
      (∀ Q ∈ pointsIn R E, Q ≠ rightConjugate R g →
        ∃ n ∈ rightConjugate A g ⊓ normalizer ((E ⊓ rightConjugate A g : Subgroup G) : Set G),
          Q = rightConjugate R n⁻¹) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := hF.base
  have hstd := hB.hyp.standard
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hR := hF.sylowR
  have hRA : R ≤ centralizer (A : Set G) := hR.le
  have h13 := step13L34_of h11 hE16
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hF.elemE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRgE : rightConjugate R g ≤ E := by
    have := hF.inf_eq ▸ (le_sup_right : rightConjugate R g ≤ R ⊔ rightConjugate R g)
    exact this.trans inf_le_left
  have hRA1 : R ⊓ A = ⊥ := inf_eq_bot_of_odd_center hRA hR.isPGroup hodd
  have hR1 : R ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hR hKte.1
  have hgK : g ∉ normalizer (centralizer (A : Set G) : Set G) := hNK ▸ hF.not_mem
  have hRRg : R ⊓ rightConjugate R g = ⊥ := by
    have h := two_subgroup_inf_conjugate_eq_bot _ (R ⊓ rightConjugate R g) hKte
      (hR.isPGroup.to_le inf_le_left) g hgK
      (inf_le_right.trans (AschbacherTheorem3.rightConjugate_le_rightConjugate hRA g))
    rwa [inf_eq_left.mpr (inf_le_left.trans hRA)] at h
  have hRgR : rightConjugate R g ≠ R := fun h => hR1 (by rw [h, inf_idem] at hRRg; exact hRRg)
  have hfix : ∀ x : G, x ∈ normalizer (A : Set G) →
      rightConjugate R x ≤ centralizer (R : Set G) → rightConjugate R x = R := by
    intro x hx hxc
    have hxK : x ∈ normalizer (centralizer (A : Set G) : Set G) := hNK ▸ hx
    have hRx : IsSylowOf 2 (rightConjugate R x) (centralizer (A : Set G)) := by
      have := AschbacherTheorem3.isSylowOf_rightConjugate hR x
      rwa [(rightConjugate_eq_self_iff _ x).mpr hxK] at this
    have hN : rightConjugate R x ≤ normalizer (R : Set G) :=
      hxc.trans (Subgroup.centralizer_le_normalizer _)
    have h2 := hR.isPGroup.to_sup_of_normal_left' hRx.isPGroup hN
    have h1 := hR.eq_of_le le_sup_left (sup_le hR.le hRx.le) h2
    have h3 := hRx.eq_of_le le_sup_right (sup_le hR.le hRx.le) h2
    rw [← h3, h1]
  have hcR : ∀ Q ∈ pointsIn R E, Q ≤ centralizer (R : Set G) := fun Q hQ y hy =>
    mem_centralizer_iff.mpr fun z hz => hcomm z (hF.R_le_E hz) y (hQ.1 hy)
  have hpts : ∀ Q ∈ pointsIn R E, Q ≠ R → Q ⊓ A = ⊥ := by
    rintro Q ⟨hQE, x, rfl⟩ hQR
    have hxc := hcR _ ⟨hQE, x, rfl⟩
    have hxN : x ∉ normalizer (A : Set G) := fun hx => hQR (hfix x hx hxc)
    exact (h13 G A hB hL R hR x hxN hxc).2.2 hodd
  have hEA16 : Nat.card (E ⊓ A : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRA hF.R_le_E hF.E_le hRA1
    rw [hF.cardE, hF.cardR] at this
    omega
  have htrans : ∀ h ∈ E ⊓ A, ∀ h' ∈ E ⊓ A, h ≠ 1 → h' ≠ 1 →
      ∃ n ∈ A ⊓ normalizer ((E ⊓ A : Subgroup G) : Set G), n * h * n⁻¹ = h' :=
    fun h hh h' hh' h1 h1' => exists_conj_eq_of_card_sixteen hstd.1 hL hodd inf_le_right
      (AS76b.IsElemAbelian.mono hF.elemE inf_le_left) hEA16 hh hh' h1 h1'
  have hQ₀ : rightConjugate R g ∈ pointsIn R E := ⟨hRgE, g, rfl⟩
  refine ⟨fun e he heA => ?_, fun Q₁ hQ₁ Q₂ hQ₂ hne =>
      inf_eq_bot_of_mem_pointsIn hKte hR hcomm hQ₁ hQ₂ hne,
    card_pointsIn hKte hR hF.elemE hF.R_le_E hF.E_le hRA1 hpts htrans hQ₀ hRgR hF.cardE hF.cardR,
    fun Q hQ hQR => exists_eq_rightConjugate_of_mem_pointsIn hKte hR hF.elemE hF.R_le_E hF.E_le
      hRA1 hpts htrans hQ₀ hRgR hQ hQR, fun Q hQ hQRg => ?_⟩
  · rcases exists_mem_rightConjugate_of_not_mem hKte hR hF.elemE hF.R_le_E hF.E_le hRA1 hpts
      htrans hQ₀ hRgR he heA with heR | ⟨n, hn, hen⟩
    · exact ⟨R, self_mem_pointsIn hF.R_le_E, heR⟩
    · have hnN : n⁻¹ ∈ normalizer (E : Set G) := by
        refine (normalizer (E : Set G)).inv_mem ?_
        rw [eq_inf_sup_of_le_sup hRA hF.R_le_E hF.E_le]
        exact mem_normalizer_sup hn.2 (Subgroup.centralizer_le_normalizer _
          (mem_centralizer_iff.mpr fun r hr => (mem_centralizer_iff.mp (hRA hr) n hn.1).symm))
      exact ⟨_, rightConjugate_mem_pointsIn hQ₀ hnN, hen⟩
  have hKg : rightConjugate (centralizer (A : Set G)) g =
      centralizer (rightConjugate A g : Set G) := AschbacherTheorem3.rightConjugate_centralizer A g
  have hKgte : TightlyEmbedded (centralizer (rightConjugate A g : Set G)) :=
    hKg ▸ RankTwoSporadic.tightlyEmbedded_rightConjugate' hKte g
  have hRg : IsSylowOf 2 (rightConjugate R g) (centralizer (rightConjugate A g : Set G)) :=
    hKg ▸ AschbacherTheorem3.isSylowOf_rightConjugate hR g
  have hEARg := le_sup_of_frame hE16 hF hL
  have hRA1g : rightConjugate R g ⊓ rightConjugate A g = ⊥ := by
    rw [← AschbacherTheorem3.rightConjugate_inf, hRA1, AschbacherTheorem3.rightConjugate_bot]
  have hptsg : ∀ Q ∈ pointsIn (rightConjugate R g) E, Q ≠ rightConjugate R g →
      Q ⊓ rightConjugate A g = ⊥ := by
    rw [pointsIn_rightConjugate]
    rintro Q ⟨hQE, x, rfl⟩ hQR
    have hconj : rightConjugate R (x * g⁻¹) = rightConjugate (rightConjugate R x) g⁻¹ := by
      rw [rightConjugate_mul]
    have hxc : rightConjugate R (x * g⁻¹) ≤ centralizer (R : Set G) := by
      intro y hy
      rw [hconj, mem_rightConjugate_iff, inv_inv] at hy
      rw [mem_centralizer_iff]
      intro r hr
      have h1 := hcomm _ (hRgE ((mem_rightConjugate_iff R g (g⁻¹ * r * g)).mpr (by
        simpa [mul_assoc] using hr))) _ (hQE hy)
      calc r * y = g * ((g⁻¹ * r * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
        _ = y * r := by group
    have hxN : x * g⁻¹ ∉ normalizer (A : Set G) := by
      intro hx
      apply hQR
      have h2 := congrArg (fun H => rightConjugate H g) (hfix _ hx hxc)
      simp only [rightConjugate_mul, inv_mul_cancel_right] at h2
      exact h2
    have h := (h13 G A hB hL R hR _ hxN hxc).2.2 hodd
    have h' := congrArg (fun H => rightConjugate H g) h
    simp only [AschbacherTheorem3.rightConjugate_inf, AschbacherTheorem3.rightConjugate_bot,
      rightConjugate_mul, inv_mul_cancel_right] at h'
    exact h'
  have hEAg16 : Nat.card (E ⊓ rightConjugate A g : Subgroup G) = 16 := by
    have := card_eq_card_inf_mul hRg.le hRgE hEARg hRA1g
    rw [hF.cardE, rightConjugate_card, hF.cardR] at this
    omega
  have hoddg : Odd (Nat.card (center ↥(rightConjugate A g))) := by
    rw [card_center_rightConjugate]
    exact hodd
  have htransg : ∀ h ∈ E ⊓ rightConjugate A g, ∀ h' ∈ E ⊓ rightConjugate A g, h ≠ 1 → h' ≠ 1 →
      ∃ n ∈ rightConjugate A g ⊓ normalizer ((E ⊓ rightConjugate A g : Subgroup G) : Set G),
        n * h * n⁻¹ = h' :=
    fun h hh h' hh' h1 h1' => exists_conj_eq_of_card_sixteen
      (isQuasisimple_rightConjugate g hstd.1) (typeL34_rightConjugate g hL) hoddg inf_le_right
      (AS76b.IsElemAbelian.mono hF.elemE inf_le_left) hEAg16 hh hh' h1 h1'
  have hR₀ : R ∈ pointsIn (rightConjugate R g) E := by
    rw [pointsIn_rightConjugate]
    exact self_mem_pointsIn hF.R_le_E
  rw [← pointsIn_rightConjugate R E g] at hQ
  exact exists_eq_rightConjugate_of_mem_pointsIn hKgte hRg hF.elemE hRgE hEARg hRA1g hptsg
    htransg hR₀ hRgR.symm hQ hQRg

end Frame

end CFSG.ComponentClassification.AS81
