module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeZInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKNormalClaim
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKNormalCore
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma514G
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS
  CFSG.ComponentClassification.UnbalancedLayer

@[expose] def IsHeldKType (G : Type) [Group G] : Prop :=
  Group.IsPerfect G ∧ Nat.card (center G) = 4 ∧ (∀ z ∈ center G, z * z = 1) ∧
    IsL34Type (G ⧸ center G)

theorem isQuasisimple_of_perfect_of_simple_quot {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) : IsQuasisimple Q := by
  refine ⟨hperf, hs, ?_⟩
  by_contra hno
  push Not at hno
  have hle : commutator Q ≤ Subgroup.center Q := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def, ← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]
    exact hno _ _
  rw [hperf.commutator_eq_top, top_le_iff] at hle
  have := hs
  obtain ⟨y, hy⟩ := exists_ne (1 : Q ⧸ Subgroup.center Q)
  obtain ⟨y0, rfl⟩ := QuotientGroup.mk_surjective y
  apply hy
  rw [QuotientGroup.eq_one_iff, hle]
  exact Subgroup.mem_top y0

theorem IsHeldKType.isQuasisimple {G : Type} [Group G] (h : IsHeldKType G) : IsQuasisimple G := by
  obtain ⟨hp, -, -, hq⟩ := h
  have hs : IsSimpleGroup (G ⧸ center G) :=
    (LieType.Simplicity.fam_PSL_simplicity _ 3 2 2
      (GSThmB.statedClassicalModel_of_lieModel_ne_zero (by norm_num) hq)).2
  exact isQuasisimple_of_perfect_of_simple_quot hp hs

theorem IsHeldKType.of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : IsHeldKType G) : IsHeldKType H := by
  obtain ⟨hp, hc, hz, hq⟩ := h
  have hcen : (center G).map (e : G →* H) = center H := Subgroup.map_center_eq e
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Group.isPerfect_def, _root_.commutator_def] at hp ⊢
    rw [← Subgroup.map_top_of_surjective (e : G →* H) e.surjective, ← Subgroup.map_commutator, hp]
  · rw [← hcen, Subgroup.card_map_of_injective e.injective]
    exact hc
  · intro z hz'
    rw [← hcen] at hz'
    obtain ⟨z', hz'c, rfl⟩ := hz'
    rw [← map_mul, hz z' hz'c, map_one]
  · exact LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.congr _ _ e hcen) hq

theorem IsHeldKType.fusionZStar_eq_center {G : Type} [Group G] [Finite G] (h : IsHeldKType G) :
    Open.fusionZStar G = center G := by
  have hq := h.isQuasisimple
  obtain ⟨-, hc, hz, -⟩ := h
  have hodd : Open.fusionOddCore G = ⊥ := by
    refine le_bot_iff.mp (sSup_le fun N hN => ?_)
    obtain ⟨hNn, hNodd⟩ := hN
    rcases LocalCores.quasisimple_normal_subgroups hq hNn with hNtop | hNz
    · exfalso
      rw [hNtop, Subgroup.card_top] at hNodd
      have h2 : 2 ∣ Nat.card G := by
        have := Subgroup.card_subgroup_dvd_card (center G)
        rw [hc] at this
        exact (by norm_num : 2 ∣ 4).trans this
      exact (Nat.not_even_iff_odd.mpr hNodd) (even_iff_two_dvd.mpr h2)
    · intro x hx
      rw [Subgroup.mem_bot]
      have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hz x (hNz hx))
      have h2 : orderOf x ∣ Nat.card N := by
        have := Subgroup.orderOf_dvd_natCard N hx
        simpa using this
      have h3 : Odd (orderOf x) := hNodd.of_dvd_nat h2
      have h4 : orderOf x = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h5 | h5
        · exact h5
        · rw [h5] at h3
          exact absurd h3 (by decide)
      exact orderOf_eq_one_iff.mp h4
  ext x
  constructor
  · intro hx
    rw [Open.fusionZStar, mem_comap, mem_center_iff] at hx
    rw [mem_center_iff]
    intro g
    have h1 := hx (QuotientGroup.mk' (Open.fusionOddCore G) g)
    rw [← map_mul, ← map_mul] at h1
    have h2 : (g * x)⁻¹ * (x * g) ∈ Open.fusionOddCore G := QuotientGroup.eq.mp h1
    rw [hodd, Subgroup.mem_bot] at h2
    calc g * x = (g * x) * ((g * x)⁻¹ * (x * g)) := by rw [h2, mul_one]
      _ = x * g := by group
  · intro hx
    rw [Open.fusionZStar, mem_comap, mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Open.fusionOddCore G) q
    show QuotientGroup.mk' (Open.fusionOddCore G) g * QuotientGroup.mk' (Open.fusionOddCore G) x =
      QuotientGroup.mk' (Open.fusionOddCore G) x * QuotientGroup.mk' (Open.fusionOddCore G) g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx g]

theorem IsHeldKType.isL34_fusionZStar {G : Type} [Group G] [Finite G] (h : IsHeldKType G) :
    IsL34Type (G ⧸ Open.fusionZStar G) :=
  LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq h.fusionZStar_eq_center).symm h.2.2.2

theorem exists_involution_of_fact (hFact : L34InvolutionCentralizerFact) {X : Type} [Group X]
    [Finite X] {K' : Subgroup X} (hK' : IsHeldKType ↥K') {τ : X}
    (hτ : τ ∈ normalizer (K' : Set X)) (hττ : τ * τ = 1) :
    ∃ w ∈ K', w * w = 1 ∧ w * τ = τ * w ∧ ¬ (∀ k ∈ K', w * k = k * w) ∧
      ¬ (∀ k ∈ K', (w⁻¹ * τ) * k = k * (w⁻¹ * τ)) := by
  obtain ⟨w, hwK, hww, hwτ, hwz, hwc⟩ :=
    hFact X K' τ (isPerfect_iff.mp hK'.1) hK'.isL34_fusionZStar hττ hτ
  refine ⟨w, hwK, hww, hwτ, fun hcomm => hwz ?_, fun hcomm => hwc ?_⟩
  · refine ⟨⟨w, hwK⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, hK'.fusionZStar_eq_center, mem_center_iff]
    intro g
    exact Subtype.ext (hcomm g g.2).symm
  · have hgC : w⁻¹ * τ ∈ centralizer (K' : Set X) :=
      mem_centralizer_iff.mpr fun h hh => (hcomm h hh).symm
    rw [mem_coreActionKernel]
    refine ⟨centralizer_le_normalizer _ hgC, fun j hj => ?_⟩
    have : j⁻¹ * (w⁻¹ * τ)⁻¹ * j * (w⁻¹ * τ) = 1 := by
      calc j⁻¹ * (w⁻¹ * τ)⁻¹ * j * (w⁻¹ * τ) = j⁻¹ * (w⁻¹ * τ)⁻¹ * (j * (w⁻¹ * τ)) := by group
        _ = j⁻¹ * (w⁻¹ * τ)⁻¹ * ((w⁻¹ * τ) * j) := by rw [hcomm j hj]
        _ = 1 := by group
    rw [this]
    exact one_mem _

theorem heldKNormalAt_of_inputs (hLay : HeldTwoALayerFact) (hAK : HeldTwoAKFact)
    (hInv : HeldInvolAutFact) (hFact : L34InvolutionCentralizerFact) {X : Type} [Group X]
    [Finite X] {L : Subgroup X} (hset : HeldEndSetting X L) {u : X} (hu : HeldTwoA L u)
    (hsub : ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))).IsSubnormal) :
    ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))).Normal ∧
      ∀ K₁ : Subgroup X, K₁ ≤ centralizer ({u} : Set X) →
        (K₁.subgroupOf (centralizer ({u} : Set X))).Normal →
        Nonempty (↥K₁ ≃* ↥(gsFixedLayer L u)) → K₁ = gsFixedLayer L u := by
  obtain ⟨⟨-, -, -, -, -, ⟨a, ha2, hLa, -⟩, -⟩, -, hstd, ⟨eL⟩, hrank⟩ := id hset
  have hKLD : gsFixedLayer L u ≤ L ⊓ centralizer ({u} : Set X) := gsFixedLayer_le_inf L u
  have hKL : gsFixedLayer L u ≤ L := hKLD.trans inf_le_left
  have hKD : gsFixedLayer L u ≤ centralizer ({u} : Set X) := hKLD.trans inf_le_right
  obtain ⟨hKp, hKt⟩ := hLay X L ⟨eL⟩ u hu
  obtain ⟨hKcen, -, hKC⟩ := hAK X L ⟨eL⟩ u hu
  have hKel : ∀ z ∈ center ↥(gsFixedLayer L u), z * z = 1 := by
    intro z hz
    have hzc : ∀ k ∈ gsFixedLayer L u, (z : X) * k = k * z := fun k hk =>
      (congrArg Subtype.val (mem_center_iff.mp hz ⟨k, hk⟩)).symm
    rcases hKC (z : X) (hKL z.2) hzc with h | ⟨hzA, -⟩
    · exact Subtype.ext (by simp [h])
    · have hsq : (z : X) * z = 1 := by rw [← sq, ← hzA.2.1, pow_orderOf_eq_one]
      exact Subtype.ext (by simpa using hsq)
  have hKtype : IsHeldKType ↥(gsFixedLayer L u) := ⟨isPerfect_iff.mpr hKp, hKcen, hKel, hKt⟩
  have hKq : IsQuasisimple ↥(gsFixedLayer L u) := hKtype.isQuasisimple
  have hKcomp : IsComponent ((gsFixedLayer L u).subgroupOf (centralizer ({u} : Set X))) :=
    ⟨LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hKD).symm hKq, hsub⟩
  have haC : a ∈ centralizer (L : Set X) :=
    mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hLa hh)
  have haa : a * a = 1 := by rw [← sq, ← ha2, pow_orderOf_eq_one]
  have haD : a ∈ centralizer ({u} : Set X) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp haC u hu.1).symm
  have haK : ∀ k ∈ gsFixedLayer L u, a * k = k * a := fun k hk =>
    (mem_centralizer_iff.mp haC k (hKL hk)).symm
  have hZK : (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype ≤ gsFixedLayer L u :=
    Subgroup.map_subtype_le _
  have hKcard : 15120 < Nat.card ↥(gsFixedLayer L u) := by
    have h1 := card_eq_card_quotient_mul_card_subgroup (center ↥(gsFixedLayer L u))
    rw [GSThmB.card_of_lieModel_L34 hKt, hKcen] at h1
    omega
  have hI : ∀ v : X, v * v = 1 → a * v = v * a → (∀ k ∈ gsFixedLayer L u, v * k = k * v) →
      ∃ z ∈ (center ↥(gsFixedLayer L u)).map (gsFixedLayer L u).subtype, v = z ∨ v = z * a :=
    fun v hv hav hvK => HeKN.exists_eq_mul_of_involution ha2 haC hrank
      (HeKN.centralizer_le_normalizer hstd haC ha2) hKL
      (fun y hy hyK => by
        rcases hKC y hy hyK with h | ⟨-, h⟩
        · rw [h]; exact one_mem _
        · exact h)
      (fun n hn hnn hnC => by
        rcases hInv X L ⟨eL⟩ n hn hnn hnC with h | ⟨-, -, hS, -⟩
        · exact Or.inl h
        · exact Or.inr hS)
      hKcard hv hav hvK
  have hP : ∀ g ∈ centralizer ({u} : Set X),
      IsHeldKType ↥((gsFixedLayer L u).map (MulAut.conj g).toMonoidHom) := fun g _ =>
    IsHeldKType.of_mulEquiv ((gsFixedLayer L u).equivMapOfInjective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective) hKtype
  have hKA : ∀ K' : Subgroup X, IsHeldKType ↥K' → ∀ τ ∈ normalizer (K' : Set X), τ * τ = 1 →
      ∃ w ∈ K', w * w = 1 ∧ w * τ = τ * w ∧ ¬ (∀ k ∈ K', w * k = k * w) ∧
        ¬ (∀ k ∈ K', (w⁻¹ * τ) * k = k * (w⁻¹ * τ)) :=
    fun K' hK' τ hτ hττ => exists_involution_of_fact hFact hK' hτ hττ
  have hnormal := HeKN.normal_of_key (fun K' => IsHeldKType ↥K') hKD haD haa haK hZK hKcomp hI hP
    hKA
  refine ⟨hnormal, ?_⟩
  rintro K₁ hK₁D hK₁n ⟨e⟩
  exact HeKN.eq_of_key (fun K' => IsHeldKType ↥K') hKD hK₁D haD haa haK hZK hKq
    (LocalCores.isQuasisimple_of_mulEquiv e.symm hKq) hnormal hK₁n hI
    (IsHeldKType.of_mulEquiv e.symm hKtype) hKA

end CFSG.ComponentClassification.GrSLit
