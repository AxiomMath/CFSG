module

public import CFSG.ClassicalInvolution.Q3.Q3CPThin
public import CFSG.ClassicalInvolution.SmallCases.NDBH2
public import CFSG.ClassicalInvolution.Q3.Q3CPSat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Asc77

section Defs

@[expose] def L67Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)),
    Disconnected.AschTight.HypOmegaGen Ω →
    ∀ S : Sylow 2 G, ∀ R ∈ RSet Ω, ∀ R' ∈ RSet Ω, R ≤ (S : Subgroup G) → R' ≤ (S : Subgroup G) →
      R ≠ R' → Commutes R R'

@[expose] def Loc26False3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G) (Q Q' : Subgroup G),
    HypOmegaModU (.sl2 3 1) Ω → (∀ M ∈ Ω, AEmpty Ω M) → K ∈ Ω →
    (∀ M ∈ Ω, ∃ g : G, conjSub g K = M) → (∀ K' ∈ twinSet Ω K, K' = K) →
    IsUniqueInvolution K z → J ∈ omegaNbr Ω K → IsUniqueInvolution J t →
    (R ∈ RSet Ω ∧ R ≤ K ∧ R ≤ (S : Subgroup G)) → (T ∈ RSet Ω ∧ T ≤ J ∧ T ≤ (S : Subgroup G)) →
    (W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧ ∀ s ∈ (S : Subgroup G), conjSub s W = W) →
    T8R.Loc.Loc26 Ω K J S R T z t Q → T8R.Loc.Loc26 Ω J K S T R t z Q' → False

end Defs

section Generic

variable {G : Type} [Group G] [Finite G]

theorem exists_W_of_hypOmegaGen {Ω : Set (Subgroup G)}
    (hgen : Disconnected.AschTight.HypOmegaGen Ω) (S : Sylow 2 G) :
    ∃ W : Subgroup G, W ∈ WSet Ω ∧ W ≤ (S : Subgroup G) ∧
      ∀ s ∈ (S : Subgroup G), conjSub s W = W := by
  obtain ⟨η, hη, hηinv⟩ :=
    Disconnected.AschTight.Sec6Gen.exists_invariant_mem_etaSet hgen S
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η, U : Subgroup G) : Set G) :=
    Thompson.le_normalizer_biSup_of_acts hηinv
  exact ⟨⨆ U ∈ η, U, ⟨η, ⟨S, hη, hηinv⟩, rfl⟩, iSup₂_le fun U hU => (hη.1 hU).2,
    fun s hs' => mem_normalizer_iff_conjSub_eq.mp (hSN hs')⟩

theorem exists_involution_of_four_le {A : Subgroup G} (hA : IsPGroup 2 A) (h4 : 4 ≤ Nat.card A) :
    ∃ a ∈ A, a * a = 1 ∧ a ≠ 1 := by
  have hdvd : 2 ∣ Nat.card A := by
    rcases hA.card_eq_or_dvd with h | h
    · omega
    · exact h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hdvd
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  refine ⟨(a : G), a.2, ?_, ?_⟩
  · have h2 : (a : G) ^ 2 = 1 := by
      have := congrArg Subtype.val ha2
      simpa using this
    rwa [pow_two] at h2
  · intro h1
    have : a = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ha
    omega

theorem eq_of_isSylow2In_of_le_sylow' {M P Q : Subgroup G} {S : Sylow 2 G}
    (hP : IsSylow2In P M) (hQ : IsSylow2In Q M) (hPS : P ≤ (S : Subgroup G))
    (hQS : Q ≤ (S : Subgroup G)) : P = Q := by
  have h1 : M ⊓ (S : Subgroup G) = P :=
    hP.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hP.1 hPS)
  have h2 : M ⊓ (S : Subgroup G) = Q :=
    hQ.eq_of_le S.isPGroup'.to_inf_right inf_le_left (le_inf hQ.1 hQS)
  exact h1.symm.trans h2

end Generic

section Branch

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

@[expose] def AEmptyAt (K : Subgroup G) (z : G) : Prop :=
  ∀ M ∈ satClass K z, AEmpty (satClass K z) M

theorem exists_raw_containing_sylow (hz : IsClassicalMember3 K z) {M₀ : Subgroup G} {w : G}
    (hM₀ : M₀ ∈ conjClass3 K) (hw : IsClassicalMember3 M₀ w) {P : Subgroup G}
    (hP : IsSylow2In P (satU (.sl2 3 1) M₀ w)) :
    ∃ M₁ : Subgroup G, M₁ ∈ conjClass3 K ∧ IsClassicalMember3 M₁ w ∧ IsSylow2In P M₁ := by
  obtain ⟨P₀, hP₀⟩ := exists_isSylow2In M₀
  have hP₀' : IsSylow2In P₀ (satU (.sl2 3 1) M₀ w) := isSylow2In_satU hw hP₀
  obtain ⟨x, hx, hxP⟩ :=
    Disconnected.AschTight.Sec6Gen.exists_conjSub_eq_of_isSylow2In hP₀' hP
  have hxc : x ∈ Subgroup.centralizer ({w} : Set G) := satU_le_centralizer hw hx
  have hxw : x * w * x⁻¹ = w := by
    have := Subgroup.mem_centralizer_singleton_iff.mp hxc
    calc x * w * x⁻¹ = (w * x) * x⁻¹ := by rw [this]
      _ = w := by group
  refine ⟨conjSub x M₀, (inClass3_conjugates hz).conjInvariant x M₀ hM₀, ?_, ?_⟩
  · have := hw.conj x
    rwa [hxw] at this
  · rw [← hxP]
    exact hP₀.conj x

theorem aEmptyAt_of_not_a2 (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K)) (hA2 : ¬ A2Configuration z K) :
    AEmptyAt K z := by
  have hC := locCommuteAt_of_not_a2Configuration hz hA2
  have hgen := hypOmegaGen_of_loc hnab hz hΔ hB hC
  intro M hM J hJ hJn
  exfalso
  apply hJn
  obtain ⟨hJΩ, hJM, U, hU, hUJ, hUN⟩ := hJ
  obtain ⟨R, hRΩ, J', hJ'Ω, hRJ', hUR, hcyc, hcard, h4⟩ :=
    Disconnected.AschTight.Sec6Gen.exists_data_of_mem_USet hgen hU
  have hU2 : IsPGroup 2 U := Disconnected.AschTight.Sec6Gen.isPGroup_of_mem_USet hgen hU
  obtain ⟨u, huU, hu2, hu1⟩ := exists_involution_of_four_le hU2 h4
  obtain ⟨J₀, y, hJ₀, hy, rfl⟩ := exists_raw_of_mem_satClass hz hJΩ
  obtain ⟨M₀, w, hM₀, hw, rfl⟩ := exists_raw_of_mem_satClass hz hM
  have hyu := isUniqueInvolution_satU hy
  have hwu := isUniqueInvolution_satU hw
  have huy : u = y := (hyu.unique u (hUJ huU) hu2).resolve_left hu1
  have hyw : y * w = w * y := by
    have hconj : conjSub u (satU (.sl2 3 1) M₀ w) = satU (.sl2 3 1) M₀ w :=
      mem_normalizer_iff_conjSub_eq.mp (hUN huU)
    have h1 := hwu.conj u
    rw [hconj] at h1
    have h2 : w = u * w * u⁻¹ := hwu.eq h1
    rw [huy] at h2
    calc y * w = (y * w * y⁻¹) * y := by group
      _ = w * y := by rw [← h2]
  have hne : w ≠ y := by
    intro h
    apply hJM
    have hyw' : IsUniqueInvolution (satU (.sl2 3 1) J₀ y) w := by rw [h]; exact hyu
    exact satClass_eq_of_involution_eq hnab hz hΔ hB hC hJΩ hM hyw' hwu
  have hcomm : Commutes M₀ J₀ :=
    commutes_of_not_a2Configuration3 hz hA2 hM₀ hJ₀ hw hy hne hyw.symm
  obtain ⟨P, hP⟩ := exists_isSylow2In J₀
  have hPc : P ≤ Subgroup.centralizer ({w} : Set G) := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((hcomm w hw.mem p (hP.1 hp)).symm)
  have hPN : P ≤ Subgroup.normalizer ((satU (.sl2 3 1) M₀ w : Subgroup G) : Set G) :=
    hPc.trans (centralizer_le_normalizer_of_mem_satClass hnab hz hΔ hB hC hM hwu)
  have hPsyl : IsSylow2In P (satU (.sl2 3 1) J₀ y) := isSylow2In_satU hy hP
  exact ⟨hJΩ, hJM, P, mem_RSet_of_isSylow2In hJΩ hPsyl, hPsyl.1, hPN⟩

theorem omegaNbr_involution (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z)
    {K₁ : Subgroup G} {z₁ : G} (hK₁ : K₁ ∈ conjClass3 K) (hz₁ : IsClassicalMember3 K₁ z₁)
    {L : Subgroup G} {y : G} (hL : L ∈ omegaNbr (satClass K z) (satU (.sl2 3 1) K₁ z₁))
    (hy : IsUniqueInvolution L y) :
    y ≠ z₁ ∧ z₁ * y = y * z₁ ∧ y ∈ nbrSpan3 (conjClass3 K) K₁ := by
  obtain ⟨hLΩ, hLne, R', hR'Ω, hR'L, hR'N⟩ := hL
  obtain ⟨M, hMΩ, hR'M⟩ := exists_isSylow2In_of_mem_RSet hR'Ω
  obtain ⟨M₀, w, hM₀, hw, rfl⟩ := exists_raw_of_mem_satClass hz hMΩ
  have hwu := isUniqueInvolution_satU hw
  have hwR : w ∈ R' := mem_of_isSylow2In_of_isUniqueInvolution hwu hR'M
  have hwy : w = y := by
    rcases hy.unique w (hR'L hwR) hw.isCentralInvolution.sq with h | h
    · exact absurd h hw.ne_one
    · exact h
  subst hwy
  have hK₁Ω : satU (.sl2 3 1) K₁ z₁ ∈ satClass K z := satU_mem_satClass hz hK₁ hz₁
  have hu₁ := isUniqueInvolution_satU hz₁
  have hR'c : ∀ r ∈ R', r * z₁ = z₁ * r := by
    intro r hr
    have hconj : conjSub r (satU (.sl2 3 1) K₁ z₁) = satU (.sl2 3 1) K₁ z₁ :=
      mem_normalizer_iff_conjSub_eq.mp (hR'N hr)
    have h1 := hu₁.conj r
    rw [hconj] at h1
    have h2 : z₁ = r * z₁ * r⁻¹ := hu₁.eq h1
    calc r * z₁ = (r * z₁ * r⁻¹) * r := by group
      _ = z₁ * r := by rw [← h2]
  have hc : z₁ * w = w * z₁ := (hR'c w hwR).symm
  have hne : w ≠ z₁ := by
    intro h
    apply hLne
    have hy' : IsUniqueInvolution L z₁ := by rw [← h]; exact hy
    exact satClass_eq_of_involution_eq hnab hz hΔ hB hC hLΩ hK₁Ω hy' hu₁
  refine ⟨hne, hc, ?_⟩
  obtain ⟨M₁, hM₁, hw₁, hR'M₁⟩ := exists_raw_containing_sylow hz hM₀ hw hR'M
  exact mem_nbrSpan3_of_involution hC hK₁ hz₁ hM₁ hw₁ hne hc ⟨R', hR'M₁, fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hR'c r hr)⟩

theorem satU_mem_omegaNbr (hnab : ∃ a b : G, a * b ≠ b * a) (hz : IsClassicalMember3 K z)
    (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K)) (hC : LocCommuteAt K z)
    {K₁ K₂ : Subgroup G} {z₁ z₂ : G} (he : IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂)
    {T : Subgroup G} (hT : IsSylow2In T K₂) :
    satU (.sl2 3 1) K₂ z₂ ∈ omegaNbr (satClass K z) (satU (.sl2 3 1) K₁ z₁) := by
  have hK₁Ω := satU_mem_satClass hz he.mem₁ he.cls₁
  have hK₂Ω := satU_mem_satClass hz he.mem₂ he.cls₂
  have hu₁ := isUniqueInvolution_satU he.cls₁
  have hu₂ := isUniqueInvolution_satU he.cls₂
  have hne : satU (.sl2 3 1) K₂ z₂ ≠ satU (.sl2 3 1) K₁ z₁ := by
    intro h
    rw [h] at hu₂
    exact he.ne (hu₁.eq hu₂)
  refine ⟨hK₂Ω, hne, T, mem_RSet_of_isSylow2In hK₂Ω (isSylow2In_satU he.cls₂ hT),
    (isSylow2In_satU he.cls₂ hT).1, ?_⟩
  exact (hT.1.trans he.le_centralizer_left).trans
    (centralizer_le_normalizer_of_mem_satClass hnab hz hΔ hB hC hK₁Ω hu₁)

end Branch

section Loc26

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem loc26_of_thinData (h67 : L67Gen) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hz : IsClassicalMember3 K z) (hΔ : DeltaConnected K) (hB : ¬ BootData3 (conjClass3 K))
    (hC : LocCommuteAt K z) {K₁ K₂ : Subgroup G} {z₁ z₂ : G}
    (h : ThinData (conjClass3 K) K₁ K₂ z₁ z₂) {S : Sylow 2 G} {R T : Subgroup G}
    (hR : IsSylow2In R K₁) (hT : IsSylow2In T K₂) (hRS : R ≤ (S : Subgroup G))
    (hTS : T ≤ (S : Subgroup G)) :
    T8R.Loc.Loc26 (satClass K z) (satU (.sl2 3 1) K₁ z₁) (satU (.sl2 3 1) K₂ z₂) S R T z₁ z₂
      (Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₁)) := by
  have he := h.edge
  have hgen := hypOmegaGen_of_loc hnab hz hΔ hB hC
  have hΩ0 : ConjInvariant (conjClass3 K) := (inClass3_conjugates hz).conjInvariant
  have hK₁Ω := satU_mem_satClass hz he.mem₁ he.cls₁
  have hK₂Ω := satU_mem_satClass hz he.mem₂ he.cls₂
  have hu₁ := isUniqueInvolution_satU he.cls₁
  have hu₂ := isUniqueInvolution_satU he.cls₂
  have hRsat : IsSylow2In R (satU (.sl2 3 1) K₁ z₁) := isSylow2In_satU he.cls₁ hR
  have hTsat : IsSylow2In T (satU (.sl2 3 1) K₂ z₂) := isSylow2In_satU he.cls₂ hT
  have hRΩ : R ∈ RSet (satClass K z) := mem_RSet_of_isSylow2In hK₁Ω hRsat
  have hTΩ : T ∈ RSet (satClass K z) := mem_RSet_of_isSylow2In hK₂Ω hTsat
  have hraw₁ : IsUniqueInvolution K₁ z₁ :=
    (IsClassicalMemberU.ofQ3 he.cls₁).isUniqueInvolution (MemberType.cert_sl2 3 1)
  have hraw₂ : IsUniqueInvolution K₂ z₂ :=
    (IsClassicalMemberU.ofQ3 he.cls₂).isUniqueInvolution (MemberType.cert_sl2 3 1)
  have hz₁R : z₁ ∈ R := mem_of_isSylow2In_of_isUniqueInvolution hraw₁ hR
  have hz₂T : z₂ ∈ T := mem_of_isSylow2In_of_isUniqueInvolution hraw₂ hT
  have hz2sq : z₂ * z₂ = 1 := he.cls₂.isCentralInvolution.sq
  have hz₁c : ∀ x ∈ nbrSpan3 (conjClass3 K) K₁, z₁ * x = x * z₁ := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (nbrSpan3_le_centralizer (conjClass3 K) K₁ hx) z₁
      he.cls₁.mem
  refine ⟨Balance.odd_card_oddCoreIn _, ?_, ?_, ?_, ?_⟩
  ·
    intro P hP hPS
    by_contra hcon
    push Not at hcon
    obtain ⟨M, hMΩ, hPM⟩ := exists_isSylow2In_of_mem_RSet hP
    obtain ⟨M₀, w, hM₀, hw, rfl⟩ := exists_raw_of_mem_satClass hz hMΩ
    have hwu := isUniqueInvolution_satU hw
    have hwP : w ∈ P := mem_of_isSylow2In_of_isUniqueInvolution hwu hPM
    have hcR : Commutes R P :=
      h67 G (satClass K z) hgen S R hRΩ P hP hRS hPS hcon.1.symm
    have hcT : Commutes T P :=
      h67 G (satClass K z) hgen S T hTΩ P hP hTS hPS hcon.2.symm
    have hc₁ : z₁ * w = w * z₁ := hcR z₁ hz₁R w hwP
    have hc₂ : z₂ * w = w * z₂ := hcT z₂ hz₂T w hwP
    by_cases hw1 : w = z₁
    · apply hcon.1
      have hu' : IsUniqueInvolution (satU (.sl2 3 1) M₀ w) z₁ := by rw [← hw1]; exact hwu
      have hMeq := satClass_eq_of_involution_eq hnab hz hΔ hB hC hMΩ hK₁Ω hu' hu₁
      rw [hMeq] at hPM
      exact eq_of_isSylow2In_of_le_sylow' hPM hRsat hPS hRS
    · obtain ⟨M₁, hM₁, hw₁, hPM₁⟩ := exists_raw_containing_sylow hz hM₀ hw hPM
      have hwX : w ∈ nbrSpan3 (conjClass3 K) K₁ :=
        mem_nbrSpan3_of_involution hC he.mem₁ he.cls₁ hM₁ hw₁ hw1 hc₁
          ⟨P, hPM₁, fun p hp => Subgroup.mem_centralizer_singleton_iff.mpr (hcR z₁ hz₁R p hp).symm⟩
      have hwz₂ : w = z₂ := h.eq_of_comm hwX hw.isCentralInvolution.sq hw.ne_one hc₂.symm
      apply hcon.2
      have hu' : IsUniqueInvolution (satU (.sl2 3 1) M₀ w) z₂ := by rw [← hwz₂]; exact hwu
      have hMeq := satClass_eq_of_involution_eq hnab hz hΔ hB hC hMΩ hK₂Ω hu' hu₂
      rw [hMeq] at hPM
      exact eq_of_isSylow2In_of_le_sylow' hPM hTsat hPS hTS
  ·
    intro M hM h4 hMJ hnbr
    obtain ⟨M₀, w, hM₀, hw, rfl⟩ := exists_raw_of_mem_satClass hz hM
    have hwu := isUniqueInvolution_satU hw
    obtain ⟨-, -, hwX⟩ := omegaNbr_involution hnab hz hΔ hB hC he.mem₁ he.cls₁ hnbr hwu
    have hA2g : IsPGroup 2 ↥(satU (.sl2 3 1) M₀ w ⊓ (S : Subgroup G)) :=
      S.isPGroup'.to_inf_right
    obtain ⟨a, haA, ha2, ha1⟩ := exists_involution_of_four_le hA2g h4
    have haw : a = w := (hwu.unique a haA.1 ha2).resolve_left ha1
    have hwS : w ∈ (S : Subgroup G) := haw ▸ haA.2
    have hTX : T ≤ nbrSpan3 (conjClass3 K) K₁ := hT.1.trans h.le_nbrSpan
    have hXS2 : IsPGroup 2 ↥(nbrSpan3 (conjClass3 K) K₁ ⊓ (S : Subgroup G)) :=
      S.isPGroup'.to_inf_right
    have hXST : nbrSpan3 (conjClass3 K) K₁ ⊓ (S : Subgroup G) = T :=
      (h.isSylow2In hT).eq_of_le hXS2 inf_le_left (le_inf hTX hTS)
    have hwT : w ∈ T := by
      rw [← hXST]
      exact Subgroup.mem_inf.mpr ⟨hwX, hwS⟩
    have hwz₂ : w = z₂ :=
      (hraw₂.unique w (hT.1 hwT) hw.isCentralInvolution.sq).resolve_left hw.ne_one
    apply hMJ
    have hu' : IsUniqueInvolution (satU (.sl2 3 1) M₀ w) z₂ := by rw [← hwz₂]; exact hwu
    exact satClass_eq_of_involution_eq hnab hz hΔ hB hC hM hK₂Ω hu' hu₂
  ·
    intro L hL y hy
    obtain ⟨-, -, hyX⟩ := omegaNbr_involution hnab hz hΔ hB hC he.mem₁ he.cls₁ hL hy
    exact h.congr y hyX z₂ h.z₂_mem hy.sq hz2sq hy.ne_one he.cls₂.ne_one
  ·
    intro y hy
    have hyc : y * z₁ = z₁ * y := Subgroup.mem_centralizer_singleton_iff.mp hy
    have hy1 : y * z₁ * y⁻¹ = z₁ := by
      calc y * z₁ * y⁻¹ = (z₁ * y) * y⁻¹ := by rw [hyc]
        _ = z₁ := by group
    have hy2 : y⁻¹ * z₁ * y = z₁ := by
      calc y⁻¹ * z₁ * y = y⁻¹ * (y * z₁ * y⁻¹) * y := by rw [hy1]
        _ = z₁ := by group
    obtain ⟨z₂', hz₂'⟩ : ∃ z₂' : G, z₂' = y * z₂ * y⁻¹ := ⟨_, rfl⟩
    have hcls : IsClassicalMember3 (conjSub y K₂) z₂' := by
      rw [hz₂']
      exact he.cls₂.conj y
    have hmem : conjSub y K₂ ∈ conjClass3 K := hΩ0 y K₂ he.mem₂
    have hne : z₂' ≠ z₁ := by
      intro hh
      apply he.ne
      calc z₁ = y⁻¹ * (y * z₁ * y⁻¹) * y := by group
        _ = y⁻¹ * z₁ * y := by rw [hy1]
        _ = y⁻¹ * z₂' * y := by rw [hh]
        _ = z₂ := by rw [hz₂']; group
    have hcomm : z₁ * z₂' = z₂' * z₁ := by
      have h1 : (y * z₁ * y⁻¹) * (y * z₂ * y⁻¹) = (y * z₂ * y⁻¹) * (y * z₁ * y⁻¹) := by
        calc (y * z₁ * y⁻¹) * (y * z₂ * y⁻¹) = y * (z₁ * z₂) * y⁻¹ := by group
          _ = y * (z₂ * z₁) * y⁻¹ := by rw [he.comm_involutions]
          _ = (y * z₂ * y⁻¹) * (y * z₁ * y⁻¹) := by group
      rw [hy1, ← hz₂'] at h1
      exact h1
    have hle : conjSub y K₂ ≤ Subgroup.centralizer ({z₁} : Set G) := by
      intro k hk
      rw [mem_conjSub_iff] at hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : (y⁻¹ * k * y) * z₁ = z₁ * (y⁻¹ * k * y) :=
        Subgroup.mem_centralizer_singleton_iff.mp (he.le_centralizer_left hk)
      calc k * z₁ = y * ((y⁻¹ * k * y) * (y⁻¹ * z₁ * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * k * y) * z₁) * y⁻¹ := by rw [hy2]
        _ = y * (z₁ * (y⁻¹ * k * y)) * y⁻¹ := by rw [h1]
        _ = (y * z₁ * y⁻¹) * k := by group
        _ = z₁ * k := by rw [hy1]
    obtain ⟨P, hP⟩ := exists_isSylow2In (conjSub y K₂)
    have hX : z₂' ∈ nbrSpan3 (conjClass3 K) K₁ :=
      mem_nbrSpan3_of_involution hC he.mem₁ he.cls₁ hmem hcls hne hcomm ⟨P, hP, hP.1.trans hle⟩
    have hcong := h.congr z₂' hX z₂ h.z₂_mem hcls.isCentralInvolution.sq hz2sq hcls.ne_one
      he.cls₂.ne_one
    have e : y * (z₁ * z₂) * y⁻¹ * (z₁ * z₂)⁻¹ = z₂' * z₂⁻¹ := by
      have h3 : z₁ * (z₂' * z₂⁻¹) = (z₂' * z₂⁻¹) * z₁ :=
        hz₁c _ ((nbrSpan3 (conjClass3 K) K₁).mul_mem hX
          ((nbrSpan3 (conjClass3 K) K₁).inv_mem h.z₂_mem))
      calc y * (z₁ * z₂) * y⁻¹ * (z₁ * z₂)⁻¹
          = (y * z₁ * y⁻¹) * (y * z₂ * y⁻¹) * z₂⁻¹ * z₁⁻¹ := by group
        _ = z₁ * z₂' * z₂⁻¹ * z₁⁻¹ := by rw [hy1, ← hz₂']
        _ = (z₁ * (z₂' * z₂⁻¹)) * z₁⁻¹ := by group
        _ = ((z₂' * z₂⁻¹) * z₁) * z₁⁻¹ := by rw [h3]
        _ = z₂' * z₂⁻¹ := by group
    rw [e]
    exact hcong

end Loc26

section Final

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem satClass_trans (hz : IsClassicalMember3 K z) {K₁ : Subgroup G} {z₁ : G}
    (hK₁ : K₁ ∈ conjClass3 K) (hz₁ : IsClassicalMember3 K₁ z₁) :
    ∀ M ∈ satClass K z, ∃ g : G, conjSub g (satU (.sl2 3 1) K₁ z₁) = M := by
  intro M hM
  obtain ⟨a, rfl⟩ := CoreAssembly.single_class _ M hM
  obtain ⟨b, hb⟩ := satU_mem_satClass hz hK₁ hz₁
  refine ⟨a * b⁻¹, ?_⟩
  rw [← hb, ← conjSub_mul]
  congr 1
  group

end Final

@[expose] def TypeC3NbhdNotThinFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → LocCommuteAt K z → AEmptyAt K z →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        ¬ nbrSpan3 (conjClass3 K) K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₁)

@[expose] def TypeC3NoThinFree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMember3 K z → CIT3Below (Nat.card G) →
      3 ≤ twoRank G → ¬ TwoSubgroupsFourGenerated G → DeltaConnected K →
      ¬ BootData3 (conjClass3 K) → LocCommuteAt K z → AEmptyAt K z →
      ∀ (K₁ K₂ : Subgroup G) (z₁ z₂ : G), IsEdge3 (conjClass3 K) K₁ K₂ z₁ z₂ →
        z₁ ∈ nbrSpan3 (conjClass3 K) K₁

theorem typeC3NoThinFree_of_notThinFree (h : TypeC3NbhdNotThinFree) : TypeC3NoThinFree := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hC hAE K₁ K₂ z₁ z₂ he
  rcases nbhd_mem_or_thin_free hz hBelow hB hC he with hmem | hthin
  · exact hmem
  · exact absurd hthin (h G hnab K z hz hBelow h3 h4 hΔ hB hC hAE K₁ K₂ z₁ z₂ he)

theorem typeC3NbhdNotThinFree_of_loc26 (h67 : L67Gen) (hcore : Loc26False3) :
    TypeC3NbhdNotThinFree := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hC hAE K₁ K₂ z₁ z₂ he hthin
  have h := thinData_of_thin hz hBelow hB hC he hthin
  have h' := thinData_symm hz hBelow hB hC h
  have hgen := hypOmegaGen_of_loc hnab hz hΔ hB hC
  have hK₁Ω := satU_mem_satClass hz he.mem₁ he.cls₁
  have hK₂Ω := satU_mem_satClass hz he.mem₂ he.cls₂
  have hu₁ := isUniqueInvolution_satU he.cls₁
  have hu₂ := isUniqueInvolution_satU he.cls₂
  obtain ⟨R, hR⟩ := exists_isSylow2In K₁
  obtain ⟨T, hT⟩ := exists_isSylow2In K₂
  have hTc : T ≤ Subgroup.centralizer (R : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.mpr fun r hr => he.comm r (hR.1 hr) t (hT.1 ht)
  have hTR2 : IsPGroup 2 ↥(T ⊔ R) :=
    hT.2.1.to_sup_of_normal_right' hR.2.1 (hTc.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨S, hS⟩ := hTR2.exists_le_sylow
  have hRS : R ≤ (S : Subgroup G) := le_sup_right.trans hS
  have hTS : T ≤ (S : Subgroup G) := le_sup_left.trans hS
  obtain ⟨W, hW, hWS, hWn⟩ := exists_W_of_hypOmegaGen hgen S
  have hRsat : IsSylow2In R (satU (.sl2 3 1) K₁ z₁) := isSylow2In_satU he.cls₁ hR
  have hTsat : IsSylow2In T (satU (.sl2 3 1) K₂ z₂) := isSylow2In_satU he.cls₂ hT
  exact hcore G (satClass K z) (satU (.sl2 3 1) K₁ z₁) (satU (.sl2 3 1) K₂ z₂) S R T W z₁ z₂
    (Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₁))
    (Balance.oddCoreIn (nbrSpan3 (conjClass3 K) K₂)) (hypOmegaModU_of_loc hnab hz hΔ hB hC) hAE
    hK₁Ω (satClass_trans hz he.mem₁ he.cls₁)
    (fun K' hK' => by
      obtain ⟨hK'Ω, w, hw₁, hw'⟩ := hK'
      exact satClass_eq_of_involution_eq hnab hz hΔ hB hC hK'Ω hK₁Ω hw' hw₁)
    hu₁ (satU_mem_omegaNbr hnab hz hΔ hB hC he hT) hu₂
    ⟨mem_RSet_of_isSylow2In hK₁Ω hRsat, hR.1.trans le_satU, hRS⟩
    ⟨mem_RSet_of_isSylow2In hK₂Ω hTsat, hT.1.trans le_satU, hTS⟩ ⟨hW, hWS, hWn⟩
    (loc26_of_thinData h67 hnab hz hΔ hB hC h hR hT hRS hTS)
    (loc26_of_thinData h67 hnab hz hΔ hB hC h' hT hR hTS hRS)

theorem typeC3NbhdNotThin_of_loc26 (h67 : L67Gen) (hcore : Loc26False3) : TypeC3NbhdNotThin := by
  intro G _ _ _ hnab K z hz hBelow h3 h4 hΔ hB hA2 K₁ K₂ z₁ z₂ he
  exact typeC3NbhdNotThinFree_of_loc26 h67 hcore G hnab K z hz hBelow h3 h4 hΔ hB
    (locCommuteAt_of_not_a2Configuration hz hA2) (aEmptyAt_of_not_a2 hnab hz hΔ hB hA2)
    K₁ K₂ z₁ z₂ he

theorem typeC3NoThin_of_loc26 (h67 : L67Gen) (hcore : Loc26False3) : Q3Y.TypeC3NoThin :=
  typeC3NoThin_of_notThin (typeC3NbhdNotThin_of_loc26 h67 hcore)

end CFSG.ClassicalInvolution.Q3.Q3CP
