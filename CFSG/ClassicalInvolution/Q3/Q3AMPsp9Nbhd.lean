module

public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9WC
public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9XSL4
public import CFSG.ClassicalInvolution.Q3.Q3AMPsp9Layer

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3CH
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf finite_perfectResidualOf_isPerfect
  perfectResidualOf_normalizer_contains)
open scoped MatrixGroups commutatorElement

section Nbhd


variable {G : Type} [Group G] [Finite G]

theorem exists_layer9_pkg [IsSimpleGroup G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
    {S : Sylow 2 G} {R T W : Subgroup G} {z t : G} (h : Q3T8.Asc77.BadStd8 Ω K J S R T W z t)
    (hint : IsIntrinsicU (.sl2 3 1) K z) {M : Subgroup G} {a : G} (hM : M ∈ Ω)
    (ha : IsUniqueInvolution M a) (hD : PspNbhdL4 Ω M a) {w t₀ s : G}
    (hw : w ∈ nbrLayer Ω M a) (hww : w * w = a) (ht₀ : t₀ ∈ M) (hs : s = t₀ * w)
    (hsa : s * a = a * s) (hs2 : s * s = 1) :
    ∃ L : Subgroup G, Psp9Layer (nbrLayer Ω M a) s a L := by
  classical
  obtain ⟨ι, hι, D, ha', i₁, hall, hk, f, hf, hfz⟩ := hD
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  have hMc : IsClassicalMember3 M a :=
    Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution hstd.stand.modU hM ha
  have hCM : ∀ g ∈ Subgroup.centralizer ({a} : Set G), conjSub g M = M := fun g hg =>
    mem_normalizer_iff_conjSub_eq.mp
      (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) ha hg)
  have hCY : ∀ g ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ nbrLayer Ω M a,
      g * y * g⁻¹ ∈ nbrLayer Ω M a := fun g hg y hy => conj_mem_nbrLayer hΩ hCM hg hy
  have hex : ∀ N ∈ omegaNbr Ω M, Nat.card ↥(Subgroup.map
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(nbrLayer Ω M a)))
      ((exactCore3 a N).subgroupOf (nbrLayer Ω M a))) = 24 := fun N hN =>
    nbrExact_of_lieSystem D hN
  have hact : ∀ y ∈ nbrLayer Ω M a,
      s * y * s⁻¹ * (w * y * w⁻¹)⁻¹ ∈ oddCoreOf (nbrLayer Ω M a) := by
    intro y hy
    have hwy : w * y * w⁻¹ ∈ nbrLayer Ω M a :=
      (nbrLayer Ω M a).mul_mem ((nbrLayer Ω M a).mul_mem hw hy) ((nbrLayer Ω M a).inv_mem hw)
    have h1 := commutator_mem_oddCoreOf_nbrLayer h hint hM ha hex ht₀ hwy
    have e : s * y * s⁻¹ * (w * y * w⁻¹)⁻¹ = ⁅t₀, w * y * w⁻¹⁆ := by
      rw [hs, commutatorElement_def]
      group
    rwa [e]
  set Y := nbrLayer Ω M a with hY
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  have hne : π ⟨a, ha'⟩ ≠ 1 :=
    Q3Y.mk_ne_one_of_involution Y ha' ha.sq ha.ne_one
  have hfz' : D.hom i₁ f = π ⟨a, ha'⟩ := hfz
  have hfne : D.hom i₁ f ≠ 1 := by
    rw [hfz']
    exact hne
  let wY : ↥Y := ⟨w, hw⟩
  have hwwY : wY * wY = ⟨a, ha'⟩ := Subtype.ext hww
  have hub : π wY * π wY = D.hom i₁ f := by
    rw [← map_mul, hwwY, hfz']
  have hψs : Function.Surjective (D.hom i₁) :=
    MonoidHom.range_eq_top.mp (range_eq_top_of_forall_eq D hall)
  obtain ⟨Lb, hLc, hLn, hubL, hLiso, hM3, hM2, -⟩ :=
    exists_layer_bar_comp9_strong hk (D.hom i₁) hψs (D.ker_le_center i₁) hf hfne hub
  have hcard : Nat.card (GaloisField 3 2) = 9 := by
    rw [GaloisField.card 3 2 (by norm_num)]
    norm_num
  have hodd9 : Odd (Nat.card (GaloisField 3 2)) := by rw [hcard]; decide
  have h39 : 3 ≤ Nat.card (GaloisField 3 2) := by rw [hcard]; norm_num
  obtain ⟨Lw, hLwY, hLws, hzLw, hsub, hiso, hmemLw, hsurLw, hcentLw, hoddLw⟩ :=
    exists_layerGen_of_action (oddCore_sl2_eq_bot hodd9 h39) (nbrLayer_le_centralizer Ω M a) hCY
      ha' hw hww hsa hs2 hact hLc hLn hubL hLiso
  obtain ⟨hsect, hLprod⟩ := isSectionMember_perfectResidualOf_layer (p := 3) (f := 2)
    (by norm_num) (by norm_num) hLws hMc.orderOf_eq_two hzLw hsub hiso
  set P := perfectResidualOf Lw with hP
  have hPLw : P ≤ Lw := Subgroup.map_subtype_le _
  have hPY : P ≤ Y := hPLw.trans hLwY
  have hPperf : Group.IsPerfect ↥P := finite_perfectResidualOf_isPerfect Lw
  have hPc : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.mp hPperf
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  set Cs := Subgroup.centralizer ({s} : Set G) with hCs
  have hYCa : Y ≤ Ca := nbrLayer_le_centralizer Ω M a
  have hCYinv : ∀ g ∈ Ca, ∀ y ∈ Y, g⁻¹ * y * g ∈ Y := fun g hg y hy => by
    simpa using hCY g⁻¹ (Ca.inv_mem hg) y hy
  have hπP : ∀ b ∈ Lb, ∃ (y : G) (hy : y ∈ Y), y ∈ P ∧ π ⟨y, hy⟩ = b := by
    intro b hb
    obtain ⟨y, hy, hyLw, hyb⟩ := hsurLw b hb
    obtain ⟨q, hq, o, ho, hyqo⟩ := hLprod y hyLw
    have hqY : q ∈ Y := hPY hq
    have hoY : o ∈ Y := (oddCoreIn_le Lw).trans hLwY ho
    refine ⟨q, hqY, hq, ?_⟩
    rw [← hyb]
    have e : (⟨y, hy⟩ : ↥Y) = ⟨q, hqY⟩ * ⟨o, hoY⟩ := Subtype.ext hyqo
    rw [e, map_mul, hoddLw o hoY ho, mul_one]
  have hOY : oddCoreIn Y ≤ oddCoreIn Ca := by
    refine le_oddCoreIn_of_normalizes ((oddCoreIn_le Y).trans hYCa) ?_ (odd_card_oddCoreIn Y)
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact conj_mem_oddCoreOf_of_mem_normalizer (hCY g hg) (hCYinv g hg) hx
    · intro hx
      have h1 : ∀ y ∈ Y, g⁻¹ * y * g⁻¹⁻¹ ∈ Y := fun y hy => by
        simpa using hCYinv g hg y hy
      have h2 : ∀ y ∈ Y, g⁻¹⁻¹ * y * g⁻¹ ∈ Y := fun y hy => by
        simpa using hCY g hg y hy
      have h3 := conj_mem_oddCoreOf_of_mem_normalizer h1 h2 hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rw [e] at h3
      exact h3
  refine ⟨P, ⟨hPY, hsect, ?_, ?_, ?_⟩⟩
  ·
    intro g hgz hgs
    set Pg := conjSub g P with hPg
    have hPgY : Pg ≤ Y := fun y hy => by
      have h1 : g⁻¹ * y * g ∈ P := mem_conjSub_iff.mp hy
      have := hCY g hgz _ (hPY h1)
      simpa [mul_assoc] using this
    have hPgs : Pg ≤ Cs := fun y hy => by
      have h1 : g⁻¹ * y * g ∈ P := mem_conjSub_iff.mp hy
      have h2 : g⁻¹ * y * g ∈ Cs := hLws (hPLw h1)
      have := Cs.mul_mem (Cs.mul_mem hgs h2) (Cs.inv_mem hgs)
      simpa [mul_assoc] using this
    have hPgperf : Group.IsPerfect ↥Pg := isPerfect_conjSub hPperf g
    have hPgc : ⁅Pg, Pg⁆ = Pg := Subgroup.isPerfect_iff.mp hPgperf
    have hPgLw : Pg ≤ Lw := by
      set Q : Subgroup (↥Y ⧸ classicalInvolutionOddCore ↥Y) := (Pg.subgroupOf Y).map π with hQ
      have hsubperf : ⁅Pg.subgroupOf Y, Pg.subgroupOf Y⁆ = Pg.subgroupOf Y := by
        apply Subgroup.map_injective Y.subtype_injective
        rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPgY, hPgc]
      have hQperf : ⁅Q, Q⁆ = Q := by
        rw [hQ, ← Subgroup.map_commutator, hsubperf]
      have hQc : Q ≤ Subgroup.centralizer ({π wY} : Set (↥Y ⧸ classicalInvolutionOddCore ↥Y)) := by
        rintro _ ⟨⟨y, hyY⟩, hy, rfl⟩
        exact hcentLw y hyY (hPgs hy)
      have hQLb : Q ≤ Lb := hM3 Q hQc hQperf
      intro y hy
      have hyY := hPgY hy
      exact (hmemLw y hyY).mpr ⟨hPgs hy, hQLb ⟨⟨y, hyY⟩, hy, rfl⟩⟩
    have hPgP : Pg ≤ P := le_perfectResidualOf_of_perfect hPgLw hPgperf
    have hcard : Nat.card ↥Pg = Nat.card ↥P :=
      Subgroup.card_map_of_injective (MulAut.conj g).injective
    exact Subgroup.eq_of_le_of_card_ge hPgP hcard.ge
  ·
    intro x hx
    obtain ⟨hxP, hxO⟩ := hx
    have hxY : x ∈ Y := hPY hxP
    have hx1 : x ∈ oddCoreIn P := by
      refine le_oddCoreIn_of_normalizes (S := P ⊓ oddCoreIn Cs) (X := P) inf_le_left ?_
        ((odd_card_oddCoreIn Cs).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_right)) ⟨hxP, hxO⟩
      intro p hp
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have hpC : p ∈ Cs := hLws (hPLw hp)
      constructor
      · rintro ⟨hy1, hy2⟩
        exact ⟨P.mul_mem (P.mul_mem hp hy1) (P.inv_mem hp), conj_mem_oddCoreIn hpC hy2⟩
      · rintro ⟨hy1, hy2⟩
        have e : y = p⁻¹ * (p * y * p⁻¹) * p := by group
        have h3 := conj_mem_oddCoreIn (Cs.inv_mem hpC) hy2
        rw [inv_inv] at h3
        refine ⟨?_, ?_⟩
        · rw [e]
          exact P.mul_mem (P.mul_mem (P.inv_mem hp) hy1) hp
        · rw [e]
          exact h3
    have hPsub : IsSubnormal P Lw := by
      refine isSubnormal_of_normal_subgroupOf hPLw ?_
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPLw]
      intro y hy
      exact perfectResidualOf_normalizer_contains Lw (Subgroup.le_normalizer hy)
    have hx2 : x ∈ oddCoreIn Lw := oddCoreIn_le_of_isSubnormal hPsub hx1
    have hxπ : π ⟨x, hxY⟩ = 1 := hoddLw x hxY hx2
    have hmem : x ∈ oddCoreIn Y := ⟨⟨x, hxY⟩, (QuotientGroup.eq_one_iff _).mp hxπ, rfl⟩
    exact hOY hmem
  ·
    intro x hxY hxs hx2 hcomm
    have h1 : π ⟨x, hxY⟩ * π ⟨x, hxY⟩ = 1 := by
      rw [← map_mul]
      have : (⟨x, hxY⟩ * ⟨x, hxY⟩ : ↥Y) = 1 := Subtype.ext hx2
      rw [this, map_one]
    have h2 : π ⟨x, hxY⟩ * π wY = π wY * π ⟨x, hxY⟩ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcentLw x hxY hxs)
    have h3 : ∀ y ∈ Lb, π ⟨x, hxY⟩ * y = y * π ⟨x, hxY⟩ := by
      intro b hb
      obtain ⟨q, hqY, hqP, rfl⟩ := hπP b hb
      obtain ⟨o, ho, hoe⟩ := hcomm q hqP
      have e : (⟨x, hxY⟩ : ↥Y)⁻¹ * ⟨q, hqY⟩⁻¹ * ⟨x, hxY⟩ * ⟨q, hqY⟩ = o := Subtype.ext hoe.symm
      have h4 : π ((⟨x, hxY⟩ : ↥Y)⁻¹ * ⟨q, hqY⟩⁻¹ * ⟨x, hxY⟩ * ⟨q, hqY⟩) = 1 := by
        rw [e]
        exact (QuotientGroup.eq_one_iff _).mpr ho
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h4
      calc π ⟨x, hxY⟩ * π ⟨q, hqY⟩
          = π ⟨q, hqY⟩ * π ⟨x, hxY⟩ * ((π ⟨x, hxY⟩)⁻¹ * (π ⟨q, hqY⟩)⁻¹ * π ⟨x, hxY⟩ *
              π ⟨q, hqY⟩) := by group
        _ = π ⟨q, hqY⟩ * π ⟨x, hxY⟩ := by rw [h4, mul_one]
    rcases hM2 _ h1 h2 h3 with h5 | h5
    · left
      have hmem : x ∈ oddCoreIn Y := ⟨⟨x, hxY⟩, (QuotientGroup.eq_one_iff _).mp h5, rfl⟩
      have h6 := Subgroup.orderOf_dvd_natCard (oddCoreIn Y) hmem
      have h7 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
      have hodd1 : Odd (orderOf x) := (odd_card_oddCoreIn Y).of_dvd_nat h6
      rcases (Nat.dvd_prime Nat.prime_two).mp h7 with h8 | h8
      · exact orderOf_eq_one_iff.mp h8
      · rw [h8] at hodd1
        exact absurd hodd1 (by decide)
    · right
      have haa : (⟨a, ha'⟩ : ↥Y) * ⟨a, ha'⟩ = 1 := Subtype.ext ha.sq
      have h6 : π ⟨x * a, Y.mul_mem hxY ha'⟩ = 1 := by
        have e : (⟨x * a, Y.mul_mem hxY ha'⟩ : ↥Y) = ⟨x, hxY⟩ * ⟨a, ha'⟩ := rfl
        rw [e, map_mul, h5, hub, hfz', ← map_mul, haa, map_one]
      exact ⟨⟨x * a, Y.mul_mem hxY ha'⟩, (QuotientGroup.eq_one_iff _).mp h6, rfl⟩

end Nbhd

end CFSG.ClassicalInvolution.Q3.Q3AM
