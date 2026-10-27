module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm1RTwinDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDich
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.FStarBar
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.HasLiftTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.CentQuotAEmpty
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace TwinRed

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {N : Subgroup Y} [N.Normal]

omit [N.Normal] in
theorem inf_eq_bot (hd : Q8TwinDatum R S t) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) : R ⊓ N = ⊥ := by
  by_contra h
  exact htN (Subgroup.mem_inf.mp (Inner.mem_of_ne_bot hd inf_le_left (hN2.to_le inf_le_right) h)).2

omit [N.Normal] in
theorem core_inf_eq_bot (hd : Q8TwinDatum R S t) (hN2 : IsPGroup 2 ↥N) (htN : t ∉ N) :
    tightCore R ⊓ N = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf_right N (tightCore_le R)).trans (inf_eq_bot hd hN2 htN).le)

omit [Finite Y] in
theorem inf_conj_eq_bot (h0 : tightCore R ⊓ N = ⊥)
    {K : Subgroup Y} (hK : K ∈ CoreAssembly.conjClass (tightCore R)) : N ⊓ K = ⊥ := by
  obtain ⟨g, rfl⟩ := hK
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxN, hxK⟩ := Subgroup.mem_inf.mp hx
  rw [mem_conjSub_iff] at hxK
  have hxN' : g⁻¹ * x * g ∈ N := by
    have h3 := (inferInstance : N.Normal).conj_mem _ hxN g⁻¹
    rwa [inv_inv] at h3
  have h1 : g⁻¹ * x * g ∈ tightCore R ⊓ N := ⟨hxK, hxN'⟩
  rw [h0, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h1]; group

omit [Finite Y] [N.Normal] in
theorem odd_of_inf_eq_bot {K : Subgroup Y} (h : N ⊓ K = ⊥) : Odd (Nat.card ↥(N ⊓ K)) := by
  rw [h, Subgroup.card_bot]
  exact odd_one

theorem q8TwinDatum_map (hd : Q8TwinDatum R S t) (hRN : R ⊓ N = ⊥) (htN : t ∉ N) :
    Q8TwinDatum (R.map (QuotientGroup.mk' N)) (TwistQ.sylowMap N S) (QuotientGroup.mk' N t) := by
  have hcent : R.map (QuotientGroup.mk' N) ≤
      Subgroup.centralizer ({QuotientGroup.mk' N t} : Set (Y ⧸ N)) := by
    rintro _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hd.cent hr)]
  refine ⟨?_, ?_, ?_, hcent, ?_⟩
  · obtain ⟨r, hr, ⟨e⟩⟩ := hd.quat
    exact ⟨r, hr, ⟨(TwistQ.sylowMapEquiv hRN S).symm.trans e⟩⟩
  · rw [TwistQ.sylowMap_map_subtype]
    exact Subgroup.mem_map_of_mem _ hd.mem
  · refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, ← hd.order, pow_orderOf_eq_one, map_one]
    · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact htN
  · have he := CFSG.ABGLocalTools.oddCore_map_mulEquiv (TwistQ.mapEquiv (N := N) hRN)
    exact hd.twoGroup.of_equiv (QuotientGroup.congr _ _ (TwistQ.mapEquiv hRN) he)

theorem q8_map (hRN : R ⊓ N = ⊥)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) :
    Nonempty (↥((TwistQ.sylowMap N S : Sylow 2 _) : Subgroup ↥(R.map (QuotientGroup.mk' N))) ≃*
      QuaternionGroup 2) :=
  ⟨(TwistQ.sylowMapEquiv hRN S).symm.trans hq8.some⟩

omit [Finite Y] in
theorem selfGen_map (hRN : R ⊓ N = ⊥) (hgen : TightSelfGen R) :
    TightSelfGen (R.map (QuotientGroup.mk' N)) := by
  have hgen' : (⨆ g : Y, conjSub g (tightCore R)) = ⊤ := hgen
  show (⨆ g : Y ⧸ N, conjSub g (tightCore (R.map (QuotientGroup.mk' N)))) = ⊤
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), ← hgen',
    Subgroup.map_iSup]
  refine iSup_le fun g => ?_
  rw [TwistQ.conjSub_map, TwistQ.tightCore_map hRN]
  exact le_iSup (fun g : Y ⧸ N => conjSub g (tightCore (R.map (QuotientGroup.mk' N))))
    (QuotientGroup.mk' N g)

theorem hyp_map (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hNc : N ≤ Subgroup.center Y) (hRN : R ⊓ N = ⊥) (h0 : tightCore R ⊓ N = ⊥) :
    HypOmegaGen (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N)))) := by
  rw [← TwistQ.tightCore_map hRN, ← image_conjClass (N := N)]
  exact CentQ.quotient_hypOmegaGen hΩ N hNc fun K hK => odd_of_inf_eq_bot (inf_conj_eq_bot h0 hK)

theorem eq_of_map {Ω : Set (Subgroup Y)} (hΩ : HypOmegaGen Ω) (hNc : N ≤ Subgroup.center Y)
    (hXK : ∀ K ∈ Ω, Odd (Nat.card ↥(N ⊓ K))) {K J : Subgroup Y} (hK : K ∈ Ω) (hJ : J ∈ Ω)
    (h : K.map (QuotientGroup.mk' N) = J.map (QuotientGroup.mk' N)) : K = J := by
  by_contra hne
  have h62 : L6_2On Ω := Sec6Gen.l6_2Gen Y Ω hΩ
  have h4 := (CentQ.omega4_quot_gen hΩ h62 N hNc hXK hK hJ hne).1
  obtain ⟨-, P, hP, -⟩ := hΩ.omega1 K hK
  have h8 : 8 ≤ Nat.card ↥P := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hP)
  have hPN : P ⊓ N = ⊥ := AscQuot.inf_eq_bot_of_isPGroup_of_odd N hP.2.1 hP.1 (hXK K hK)
  obtain ⟨m, hm⟩ := hP.2.1.exists_card_eq
  have hcardP : Nat.card ↥(P.map (QuotientGroup.mk' N)) = Nat.card ↥P :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv hPN).toEquiv).symm
  have hle : P.map (QuotientGroup.mk' N) ≤
      K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N) :=
    le_inf (Subgroup.map_mono hP.1) (h ▸ Subgroup.map_mono hP.1)
  have hdvd : 2 ^ m ∣ Nat.card ↥(K.map (QuotientGroup.mk' N) ⊓ J.map (QuotientGroup.mk' N)) := by
    rw [← hm, ← hcardP]
    exact Subgroup.card_dvd_of_le hle
  have h5 := (padicValNat_dvd_iff_le (p := 2) Nat.card_pos.ne').mp hdvd
  have : 3 ≤ m := by
    by_contra hlt
    push Not at hlt
    interval_cases m <;> omega
  omega

theorem centQuotGen (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hNc : N ≤ Subgroup.center Y) (hRN : R ⊓ N = ⊥) (h0 : tightCore R ⊓ N = ⊥) :
    CentQuotGen (CoreAssembly.conjClass (tightCore R)) N where
  hyp := hΩ
  hyp' := by
    have h : quotFamily (CoreAssembly.conjClass (tightCore R)) N =
        CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' N)) :=
      image_conjClass (N := N) (tightCore R)
    rw [h, TwistQ.tightCore_map hRN]
    exact hyp_map hΩ hNc hRN h0
  meet J hJ := by
    rw [inf_comm]
    exact inf_conj_eq_bot h0 hJ
  eq_of_map K hK J hJ h :=
    eq_of_map hΩ hNc (fun K hK => odd_of_inf_eq_bot (inf_conj_eq_bot h0 hK)) hK hJ h
  normalizer_of_map := by
    rintro K hK u hu
    rw [mem_normalizer_iff_conjSub_eq] at hu ⊢
    have hK' : conjSub u K ∈ CoreAssembly.conjClass (tightCore R) := by
      obtain ⟨g, rfl⟩ := hK
      exact ⟨u * g, conjSub_mul u g _⟩
    refine eq_of_map hΩ hNc (fun K hK => odd_of_inf_eq_bot (inf_conj_eq_bot h0 hK)) hK' hK ?_
    rw [TwistQ.conjSub_map, hu]

theorem aEmpty_map (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hA : AEmpty (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (hNc : N ≤ Subgroup.center Y) (hRN : R ⊓ N = ⊥) (h0 : tightCore R ⊓ N = ⊥) :
    AEmpty (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
      (tightCore (R.map (QuotientGroup.mk' N))) := by
  have h : quotFamily (CoreAssembly.conjClass (tightCore R)) N =
      CoreAssembly.conjClass ((tightCore R).map (QuotientGroup.mk' N)) :=
    image_conjClass (N := N) (tightCore R)
  have hall := aEmpty_forall_of_transitive hΩ.conjInvariant (fun _ ⟨g, hg⟩ => ⟨g, hg⟩) hA
  have := (centQuotGen hΩ hNc hRN h0).aEmpty_quotFamily hall
    ((tightCore R).map (QuotientGroup.mk' N))
    (map_mem_quotFamily (CoreAssembly.mem_conjClass_self _))
  rw [h] at this
  rw [← TwistQ.tightCore_map hRN]
  exact this

theorem twin_map (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hNc : N ≤ Subgroup.center Y) (hRN : R ⊓ N = ⊥) (h0 : tightCore R ⊓ N = ⊥)
    (htw : ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      K' ≠ tightCore R) :
    ∃ K' ∈ twinSet (CoreAssembly.conjClass (tightCore (R.map (QuotientGroup.mk' N))))
      (tightCore (R.map (QuotientGroup.mk' N))), K' ≠ tightCore (R.map (QuotientGroup.mk' N)) := by
  obtain ⟨K', hK', hne⟩ := htw
  have hodd := fun K (hK : K ∈ CoreAssembly.conjClass (tightCore R)) =>
    odd_of_inf_eq_bot (inf_conj_eq_bot h0 hK)
  refine ⟨K'.map (QuotientGroup.mk' N), ?_, ?_⟩
  · obtain ⟨hKΩ, z, hz, hz'⟩ := hK'
    refine ⟨?_, QuotientGroup.mk' N z, ?_, ?_⟩
    · exact TwistQ.map_mem_conjClass hRN hKΩ
    · rw [← TwistQ.tightCore_map hRN]
      exact isUniqueInvolution_map_mk_of_odd (hodd _ (CoreAssembly.mem_conjClass_self _)) hz
    · exact isUniqueInvolution_map_mk_of_odd (hodd _ hKΩ) hz'
  · rw [← TwistQ.tightCore_map hRN]
    intro h
    exact hne (eq_of_map hΩ hNc hodd hK'.1 (CoreAssembly.mem_conjClass_self _) h)

theorem le_center_of_normal_two (hd : Q8TwinDatum R S t) (hgen : TightSelfGen R)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) {X : Subgroup Y} (hXn : X.Normal)
    (hX2 : IsPGroup 2 ↥X) (htX : t ∉ X) : X ≤ Subgroup.center Y := by
  have htop : Subgroup.centralizer (X : Set Y) = ⊤ :=
    eq_top_of_conj hd hgen fun y x hx => by
      rw [mem_conjSub_iff] at hx
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hp' : y⁻¹ * p * y ∈ X := by simpa using hXn.conj_mem p hp y⁻¹
      have := Inner.commute_of_normal_two hd hΩ hXn hX2 htX hx hp'
      calc p * x = y * ((y⁻¹ * p * y) * (y⁻¹ * x * y)) * y⁻¹ := by group
        _ = y * ((y⁻¹ * x * y) * (y⁻¹ * p * y)) * y⁻¹ := by rw [← this]
        _ = x * p := by group
  intro p hp
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (X : Set Y) := htop ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hg p hp).symm

omit [Finite Y] in
theorem fstar_simple_of_fitting_eq_bot [Finite Y] (hQ : TightFStarQuasisimple Y)
    (hF : genFittingFitting Y = ⊥) :
    IsSimpleGroup ↥(genFittingFStar Y) ∧ ∃ a b : ↥(genFittingFStar Y), a * b ≠ b * a := by
  obtain ⟨hperf, hsimple⟩ := hQ
  have hZ : Subgroup.center ↥(genFittingFStar Y) = ⊥ := by
    have h1 := center_map_le_fitting (genFittingFStar_normal Y)
    rw [hF, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (genFittingFStar Y).subtype_injective).mp h1
  have e : ↥(genFittingFStar Y) ⧸ Subgroup.center ↥(genFittingFStar Y) ≃* ↥(genFittingFStar Y) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hs : IsSimpleGroup ↥(genFittingFStar Y) := by
    have := hsimple
    exact e.symm.isSimpleGroup
  refine ⟨hs, ?_⟩
  have := hs
  exact TA3.exists_ne_comm_of_commutator_eq_top hperf

theorem odd1 {G : Type} [Group G] [Finite G] (K Z : Subgroup G) [K.Normal]
    (hZc : Z ≤ Subgroup.center G) (hZ2 : IsPGroup 2 ↥Z) (hKZ : K ⊓ Z = ⊥) {d : ℕ}
    (hd : Odd d) (hcard : Nat.card G = Nat.card K * Nat.card Z * d) :
    (Subgroup.closure {x : G | Odd (orderOf x)} ⊔ K) ⊓ Z = ⊥ := by
  classical
  set ν := QuotientGroup.mk' K with hν
  set Z' : Subgroup (G ⧸ K) := Z.map ν with hZ'
  have hZ'c : Z' ≤ Subgroup.center (G ⧸ K) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro e
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective K e
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (hZc hz) g).symm]
  have : Z'.Normal := Subgroup.normal_of_le_center hZ'c
  have hZK : Z ⊓ K = ⊥ := by rw [inf_comm]; exact hKZ
  have hcardZ' : Nat.card Z' = Nat.card Z :=
    (Nat.card_congr (AscQuot.quotRestrictEquiv hZK).toEquiv).symm
  have hpos : 0 < Nat.card Z := Nat.card_pos
  have hEcard : Nat.card (G ⧸ K) = Nat.card Z * d := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    have hKpos : 0 < Nat.card K := Nat.card_pos
    rw [hcard] at h1
    have : Nat.card K * (Nat.card Z * d) = Nat.card K * Nat.card (G ⧸ K) := by
      calc Nat.card K * (Nat.card Z * d) = Nat.card K * Nat.card Z * d := by ring
        _ = Nat.card (G ⧸ K) * Nat.card K := h1
        _ = Nat.card K * Nat.card (G ⧸ K) := by ring
    exact (Nat.eq_of_mul_eq_mul_left hKpos this).symm
  have hidx : Z'.index = d := by
    have h1 := Subgroup.card_mul_index Z'
    rw [hcardZ', hEcard] at h1
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hcop : (Nat.card Z').Coprime Z'.index := by
    obtain ⟨a, ha⟩ := hZ2.exists_card_eq
    rw [hcardZ', ha, hidx]
    exact (Nat.coprime_two_left.mpr hd).pow_left a
  obtain ⟨C, hC⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hdisj : Disjoint Z' C := hC.disjoint
  have hsup : Z' ⊔ C = ⊤ := hC.sup_eq_top
  have hoddC : ∀ x : G, Odd (orderOf x) → ν x ∈ C := by
    intro x hx
    have hx' : ν x ∈ Z' ⊔ C := hsup ▸ Subgroup.mem_top _
    obtain ⟨z, hz, c, hc, hzc⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
    have hzcentral : ∀ e : G ⧸ K, e * z = z * e := Subgroup.mem_center_iff.mp (hZ'c hz)
    have hpow : (ν x) ^ orderOf x = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [← hzc, (show Commute z c from (hzcentral c).symm).mul_pow] at hpow
    have h1 : z ^ orderOf x = (c ^ orderOf x)⁻¹ := eq_inv_of_mul_eq_one_left hpow
    have h2 : z ^ orderOf x ∈ Z' ⊓ C :=
      ⟨Z'.pow_mem hz _, by rw [h1]; exact C.inv_mem (C.pow_mem hc _)⟩
    rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at h2
    have hz1 : z = 1 := eq_one_of_pow_odd hx (hZ2.map ν |>.to_le
      (Subgroup.zpowers_le.mpr hz)) h2
    rw [← hzc, hz1, one_mul]
    exact hc
  have hM : Subgroup.closure {x : G | Odd (orderOf x)} ≤ C.comap ν :=
    (Subgroup.closure_le _).mpr fun x hx => hoddC x hx
  have hKle : K ≤ C.comap ν := fun k hk => by
    have h : ν k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    show ν k ∈ C
    rw [h]
    exact C.one_mem
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨hnMK, hnZ⟩ := hn
  have h1 : ν n ∈ C := (sup_le hM hKle) hnMK
  have h2 : ν n ∈ Z' := Subgroup.mem_map_of_mem _ hnZ
  have h3 : ν n ∈ Z' ⊓ C := ⟨h2, h1⟩
  rw [disjoint_iff.mp hdisj, Subgroup.mem_bot] at h3
  have h4 : n ∈ K := (QuotientGroup.eq_one_iff n).mp h3
  have h5 : n ∈ K ⊓ Z := ⟨h4, hnZ⟩
  rwa [hKZ] at h5

theorem two_elt_mem_of_subnormal {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (h : IsSubnormal H K)
    (hv : (Nat.card ↥H).factorization 2 = (Nat.card ↥K).factorization 2) :
    ∀ x ∈ K, IsPGroup 2 ↥(Subgroup.zpowers x) → x ∈ H := by
  induction h with
  | refl => exact fun x hx _ => hx
  | @step H M K hHM hn hMK ih =>
    intro x hxK hx2
    have hHMd : Nat.card ↥H ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hHM
    have hMKd : Nat.card ↥M ∣ Nat.card ↥K := Subgroup.card_dvd_of_le (isSubnormal_le hMK)
    have hle1 : (Nat.card ↥H).factorization 2 ≤ (Nat.card ↥M).factorization 2 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hHMd 2
    have hle2 : (Nat.card ↥M).factorization 2 ≤ (Nat.card ↥K).factorization 2 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hMKd 2
    have hvM : (Nat.card ↥M).factorization 2 = (Nat.card ↥K).factorization 2 := by omega
    have hxM : x ∈ M := ih hvM x hxK hx2
    have hvH : (Nat.card ↥H).factorization 2 = (Nat.card ↥M).factorization 2 := by omega
    set H' : Subgroup ↥M := H.subgroupOf M with hH'
    have hcardH' : Nat.card ↥H' = Nat.card ↥H := by
      rw [hH']
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv
    have hcardM : Nat.card ↥M = Nat.card (↥M ⧸ H') * Nat.card ↥H' :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup H'
    have hodd : ¬ 2 ∣ Nat.card (↥M ⧸ H') := by
      intro h2
      have h3 : (Nat.card ↥M).factorization 2 =
          (Nat.card (↥M ⧸ H')).factorization 2 + (Nat.card ↥H').factorization 2 := by
        rw [hcardM, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
        rfl
      have h4 : 0 < (Nat.card (↥M ⧸ H')).factorization 2 :=
        (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne' h2)
      rw [hcardH', ← hvH] at h3
      omega
    set x' : ↥M := ⟨x, hxM⟩ with hx'
    obtain ⟨a, ha⟩ := hx2.exists_card_eq
    rw [Nat.card_zpowers] at ha
    have h5 : orderOf (QuotientGroup.mk x' : ↥M ⧸ H') ∣ 2 ^ a := by
      rw [← ha]
      have : orderOf x' = orderOf x := (Subgroup.orderOf_coe x').symm
      rw [← this]
      exact orderOf_dvd_of_pow_eq_one (by
        rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]; rfl)
    have h6 : orderOf (QuotientGroup.mk x' : ↥M ⧸ H') ∣ Nat.card (↥M ⧸ H') := orderOf_dvd_natCard _
    have hcop : Nat.Coprime (2 ^ a) (Nat.card (↥M ⧸ H')) :=
      (Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd))
    have h7 : orderOf (QuotientGroup.mk x' : ↥M ⧸ H') = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop h5 h6
    have h8 : (QuotientGroup.mk x' : ↥M ⧸ H') = 1 := orderOf_eq_one_iff.mp h7
    have h9 : x' ∈ H' := (QuotientGroup.eq_one_iff x').mp h8
    exact Subgroup.mem_subgroupOf.mp h9

theorem conjSub_eq_of_subnormal_odd {G : Type} [Group G] [Finite G] {H M C : Subgroup G}
    (hHC : IsSubnormal H C) (hHM : H ≤ M) (hMC : M ≤ C)
    (hv : (Nat.card ↥H).factorization 2 = (Nat.card ↥M).factorization 2)
    (hgen : H ≤ Subgroup.closure {x : G | x ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers x)}) :
    ∀ m ∈ M, conjSub m H = H := by
  have hHM' : IsSubnormal H M := by
    have := isSubnormal_inf hHC M
    rwa [inf_eq_left.mpr hHM, inf_eq_right.mpr hMC] at this
  have h2 := two_elt_mem_of_subnormal hHM' hv
  have hHeq : H = Subgroup.closure {x : G | x ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers x)} :=
    le_antisymm hgen ((Subgroup.closure_le _).mpr fun x hx => h2 x hx.1 hx.2)
  have hnorm : ∀ m ∈ M, ∀ y ∈ H, m * y * m⁻¹ ∈ H := by
    intro m hm y hy
    have hle : Subgroup.closure {x : G | x ∈ M ∧ IsPGroup 2 ↥(Subgroup.zpowers x)} ≤
        H.comap (MulAut.conj m).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr fun x hx => ?_
      show (MulAut.conj m) x ∈ H
      rw [MulAut.conj_apply]
      refine h2 _ ?_ ?_
      · exact M.mul_mem (M.mul_mem hm hx.1) (M.inv_mem hm)
      · have : Subgroup.zpowers (m * x * m⁻¹) = (Subgroup.zpowers x).map (MulAut.conj m).toMonoidHom := by
          rw [MonoidHom.map_zpowers]
          rfl
        rw [this]
        exact hx.2.map _
    have := hle (hHeq ▸ hy)
    exact this
  intro m hm
  ext x
  rw [mem_conjSub_iff]
  constructor
  · intro hx
    have := hnorm m hm _ hx
    rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at this
  · intro hx
    have := hnorm m⁻¹ (M.inv_mem hm) _ hx
    rwa [inv_inv] at this

omit [Finite Y] [N.Normal] in
theorem le_closure_two_of_mem_conjClass {K : Subgroup Y}
    (hK : K ∈ CoreAssembly.conjClass (tightCore R)) :
    K ≤ Subgroup.closure {x : Y | x ∈ K ∧ IsPGroup 2 ↥(Subgroup.zpowers x)} := by
  obtain ⟨g, rfl⟩ := hK
  have e : conjSub g (tightCore R) = Subgroup.closure ((MulAut.conj g).toMonoidHom ''
      {x : Y | x ∈ R ∧ IsPGroup 2 ↥(Subgroup.zpowers x)}) := by
    unfold conjSub tightCore
    exact MonoidHom.map_closure _ _
  refine e.le.trans (Subgroup.closure_le _ |>.mpr ?_)
  rintro _ ⟨x, ⟨hxR, hx2⟩, rfl⟩
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom (Subgroup.subset_closure
      (show x ∈ {x : Y | x ∈ R ∧ IsPGroup 2 ↥(Subgroup.zpowers x)} from ⟨hxR, hx2⟩))
  · rw [← MonoidHom.map_zpowers]
    exact hx2.map _

theorem factorization_classical {Z : Type} [Group Z] [Finite Z] {M : Subgroup Z} {z : Z}
    (h : IsClassicalMember3 M z) : (Nat.card ↥M).factorization 2 = 3 := by
  obtain ⟨e⟩ := h.nonempty_equiv
  have h1 : Nat.card ↥M = Nat.card (↥M ⧸ classicalInvolutionOddCore ↥M) *
      Nat.card (classicalInvolutionOddCore ↥M) := Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥M)) :=
    CFSG.ComponentClassification.OddCore.odd_card ↥M
  rw [Nat.card_congr e.toEquiv, natCard_sl2Three] at h1
  have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  rw [h1, Nat.factorization_mul (by norm_num) hodd.pos.ne', h24,
    Nat.factorization_mul (by norm_num) (by norm_num), Nat.Prime.factorization_pow Nat.prime_two]
  have h3 : (3 : ℕ).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have h4 : (Nat.card (classicalInvolutionOddCore ↥M)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by
      intro hd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd))
  simp [h3, h4]

theorem three_le_factorization {Z : Type} [Group Z] [Finite Z] {Ω : Set (Subgroup Z)}
    (hΩ : HypOmegaGen Ω) {K : Subgroup Z} (hK : K ∈ Ω) :
    3 ≤ (Nat.card ↥K).factorization 2 := by
  obtain ⟨-, P, hP, -⟩ := hΩ.omega1 K hK
  have h8 : 8 ≤ Nat.card ↥P := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hP)
  obtain ⟨a, ha⟩ := hP.2.1.exists_card_eq
  have hdvd : 2 ^ a ∣ Nat.card ↥K := ha ▸ Subgroup.card_dvd_of_le hP.1
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  have : 3 ≤ a := by
    by_contra hlt
    push Not at hlt
    rw [ha] at h8
    interval_cases a <;> omega
  omega

theorem conjSub_eq_of_classical {Z : Type} [Group Z] [Finite Z] {Ω : Set (Subgroup Z)}
    (hΩ : HypOmegaGen Ω) {K : Subgroup Z} (hK : K ∈ Ω) {z : Z} (hz : IsUniqueInvolution K z)
    {M : Subgroup Z} (hM : IsClassicalMember3 M z) (hKM : K ≤ M)
    (hgen : K ≤ Subgroup.closure {x : Z | x ∈ K ∧ IsPGroup 2 ↥(Subgroup.zpowers x)}) :
    ∀ m ∈ M, conjSub m K = K := by
  have h3 := three_le_factorization hΩ hK
  have hM3 := factorization_classical hM
  have hle : (Nat.card ↥K).factorization 2 ≤ (Nat.card ↥M).factorization 2 :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
      (Subgroup.card_dvd_of_le hKM) 2
  refine conjSub_eq_of_subnormal_odd (CentQ.isSubnormal_centralizer_gen hΩ hK hz) hKM
    (isSubnormal_le hM.subnormal) (by omega) ?_
  exact hgen.trans (Subgroup.closure_mono fun x hx => ⟨hKM hx.1, hx.2⟩)

omit [Finite Y] [N.Normal] in
theorem isSubnormal_comap' {Y Z : Type} [Group Y] [Group Z] (f : Z →* Y) {A B : Subgroup Y}
    (h : IsSubnormal A B) : IsSubnormal (A.comap f) (B.comap f) :=
  h.comap f

omit [Finite Y] [N.Normal] in
theorem conjSub_closure_odd {P : Subgroup Y} {g : Y} (hg : g ∈ P) :
    conjSub g (Subgroup.closure {x : Y | x ∈ P ∧ Odd (orderOf x)}) =
      Subgroup.closure {x : Y | x ∈ P ∧ Odd (orderOf x)} := by
  have key : ∀ g ∈ P, conjSub g (Subgroup.closure {x : Y | x ∈ P ∧ Odd (orderOf x)}) ≤
      Subgroup.closure {x : Y | x ∈ P ∧ Odd (orderOf x)} := by
    intro g hg
    unfold conjSub
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, ⟨hxP, hxo⟩, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · exact P.mul_mem (P.mul_mem hg hxP) (P.inv_mem hg)
    · show Odd (orderOf ((MulAut.conj g) x))
      rw [MulAut.conj_apply, orderOf_conj_eq]
      exact hxo
  refine le_antisymm (key g hg) ?_
  have h2 := conjSub_mono (n := g) (key g⁻¹ (P.inv_mem hg))
  rwa [conjSub_conjSub_inv] at h2

theorem lift_member (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N) (hRN : R ⊓ N = ⊥)
    (h0 : tightCore R ⊓ N = ⊥) (ht2 : orderOf t = 2) {K₁ : Subgroup Y}
    (hK₁ : K₁ ∈ CoreAssembly.conjClass (tightCore R)) (hz : IsUniqueInvolution K₁ t)
    {Mb : Subgroup (Y ⧸ N)} (hMb : IsClassicalMember3 Mb (QuotientGroup.mk' N t))
    (hKM : K₁.map (QuotientGroup.mk' N) ≤ Mb) :
    ∃ M : Subgroup Y, M = Subgroup.closure {x : Y | x ∈ Mb.comap (QuotientGroup.mk' N) ∧
        Odd (orderOf x)} ∧ M.map (QuotientGroup.mk' N) = Mb ∧ K₁ ≤ M ∧
      M ≤ Subgroup.centralizer ({t} : Set Y) ∧ IsClassicalMember3 M t := by
  classical
  set π := QuotientGroup.mk' N with hπ
  set Mt : Subgroup Y := Mb.comap π with hMt
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  set M : Subgroup Y := Subgroup.closure {x : Y | x ∈ Mt ∧ Odd (orderOf x)} with hM
  have hodd : ∀ K ∈ CoreAssembly.conjClass (tightCore R), Odd (Nat.card ↥(N ⊓ K)) :=
    fun K hK => odd_of_inf_eq_bot (inf_conj_eq_bot h0 hK)
  have hΩb := hyp_map hΩ hNc hRN h0
  have hK₁b : K₁.map π ∈ CoreAssembly.conjClass (tightCore (R.map π)) :=
    TwistQ.map_mem_conjClass hRN hK₁
  have hzb : IsUniqueInvolution (K₁.map π) (π t) :=
    isUniqueInvolution_map_mk_of_odd (hodd K₁ hK₁) hz
  have hK₁N : N ⊓ K₁ = ⊥ := inf_conj_eq_bot h0 hK₁
  have hK₁N' : K₁ ⊓ N = ⊥ := by rw [inf_comm]; exact hK₁N
  have hNC : N ≤ C := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp (hNc hn) t).symm
  have hMbC : Mb ≤ C.map π := le_map_centralizer_of_isClassicalMember3 hNc hN2 hMb
  have hCb : C.map π ≤ Subgroup.centralizer ({π t} : Set (Y ⧸ N)) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hg]
  have hMtC : Mt ≤ C := by
    intro x hx
    obtain ⟨c, hcC, hcx⟩ := hMbC hx
    have h1 : c⁻¹ * x ∈ N := by
      have := hcx
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
      exact this
    have hx' : x = c * (c⁻¹ * x) := by group
    rw [hx']
    exact C.mul_mem hcC (hNC h1)
  have hK₁Mt : K₁ ≤ Mt := fun k hk => hKM (Subgroup.mem_map_of_mem π hk)
  have hNMt : N ≤ Mt := fun n hn => by
    have h : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    show π n ∈ Mb
    rw [h]
    exact Mb.one_mem
  have hgen : K₁.map π ≤ Subgroup.closure {x : Y ⧸ N | x ∈ K₁.map π ∧
      IsPGroup 2 ↥(Subgroup.zpowers x)} := by
    have h1 := Subgroup.map_mono (f := π) (le_closure_two_of_mem_conjClass hK₁)
    rw [MonoidHom.map_closure] at h1
    refine h1.trans (Subgroup.closure_mono ?_)
    rintro _ ⟨x, ⟨hxK, hx2⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem π hxK, ?_⟩
    rw [← MonoidHom.map_zpowers]
    exact hx2.map _
  have hKbar : ∀ m ∈ Mb, conjSub m (K₁.map π) = K₁.map π :=
    conjSub_eq_of_classical hΩb hK₁b hzb hMb hKM hgen
  have hKnorm : ∀ l ∈ Mt, conjSub l K₁ = K₁ := by
    intro l hl
    have hconj : conjSub l K₁ ∈ CoreAssembly.conjClass (tightCore R) :=
      hΩ.conjInvariant l K₁ hK₁
    refine eq_of_map hΩ hNc hodd hconj hK₁ ?_
    rw [TwistQ.conjSub_map]
    exact hKbar (π l) hl
  have hcardMb : Nat.card ↥Mb = Nat.card ↥(K₁.map π) * (Nat.card ↥Mb / Nat.card ↥(K₁.map π)) := by
    exact (Nat.mul_div_cancel' (Subgroup.card_dvd_of_le hKM)).symm
  set d : ℕ := Nat.card ↥Mb / Nat.card ↥(K₁.map π) with hd
  have hdodd : Odd d := by
    have h3 := three_le_factorization hΩb hK₁b
    have hM3 := factorization_classical hMb
    have hle : (Nat.card ↥(K₁.map π)).factorization 2 ≤ (Nat.card ↥Mb).factorization 2 :=
      (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le hKM) 2
    have h4 : (Nat.card ↥Mb).factorization 2 =
        (Nat.card ↥(K₁.map π)).factorization 2 + d.factorization 2 := by
      conv_lhs => rw [hcardMb]
      rw [Nat.factorization_mul Nat.card_pos.ne' ?_]
      · rfl
      · intro h; rw [h] at hcardMb; simp at hcardMb; exact Nat.card_pos.ne' hcardMb
    have h5 : d.factorization 2 = 0 := by omega
    have hd0 : d ≠ 0 := by
      intro h; rw [h] at hcardMb; simp at hcardMb; exact Nat.card_pos.ne' hcardMb
    have : ¬ 2 ∣ d := fun h2 =>
      absurd h5 (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hd0 h2).ne'
    exact Nat.not_even_iff_odd.mp (fun he => this (even_iff_two_dvd.mp he))
  have hMtcard : Nat.card ↥Mt = Nat.card ↥Mb * Nat.card ↥N := by
    set f : ↥Mt →* Y ⧸ N := π.comp Mt.subtype with hf
    have hrange : f.range = Mb := by
      rw [hf, MonoidHom.range_comp, Subgroup.range_subtype, hMt,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N)]
    have hker : f.ker = N.subgroupOf Mt := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf, MonoidHom.comp_apply]
      exact QuotientGroup.eq_one_iff _
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, hker] at h1
    rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNMt).toEquiv]
  have hK₁card : Nat.card ↥(K₁.subgroupOf Mt) = Nat.card ↥(K₁.map π) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK₁Mt).toEquiv]
    exact Nat.card_congr (AscQuot.quotRestrictEquiv hK₁N').toEquiv
  have hKn : (K₁.subgroupOf Mt).Normal := by
    refine ⟨fun k hk g => ?_⟩
    have hk' : (k : Y) ∈ K₁ := hk
    show ((g * k * g⁻¹ : ↥Mt) : Y) ∈ K₁
    have := conj_mem_conjSub (n := (g : Y)) hk'
    rw [hKnorm g g.2] at this
    exact this
  have hZc : N.subgroupOf Mt ≤ Subgroup.center ↥Mt := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hNc (Subgroup.mem_subgroupOf.mp hz)) g)
  have hZ2 : IsPGroup 2 ↥(N.subgroupOf Mt) := hN2.comap_subtype
  have hKZ : K₁.subgroupOf Mt ⊓ N.subgroupOf Mt = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxN⟩
    have : (x : Y) ∈ K₁ ⊓ N := ⟨hxK, hxN⟩
    rw [hK₁N', Subgroup.mem_bot] at this
    exact Subtype.ext this
  have hcard : Nat.card ↥Mt = Nat.card ↥(K₁.subgroupOf Mt) * Nat.card ↥(N.subgroupOf Mt) * d := by
    rw [hMtcard, hK₁card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNMt).toEquiv]
    conv_lhs => rw [hcardMb]
    ring
  have hodd1 := odd1 (K₁.subgroupOf Mt) (N.subgroupOf Mt) hZc hZ2 hKZ hdodd hcard
  set MG : Subgroup ↥Mt := Subgroup.closure {x : ↥Mt | Odd (orderOf x)} with hMG
  have hMmap : MG.map Mt.subtype = M := by
    rw [hMG, MonoidHom.map_closure, hM]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : Odd (orderOf x) := hx
      refine ⟨x.2, ?_⟩
      show Odd (orderOf (x : Y))
      rwa [Subgroup.orderOf_coe]
    · rintro ⟨hy, hyo⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      show Odd (orderOf (⟨y, hy⟩ : ↥Mt))
      rw [← Subgroup.orderOf_coe]
      exact hyo
  have hKmap : (K₁.subgroupOf Mt).map Mt.subtype = K₁ := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr hK₁Mt
  have hstar : ∀ h ∈ K₁ ⊔ M, h ∈ N → h = 1 := by
    intro h hh hN
    have h1 : h ∈ (MG ⊔ K₁.subgroupOf Mt).map Mt.subtype := by
      rw [Subgroup.map_sup, hMmap, hKmap, sup_comm]
      exact hh
    obtain ⟨y, hy, rfl⟩ := h1
    have hyZ : y ∈ N.subgroupOf Mt := hN
    have : y ∈ (MG ⊔ K₁.subgroupOf Mt) ⊓ N.subgroupOf Mt := ⟨hy, hyZ⟩
    rw [hodd1, Subgroup.mem_bot] at this
    rw [this]
    rfl
  have hMMt : M ≤ Mt := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hπM : M.map π = Mb := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr hMMt) ?_
    obtain ⟨e⟩ := hMb.nonempty_equiv
    obtain ⟨ψ, hψs, hψk⟩ := Q3T7T2.exists_proj e
    have hcl := Q3T7T2.odd_closure_of_proj ψ hψs hψk
    rw [← hcl]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxMb, hxo⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    have hxC := (isSubnormal_le hMb.subnormal) hxMb
    obtain ⟨g, hgC, hgm, hgx⟩ :=
      exists_lift_centralizer (t := t) hNc hN2 hxo hxC (pow_orderOf_eq_one _)
    have hgodd : Odd (orderOf g) := hxo.of_dvd_nat (orderOf_dvd_of_pow_eq_one hgm)
    have hgMt : g ∈ Mt := by
      show π g ∈ Mb
      rw [hgx]
      exact hxMb
    exact ⟨g, Subgroup.subset_closure ⟨hgMt, hgodd⟩, hgx⟩
  have hinj : ∀ a ∈ K₁ ⊔ M, ∀ b ∈ K₁ ⊔ M, π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ N := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
      exact hab
    have h2 := hstar _ ((K₁ ⊔ M).mul_mem ((K₁ ⊔ M).inv_mem ha) hb) h1
    exact inv_mul_eq_one.mp h2
  have hKM' : K₁ ≤ M := by
    intro k hk
    have hπk : π k ∈ M.map π := by
      rw [hπM]
      exact hKM (Subgroup.mem_map_of_mem π hk)
    obtain ⟨m, hm, hmk⟩ := hπk
    have := hinj m (Subgroup.mem_sup_right hm) k (Subgroup.mem_sup_left hk) hmk
    rw [← this]
    exact hm
  have hMN : M ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxM, hxN⟩
    exact Subgroup.mem_bot.mpr (hstar x (Subgroup.mem_sup_right hxM) hxN)
  have hMC : M ≤ C := hMMt.trans hMtC
  have hClass : IsClassicalMember3 M t := by
    refine ⟨ht2, hKM' hz.mem, ?_, ?_⟩
    · have hsub1 : IsSubnormal Mb (C.map π) := by
        have h := isSubnormal_inf hMb.subnormal (C.map π)
        rwa [inf_eq_left.mpr hMbC, inf_eq_right.mpr hCb] at h
      have hsub2 := isSubnormal_comap' π hsub1
      have hcm : (C.map π).comap π = C := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
        exact sup_eq_left.mpr hNC
      rw [hcm] at hsub2
      refine IsSubnormal.step hMMt ?_ hsub2
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMMt]
      intro g hg
      rw [mem_normalizer_iff_conjSub_eq]
      exact conjSub_closure_odd hg
    · have hMb' : IsClassicalMember3 (M.map π) (π t) := by
        rw [hπM]
        exact hMb
      obtain ⟨e⟩ := hMb'.nonempty_equiv
      have he := CFSG.ABGLocalTools.oddCore_map_mulEquiv (TwistQ.mapEquiv (N := N) hMN)
      exact ⟨(QuotientGroup.congr _ _ (TwistQ.mapEquiv hMN) he).trans e⟩
  exact ⟨M, rfl, hπM, hKM', hMC, hClass⟩

theorem commute_of_odd (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N) {x y : Y}
    (hx : Odd (orderOf x))
    (hxy : QuotientGroup.mk' N x * QuotientGroup.mk' N y =
      QuotientGroup.mk' N y * QuotientGroup.mk' N x) : x * y = y * x := by
  set c : Y := x * y * x⁻¹ * y⁻¹ with hc
  have hcN : c ∈ N := by
    have h1 : QuotientGroup.mk' N c = 1 := by
      rw [hc]
      simp only [map_mul, map_inv]
      rw [hxy]
      group
    exact (QuotientGroup.eq_one_iff c).mp h1
  have hcZ : ∀ a : Y, a * c = c * a := Subgroup.mem_center_iff.mp (hNc hcN)
  have hconj : x * y * x⁻¹ = y * c := by
    rw [hc]
    have := hcZ y
    calc x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
      _ = c * y := rfl
      _ = y * c := (hcZ y).symm
  have hpow := pow_conj_central hcZ hconj (orderOf x)
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at hpow
  have hcm : c ^ orderOf x = 1 := mul_left_cancel (a := y) (by rw [mul_one]; exact hpow.symm)
  have hc1 : c = 1 := eq_one_of_pow_odd hx (hN2.to_le (Subgroup.zpowers_le.mpr hcN)) hcm
  rw [hc1] at hconj
  calc x * y = (x * y * x⁻¹) * x := by group
    _ = y * x := by rw [hconj, mul_one]

theorem commute_closure_odd (hNc : N ≤ Subgroup.center Y) (hN2 : IsPGroup 2 ↥N)
    {A B : Subgroup (Y ⧸ N)} (hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) :
    ∀ x ∈ Subgroup.closure {x : Y | x ∈ A.comap (QuotientGroup.mk' N) ∧ Odd (orderOf x)},
      ∀ y ∈ Subgroup.closure {x : Y | x ∈ B.comap (QuotientGroup.mk' N) ∧ Odd (orderOf x)},
        x * y = y * x := by
  have h1 : ∀ y : Y, y ∈ B.comap (QuotientGroup.mk' N) → Odd (orderOf y) →
      Subgroup.closure {x : Y | x ∈ A.comap (QuotientGroup.mk' N) ∧ Odd (orderOf x)} ≤
        Subgroup.centralizer ({y} : Set Y) := by
    intro y hy hyo
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (commute_of_odd hNc hN2 (x := y) (y := x) hyo (hAB _ hx.1 _ hy).symm).symm
  intro x hx
  have h2 : Subgroup.closure {x : Y | x ∈ B.comap (QuotientGroup.mk' N) ∧ Odd (orderOf x)} ≤
      Subgroup.centralizer ({x} : Set Y) := by
    refine (Subgroup.closure_le _).mpr fun y hy => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (h1 y hy.1 hy.2 hx)).symm
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.mp (h2 hy)).symm

omit [Finite Y] [N.Normal] in
theorem twinE4_of_surjective {Y' : Type} [Group Y'] (g : Y →* Y') (hg : Function.Surjective g)
    (hk : IsPGroup 2 ↥g.ker) (h : TwinE4 Y') : TwinE4 Y := by
  obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := h
  refine ⟨Q, inferInstance, f.comp g, hfs.comp hg, ?_, hQ⟩
  rw [← MonoidHom.comap_ker]
  exact hf2.comap_of_ker_isPGroup g hk

end TwinRed

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
