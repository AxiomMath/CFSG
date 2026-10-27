module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieOrder
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309LieMono
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelCov
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelLU
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelLin
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309ModelPhi
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291SCY

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309L
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309M
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
open CFSG.ABGLocalTools

@[expose] def ShapeStmt : Prop :=
  ∀ (p : ℕ) (Y : Type) [Group Y] [Finite Y] (P : Subgroup Y) (x z : Y) (L : Subgroup Y),
    LinUniCfg p P x z L → LinUniShape p x L

namespace KD309M

theorem centralizer_eq_bot_of_center {Y' : Type} [Group Y'] [Finite Y'] {L : Subgroup Y'}
    (hcore : primeComplementCore (G := Y') 5 = ⊥) (hL : IsComponentOf L ⊤)
    (hLu : ∀ K : Subgroup Y', IsComponentOf K ⊤ → K = L) (hzero : LinUniZero 5 L)
    (hCp : IsPGroup 5 (centralizer (L : Set Y'))) (hZ : center ↥L = ⊥) :
    centralizer (L : Set Y') = ⊥ := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  by_contra hne
  have hC5 : 5 ∣ Nat.card (centralizer (L : Set Y')) := by
    obtain ⟨k, hk⟩ := hCp.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
    rw [hk]
    exact dvd_pow_self 5 hk0
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 5 hC5
  have hgC : (g : Y') ∈ centralizer (L : Set Y') := g.2
  have hg5 : (g : Y') ^ 5 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    simpa using congrArg Subtype.val h
  have hgp : (g : Y') ∈ CFSG.pCore 5 Y' := by
    rw [← I292.centralizer_eq_pCore hcore hL hLu hzero.pCore_cyclic hzero.omega_le]
    exact hgC
  have hgL : (g : Y') ∈ L := hzero.omega_le (g : Y') hgp hg5
  have hmem : (⟨(g : Y'), hgL⟩ : ↥L) ∈ center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hgC l l.2)
  rw [hZ, Subgroup.mem_bot] at hmem
  have h0 : (g : Y') = 1 := congrArg Subtype.val hmem
  have h1 : g = 1 := Subtype.ext h0
  rw [h1, orderOf_one] at hg
  norm_num at hg

theorem pkg_of_plane63 (hS : ShapeStmt) {Y : Type} [Group Y] [Finite Y] {P : Sylow 5 Y}
    {x z : Y} (hpl : Plane63 5 Y P x z)
    {L : Subgroup (Y ⧸ primeComplementCore (G := Y) 5)} (hL : IsComponentOf L ⊤)
    (hLu : ∀ K : Subgroup (Y ⧸ primeComplementCore (G := Y) 5), IsComponentOf K ⊤ → K = L)
    (h29 : I291P65.Is29a ↥L) [L.Normal] [Group.IsPerfect ↥L] :
    IsPGroup 5 ↥(centralizer (L : Set (Y ⧸ primeComplementCore (G := Y) 5))) ∧
      LinUniZero 5 L ∧
      Nonempty (Pkg (Y ⧸ primeComplementCore (G := Y) 5) L
        (x : Y ⧸ primeComplementCore (G := Y) 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hYD := I291.yData_of_plane63 hpl
  have hlu := is29a_isLinearOrUnitaryAt hL.2.2 h29
  have hcfg : LinUniCfg 5 ((P : Subgroup Y).map
      (QuotientGroup.mk' (primeComplementCore (G := Y) 5)))
      (x : Y ⧸ primeComplementCore (G := Y) 5) (z : Y ⧸ primeComplementCore (G := Y) 5) L :=
    ⟨hYD, hL, hLu, hlu⟩
  have hshape := hS 5 _ _ _ _ L hcfg
  have hCp : IsPGroup 5 (centralizer (L : Set (Y ⧸ primeComplementCore (G := Y) 5))) :=
    I292.centralizer_isPGroup hYD.cfg.core hL hLu hshape.zero.pCore_cyclic
      hshape.zero.omega_le
  exact ⟨hCp, hshape.zero, hshape.model.elim (pkg_lin hcfg hCp) (pkg_uni hcfg hCp)⟩

theorem second_disjunct {Y : Type} [Group Y] [Finite Y] (P : Sylow 5 Y) {x : Y}
    (hxP : x ∈ (P : Subgroup Y)) (L : Subgroup (Y ⧸ primeComplementCore (G := Y) 5)) [L.Normal]
    (hxL : (x : Y ⧸ primeComplementCore (G := Y) 5) ∉ L)
    (hP6 : Nat.card (P : Subgroup Y) ≤ 5 ^ 6)
    (hsyl : ∀ T : Sylow 5 ↥L, Nat.card (T : Subgroup ↥L) ≤ 5 ^ 5 →
      Nat.card (T : Subgroup ↥L) = 5 ^ 5 ∧ (∀ t ∈ (T : Subgroup ↥L), t ^ 5 = 1) ∧
        ∃ s ∈ (T : Subgroup ↥L), ∃ t ∈ (T : Subgroup ↥L), s * t ≠ t * s) :
    ∃ S : Subgroup Y, S ≤ (P : Subgroup Y) ∧ Nat.card (P : Subgroup Y) = 5 ^ 6 ∧
      Nat.card S = 5 ^ 5 ∧ (∀ s ∈ S, s ^ 5 = 1) ∧ (∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) ∧
        x ∉ S := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set O : Subgroup Y := primeComplementCore (G := Y) 5 with hO
  have hOcop : ¬ 5 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mp (primeComplementCore_coprime 5)
  set π : Y →* Y ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hpP : IsPGroup 5 (P : Subgroup Y) := P.isPGroup'
  have inj : ∀ a ∈ (P : Subgroup Y), ∀ b ∈ (P : Subgroup Y), π a = π b → a = b :=
    inj_of_pgroup O hOcop hpP
  let Pb : Sylow 5 (Y ⧸ O) := Sylow.mapSurjective hπs P
  have hPb : (Pb : Subgroup (Y ⧸ O)) = (P : Subgroup Y).map π := rfl
  have hPbcard : Nat.card (Pb : Subgroup (Y ⧸ O)) = Nat.card (P : Subgroup Y) := by
    rw [hPb]
    exact card_map_eq_of_inj π _ inj
  have hxPb : (x : Y ⧸ O) ∈ (Pb : Subgroup (Y ⧸ O)) := ⟨x, hxP, rfl⟩
  have hPbS : IsSylowOf 5 (Pb : Subgroup (Y ⧸ O)) ⊤ :=
    isSylowOf_of_card le_top (by rw [Subgroup.card_top]; exact Pb.card_eq_multiplicity)
  have hnorm : (⊤ : Subgroup (Y ⧸ O)) ≤ normalizer (L : Set (Y ⧸ O)) := by
    intro g _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => Subgroup.Normal.conj_mem inferInstance h hh g, fun hh => ?_⟩
    have := Subgroup.Normal.conj_mem inferInstance _ hh g⁻¹
    simpa [mul_assoc] using this
  have hTS : IsSylowOf 5 ((Pb : Subgroup (Y ⧸ O)) ⊓ L) L :=
    hPbS.inf_of_le_normalizer le_top hnorm
  obtain ⟨Tsyl, hTsyl⟩ := hTS.exists_sylow_eq_subgroupOf
  set T' : Subgroup (Y ⧸ O) := (Pb : Subgroup (Y ⧸ O)) ⊓ L with hT'
  have hT'card : Nat.card (Tsyl : Subgroup ↥L) = Nat.card T' := by
    rw [hTsyl]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : T' ≤ L)).toEquiv
  have hT'lt : Nat.card T' < Nat.card (Pb : Subgroup (Y ⧸ O)) := by
    refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun h => hxL ?_)
    have : (x : Y ⧸ O) ∈ T' := by rw [h]; exact hxPb
    exact this.2
  obtain ⟨m, hm⟩ := Pb.isPGroup'.exists_card_eq
  obtain ⟨k, hk⟩ := (Pb.isPGroup'.to_le (inf_le_left : T' ≤ (Pb : Subgroup (Y ⧸ O)))).exists_card_eq
  rw [hk, hm] at hT'lt
  have hkm : k < m := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hT'lt
  have hm6 : m ≤ 6 := by
    rw [hPbcard] at hm
    rw [hm] at hP6
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hP6
  have hT5 : Nat.card (Tsyl : Subgroup ↥L) ≤ 5 ^ 5 := by
    rw [hT'card, hk]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hTc, hexp, u, hu, v, hv, huv⟩ := hsyl Tsyl hT5
  rw [hT'card] at hTc
  have hk5 : k = 5 := by
    rw [hk] at hTc
    exact Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num)) hTc
  have hm6' : m = 6 := by omega
  have hPc : Nat.card (P : Subgroup Y) = 5 ^ 6 := by rw [← hPbcard, hm, hm6']
  set S : Subgroup Y := (L.comap π) ⊓ (P : Subgroup Y) with hS
  have hSmap : S.map π = T' := by
    ext y
    constructor
    · rintro ⟨s, ⟨hsL, hsP⟩, rfl⟩
      exact ⟨⟨s, hsP, rfl⟩, hsL⟩
    · rintro ⟨⟨p, hp, rfl⟩, hpL⟩
      exact ⟨p, ⟨hpL, hp⟩, rfl⟩
  have hScard : Nat.card S = 5 ^ 5 := by
    have h1 := card_map_eq_of_inj π S (fun a ha b hb hab => inj a ha.2 b hb.2 hab)
    rw [hSmap] at h1
    rw [← h1]
    exact hTc
  refine ⟨S, inf_le_right, hPc, hScard, ?_, ?_, ?_⟩
  · intro s hs
    have hπs' : π s ∈ T' := by rw [← hSmap]; exact ⟨s, hs, rfl⟩
    have hmem : (⟨π s, hs.1⟩ : ↥L) ∈ (Tsyl : Subgroup ↥L) := by
      rw [hTsyl]
      exact hπs'
    have h5 := hexp _ hmem
    have h6 : (π s) ^ 5 = 1 := congrArg Subtype.val h5
    have h7 : π (s ^ 5) = π 1 := by rw [map_pow, map_one]; exact h6
    exact inj _ (pow_mem hs.2 5) 1 (one_mem _) h7
  · have hlift : ∀ w : ↥L, w ∈ (Tsyl : Subgroup ↥L) → ∃ a ∈ S, π a = (w : Y ⧸ O) := by
      intro w hw
      rw [hTsyl] at hw
      have hw' : (w : Y ⧸ O) ∈ T' := hw
      obtain ⟨a, ha, haw⟩ := hw'.1
      have haL : π a ∈ L := by
        rw [haw]
        exact w.2
      exact ⟨a, ⟨haL, ha⟩, haw⟩
    obtain ⟨a, ha, hau⟩ := hlift u hu
    obtain ⟨b, hb, hbv⟩ := hlift v hv
    refine ⟨a, ha, b, hb, fun hab => huv ?_⟩
    apply Subtype.ext
    have := congrArg π hab
    rw [map_mul, map_mul, hau, hbv] at this
    exact this
  · intro hxS
    exact hxL hxS.1

theorem exists_sylow_quot {Y : Type} [Group Y] [Finite Y] (P : Sylow 5 Y) :
    ∃ Pb : Sylow 5 (Y ⧸ primeComplementCore (G := Y) 5),
      Nat.card (Pb : Subgroup (Y ⧸ primeComplementCore (G := Y) 5)) =
        Nat.card (P : Subgroup Y) := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set O : Subgroup Y := primeComplementCore (G := Y) 5 with hO
  have hOcop : ¬ 5 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mp (primeComplementCore_coprime 5)
  set π : Y →* Y ⧸ O := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have inj := inj_of_pgroup O hOcop (P.isPGroup' : IsPGroup 5 (P : Subgroup Y))
  refine ⟨Sylow.mapSurjective hπs P, ?_⟩
  change Nat.card ((P : Subgroup Y).map π) = _
  exact card_map_eq_of_inj π _ inj

theorem not_mem_of_pkg {Y' : Type} [Group Y'] [Finite Y'] {L : Subgroup Y'} [L.Normal] {x : Y'}
    (pkg : Pkg Y' L x) : x ∉ L := fun hxL =>
  pkg.hout ⟨_, (thetaP_of_mem L pkg.eP ⟨x, hxL⟩).symm⟩

end KD309M

theorem kd309OrderModel_of_shape (hS : ShapeStmt) : KD309OrderModel := by
  intro Y _ _ P x z hpl L hL hLu h29 hP6
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI hLn : L.Normal := I291.normal_of_unique hL hLu
  haveI hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  obtain ⟨hCp, hzero, ⟨pkg⟩⟩ := pkg_of_plane63 hS hpl hL hLu h29
  obtain ⟨hxP, -, -, -, -, -⟩ := I291P65.plane_facts hpl.prime hpl.plane
  have hYD := I291.yData_of_plane63 hpl
  have hxL := not_mem_of_pkg pkg
  obtain ⟨Pb, hPbcard⟩ := exists_sylow_quot P
  have hord := card_sylow_eq pkg.M Nat.prime_five pkg.hAut hCp Pb pkg.hGL pkg.hker
  have hcomm : commutator ↥L = ⊤ := hL.2.2.1
  have hleft : center ↥L = ⊥ →
      Nat.card (P : Subgroup Y) ≤ 5 ^ 5 ∨ ∃ S : Subgroup Y, S ≤ (P : Subgroup Y) ∧
        Nat.card (P : Subgroup Y) = 5 ^ 6 ∧ Nat.card S = 5 ^ 5 ∧ (∀ s ∈ S, s ^ 5 = 1) ∧
          (∃ a ∈ S, ∃ b ∈ S, a * b ≠ b * a) ∧ x ∉ S := fun hZ => by
    left
    have hC1 := centralizer_eq_bot_of_center hYD.cfg.core hL hLu hzero hCp hZ
    rw [hC1, Subgroup.card_bot, one_mul] at hord
    rw [← hPbcard, hord]
    rw [← hPbcard, hord] at hP6
    have h1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).mp hP6
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases h29 with ⟨K0, _, _, hpK, he⟩ | ⟨q0, K0, _, _, hK0, hpq0, he⟩
  · rcases he with ⟨⟨e0⟩⟩ | ⟨⟨e0⟩⟩
    · exact Or.inr (second_disjunct P hxP L hxL hP6 fun T hT => sylow_statedSL e0 hpK T hT)
    · exact hleft (center_eq_bot_of_psl hcomm e0)
  · rcases he with ⟨⟨e0⟩⟩ | ⟨⟨e0⟩⟩
    · exact Or.inr (second_disjunct P hxP L hxL hP6 fun T hT => sylow_statedSU e0 hK0 hpq0 T hT)
    · exact hleft (center_eq_bot_of_psu hcomm hK0 e0)

theorem kd309MonoModel_of_shape (hS : ShapeStmt) : KD309MonoModel := by
  intro Y _ _ P x z hpl L hL hLu h29 hPcard
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI hLn : L.Normal := I291.normal_of_unique hL hLu
  haveI hperf : Group.IsPerfect ↥L := ⟨hL.2.2.1⟩
  obtain ⟨hCp, hzero, ⟨pkg⟩⟩ := pkg_of_plane63 hS hpl hL hLu h29
  obtain ⟨Pb, hPbcard⟩ := exists_sylow_quot P
  have hord := card_sylow_eq pkg.M Nat.prime_five pkg.hAut hCp Pb pkg.hGL pkg.hker
  rw [hPbcard, hPcard] at hord
  have hC1 : Nat.card (centralizer (L : Set (Y ⧸ primeComplementCore (G := Y) 5))) = 1 := by
    have h1 : 5 ^ 5 ≤ 5 ^ ((5 - 1) * pkg.a + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by have := pkg.ha; omega)
    have hpos : 0 < 5 ^ ((5 - 1) * pkg.a + 1) := by positivity
    have hCpos : 0 < Nat.card (centralizer (L : Set (Y ⧸ primeComplementCore (G := Y) 5))) :=
      Nat.card_pos
    by_contra hne
    have h2 : 2 ≤ Nat.card (centralizer (L : Set (Y ⧸ primeComplementCore (G := Y) 5))) := by
      omega
    nlinarith
  have hC1' : centralizer (L : Set (Y ⧸ primeComplementCore (G := Y) 5)) = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ hC1
  obtain ⟨Φ, hΦ, w, hw⟩ := exists_phi pkg hC1'
  refine ⟨Φ, hΦ, ?_, w, hw⟩
  have h1 := card_map_mul_five hΦ (Sc_le_T5.trans T5_le_Pm)
  rw [card_Pm] at h1
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
