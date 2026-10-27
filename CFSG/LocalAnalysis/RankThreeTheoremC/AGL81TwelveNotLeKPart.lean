module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeHat
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGroup
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenElevenCfgOf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeGamma
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeNormalRank
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenReduce
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNormalizesNoSU
import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIIConfigO2
import CFSG.LocalAnalysis.AGLEmbedding.SUPairCommute
import CFSG.HardMathSupport.Cooperstein.Proving.A6Z3Kernel
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenTwelveOneSetup

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111 Subgroup
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.ComponentClassification.AS76b (oUpperTwo)
open CFSG.HardMathSupport.Cooperstein.Proving (barMHomSub subgroupOf_barM_eq_map)

section Perfect

variable {V : Type} [Group V] [Finite V]

theorem oUpperTwo_eq_self_of_perfect {X : Subgroup V} (hX : ⁅X, X⁆ = X) : oUpperTwo X = X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := oUpperTwo X with hOdef
  have hOX : O ≤ X := CFSG.AGLEmbedding.oUpperTwo_le_self X
  haveI hn : (O.subgroupOf X).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hOX]
    intro c hc
    rw [mem_normalizer_iff]
    intro y
    exact ⟨fun hy => CFSG.ComponentClassification.RankTwoHypIIClassical.oUpperTwo_conj_mem hc hy,
      fun hy => by
        have h := CFSG.ComponentClassification.RankTwoHypIIClassical.oUpperTwo_conj_mem
          (X.inv_mem hc) hy
        simpa [mul_assoc] using h⟩
  have hp : IsPGroup 2 (↥X ⧸ O.subgroupOf X) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (O.subgroupOf X) q
    obtain ⟨a, ha⟩ := CFSG.AGLEmbedding.SUPair.exists_two_pow_mem x.2
    refine ⟨a, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    simpa using ha
  haveI : Group.IsNilpotent (↥X ⧸ O.subgroupOf X) := hp.isNilpotent
  have htop : ⁅(⊤ : Subgroup ↥X), (⊤ : Subgroup ↥X)⁆ = (⊤ : Subgroup ↥X) := by
    apply map_injective X.subtype_injective
    rw [map_commutator, Subgroup.map_top, range_subtype, hX]
  have hcomm : commutator (↥X ⧸ O.subgroupOf X) = ⊤ := by
    rw [_root_.commutator_def,
      ← map_top_of_surjective _ (QuotientGroup.mk'_surjective (O.subgroupOf X)), ← map_commutator,
      htop]
  rcases subsingleton_or_nontrivial (↥X ⧸ O.subgroupOf X) with hs | hnt
  · refine le_antisymm hOX fun x hx => ?_
    have h1 : QuotientGroup.mk' (O.subgroupOf X) ⟨x, hx⟩ = 1 := Subsingleton.elim _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    exact h1
  · exact absurd hcomm (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial _))

theorem commutator_subgroupOf_eq_of_perfect {L X : Subgroup V} (hLX : L ≤ X) (hp : ⁅L, L⁆ = L) :
    ⁅L.subgroupOf X, L.subgroupOf X⁆ = L.subgroupOf X := by
  apply map_injective X.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hLX, hp]

theorem mem_sylow_of_mem_normalizer {p : ℕ} [Fact p.Prime] (S : Sylow p V) {x : V}
    (hx : x ∈ normalizer ((S : Subgroup V) : Set V)) {k : ℕ} (hxk : x ^ p ^ k = 1) :
    x ∈ (S : Subgroup V) := by
  have hp : IsPGroup p (zpowers x) := by
    have hd : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have h := hp.inf_normalizer_sylow S
  exact (h.le ⟨mem_zpowers x, hx⟩).2

theorem exists_lift_cube {I : Subgroup V} (c : ↥I ⧸ CFSG.pCore 2 ↥I) (hc : c ^ 3 = 1) :
    ∃ x : ↥I, x ^ 3 = 1 ∧ ∃ n : ℕ, (QuotientGroup.mk' (CFSG.pCore 2 ↥I) x) ^ n = c := by
  obtain ⟨e, he⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).exists_card_eq
  obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I) c
  have hx'O : x' ^ 3 ∈ CFSG.pCore 2 ↥I := by
    rw [← QuotientGroup.eq_one_iff, ← hc]
    rfl
  refine ⟨x' ^ (2 ^ e), ?_, 2 ^ e, ?_⟩
  · have h1 := pow_card_eq_one' (G := ↥(CFSG.pCore 2 ↥I)) (x := ⟨x' ^ 3, hx'O⟩)
    rw [he] at h1
    have h2 : (x' ^ 3) ^ (2 ^ e) = 1 := by simpa using congrArg Subtype.val h1
    rw [← pow_mul, mul_comm, pow_mul, h2]
  · have h4 : 2 ^ e * 2 ^ e % 3 = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    rw [map_pow, ← pow_mul, pow_eq_pow_mod _ hc, h4, pow_one]

end Perfect

variable {G : Type} [Group G] [Finite G]

section Parts

variable {H : Subgroup G} {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem center_eq_bot_of_isAltTwoP (hA6 : IsAltTwoP 3 K) : center ↥K = ⊥ := by
  obtain ⟨e⟩ := hA6
  have hcen : (center ↥K).map e.toMonoidHom = center (alternatingGroup (Fin (2 * 3))) :=
    map_center_eq e
  rw [alternatingGroup.center_eq_bot (by simp)] at hcen
  exact (map_eq_bot_iff_of_injective _ e.injective).1 hcen

theorem coprime_orderOf_of_mem_hyp111Pre_d1PlusCore (hZ : center ↥K = ⊥) {x : G}
    (hxK : x ∈ hyp111Pre 3 H K) (hxX : x ∈ d1PlusCore 3 H K) : Nat.Coprime 3 (orderOf x) := by
  obtain ⟨h, hhK, rfl⟩ := hxK
  obtain ⟨h', hh'C, hh'⟩ := hxX
  have hhh : h' = h := H.subtype_injective hh'
  subst hhh
  set N := primeComplementCore (G := H) 3 with hN
  have hk : (⟨QuotientGroup.mk' N h', hhK⟩ : ↥K) ∈ center ↥K := by
    rw [mem_center_iff]
    intro k
    apply Subtype.ext
    exact ((mem_centralizer_iff.mp hh'C) k k.2)
  rw [hZ, mem_bot] at hk
  have h1 : QuotientGroup.mk' N h' = 1 := congrArg Subtype.val hk
  have hmem : h' ∈ N := (QuotientGroup.eq_one_iff h').mp h1
  have hd : orderOf h' ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hmem
  rw [Subgroup.subtype_apply, Subgroup.orderOf_coe]
  exact (primeComplementCore_coprime (G := H) 3).coprime_dvd_right hd

theorem eq_one_of_mem_hyp111Pre_d1PlusCore (hZ : center ↥K = ⊥) {x : G}
    (hxK : x ∈ hyp111Pre 3 H K) (hxX : x ∈ d1PlusCore 3 H K) {k : ℕ} (hx : x ^ 3 ^ k = 1) :
    x = 1 := by
  have hc := coprime_orderOf_of_mem_hyp111Pre_d1PlusCore hZ hxK hxX
  have h1 : orderOf x = 1 :=
    ((Nat.Coprime.pow_left k hc).symm.coprime_dvd_left dvd_rfl).eq_one_of_dvd
      (orderOf_dvd_of_pow_eq_one hx) |>.symm ▸ rfl
  exact orderOf_eq_one_iff.mp h1

theorem coprime_orderOf_commutator_of_mem {x y : G} (hx : x ∈ hyp111Pre 3 H K)
    (hy : y ∈ d1PlusCore 3 H K) :
    Nat.Coprime 3 (orderOf (y * x * y⁻¹ * x⁻¹)) := by
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  set N := primeComplementCore (G := H) 3 with hN
  set c₀ : H := y₀ * x₀ * y₀⁻¹ * x₀⁻¹ with hc₀def
  have hc₀ : c₀ ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
    have hcomm : QuotientGroup.mk' N x₀ * QuotientGroup.mk' N y₀ =
        QuotientGroup.mk' N y₀ * QuotientGroup.mk' N x₀ :=
      (mem_centralizer_iff.mp hy₀) _ hx₀
    rw [hc₀def, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  have hd : orderOf c₀ ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hc₀
  have he : H.subtype y₀ * H.subtype x₀ * (H.subtype y₀)⁻¹ * (H.subtype x₀)⁻¹ = H.subtype c₀ := by
    simp [hc₀def]
  rw [he, Subgroup.subtype_apply, Subgroup.orderOf_coe]
  exact (primeComplementCore_coprime (G := H) 3).coprime_dvd_right hd

theorem mem_normalizer_map_comap {N' : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    [N'.Normal] {h : G} (hh : h ∈ H) :
    h ∈ normalizer ((N'.comap (QuotientGroup.mk' (primeComplementCore (G := H) 3))).map
      H.subtype : Set G) := by
  haveI : (N'.comap (QuotientGroup.mk' (primeComplementCore (G := H) 3))).Normal :=
    Subgroup.Normal.comap inferInstance _
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨x₀, hx₀, rfl⟩
    exact ⟨(⟨h, hh⟩ : ↥H) * x₀ * (⟨h, hh⟩ : ↥H)⁻¹, Normal.conj_mem inferInstance _ hx₀ _, rfl⟩
  · rintro ⟨y₀, hy₀, hy⟩
    set w : ↥H := (⟨h, hh⟩ : ↥H)⁻¹ * y₀ * (⟨h, hh⟩ : ↥H) with hw
    have hwx : (w : G) = x := by
      have h1 : (y₀ : G) = h * x * h⁻¹ := hy
      rw [hw, coe_mul, coe_mul, coe_inv, h1]
      group
    refine ⟨w, ?_, hwx⟩
    have h2 := Normal.conj_mem (inferInstance :
      (N'.comap (QuotientGroup.mk' (primeComplementCore (G := H) 3))).Normal) _ hy₀
      (⟨h, hh⟩ : ↥H)⁻¹
    simpa [hw] using h2

theorem mem_normalizer_hyp111Pre_d1PlusCore [K.Normal] {h : G} (hh : h ∈ H) :
    h ∈ normalizer (hyp111Pre 3 H K : Set G) ∧ h ∈ normalizer (d1PlusCore 3 H K : Set G) :=
  ⟨mem_normalizer_map_comap (N' := K) hh,
    mem_normalizer_map_comap (N' := centralizer (K : Set (H ⧸ primeComplementCore (G := H) 3))) hh⟩

end Parts

section Shape

variable {P : Sylow 3 G} {M H Q : Subgroup G}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem kPart_shape (hAS : KFactTwelveNotLeAltSix) (hd : AGL81CfgData 3 P M H Q K)
    (hA6 : IsAltTwoP 3 K) (S : Sylow 3 ↥K)
    (hS : (S : Subgroup K).map K.subtype =
      (Q.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ⊓ K)
    {L I₀ : Subgroup G} (hLM : L ≤ M) (hI₀ : I₀ ∈ cZero (H ⊓ L))
    (hIK : oUpperTwo I₀ ≤ hyp111Pre 3 H K) (h3 : 3 ∣ Nat.card (oUpperTwo I₀)) :
    pCoreOf 2 I₀ = pCoreOf 2 (H ⊓ L) ∧
      Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* Equiv.Perm (Fin 3)) ∧
      ((oUpperTwo I₀).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ≤
        (S : Subgroup K).map K.subtype ∧
      Nat.card (((oUpperTwo I₀).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) 3))) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := primeComplementCore (G := H) 3 with hN
  set π := QuotientGroup.mk' N with hπ
  have hI₀' : IsCZeroMember (H ⊓ L) I₀ := hI₀
  set I := oUpperTwo I₀ with hIdef
  have hII₀ : I ≤ I₀ := CFSG.AGLEmbedding.oUpperTwo_le_self I₀
  have hI₀M : I₀ ≤ H ⊓ M := hI₀'.le.trans (inf_le_inf le_rfl hLM)
  have hI₀H : I₀ ≤ H := hI₀M.trans inf_le_left
  have hIH : I ≤ H := hII₀.trans hI₀H
  set Ist := (I.subgroupOf H).map π with hIst
  have hIstK : Ist ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hIK (mem_subgroupOf.mp hx)
    have : y = x := H.subtype_injective hyx
    rw [← this]
    exact hy
  have hIstX : Ist ≤ d1X0 3 M H := TenThirteen.map_mk_le_d1X0 (hII₀.trans hI₀M)
  set U : Subgroup ↥K := (d1X0 3 M H).subgroupOf K with hU
  have hEU : (S : Subgroup ↥K) ≤ U := by
    intro s hs
    rw [hU, mem_subgroupOf]
    have h1 : (s : H ⧸ N) ∈ (S : Subgroup K).map K.subtype := ⟨s, hs, rfl⟩
    rw [hS] at h1
    have hQX : Q.subgroupOf H ≤ (H ⊓ M).subgroupOf H := fun x hx =>
      mem_subgroupOf.mpr (mem_inf.mpr ⟨x.2, hd.base.1 (mem_subgroupOf.mp hx)⟩)
    exact map_mono hQX h1.1
  have hUtop : U ≠ ⊤ := by
    intro h
    apply hd.not_le_X0
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ U := h ▸ mem_top _
    exact mem_subgroupOf.mp this
  have hUN : U ≤ normalizer ((S : Subgroup ↥K) : Set ↥K) := (hAS ↥K hA6 S).1 U hEU hUtop
  have hIstN : Ist.subgroupOf K ≤ normalizer ((S : Subgroup ↥K) : Set ↥K) := fun k hk =>
    hUN (mem_subgroupOf.mpr (hIstX (mem_subgroupOf.mp hk)))
  have hkerI : ∀ x : ↥H, π x = 1 → Nat.Coprime 3 (orderOf (x : G)) := by
    intro x hx
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).mp hx
    rw [Subgroup.orderOf_coe]
    exact (primeComplementCore_coprime (G := H) 3).coprime_dvd_right
      (Subgroup.orderOf_dvd_natCard N hxN)
  obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hx₃o : orderOf (x₃ : G) = 3 := by rw [Subgroup.orderOf_coe, hx₃]
  have hx₃H : (x₃ : G) ∈ H := hIH x₃.2
  have hπx₃ : π ⟨x₃, hx₃H⟩ ≠ 1 := fun h => by
    have h1 := hkerI _ h
    rw [show ((⟨x₃, hx₃H⟩ : ↥H) : G) = x₃ from rfl, hx₃o] at h1
    norm_num at h1
  have hx₃Ist : π ⟨x₃, hx₃H⟩ ∈ Ist := ⟨⟨x₃, hx₃H⟩, mem_subgroupOf.mpr x₃.2, rfl⟩
  rcases hI₀'.shape with ha | ⟨hO2, hb⟩
  ·
    exfalso
    have hIeq : I = I₀ := oUpperTwo_eq_self_of_perfect ha.perfect
    have hperfH : ⁅I.subgroupOf H, I.subgroupOf H⁆ = I.subgroupOf H :=
      commutator_subgroupOf_eq_of_perfect hIH (hIeq ▸ ha.perfect)
    have hperfIst : ⁅Ist, Ist⁆ = Ist := by rw [hIst, ← map_commutator, hperfH]
    have hperfK : ⁅Ist.subgroupOf K, Ist.subgroupOf K⁆ = Ist.subgroupOf K :=
      commutator_subgroupOf_eq_of_perfect hIstK hperfIst
    haveI := (hAS ↥K hA6 S).2.1
    have hbot := eq_bot_of_perfect_of_le hIstN hperfK
    have h2 : (⟨π ⟨x₃, hx₃H⟩, hIstK hx₃Ist⟩ : ↥K) ∈ Ist.subgroupOf K := mem_subgroupOf.mpr hx₃Ist
    rw [hbot, mem_bot] at h2
    exact hπx₃ (congrArg Subtype.val h2)
  have hgen : ∀ g ∈ I₀, Odd (orderOf g) → g ^ 3 = 1 := by
    intro g hg hgo
    have hg3 : g ^ 3 ∈ pCoreOf 2 I₀ :=
      IsCZeroMember.cube_mem kFactSUThreeTwoShape_holds hb g (subset_closure ⟨hg, hgo⟩)
    obtain ⟨z, hz, hzg⟩ := CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.mp hg3
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I₀)) ⟨z, hz⟩
    have hk' : (g ^ 3) ^ 2 ^ k = 1 := by
      rw [← hzg]
      simpa using congrArg (fun w : ↥(CFSG.pCore 2 ↥I₀) => ((w : ↥I₀) : G)) hk
    have hd2 : orderOf (g ^ 3) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hodd3 : Odd (orderOf (g ^ 3)) := hgo.of_dvd_nat (orderOf_pow_dvd 3)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    have hj0 : j = 0 := by
      by_contra hj0
      rw [hj] at hodd3
      exact (Nat.not_even_iff_odd.mpr hodd3) ((Nat.even_pow' hj0).mpr even_two)
    rw [hj0, pow_zero] at hj
    exact orderOf_eq_one_iff.mp hj
  have hEmap : I ≤ (((S : Subgroup K).map K.subtype).comap π).map H.subtype := by
    refine (closure_le _).mpr fun g ⟨hg, hgo⟩ => ?_
    have hgH : g ∈ H := hI₀H hg
    have h1 : π ⟨g, hgH⟩ ∈ Ist := ⟨⟨g, hgH⟩, mem_subgroupOf.mpr (subset_closure ⟨hg, hgo⟩), rfl⟩
    have hk : (⟨π ⟨g, hgH⟩, hIstK h1⟩ : ↥K) ∈ normalizer ((S : Subgroup ↥K) : Set ↥K) :=
      hIstN (mem_subgroupOf.mpr h1)
    have hk3 : (⟨π ⟨g, hgH⟩, hIstK h1⟩ : ↥K) ^ 3 ^ 1 = 1 := by
      apply Subtype.ext
      rw [pow_one, coe_pow, coe_one, ← map_pow,
        show (⟨g, hgH⟩ : ↥H) ^ 3 = 1 from Subtype.ext (by simpa using hgen g hg hgo), map_one]
    exact ⟨⟨g, hgH⟩, ⟨_, mem_sylow_of_mem_normalizer S hk hk3, rfl⟩, rfl⟩
  have hIstE : Ist ≤ (S : Subgroup K).map K.subtype := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hEmap (mem_subgroupOf.mp hx)
    have : y = x := H.subtype_injective hyx
    rw [← this]
    exact hy
  have hSe := isElemAbelian_sylow_of_isAltTwoP hA6 S
  have hS3 : Nonempty (↥I₀ ⧸ CFSG.pCore 2 ↥I₀ ≃* Equiv.Perm (Fin 3)) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    obtain ⟨a, c, ha3, hc3, hac⟩ := TwelveNoSU.exists_cube_not_comm hb hne
    obtain ⟨x, hx3, n, hxn⟩ := exists_lift_cube a ha3
    obtain ⟨y, hy3, m, hym⟩ := exists_lift_cube c hc3
    set ρ := QuotientGroup.mk' (CFSG.pCore 2 ↥I₀) with hρ
    have hodd : ∀ z : ↥I₀, z ^ 3 = 1 → Odd (orderOf (z : G)) := fun z hz =>
      Odd.of_dvd_nat (by decide : Odd 3)
        (orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hz))
    have hxI : (x : G) ∈ I := subset_closure ⟨x.2, hodd x hx3⟩
    have hyI : (y : G) ∈ I := subset_closure ⟨y.2, hodd y hy3⟩
    have hxE : π ⟨x, hI₀H x.2⟩ ∈ (S : Subgroup K).map K.subtype :=
      hIstE ⟨⟨x, hI₀H x.2⟩, mem_subgroupOf.mpr hxI, rfl⟩
    have hyE : π ⟨y, hI₀H y.2⟩ ∈ (S : Subgroup K).map K.subtype :=
      hIstE ⟨⟨y, hI₀H y.2⟩, mem_subgroupOf.mpr hyI, rfl⟩
    obtain ⟨u, hu, hux⟩ := mem_map.mp hxE
    obtain ⟨v, hv, hvy⟩ := mem_map.mp hyE
    have huv : u * v = v * u := congrArg Subtype.val
      (isMulCommutative_iff.mp hSe.1.1 ⟨u, hu⟩ ⟨v, hv⟩)
    have hcomm : π ⟨x, hI₀H x.2⟩ * π ⟨y, hI₀H y.2⟩ = π ⟨y, hI₀H y.2⟩ * π ⟨x, hI₀H x.2⟩ := by
      rw [← hux, ← hvy, ← map_mul, ← map_mul, huv]
    set w : ↥I₀ := x * y * x⁻¹ * y⁻¹ with hw
    have hw1 : π ⟨w, hI₀H w.2⟩ = 1 := by
      have he : (⟨w, hI₀H w.2⟩ : ↥H) = ⟨x, hI₀H x.2⟩ * ⟨y, hI₀H y.2⟩ * ⟨x, hI₀H x.2⟩⁻¹ *
          ⟨y, hI₀H y.2⟩⁻¹ := Subtype.ext (by simp [hw])
      rw [he, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have hwc := hkerI _ hw1
    have hmemO : ∀ z : ↥I₀, z ^ 3 = 1 → ρ z ∈ oUpperTwo (⊤ : Subgroup (↥I₀ ⧸ CFSG.pCore 2 ↥I₀)) :=
      fun z hz => subset_closure ⟨mem_top _, Odd.of_dvd_nat (by decide : Odd 3)
        (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hz, map_one]))⟩
    have hρw : ρ w ∈ oUpperTwo (⊤ : Subgroup (↥I₀ ⧸ CFSG.pCore 2 ↥I₀)) := by
      rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact mul_mem (mul_mem (mul_mem (hmemO x hx3) (hmemO y hy3)) (inv_mem (hmemO x hx3)))
        (inv_mem (hmemO y hy3))
    have hρw3 : (ρ w) ^ 3 = 1 := IsSymThreeOrSUThreeTwo.cube kFactSUThreeTwoShape_holds hb _ hρw
    have hρw1 : ρ w = 1 := by
      have h1 : orderOf (ρ w) ∣ orderOf (w : G) := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_map_dvd _ _
      have h2 : orderOf (ρ w) = 1 :=
        ((Nat.Coprime.coprime_dvd_right h1 hwc).symm).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hρw3)
      exact orderOf_eq_one_iff.mp h2
    have hxy : ρ x * ρ y = ρ y * ρ x := by
      have h := hρw1
      rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv] at h
      calc ρ x * ρ y = (ρ x * ρ y * (ρ x)⁻¹ * (ρ y)⁻¹) * (ρ y * ρ x) := by group
        _ = ρ y * ρ x := by rw [h, one_mul]
    apply hac
    rw [← hxn, ← hym]
    exact (Commute.pow_pow hxy n m).eq
  refine ⟨hO2, hS3, hIstE, ?_⟩
  have hIstp : IsPGroup 3 Ist :=
    ((S.isPGroup').map K.subtype).to_le hIstE
  obtain ⟨j, hj⟩ := hIstp.exists_card_eq
  have h3d : 3 ∣ Nat.card Ist := by
    have ho : orderOf (π ⟨x₃, hx₃H⟩) = 3 := by
      have hd : orderOf (π ⟨x₃, hx₃H⟩) ∣ 3 := (orderOf_map_dvd _ _).trans (by
        rw [← Subgroup.orderOf_coe, show ((⟨x₃, hx₃H⟩ : ↥H) : G) = x₃ from rfl, hx₃o])
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hπx₃
      · exact h
    have h1 := orderOf_dvd_natCard (⟨_, hx₃Ist⟩ : ↥Ist)
    rwa [Subgroup.orderOf_mk, ho] at h1
  have hdvdI₀ : Nat.card Ist ∣ Nat.card I₀ := by
    refine (card_map_dvd _ π).trans ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe hIH).toEquiv]
    exact card_dvd_of_le hII₀
  obtain ⟨e⟩ := hS3
  obtain ⟨f, hf⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I₀)).exists_card_eq
  have hI₀card : Nat.card I₀ = 6 * 2 ^ f := by
    rw [card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥I₀), hf,
      Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [hj] at h3d hdvdI₀ ⊢
  rw [hI₀card] at hdvdI₀
  have hj1 : 1 ≤ j := by
    by_contra h0
    push Not at h0
    interval_cases j
    norm_num at h3d
  have hj2 : j ≤ 1 := by
    by_contra h2
    push Not at h2
    have h9 : 9 ∣ 6 * 2 ^ f := (pow_dvd_pow 3 h2).trans hdvdI₀
    have hc : Nat.Coprime 9 (2 ^ f) := Nat.Coprime.pow_right f (by norm_num)
    have h96 : 9 ∣ 6 := hc.dvd_of_dvd_mul_right h9
    norm_num at h96
  rw [show j = 1 by omega, pow_one]

theorem coe_mem_d1X0_of_mem_normalizer (hd : AGL81CfgData 3 P M H Q K) (hA6 : IsAltTwoP 3 K)
    (S : Sylow 3 ↥K)
    (hS : (S : Subgroup K).map K.subtype =
      (Q.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ⊓ K)
    {b : G} (hb : TwelveB M H Q K b) {k : ↥K}
    (hk : k ∈ normalizer ((S : Subgroup ↥K) : Set ↥K)) :
    (k : H ⧸ primeComplementCore (G := H) 3) ∈ d1X0 3 M H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  obtain ⟨hbHM, hbX, hob, -, hQb⟩ := hb
  obtain ⟨hAX, hAel, hA9⟩ := d1LiftX_facts_cfg hd hA6
  set A := d1LiftX 3 H Q K with hA
  have hAQ : A ≤ Q := d1LiftX_le 3 H Q K
  have hAH : A ≤ H := hAQ.trans hd.le_H
  have hAM : A ≤ M := hAQ.trans hd.base.1
  have hbA : b ∉ A := fun h => by
    have h1 : b ∈ A ⊓ d1PlusCore 3 H K := ⟨h, hbX⟩
    rw [hAX, mem_bot] at h1
    rw [h1, orderOf_one] at hob
    exact absurd hob (by norm_num)
  have hcomm : ∀ e ∈ A, e * b = b * e := fun e he =>
    mem_centralizer_singleton_iff.mp (hQb (hAQ he))
  have hb3 : b ^ 3 = 1 := by rw [← hob]; exact pow_orderOf_eq_one b
  obtain ⟨hEel, hE27⟩ := CFSG.Goldschmidt.Sec82.isElemAbelian_sup_zpowers Nat.prime_three
    (by rw [hA9]; norm_num) hAel.2 hb3 hbA hcomm
  set E := A ⊔ zpowers b with hE
  have hEH : E ≤ H := sup_le hAH (zpowers_le.mpr hbHM.1)
  have hEM : E ≤ M := sup_le hAM (zpowers_le.mpr hbHM.2)
  have hE3 : IsPGroup 3 E := IsPGroup.of_card hE27
  have hwc := Hyp111.weakCore_le_d1X0_of_escape he hEH hEM hE3
  set N := primeComplementCore (G := H) 3 with hN
  set π := QuotientGroup.mk' N with hπ
  set Eb := (E.subgroupOf H).map π with hEb
  set Ab := (A.subgroupOf H).map π with hAb
  have hAbS : Ab = (S : Subgroup K).map K.subtype := by rw [hS, hAb, hA, map_d1LiftX]
  have hAbE : Ab ≤ Eb := map_mono fun x hx => mem_subgroupOf.mpr (le_sup_left (a := A)
    (mem_subgroupOf.mp hx))
  have hO : (3 : ℕ).Coprime (Nat.card N) := primeComplementCore_coprime (G := H) 3
  have hrA : 2 ≤ CFSG.Open.pRank 3 Ab := by
    rw [hAb, pRank_map_mk_eq_pRank_map_subtype Nat.prime_three N hO, map_subgroupOf_eq_of_le hAH]
    exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl hAel (by rw [hA9]; norm_num)
  have hrE : 3 ≤ CFSG.Open.pRank 3 Eb := by
    rw [hEb, pRank_map_mk_eq_pRank_map_subtype Nat.prime_three N hO, map_subgroupOf_eq_of_le hEH]
    exact CFSG.SectionRank.le_pRank (by norm_num) le_rfl hEel hE27
  have hEbC : Eb ≤ Ab ⊔ (Eb ⊓ centralizer (Ab : Set (H ⧸ N))) := by
    intro x hx
    refine mem_sup_right (mem_inf.mpr ⟨hx, mem_centralizer_iff.mpr fun y hy => ?_⟩)
    obtain ⟨x', hx', rfl⟩ := mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_map.mp (hAbE hy)
    have hxy : x' * y' = y' * x' := by
      have h := isMulCommutative_iff.mp hEel.1 ⟨_, mem_subgroupOf.mp hx'⟩ ⟨_, mem_subgroupOf.mp hy'⟩
      exact Subtype.ext (by simpa using congrArg Subtype.val h)
    rw [← map_mul, ← map_mul, hxy]
  have hrC : 3 ≤ CFSG.Open.pRank 3 (Ab ⊔ (Eb ⊓ centralizer (Ab : Set (H ⧸ N)))) :=
    hrE.trans (CFSG.SectionRank.pRank_mono (by norm_num) hEbC)
  have hNw := CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore 3 hAbE hrA hrC
  have hk' : (k : H ⧸ N) ∈ normalizer (Ab : Set (H ⧸ N)) := by
    rw [hAbS]
    exact le_normalizer_map K.subtype ⟨k, hk, rfl⟩
  exact hwc (hNw hk')

theorem exists_two_element_moving (hAS : KFactTwelveNotLeAltSix) (hd : AGL81CfgData 3 P M H Q K)
    (hA6 : IsAltTwoP 3 K) (S : Sylow 3 ↥K)
    (hS : (S : Subgroup K).map K.subtype =
      (Q.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ⊓ K)
    {b : G} (hb : TwelveB M H Q K b) :
    ∃ t : ↥H, (t : G) ∈ M ∧ QuotientGroup.mk' (primeComplementCore (G := H) 3) t ∈ K ∧
      (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
      ∀ Z : Subgroup (H ⧸ primeComplementCore (G := H) 3), Z ≤ (S : Subgroup K).map K.subtype →
        Nat.card Z = 3 → QuotientGroup.mk' (primeComplementCore (G := H) 3) t ∉
          normalizer (Z : Set (H ⧸ primeComplementCore (G := H) 3)) := by
  set N := primeComplementCore (G := H) 3 with hN
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨t₀, ht₀N, ⟨k₀, hk₀⟩, hmove⟩ := (hAS ↥K hA6 S).2.2
  have hX0 := coe_mem_d1X0_of_mem_normalizer hd hA6 S hS hb ht₀N
  obtain ⟨h₀, hh₀, hh₀t⟩ := mem_map.mp hX0
  have hh₀M : (h₀ : G) ∈ M := (mem_inf.mp (mem_subgroupOf.mp hh₀)).2
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h₀).ne'
  have hπt : π (h₀ ^ m) = (t₀ : H ⧸ N) ^ m := by rw [map_pow, hh₀t]
  refine ⟨h₀ ^ m, ?_, ?_, ⟨a, ?_⟩, ?_⟩
  · rw [coe_pow]
    exact M.pow_mem hh₀M m
  · rw [hπt]
    exact K.pow_mem t₀.2 m
  · rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  · intro Z hZ hZ3 hnorm
    rw [hπt] at hnorm
    have ht₀o : orderOf (t₀ : H ⧸ N) ∣ 2 ^ k₀ := by
      rw [← Subgroup.orderOf_coe] at *
      exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk₀)
    have hcop : Nat.Coprime m (orderOf (t₀ : H ⧸ N)) :=
      Nat.Coprime.coprime_dvd_right ht₀o (Nat.Coprime.pow_right k₀ (Nat.coprime_two_right.mpr hm))
    obtain ⟨m', hm'⟩ := exists_pow_eq_self_of_coprime hcop
    have ht₀Z : (t₀ : H ⧸ N) ∈ normalizer (Z : Set (H ⧸ N)) := by
      rw [← hm']
      exact pow_mem hnorm m'
    have hZK : Z ≤ K := hZ.trans (map_subtype_le _)
    set Z' : Subgroup ↥K := Z.subgroupOf K with hZ'
    have hZ'S : Z' ≤ (S : Subgroup ↥K) := by
      intro z hz
      obtain ⟨s, hs, hsz⟩ := mem_map.mp (hZ (mem_subgroupOf.mp hz))
      rwa [← Subtype.ext hsz]
    have hZ'3 : Nat.card Z' = 3 := by
      rw [hZ', Nat.card_congr (subgroupOfEquivOfLe hZK).toEquiv, hZ3]
    have hmap : Z'.map (MulAut.conj t₀).toMonoidHom = Z' := by
      apply mem_normalizer_iff_map_conj_eq.mp
      rw [mem_normalizer_iff]
      intro z
      rw [hZ', mem_subgroupOf, mem_subgroupOf]
      simpa using (mem_normalizer_iff.mp ht₀Z (z : H ⧸ N))
    exact hmove Z' hZ'S hZ'3 hmap

theorem normal_of_cfg (hd : AGL81CfgData 3 P M H Q K) (hA6 : IsAltTwoP 3 K) : K.Normal := by
  obtain ⟨H₁, R₁, he⟩ := hd.escape
  have hKbot : d1KBar 3 M H ≠ ⊥ := by
    rw [← hd.kbar]
    intro h
    obtain ⟨e⟩ := hA6
    have h1 : Nat.card ↥K = Nat.card (alternatingGroup (Fin (2 * 3))) := Nat.card_congr e.toEquiv
    rw [h, card_bot, nat_card_alternatingGroup, Nat.card_fin] at h1
    norm_num at h1
  have := Hyp111.d1KBar_normal_of_escape he hd.base hd.le_H hKbot
  rw [← hd.kbar] at this
  exact this

theorem oUpperTwo_map_conj_le [K.Normal] {I₀ : Subgroup G} (hIK : oUpperTwo I₀ ≤ hyp111Pre 3 H K)
    {g : G} (hg : g ∈ H) : oUpperTwo (I₀.map (MulAut.conj g).toMonoidHom) ≤ hyp111Pre 3 H K := by
  refine (closure_le _).mpr fun y ⟨hy, hyo⟩ => ?_
  obtain ⟨z, hz, rfl⟩ := mem_map.mp hy
  have hzo : Odd (orderOf z) := by
    have hsc : SemiconjBy g z (g * z * g⁻¹) := by rw [SemiconjBy, inv_mul_cancel_right]
    have h1 : Odd (orderOf (g * z * g⁻¹)) := by simpa [MulAut.conj_apply] using hyo
    rwa [← hsc.orderOf_eq] at h1
  have hzK : z ∈ hyp111Pre 3 H K := hIK (subset_closure ⟨hz, hzo⟩)
  exact (mem_normalizer_iff.mp (mem_normalizer_hyp111Pre_d1PlusCore hg).1 z).mp hzK

theorem commutator_mem_pCoreOf_of_kPart (hAS : KFactTwelveNotLeAltSix)
    (hd : AGL81CfgData 3 P M H Q K) (hA6 : IsAltTwoP 3 K) (S : Sylow 3 ↥K)
    (hS : (S : Subgroup K).map K.subtype =
      (Q.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ⊓ K)
    {b : G} (hbH : b ∈ H) (hbX : b ∈ d1PlusCore 3 H K) {L : Subgroup G} (hLM : L ≤ M)
    (hbL : b ∈ normalizer (L : Set G))
    (h3 : ∀ I ∈ cZero (H ⊓ L), 3 ∣ Nat.card (oUpperTwo I)) {I₀ : Subgroup G}
    (hI₀ : I₀ ∈ cZero (H ⊓ L)) (hIK : oUpperTwo I₀ ≤ hyp111Pre 3 H K) :
    ∀ s ∈ I₀, b * s * b⁻¹ * s⁻¹ ∈ pCoreOf 2 I₀ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := normal_of_cfg hd hA6
  have hZ := center_eq_bot_of_isAltTwoP hA6
  set D := H ⊓ L with hD
  have hDM : D ≤ M := inf_le_right.trans hLM
  have hbD : b ∈ normalizer (D : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have h1 := mem_normalizer_iff.mp (le_normalizer hbH : b ∈ normalizer (H : Set G)) x
    have h2 := mem_normalizer_iff.mp hbL x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  have hI₀' : IsCZeroMember D I₀ := hI₀
  set I₀b := I₀.map (MulAut.conj b).toMonoidHom with hI₀b
  have hI₀b' : IsCZeroMember D I₀b := hI₀'.map_conj hbD
  have hIKb : oUpperTwo I₀b ≤ hyp111Pre 3 H K := oUpperTwo_map_conj_le hIK hbH
  obtain ⟨hO2, ⟨e⟩, -, -⟩ := kPart_shape hAS hd hA6 S hS hLM hI₀ hIK (h3 I₀ hI₀)
  obtain ⟨hO2b, ⟨eb⟩, -, -⟩ := kPart_shape hAS hd hA6 S hS hLM hI₀b' hIKb (h3 I₀b hI₀b')
  obtain ⟨g₀, hg₀⟩ := exists_prime_orderOf_dvd_card' 3 (h3 I₀ hI₀)
  set g : G := (g₀ : G) with hgdef
  have hgo : orderOf g = 3 := by rw [hgdef, orderOf_coe, hg₀]
  have hgI : g ∈ oUpperTwo I₀ := g₀.2
  have hgI₀ : g ∈ I₀ := CFSG.AGLEmbedding.oUpperTwo_le_self I₀ hgI
  have hgK : g ∈ hyp111Pre 3 H K := hIK hgI
  have hgb : g ∈ I₀b := by
    have hy : b * g * b⁻¹ ∈ I₀b := ⟨g, hgI₀, by simp [MulAut.conj_apply]⟩
    have hc : Nat.Coprime 3 (orderOf (b * g⁻¹ * b⁻¹ * g⁻¹⁻¹)) :=
      coprime_orderOf_commutator_of_mem (inv_mem hgK) hbX
    refine mem_of_isSubnormal_of_mul hI₀b'.subnormal (hI₀'.le hgI₀) (k := 1)
      (by rw [pow_one, ← hgo, pow_orderOf_eq_one]) hy hc ?_
    group
  set Pb := barM M D with hPb
  set ĝ : ↥Pb ⧸ CFSG.pCore 2 ↥Pb :=
    QuotientGroup.mk' (CFSG.pCore 2 ↥Pb) (barMHomSub hDM ⟨g, hI₀'.le hgI₀⟩) with hĝ
  have hmemhat : ∀ {X : Subgroup G} (hXD : X ≤ D), g ∈ X → ĝ ∈ hatOf Pb (barM M X) := by
    intro X hXD hgX
    refine mem_map.mpr ⟨_, ?_, rfl⟩
    rw [subgroupOf_barM_eq_map hDM hXD]
    exact mem_map.mpr ⟨⟨g, hXD hgX⟩, mem_subgroupOf.mpr hgX, rfl⟩
  have hĝo : orderOf ĝ = 3 := by
    have hd3 : orderOf ĝ ∣ 3 := (orderOf_map_dvd _ _).trans ((orderOf_map_dvd _ _).trans (by
      rw [← Subgroup.orderOf_coe, show ((⟨g, hI₀'.le hgI₀⟩ : ↥D) : G) = g from rfl, hgo]))
    rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h | h
    · exfalso
      rw [orderOf_eq_one_iff, hĝ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        barMHomSub_mem_pCore_iff] at h
      obtain ⟨k, hk⟩ := (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 D) ⟨g, h⟩
      have hk' : g ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h32 : 3 ∣ 2 ^ k := hgo ▸ orderOf_dvd_of_pow_eq_one hk'
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h32) (by norm_num)
    · exact h
  obtain ⟨eX⟩ := nonempty_hatOf_mulEquiv hDM hI₀'.le (inf_pCoreOf_eq_of_isSubnormal hI₀'.subnormal)
  obtain ⟨eW⟩ := nonempty_hatOf_mulEquiv hDM hI₀b'.le
    (inf_pCoreOf_eq_of_isSubnormal hI₀b'.subnormal)
  have hhat : hatOf Pb (barM M I₀b) = hatOf Pb (barM M I₀) :=
    (eq_of_isSubnormal_symThree (V := ↥Pb ⧸ CFSG.pCore 2 ↥Pb)
      (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot)
      (isSubnormal_hatOf hDM hI₀'.subnormal) (isSubnormal_hatOf hDM hI₀b'.subnormal)
      (eX.trans e) (eW.trans eb)
      (zpowers_le.mpr (hmemhat hI₀'.le hgI₀)) (zpowers_le.mpr (hmemhat hI₀b'.le hgb))
      (by rw [Nat.card_zpowers, hĝo])).symm
  have hle : I₀b ≤ I₀ := by
    have h1 := le_sup_pCoreOf_of_hatOf_eq hDM hI₀b'.le hI₀'.le hhat
    rwa [← hO2, sup_eq_left.mpr (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 I₀)] at h1
  have heq : I₀b = I₀ := eq_of_le_of_card_ge hle (by
    rw [hI₀b, card_map_of_injective (MulAut.conj b).injective])
  have hI₀H : I₀ ≤ H := hI₀'.le.trans inf_le_left
  have hX : ∀ w : ↥I₀, (w : G) ∈ d1PlusCore 3 H K → w ∈ CFSG.pCore 2 ↥I₀ :=
    mem_pCore_of_symThree e (fun x hx => (mem_normalizer_hyp111Pre_d1PlusCore (hI₀H hx)).2)
      fun y hy hyX k hyk => eq_one_of_mem_hyp111Pre_d1PlusCore hZ
        (hIK (subset_closure ⟨hy, Odd.of_dvd_nat (Odd.pow (by decide : Odd 3))
          (orderOf_dvd_of_pow_eq_one hyk)⟩)) hyX hyk
  intro s hs
  have hbs : b * s * b⁻¹ ∈ I₀ := heq ▸ (⟨s, hs, by simp [MulAut.conj_apply]⟩ : b * s * b⁻¹ ∈ I₀b)
  have hw : b * s * b⁻¹ * s⁻¹ ∈ I₀ := I₀.mul_mem hbs (I₀.inv_mem hs)
  have hwX : b * s * b⁻¹ * s⁻¹ ∈ d1PlusCore 3 H K := by
    have h1 : s * b⁻¹ * s⁻¹ ∈ d1PlusCore 3 H K :=
      (mem_normalizer_iff.mp (mem_normalizer_hyp111Pre_d1PlusCore (hI₀H hs)).2 b⁻¹).mp
        (inv_mem hbX)
    have h2 := (d1PlusCore 3 H K).mul_mem hbX h1
    simpa [mul_assoc] using h2
  exact CFSG.HardMathSupport.Cooperstein.Proving.mem_pCoreOf_iff.mpr ⟨⟨_, hw⟩, hX ⟨_, hw⟩ hwX, rfl⟩

theorem commutator_jZero_le_of_forall_kPart (hAS : KFactTwelveNotLeAltSix)
    (hd : AGL81CfgData 3 P M H Q K) (hA6 : IsAltTwoP 3 K) (S : Sylow 3 ↥K)
    (hS : (S : Subgroup K).map K.subtype =
      (Q.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ⊓ K)
    {b : G} (hbH : b ∈ H) (hbX : b ∈ d1PlusCore 3 H K) {L : Subgroup G} (hLM : L ≤ M)
    (hbL : b ∈ normalizer (L : Set G))
    (h3 : ∀ I ∈ cZero (H ⊓ L), 3 ∣ Nat.card (oUpperTwo I))
    (hall : ∀ I ∈ cZero (H ⊓ L), oUpperTwo I ≤ hyp111Pre 3 H K) :
    ⁅jZero H L, zpowers b⁆ ≤ pCoreOf 2 (jZero H L) := by
  set J := jZero H L with hJ
  have hbD : b ∈ normalizer ((H ⊓ L : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    have h1 := mem_normalizer_iff.mp (le_normalizer hbH : b ∈ normalizer (H : Set G)) x
    have h2 := mem_normalizer_iff.mp hbL x
    exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
  have hbJ : b ∈ normalizer (J : Set G) := le_normalizer_jZero H L hbD
  have hbO : b ∈ normalizer (pCoreOf 2 J : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J hbJ
  have hJO : J ≤ normalizer (pCoreOf 2 J : Set G) := localGroup_le_normalizer_pCoreOf 2 J
  let T : Subgroup G :=
    { carrier := {x | x ∈ J ∧ b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 J}
      mul_mem' := by
        rintro x y ⟨hx, hxO⟩ ⟨hy, hyO⟩
        refine ⟨J.mul_mem hx hy, ?_⟩
        have h1 := (mem_normalizer_iff.mp (hJO hx) _).mp hyO
        have he : b * (x * y) * b⁻¹ * (x * y)⁻¹ =
            (b * x * b⁻¹ * x⁻¹) * (x * (b * y * b⁻¹ * y⁻¹) * x⁻¹) := by group
        rw [he]
        exact mul_mem hxO h1
      one_mem' := ⟨J.one_mem, by simp⟩
      inv_mem' := by
        rintro x ⟨hx, hxO⟩
        refine ⟨J.inv_mem hx, ?_⟩
        have h1 := (mem_normalizer_iff.mp (hJO (J.inv_mem hx)) _).mp (inv_mem hxO)
        have he : b * x⁻¹ * b⁻¹ * x⁻¹⁻¹ = x⁻¹ * (b * x * b⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [he]
        exact h1 }
  have hJT : J ≤ T := by
    refine iSup₂_le fun I hI => ?_
    have hI' : IsCZeroMember (H ⊓ L) I := hI
    have hIJ : I ≤ J := hI'.le_jZero
    have hsub : IsSubnormal I J := by
      have h := IsSubnormal.inf_of_le hI'.subnormal (jZero_le H L)
      rwa [inf_eq_left.mpr hIJ] at h
    have hOO := CFSG.HardMathSupport.Cooperstein.Proving.pCoreOf_le_pCoreOf_of_isSubnormal 2 hsub
    intro x hx
    exact ⟨hIJ hx, hOO (commutator_mem_pCoreOf_of_kPart hAS hd hA6 S hS hbH hbX hLM hbL h3 hI
      (hall I hI) x hx)⟩
  exact commutator_zpowers_le_of_forall hbJ hbO fun x hx => (hJT hx).2

theorem exists_xPart_of_not_le (hAS : KFactTwelveNotLeAltSix) (h1013 : AGL81TenThirteenAt G)
    (h3σ : 3 ∈ rankThreeSigmaA G) (hS' : Setting G) (hd : AGL81CfgData 3 P M H Q K)
    (hA6 : IsAltTwoP 3 K) (S : Sylow 3 ↥K)
    (hS : (S : Subgroup K).map K.subtype =
      (Q.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) ⊓ K)
    {b : G} (hbH : b ∈ H) (hbX : b ∈ d1PlusCore 3 H K) {L : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hbL : b ∈ normalizer (L : Set G))
    (h3 : ∀ I ∈ cZero (H ⊓ L), 3 ∣ Nat.card (oUpperTwo I))
    (hJ : ¬ ⁅jZero H L, zpowers b⁆ ≤ pCoreOf 2 (jZero H L)) :
    ∃ I₁ ∈ cZero (H ⊓ L), oUpperTwo I₁ ≤ d1PlusCore 3 H K := by
  by_contra hno
  push Not at hno
  refine hJ (commutator_jZero_le_of_forall_kPart hAS hd hA6 S hS hbH hbX hL.le hbL h3
    fun I hI => ?_)
  rcases h1013 hS' 3 P M H Q K h3σ hd L hL I hI with hX | ⟨-, -, hK⟩
  · exact absurd hX (hno I hI)
  · exact hK

end Shape

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
