module

public import CFSG.Open.RankThreeDefs
import CFSG.GroupTheory.ExtraspecialThreeFive
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KFAutDefs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerNaturality.LayerNaturality
import CFSG.RankThree.PartTwo.Sec8.Hering418L2

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem ker_normalizerMonoidHom_comp_inclusion {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    (K.normalizerMonoidHom.comp (Subgroup.inclusion hHK)).ker =
      (H ⊓ Subgroup.centralizer (K : Set G) : Subgroup G).subgroupOf H := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx
    refine ⟨x.2, ?_⟩
    intro y hy
    have hxy := congrArg (fun σ : MulAut ↥K => ((σ ⟨y, hy⟩ : ↥K) : G)) hx
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply,
      Subgroup.coe_one, Subgroup.coe_inclusion] at hxy
    have hcommute : (x : G) * y = y * (x : G) := by
      calc (x : G) * y = ((x : G) * y * (x : G)⁻¹) * (x : G) := by group
        _ = y * (x : G) := by rw [hxy]
    exact hcommute.symm
  · rintro ⟨-, hx⟩
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply,
      Subgroup.coe_one]
    have hy : y * (x : G) = (x : G) * y := hx y y.2
    calc (x : G) * (y : G) * (x : G)⁻¹ = ((x : G) * y) * (x : G)⁻¹ := rfl
      _ = (y * (x : G)) * (x : G)⁻¹ := by rw [← hy]
      _ = (y : G) := by group

theorem card_le_three_mul_card_inf_centralizer_of_le_normalizer {p : ℕ} [Fact p.Prime]
    {H K : Subgroup G} (hK : Nat.card K = p)
    (hHK : H ≤ Subgroup.normalizer (K : Set G))
    (hexp : ∀ x : ↥H, x ^ 3 = 1) :
    Nat.card H ≤ 3 * Nat.card (H ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by
  classical
  haveI : IsCyclic ↥K := isCyclic_of_prime_card hK
  have hAutCyc : IsCyclic (MulAut ↥K) := by
    let e := IsCyclic.mulAutMulEquiv (G := ↥K)
    rw [hK] at e
    haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime (Fact.out : Nat.Prime p)
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  let φ : ↥H →* MulAut ↥K :=
    K.normalizerMonoidHom.comp (Subgroup.inclusion hHK)
  have hker : φ.ker = (H ⊓ Subgroup.centralizer (K : Set G) : Subgroup G).subgroupOf H :=
    ker_normalizerMonoidHom_comp_inclusion hHK
  have hrange : Nat.card φ.range ≤ 3 := by
    haveI : IsCyclic (MulAut ↥K) := hAutCyc
    have hcyc : IsCyclic φ.range := Subgroup.isCyclic _
    have hexp3 : Monoid.exponent φ.range ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one (fun y => by
        obtain ⟨x, hx⟩ := y.2
        have hy : (y : MulAut ↥K) = φ x := hx.symm
        apply Subtype.ext
        change ((y : MulAut ↥K)) ^ 3 = 1
        rw [hy, ← map_pow, hexp x, map_one])
    have hle := Nat.le_of_dvd (by norm_num : 0 < 3) hexp3
    rwa [IsCyclic.exponent_eq_card] at hle
  have hcard : Nat.card ↥H = Nat.card φ.range * Nat.card φ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hkercard : Nat.card φ.ker =
      Nat.card (H ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card H = Nat.card φ.range * Nat.card φ.ker := hcard
    _ = Nat.card φ.range * Nat.card
          (H ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by rw [hkercard]
    _ ≤ 3 * Nat.card (H ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :=
        Nat.mul_le_mul_right _ hrange

private theorem le_normalizer_centralizer_and_layer {P₀ Q : Subgroup G}
    (hQP₀ : Q ≤ Subgroup.normalizer (P₀ : Set G)) :
    Q ≤ Subgroup.normalizer (Subgroup.centralizer (P₀ : Set G) : Set G) ∧
      Q ≤ Subgroup.normalizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) := by
  let C : Subgroup G := Subgroup.centralizer (P₀ : Set G)
  let L : Subgroup G := CFSG.Open.rankThreeLayer C
  have hC : Q ≤ Subgroup.normalizer (C : Set G) :=
    hQP₀.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup P₀)
  have hL : Q ≤ Subgroup.normalizer (L : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hqC : q ∈ Subgroup.normalizer (C : Set G) := hC hq
    have hmapC : C.map (MulAut.conj q).toMonoidHom = C :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hqC
    have h := CFSG.LocalAnalysis.RankThreeUC.ProofSupport.LayerNaturality.map_layer
      (MulAut.conj q) C
    rw [hmapC] at h
    exact h
  exact ⟨by simpa [C] using hC, by simpa [L, C] using hL⟩

private theorem card_le_three_inf_centralizer
    {P₀ Q : Subgroup G}
    (hF2 : CFSG.Open.pRank 3 (Subgroup.centralizer (P₀ : Set G) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≤ 1)
    (hexp : ∀ x : ↥Q, x ^ 3 = 1) :
    Nat.card ↥((Q ⊓ Subgroup.centralizer (P₀ : Set G)) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) :
        Subgroup G) ≤ 3 := by
  refine KFAut.card_le_three_of_exponent_three_of_pRank_le_one (fun x hx => ?_)
    ((CFSG.SectionRank.pRank_mono (by norm_num) (inf_le_inf_right _ inf_le_right)).trans hF2)
  simpa using congrArg Subtype.val (hexp ⟨x, hx.1.1⟩)

private theorem card_eq_three_inf_centralizer_of_ne_bot
    {P₀ Q : Subgroup G}
    (hF2 : CFSG.Open.pRank 3 (Subgroup.centralizer (P₀ : Set G) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≤ 1)
    (hcard : Nat.card ↥Q = 3 ^ 5) (hexp : ∀ x : ↥Q, x ^ 3 = 1)
    (hRne : ((Q ⊓ Subgroup.centralizer (P₀ : Set G)) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≠ ⊥) :
    Nat.card ↥((Q ⊓ Subgroup.centralizer (P₀ : Set G)) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G) :
        Subgroup G) = 3 := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P₀ : Set G)
  let L : Subgroup G := CFSG.Open.rankThreeLayer C
  let R : Subgroup G := (Q ⊓ C) ⊓ Subgroup.centralizer (L : Set G)
  have hRne' : R ≠ ⊥ := by simpa [R, C, L] using hRne
  have h : Nat.card R = 3 := by
    have hRcardle : Nat.card ↥R ≤ 3 := by
      simpa [R, C, L] using card_le_three_inf_centralizer (P₀ := P₀) (Q := Q) hF2 hexp
    have hR3 : IsPGroup 3 R := (IsPGroup.of_card hcard).to_le (inf_le_left.trans inf_le_left)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases IsPGroup.card_eq_or_dvd (G := ↥R) hR3 with h1 | h3
    · exact absurd (Subgroup.eq_bot_of_card_eq R (by simpa using h1)) hRne'
    · obtain ⟨k, hk⟩ := h3
      have hpos : 0 < Nat.card ↥R := Nat.card_pos
      omega
  simpa [R, C, L] using h

private theorem isElemAbelian_range_of_commutator_le_ker {H M : Type*} [Group H] [Group M]
    (φ : H →* M) (hcomm : commutator H ≤ φ.ker) (hexp : ∀ x : H, x ^ 3 = 1) :
    CFSG.Open.IsElemAbelian 3 φ.range := by
  classical
  haveI : IsMulCommutative (H ⧸ φ.ker) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr hcomm
  have hrangeComm : IsMulCommutative φ.range := by
    rw [isMulCommutative_iff]
    intro a b
    let e := QuotientGroup.quotientKerEquivRange φ
    have h : e.symm a * e.symm b = e.symm b * e.symm a :=
      mul_comm' (e.symm a) (e.symm b)
    have h' := congrArg (fun z => e z) h
    simpa using h'
  have hrangeExp : ∀ y ∈ φ.range, y ^ 3 = 1 := by
    rintro y ⟨x, rfl⟩
    change (φ x) ^ 3 = 1
    rw [← map_pow, hexp x, map_one]
  exact ⟨hrangeComm, hrangeExp⟩

private theorem card_range_ge_27_of_ker_card {H M : Type*} [Group H] [Group M]
    (φ : H →* M) (hker : Nat.card φ.ker = 3) (hH : 81 ≤ Nat.card H) :
    27 ≤ Nat.card φ.range := by
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hker] at hmul
  omega

private theorem commutator_le_ker_of_eq_center {Q₁ Q R L : Subgroup G}
    (φ : ↥Q₁ →* MulAut ↥L) (hker : φ.ker = R.subgroupOf Q₁)
    (hQ₁Q : Q₁ ≤ Q) (hcenter : R.subgroupOf Q = Subgroup.center ↥Q)
    (hcomm : commutator ↥Q ≤ Subgroup.center ↥Q) :
    commutator ↥Q₁ ≤ φ.ker := by
  rw [hker, _root_.commutator_def, Subgroup.commutator_le]
  intro x _ y _
  have hmem : (Subgroup.inclusion hQ₁Q) ⁅x, y⁆ ∈ commutator ↥Q := by
    rw [_root_.commutator_def, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hcommQR : commutator ↥Q ≤ R.subgroupOf Q := by
    rw [hcenter]
    exact hcomm
  have hmemR := hcommQR hmem
  rw [Subgroup.mem_subgroupOf] at hmemR ⊢
  rwa [Subgroup.coe_inclusion] at hmemR

private theorem subgroupOf_inf_centralizers_eq_center
    {P₀ Q : Subgroup G}
    (hF2 : CFSG.Open.pRank 3 (Subgroup.centralizer (P₀ : Set G) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≤ 1)
    (hQP₀ : Q ≤ Subgroup.normalizer (P₀ : Set G))
    (hcard : Nat.card ↥Q = 3 ^ 5) (hexp : ∀ x : ↥Q, x ^ 3 = 1)
    (hZ : Nat.card (Subgroup.center ↥Q) = 3)
    (hRne : ((Q ⊓ Subgroup.centralizer (P₀ : Set G)) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≠ ⊥) :
    (((Q ⊓ Subgroup.centralizer (P₀ : Set G)) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)).subgroupOf Q) =
      Subgroup.center ↥Q := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P₀ : Set G)
  let L : Subgroup G := CFSG.Open.rankThreeLayer C
  let R : Subgroup G := (Q ⊓ C) ⊓ Subgroup.centralizer (L : Set G)
  have hRne' : R ≠ ⊥ := by simpa [R, C, L] using hRne
  have h : R.subgroupOf Q = Subgroup.center ↥Q := by
    obtain ⟨hPC, hPL⟩ := le_normalizer_centralizer_and_layer hQP₀
    have hRcard : Nat.card ↥R = 3 :=
      card_eq_three_inf_centralizer_of_ne_bot (P₀ := P₀) (Q := Q) hF2 hcard hexp hRne'
    have hRQ : R ≤ Q := inf_le_left.trans inf_le_left
    have hQNR : Q ≤ Subgroup.normalizer (R : Set G) := by
      have hQ1 : Q ≤ Subgroup.normalizer (Q ⊓ C : Subgroup G) :=
        (le_inf Subgroup.le_normalizer hPC).trans
          (Subgroup.inf_normalizer_le_normalizer_inf)
      have hQCL : Q ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
        hPL.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup L)
      exact (le_inf hQ1 hQCL).trans (Subgroup.inf_normalizer_le_normalizer_inf)
    have hRnormal : (R.subgroupOf Q).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
      rwa [inf_eq_left.mpr hRQ]
    haveI hRQnormal : (R.subgroupOf Q).Normal := hRnormal
    have hRsubcard : Nat.card (R.subgroupOf Q) = 3 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRQ).toEquiv).trans hRcard
    haveI : Fact (IsPGroup 3 ↥Q) := ⟨IsPGroup.of_card hcard⟩
    have hlecent : R.subgroupOf Q ≤ Subgroup.center ↥Q :=
      CFSG.normal_subgroup_card_eq_prime_le_center (p := 3) (R.subgroupOf Q) hRsubcard
    exact Subgroup.eq_of_le_of_card_ge hlecent (by rw [hRsubcard, hZ])
  simpa [R, C, L] using h

private theorem exists_elemAbelian_27_of_inf_eq_bot {p : ℕ} [Fact p.Prime]
    {P₀ Q : Subgroup G} (hP₀ : Nat.card P₀ = p)
    (hQP₀ : Q ≤ Subgroup.normalizer (P₀ : Set G))
    (hcard : Nat.card ↥Q = 3 ^ 5) (hexp : ∀ x : ↥Q, x ^ 3 = 1)
    (hZ : Nat.card (Subgroup.center ↥Q) = 3)
    (hcomm : commutator ↥Q ≤ Subgroup.center ↥Q)
    (hRbot : ((Q ⊓ Subgroup.centralizer (P₀ : Set G)) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) = ⊥) :
    ∃ B : Subgroup (MulAut ↥(CFSG.Open.rankThreeLayer
        (Subgroup.centralizer (P₀ : Set G)))),
      CFSG.Open.IsElemAbelian 3 B ∧ 27 ≤ Nat.card B := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P₀ : Set G)
  let L : Subgroup G := CFSG.Open.rankThreeLayer C
  let Q₁ : Subgroup G := Q ⊓ C
  let R : Subgroup G := Q₁ ⊓ Subgroup.centralizer (L : Set G)
  have hRbot' : R = ⊥ := by simpa [R, Q₁, C, L] using hRbot
  obtain ⟨hPC, hPL⟩ := le_normalizer_centralizer_and_layer hQP₀
  have hle : Nat.card Q ≤ 3 * Nat.card Q₁ :=
    card_le_three_mul_card_inf_centralizer_of_le_normalizer hP₀ hQP₀ hexp
  obtain ⟨E, hER, hEea, hEcard⟩ :=
    CFSG.GroupTheory.ExtraspecialThreeFive.exists_elemAbelian_27_le_inf
      (R := Q) (N := C) hcard hexp hZ hcomm (by simpa [Q₁] using hle)
  have hEQ₁ : E ≤ Q₁ := by simpa [Q₁] using hER
  let φ : ↥Q₁ →* MulAut ↥L :=
    L.normalizerMonoidHom.comp (Subgroup.inclusion (inf_le_left.trans hPL))
  have hkerφ : φ.ker = R.subgroupOf Q₁ :=
    ker_normalizerMonoidHom_comp_inclusion (inf_le_left.trans hPL)
  have hkerbot : φ.ker = ⊥ := by rw [hkerφ, hRbot', Subgroup.bot_subgroupOf]
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  have hEcard' : Nat.card (E.subgroupOf Q₁) = 27 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ₁).toEquiv).trans hEcard
  have hEea' : CFSG.Open.IsElemAbelian 3 (E.subgroupOf Q₁) := hEea.subgroupOf Q₁
  refine ⟨(E.subgroupOf Q₁).map φ, hEea'.map φ, ?_⟩
  rw [Subgroup.card_map_of_injective hinj, hEcard']

private theorem exists_elemAbelian_27_of_inf_ne_bot {p : ℕ} [Fact p.Prime]
    {P₀ Q : Subgroup G} (hP₀ : Nat.card P₀ = p)
    (hQP₀ : Q ≤ Subgroup.normalizer (P₀ : Set G))
    (hF2 : CFSG.Open.pRank 3 (Subgroup.centralizer (P₀ : Set G) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≤ 1)
    (hcard : Nat.card ↥Q = 3 ^ 5) (hexp : ∀ x : ↥Q, x ^ 3 = 1)
    (hcomm : commutator ↥Q ≤ Subgroup.center ↥Q)
    (hRne : ((Q ⊓ Subgroup.centralizer (P₀ : Set G)) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≠ ⊥)
    (hcenter : (((Q ⊓ Subgroup.centralizer (P₀ : Set G)) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)).subgroupOf Q) =
      Subgroup.center ↥Q) :
    ∃ B : Subgroup (MulAut ↥(CFSG.Open.rankThreeLayer
        (Subgroup.centralizer (P₀ : Set G)))),
      CFSG.Open.IsElemAbelian 3 B ∧ 27 ≤ Nat.card B := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P₀ : Set G)
  let L : Subgroup G := CFSG.Open.rankThreeLayer C
  let Q₁ : Subgroup G := Q ⊓ C
  let R : Subgroup G := Q₁ ⊓ Subgroup.centralizer (L : Set G)
  obtain ⟨hPC, hPL⟩ := le_normalizer_centralizer_and_layer hQP₀
  have hle : Nat.card Q ≤ 3 * Nat.card Q₁ :=
    card_le_three_mul_card_inf_centralizer_of_le_normalizer hP₀ hQP₀ hexp
  have hbig : 81 ≤ Nat.card ↥Q₁ := by
    have h : 3 * 81 ≤ 3 * Nat.card ↥Q₁ := by
      calc 3 * 81 = 243 := by norm_num
        _ = Nat.card ↥Q := by rw [hcard]; norm_num
        _ ≤ 3 * Nat.card ↥Q₁ := hle
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  let φ : ↥Q₁ →* MulAut ↥L :=
    L.normalizerMonoidHom.comp (Subgroup.inclusion (inf_le_left.trans hPL))
  have hkerφ : φ.ker = R.subgroupOf Q₁ :=
    ker_normalizerMonoidHom_comp_inclusion (inf_le_left.trans hPL)
  have hcenter' : R.subgroupOf Q = Subgroup.center ↥Q := by
    simpa [R, Q₁, C, L] using hcenter
  have hcommKer : commutator ↥Q₁ ≤ φ.ker :=
    commutator_le_ker_of_eq_center φ hkerφ inf_le_left hcenter' hcomm
  have hexpQ₁ : ∀ x : ↥Q₁, x ^ 3 = 1 := by
    intro x
    apply Subtype.ext
    have hxQ : ((x : Q₁) : G) ∈ Q := (inf_le_left : Q₁ ≤ Q) x.2
    have hx := hexp (⟨((x : Q₁) : G), hxQ⟩ : ↥Q)
    simpa using congrArg Subtype.val hx
  have hrangeEa := isElemAbelian_range_of_commutator_le_ker φ hcommKer hexpQ₁
  have hRcard : Nat.card ↥R = 3 :=
    card_eq_three_inf_centralizer_of_ne_bot (P₀ := P₀) (Q := Q) hF2 hcard hexp
      (by simpa [R, Q₁, C, L] using hRne)
  have hkerφcard : Nat.card φ.ker = 3 := by
    rw [hkerφ]
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : R ≤ Q₁)).toEquiv).trans hRcard
  have hrangeCard : 27 ≤ Nat.card φ.range :=
    card_range_ge_27_of_ker_card φ hkerφcard hbig
  exact ⟨φ.range, hrangeEa, hrangeCard⟩

theorem exists_isElemAbelian_27_mulAut_of_threeOnePlusFour {p : ℕ} [Fact p.Prime]
    {P₀ Q : Subgroup G} (hP₀ : Nat.card P₀ = p)
    (hF2 : CFSG.Open.pRank 3 (Subgroup.centralizer (P₀ : Set G) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≤ 1)
    (hQP₀ : Q ≤ Subgroup.normalizer (P₀ : Set G))
    (hcard : Nat.card ↥Q = 3 ^ 5) (hexp : ∀ x : ↥Q, x ^ 3 = 1)
    (hZ : Nat.card (Subgroup.center ↥Q) = 3)
    (hcomm : commutator ↥Q ≤ Subgroup.center ↥Q) :
    ∃ B : Subgroup (MulAut ↥(CFSG.Open.rankThreeLayer
        (Subgroup.centralizer (P₀ : Set G)))),
      CFSG.Open.IsElemAbelian 3 B ∧ 27 ≤ Nat.card B := by
  classical
  by_cases hRbot : ((Q ⊓ Subgroup.centralizer (P₀ : Set G)) ⊓
      Subgroup.centralizer
        (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) = ⊥
  · exact exists_elemAbelian_27_of_inf_eq_bot hP₀ hQP₀ hcard hexp hZ hcomm hRbot
  · exact exists_elemAbelian_27_of_inf_ne_bot hP₀ hQP₀ hF2 hcard hexp hcomm hRbot
      (subgroupOf_inf_centralizers_eq_center hF2 hQP₀ hcard hexp hZ hRbot)

theorem false_of_threeOnePlusFour_le_normalizer {p m : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hm : m ≠ 0) {P₀ Q : Subgroup G}
    (hP₀ : Nat.card P₀ = p)
    (hL : Nonempty (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) ≃*
      PSL(2, GaloisField p m)))
    (hF2 : CFSG.Open.pRank 3 (Subgroup.centralizer (P₀ : Set G) ⊓ Subgroup.centralizer
      (CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G)) : Set G)) ≤ 1)
    (hQP₀ : Q ≤ Subgroup.normalizer (P₀ : Set G))
    (hcard : Nat.card ↥Q = 3 ^ 5) (hexp : ∀ x : ↥Q, x ^ 3 = 1)
    (hZ : Nat.card (Subgroup.center ↥Q) = 3)
    (hcomm : commutator ↥Q ≤ Subgroup.center ↥Q) : False := by
  classical
  obtain ⟨e⟩ := hL
  obtain ⟨B, hBea, hBcard⟩ :=
    exists_isElemAbelian_27_mulAut_of_threeOnePlusFour hP₀ hF2 hQP₀ hcard hexp hZ hcomm
  let eAut : MulAut ↥(CFSG.Open.rankThreeLayer (Subgroup.centralizer (P₀ : Set G))) ≃*
      MulAut (PSL(2, GaloisField p m)) := MulAut.congr e
  let B' : Subgroup (MulAut (PSL(2, GaloisField p m))) := B.map eAut.toMonoidHom
  have hB'ea : CFSG.Open.IsElemAbelian 3 B' := hBea.map eAut.toMonoidHom
  have hB'card : Nat.card B' = Nat.card B := Subgroup.card_map_of_injective eAut.injective
  have hchar : ringChar (GaloisField p m) ≠ 3 := by
    rw [ringChar.eq (GaloisField p m) p]
    omega
  have hfour : 4 ≤ Nat.card (GaloisField p m) := by
    rw [GaloisField.card p m hm]
    calc 4 ≤ p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ m := Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ m)
  have hnine := CFSG.RankThree.PartTwo.Sec4.Hering418L2.card_le_nine_of_mulAut_PSL2
    (K := GaloisField p m) hchar hfour B' hB'ea
  rw [hB'card] at hnine
  omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14

end
