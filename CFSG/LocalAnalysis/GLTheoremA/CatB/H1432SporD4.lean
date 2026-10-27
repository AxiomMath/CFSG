module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432ExtraComp
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432Cent
import CFSG.HardMathSupport.Dickson.Sec6.Up34SporAux.BMNum
public import CFSG.LocalAnalysis.GLTheoremA.CatA.BMTypeRows
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1432ClsRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.SporD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.LocalAnalysis.GLTheoremA.BMType (catalogIs_of_mulEquiv)

structure TypeHypC (P : TauCeti.CFSGIndex → Prop) (n : ℕ) : Prop where
  card : ∀ (T : Type) [Group T] [Finite T], catalogIs T P → Nat.card T = n
  big : 25920 ≤ n
  nine : 9 ∣ n

section Generic

variable {G : Type} [Group G] [Finite G]

theorem comp_data_of_typeC {P : TauCeti.CFSGIndex → Prop} {n : ℕ} (hP : TypeHypC P n)
    {C J : Subgroup G} (hO : GLAPPrimeCoreOf 3 C = ⊥) (hJ : GLAPComponent 3 C J)
    (hT : catalogIs (PSimple 3 J) P) :
    IsComponentOf J C ∧ catalogIs (↥J ⧸ Subgroup.center ↥J) P ∧
      (Subgroup.center ↥J).index = n ∧ (∃ a : ℕ, Nat.card ↥(Subgroup.center ↥J) = 3 ^ a) ∧
      Nat.card ↥J = Nat.card ↥(Subgroup.center ↥J) * n := by
  have hcore := CFSG.HardMathSupport.Solomon.Coordinator.YS08.glaPPrimeCore_eq_bot_of_glaPComponent
    hO hJ
  let e : PQuot 3 J ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  let eS : (↥J ⧸ Subgroup.center ↥J) ≃* PSimple 3 J :=
    QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)
  have hcat : catalogIs (↥J ⧸ Subgroup.center ↥J) P := catalogIs_of_mulEquiv eS hT
  have hidx : (Subgroup.center ↥J).index = n := by
    rw [Subgroup.index]
    exact hP.card _ hcat
  have hZ : IsPGroup 3 ↥(Subgroup.center ↥J) :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.SchurFacts.isPGroup_center_of_glaPPrimeCore_eq_bot
      Nat.prime_three hcore
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card.1 hZ)
  refine ⟨CFSG.HardMathSupport.Solomon.Coordinator.YS08.isComponentOf_of_glaPComponent' hO hJ,
    hcat, hidx, ⟨a, ha⟩, ?_⟩
  rw [← hidx, mul_comm]
  exact (Subgroup.card_mul_index _).symm.trans (by rw [mul_comm])

theorem false_of_inverted_typeC_prime {P : TauCeti.CFSGIndex → Prop} {n : ℕ}
    (hP : TypeHypC P n) {s α : G} (hα : α * α = 1) (hinv : α * s * α⁻¹ = s⁻¹)
    (hO : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({s} : Set G)) = ⊥)
    {H : Subgroup G} (hH : IsSimpleGroup ↥H)
    (hHα : ∀ h ∈ H, α * h = h * α) (hHs : ∀ h ∈ H, s * h = h * s)
    (hHn : ∀ q : G, α * q = q * α → s * q = q * s → ∀ h ∈ H, q * h * q⁻¹ ∈ H)
    (hCQ : ∀ q : G, α * q = q * α → s * q = q * s → (∀ h ∈ H, q * h = h * q) → q = 1)
    (hbig : ∀ k : ℕ, n ^ k ≤ Nat.card G → ¬ Nat.card ↥H ∣ k.factorial)
    {q : ℕ} (hq : q.Prime) (hqH : q ∣ Nat.card ↥H) (hqn : ¬ q ∣ n)
    {J : Subgroup G} (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set G)) J)
    (hT : catalogIs (PSimple 3 J) P) : False := by
  obtain ⟨-, -, hidx, ⟨a, ha⟩, hcard⟩ := comp_data_of_typeC hP hO hJ hT
  have hnab : ∃ x y : ↥J, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    have hZtop : Subgroup.center ↥J = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact hcon y x
    rw [hZtop, Subgroup.index_top] at hidx
    have := hP.big
    omega
  refine CFSG.HardMathSupport.Solomon.Coordinator.false_of_inverted_component hα hinv hO hH hHα hHs
    hHn hCQ n hbig hJ (by rw [hcard, mul_comm]) hnab ?_
  intro hd
  have hq' : q ∣ (3 ^ a * n) ^ 2 := by
    rw [hcard, ha] at hd
    exact hqH.trans hd
  have h1 := hq.dvd_of_dvd_pow hq'
  rcases (Nat.Prime.dvd_mul hq).1 h1 with h2 | h2
  · have h3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h2)
    subst h3
    exact hqn ((by norm_num : (3 : ℕ) ∣ 9).trans hP.nine)
  · exact hqn h2

end Generic

end CFSG.LocalAnalysis.GLTheoremA.H1420.SporD4


namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
open scoped Matrix

set_option maxRecDepth 100000 in
theorem exists_z_no_large_comp
    :
    ∃ z : NativeSporadic.B, orderOf z = 3 ∧ rk z = 2916 ∧
      ∀ K : Subgroup NativeSporadic.B,
        IsComponentOf K (Subgroup.centralizer ({z} : Set NativeSporadic.B)) →
        9 ∣ (Subgroup.center ↥K).index → Subgroup.center ↥K = ⊥ →
        6 ≤ (Nat.card K).factorization 3 → False := by
  obtain ⟨x, y, z, g, hH, hy3, hgx, hgy, hgz, hrk⟩ := bNF_holds
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hn : 0 < 4 := by norm_num
  have hz3 : z ^ 3 = 1 := hH.zp
  refine ⟨z, orderOf_z hH, hrk, ?_⟩
  have hdX : ∀ (k : Fin 2) (j : Fin 4), ∀ i < 9,
      (nfXData.getD (4 * k.val + j.val) []).getD i 0 < 3 := by
    set_option maxRecDepth 100000 in decide
  have hdY : ∀ (k : Fin 2) (j : Fin 4), ∀ i < 9,
      (nfYData.getD (4 * k.val + j.val) []).getD i 0 < 3 := by
    set_option maxRecDepth 100000 in decide
  set Q := heisSub x y with hQ
  have hgxQ : ∀ k j, g k * x j * (g k)⁻¹ ∈ Q := fun k j => by
    rw [hgx k j, nfProd_eq_heisNF _ _ _ _ (hdX k j)]
    exact heisNF_mem hH hn _ _
  have hgyQ : ∀ k j, g k * y j * (g k)⁻¹ ∈ Q := fun k j => by
    rw [hgy k j, nfProd_eq_heisNF _ _ _ _ (hdY k j)]
    exact heisNF_mem hH hn _ _
  have hgN : ∀ k, g k ∈ Subgroup.normalizer (Q : Set NativeSporadic.B) := fun k =>
    mem_normalizer_of_conj_mem (hgxQ k) (hgyQ k)
  have hmat : ∀ k : Fin 2, heisMat hH hy3 (g k) = tMat k.val := fun k =>
    heisMat_eq_of_nf hH hy3 hn (tMat k.val)
      (fun j => ⟨_, by
        rw [hgx k j, nfProd_eq_heisNF _ _ _ _ (hdX k j)]
        congr 1
        funext i
        simp [tMat]⟩)
      (fun j => ⟨_, by
        rw [hgy k j, nfProd_eq_heisNF _ _ _ _ (hdY k j)]
        congr 1
        funext i
        simp [tMat]⟩)
  have hmat0 : heisMat hH hy3 (g 0) = tA := by
    have h0 := hmat 0
    simp only [Fin.val_zero] at h0
    rw [h0, tMat_zero]
  have hmat1 : heisMat hH hy3 (g 1) = tB := by
    have h1 := hmat 1
    simp only [Fin.val_one] at h1
    rw [h1, tMat_one]
  set L : Subgroup NativeSporadic.B :=
    Subgroup.closure (Set.range g ∪ (Set.range x ∪ Set.range y)) with hL
  have hQL : Q ≤ L := Subgroup.closure_mono Set.subset_union_right
  have hxQ : ∀ i, x i ∈ Q := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have hyQ : ∀ i, y i ∈ Q := fun i => Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hLN : L ≤ Subgroup.normalizer (Q : Set NativeSporadic.B) := by
    rw [hL, Subgroup.closure_le]
    rintro _ (⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hgN k
    · exact Subgroup.le_normalizer (hxQ i)
    · exact Subgroup.le_normalizer (hyQ i)
  set X := Subgroup.centralizer ({z} : Set NativeSporadic.B) with hX
  have hLX : L ≤ Subgroup.normalizer (X : Set NativeSporadic.B) := by
    rw [hL, Subgroup.closure_le]
    rintro _ (⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact mem_normalizer_centralizer_of_conj_eq_sq hz3 (hgz k)
    · exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 (hH.zx i))
    · exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 (hH.zy i))
  have hgL : ∀ k, g k ∈ L := fun k => Subgroup.subset_closure (Or.inl ⟨k, rfl⟩)
  have hhN : ∀ i : Fin 2, (![(g 0 * g 1) ^ 60, (g 1 * g 0) ^ 60] : Fin 2 → NativeSporadic.B) i ∈
      Subgroup.normalizer (Q : Set NativeSporadic.B) := by
    intro i
    fin_cases i
    · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (hgN 0) (hgN 1)) 60
    · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (hgN 1) (hgN 0)) 60
  have hmat60 : ∀ i : Fin 2,
      heisMat hH hy3 ((![(g 0 * g 1) ^ 60, (g 1 * g 0) ^ 60] : Fin 2 → NativeSporadic.B) i) =
        hM i := by
    intro i
    fin_cases i
    · show heisMat hH hy3 ((g 0 * g 1) ^ 60) = hA
      rw [heisMat_pow hH hy3 (Subgroup.mul_mem _ (hgN 0) (hgN 1)),
        heisMat_mul hH hy3 (hgN 0) (hgN 1), hmat0, hmat1]
      exact pow_sixty_tA_tB
    · show heisMat hH hy3 ((g 1 * g 0) ^ 60) = hB
      rw [heisMat_pow hH hy3 (Subgroup.mul_mem _ (hgN 1) (hgN 0)),
        heisMat_mul hH hy3 (hgN 1) (hgN 0), hmat0, hmat1]
      exact pow_sixty_tB_tA
  have hdich : ∀ N : Subgroup NativeSporadic.B, N ≤ Q →
      (∀ a ∈ L, a ^ 60 ∈ Subgroup.normalizer (N : Set NativeSporadic.B)) →
        N ≤ Subgroup.zpowers z ∨ N = Q := by
    intro N hNQ hNn
    refine dich_of_irred hH hy3 hn ![(g 0 * g 1) ^ 60, (g 1 * g 0) ^ 60] hhN
      (fun U hU => irred_hAB U fun i v hv => by
        have := hU i v hv
        rwa [hmat60 i] at this) N hNQ (fun i => ?_)
    fin_cases i
    · exact hNn _ (Subgroup.mul_mem _ (hgL 0) (hgL 1))
    · exact hNn _ (Subgroup.mul_mem _ (hgL 1) (hgL 0))
  have hidx : ¬ (Subgroup.zpowers z).relIndex Q ∣ (6 : ℕ).factorial := by
    rw [hQ, relIndex_zpowers_heisSub hH hy3 hn]
    decide
  have hG : ¬ 9 ^ (6 + 1) ∣ Nat.card NativeSporadic.B := by
    intro hd
    have h14 : 3 ^ 14 ∣ Nat.card NativeSporadic.B := by
      have : (9 : ℕ) ^ (6 + 1) = 3 ^ 14 := by norm_num
      rwa [this] at hd
    have hpos : Nat.card NativeSporadic.B ≠ 0 := Nat.card_pos.ne'
    have := (Nat.prime_three.pow_dvd_iff_le_factorization hpos).1 h14
    rw [factorization_card_B_three] at this
    omega
  have hm : ∀ k, 0 < k → k ≤ 6 → k ∣ 60 := by
    intro k hk0 hk6
    interval_cases k <;> decide
  intro K hK h9 hZ h6
  have hQc : Nat.card Q = 3 ^ 9 := by rw [hQ, card_heisSub hH hy3 hn]
  have hv : (3 ^ 9 : ℕ).factorization 3 = 9 := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_three]
    rfl
  refine CFSG.LocalAnalysis.GLTheoremA.H1420.SporD4.false_of_large_component z X Q L 6 60 hm hQL hLN
    hLX hdich hidx hG (orderOf_z hH) (z_mem hH hn) le_rfl hK h9 hZ ?_
  rw [factorization_card_B_three, hQc, hv]
  omega

end CFSG.HardMathSupport.Solomon.Coordinator.B3B

namespace CFSG.HardMathSupport.MathTwE6.M3BIrr

open CFSG.AGLEmbedding.Norton.MON5_7 CFSG.Monster.Generated CFSG.Monster.B.Pinned
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF (QQ tbL tbL_conj QQ_le_tbL tbb₁_mem
  tbb₂_mem card_QQ not_three_pow_21_dvd factorization_tbL le_zpowers_of_le_CQ isAct_b₁ isAct_b₂)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem no_large_comp_of_certificates
    :
    ∀ J : Subgroup Gmat,
      CFSG.Open.IsComponentOf J
        (Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat)) →
      9 ∣ (Subgroup.center J).index → Subgroup.center J = ⊥ →
      9 ≤ (Nat.card J).factorization 3 → False := by
  have hirr := Certificates.certificate136207
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  have hcardG : Nat.card Gmat = CFSG.Open.monsterOrder := CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder
  have hLQ : tbL ≤ Subgroup.normalizer (QQ : Set Gmat) := fun b hb =>
    mem_normalizer_of_conj (tbL_conj b hb)
  have hLX : tbL ≤ Subgroup.normalizer
      (Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) : Set Gmat) :=
    fun b hb => CFSG.HardMathSupport.MathTwE6.mem_normalizer_centralizer
      (tbL_le_normalizer_zpowers hb)
  have hrel : (Subgroup.zpowers tbw).relIndex QQ = 3 ^ 12 := by
    have h := Subgroup.relIndex_mul_card (H := Subgroup.zpowers tbw) (K := QQ)
    rw [inf_of_le_left (Subgroup.zpowers_le.2 tbCommData.mem_z), Nat.card_zpowers,
      tbCommData.orderOf_z, card_QQ] at h
    omega
  have hidx : ¬ (Subgroup.zpowers tbw).relIndex QQ ∣ (10 : ℕ).factorial := by
    rw [hrel]; decide
  have hG : ¬ 9 ^ (10 + 1) ∣ Nat.card Gmat := fun h =>
    not_three_pow_21_dvd (hcardG ▸ (pow_dvd_pow 3 (by norm_num : 21 ≤ 22)).trans
      (by simpa [show (9 : ℕ) ^ 11 = 3 ^ 22 by norm_num] using h))
  have hv : (Nat.card Gmat).factorization 3 ≤ 20 := by
    by_contra h
    exact not_three_pow_21_dvd (hcardG ▸
      (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 (by omega))
  have hvQ : (Nat.card QQ).factorization 3 = 13 := by
    rw [card_QQ, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_three]
    rfl
  have hXw : Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) ≤
      Subgroup.centralizer ({tbw} : Set Gmat) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Subgroup.mem_zpowers tbw))
  have hm : ∀ k, 0 < k → k ≤ 10 → k ∣ (10 : ℕ).factorial := fun k hk hk10 =>
    Nat.dvd_factorial hk hk10
  intro J hJ hJ9 hZ h9
  refine CFSG.LocalAnalysis.GLTheoremA.H1420.SporD4.false_of_large_component tbw _ QQ tbL 10
    (10 : ℕ).factorial hm QQ_le_tbL hLQ hLX (fun N hN hnorm => tbL_dichotomy hirr N hN hnorm) hidx hG
    tbCommData.orderOf_z tbCommData.mem_z hXw hJ hJ9 hZ ?_
  rw [hvQ]
  omega

end CFSG.HardMathSupport.MathTwE6.M3BIrr

namespace CFSG.LocalAnalysis.GLTheoremA.H1420.SporD4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.Coordinator (sporOrd SporadicOrdersTable)
open CFSG.LocalAnalysis.GLTheoremA.K14Spor CFSG.LocalAnalysis.GLTheoremA.BMType
open CFSG.Blueprint.NativeSporadic (Carrier)

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Generic

variable {G : Type} [Group G] [Finite G]

theorem typeHypC_d4three
    : TypeHypC (S8.isD4of 3) 4952179814400 where
  card := fun _ _ _ h => ClsRed.card_d4three CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds h
  big := by norm_num
  nine := by norm_num

theorem d4_comp_facts
    {C J : Subgroup G} (hO : GLAPPrimeCoreOf 3 C = ⊥) (hJ : GLAPComponent 3 C J)
    (hT : catalogIs (PSimple 3 J) (S8.isD4of 3)) :
    IsComponentOf J C ∧ 9 ∣ (Subgroup.center ↥J).index ∧ Subgroup.center ↥J = ⊥ ∧
      12 ≤ (Nat.card J).factorization 3 := by
  obtain ⟨hcomp, hcat, hidx, ⟨a, ha⟩, hcard⟩ := comp_data_of_typeC typeHypC_d4three hO hJ hT
  have hq : CFSG.Open.IsQuasisimple ↥J := hcomp.2.2
  have h1 : Nat.card ↥(Subgroup.center ↥J) = 1 := by
    refine i1432Cent_holds ↥J hq (fun z _ => ⟨a, ?_⟩) (Or.inr (Or.inr (Or.inl hcat)))
    have := pow_card_eq_one' (G := ↥(Subgroup.center ↥J)) (x := ⟨z, ‹_›⟩)
    rw [ha] at this
    exact congrArg Subtype.val this
  have hZ : Subgroup.center ↥J = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  refine ⟨hcomp, by rw [hidx]; norm_num, hZ, ?_⟩
  rw [hcard, h1, one_mul]
  exact (Nat.prime_three.pow_dvd_iff_le_factorization (by norm_num)).1 (by norm_num)

end Generic

section BRow

open CFSG.Monster.GMS CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Dickson.Sec6.BM CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.B3B
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal

set_option maxRecDepth 100000 in
theorem false_of_d4_B
    {s : NativeSporadic.B} (hs : orderOf s = 3) {J : Subgroup NativeSporadic.B}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set NativeSporadic.B)) J)
    (hT : catalogIs (PSimple 3 J) (S8.isD4of 3)) : False := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hG : Nat.card NativeSporadic.B = 4154781481226426191177580544000000 := by
    rw [card_nativeB, monsterBabyOrder_eq_numeral]
  have hO3 : OPrimeCoreTrivialAt 3 NativeSporadic.B := BThreeFi23.oPrimeCoreTrivialAt_B_three
  by_cases hinv : ∃ d : NativeSporadic.B, BabyInv 0 d ∧ d * s * d⁻¹ = s⁻¹
  · obtain ⟨d, hd, hdinv⟩ := hinv
    obtain ⟨H, hH, -, hcard, hHd, hHs, hHn, hCQ⟩ := B_inverted_data hs hd hdinv
    have hdd : d * d = 1 := by
      have := pow_orderOf_eq_one d
      rwa [hd.1, sq] at this
    have hO := hO3 s hs
    have key := @false_of_inverted_typeC_prime NativeSporadic.B _ _ _ _ typeHypC_d4three s d hdd hdinv hO
    have h11 : Nat.Prime 11 := by norm_num
    refine key hH hHd hHs hHn hCQ ?_ h11 (by rw [hcard]; norm_num)
      (show ¬ (11 : ℕ) ∣ 4952179814400 by norm_num) hJ hT
    intro k hk
    rw [hG] at hk
    rw [hcard]
    exact not_dvd_factorial_of_bound (K := 7) typeHypC_d4three.big (by norm_num) (by decide) hk
  · have hunv : ∀ d : NativeSporadic.B, BabyInv 0 d → d * s * d⁻¹ ≠ s⁻¹ :=
      fun d hd h => hinv ⟨d, hd, h⟩
    obtain ⟨z, hz3, hzrk, hmain⟩ := exists_z_no_large_comp
    have hzc : IsConj z (phiB (t3 1)) := isConj_phiB_t3_one_of_rk hz3 hzrk
    have hnot0 : ¬ IsConj s (phiB (t3 0)) := by
      intro hc
      obtain ⟨d, hd, hdr⟩ := phiB_t3_zero_inverted
      obtain ⟨c, hcx⟩ := isConj_iff.1 hc
      refine hunv (c⁻¹ * d * c) (CFSG.Monster.GMS.BabyInv.of_isConj hd
        (isConj_iff.2 ⟨c⁻¹, by simp⟩)) ?_
      have hx' : s = c⁻¹ * phiB (t3 0) * c := by rw [← hcx]; group
      calc c⁻¹ * d * c * s * (c⁻¹ * d * c)⁻¹
          = c⁻¹ * (d * phiB (t3 0) * d⁻¹) * c := by rw [hx']; group
        _ = s⁻¹ := by rw [hdr, hx']; group
    have hsc : IsConj s (phiB (t3 1)) := by
      obtain ⟨i, hi⟩ := bThree_classes s hs
      fin_cases i
      · exact absurd hi hnot0
      · exact hi
      · exact absurd (hi.trans bThreeRc_holds) hnot0
      · exact hi.trans bThreeRd_holds
    obtain ⟨c, hc⟩ := isConj_iff.1 (hsc.trans hzc.symm)
    obtain ⟨hJ', hT'⟩ := glaPComponent_conj_type c hJ hT
    rw [MulAut.conj_apply, hc] at hJ'
    obtain ⟨hcomp, h9, hZ, h12⟩ := d4_comp_facts (hO3 z hz3) hJ' hT'
    exact hmain _ hcomp h9 hZ (by omega)

theorem typeRow_d4_B
    : TypeRow (S8.isD4of 3) .B := by
  obtain ⟨hfin, hs, ⟨b⟩, hnc⟩ := CFSG.HardMathSupport.Dickson.BMRows.model_B
  exact @typeRow_of_model _ .B (Carrier .B) _ hfin hs
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds b hnc
    fun k hk J hJ hT => false_of_d4_B (s := k) hk hJ hT

end BRow

section MRow

open CFSG.Monster.Generated CFSG.Monster.Existence CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.AGLEmbedding.Norton.MON5_7

set_option maxRecDepth 100000 in
theorem false_of_d4_gmat
    {s : CFSG.Monster.Generated.Gmat} (hs : orderOf s = 3)
    {J : Subgroup CFSG.Monster.Generated.Gmat}
    (hJ : GLAPComponent 3 (Subgroup.centralizer ({s} : Set CFSG.Monster.Generated.Gmat)) J)
    (hT : catalogIs (PSimple 3 J) (S8.isD4of 3)) : False := by
  haveI : Finite Gmat := ThreeBNF.finite_Gmat
  by_cases hinv : InvertedByTwoA s
  · have hE := CFSG.Milestones.cl_lit_monster_existence_griess_conway
    haveI : Finite MGriess := hE.1.1
    let φ : Gmat ≃* MGriess :=
      (CFSG.YGroups.Y443.griessEquivGmat CFSG.YGroups.Y443.Gmat_eq_AutO_of_stroth).symm
    have hs' : orderOf (φ s) = 3 := by rwa [MulEquiv.orderOf_eq]
    obtain ⟨hJ', hT'⟩ := glaPComponent_map_type φ hJ hT
    have hO := gLAPPrimeCoreOf_eq_bot_of_invertedByTwoA hE Nat.prime_three (by norm_num) hs'
      (hinv.map φ)
    obtain ⟨α, H, hα, hαs, hH, -, hcard, hHα, hHs, hHn, hCQ⟩ :=
      CFSG.HardMathSupport.Dickson.Sec6.BM.M_inverted_data hE hs' (hinv.map φ)
    have hG : Nat.card MGriess = 808017424794512875886459904961710757005754368000000000 := by
      have := hE.1.2.2.2
      rw [CFSG.HardMathSupport.Dickson.Sec6.BM.monsterOrder_eq_numeral] at this
      exact this
    have key := @false_of_inverted_typeC_prime MGriess _ _ _ _ typeHypC_d4three _ α hα hαs hO
    have hbig : ∀ k : ℕ, 4952179814400 ^ k ≤ Nat.card MGriess → ¬ Nat.card ↥H ∣ k.factorial := by
      intro k hk
      rw [hG] at hk
      rcases hcard with hc | hc <;> rw [hc] <;>
        exact not_dvd_factorial_of_bound (K := 12) typeHypC_d4three.big (by norm_num) (by decide) hk
    have h11 : Nat.Prime 11 := by norm_num
    have h19 : Nat.Prime 19 := by norm_num
    rcases hcard with hc | hc
    · exact key hH hHα hHs hHn hCQ hbig h11 (by rw [hc]; norm_num)
        (show ¬ (11 : ℕ) ∣ 4952179814400 by norm_num) hJ' hT'
    · exact key hH hHα hHs hHn hCQ hbig h19 (by rw [hc]; norm_num)
        (show ¬ (19 : ℕ) ∣ 4952179814400 by norm_num) hJ' hT'
  · have hOu : UninvertedOPrimeTrivial 3 Gmat :=
      uninvertedOPrimeTrivial_gmat_of_twoAPureKlein Nat.prime_three (by norm_num)
        BThreeFi23.oPrimeCoreTrivialAt_B_three ThreeBNF.twoAPureKlein_three_Gmat
    have hsc : IsConj s tbw := CFSG.HardMathSupport.Dickson.Sec6.BM2.m3bClass_holds s hs hinv
    obtain ⟨c, hc⟩ := isConj_iff.1 hsc
    obtain ⟨hJ', hT'⟩ := glaPComponent_conj_type c hJ hT
    rw [MulAut.conj_apply, hc] at hJ'
    have hw3 : orderOf tbw = 3 := by rw [← hc, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hs]
    have hwinv : ¬ InvertedByTwoA tbw := by
      intro hw
      apply hinv
      have h := hw.map (MulAut.conj c⁻¹)
      rwa [MulAut.conj_apply, ← hc, show c⁻¹ * (c * s * c⁻¹) * c⁻¹⁻¹ = s by group] at h
    have hOw := hOu tbw hw3 hwinv
    obtain ⟨hcomp, h9, hZ, h12⟩ := d4_comp_facts hOw hJ' hT'
    have hC : Subgroup.centralizer ((Subgroup.zpowers tbw : Subgroup Gmat) : Set Gmat) =
        Subgroup.centralizer ({tbw} : Set Gmat) := by
      rw [Subgroup.zpowers_eq_closure]
      exact Subgroup.centralizer_closure {tbw}
    rw [← hC] at hcomp
    exact CFSG.HardMathSupport.MathTwE6.M3BIrr.no_large_comp_of_certificates _ hcomp h9 hZ (by omega)

theorem typeRow_d4_M
    : TypeRow (S8.isD4of 3) .M := by
  obtain ⟨-, hs, hfin⟩ := CFSG.Monster.Generated.generated_rational_group_finite_simple
  obtain ⟨b⟩ := CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  have hnc : ∃ a c : CFSG.Monster.Generated.Gmat, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by
      rw [CFSG.YGroups.Y443.natCard_Gmat_eq_monsterOrder, CFSG.Open.monsterOrder]
      norm_num)
  exact @typeRow_of_model _ .M CFSG.Monster.Generated.Gmat _ hfin hs
    CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds b hnc
    fun k hk J hJ hT => false_of_d4_gmat (s := k) hk hJ hT

end MRow

theorem cardRow_fi23_d4
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    CardRow 4952179814400 .Fi23 := by
  have hc : Nat.card (NativeSporadic.Carrier .Fi23) = 4089470473293004800 :=
    CFSG.Sporadic.Fi23.card_Fi23
  haveI : Finite (NativeSporadic.Carrier .Fi23) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (NativeSporadic.Carrier .Fi23) := CFSG.Sporadic.Fi23.isSimpleGroup_Fi23
  refine cardRow_of_centShapeRk (s := .Fi23) hOut (hbr .Fi23).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711c.fi23CentShapeRk_native ?_
  intro T _ hT hcT
  obtain ⟨e⟩ := hT
  rw [Nat.card_congr e.toEquiv, CFSG.HardMathSupport.Dickson.I271.tabFi23_card_om] at hcT
  norm_num at hcT

theorem names_of_dvd_d4
    (s : TauCeti.SporadicName) (h : 4952179814400 ∣ sporOrd s) :
    s = .Fi23 ∨ s = .Fi24Prime ∨ s = .B ∨ s = .M := by
  revert h
  cases s <;> decide +kernel

theorem i1432SporD4S_holds
    : ClsRed.I1432SporD4S := by
  have hOut := CFSG.HardMathSupport.Timmesfeld.Proving.sporadicOuterLeTwo_holds
  have hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges :=
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
  have hOrd := CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
  intro S _ _ s e β hβ3 hβ1 J hJ hT
  obtain ⟨e'⟩ := e
  have hcJ : Nat.card (PSimple 3 J) = 4952179814400 :=
    ClsRed.card_d4three CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hT
  have hd : 4952179814400 ∣ sporOrd s := by
    rw [← hcJ, ← (Nat.card_congr e'.toEquiv).trans (hOrd s)]
    have h2 : Nat.card (PSimple 3 J) ∣ Nat.card (PQuot 3 J) := Subgroup.card_quotient_dvd_card _
    have h3 : Nat.card (PQuot 3 J) ∣ Nat.card J := Subgroup.card_quotient_dvd_card _
    exact h2.trans (h3.trans (Subgroup.card_subgroup_dvd_card J))
  rcases names_of_dvd_d4 s hd with rfl | rfl | rfl | rfl
  · exact (cardRow_fi23_d4 hOut hbr S ⟨e'⟩ β hβ3 hβ1 J hJ hcJ).elim
  · rfl
  · exact (typeRow_d4_B S ⟨e'⟩ β hβ3 hβ1 J hJ hT).elim
  · exact (typeRow_d4_M S ⟨e'⟩ β hβ3 hβ1 J hJ hT).elim

end CFSG.LocalAnalysis.GLTheoremA.H1420.SporD4

end
