module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddNoBlock
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34OddAbel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.SL2Model
open scoped commutatorElement

namespace Setup5_1_17Odd

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (s : Setup5_1_17Odd G T M L V H B D n)
include s

theorem T_inf_centralizer_L_eq_bot_F4 (h5114 : Stmt5_1_14_first_F4) :
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  have hZL := (h5114 G T M L V H B D n s.hyp.hyp s.hyp.notation59 s.hyp.module s.hyp.l34).2.2
  have hT2 : IsPGroup 2 T := (hh.isSylowTwoOf le_top).2.1
  by_contra hne
  have hTC : T ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    hh.T_le_normalizer.trans (normalizer_le_normalizer_centralizer'' L)
  have hTX : T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro t ht
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    exact ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht),
      (Subgroup.mem_normalizer_iff.mp (hTC ht) x).mp hx.2⟩
  obtain ⟨z, hzX, hz1, hzT⟩ := exists_ne_one_mem_centralizer hT2 inf_le_left hTX hne

  have hzle : Subgroup.zpowers z ≤ (T ⊓ Subgroup.centralizer (L : Set G)) ⊓
      Subgroup.centralizer (T : Set G) := Subgroup.zpowers_le.mpr ⟨hzX, hzT⟩
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    hT2.to_le (hzle.trans (inf_le_left.trans inf_le_left))
  have hdvd : 2 ∣ Nat.card (Subgroup.zpowers z) := by
    rcases hz2.card_eq_or_dvd with h1 | h1
    · exfalso
      apply hz1
      have := (Subgroup.card_eq_one.mp h1)
      have hzm : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
      rw [this, Subgroup.mem_bot] at hzm
      exact hzm
    · exact h1
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.zpowers z)) 2 hdvd
  have hy' : orderOf (y : G) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hyZ : (y : G) ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) := by
    have hyX := hzle y.2
    refine ⟨mem_quasithinOmegaOneCenter_iff.mpr ⟨hyX.1.1, hyX.2, ?_⟩, hyX.1.2⟩
    rw [← hy']
    exact pow_orderOf_eq_one _
  rw [hZL, Subgroup.mem_bot] at hyZ
  rw [hyZ, orderOf_one] at hy'
  exact absurd hy' (by norm_num)

theorem not_commutator_pCoreOf_le_F4 (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h5114 : Stmt5_1_14_first_F4) : ¬ ⁅pCoreOf 2 L, L⁆ ≤ V := by
  intro hblock
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh := s.hyp.hyp.toHyp5_0_1
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hQT : Q ≤ T := by
    rw [hQdef, ← hh.centralizer_eq_pCoreOf s.hyp.module]
    exact inf_le_left

  have hQ2 : ∀ q ∈ Q, q ^ 2 = 1 := by
    intro q hq
    have hQC : Q ≤ Subgroup.centralizer (V : Set G) := by
      rw [hQdef, ← hh.centralizer_eq_pCoreOf s.hyp.module]
      exact inf_le_right
    have h1 := sq_mem_centralizer_of_commutator_mem hQC s.elemAbelian
      (fun q hq l hl => s.commutator_mem_of_block hblock hq hl) hq
    have h2 : q ^ 2 ∈ T ⊓ Subgroup.centralizer (L : Set G) := ⟨T.pow_mem (hQT hq) 2, h1⟩
    rw [s.T_inf_centralizer_L_eq_bot_F4 h5114, Subgroup.mem_bot] at h2
    exact h2
  have hinv : ∀ q ∈ Q, q⁻¹ = q := fun q hq => by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hQ2 q hq]
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    calc x * y = (x * y)⁻¹ := (hinv _ (Q.mul_mem hx hy)).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by rw [hinv y hy, hinv x hx]

  have hCQ : ∀ t ∈ T, t ∈ Subgroup.centralizer (D : Set G) → t ∈ Q := fun t ht htD => by
    rw [hQdef, ← hh.centralizer_eq_pCoreOf s.hyp.module]
    exact ⟨ht, s.mem_centralizer_of_mem_centralizer_D hI hF ht htD⟩

  set P := T ⊓ K with hPdef
  have hDT : D ≤ Subgroup.normalizer (T : Set G) :=
    s.hyp.notation59.2.1.1.trans (hh.borelL_le_normalizer_T_of_odd hI s.odd)
  have hDK : D ≤ Subgroup.normalizer (K : Set G) := s.D_le_normalizer
  have hDP : D ≤ Subgroup.normalizer (P : Set G) := by
    intro d hd
    apply mem_normalizer_of_forall_conj_mem'
    intro x hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hDT hd) x).mp hx.1,
      (Subgroup.mem_normalizer_iff.mp (hDK hd) x).mp hx.2⟩
  have hP2 : IsPGroup 2 P := (hh.isSylowTwoOf le_top).2.1.to_le inf_le_left
  have hPsolv : Group.IsSolvable ↥P := by
    have := hP2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card D) (Nat.card P) := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr s.hyp.notation59.2.1.2.1)
  have hfac := coprime_le_commutator_sup_inf_centralizer hDP hPsolv hcop
  have hPD : ⁅P, D⁆ ≤ pCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    intro p hp d hd
    have := (pCoreOf 2 K).inv_mem
      (commutator_mem_of_mem_centralizerModO2 (s.D_le_centralizer hd) hp.2)
    have e : (d * p * d⁻¹ * p⁻¹)⁻¹ = ⁅p, d⁆ := by rw [commutatorElement_def]; group
    rwa [e] at this

  have hPsyl : IsSylowTwoOf P K :=
    A4.isSylowTwoOf_inf_normal (hh.isSylowTwoOf s.hyp.hyp.hStar.1.1) (oTwoUpper_le H)
      (le_normalizer_oTwoUpper H)
  let π : ↥K →* O2Q K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ P.subgroupOf K := by
    intro x hx
    rw [QuotientGroup.ker_mk'] at hx
    exact (pCoreOf_two_le_of_isSylowTwoOf hPsyl) ⟨x, hx, rfl⟩
  set S := (P.subgroupOf K).map π with hSdef
  have hS : IsSylowTwoOf S ⊤ := by
    refine ⟨le_top, (hPsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hPsyl.1).symm).map π, ?_⟩
    show ¬ 2 ∣ S.relIndex ⊤
    rw [Subgroup.relIndex_top_right, hSdef, Subgroup.index_map_eq _ hπs hker]
    exact hPsyl.2.2

  have hSab : IsMulCommutative S := by
    set A := P ⊓ Subgroup.centralizer (D : Set G) with hAdef
    have hAK : A ≤ K := inf_le_left.trans inf_le_right
    have hPDK : ⁅P, D⁆ ≤ K := hPD.trans (pCoreOf_le 2 K)
    have hSle : S ≤ (A.subgroupOf K).map π := by
      have h1 : P.subgroupOf K ≤ ⁅P, D⁆.subgroupOf K ⊔ A.subgroupOf K := by
        rw [← Subgroup.subgroupOf_sup hPDK hAK]
        intro x hx
        exact hfac hx
      have h2 : (⁅P, D⁆.subgroupOf K).map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        intro x hx
        rw [QuotientGroup.ker_mk']
        have hx' : (x : G) ∈ pCoreOf 2 K := hPD hx
        obtain ⟨y, hy, hyx⟩ := hx'
        have : y = x := Subtype.ext hyx
        rwa [← this]
      calc S = (P.subgroupOf K).map π := rfl
        _ ≤ (⁅P, D⁆.subgroupOf K ⊔ A.subgroupOf K).map π := Subgroup.map_mono h1
        _ = (A.subgroupOf K).map π := by rw [Subgroup.map_sup, h2, bot_sup_eq]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    obtain ⟨x, hx, hxa⟩ := hSle a.2
    obtain ⟨y, hy, hyb⟩ := hSle b.2
    have hxy : x * y = y * x := Subtype.ext
      (hQab _ (hCQ _ hx.1.1 hx.2) _ (hCQ _ hy.1.1 hy.2))
    show (a : O2Q K) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  exact not_isMulCommutative_of_isSylowTwoOf s.hyp.l34 hS hSab

end Setup5_1_17Odd

theorem stmt5_1_17_noBlock_of_F4 (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h5114 : Stmt5_1_14_first_F4) : Stmt5_1_17_noBlock_F4 :=
  fun _ _ _ _ _ _ _ _ _ _ _ s => s.not_commutator_pCoreOf_le_F4 hI hF h5114

theorem stmt5_1_17_abelian_proved_F4 (hI : L2OddInnerFact) (hF : L2TorusFact)
    (h5114 : Stmt5_1_14_first_F4) (h126 : A126TwoFact) : Stmt5_1_17_abelian_F4 :=
  stmt5_1_17_abelian_of_F4 hI hF h5114 h126 (stmt5_1_17_noBlock_of_F4 hI hF h5114)

end CFSG.Quasithin.H13
