module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A5W1619d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Inputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1619a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1619c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5X1367d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.GH74.QTGen4.U42.ModelP1
public import CFSG.GH74.QTGen4.U42.StubA4b
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP4Mod
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP5Psi

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

local notation "StSL" => Assembly.LowTwoRank.StatedSL

local notation "StSp" => Assembly.LowTwoRank.StatedSp

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)

theorem false_of_levi_F4
    (h126 : TheoremC126) (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4)
    (h132fsu : Stmt13_3_2_three_fsu_F4) (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4)
    (h1327 : Stmt13_2_7_F4) (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))) {K : Subgroup G}
    [IsMulCommutative ↥(S.WK K)] (hK : S.InYz K) (hT : S.Tv ≤ Subgroup.normalizer (K : Set G))
    {L' : Subgroup (MulAut ↥(S.WK K))} (hL'K : L' ≤ S.plus K) (hL'p : ⁅L', L'⁆ = L')
    {K' : Type} [Field K'] [Finite K'] {m : ℕ} (hK' : Nat.card K' = 2 ^ m) (hm : 2 ≤ m)
    {g : ↥L' →* Matrix.SpecialLinearGroup (Fin 2) K'} (hg : Function.Surjective g)
    (hgk : IsPGroup 2 g.ker) (hc : CharTwo L') (hns : ¬ Group.IsSolvable ↥L')
    (hTL : autOn S.Tv (S.WK K) ≤ Subgroup.normalizer (L' : Set (MulAut ↥(S.WK K))))
    (hz : ∃ a ∈ L', ∃ w : ↥(S.WK K), (w : G) = S.z ∧ a w ≠ w) : False := by
  classical
  have hq := S.isQuasisimple_plus_F4 h1222 h517 hF hK hT
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have hHKW : S.HK K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hR.2.1
  have hKHK : K ≤ S.HK K := le_sup_left.trans le_sup_left
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) := hKHK.trans hHKW
  have hTW : S.Tv ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (S.Tv_le_HK K).trans hHKW
  set N := Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) with hNdef

  set K₂ : Subgroup G := K ⊓ (L'.comap (conjAct (S.WK K))).map N.subtype with hK₂def
  have hK₂K : K₂ ≤ K := inf_le_left
  have hK₂W : K₂ ≤ N := hK₂K.trans hKW
  have hK₂im : autOn K₂ (S.WK K) = L' := by
    apply le_antisymm
    · intro a ha
      obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := Setup.mem_autOn_iff.1 ha
      obtain ⟨y, hy, hyk⟩ := hk.2
      have e : y = ⟨k, hkN⟩ := Subtype.ext hyk
      rw [← e]
      exact hy
    · intro a ha
      obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := Setup.mem_autOn_iff.1 (hL'K ha)
      exact Setup.mem_autOn_iff.2 ⟨⟨k, hkN⟩, ⟨hk, ⟨k, hkN⟩, ha, rfl⟩, rfl⟩
  have hTK₂ : S.Tv ≤ Subgroup.normalizer (K₂ : Set G) := by
    intro t ht
    have htN : t ∈ N := hTW ht
    have htL : conjAct (S.WK K) ⟨t, htN⟩ ∈ Subgroup.normalizer (L' : Set (MulAut ↥(S.WK K))) :=
      hTL (Setup.mem_autOn_iff.2 ⟨⟨t, htN⟩, ht, rfl⟩)
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨hT ht, ?_⟩
    exact Subgroup.le_normalizer_map N.subtype
      ⟨⟨t, htN⟩, Subgroup.le_normalizer_comap _ htL, rfl⟩

  set K₁ := perfectCore K₂ with hK₁def
  have hK₁K₂ : K₁ ≤ K₂ := perfectCore_le K₂
  have hK₁K : K₁ ≤ K := hK₁K₂.trans hK₂K
  have hK₁W : K₁ ≤ N := hK₁K₂.trans hK₂W
  have hK₁p : ⁅K₁, K₁⁆ = K₁ := perfectCore_perfect K₂
  have hTK₁ : S.Tv ≤ Subgroup.normalizer (K₁ : Set G) :=
    hTK₂.trans (normalizer_le_normalizer_perfectCore K₂)
  have hK₁im : autOn K₁ (S.WK K) = L' := by
    rw [hK₁def, autOn_perfectCore hK₂W, hK₂im, perfectCore_eq_self_of_perfect hL'p]

  have hTsyl : IsSylowTwoOf S.Tv (K₁ ⊔ S.Tv) := by
    have hsyl := S.isSylowTwoOf_Tv_F4 h1222 h517
    refine ⟨le_sup_right, hsyl.2.1, fun h2 => hsyl.2.2 ?_⟩
    have hrel := Subgroup.relIndex_mul_relIndex S.Tv (K₁ ⊔ S.Tv) _ le_sup_right
      (sup_le (hK₁K.trans hK.1) S.Tv_le_Gv)
    have h' : 2 ∣ S.Tv.relIndex (K₁ ⊔ S.Tv) := h2
    have h3 : 2 ∣ S.Tv.relIndex (Subgroup.centralizer ({S.v12} : Set G)) :=
      hrel ▸ dvd_mul_of_dvd_left h' _
    exact h3

  have hker : Group.IsSolvable ↥(K₁ ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) := by
    have hsub : IsSubnormal (K ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G)) K := by
      refine A3.subnormal_of_normal inf_le_left ?_
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
      intro k hk
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, mem_normalizer_centralizer_of_mem_normalizer (hKW hk)⟩
    have hlt : K ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) < K := by
      refine lt_of_le_of_ne inf_le_left fun h => (qs_perfect_ne_bot hq).2 ?_
      rw [show S.plus K = autOn K (S.WK K) from rfl, autOn_eq_bot_iff hKW]
      intro k hk
      rw [← h] at hk
      exact hk.2
    have hle := le_solvRad_of_subnormal_lt hK.2.1 hsub hlt
    have hle' : K₁ ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) ≤ solvRad K :=
      (inf_le_inf_right _ hK₁K).trans hle
    have := solvRad_isSolvable K
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle')
      (Subgroup.inclusion_injective hle')

  have hLT : IsSylowTwoOf (autOn S.Tv (S.WK K) ⊓ L') L' := by
    have hTvHK : IsSylowTwoOf (autOn S.Tv (S.WK K)) (autOn (S.HK K) (S.WK K)) :=
      Setup.isSylowTwoOf_autOn (S.isSylowTwoOf_Tv_HK_F4 h1222 h517 hK.1) hHKW
    have hLH : L' ⊔ autOn S.Tv (S.WK K) ≤ autOn (S.HK K) (S.WK K) :=
      sup_le (hL'K.trans (A4.autOn_mono hKHK)) (A4.autOn_mono (S.Tv_le_HK K))
    have hT1 : IsSylowTwoOf (autOn S.Tv (S.WK K)) (L' ⊔ autOn S.Tv (S.WK K)) := by
      refine ⟨le_sup_right, hTvHK.2.1, fun h2 => hTvHK.2.2 ?_⟩
      have hrel := Subgroup.relIndex_mul_relIndex (autOn S.Tv (S.WK K))
        (L' ⊔ autOn S.Tv (S.WK K)) _ le_sup_right hLH
      have h' : 2 ∣ (autOn S.Tv (S.WK K)).relIndex (L' ⊔ autOn S.Tv (S.WK K)) := h2
      have h3 : 2 ∣ (autOn S.Tv (S.WK K)).relIndex (autOn (S.HK K) (S.WK K)) :=
        hrel ▸ dvd_mul_of_dvd_left h' _
      exact h3
    exact A4.isSylowTwoOf_inf_normal hT1 le_sup_left (sup_le Subgroup.le_normalizer hTL)
  have hR1 := rankOneAt_of_levi hLT hK' hm hg hgk

  have hsup : autOn (K₁ ⊔ S.Tv) (S.WK K) = L' ⊔ autOn S.Tv (S.WK K) := by
    rw [autOn_sup hK₁W hTW, hK₁im]
  have hM := isUniqueMaxOver_borelOf_sup hR1 hTL
  have hnn := not_le_normalizer_of_rankOneAt hR1
  rw [← hsup] at hM hnn
  have hQ : autOn K₁ (S.WK K) ∈ cComp (autOn K₁ (S.WK K)) := by
    rw [hK₁im]
    exact mem_cComp_self_of_levi hL'p hK' hm hg hgk
  obtain ⟨K₀, hmin, hmp⟩ := exists_minParabolic_member hK₁p hK₁W hTW hTK₁ hTsyl hker hQ hM hnn
  obtain ⟨hK₀K₁, hK₀, hTK₀, hK₀im⟩ := hmin.1
  rw [hK₁im] at hK₀im
  have hK₀K : K₀ ≤ K := hK₀K₁.trans hK₁K

  have hz₀ : ¬ K₀ ≤ Subgroup.centralizer ({S.z} : Set G) := by
    intro h
    obtain ⟨a, ha, w, hw, haw⟩ := hz
    rw [← hK₀im] at ha
    obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := Setup.mem_autOn_iff.1 ha
    apply haw
    apply Subtype.ext
    rw [InternalSec.coe_conjAct_apply, hw, Subgroup.mem_centralizer_singleton_iff.mp (h hk),
      mul_inv_cancel_right]

  obtain ⟨hblk, hcases⟩ := S.isChi0Block_of_minParabolic_F4 h126 h1222 h517 h132two h132fsu h132A5
    h331 h1327 h37 h39 hF (hK₀K.trans hK.1) hK₀ hTK₀ hz₀ hmp
  have hcen := S.pCoreOf_autOn_le_centralizer_F4 h1222 h517 hF hK hT hK₀K hK₀ hTK₀ hz₀ hblk.1.1
    hcases
  rw [hK₀im] at hcen
  exact false_of_charTwo_of_le_centralizer hc hns hcen

end Setting

theorem lemma13619_of_F4
    (h126 : TheoremC126) (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h56 : AsB56) (h132two : Stmt13_3_2_two_F4)
    (h132fsu : Stmt13_3_2_three_fsu_F4) (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4)
    (h1327 : Stmt13_2_7_F4) (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (hng : FactNoGraphTwist) : Lemma13619_F4 := by
  intro G _ _ T L V S hH K hK hT n F _ _ hn hFn
  have hF := hH.hF
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have : IsMulCommutative ↥(S.WK K) := hR.2.2.1.1
  have key : (Nonempty (↥(S.plus K) ≃* ↥(StSL 3 F)) ∨ Nonempty (↥(S.plus K) ≃* ↥(StSp 2 F)) ∨
      Nonempty (↥(S.plus K) ≃* ↥(CFSG.Open.quasithinG2 F))) → False := by
    intro hY
    obtain ⟨L', hL'K, hL'p, ⟨K', _, _, m, hK', hm, g, hg, hgk⟩, hc, hns, hTL, hz⟩ :=
      S.exists_levi_of_rank2_F4 h1222 h517 h56 hng hH hK hT hn hFn hY
    exact S.false_of_levi_F4 h126 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 hF hK hT hL'K
      hL'p hK' hm hg hgk hc hns hTL hz
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr (Or.inl h)),
    fun h => key (Or.inr (Or.inr h))⟩

end CFSG.Quasithin.H13.A5
