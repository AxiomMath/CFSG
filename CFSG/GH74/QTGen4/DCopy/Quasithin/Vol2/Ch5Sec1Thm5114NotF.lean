module

public import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114NotF
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1Thm5114FSU
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL4S331
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL5C
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34QDiag

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L34Orders
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T M L V H B D : Subgroup G} {n : ℕ}

namespace Hyp5_1_14

variable (h : Hyp5_1_14 G T M L V H B D n)
include h

theorem not_faithful_F4
    (h510 : Stmt5_1_10_F4) (h5112 : Stmt5_1_12_F4) (h323 : Stmt3_2_3) (h325 : Stmt3_2_5_F4)
    (h328 : Stmt3_2_8) (h329 : Stmt3_2_9C_F4) : ¬ quasithinIsFaithfulLocal T (oTwoUpper H) := by
  intro hKf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V₀, hV₀, hfsu⟩ := h.exists_fsu_F4 h510 h5112 h323 hKf
  set K := oTwoUpper H with hKdef
  have hKK : K = conjClosure K T := h.conjClosure_K.symm
  have hR : V₀ ≤ reducedAggregate (K ⊔ T) := hV₀.1
  have hKV₀ : K ≤ Subgroup.normalizer (V₀ : Set G) := hV₀.2.2.1
  have hne₀ : ¬ K ≤ Subgroup.centralizer (V₀ : Set G) := not_le_centralizer_of_isIrrPlusIn hV₀
  have hKV : K ≤ Subgroup.normalizer (conjClosure V₀ T : Set G) :=
    h.le_normalizer_conjClosure_K hKV₀
  have hVR : conjClosure V₀ T ≤ reducedAggregate (K ⊔ T) :=
    Hyp5_1_14.conjClosure_le_reducedAggregate hR
  have hneV : ¬ K ≤ Subgroup.centralizer (conjClosure V₀ T : Set G) := fun hc =>
    hne₀ (hc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure V₀ T))))
  have hcardV := h.card_autOn_K hKV hVR hneV

  obtain ⟨-, -, hcases⟩ := h325 G T K V₀ hfsu hKK
  have hVeq : V₀ = conjClosure V₀ T := by
    rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, hlist, -⟩
    · exact h1
    · exact h1
    · exfalso
      rcases hlist with ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ |
        ⟨he, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
      · exact card_SL3_ne_20160 hF ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · exact card_statedSp_ne_20160 hF ((Nat.card_congr e.toEquiv).symm.trans hcardV)
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_alt 6 (by norm_num)] at h1
        norm_num [Nat.factorial] at h1
      · exact h.not_equiv_SL4 hKV hVR hneV he
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_SL5_two] at h1
        norm_num at h1
      · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcardV
        rw [card_alt 7 (by norm_num)] at h1
        norm_num [Nat.factorial] at h1

  have hcard := h.card_autOn_K hKV₀ hR hne₀
  have hTV₀ : T ≤ Subgroup.normalizer (V₀ : Set G) := by
    rw [hVeq]
    exact le_normalizer_conjClosure V₀ T
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := h.T_le_normalizer_K
  obtain ⟨k, hk⟩ := exists_card_autOn_sup hKV₀ hTV₀ hTK h.hyp.sylow.1
  rw [hcard] at hk
  have hfinKT : Finite ↥(autOn (K ⊔ T) V₀) :=
    Finite.of_surjective _ (InternalSec.autOnHom_surjective (sup_le hKV₀ hTV₀))
  have hc : IsMulCommutative ↥V₀ :=
    ⟨⟨fun a b => Subtype.ext ((reducedAggregate_props _).2.1 _ (hR a.2) _ (hR b.2))⟩⟩
  by_cases hFF : IsFFModule (V := ↥V₀) (Subgroup.normalizer ((autOn K V₀ : Set (MulAut ↥V₀))))
  ·
    obtain ⟨_, hcases⟩ := h328 G T K V₀ hfsu hKK hVeq ⟨hc, hFF⟩
    rcases hcases with ⟨m, hl, -⟩ | ⟨⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩⟩ |
      ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨m, F, _, _, hF, ⟨e⟩, -⟩ | ⟨⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨-, hZ, ⟨e⟩, -⟩ | ⟨m, hm, ⟨e⟩, -⟩ | ⟨he, -⟩ | ⟨⟨e⟩, -⟩
    · have h1 := CFSG.GH74.card_of_lieModel_PSL (by norm_num) hl
      rw [hcard] at h1
      exact ordA_one_ne_20160' _ h1.symm
    · exact card_SL3_ne_20160 hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact card_SL3_ne_20160 (F := ZMod 2) (n := 1) (by rw [Nat.card_zmod]; norm_num)
        ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact card_statedSp_ne_20160 hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · exact card_G2_derived_ne_20160 hF ((Nat.card_congr e.toEquiv).symm.trans hcard)
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 5 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 7 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := (Nat.card_congr e.toEquiv).symm.trans hcard
      rw [card_alt 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk, card_alt 7 (by norm_num), show Nat.factorial 7 / 2 = 2520 by decide] at h1
      exact mul_two_pow_ne_2520 k h1
    · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center ↥(autOn K V₀))
      rw [hcard, hZ, Nat.card_congr e.toEquiv, card_alt 6 (by norm_num)] at h1
      norm_num [Nat.factorial] at h1
    · rcases hm with rfl | rfl
      · have h1 := Nat.card_congr e.toEquiv
        rw [hk, card_SL4_two] at h1
        have hk1 := two_pow_eq_one_of_mul k h1
        have heq : autOn K V₀ = autOn (K ⊔ T) V₀ :=
          autOn_eq_of_card_eq (by rw [hk, hk1, hcard, mul_one])
        exact h.not_equiv_SL4 hKV₀ hR hne₀ ⟨(MulEquiv.subgroupCongr heq).trans e⟩
      · have h1 := Nat.card_congr e.toEquiv
        rw [hk, card_SL5_two] at h1
        exact mul_two_pow_ne_9999360 k h1
    · exact h.not_equiv_SL4 hKV₀ hR hne₀ he
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk, card_SL5_two] at h1
      exact mul_two_pow_ne_9999360 k h1
  ·
    obtain ⟨_, hcases⟩ := h329 G T K V₀ hfsu hKK hVeq ⟨hc, hFF⟩
    rcases hcases with ⟨m, -, hl, -⟩ | ⟨m, hSU, -⟩ | ⟨f, hSz, -⟩ |
      ⟨m, F, _, _, _, hm, hF, -, -, -, -, π, hπ, hno⟩ | ⟨⟨e⟩, -⟩ | ⟨-, -, ⟨e⟩, -⟩ |
      ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨e⟩, -⟩
    · have h1 := CFSG.GH74.card_of_lieModel_PSL (by norm_num) hl
      rw [hcard] at h1
      exact ordA_one_ne_20160' _ h1.symm
    · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := BinaryNaturalSU3.exists_equiv hSU
      have hm0 : m ≠ 0 := by
        rintro rfl
        have := Finite.one_lt_card (α := F)
        rw [hF] at this
        norm_num at this
      have : CharP F 2 := Vol2.KGNat.charP_two_of_card (n := m * 2) (by omega)
        (by rw [hF, pow_mul])
      exact card_statedSU_ne_20160 hF ((Nat.card_congr e.toEquiv).trans hcard)
    · obtain ⟨a, F, _, _, ha, hf, hF, ⟨e⟩⟩ := BinaryNaturalSz.exists_equiv hSz
      have hSzM : SuzukiModel ↥(autOn K V₀) 2 f := ⟨rfl, a, ha, F, inferInstance,
        inferInstance, hf, hF, ⟨e.symm⟩⟩
      obtain ⟨-, a', -, hf', hc'⟩ := CFSG.GH74.card_of_suzukiModel hSzM
      rw [hcard] at hc'
      apply not_three_dvd_ordSuzuki (f := f) ⟨a', hf'⟩
      rw [← hc']
      norm_num
    · have hS : IsSylowTwoOf (T ⊓ K) K :=
        A4.isSylowTwoOf_inf_normal (h.hyp.isSylowTwoOf h.hyp.hStar.1.1) (oTwoUpper_le H)
          (le_normalizer_oTwoUpper H)
      exact SL3.not_isDiagramNontrivial_of_noGraph (by omega) hF hKV₀ hTV₀ hTK hS π hπ.1
        (fun g hg => SL3.twistTensor_ker_scalar m hπ g hg) hno (h.isDiagramNontrivial_F4 h510)
    · have h1 := Nat.card_congr e.toEquiv
      rw [hk] at h1
      have h11 := eleven_dvd_card_mulAut_M12
      rw [← h1] at h11
      exact not_dvd_mul_two_pow (by norm_num) (by norm_num) (by norm_num) k h11
    · have h1 := Subgroup.card_quotient_dvd_card (Subgroup.center ↥(autOn K V₀))
      rw [Nat.card_congr e.toEquiv, hcard] at h1
      have h11 := eleven_dvd_card_M22.trans h1
      norm_num at h11
    · have h11 := eleven_dvd_card_M22
      rw [← Nat.card_congr e.toEquiv, hcard] at h11
      norm_num at h11
    · have h23 := twentyThree_dvd_card_M23
      rw [← Nat.card_congr e.toEquiv, hcard] at h23
      norm_num at h23
    · have h23 := twentyThree_dvd_card_M24
      rw [← Nat.card_congr e.toEquiv, hcard] at h23
      norm_num at h23

end Hyp5_1_14

theorem stmt5_1_14_notf_of_F4
    (h510 : Stmt5_1_10_F4) (h5112 : Stmt5_1_12_F4) (h323 : Stmt3_2_3) (h325 : Stmt3_2_5_F4)
    (h328 : Stmt3_2_8) (h329 : Stmt3_2_9C_F4) : Stmt5_1_14_notf_F4 :=
  fun _ _ _ _ _ _ _ _ _ _ _ hyp hN hV hK =>
    (⟨hyp, hN, hV, hK⟩ : Hyp5_1_14 _ _ _ _ _ _ _ _ _).not_faithful_F4 h510 h5112 h323 h325 h328
      h329

end CFSG.Quasithin.H13
