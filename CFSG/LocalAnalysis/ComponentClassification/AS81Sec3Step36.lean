module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step32
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3G2V

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

namespace Sec3

theorem eq_one_or_eq_of_mem_zpowers {M : Type*} [Group M] {c y : M} (hc : c * c = 1)
    (hy : y ∈ zpowers c) : y = 1 ∨ y = c := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have hc2 : c ^ 2 = 1 := by rw [sq, hc]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [show m + m = 2 * m by ring, zpow_mul, zpow_ofNat, hc2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, hc2, one_zpow, one_mul, zpow_one]

theorem quaternion_central_of_mul_self (q r : QuaternionGroup 2) (hq : q * q = 1) :
    q * r = r * q := by
  revert q r
  decide

theorem zpowers_subgroupOf {M : Type*} [Group M] {C : Subgroup M} (c : ↥C) :
    (zpowers (c : M)).subgroupOf C = zpowers c :=
  (eq_subgroupOf_of_map_eq (MonoidHom.map_zpowers _ c)).symm

end Sec3

open Sec3 in
theorem exists_sec3Q0_model
    {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
    {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U : Subgroup G}
    (hD : Sec3D G A A₁ R g E F x Zs P T Q B₀ z y D J U) :
    ∃ (K : Type) (_ : Field K) (_ : CharP K 2) (_ : Finite K), Nat.card K = 4 ∧
      ∃ f : ↥(adjointGroup .G2 K) →* G, Sec3Model G A A₁ E F x K f ∧
        ∃ (l : K) (t₀ : Kˣ) (h₀ : ↥(adjointGroup .G2 K)), l ≠ 0 ∧ t₀ ≠ 1 ∧
          torusElt .G2 K g2ir t₀ = (h₀ : ModGL .G2 K) ∧ f h₀ = x ∧
          D = ((g2ShortParabolicRadical K).subgroupOf (adjointGroup .G2 K)).map f ∧
          Sec3Q0 G A A₁ R g E F x Zs P T Q B₀ z y D J U
            (((G2.g2V0 K).subgroupOf (adjointGroup .G2 K)).map f)
            (((G2.g2V K).subgroupOf (adjointGroup .G2 K)).map f)
            (((G2.g2Q0 K l).subgroupOf (adjointGroup .G2 K)).map f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSz := hD.suz
  have hS := hSz.setting
  obtain ⟨hEA, -, -, -, hE16, -, -, hSyl, hS64⟩ := frame_inf_A₁ hS
  obtain ⟨K, _, _, _, hK, f, hM⟩ := exists_sec3Model hS
  have hfinj := hM.inj
  have hD₀C : g2ShortParabolicRadical K ≤ adjointGroup .G2 K :=
    G2.g2ShortParabolicRadical_le_adjointGroup
  have hLaC : g2RankOne K g2ia ≤ adjointGroup .G2 K := g2RankOne_le_adjointGroup g2ia
  have hHrC : g2TorusR K ≤ adjointGroup .G2 K := G2.g2TorusR_le_adjointGroup
  have hZ₀C : g2BCGroup K ≤ adjointGroup .G2 K :=
    G2.g2BCGroup_le_g2ShortParabolicRadical.trans hD₀C
  have hPC : G2.g2Para K ≤ adjointGroup .G2 K := sup_le (sup_le hD₀C hLaC) hHrC
  have hV0C : G2.g2V0 K ≤ adjointGroup .G2 K := G2.g2V0_le_g2ShortParabolicRadical.trans hD₀C
  have hVC : G2.g2V K ≤ adjointGroup .G2 K := G2.g2V_le_g2V0.trans hV0C
  have hLPC : G2.g2LongPos K ≤ adjointGroup .G2 K :=
    G2.g2LongPos_le_g2LongA2.trans g2LongA2_le_adjointGroup
  have hACC : G2.g2ACGroup K ≤ adjointGroup .G2 K := G2.g2ACGroup_le_g2LongPos.trans hLPC
  have hDf : D = ((g2ShortParabolicRadical K).subgroupOf (adjointGroup .G2 K)).map f := by
    rw [hD.D_eq, hM.I_eq, tr_pCoreOf hfinj hPC, G2.pCoreOf_g2Para hK]
  have hUL : ((G2.g2LongPos K).subgroupOf (adjointGroup .G2 K)).map f = (E ⊔ F) ⊓ A₁ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · have h1 : G2.g2LongPos K ≤ g2BCGroup K ⊔ G2.g2ACGroup K := by
        rintro _ ⟨B, E', F', rfl⟩
        rw [show g2N 0 B 0 0 E' F' = g2N 0 0 0 0 E' 0 * g2N 0 B 0 0 0 (F' + B * E') by
          rw [g2N_zero_mul_g2N_zero]
          exact g2N_eq_g2N rfl (by ring) (by ring) (by ring) (by ring) (by char2_ring)]
        exact mul_mem_sup ⟨E', 0, rfl⟩ ⟨B, F' + B * E', rfl⟩
      refine (tr_mono h1).trans ?_
      rw [tr_sup hZ₀C hACC, hM.E_eq, hM.F_eq, hEA]
      exact sup_le (inf_le_inf_right _ le_sup_left) (inf_le_inf_right _ le_sup_right)
    · rw [hS64, card_map_of_injective hfinj, Nat.card_congr (subgroupOfEquivOfLe hLPC).toEquiv,
        G2.card_g2LongPos, hK]
      norm_num
  have hx : x ∈ ((g2TorusR K).subgroupOf (adjointGroup .G2 K)).map f := by
    rw [hM.x_eq]
    exact mem_zpowers x
  obtain ⟨h₀, hh₀, hfh₀⟩ := hx
  obtain ⟨t₀, ht₀⟩ := mem_subgroupOf.mp hh₀
  have ht₀1 : t₀ ≠ 1 := by
    rintro rfl
    have h1 : h₀ = 1 := Subtype.ext (by rw [← ht₀, map_one]; rfl)
    have h2 := hS.order_x
    rw [← hfh₀, h1, map_one, orderOf_one] at h2
    norm_num at h2
  have hJA₁ : J ≤ A₁ := by
    intro j hj
    have hjA : j ∈ A := (hD.J_le hj).1
    rw [← hM.range_eq] at hjA
    obtain ⟨c, rfl⟩ := hjA
    have hjx : f c * x = x * f c := mem_centralizer_singleton_iff.mp (hD.J_comm hj)
    have hcH : (c : ModGL .G2 K) ∈ centralizer (g2TorusR K : Set (ModGL .G2 K)) := by
      rw [mem_centralizer_iff]
      intro h hh
      have h1 : f ⟨h, hHrC hh⟩ ∈ zpowers x := by
        rw [← hM.x_eq]
        exact ⟨⟨h, hHrC hh⟩, mem_subgroupOf.mpr hh, rfl⟩
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
      have h2 : f (⟨h, hHrC hh⟩ * c) = f (c * ⟨h, hHrC hh⟩) := by
        rw [map_mul, map_mul, ← hk]
        exact ((Commute.zpow_right (hjx : Commute (f c) x) k).eq).symm
      exact congrArg Subtype.val (hfinj h2)
    have hcL : (c : ModGL .G2 K) ∈ g2LongA2 K := by
      rw [← g2Centralizer_g2TorusR_eq_g2LongA2 hK]
      exact ⟨c.2, hcH⟩
    rw [← hM.A₁_eq]
    exact ⟨c, mem_subgroupOf.mpr hcL, rfl⟩
  have hET : E ≤ T := by
    have hxA₁ : x ∈ centerIn A₁ := by
      rw [hS.center_A₁]
      exact mem_zpowers x
    have hA₁B : A₁ ≤ sec3B A₁ x := fun a ha =>
      ⟨⟨a, mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxA₁.2 a ha)⟩,
        subset_normalClosure (mem_subgroupOf.mpr ha), rfl⟩
    have hEB : E ≤ sec3B A₁ x := hS.frame.E_le.trans (sup_le hA₁B hSz.R_le)
    have hE2 : IsPGroup 2 E := fun e => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hS.frame.elemE.2 _ e.2)⟩
    refine (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (le_inf hEB le_normalizer)
      inf_le_right hE2).trans ?_
    rw [← hSz.P_eq]
    exact hSz.P_le
  have hTA₁ : T ⊓ A₁ = (E ⊔ F) ⊓ A₁ :=
    hSyl.eq_of_le (inf_le_inf_right _ (sup_le hET hSz.F_le)) inf_le_right
      (hSz.T_two.to_le inf_le_left)
  have hT₁ : T ⊓ J ≤ ((G2.g2LongPos K).subgroupOf (adjointGroup .G2 K)).map f := by
    rw [hUL, ← hTA₁]
    exact inf_le_inf_left _ hJA₁
  obtain ⟨eJ⟩ := hD.J_iso
  obtain ⟨-, -, -, -, -, -, -, ⟨ρ, -, -, hρrange, hρinj⟩, -⟩ :=
    even_G2_highest_short_root_centralizer K
  let eρ : LieType.Chevalley.SL2 K ≃* ↥(g2RankOne K g2ia) :=
    (MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hρrange)
  let _ : Fintype K := Fintype.ofFinite K
  let _ : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card K = Fintype.card (GaloisField 2 2) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card 2 2
      (by norm_num)]
    norm_num
  let eJL : ↥J ≃* ↥(g2RankOne K g2ia) :=
    eJ.trans ((slTwoMapEquiv (FiniteField.ringEquivOfCardEq hcard)).symm.trans eρ)
  have hLa60 : Nat.card (g2RankOne K g2ia) = 60 := by
    rw [← Nat.card_congr eρ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK]
    norm_num
  have hJ60 : Nat.card J = 60 := by rw [Nat.card_congr eJL.toEquiv, hLa60]
  obtain ⟨-, hsimp, -⟩ := g2RankOne_isPerfect_isSimpleGroup (K := K) (by rw [hK])
  have hsimpJ : IsSimpleGroup ↥J := eJL.isSimpleGroup
  have hJEA : J ⊓ (E ⊓ A) = ⊥ := by
    have hN : ((E ⊓ A).subgroupOf J).Normal := ⟨fun n hn j => by
      rw [mem_subgroupOf] at hn ⊢
      have h1 := (mem_normalizer_iff.mp (hD.J_le j.2).2 n).mp hn
      simpa using h1⟩
    have := hN
    rcases hsimpJ.eq_bot_or_eq_top_of_normal ((E ⊓ A).subgroupOf J) with h | h
    · rw [eq_bot_iff]
      rintro w ⟨hwJ, hwE⟩
      have h1 : (⟨w, hwJ⟩ : ↥J) ∈ (E ⊓ A).subgroupOf J := mem_subgroupOf.mpr hwE
      rw [h, mem_bot] at h1
      exact congrArg Subtype.val h1
    · exfalso
      have hJE : J ≤ E ⊓ A := fun w hw => by
        have h1 : (⟨w, hw⟩ : ↥J) ∈ (E ⊓ A).subgroupOf J := by
          rw [h]
          exact mem_top _
        exact mem_subgroupOf.mp h1
      have hdvd := Subgroup.card_dvd_of_le hJE
      rw [hJ60, hEA, hE16] at hdvd
      norm_num at hdvd
  have hT₁4 : Nat.card ↥(T ⊓ J) = 4 := by
    rw [hD.T₁_sylow.card_eq, hJ60]
    have h1 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
    rw [h1, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by decide)]
    norm_num
  obtain ⟨⟨t₁, ht₁⟩, ht₁1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := T ⊓ J)).mp (fun h => by
    rw [h, Subgroup.card_bot] at hT₁4
    norm_num at hT₁4)
  have ht₁E : t₁ ∉ E ⊓ A := fun h => ht₁1 (Subtype.ext (by
    have h1 : t₁ ∈ J ⊓ (E ⊓ A) := ⟨ht₁.2, h⟩
    rw [hJEA, mem_bot] at h1
    exact h1))
  have hzZs : z ∈ A₁ ⊓ ((E ⊔ F) ⊓ centralizer ((E ⊔ F : Subgroup G) : Set G)) := by
    have h := hSz.z_mem
    rw [hSz.Zs_eq] at h
    exact h
  obtain ⟨hzA₁, hzEF, hzc⟩ := hzZs
  have hzUL : z ∈ ((G2.g2LongPos K).subgroupOf (adjointGroup .G2 K)).map f := by
    rw [hUL]
    exact ⟨hzEF, hzA₁⟩
  obtain ⟨b, hb, hfb⟩ := hzUL
  have hXa1 : g2N 0 1 0 0 0 0 ∈ adjointGroup .G2 K := hACC ⟨1, 0, rfl⟩
  have hXb1 : g2N 0 0 0 0 1 0 ∈ adjointGroup .G2 K := hZ₀C ⟨1, 0, rfl⟩
  have hfa : f ⟨_, hXa1⟩ ∈ E ⊔ F := by
    have h1 : f ⟨_, hXa1⟩ ∈ F ⊓ A₁ := by
      rw [← hM.F_eq]
      exact ⟨⟨_, hXa1⟩, mem_subgroupOf.mpr ⟨1, 0, rfl⟩, rfl⟩
    exact mem_sup_right h1.1
  have hfb' : f ⟨_, hXb1⟩ ∈ E ⊔ F := by
    have h1 : f ⟨_, hXb1⟩ ∈ E ⊓ A := by
      rw [← hM.E_eq]
      exact ⟨⟨_, hXb1⟩, mem_subgroupOf.mpr ⟨1, 0, rfl⟩, rfl⟩
    exact mem_sup_left h1.1
  have hcomm : ∀ {w : ↥(adjointGroup .G2 K)}, f w ∈ E ⊔ F → (b : ModGL .G2 K) * w = w * b := by
    intro w hw
    have h1 := mem_centralizer_iff.mp hzc _ hw
    rw [← hfb, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (hfinj h1).symm
  obtain ⟨l, hl⟩ := G2.eq_g2N_c_of_mem_g2LongPos (mem_subgroupOf.mp hb)
    (hcomm (w := ⟨_, hXa1⟩) hfa) (hcomm (w := ⟨_, hXb1⟩) hfb')
  have hz1 : z ≠ 1 := by
    rintro rfl
    have h1 := card_centerIn_of_extraspecial hSz.q8.1
    rw [hSz.Q_center, zpowers_one_eq_bot, Subgroup.card_bot] at h1
    norm_num at h1
  have hl0 : l ≠ 0 := by
    rintro rfl
    apply hz1
    rw [← hfb, show b = 1 from Subtype.ext (by rw [hl, g2N_zero]; rfl), map_one]
  have hQ0C : G2.g2Q0 K l ≤ adjointGroup .G2 K := (G2.g2Q0_le_g2V l).trans hVC
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, f, hM, l, t₀, h₀, hl0, ht₀1, ht₀,
    hfh₀, hDf, hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    ext d
    simp only [SetLike.mem_coe, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨hDf ▸ tr_mono G2.g2V0_le_g2ShortParabolicRadical ⟨a, ha, rfl⟩, fun t ht => ?_⟩
      obtain ⟨b', hb', rfl⟩ := hT₁ ht
      rw [← hM.E_eq, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      exact ⟨_, mem_subgroupOf.mpr (G2.commutator_mem_g2BCGroup_of_mem_g2V0 (mem_subgroupOf.mp ha)
        (mem_subgroupOf.mp hb')), rfl⟩
    · rintro ⟨hdD, hd⟩
      rw [hDf] at hdD
      obtain ⟨a, ha, rfl⟩ := hdD
      obtain ⟨b', hb', hfb'⟩ := hT₁ ht₁
      have h1 := hd t₁ ht₁
      rw [← hfb', ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← hM.E_eq,
        mem_map_iff_mem hfinj, mem_subgroupOf] at h1
      have hbZ : (b' : ModGL .G2 K) ∉ g2BCGroup K := fun hbZ => ht₁E (by
        rw [← hfb', ← hM.E_eq]
        exact ⟨b', mem_subgroupOf.mpr hbZ, rfl⟩)
      exact ⟨a, mem_subgroupOf.mpr (G2.mem_g2V0_of_commutator_mem (mem_subgroupOf.mp ha)
        (mem_subgroupOf.mp hb') hbZ h1), rfl⟩
  ·
    rw [← hM.x_eq, ← tr_commutator hV0C hHrC, G2.commutator_g2V0_g2TorusR hK]
  ·
    exact tr_mono (G2.g2Q0_le_g2V l)
  ·
    rw [← hfh₀]
    have hn : (h₀ : ModGL .G2 K) ∈ adjointGroup .G2 K ⊓
        normalizer (G2.g2Q0 K l : Set (ModGL .G2 K)) := by
      refine ⟨h₀.2, ?_⟩
      rw [← ht₀]
      exact G2.torusElt_mem_normalizer_g2Q0 hK l t₀
    exact ((tr_normalizer hfinj hQ0C).ge ⟨h₀, mem_subgroupOf.mpr hn, rfl⟩).2
  ·
    obtain ⟨e⟩ := G2.g2Q0_quaternion hK hl0
    exact ⟨((((G2.g2Q0 K l).subgroupOf (adjointGroup .G2 K)).equivMapOfInjective f
      hfinj).symm.trans (subgroupOfEquivOfLe hQ0C)).trans e⟩
  ·
    rw [hSz.Q_center, tr_centerIn hfinj hQ0C,
      show centerIn (G2.g2Q0 K l) = zpowers (g2N 0 0 0 0 0 l) from G2.centerIn_g2Q0 hK hl0, ← hl,
      zpowers_subgroupOf, MonoidHom.map_zpowers, hfb]
  ·
    intro Q' hQ'V hxQ' ⟨e'⟩ hcQ'
    have hQ'A : Q' ≤ f.range := hQ'V.trans (map_le_range _ _)
    set Y : Subgroup (ModGL .G2 K) := (Q'.comap f).map (adjointGroup .G2 K).subtype with hYdef
    have hYC : Y ≤ adjointGroup .G2 K := map_subtype_le _
    have hYsub : Y.subgroupOf (adjointGroup .G2 K) = Q'.comap f :=
      comap_map_eq_self_of_injective (adjointGroup .G2 K).subtype_injective _
    have hQ'Y : Q' = (Y.subgroupOf (adjointGroup .G2 K)).map f := by
      rw [hYsub, map_comap_eq, inf_eq_right.mpr hQ'A]
    have hYV : Y ≤ G2.g2V K := by
      rintro _ ⟨w, hw, rfl⟩
      have h1 : f w ∈ ((G2.g2V K).subgroupOf (adjointGroup .G2 K)).map f := hQ'V hw
      rw [mem_map_iff_mem hfinj, mem_subgroupOf] at h1
      exact h1
    have hN : torusElt .G2 K g2ir t₀ ∈ normalizer (Y : Set (ModGL .G2 K)) := by
      have hxinv : x⁻¹ ∈ normalizer (Q' : Set G) := inv_mem hxQ'
      refine G2.mem_normalizer_of_conj (fun w hw => ?_) (fun w hw => ?_)
      · obtain ⟨w', hw', rfl⟩ := hw
        refine ⟨h₀ * w' * h₀⁻¹, ?_, by
          rw [show torusElt .G2 K g2ir t₀ = (h₀ : ModGL .G2 K) from ht₀]
          rfl⟩
        show f (h₀ * w' * h₀⁻¹) ∈ Q'
        rw [map_mul, map_mul, map_inv, hfh₀]
        exact (mem_normalizer_iff.mp hxQ' _).mp hw'
      · obtain ⟨w', hw', rfl⟩ := hw
        refine ⟨h₀⁻¹ * w' * h₀, ?_, by
          rw [show torusElt .G2 K g2ir t₀ = (h₀ : ModGL .G2 K) from ht₀]
          rfl⟩
        show f (h₀⁻¹ * w' * h₀) ∈ Q'
        rw [map_mul, map_mul, map_inv, hfh₀]
        have h1 := (mem_normalizer_iff.mp hxinv _).mp hw'
        rwa [inv_inv] at h1
    have h8 : Nat.card Y = 8 := by
      have h1 : Nat.card Q' = 8 := by
        rw [Nat.card_congr e'.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
      rw [hQ'Y, card_map_of_injective hfinj, Nat.card_congr (subgroupOfEquivOfLe hYC).toEquiv]
        at h1
      exact h1
    have hinv : ∀ w ∈ Y, w * w = 1 → w = 1 ∨ w = g2N 0 0 0 0 0 l := by
      rintro _ ⟨w, hw, rfl⟩ hww
      have hfw : f w ∈ Q' := hw
      have hcent : f w ∈ centerIn Q' := by
        refine ⟨hfw, mem_centralizer_iff.mpr fun q hq => ?_⟩
        have hww' : (⟨f w, hfw⟩ : ↥Q') * ⟨f w, hfw⟩ = 1 := Subtype.ext (by
          rw [Subgroup.coe_mul, ← map_mul, Subgroup.coe_one,
            show w * w = 1 from Subtype.ext hww, map_one])
        have h1 := quaternion_central_of_mul_self (e' ⟨f w, hfw⟩) (e' ⟨q, hq⟩)
          (by rw [← map_mul, hww', map_one])
        rw [← map_mul, ← map_mul] at h1
        exact congrArg Subtype.val (e'.injective h1).symm
      rw [hcQ', hSz.Q_center, ← hfb, ← MonoidHom.map_zpowers, mem_map_iff_mem hfinj] at hcent
      have hbb : b * b = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, hl, G2.g2N_uv_mul, Subgroup.coe_one, ← g2N_zero]
        exact g2N_eq_g2N rfl rfl (by ring) (by ring) (by ring) (by char2_ring))
      rcases eq_one_or_eq_of_mem_zpowers hbb hcent with h | h
      · left
        rw [h]
        rfl
      · right
        rw [h]
        exact hl
    rw [hQ'Y, G2.eq_g2Q0 hK hl0 ht₀1 hYV hN h8 hinv]

theorem step36_of :
    Step36 := by
  intro G _ _ A A₁ R g E F x Zs P T Q B₀ z y D J U hD
  obtain ⟨K, _, _, _, -, f, -, l, -, -, -, -, -, -, -, hQ⟩ := exists_sec3Q0_model hD
  exact ⟨_, _, _, hQ⟩

end CFSG.ComponentClassification.AS81
