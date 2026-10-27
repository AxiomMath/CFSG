module

public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {Γ : Type} [Group Γ] [Finite Γ]

private def MaxRank (T U : Subgroup Γ) : Prop :=
  ∀ V : Subgroup Γ, V ≤ T → IsMulCommutative V → CFSG.pRank 2 V ≤ CFSG.pRank 2 U

private def IsMaxAb (T U : Subgroup Γ) : Prop :=
  U ≤ T ∧ IsMulCommutative U ∧ MaxRank T U

private lemma thompsonRank_eq_sSup (T : Subgroup Γ) :
    thompsonRank T = sSup {U : Subgroup Γ | IsMaxAb T U} := by
  rw [thompsonRank]
  apply le_antisymm
  · exact iSup_le fun U => iSup_le fun hU => iSup_le fun hc => iSup_le fun hm =>
      le_sSup ⟨hU, hc, hm⟩
  · exact sSup_le fun U hU => le_iSup_of_le U (le_iSup_of_le hU.1 (le_iSup_of_le hU.2.1
      (le_iSup_of_le hU.2.2 le_rfl)))

private lemma isElemAbelian_of_isElemAbelian_top {G : Type*} [Group G] (E : Subgroup G)
    (h : IsElemAbelian 2 (⊤ : Subgroup E)) : IsElemAbelian 2 E := by
  refine ⟨?_, ?_⟩
  · refine IsMulCommutative.of_comm fun a b => ?_
    exact congrArg Subtype.val
      ((isMulCommutative_iff.mp h.1) ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩)
  · intro x hx
    have h2 : (⟨x, hx⟩ : ↥E) ^ 2 = 1 := h.2 ⟨x, hx⟩ (Subgroup.mem_top _)
    simpa using congrArg (fun y : E => (y : G)) h2

private lemma isElemAbelian_inf_left {E W' : Subgroup Γ} (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 (E ⊓ W') := by
  refine ⟨?_, ?_⟩
  · rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    exact congrArg (Subtype.val : ↥E → Γ)
      ((isMulCommutative_iff.mp hE.1) ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩)
  · intro x hx
    exact hE.2 x hx.1

private lemma isElemAbelian_sup_of_le_centralizer {A B : Subgroup Γ}
    (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B)
    (hle : B ≤ Subgroup.centralizer (A : Set Γ)) : IsElemAbelian 2 (A ⊔ B) := by
  haveI hAc : IsElementaryAbelian 2 ↥A :=
    { toIsMulCommutative := hA.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun x => Subtype.ext (hA.2 x.1 x.2)) }
  haveI hBc : IsElementaryAbelian 2 ↥B :=
    { toIsMulCommutative := hB.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun x => Subtype.ext (hB.2 x.1 x.2)) }
  have h : IsElementaryAbelian 2 ↥(A ⊔ B) :=
    IsElementaryAbelian.sup_of_le_centralizer (p := 2) (E := A) (C := B) hle
  exact ⟨h.toIsMulCommutative,
    fun x hx => congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.exponent_dvd_p ⟨x, hx⟩)⟩

private lemma openPRank_eq_of_isElemAbelian_card {E : Subgroup Γ} (hE : IsElemAbelian 2 E)
    {k : ℕ} (hk : Nat.card ↥E = 2 ^ k) : CFSG.Open.pRank 2 E = k := by
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le (p := 2) one_lt_two (H := E) (k := k) fun F hF _ => ?_
    rw [← hk]
    exact Subgroup.card_le_of_le hF
  · exact CFSG.SectionRank.le_pRank (p := 2) (H := E) (E := E) one_lt_two le_rfl hE hk

private lemma card_eq_two_pow_pRank {E : Subgroup Γ} (hE : IsElemAbelian 2 E) :
    Nat.card ↥E = 2 ^ CFSG.Open.pRank 2 E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hEc : IsElementaryAbelian 2 ↥E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
        (fun x => Subtype.ext (hE.2 x.1 x.2)) }
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 ↥E).exists_card_eq
  rw [hk]
  exact congrArg (fun j => 2 ^ j) (openPRank_eq_of_isElemAbelian_card hE hk).symm

theorem y53_jr_abs {W Ab K : Subgroup Γ} (hWn : W.Normal) (hWK : W ⊔ K = ⊤) (hAW : Ab ≤ W)
    (hAb : IsE 4 ↥Ab) (hK : IsE 2 ↥K) (hKA : ∀ k ∈ K, ∀ a ∈ Ab, k * a = a * k)
    (hAK : Ab ⊓ K = ⊥) (hCW : ∀ w ∈ W, (∀ a ∈ Ab, w * a = a * w) → w ∈ Ab)
    (hJ : thompsonRank W = Ab) : thompsonRank (⊤ : Subgroup Γ) = Ab ⊔ K := by
  haveI hWnI : W.Normal := hWn
  have hAb_ea : IsElemAbelian 2 Ab := isElemAbelian_of_isElemAbelian_top Ab hAb.1
  have hK_ea : IsElemAbelian 2 K := isElemAbelian_of_isElemAbelian_top K hK.1
  have hAb_card : Nat.card ↥Ab = 16 := by rw [hAb.2]; norm_num
  have hK_card : Nat.card ↥K = 4 := by rw [hK.2]; norm_num
  have hAb_rank : CFSG.Open.pRank 2 Ab = 4 := by
    apply le_antisymm
    · refine CFSG.SectionRank.pRank_le (p := 2) one_lt_two (H := Ab) (k := 4) fun F hF _ => ?_
      calc Nat.card ↥F ≤ Nat.card ↥Ab := Subgroup.card_le_of_le hF
        _ = 2 ^ 4 := hAb.2
    · exact CFSG.SectionRank.le_pRank (p := 2) (H := Ab) (E := Ab) one_lt_two le_rfl hAb_ea hAb.2
  have hW_rank : CFSG.Open.pRank 2 W = 4 := by
    apply le_antisymm
    · obtain ⟨E, hEW, hEea, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two W
      have hErank : CFSG.Open.pRank 2 E = CFSG.Open.pRank 2 W :=
        le_antisymm (CFSG.SectionRank.pRank_mono one_lt_two hEW)
          (CFSG.SectionRank.le_pRank (p := 2) (H := E) (E := E) one_lt_two le_rfl hEea hEcard)
      have hEmax : IsMaxAb W E := by
        refine ⟨hEW, hEea.1, ?_⟩
        intro V hVW _
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank 2 V,
          CFSG.SectionRank.pRank_coe_eq_openPRank 2 E, hErank]
        exact CFSG.SectionRank.pRank_mono one_lt_two hVW
      have hE_le_Ab : E ≤ Ab := by
        have h1 : E ≤ thompsonRank W := by
          rw [thompsonRank_eq_sSup W]
          exact le_sSup hEmax
        rwa [hJ] at h1
      calc CFSG.Open.pRank 2 W = CFSG.Open.pRank 2 E := hErank.symm
        _ ≤ CFSG.Open.pRank 2 Ab := CFSG.SectionRank.pRank_mono one_lt_two hE_le_Ab
        _ = 4 := hAb_rank
    · calc 4 = CFSG.Open.pRank 2 Ab := hAb_rank.symm
        _ ≤ CFSG.Open.pRank 2 W := CFSG.SectionRank.pRank_mono one_lt_two hAW
  have hD : ∀ V : Subgroup Γ, V ≤ W → IsMulCommutative V → CFSG.Open.pRank 2 V ≤ 4 := by
    intro V hVW _
    calc CFSG.Open.pRank 2 V ≤ CFSG.Open.pRank 2 W := CFSG.SectionRank.pRank_mono one_lt_two hVW
      _ = 4 := hW_rank
  have hEmax_le : ∀ V : Subgroup Γ, V ≤ W → IsMulCommutative V →
      CFSG.Open.pRank 2 V = 4 → V ≤ Ab := by
    intro V hVW hVc hVrank
    have hmax : IsMaxAb W V := by
      refine ⟨hVW, hVc, ?_⟩
      intro V' hV'W _
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank 2 V',
        CFSG.SectionRank.pRank_coe_eq_openPRank 2 V, hVrank]
      calc CFSG.Open.pRank 2 V' ≤ CFSG.Open.pRank 2 W :=
            CFSG.SectionRank.pRank_mono one_lt_two hV'W
        _ = 4 := hW_rank
    have h1 : V ≤ thompsonRank W := by
      rw [thompsonRank_eq_sSup W]
      exact le_sSup hmax
    rwa [hJ] at h1
  have hWind : W.index ≤ 4 := by
    rw [← Subgroup.relIndex_top_right W, ← hWK]
    rw [Subgroup.relIndex_sup_left]
    calc W.relIndex K ≤ Nat.card ↥K :=
          Nat.le_of_dvd (by rw [hK_card]; norm_num)
            (Subgroup.relIndex_dvd_card (H := W) (K := K))
      _ = 4 := hK_card
  have hcard_bound : ∀ E : Subgroup Γ, IsElemAbelian 2 E → Nat.card ↥E ≤ 64 := by
    intro E hEea
    have he_ea : IsElemAbelian 2 (E ⊓ W) := isElemAbelian_inf_left (W' := W) hEea
    have he_le : CFSG.Open.pRank 2 (E ⊓ W) ≤ 4 := hD (E ⊓ W) inf_le_right he_ea.1
    have he_card : Nat.card ↥(E ⊓ W) ≤ 16 := by
      calc Nat.card ↥(E ⊓ W) = 2 ^ CFSG.Open.pRank 2 (E ⊓ W) := card_eq_two_pow_pRank he_ea
        _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) he_le
        _ = 16 := by norm_num
    have hrel : Nat.card ↥E = W.relIndex E * Nat.card ↥(E ⊓ W) := by
      have h := Subgroup.relIndex_mul_card (H := W) (K := E)
      rw [inf_comm] at h
      exact h.symm
    have hrel_le : W.relIndex E ≤ W.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := W)))
        (Subgroup.relIndex_dvd_index_of_normal (H := W) (K := E))
    calc Nat.card ↥E = W.relIndex E * Nat.card ↥(E ⊓ W) := hrel
      _ ≤ W.index * 16 := Nat.mul_le_mul hrel_le he_card
      _ ≤ 4 * 16 := Nat.mul_le_mul_right 16 hWind
      _ = 64 := by norm_num
  have hcard_eq_Ab : ∀ E : Subgroup Γ, IsElemAbelian 2 E → Nat.card ↥E = 64 → E ⊓ W = Ab := by
    intro E hEea hE64
    have he_ea : IsElemAbelian 2 (E ⊓ W) := isElemAbelian_inf_left (W' := W) hEea
    have he_le : CFSG.Open.pRank 2 (E ⊓ W) ≤ 4 := hD (E ⊓ W) inf_le_right he_ea.1
    have he_card : Nat.card ↥(E ⊓ W) ≤ 16 := by
      calc Nat.card ↥(E ⊓ W) = 2 ^ CFSG.Open.pRank 2 (E ⊓ W) := card_eq_two_pow_pRank he_ea
        _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) he_le
        _ = 16 := by norm_num
    have hrel : Nat.card ↥E = W.relIndex E * Nat.card ↥(E ⊓ W) := by
      have h := Subgroup.relIndex_mul_card (H := W) (K := E)
      rw [inf_comm] at h
      exact h.symm
    have hrel_le : W.relIndex E ≤ W.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := W)))
        (Subgroup.relIndex_dvd_index_of_normal (H := W) (K := E))
    have hge16 : 16 ≤ Nat.card ↥(E ⊓ W) := by
      have h1 : W.relIndex E * Nat.card ↥(E ⊓ W) = 64 := by rw [← hrel]; exact hE64
      have h2 : 64 ≤ 4 * Nat.card ↥(E ⊓ W) := by
        rw [← h1]
        exact Nat.mul_le_mul_right _ (hrel_le.trans hWind)
      have h3 : 4 * 16 ≤ 4 * Nat.card ↥(E ⊓ W) := by
        calc 4 * 16 = 64 := by norm_num
          _ ≤ 4 * Nat.card ↥(E ⊓ W) := h2
      exact Nat.le_of_mul_le_mul_left h3 (by norm_num)
    have he16 : Nat.card ↥(E ⊓ W) = 16 := le_antisymm he_card hge16
    have he_rank : CFSG.Open.pRank 2 (E ⊓ W) = 4 :=
      le_antisymm he_le
        (CFSG.SectionRank.le_pRank (p := 2) (H := E ⊓ W) (E := E ⊓ W) one_lt_two le_rfl he_ea
          (by rw [he16]; norm_num))
    have hle : E ⊓ W ≤ Ab := hEmax_le (E ⊓ W) inf_le_right he_ea.1 he_rank
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hAb_card, he16])
  have hcomm_Ab_K : ∀ x ∈ Ab, ∀ y ∈ K, x * y = y * x :=
    fun x hx y hy => (hKA y hy x hx).symm
  have hAbK_card : Nat.card ↥(Ab ⊔ K) = 64 := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Ab K hcomm_Ab_K).1
    rw [hAK, Subgroup.card_bot, mul_one, hAb_card, hK_card] at h
    omega
  have hKcent : K ≤ Subgroup.centralizer (Ab : Set Γ) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hKA k hk a ha).symm
  have hAbK_ea : IsElemAbelian 2 (Ab ⊔ K) :=
    isElemAbelian_sup_of_le_centralizer hAb_ea hK_ea hKcent
  have hAbK_rank : CFSG.Open.pRank 2 (Ab ⊔ K) = 6 := by
    apply le_antisymm
    · refine CFSG.SectionRank.pRank_le (p := 2) one_lt_two (H := Ab ⊔ K) (k := 6) fun F _ hFea => ?_
      have := hcard_bound F hFea
      simpa using this
    · have hc : Nat.card ↥(Ab ⊔ K) = 2 ^ 6 := by rw [hAbK_card]; norm_num
      exact CFSG.SectionRank.le_pRank (p := 2) (H := Ab ⊔ K) (E := Ab ⊔ K) one_lt_two le_rfl
        hAbK_ea hc
  have hTop_rank : CFSG.Open.pRank 2 (⊤ : Subgroup Γ) = 6 := by
    apply le_antisymm
    · refine CFSG.SectionRank.pRank_le (p := 2) one_lt_two (H := ⊤) (k := 6) fun F _ hFea => ?_
      have := hcard_bound F hFea
      simpa using this
    · calc 6 = CFSG.Open.pRank 2 (Ab ⊔ K) := hAbK_rank.symm
        _ ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Γ) := CFSG.SectionRank.pRank_mono one_lt_two le_top
  have hCent_le_AbK : Subgroup.centralizer (Ab : Set Γ) ≤ Ab ⊔ K := by
    intro x hx
    have hxmem : x ∈ W ⊔ K := by rw [hWK]; trivial
    rw [Subgroup.mem_sup_of_normal_left (s := W) (t := K)] at hxmem
    obtain ⟨w, hw, k, hk, rfl⟩ := hxmem
    have hxca : ∀ a ∈ Ab, a * (w * k) = (w * k) * a := fun a ha =>
      (Subgroup.mem_centralizer_iff.mp hx) a ha
    have hw_Ab : w ∈ Ab := by
      apply hCW w hw
      intro a ha
      have hka : k * a = a * k := hKA k hk a ha
      have hkia : k⁻¹ * a = a * k⁻¹ := by
        calc k⁻¹ * a = k⁻¹ * (a * k) * k⁻¹ := by group
          _ = k⁻¹ * (k * a) * k⁻¹ := by rw [← hka]
          _ = a * k⁻¹ := by group
      calc w * a = (w * k) * k⁻¹ * a := by group
        _ = (w * k) * (k⁻¹ * a) := by group
        _ = (w * k) * (a * k⁻¹) := by rw [hkia]
        _ = ((w * k) * a) * k⁻¹ := by group
        _ = (a * (w * k)) * k⁻¹ := by rw [← hxca a ha]
        _ = a * ((w * k) * k⁻¹) := by group
        _ = a * w := by group
    exact Subgroup.mul_mem_sup hw_Ab hk
  apply le_antisymm
  · rw [thompsonRank_eq_sSup]
    refine sSup_le fun U hU => ?_
    have hUrank : CFSG.Open.pRank 2 U = 6 := by
      apply le_antisymm
      · calc CFSG.Open.pRank 2 U ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Γ) :=
              CFSG.SectionRank.pRank_mono one_lt_two le_top
          _ = 6 := hTop_rank
      · have hh := hU.2.2 (Ab ⊔ K) le_top hAbK_ea.1
        rw [CFSG.SectionRank.pRank_coe_eq_openPRank 2 (Ab ⊔ K),
          CFSG.SectionRank.pRank_coe_eq_openPRank 2 U, hAbK_rank] at hh
        exact hh
    obtain ⟨E, hEU, hEea, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 2) one_lt_two U
    have hE64 : Nat.card ↥E = 64 := by rw [hEcard, hUrank]; norm_num
    have hEinf : E ⊓ W = Ab := hcard_eq_Ab E hEea hE64
    have hAbU : Ab ≤ U := by
      have hAbE : Ab ≤ E := by rw [← hEinf]; exact inf_le_left
      exact hAbE.trans hEU
    have hUcent : U ≤ Subgroup.centralizer (Ab : Set Γ) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (congrArg Subtype.val
        ((isMulCommutative_iff.mp hU.2.1) ⟨u, hu⟩ ⟨a, hAbU ha⟩)).symm
    exact hUcent.trans hCent_le_AbK
  · rw [thompsonRank_eq_sSup]
    apply le_sSup
    refine ⟨le_top, hAbK_ea.1, ?_⟩
    intro V _ _
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank 2 V,
      CFSG.SectionRank.pRank_coe_eq_openPRank 2 (Ab ⊔ K)]
    calc CFSG.Open.pRank 2 V ≤ CFSG.Open.pRank 2 (⊤ : Subgroup Γ) :=
          CFSG.SectionRank.pRank_mono one_lt_two le_top
      _ = 6 := hTop_rank
      _ = CFSG.Open.pRank 2 (Ab ⊔ K) := hAbK_rank.symm

end CFSG.OddStandard.HigherRank.YamadaG23
