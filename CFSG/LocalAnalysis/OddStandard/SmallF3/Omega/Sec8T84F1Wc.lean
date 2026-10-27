module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Wr
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {T1 T2 : Subgroup G}

private lemma local_mem_sup_of_le_normalizer {H K : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) {x : G} :
    x ∈ H ⊔ K ↔ ∃ a ∈ H, ∃ b ∈ K, a * b = x := by
  have hconj : ∀ a ∈ H, ∀ b ∈ K, a * b * a⁻¹ ∈ K :=
    Subgroup.le_normalizer_iff.mp hHK
  constructor
  · intro hx
    let P : Subgroup G :=
      { carrier := {x | ∃ a ∈ H, ∃ b ∈ K, a * b = x}
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
        mul_mem' := by
          rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
          exact ⟨a * c, H.mul_mem ha hc, (c⁻¹ * b * c) * d,
            K.mul_mem (by simpa using hconj c⁻¹ (H.inv_mem hc) b hb) hd, by group⟩
        inv_mem' := by
          rintro x ⟨a, ha, b, hb, rfl⟩
          exact ⟨a⁻¹, H.inv_mem ha, a * b⁻¹ * a⁻¹, hconj a ha b⁻¹ (K.inv_mem hb),
            by group⟩ }
    have hHP : H ≤ P := fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩
    have hKP : K ≤ P := fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩
    exact SetLike.le_def.mp (sup_le hHP hKP) hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

private lemma local_zpowers_inf_eq_bot_of_notMem {C : Subgroup G}
    (ht : t ∉ C) (hcard : Nat.card ↥(zpowers t) = 2) : zpowers t ⊓ C = ⊥ := by
  haveI : Fact (Nat.card ↥(zpowers t)).Prime := ⟨by rw [hcard]; exact Nat.prime_two⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (C.subgroupOf (zpowers t)) with h | h
  · have hd : Disjoint C (zpowers t) := Subgroup.subgroupOf_eq_bot.mp h
    rw [Subgroup.disjoint_def] at hd
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    exact hd hx.2 hx.1
  · exact absurd ((Subgroup.subgroupOf_eq_top.mp h) (Subgroup.mem_zpowers t)) ht

private lemma local_mem_diag_map {d : ↥T1 →* G} {R : Subgroup G} {a : G} (ha : a ∈ T1) :
    a ∈ (R.comap d).map T1.subtype ↔ d ⟨a, ha⟩ ∈ R := by
  constructor
  · intro h
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp h
    have hb' : b = ⟨a, ha⟩ := Subtype.ext hba
    rw [hb', Subgroup.mem_comap] at hb
    exact hb
  · intro h
    exact Subgroup.mem_map.mpr ⟨⟨a, ha⟩, Subgroup.mem_comap.mpr h, rfl⟩

theorem sec8t84_wr_card_cent_T (W : Sec8T84Wr G t T1 T2) (ht : t ∉ T1 ⊔ T2) :
    Nat.card ↥((zpowers t ⊔ (T1 ⊔ T2)) ⊓ centralizer ({t} : Set G)) = 2 * Nat.card T1 := by
  set T0 : Subgroup G := T1 ⊔ T2 with hT0
  have ht0 : t ∉ T0 := by rw [hT0]; exact ht
  have ht_ne : t ≠ 1 := fun h => ht0 (by simpa [h] using Subgroup.one_mem T0)
  have h2 : Nat.card ↥(zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact W.t_sq) ht_ne
  have hconj : ∀ e ∈ T0, t * e * t⁻¹ ∈ T0 := fun e he => by
    rw [hT0] at he ⊢
    exact sec8t84_wr_conj_mem W he
  have hN : t ∈ normalizer (T0 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    exact ⟨fun he => hconj e he, fun he => by
      have h := hconj (t * e * t⁻¹) he
      rwa [show t * (t * e * t⁻¹) * t⁻¹ = e by
        have hsinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right W.t_sq
        calc t * (t * e * t⁻¹) * t⁻¹ = (t * t) * e * (t⁻¹ * t⁻¹) := by group
          _ = e := by rw [W.t_sq, hsinv, W.t_sq]; group] at h⟩
  have hzpN : zpowers t ≤ Subgroup.normalizer (T0 : Set G) := Subgroup.zpowers_le.mpr hN
  have hbot : zpowers t ⊓ T0 = ⊥ := local_zpowers_inf_eq_bot_of_notMem ht0 h2
  have hcent_t : zpowers t ≤ centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hEq : (zpowers t ⊔ T0) ⊓ centralizer ({t} : Set G) =
      zpowers t ⊔ (T0 ⊓ centralizer ({t} : Set G)) := by
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · intro x hx
      obtain ⟨hxK, hxY⟩ := Subgroup.mem_inf.mp hx
      obtain ⟨a, ha, b, hb, hab⟩ := (local_mem_sup_of_le_normalizer hzpN).mp hxK
      have ha_c : a ∈ centralizer ({t} : Set G) := hcent_t ha
      have hb_c : b ∈ centralizer ({t} : Set G) := by
        have hb_eq : b = a⁻¹ * x := by rw [← hab]; group
        rw [hb_eq]
        exact mul_mem (inv_mem ha_c) hxY
      rw [← hab]
      exact Subgroup.mul_mem_sup ha (Subgroup.mem_inf.mpr ⟨hb, hb_c⟩)
    · exact fun a ha => Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left ha, hcent_t ha⟩
    · exact fun b hb => Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hb.1, hb.2⟩
  have hc : ∀ a ∈ zpowers t,
      ∀ b ∈ T0 ⊓ centralizer ({t} : Set G), a * b = b * a := by
    intro a ha b hb
    have hb_comm : b * t = t * b := Subgroup.mem_centralizer_singleton_iff.mp hb.2
    have hle : zpowers t ≤ centralizer ({b} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hb_comm.symm)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  have hd : zpowers t ⊓ (T0 ⊓ centralizer ({t} : Set G)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx' : x ∈ zpowers t ⊓ T0 := ⟨hx.1, hx.2.1⟩
    rwa [hbot] at hx'
  rw [hEq, sec124_card_sup hc hd, h2, hT0, sec8t84_wr_card_cent W]

theorem sec8t84_wr_elem_cent (W : Sec8T84Wr G t T1 T2) {R : Subgroup G}
    (hR : R ≤ (T1 ⊔ T2) ⊓ centralizer ({t} : Set G)) (he : CFSG.Open.IsElemAbelian 2 R) :
    ∃ R1 : Subgroup G, R1 ≤ T1 ∧ CFSG.Open.IsElemAbelian 2 R1 ∧ Nat.card R1 = Nat.card R ∧
      (∀ x ∈ R, ∃ a ∈ R1, x = a * (t * a * t⁻¹)) ∧ ∀ a ∈ R1, a * (t * a * t⁻¹) ∈ R := by
  let d : ↥T1 →* G :=
    { toFun := fun a => (a : G) * (t * a * t⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        have hta : t * (a : G) * t⁻¹ ∈ T2 := W.swap1 a a.2
        have hcomm : (t * (a : G) * t⁻¹) * (b : G) =
            (b : G) * (t * (a : G) * t⁻¹) :=
          (W.comm (b : G) b.2 (t * (a : G) * t⁻¹) hta).symm
        show ((a : G) * (b : G)) * (t * ((a : G) * (b : G)) * t⁻¹) =
          ((a : G) * (t * (a : G) * t⁻¹)) * ((b : G) * (t * (b : G) * t⁻¹))
        rw [show t * ((a : G) * (b : G)) * t⁻¹ =
          (t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹) from by group]
        calc ((a : G) * (b : G)) * ((t * (a : G) * t⁻¹) * (t * (b : G) * t⁻¹))
            = (a : G) * ((b : G) * (t * (a : G) * t⁻¹)) *
                (t * (b : G) * t⁻¹) := by group
          _ = (a : G) * ((t * (a : G) * t⁻¹) * (b : G)) *
                (t * (b : G) * t⁻¹) := by rw [← hcomm]
          _ = ((a : G) * (t * (a : G) * t⁻¹)) *
                ((b : G) * (t * (b : G) * t⁻¹)) := by group }
  have hd_inj : Function.Injective d := fun a b h =>
    Subtype.ext (sec8t84_wr_diag_inj W a.2 b.2 h)
  let R1 : Subgroup G := (R.comap d).map T1.subtype
  have hR1_le : R1 ≤ T1 := by
    intro x hx
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact a.2
  have hR1_mem : ∀ {a : G} (ha : a ∈ T1), a ∈ R1 ↔ d ⟨a, ha⟩ ∈ R :=
    fun ha => local_mem_diag_map (d := d) (R := R) ha
  have hda_mem : ∀ {a : G} (ha : a ∈ R1), d ⟨a, hR1_le ha⟩ ∈ R :=
    fun ha => (hR1_mem (hR1_le ha)).mp ha
  have hcard : Nat.card R1 = Nat.card R := by
    rw [Subgroup.card_subtype T1 (R.comap d)]
    refine Nat.card_congr (Equiv.ofBijective
      (fun b : ↥(R.comap d) => (⟨d (b : ↥T1), Subgroup.mem_comap.mp b.2⟩ : ↥R))
      ⟨?_, ?_⟩)
    · intro b1 b2 h
      exact Subtype.ext (hd_inj (Subtype.ext_iff.mp h))
    · intro y
      obtain ⟨a, ha, hya⟩ := (sec8t84_wr_mem_cent W).mp (hR y.2)
      have hda : d ⟨a, ha⟩ ∈ R := by
        change a * (t * a * t⁻¹) ∈ R
        rw [← hya]
        exact y.2
      refine ⟨⟨⟨a, ha⟩, Subgroup.mem_comap.mpr hda⟩, ?_⟩
      exact Subtype.ext hya.symm
  have hsq : ∀ a ∈ R1, a * a = 1 := by
    intro a ha
    have h1 : d ⟨a, hR1_le ha⟩ * d ⟨a, hR1_le ha⟩ = 1 :=
      CFSG.Open.IsElemAbelian.mul_self_eq_one he (hda_mem ha)
    have hkey : d ⟨a * a, T1.mul_mem (hR1_le ha) (hR1_le ha)⟩ = d 1 := by
      rw [map_one]
      have hmul : (⟨a, hR1_le ha⟩ * ⟨a, hR1_le ha⟩ : ↥T1) =
          ⟨a * a, T1.mul_mem (hR1_le ha) (hR1_le ha)⟩ := rfl
      rw [← hmul, map_mul, h1]
    exact congrArg Subtype.val (hd_inj hkey)
  have hcommR1 : ∀ a ∈ R1, ∀ b ∈ R1, a * b = b * a := by
    intro a ha b hb
    have hkey : d ⟨a * b, T1.mul_mem (hR1_le ha) (hR1_le hb)⟩ =
        d ⟨b * a, T1.mul_mem (hR1_le hb) (hR1_le ha)⟩ := by
      have hmul1 : (⟨a, hR1_le ha⟩ * ⟨b, hR1_le hb⟩ : ↥T1) =
          ⟨a * b, T1.mul_mem (hR1_le ha) (hR1_le hb)⟩ := rfl
      have hmul2 : (⟨b, hR1_le hb⟩ * ⟨a, hR1_le ha⟩ : ↥T1) =
          ⟨b * a, T1.mul_mem (hR1_le hb) (hR1_le ha)⟩ := rfl
      rw [← hmul1, ← hmul2, map_mul, map_mul,
        CFSG.Open.IsElemAbelian.comm he (hda_mem ha) (hda_mem hb)]
    exact congrArg Subtype.val (hd_inj hkey)
  have heR1 : CFSG.Open.IsElemAbelian 2 R1 :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommR1 a a.2 b b.2)⟩⟩, fun x hx => by
      rw [pow_two]
      exact hsq x hx⟩
  refine ⟨R1, hR1_le, heR1, hcard, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := (sec8t84_wr_mem_cent W).mp (hR hx)
    have hda : d ⟨a, ha⟩ ∈ R := by
      change a * (t * a * t⁻¹) ∈ R
      rw [← hxa]
      exact hx
    exact ⟨a, (hR1_mem ha).mpr hda, hxa⟩
  · intro a ha
    change a * (t * a * t⁻¹) ∈ R
    exact (hR1_mem (hR1_le ha)).mp ha

section TData

variable {E T V1 V2 F1 F2 : Subgroup G}

theorem sec8t84_card_cent_t (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) :
    Nat.card ↥(T ⊓ centralizer ({t} : Set G)) = 2 ^ 8 := by
  rw [D.T_eq, sec8t84_wr_card_cent_T D.wr D.t_not, D.mod1.card]
  norm_num

theorem sec8t84_cent_E16_le_E0 (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {B' : Subgroup G}
    (hB' : B' ≤ (T1 ⊔ T2) ⊓ centralizer ({t} : Set G)) (h16 : IsElemAb2 B' 4)
    (hne : B' ≠ E ⊓ centralizer ({t} : Set G)) : B' ≤ F1 ⊔ F2 := by
  obtain ⟨R1, hR1_le, hR1_elem, hR1_card, hdiag, hdiag_mem⟩ :=
    sec8t84_wr_elem_cent D.wr hB' h16.1
  have hR1_16 : IsElemAb2 R1 4 := ⟨hR1_elem, by rw [hR1_card, h16.2]⟩
  have hV1T1 : V1 ≤ T1 := D.mod1.V_le
  have hV2T2 : V2 ≤ T2 := by
    intro x hx
    rw [D.V2_eq] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [MulAut.conj_apply] using D.swap1 a (hV1T1 ha)
  have hE_T0 : E ≤ T1 ⊔ T2 := by
    rw [D.E_eq]
    exact sup_le (hV1T1.trans le_sup_left) (hV2T2.trans le_sup_right)
  have hcommV : ∀ p ∈ V1, ∀ q ∈ V2, p * q = q * p :=
    fun p hp q hq => D.comm p (hV1T1 hp) q (hV2T2 hq)
  have hV1N : V1 ≤ Subgroup.normalizer (V2 : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp q hq
    rw [hcommV p hp q hq]
    simpa using hq
  rcases D.mod1.only R1 hR1_le hR1_16 with hR1V | hR1F
  · have hB'_le : B' ≤ E ⊓ centralizer ({t} : Set G) := by
      intro x hx
      obtain ⟨a, haR1, hxa⟩ := hdiag x hx
      have haV1 : a ∈ V1 := by rw [← hR1V]; exact haR1
      have htaV2 : t * a * t⁻¹ ∈ V2 := by
        rw [D.V2_eq]
        exact Subgroup.mem_map.mpr ⟨a, haV1, by simp [MulAut.conj_apply]⟩
      refine Subgroup.mem_inf.mpr ⟨?_, (hB' hx).2⟩
      rw [hxa, D.E_eq]
      exact Subgroup.mul_mem_sup haV1 htaV2
    have hEcent_le : E ⊓ centralizer ({t} : Set G) ≤ B' := by
      intro y hy
      obtain ⟨hyE, hyC⟩ := Subgroup.mem_inf.mp hy
      have hyT0 : y ∈ T1 ⊔ T2 := hE_T0 hyE
      obtain ⟨a, haT1, hya⟩ := (sec8t84_wr_mem_cent D.wr).mp
        (Subgroup.mem_inf.mpr ⟨hyT0, hyC⟩)
      rw [D.E_eq] at hyE
      obtain ⟨v1, hv1, v2, hv2, hprod⟩ := (local_mem_sup_of_le_normalizer hV1N).mp hyE
      have htaT2 : t * a * t⁻¹ ∈ T2 := D.swap1 a haT1
      have heq : a * (t * a * t⁻¹) = v1 * v2 := hya.symm.trans hprod.symm
      obtain ⟨haeq, -⟩ := sec8t84_wr_unique D.wr haT1 (hV1T1 hv1) htaT2 (hV2T2 hv2) heq
      have haV1 : a ∈ V1 := by rw [haeq]; exact hv1
      have haR1 : a ∈ R1 := by rw [hR1V]; exact haV1
      rw [hya]
      exact hdiag_mem a haR1
    exfalso
    exact hne (le_antisymm hB'_le hEcent_le)
  · intro x hx
    obtain ⟨a, haR1, hxa⟩ := hdiag x hx
    have haF1 : a ∈ F1 := by rw [← hR1F]; exact haR1
    have htaF2 : t * a * t⁻¹ ∈ F2 := by
      rw [D.F2_eq]
      exact Subgroup.mem_map.mpr ⟨a, haF1, by simp [MulAut.conj_apply]⟩
    rw [hxa]
    exact Subgroup.mul_mem_sup haF1 htaF2

end TData

end CFSG.OddStandard.SmallF3.Omega
