module

public import CFSG.GH74.Generic.BProg.B3.S3SL2AltMain
public import CFSG.GH74.Generic.BProg.B3.S3SL2AltLift
public import CFSG.GH74.Generic.BProg.B1.Lift0
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Comp

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup Equiv Equiv.Perm
open scoped commutatorElement

namespace S3SL2AltTr

theorem pPrimeCore_eq_bot {K : Type} [Group K] [Finite K] (hq : CFSG.IsQuasisimple K)
    (hZ : IsPGroup 2 ↥(center K)) (heven : 2 ∣ Nat.card K) : pPrimeCore 2 K = ⊥ := by
  have hodd : Nat.Coprime 2 (Nat.card (pPrimeCore 2 K)) := pPrimeCore_coprime_card
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (pPrimeCore_normal (p := 2) (G := K)) with h | h
  · exfalso
    rw [h, Subgroup.card_top] at hodd
    exact absurd (Nat.Coprime.eq_one_of_dvd hodd heven) (by norm_num)
  · have h2 : IsPGroup 2 (pPrimeCore 2 K) := hZ.to_le h
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2
    have hn0 : n = 0 := by
      by_contra hn0
      have h3 : 2 ∣ Nat.card (pPrimeCore 2 K) := hn ▸ dvd_pow_self 2 hn0
      exact absurd (Nat.Coprime.eq_one_of_dvd hodd h3) (by norm_num)
    rw [hn0, pow_zero] at hn
    exact Subgroup.card_eq_one.1 hn

end S3SL2AltTr

theorem transpExcl : TranspExcl := by
  intro Y _ _ H Lb s hsN S hq hZ hss hsH hσab hLb hLlay hLsl2
  classical
  obtain ⟨a, b, hab, hσ⟩ := hσab
  obtain ⟨q, hqodd, hq5, hLbcard⟩ := S3SL2Basic.sl2_card_data hLsl2
  have hLbH : Lb ≤ H := hLb.1.trans inf_le_right
  set F : Subgroup Y := centralizer ({s} : Set Y) ⊓ H with hF
  set D : Subgroup ↥H := S3SL2AltLift.Dsub S a b with hD
  set DY : Subgroup Y := D.map H.subtype with hDY
  have hDF : DY ≤ F := by
    rintro _ ⟨d, hd, rfl⟩
    refine ⟨mem_centralizer_iff.2 fun g hg => ?_, d.2⟩
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (S3SL2Basic.actH_eq_iff H hsN d).1 (S3SL2AltLift.Dsub_fixed S hab hσ d hd)
  have hqD : CFSG.IsQuasisimple ↥D := S3SL2AltLift.Dsub_quasisimple S hab
  let e : ↥D ≃* ↥DY := Subgroup.equivMapOfInjective D H.subtype H.subtype_injective
  have hqDY : CFSG.IsQuasisimple ↥DY := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hqD
  have hZDY : IsPGroup 2 ↥(center ↥DY) := by
    intro z
    refine ⟨1, ?_⟩
    obtain ⟨zz, hzz, hzzv⟩ : ∃ zz : ↥H, zz ∈ D ∧ (zz : Y) = (z : ↥DY) := by
      obtain ⟨zz, hzz, h⟩ := (z : ↥DY).2
      exact ⟨zz, hzz, h⟩
    have hsq : zz ^ 2 = 1 := by
      refine S3SL2AltLift.Dsub_center_sq S hab hZ hzz ?_
      intro d hd
      have hdY : (d : Y) ∈ DY := ⟨d, hd, rfl⟩
      have hzc := Subgroup.mem_center_iff.1 z.2 ⟨d, hdY⟩
      apply Subtype.ext
      have := congrArg Subtype.val hzc
      simp only [Subgroup.coe_mul] at this ⊢
      rw [hzzv]
      exact this.symm
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg (fun w : ↥H => (w : Y)) hsq
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [← hzzv]
    simpa using this
  have hcardX : 2520 ∣ Nat.card ↥D := by
    have h1 := Subgroup.card_map_dvd (H := D) S.π
    rw [S3SL2AltLift.Dsub_map S hab, S3SL2AltX.Xs_card hab] at h1
    exact h1
  have heven : 2 ∣ Nat.card ↥DY := by
    rw [← Nat.card_congr e.toEquiv]
    exact (by norm_num : 2 ∣ 2520).trans hcardX
  have hOK : pPrimeCore 2 ↥DY = ⊥ := S3SL2AltTr.pPrimeCore_eq_bot hqDY hZDY heven
  have hPC : IsPCompIn 2 DY DY :=
    ⟨le_rfl, by
      rw [Subgroup.subgroupOf_self]
      exact Stage1.Thm2.Recip.isPComponent_top hqDY hOK⟩
  have : ((DY).subgroupOf F).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : Y) ∈ DY := hn
    obtain ⟨d, hd, hdn⟩ := hn'
    have hgH : (g : Y) ∈ H := g.2.2
    have hgs : s * (g : Y) = (g : Y) * s := (mem_centralizer_iff.1 g.2.1 s rfl)
    have hfix : S3SL2Basic.actH H hsN ⟨g, hgH⟩ = ⟨g, hgH⟩ :=
      (S3SL2Basic.actH_eq_iff H hsN ⟨g, hgH⟩).2 hgs
    have hdd := S3SL2AltLift.Dsub_conj S hab hσ hfix d hd
    show ((g * n * g⁻¹ : ↥F) : Y) ∈ DY
    refine ⟨⟨g, hgH⟩ * d * ⟨g, hgH⟩⁻¹, hdd, ?_⟩
    have hdn' : (d : Y) = (n : Y) := hdn
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hdn']
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPCF : IsPCompIn 2 F DY := B1.isPCompIn_of_normal 2 hDF hPC
  have hDYLb : DY ≤ Lb := by
    rw [← hLlay]
    exact le_sSup hPCF
  set R : Subgroup (alternatingGroup (Fin 9)) := (Lb.subgroupOf H).map S.π with hR
  have hXR : S3SL2AltX.Xs a b ≤ R := by
    intro x hx
    have hx' : x ∈ D.map S.π := by
      rw [hD, S3SL2AltLift.Dsub_map S hab]
      exact hx
    obtain ⟨d, hd, rfl⟩ := hx'
    exact ⟨d, hDYLb ⟨d, hd, rfl⟩, rfl⟩
  have hN1 : 2520 ∣ Nat.card R := by
    have := Subgroup.card_dvd_of_le hXR
    rwa [S3SL2AltX.Xs_card hab] at this
  have hlc : ∀ l : ↥H, (l : Y) ∈ Lb →
      S.σ * (S.π l : Perm (Fin 9)) = (S.π l : Perm (Fin 9)) * S.σ := fun l hl =>
    S.commute_of_centralizes (mem_centralizer_iff.1 (hLb.1 hl).1 s rfl)
  have hN2 : Nat.card R ∣ 10080 := by
    have h1 := S3SL2AltOrd.card_image_dvd_centralizer S hlc
    have hct : S.σ.cycleType = {2} :=
      Equiv.Perm.isSwap_iff_cycleType.1 (by rw [hσ]; exact ⟨a, b, hab, rfl⟩)
    rw [S3SL2Perm.card_centralizer_involution S.σ_sq S.σ_ne, hct] at h1
    have hk : Multiset.card ({2} : Multiset ℕ) = 1 := rfl
    have h10 : (9 - 2 * 1).factorial * 2 ^ 1 * (1 : ℕ).factorial = 10080 := by decide +kernel
    rw [hk, h10] at h1
    exact h1
  obtain ⟨m, hm2, hmcard⟩ := S3SL2AltOrd.card_image_dvd S hLbH hZ
  rw [hLbcard] at hmcard
  obtain ⟨t, ht⟩ := hN1
  rw [ht] at hN2 hmcard
  have hpos : 0 < m * (2520 * t) := by
    rw [← hmcard]
    have := S3SL2Basic.sl2_card_ge hq5
    omega
  have hm1 : 1 ≤ m := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have ht1 : 1 ≤ t := Nat.pos_of_ne_zero (by rintro rfl; simp at hpos)
  have ht4 : t ∣ 4 := by
    have : 2520 * t ∣ 2520 * 4 := by simpa using hN2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  have htle : t ≤ 4 := Nat.le_of_dvd (by norm_num) ht4
  have hmle : m ≤ 2 := Nat.le_of_dvd (by norm_num) hm2
  have hq27 : q ≤ 27 := by
    by_contra hcon
    push Not at hcon
    have h1 : 28 * (28 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hcon (Nat.sub_le_sub_right (Nat.pow_le_pow_left hcon 2) 1)
    have h2 : m * (2520 * t) ≤ 2 * (2520 * 4) := Nat.mul_le_mul hmle (Nat.mul_le_mul_left _ htle)
    omega
  interval_cases q <;> interval_cases t <;> interval_cases m <;> omega

end CFSG.GH74.Generic.BProg.B3
