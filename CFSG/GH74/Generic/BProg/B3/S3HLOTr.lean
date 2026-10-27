module

public import CFSG.GH74.Generic.BProg.B3.S3SL2AltTr
public import CFSG.GH74.Generic.BProg.B3.S3HLOCard

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup Equiv Equiv.Perm
open scoped commutatorElement

namespace S3HLOTr

theorem card_dvd_quot {Y : Type} [Group Y] [Finite Y] {D Lb : Subgroup Y} (hDL : D ≤ Lb)
    (hO : pPrimeCore 2 ↥D = ⊥) : Nat.card ↥D ∣ Nat.card (↥Lb ⧸ pPrimeCore 2 ↥Lb) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ι : ↥D →* ↥Lb := Subgroup.inclusion hDL
  let g : ↥D →* ↥Lb ⧸ pPrimeCore 2 ↥Lb := (QuotientGroup.mk' (pPrimeCore 2 ↥Lb)).comp ι
  have hle : g.ker ≤ pPrimeCore 2 ↥D := by
    refine le_sSup ⟨inferInstance, ?_⟩
    have hmap : g.ker.map ι ≤ pPrimeCore 2 ↥Lb := by
      rintro _ ⟨k, hk, rfl⟩
      exact (QuotientGroup.eq_one_iff _).1 hk
    have h2 : Nat.card ↥(g.ker.map ι) ∣ Nat.card ↥(pPrimeCore 2 ↥Lb) := Subgroup.card_dvd_of_le hmap
    rw [Subgroup.card_map_of_injective (Subgroup.inclusion_injective hDL)] at h2
    exact Nat.Coprime.coprime_dvd_right h2 pPrimeCore_coprime_card
  rw [hO, le_bot_iff] at hle
  exact Subgroup.card_dvd_of_injective g ((MonoidHom.ker_eq_bot_iff g).1 hle)

theorem not_dvd_2520 {q : ℕ} (hq : Odd q) (hq5 : 5 ≤ q) (hq27 : q ≤ 27) :
    ¬ 2520 ∣ q * (q ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ := hq
  have hk2 : 2 ≤ k := by omega
  have hk : k ≤ 13 := by omega
  interval_cases k <;> norm_num

end S3HLOTr

theorem transpExcl' :
    ∀ {Y : Type} [Group Y] [Finite Y] {H Lb : Subgroup Y} {s : Y} {hsN : s ∈ normalizer (H : Set Y)}
      (S : AltSetting H 9 hsN), CFSG.IsQuasisimple ↥H → Nat.card (center ↥H) = 2 → s * s = 1 → s ∉ H →
      (∃ a b : Fin 9, a ≠ b ∧ S.σ = swap a b) →
      IsPCompIn 2 (centralizer ({s} : Set Y) ⊓ H) Lb → pLayerOf 2 (centralizer ({s} : Set Y) ⊓ H) = Lb →
      HasSL2Model (↥Lb ⧸ pPrimeCore 2 ↥Lb) (fun q => Odd q ∧ 5 ≤ q) → False := by
  intro Y _ _ H Lb s hsN S hq hZ hss hsH hσab hLb hLlay hLsl2
  classical
  obtain ⟨a, b, hab, hσ⟩ := hσab
  obtain ⟨q, hqodd, hq5, hLq, hLqdvd⟩ := S3HLOCard.sl2Quot_card_data hLsl2
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
  have h2520 : 2520 ∣ q * (q ^ 2 - 1) := by
    have h1 := S3HLOTr.card_dvd_quot hDYLb hOK
    rw [hLq] at h1
    exact (hcardX.trans (Nat.card_congr e.toEquiv).dvd).trans h1
  set R : Subgroup (alternatingGroup (Fin 9)) := (Lb.subgroupOf H).map S.π with hR
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
  have hRle : Nat.card R ≤ 10080 := Nat.le_of_dvd (by norm_num) hN2
  have hmle : m ≤ 2 := Nat.le_of_dvd (by norm_num) hm2
  have hLble : Nat.card Lb ≤ 20160 := by
    rw [hmcard]
    calc m * Nat.card R ≤ 2 * 10080 := Nat.mul_le_mul hmle hRle
      _ = 20160 := by norm_num
  have hq27 : q ≤ 27 := by
    by_contra hcon
    push Not at hcon
    have h1 : 28 * (28 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hcon (Nat.sub_le_sub_right (Nat.pow_le_pow_left hcon 2) 1)
    have h2 := S3HLOCard.le_card_of_dvd hLqdvd
    omega
  exact S3HLOTr.not_dvd_2520 hqodd hq5 hq27 h2520

end CFSG.GH74.Generic.BProg.B3
