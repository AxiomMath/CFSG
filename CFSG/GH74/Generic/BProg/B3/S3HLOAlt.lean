module

public import CFSG.GH74.Generic.BProg.B3.S3HLOCard
public import CFSG.GH74.Generic.BProg.B3.S3Pump306aAlt

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS Subgroup Equiv Equiv.Perm
open scoped commutatorElement

theorem false_of_alt' {Y : Type} [Group Y] [Finite Y] (hgen : Gen4 Y) {n : ℕ} (hn7 : 7 ≤ n) (hn8 : n ≤ 8)
    {H Lb : Subgroup Y} (hH : CFSG.IsComponent H) (hdc : IsDoubleCoverOfAlt ↥H n) {z : Y}
    (hz : ∀ g : Y, g * z = z * g) (hzH : z ∈ H) (hz1 : z ≠ 1) {s : Y} (hs2 : s * s = 1)
    (hsN : s ∈ normalizer (H : Set Y)) (hcomm : s ∈ _root_.commutator Y)
    (hns : ∃ h ∈ H, s * h ≠ h * s) (hLbH : Lb ≤ H) (hLbc : ∀ l ∈ Lb, s * l = l * s)
    (hLsl2 : HasSL2Model (↥Lb ⧸ pPrimeCore 2 ↥Lb) (fun q => Odd q ∧ 5 ≤ q)) : False := by
  classical
  have hZ : Nat.card (center ↥H) = 2 := hdc.2.1
  have hfact : Fact (Nat.card ↥(center ↥H)).Prime := ⟨by rw [hZ]; exact Nat.prime_two⟩
  obtain ⟨S⟩ := exists_altSetting hH.1 hn7 hdc.2.2 hs2 hsN hns
  obtain ⟨q, hqodd, hq5, -, hLbcard⟩ := S3HLOCard.sl2Quot_card_data hLsl2
  have hc : ∀ l : ↥H, (l : Y) ∈ Lb →
      S.σ * (S.π l : Perm (Fin n)) = (S.π l : Perm (Fin n)) * S.σ :=
    fun l hl => S.commute_of_centralizes (hLbc l hl)
  have hcon := S3HLOCard.constraint_of_commuting' S hLbH hZ hqodd hq5 hLbcard S.σ_sq S.σ_ne hc
  have hsupp : S.σ.support.card = 2 * S.σ.cycleType.card :=
    S3SL2Perm.card_support_involution S.σ_sq
  have hle : S.σ.support.card ≤ n := by
    have := Finset.card_le_univ S.σ.support
    simpa using this
  have hk1 : 1 ≤ S.σ.cycleType.card := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [Multiset.card_eq_zero] at h0
    exact S.σ_ne (Equiv.Perm.cycleType_eq_zero.1 h0)
  have hk1' : S.σ.cycleType.card = 1 := by omega
  have hodd : Perm.sign S.σ = -1 := by
    have h1 := S3SL2Perm.sign_involution S.σ_sq
    rw [hk1'] at h1
    simpa using h1
  have hzc : ∀ k : ℤ, ∀ g : Y, g * z ^ k = z ^ k * g := fun k g =>
    ((show Commute g z from hz g).zpow_right k).eq
  have hNn : (Subgroup.zpowers z).Normal := by
    refine ⟨fun m hm g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
    have h1 := hzc k g
    have : g * z ^ k * g⁻¹ = z ^ k := by rw [h1]; group
    rw [this]
    exact Subgroup.zpow_mem_zpowers z k
  let mk : Y →* Y ⧸ Subgroup.zpowers z := QuotientGroup.mk' (Subgroup.zpowers z)
  let ψ : ↥H →* Y ⧸ Subgroup.zpowers z := mk.comp H.subtype
  have hψmem : ∀ h : ↥H, ψ h = 1 ↔ (h : Y) ∈ Subgroup.zpowers z := fun h =>
    QuotientGroup.eq_one_iff (h : Y)
  have hcenz : ∀ h : ↥H, h ∈ center ↥H ↔ (h : Y) ∈ Subgroup.zpowers z := by
    intro h
    constructor
    · intro hh
      let z' : ↥(center ↥H) := ⟨⟨z, hzH⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hz g)⟩
      have hz'1 : z' ≠ 1 := fun h1 => hz1 (congrArg (fun w : ↥(center ↥H) => ((w : ↥H) : Y)) h1)
      rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Subgroup.zpowers z') with hb | ht
      · exfalso
        apply hz'1
        have := Subgroup.mem_zpowers z'
        rw [hb] at this
        exact Subgroup.mem_bot.1 this
      · have hmem : (⟨h, hh⟩ : ↥(center ↥H)) ∈ Subgroup.zpowers z' := by rw [ht]; trivial
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
        have h2 : ((z' ^ k : ↥(center ↥H)) : Y) = z ^ k := by
          simp [z']
        have h3 : (h : Y) = z ^ k := by
          have := congrArg (fun w : ↥(center ↥H) => ((w : ↥H) : Y)) hk
          simpa using this.symm
        rw [h3]
        exact Subgroup.zpow_mem_zpowers z k
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      show (g : Y) * (h : Y) = (h : Y) * (g : Y)
      rw [← hk]
      exact hzc k g
  have hker : ∀ h : ↥H, ψ h = 1 ↔ S.π h = 1 := fun h => by
    rw [hψmem, ← hcenz, S.mem_ker_iff]
  let e₀ := QuotientGroup.quotientKerEquivOfSurjective S.π S.surj
  have hle : S.π.ker ≤ ψ.ker := fun h hh => (hker h).2 hh
  let ι : alternatingGroup (Fin n) →* Y ⧸ Subgroup.zpowers z :=
    (QuotientGroup.lift S.π.ker ψ hle).comp e₀.symm.toMonoidHom
  have hι : ∀ h : ↥H, ι (S.π h) = ψ h := by
    intro h
    have : e₀.symm (S.π h) = (QuotientGroup.mk h : ↥H ⧸ S.π.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift S.π.ker ψ hle (e₀.symm (S.π h)) = ψ h
    rw [this, QuotientGroup.lift_mk]
  have hιinj : Function.Injective ι := by
    intro a b hab
    obtain ⟨h, rfl⟩ := S.surj a
    obtain ⟨h', rfl⟩ := S.surj b
    rw [hι, hι] at hab
    have h1 : ψ (h⁻¹ * h') = 1 := by rw [map_mul, map_inv, hab]; group
    have h2 := (hker _).1 h1
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    rw [h2]
  have hrange : ι.range = ψ.range := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨h, rfl⟩ := S.surj a
      exact ⟨h, (hι h).symm⟩
    · rintro ⟨h, rfl⟩
      exact ⟨S.π h, hι h⟩
  have hψrange : ψ.range = H.map mk := by
    show (mk.comp H.subtype).range = H.map mk
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hL₀ : CFSG.IsComponent ι.range := by
    rw [hrange]
    refine ⟨?_, ?_⟩
    · obtain ⟨h0, hh0, hne0⟩ := hns
      refine CFSG.LieType.CurtisTits.isQuasisimple_of_surjective (φ := ψ.rangeRestrict) hH.1
        ψ.rangeRestrict_surjective ⟨⟨h0, hh0⟩, ?_⟩
      intro h1
      have h2 : ψ ⟨h0, hh0⟩ = 1 := congrArg Subtype.val h1
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((hψmem _).1 h2)
      apply hne0
      show s * h0 = h0 * s
      have : h0 = z ^ k := hk.symm
      rw [this]
      exact hzc k s
    · rw [hψrange]
      exact hH.2.map (QuotientGroup.mk'_surjective _)
  have hs₀ : S3Pump306.ActsAs (mk s) ι S.σ := by
    intro a
    obtain ⟨h, rfl⟩ := S.surj a
    rw [hι]
    have h1 : mk s * ψ h * (mk s)⁻¹ = ψ (S3SL2Basic.actH H hsN h) := by
      show mk s * mk (h : Y) * (mk s)⁻¹ = mk ((S3SL2Basic.actH H hsN h : ↥H) : Y)
      rw [S3SL2Basic.actH_apply, map_mul, map_mul, map_inv]
    rw [h1, ← hι]
    congr 1
    apply Subtype.ext
    exact S.act h
  have hs2₀ : mk s * mk s = 1 := by rw [← map_mul, hs2, map_one]
  have hcomm₀ : mk s ∈ _root_.commutator (Y ⧸ Subgroup.zpowers z) := by
    have h1 : mk s ∈ (_root_.commutator Y).map mk := ⟨s, hcomm, rfl⟩
    have h2 : (_root_.commutator Y).map mk ≤ _root_.commutator (Y ⧸ Subgroup.zpowers z) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
      exact Subgroup.commutator_mono le_top le_top
    exact h2 h1
  exact S3Pump306.false_of_alt_pair (Gen4.quotient (Subgroup.zpowers z) hgen) hn7 hn8 hιinj hL₀ hs2₀ S.σ_sq hodd
    hs₀ hcomm₀

end CFSG.GH74.Generic.BProg.B3
