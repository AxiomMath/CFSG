module

public import CFSG.Open.GLADefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.HardMathSupport.Solomon.Proving

theorem mem_of_coprime_orderOf {H : Type*} [Group H] [Finite H] {p : ℕ} {C T : Subgroup H}
    (hT : Subgroup.IsComplement' C T) (hCc : ∀ c ∈ C, ∀ g : H, Commute c g)
    {k : ℕ} (hCk : Nat.card C = p ^ k) {x : H} (hx : Nat.Coprime (orderOf x) p) : x ∈ T := by
  obtain ⟨⟨⟨c, hc⟩, ⟨s, hs⟩⟩, hcs⟩ := ((Subgroup.isComplement_iff_bijective C T).mp hT).2 x
  have hcs' : c * s = x := hcs
  obtain ⟨n, hn⟩ : ∃ n, orderOf x = n := ⟨_, rfl⟩
  rw [hn] at hx
  have hxn : x ^ n = 1 := by rw [← hn]; exact pow_orderOf_eq_one x
  rw [← hcs', (hCc c hc s).mul_pow] at hxn
  have hcn : c ^ n = (s ^ n)⁻¹ := eq_inv_of_mul_eq_one_left hxn
  have hc1 : c ^ n = 1 :=
    (Subgroup.disjoint_def.mp hT.disjoint) (C.pow_mem hc n)
      (by rw [hcn]; exact T.inv_mem (T.pow_mem hs n))
  have hord : orderOf c ∣ n := orderOf_dvd_of_pow_eq_one hc1
  have hdvdC : orderOf c ∣ Nat.card C := by
    have h1 := orderOf_dvd_natCard (⟨c, hc⟩ : C)
    rw [← Subgroup.orderOf_coe] at h1
    exact h1
  have hdvdp : orderOf c ∣ p ^ k := by rw [← hCk]; exact hdvdC
  have hgcd : orderOf c ∣ Nat.gcd n (p ^ k) := Nat.dvd_gcd hord hdvdp
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k hx), Nat.dvd_one] at hgcd
  have hc1' : c = 1 := orderOf_eq_one_iff.mp hgcd
  rw [← hcs', hc1', one_mul]
  exact hs

theorem glaPPrimeCore_quotient_eq_bot_of_le_center {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (hcore : CFSG.Open.GLAPPrimeCore p Y = ⊥) {Z : Subgroup Y} [Z.Normal]
    (hZ : Z ≤ Subgroup.center Y) (hZp : IsPGroup p Z) :
    CFSG.Open.GLAPPrimeCore p (Y ⧸ Z) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set N := CFSG.Open.GLAPPrimeCore p (Y ⧸ Z) with hNdef
  have hNn : N.Normal := CFSG.Open.GLAPPrimeCore.normal p (Y ⧸ Z)
  have hNcop : Nat.Coprime p (Nat.card N) := CFSG.pPrimeCore_coprime_card (p := p) (G := Y ⧸ Z)
  set R : Subgroup Y := N.comap (QuotientGroup.mk' Z) with hRdef
  have hRn : R.Normal := hNn.comap (QuotientGroup.mk' Z)
  have hZR : Z ≤ R := by
    intro z hz
    rw [hRdef, Subgroup.mem_comap, QuotientGroup.mk'_apply]
    rw [(QuotientGroup.eq_one_iff z).mpr hz]
    exact N.one_mem
  have hcardR : Nat.card R = Nat.card Z * Nat.card N :=
    QuotientGroup.card_preimage_mk Z (N : Set (Y ⧸ Z))
  set C : Subgroup R := Z.subgroupOf R with hCdef
  have hCcent : ∀ c ∈ C, ∀ g : R, Commute c g := by
    intro c hc g
    have hcZ : (c : Y) ∈ Z := Subgroup.mem_subgroupOf.mp hc
    have hcc : (c : Y) ∈ Subgroup.center Y := hZ hcZ
    show c * g = g * c
    exact Subtype.ext (Subgroup.mem_center_iff.mp hcc (g : Y)).symm
  have hCn : C.Normal := by
    constructor
    intro n hn g
    have e : g * n * g⁻¹ = n := by
      have := hCcent n hn g
      rw [← this, mul_inv_cancel_right]
    rw [e]
    exact hn
  have hCZ : Nat.card C = Nat.card Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZR).toEquiv
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZp
  have hCpk : Nat.card C = p ^ k := hCZ.trans hk
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have h1 : Nat.card C * C.index = Nat.card C * Nat.card N := by
    rw [Subgroup.card_mul_index C, hcardR, hCZ]
  have hCidx : C.index = Nat.card N := Nat.eq_of_mul_eq_mul_left hCpos h1
  have hcop : Nat.Coprime (Nat.card C) C.index := by
    rw [hCpk, hCidx]
    exact Nat.Coprime.pow_left k hNcop
  obtain ⟨T, hT⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hTcard : Nat.card T = Nat.card N := by
    have h2 : Nat.card C * Nat.card T = Nat.card C * Nat.card N := by
      rw [hT.card_mul_card, hcardR, hCZ]
    exact Nat.eq_of_mul_eq_mul_left hCpos h2
  have hTcop : Nat.Coprime (Nat.card T) p := by
    rw [hTcard]
    exact hNcop.symm
  have hTord : ∀ t : R, t ∈ T → Nat.Coprime (orderOf t) p := by
    intro t ht
    have hdvd : orderOf t ∣ Nat.card T := by
      have h1 := orderOf_dvd_natCard (⟨t, ht⟩ : T)
      rw [← Subgroup.orderOf_coe] at h1
      exact h1
    exact Nat.Coprime.coprime_dvd_left hdvd hTcop
  have hTmcard : Nat.card (T.map R.subtype) = Nat.card T :=
    Subgroup.card_map_of_injective (f := R.subtype) Subtype.val_injective
  have hTmcop : Nat.Coprime p (Nat.card (T.map R.subtype)) := by
    rw [hTmcard, hTcard]
    exact hNcop
  have hTmn : (T.map R.subtype).Normal := by
    constructor
    intro n hn g
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hn
    have hconjR : g * (t : Y) * g⁻¹ ∈ R := Subgroup.Normal.conj_mem hRn (t : Y) t.2 g
    obtain ⟨x, hx⟩ : ∃ x : R, (x : Y) = g * (t : Y) * g⁻¹ := ⟨⟨_, hconjR⟩, rfl⟩
    have hsemi : SemiconjBy g (t : Y) (x : Y) := by
      show g * (t : Y) = (x : Y) * g
      rw [hx]
      group
    have hord : orderOf x = orderOf t := by
      calc orderOf x = orderOf (x : Y) := (Subgroup.orderOf_coe x).symm
        _ = orderOf (t : Y) := (SemiconjBy.orderOf_eq g hsemi).symm
        _ = orderOf t := Subgroup.orderOf_coe t
    have hxT : x ∈ T := by
      refine mem_of_coprime_orderOf hT hCcent hCpk ?_
      rw [hord]
      exact hTord t ht
    exact Subgroup.mem_map.mpr ⟨x, hxT, hx⟩
  have hTbot : ∀ t : R, t ∈ T → (t : Y) = 1 := by
    intro t ht
    have hmem : (t : Y) ∈ T.map R.subtype := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    have hcoreTm : (t : Y) ∈ CFSG.Open.GLAPPrimeCore p Y := by
      unfold CFSG.Open.GLAPPrimeCore CFSG.pPrimeCore
      have hmemS : T.map R.subtype ∈ {K : Subgroup Y | K.Normal ∧ Nat.Coprime p (Nat.card K)} :=
        ⟨hTmn, hTmcop⟩
      exact Subgroup.mem_sSup_of_mem hmemS hmem
    rw [hcore, Subgroup.mem_bot] at hcoreTm
    exact hcoreTm
  have hRZ : R ≤ Z := by
    intro r hr
    obtain ⟨⟨⟨c, hc⟩, ⟨s, hs⟩⟩, hcs⟩ := ((Subgroup.isComplement_iff_bijective C T).mp hT).2 ⟨r, hr⟩
    have hcs' : c * s = (⟨r, hr⟩ : R) := hcs
    have h2 : (c : Y) * (s : Y) = r := congrArg Subtype.val hcs'
    rw [hTbot s hs, mul_one] at h2
    have hcZ : (c : Y) ∈ Z := Subgroup.mem_subgroupOf.mp hc
    rw [← h2]
    exact hcZ
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  have hy : y ∈ R := Subgroup.mem_comap.mpr hx
  have hyZ : y ∈ Z := hRZ hy
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff y).mpr hyZ

end CFSG.HardMathSupport.Solomon.Proving

end
