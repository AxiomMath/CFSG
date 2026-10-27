module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021RedA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021RankMod
public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2015Data

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T2021

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.I2015
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremB (not_dvd_card_glaPPrimeCoreOf)

section Helpers

theorem trivAut_one (p : ℕ) (H : Type) [Group H] : TrivAut p H 1 := fun y => by
  rw [MulAut.one_apply, mul_inv_cancel]
  exact Subgroup.one_mem _

theorem le_normalizer_of_comm {K : Type} [Group K] (hK : ∀ g h : K, g * h = h * g) (A B : Subgroup K) :
    B ≤ Subgroup.normalizer (A : Set K) := by
  intro g _
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [hK g h]
  simp

theorem card_zpowers_sup {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime) (hK : ∀ g h : K, g * h = h * g)
    {u v : K} (hu : orderOf u = p) (hv : orderOf v = p) (huv : u ∉ Subgroup.zpowers v) :
    Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) = p ^ 2 := by
  haveI := Fact.mk hp
  have hnorm : Subgroup.zpowers v ≤ Subgroup.normalizer (Subgroup.zpowers u : Set K) :=
    le_normalizer_of_comm hK _ _
  have hmul := card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [Nat.card_zpowers, Nat.card_zpowers, hu, hv] at hmul
  have hI : Nat.card ↥(Subgroup.zpowers u ⊓ Subgroup.zpowers v) = 1 := by
    have hdvd : Nat.card ↥(Subgroup.zpowers u ⊓ Subgroup.zpowers v) ∣ Nat.card ↥(Subgroup.zpowers u) :=
      Subgroup.card_dvd_of_le inf_le_left
    rw [Nat.card_zpowers, hu] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact h1
    · exfalso
      have heq : Subgroup.zpowers u ⊓ Subgroup.zpowers v = Subgroup.zpowers u :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [Nat.card_zpowers, hu, h1])
      apply huv
      have hmem : u ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v := by
        rw [heq]
        exact Subgroup.mem_zpowers u
      exact (Subgroup.mem_inf.1 hmem).2
  rw [hI, mul_one] at hmul
  rw [pow_two]
  exact hmul

theorem coprime_card_of_isPGroup_two {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {T : Subgroup G} (hT : IsPGroup 2 T) : Nat.Coprime p (Nat.card T) := by
  obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.1 hT
  exact Nat.Coprime.coprime_dvd_right hn
    (Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2))

end Helpers

section Main

variable (G : Type) [Group G] [Finite G]

theorem i2021_of_facts (hRank : T2021RankFact) (hFix : T2021FixFact) (hLay : T2021LayerFact)
    (hTD4f : T2021TD4Fact) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : I2021At G p := by
  classical
  intro B x L b hS hChev hb hbx hR hcent hrank hT
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨⟨⟨hBmax, hxE, hcompL⟩, -⟩, -, hBN⟩, -⟩ := hS
  have hBel : CFSG.Open.IsElemAbelian p B := hBmax.1
  have hBcomm : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := fun g hg h hh => isElemAbelian_commute hBel hg hh
  have hBcomm' : ∀ g h : ↥B, g * h = h * g := fun g h =>
    Subtype.ext (by simp only [Subgroup.coe_mul]; exact hBcomm g.1 g.2 h.1 h.2)
  have hBexp : ∀ g : ↥B, g ^ p = 1 := fun g => Subtype.ext (by simpa using hBel.2 g.1 g.2)
  have hxL : ∀ l ∈ L, x * l = l * x := fun l hl =>
    Subgroup.mem_centralizer_iff.1 (hcompL.1 hl) x (Set.mem_singleton x)
  have hxB : x ∈ B := hxE.1
  set ψ : ↥B →* MulAut ↥L := conjHom L B hBN hBcomm with hψ
  have hψx1 : ψ ⟨x, hxB⟩ = 1 := by
    ext y
    simp only [hψ, conjHom_apply, conjAutOf_apply, MulAut.one_apply, Subgroup.coe_inv]
    have h := hxL y.1 y.2
    calc x⁻¹ * (y : G) * x = x⁻¹ * ((y : G) * x) := by group
      _ = x⁻¹ * (x * (y : G)) := by rw [← h]
      _ = (y : G) := by group
  have hbne : (⟨b, hb⟩ : ↥B) ≠ 1 := by
    intro h
    have hb1 : b = 1 := by simpa using congrArg Subtype.val h
    apply hbx
    rw [hb1]
    exact Subgroup.one_mem _
  obtain ⟨hbN, hFb⟩ := fieldAutOn_of_R2Prop hR
  have hFb' : FieldAutOn p ↥L (ψ ⟨b, hb⟩) := hFb
  obtain ⟨T₀, hT₀L, hT₀2, hT₀B, hT₀O⟩ := hT
  obtain ⟨T, hT₀T, hTL, hT2, hTB, hTmax⟩ := exists_maximal_B_subgroup B L T₀ hT₀L hT₀2 hT₀B
  have hTO : ¬ T ≤ GLAPPrimeCoreOf p L := fun h => hT₀O (hT₀T.trans h)
  set TH : Subgroup ↥L := T.subgroupOf L with hTH
  have hTH2 : IsPGroup 2 TH := isPGroup_subgroupOf hT2
  have hTHmap : TH.map L.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTL
  have hTHinv : ∀ g : ↥B, ∀ t ∈ TH, ψ g t ∈ TH := by
    intro g t ht
    have ht' : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    rw [hTH, Subgroup.mem_subgroupOf]
    simp only [hψ, conjHom_apply, conjAutOf_apply]
    have hginv : (g.1)⁻¹ ∈ Subgroup.normalizer (T : Set G) := hTB (B.inv_mem g.2)
    have := (Subgroup.mem_normalizer_iff.1 hginv (t : G)).1 ht'
    simpa using this
  have hTHO : ¬ TH ≤ GLAPPrimeCore p ↥L := by
    intro h
    apply hTO
    calc T = TH.map L.subtype := hTHmap.symm
      _ ≤ (GLAPPrimeCore p ↥L).map L.subtype := Subgroup.map_mono h
      _ = GLAPPrimeCoreOf p L := (glaPPrimeCoreOf_eq_map L).symm
  have hTHmax : ∀ T' : Subgroup ↥L, IsPGroup 2 T' → (∀ g : ↥B, ∀ t ∈ T', ψ g t ∈ T') → TH ≤ T' →
      T' = TH := by
    intro T' hT'2 hT'inv hTT'
    have hmax := hTmax (T'.map L.subtype) (by rw [← hTHmap]; exact Subgroup.map_mono hTT')
      (Subgroup.map_subtype_le T') (hT'2.map L.subtype) (normalizes_map_of_invariant hBN hBcomm hT'inv)
    apply Subgroup.map_injective (f := L.subtype) Subtype.val_injective
    rw [hmax, hTHmap]
  have hrankD : p ^ 3 * Nat.card {g : ↥B // TrivAut p ↥L (ψ g)} ≤ Nat.card ↥B := by
    rw [hψ, card_trivAut_eq L B hBN hBcomm]
    exact hrank
  by_cases hTD : p = 3 ∧ IsTD4 3 L
  ·
    obtain ⟨rfl, hT4⟩ := hTD
    have hcent3 : cent2Aut 3 ↥L (ψ ⟨b, hb⟩) = Nat.sqrt (twoPart (Nat.card (ppQuot 3 ↥L))) := by
      have h : centCard2 3 L b = Nat.sqrt (card2 3 L) := hcent rfl hT4
      have h2 : cent2Aut 3 ↥L (ψ ⟨b, hb⟩) = centCard2 3 L b := by
        unfold cent2Aut centCard2
        rw [show relOfAut 3 (ψ ⟨b, hb⟩) = indRel 3 L b from (indRel_eq_relOfAut 3 L b hbN).symm]
      rw [h2, h]
      rfl
    obtain ⟨T', hT'L, hT'2, hT'inv, hT'O⟩ :=
      hTD4f ↥L ↥B ψ TH ⟨b, hb⟩ hChev hT4 hBexp hBcomm' hTH2 hTHinv hTHO hTHmax hrankD hFb' hcent3
    obtain ⟨h1, h2, h3, h4⟩ := layer_transport_G hp hBN hBcomm hbN hT'L hT'2 hT'inv hT'O
    exact ⟨b, hb, hbx, hR, hcent, ⟨T'.map L.subtype, h1, h2, h3, h4⟩⟩
  ·
    obtain ⟨b₁, hb₁nt, hb₁inn, hbb₁, hkerD, hfield⟩ :=
      hRank ↥L p ↥B ψ ⟨b, hb⟩ hp hp2 hChev hBexp hBcomm' hTD hrankD hFb'
    have hb₁ne : b₁ ≠ 1 := fun h => hb₁nt (by rw [h, map_one]; exact trivAut_one p ↥L)
    have hord_b : orderOf (⟨b, hb⟩ : ↥B) = p := orderOf_eq_prime (hBexp _) hbne
    have hord_b₁ : orderOf b₁ = p := orderOf_eq_prime (hBexp _) hb₁ne
    set D : Subgroup ↥B := Subgroup.zpowers (⟨b, hb⟩ : ↥B) ⊔ Subgroup.zpowers b₁ with hD
    have hcardD : Nat.card ↥D = p ^ 2 :=
      card_zpowers_sup hp hBcomm' hord_b hord_b₁ hbb₁
    set DG : Subgroup G := D.map B.subtype with hDG
    have hDGle : DG ≤ B := by
      rintro _ ⟨d, -, rfl⟩
      exact d.2
    have hcardDG : Nat.card ↥DG = p ^ 2 := by
      rw [← hcardD]
      exact Nat.card_congr (Subgroup.equivMapOfInjective D B.subtype B.subtype_injective).symm
    have hDGab : CFSG.Open.IsElemAbelian p DG := isElemAbelian_mono hBel hDGle
    have hDGN : DG ≤ Subgroup.normalizer (T : Set G) := hDGle.trans hTB
    have hcopT : Nat.Coprime p (Nat.card T) := coprime_card_of_isPGroup_two hp hp2 hT2
    have hperf : commutator (ppQuot p ↥L) = ⊤ :=
      (isQuasisimple_pQuot_of_glaPComponent hp hcompL).1
    have hfaithO : ∀ a ∈ DG, (∀ t ∈ T, a⁻¹ * t * a * t⁻¹ ∈ GLAPPrimeCoreOf p L) → a = 1 := by
      intro a ha hat
      obtain ⟨c, hcD, rfl⟩ := Subgroup.mem_map.1 ha
      have hfixO : ∀ t ∈ TH, ψ c t * t⁻¹ ∈ GLAPPrimeCore p ↥L := by
        intro t ht
        apply mem_glaPPrimeCore_of_coe
        have h1 := hat (t : G) (Subgroup.mem_subgroupOf.1 ht)
        simpa [hψ, conjHom_apply, conjAutOf_apply] using h1
      have hTriv := hFix ↥L p ↥B ψ TH hp hp2 hChev hperf hTD hBexp hBcomm' hTH2 hTHinv hTHO hTHmax hrankD c hfixO
      have hc1 : c = 1 := hkerD c hcD hTriv
      rw [hc1]
      simp
    have hb₁G : (b₁ : G) ∈ DG := Subgroup.mem_map.2 ⟨b₁, Subgroup.mem_sup_right (Subgroup.mem_zpowers b₁), rfl⟩
    have hb₁G1 : (b₁ : G) ≠ 1 := fun h => hb₁ne (Subtype.ext h)
    have hNO : ∀ n ∈ Subgroup.normalizer (L : Set G), ∀ o ∈ GLAPPrimeCoreOf p L,
        n * o * n⁻¹ ∈ GLAPPrimeCoreOf p L := fun n hn o ho => glaPPrimeCoreOf_normalized L hn ho
    obtain ⟨aG, haDG, haN, t, htT, hcommt, hbt⟩ :=
      exists_comm_fail_mod hp (N := Subgroup.normalizer (L : Set G)) (O := GLAPPrimeCoreOf p L)
        (hDGle.trans hBN) (hTL.trans Subgroup.le_normalizer) hNO (not_dvd_card_glaPPrimeCoreOf hp L)
        hDGab hcardDG hDGN hcopT hfaithO hb₁G hb₁G1
    obtain ⟨c, hcD, hca⟩ := Subgroup.mem_map.1 haDG
    have hcb : c ∉ Subgroup.zpowers b₁ := by
      intro hc
      apply haN
      rw [← hca]
      have hmapz : (Subgroup.zpowers b₁).map B.subtype = Subgroup.zpowers (b₁ : G) :=
        MonoidHom.map_zpowers B.subtype b₁
      rw [← hmapz]
      exact Subgroup.mem_map.2 ⟨c, hc, rfl⟩
    obtain ⟨hcFix, hcNT⟩ := hfield c hcD hcb
    have hdN : (c : G) ∈ Subgroup.normalizer (L : Set G) := hBN c.2
    have hax : (c : G) ∉ Subgroup.zpowers x := by
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      have hck : c = (⟨x, hxB⟩ : ↥B) ^ k := Subtype.ext (by simp [hk])
      apply hcNT
      rw [hck, map_zpow, hψx1, one_zpow]
      exact trivAut_one p ↥L
    have hR2 : R2Prop p (c : G) L := by
      have hrel : relOfAut p (ψ c) = indRel p L (c : G) :=
        (indRel_eq_relOfAut p L (c : G) hdN).symm
      rcases hcFix with hM | ⟨h3, hT4, -⟩
      · refine Or.inl ⟨hdN, ?_⟩
        rw [hrel] at hM
        exact hM
      · exact absurd ⟨h3, hT4⟩ hTD
    have htL : t ∈ L := hTL htT
    have hexO : ∃ t' ∈ TH, ψ c t' * t'⁻¹ ∈ GLAPPrimeCore p ↥L ∧ ψ b₁ t' * t'⁻¹ ∉ GLAPPrimeCore p ↥L := by
      refine ⟨⟨t, htL⟩, Subgroup.mem_subgroupOf.2 htT, ?_, ?_⟩
      · apply mem_glaPPrimeCore_of_coe
        have h0 := hcommt
        rw [← hca] at h0
        simpa [hψ, conjHom_apply, conjAutOf_apply] using h0
      · intro h
        apply hbt
        have h' := (mem_glaPPrimeCoreOf_iff (p := p) (H := L) (g := _)).2 ⟨_, h, rfl⟩
        simpa [hψ, conjHom_apply, conjAutOf_apply] using h'
    obtain ⟨T', hT'lay, hT'2, hT'inv, hT'O⟩ := hLay ↥L p ↥B ψ TH c b₁ hp hp2 hChev hTD hBexp hBcomm' hTH2
      hTHinv hrankD hcFix hb₁inn hb₁nt hcb hexO
    obtain ⟨h1, h2, h3', h4⟩ := layer_transport_G hp hBN hBcomm hdN hT'lay hT'2 hT'inv hT'O
    exact ⟨(c : G), c.2, hax, hR2, fun h3 hT4 => absurd ⟨h3, hT4⟩ hTD,
      ⟨T'.map L.subtype, h1, h2, h3', h4⟩⟩

end Main

end CFSG.LocalAnalysis.GLTheoremA.T2021

end
