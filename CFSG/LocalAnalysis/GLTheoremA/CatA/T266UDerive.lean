module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266UTrans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266U6Facts
public import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266G2Derive
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T266UDef

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T266

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

section Helper

variable {G : Type} [Group G] [Finite G]

theorem map_inf_centralizer_single (X : Subgroup G) (S : Subgroup X) (y : X) :
    (S ⊓ Subgroup.centralizer ({y} : Set X)).map X.subtype =
      S.map X.subtype ⊓ Subgroup.centralizer ({(y : G)} : Set G) := by
  rw [Subgroup.map_inf_eq _ _ _ X.subtype_injective, Y10F.map_centralizer_singleton_subtype, ← inf_assoc,
    inf_eq_left.2 (Y10F.map_subtype_le S)]

end Helper

section U6

variable {G : Type} [Group G] [Finite G]

theorem i266U6_of_fact (n : ℕ) (hF : T266U6Fact n) (hDisj : T266G2NotU6)
    (X K B : Subgroup G) (hK : GLAPComponent 3 X K) (hodd : Odd n) (hn1 : 1 < n)
    (hU : catalogIs (PSimple 3 K) (S10.isU6n n)) (hO : GLAPPrimeCoreOf 3 K = ⊥)
    (hB : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set G)) (hBX : B ≤ X)
    (hrank : 3 ^ GLATwoLocalRank 3 ↥X ≤ Nat.card B)
    (hBc : 3 ^ 2 * Nat.card ↥(B ⊓ centModSubgroup 3 K) ≤ Nat.card B) (hInnB : InnDiagOn 3 B K)
    (hT : ∃ T : Subgroup G, T ≤ K ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      ¬ T ≤ GLAPPrimeCoreOf 3 K ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥)
    (hE0 : ∀ E : Subgroup G, S10.IsE0 B K E → ¬ ∀ g ∈ E, CentMod 3 K g) :
    ∃ (E : Subgroup G) (y : G) (J : Subgroup G), S10.IsE0 B K E ∧ y ∈ E ∧ ¬ CentMod 3 K y ∧
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J ∧
      ((catalogIs (PSimple 3 K) (S10.isG2n n) → Even n ∧ catalogIs (PSimple 3 J) (S10.isL2n n)) ∧
        (catalogIs (PSimple 3 K) (S10.isU6n n) → catalogIs (PSimple 3 J) (S10.isUrn n))) ∧
      ∃ T : Subgroup G, T ≤ K ⊓ Subgroup.centralizer ({y} : Set G) ∧ IsPGroup 2 T ∧
        B ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, B⁆ : Subgroup G) ≠ ⊥ ∧ IsEmpty (T ≃* QuaternionGroup 2) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = K ⊔ B := ⟨_, rfl⟩
  have hKY : K ≤ Y := hY ▸ le_sup_left
  have hBY : B ≤ Y := hY ▸ le_sup_right
  have hYX : Y ≤ X := hY ▸ sup_le hK.1 hBX
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := hY ▸ sup_le_normalizer_of hBN
  have hKBtop : K.subgroupOf Y ⊔ B.subgroupOf Y = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hKY hBY, ← hY, Subgroup.subgroupOf_self]
  have hi : Function.Injective Y.subtype := Y.subtype_injective
  have hKq : CFSG.Open.IsQuasisimple ↥K := isQuasisimple_of_core_eq_bot hK hO
  have hrank' : 3 ^ GLATwoLocalRank 3 ↥Y ≤ Nat.card (B.subgroupOf Y) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv]
    exact (Nat.pow_le_pow_right (by norm_num) (twoLocalRank_le_of_le hYX)).trans hrank
  have hBc' : 3 ^ 2 * Nat.card ↥(B.subgroupOf Y ⊓ centModSubgroup 3 (K.subgroupOf Y)) ≤
      Nat.card (B.subgroupOf Y) := by
    rw [card_inf_centMod_subgroupOf hKY hBY hB hBN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv]
    exact hBc
  obtain ⟨T, hTK, hT2, hTN, -, hTc⟩ := hT
  have hTY : T ≤ Y := hTK.trans hKY
  have hAT : ∃ T' : Subgroup Y, T' ≤ K.subgroupOf Y ∧ IsPGroup 2 T' ∧
      B.subgroupOf Y ≤ Subgroup.normalizer (T' : Set Y) ∧ (⁅T', B.subgroupOf Y⁆ : Subgroup Y) ≠ ⊥ := by
    refine ⟨T.subgroupOf Y, fun x hx => hTK hx,
      IsPGroup.of_injective hT2 (Subgroup.subgroupOfEquivOfLe hTY).toMonoidHom (MulEquiv.injective _),
      T171.le_normalizer_subgroupOf' Y hBY hTY hTN, ?_⟩
    intro h
    apply hTc
    rw [← T171.commutator_subgroupOf_map Y hTY hBY, h, Subgroup.map_bot]
  have hAE0 : ∀ E : Subgroup Y, S10.IsE0 (B.subgroupOf Y) (K.subgroupOf Y) E →
      ¬ ∀ g ∈ E, CentMod 3 (K.subgroupOf Y) g := by
    intro E hE hall
    apply hE0 (E.map Y.subtype) (isE0_map_subgroupOf hKY hBY hE)
    rintro _ ⟨e, he, rfl⟩
    have h1 := hall e he
    rw [centMod_iff] at h1 ⊢
    have h2 := (S267.mem_centModSubgroup_map_iff_inj Nat.prime_three Y.subtype hi).1 h1
    rwa [Subgroup.map_subgroupOf_eq_of_le hKY] at h2
  obtain ⟨E₀, y, hE₀A, hcard, hyE₀, hlay, hynot, J, hJ, hJcat, T', hT'C, hT'2, hT'N, hT'comm, hT'Q⟩ :=
    hF ↥Y (K.subgroupOf Y) (B.subgroupOf Y) hodd hn1
      (T171.normal_subgroupOf_of_le_normalizer Y hKY hYN)
      (T171.isQuasisimple_subgroupOf Y hKY hKq)
      (glaPPrimeCore_subgroupOf_eq_bot hKY hO)
      (IsPGroup.iff_card.mp (I2611.isPGroup_center_pQuot' Nat.prime_three (K.subgroupOf Y)))
      ((T171.catalogIs_pSimple_subgroupOf Y hKY).1 hU)
      (T171.isElemAbelian_subgroupOf Y hBY hB)
      hKBtop hrank' hBc'
      ((T171.innDiagOn_subgroupOf_iff Y hBY hKY).2 hInnB) hAT hAE0
  have hB3 : IsPGroup 3 B := isPGroup_of_isElemAbelian hB
  have hE₀B : E₀.map Y.subtype ≤ B :=
    (Subgroup.map_mono hE₀A).trans (Subgroup.map_subgroupOf_eq_of_le hBY).le
  have hcardE : Nat.card B ≤ 3 * Nat.card (E₀.map Y.subtype) := by
    rw [Subgroup.card_map_of_injective hi]
    calc Nat.card B = Nat.card (B.subgroupOf Y) := (Y10F.card_subgroupOf hBY).symm
      _ ≤ 3 * Nat.card E₀ := hcard
  have hlayE : GLAPLayer 3 (K ⊓ Subgroup.centralizer ((E₀.map Y.subtype : Subgroup G) : Set G)) ≠ ⊥ :=
    (layer_ne_bot_map_iff hKY E₀).2 hlay
  obtain ⟨E, hE₀E, hEB, hPE, hmaxE⟩ := exists_maxLayer (B := B) (E₀ := E₀.map Y.subtype)
    (fun E' => GLAPLayer 3 (K ⊓ Subgroup.centralizer (E' : Set G)) ≠ ⊥) hB3 hE₀B hcardE hlayE
  refine ⟨E, (y : G), J.map Y.subtype, ⟨hEB, hPE, hmaxE⟩, hE₀E (Subgroup.mem_map_of_mem Y.subtype hyE₀),
    ?_, ?_, ?_, ?_⟩
  · intro hc
    apply hynot
    rw [centMod_iff] at hc ⊢
    have h2 := (S267.mem_centModSubgroup_map_iff_inj Nat.prime_three Y.subtype hi
      (J := K.subgroupOf Y) (b := y)).2
    rw [Subgroup.map_subgroupOf_eq_of_le hKY] at h2
    exact h2 hc
  · have h1 := (Y10F.glaPComponent_map_iff Nat.prime_three hi).2 hJ
    rwa [map_inf_centralizer_single Y, Subgroup.map_subgroupOf_eq_of_le hKY] at h1
  · exact ⟨fun hG2 => (hDisj _ n n hG2 hU).elim,
      fun _ => (catalogIs_psimple_map_inj J Y.subtype hi (S10.isUrn n)).1 hJcat⟩
  · refine ⟨T'.map Y.subtype, ?_, hT'2.map Y.subtype, le_normalizer_map Y hBY hT'N, ?_, ?_⟩
    · have h1 := Subgroup.map_mono (f := Y.subtype) hT'C
      rwa [map_inf_centralizer_single Y, Subgroup.map_subgroupOf_eq_of_le hKY] at h1
    · rw [← map_subgroupOf_self hBY, ← Subgroup.map_commutator]
      intro h0
      exact hT'comm ((Subgroup.map_eq_bot_iff_of_injective _ hi).1 h0)
    · exact ⟨fun e => hT'Q.false ((Subgroup.equivMapOfInjective T' Y.subtype hi).trans e)⟩

end U6

section Main

theorem i266R_of_facts (G : Type) [Group G] [Finite G]
    (hInn : ∀ n, T266G2Inn n) (hOdd : ∀ n, T266G2Odd n) (hLayer : ∀ n, T266G2Layer n)
    (hKey : ∀ n, T266G2Key n) (hDisj : T266G2NotU6) (hU6 : ∀ n, T266U6Fact n) : I266AtR G := by
  intro X K B n _hX hK hcases hZg hOg hOu _hZu hB hBN hBX hrank hBc hInnB hT hE0
  rcases hcases with hG2 | ⟨hodd, hn1, hU⟩
  · obtain ⟨T, hTK, hT2, hTN, hTO, -⟩ := hT
    exact i266G2_of_restated G n (hInn n) (hOdd n) (hLayer n) (hKey n) hDisj X K B hK hG2 (hZg hG2) (hOg hG2)
      hB hBN hBc hInnB ⟨T, hTK, hT2, hTN, hTO⟩
  · exact i266U6_of_fact n (hU6 n) hDisj X K B hK hodd hn1 hU (hOu hU) hB hBN hBX hrank hBc hInnB hT hE0

end Main

end CFSG.LocalAnalysis.GLTheoremA.T266

end
