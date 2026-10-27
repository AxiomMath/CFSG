module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AltSevenCensus
public import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPLAux
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma55
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.AGLEmbedding.BlockAltSevenPL
open Subgroup

@[expose] def Asc81bASevenBlockAutNX : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 7)) →
    ∀ b (hb : b ∈ M), b ∈ normalizer (S : Set G) → Nat.Coprime (orderOf b) 6 →
      b ∈ normalizer (L : Set G) →
      ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * y =
        y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩

namespace ASevenBlock

variable {G : Type} [Group G] [Finite G]

theorem centralizes_of_nineThreeFive (h86 : Asc81bEightSix) {M S L : Subgroup G}
    (hK : Open.IsKGroup ↥M) (hA : Asc81bHyp M S) (hL : IsWeakSBlock M S L)
    (h5 : NineThreeFive M L) (b : G) (hb : b ∈ M) (hbS : b ∈ normalizer (S : Set G))
    (hcop : Nat.Coprime (orderOf b) 6) (hbL : b ∈ normalizer (L : Set G)) :
    ∀ y ∈ barM M L, QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ * y =
      y * QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩ := by
  obtain ⟨hsh, ⟨e⟩, hU⟩ := h5
  have hLc := hL.toIsTwoPrimeComponent
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    hLc.le_normalizer (h86 G M S hK hA _ hLc.component) hA.twoRadical.1
  set N := Subgroup.normalizer (L : Set G)
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hNU : N ≤ Subgroup.normalizer (blockU L : Set G) := fun _ hg =>
    QuasithinUnique.C1.mem_normalizer_blockU hg
  set ρ : ↥N →* MulAut ↥(blockU L) := (blockU L).normalizerMonoidHom.comp (Subgroup.inclusion hNU)
  have hρ : ∀ (n : ↥N) (u : ↥(blockU L)), ((ρ n u : ↥(blockU L)) : G) = n * u * n⁻¹ :=
    fun _ _ => rfl
  obtain ⟨hΓ, hΓs⟩ := card_mulAut_eq_and_isSimpleGroup (W := ↥(blockU L))
    (fun a b => Subtype.ext (QuasithinUnique.C1.blockU_comm hsh a a.2 b
      (QuasithinUnique.C1.blockU_le_blockQ hsh b.2)))
    (fun a => Subtype.ext (QuasithinUnique.C1.blockU_sq hsh a a.2)) hU
  have : Finite (MulAut ↥(blockU L)) := Nat.finite_of_card_ne_zero (by rw [hΓ]; norm_num)
  set π : ↥L →* ↥M ⧸ CFSG.pCore 2 ↥M := (QuotientGroup.mk' _).comp (Subgroup.inclusion hLc.le)
  set ρL : ↥L →* MulAut ↥(blockU L) := ρ.comp (Subgroup.inclusion hLN)
  have hker : π.ker = ρL.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have e1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hLc.le l) = 1 ↔
        Subgroup.inclusion hLc.le l ∈ CFSG.pCore 2 ↥M := QuotientGroup.eq_one_iff _
    change QuotientGroup.mk' _ (Subgroup.inclusion hLc.le l) = 1 ↔ ρ ⟨l, hLN l.2⟩ = 1
    rw [e1, BlockAltSevenPL.conj_eq_one_iff_mem_pCoreOf hsh hρ (n := ⟨l, hLN l.2⟩) l.2,
      ← hLc.inf_twoCore]
    constructor
    · intro h
      have h' : (l : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := ⟨_, h, rfl⟩
      exact ⟨l.2, h'⟩
    · rintro ⟨-, m, hm, hml⟩
      rw [show Subgroup.inclusion hLc.le l = m from Subtype.ext hml.symm]
      exact hm
  have himg : ∀ X : Subgroup G, X ≤ L → (X.subgroupOf L).map ρL = (X.subgroupOf N).map ρ :=
    fun X hXL => by rw [← Subgroup.map_map, map_inclusion_subgroupOf hXL hLN]
  set H := (L.subgroupOf N).map ρ
  obtain ⟨θ₀⟩ := nonempty_mulEquiv_range_of_ker_eq hker
  have hHr : ρL.range = H := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self L, himg L le_rfl]
  have hπr : π.range = barM M L := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self L, barM,
      ← map_inclusion_subgroupOf le_rfl hLc.le, Subgroup.map_map]
  let θ : ↥H ≃* alternatingGroup (Fin 7) :=
    (MulEquiv.subgroupCongr hHr.symm).trans (θ₀.symm.trans ((MulEquiv.subgroupCongr hπr).trans e))
  have hH : Nat.card H = 2520 := by
    rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hNH : ∀ n : ↥N, ρ n ∈ H := fun n => by
    have hn : Subgroup.normalizer ((L.subgroupOf N : Subgroup ↥N) : Set ↥N) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_in_normalizer
    exact mem_of_mem_normalizer_of_index_eight hΓ hH
      (Subgroup.le_normalizer_map ρ ⟨n, by rw [hn]; trivial, rfl⟩)
  set T := (S.subgroupOf N).map ρ
  have hTH : T ≤ H := by
    rintro _ ⟨n, -, rfl⟩
    exact hNH n
  have hT2 : IsPGroup 2 T := (hA.twoRadical.isPGroup.comap_subtype (K := N)).map ρ
  have hT1 : T ≠ ⊥ := by
    obtain ⟨s, hs, hρs⟩ := BlockAltSevenPL.exists_mem_conj_blockU_ne_one hA hL hsh hρ hSL
    intro hbot
    have hmem : ρ ⟨s, hSL hs⟩ ∈ T := ⟨⟨s, hSL hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hρs hmem
  set nb : ↥N := ⟨b, hbL⟩
  have hnbT : ρ nb ∈ Subgroup.normalizer (T : Set (MulAut ↥(blockU L))) := by
    have hnS : nb ∈ Subgroup.normalizer ((S.subgroupOf N : Subgroup ↥N) : Set ↥N) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hSL]
      exact Subgroup.mem_subgroupOf.mpr hbS
    exact Subgroup.le_normalizer_map ρ ⟨nb, hnS, rfl⟩
  have hP : zpowers (ρ nb) ≤ H := (zpowers_le).mpr (hNH nb)
  have h72 := card_dvd_seventyTwo_of_mulEquiv θ (T := T.subgroupOf H)
    (P := (zpowers (ρ nb)).subgroupOf H)
    hT2.comap_subtype (fun h => hT1 ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hTH))
    (fun p hp => by
      rw [← Subgroup.subgroupOf_normalizer_eq hTH]
      exact Subgroup.mem_subgroupOf.mpr ((zpowers_le.mpr hnbT) (Subgroup.mem_subgroupOf.mp hp)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv, Nat.card_zpowers] at h72
  have hdvd : orderOf (ρ nb) ∣ orderOf b := by
    have := orderOf_map_dvd ρ nb
    rwa [Subgroup.orderOf_mk] at this
  have hρb : ρ nb = 1 := by
    have hc : Nat.Coprime (orderOf (ρ nb)) 72 :=
      Nat.Coprime.coprime_dvd_left hdvd (by
        rw [show (72 : ℕ) = 6 ^ 2 * 2 by norm_num]
        exact Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 hcop)
          (Nat.Coprime.coprime_dvd_right (by norm_num) hcop))
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc h72)
  rintro _ ⟨⟨l, hlM⟩, hl, rfl⟩
  have hlL : l ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hcL : b * l * b⁻¹ * l⁻¹ ∈ L :=
    L.mul_mem ((mem_normalizer_iff.mp hbL l).mp hlL) (L.inv_mem hlL)
  have hc1 : ρ ⟨b * l * b⁻¹ * l⁻¹, hLN hcL⟩ = 1 := by
    have : (⟨b * l * b⁻¹ * l⁻¹, hLN hcL⟩ : ↥N) = nb * ⟨l, hLN hlL⟩ * nb⁻¹ * ⟨l, hLN hlL⟩⁻¹ :=
      Subtype.ext (by simp [nb])
    rw [this, map_mul, map_mul, map_mul, map_inv, map_inv, hρb]
    group
  have hcO : b * l * b⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
    (BlockAltSevenPL.conj_eq_one_iff_mem_pCoreOf hsh hρ (n := ⟨_, hLN hcL⟩) hcL).mp hc1
  rw [← hLc.inf_twoCore] at hcO
  obtain ⟨m, hm, hml⟩ := hcO.2
  have heq : (⟨b, hb⟩ * ⟨l, hlM⟩ * (⟨b, hb⟩ : M)⁻¹ * (⟨l, hlM⟩ : M)⁻¹ : M) = m :=
    Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; exact hml.symm)
  have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      ((⟨b, hb⟩ : M) * ⟨l, hlM⟩ * (⟨b, hb⟩ : M)⁻¹ * (⟨l, hlM⟩ : M)⁻¹) = 1 := by
    rw [heq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hm
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hq
  set bq := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨b, hb⟩
  set lq := QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩
  calc bq * lq = (bq * lq * bq⁻¹ * lq⁻¹) * (lq * bq) := by group
    _ = lq * bq := by rw [hq, one_mul]

theorem eq_seven_of_card_alternatingGroup {m : ℕ} (h : Nat.card (alternatingGroup (Fin m)) = 2520) :
    m = 7 := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · exfalso
    have h1 : Nat.card (Equiv.Perm (Fin m)) = 1 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      interval_cases m <;> rfl
    have h2 := Subgroup.card_le_card_group (alternatingGroup (Fin m))
    omega
  · haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
    have h2 := two_mul_card_alternatingGroup (α := Fin m)
    rw [Fintype.card_perm, Fintype.card_fin, ← Nat.card_eq_fintype_card, h] at h2
    have h7 : (7 : ℕ).factorial = m.factorial := by rw [← h2]; decide
    exact ((Nat.factorial_inj (by norm_num : 1 < 7)).mp h7).symm

theorem isClassicalTwoOrG2_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsClassicalTwoOrG2 X) : IsClassicalTwoOrG2 Y := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩)

theorem isOrthogonalTwo_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsOrthogonalTwo X) : IsOrthogonalTwo Y := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨n, hn, ⟨e.symm.trans f⟩⟩

theorem nineThreeFive_of_altSeven
    (hord : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group = CFSG.Open.ordG2 q.card)
    {M S L : Subgroup G} (hX : ¬ InClassXBlock L) (h93 : NineThreeConclusion M S L)
    (e : ↥(barM M L) ≃* alternatingGroup (Fin 7)) : NineThreeFive M L := by
  have hcen := CFSG.ComponentClassification.GSThmB.center_eq_bot_of_mulEquiv_alternating
    (by norm_num : 4 ≤ 7) e
  have eZ : ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃* alternatingGroup (Fin 7) :=
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).trans e
  have hcardA : ∀ {m : ℕ}, (alternatingGroup (Fin 7) ≃* alternatingGroup (Fin m)) → m = 7 :=
    fun f => eq_seven_of_card_alternatingGroup
      ((Nat.card_congr f.toEquiv).symm.trans AltSevenCensus.card_alternatingGroup_seven)
  rcases h93 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
  · exact (hX h1).elim
  · exact ((AltSevenCensus.not_isClassicalTwoOrG2_alt_seven_of_G2_formula hord)
      (isClassicalTwoOrG2_congr eZ h2.1)).elim
  · exact (AltSevenCensus.not_isOrthogonalTwo_alt_seven (isOrthogonalTwo_congr e h3.2.1)).elim
  · obtain ⟨-, hZ, -⟩ := h4
    rw [hcen] at hZ
    simp at hZ
  · exact h5
  · obtain ⟨-, n, ⟨e6⟩, -⟩ := h6
    have := hcardA (eZ.symm.trans e6)
    omega
  · obtain ⟨-, n, ⟨e7⟩, -⟩ := h7
    have := hcardA (e.symm.trans e7)
    omega
  · obtain ⟨-, N, r, hNe, -, -, -, -, ⟨e8⟩, -⟩ := h8
    have := hcardA (e.symm.trans e8)
    obtain ⟨k, hk⟩ := hNe
    omega

end ASevenBlock

theorem asc81bASevenBlockAutNX_holds (h86 : Asc81bEightSix) (h93 : Asc81bNineThree)
    (hord : ∀ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
      Nat.card (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group = CFSG.Open.ordG2 q.card) :
    Asc81bASevenBlockAutNX := fun G _ _ M S L hK hA hL hX ⟨e⟩ b hb hbS hcop hbL =>
  ASevenBlock.centralizes_of_nineThreeFive h86 hK hA hL
    (ASevenBlock.nineThreeFive_of_altSeven hord hX (h93 G M S L hK hA hL) e) b hb hbS hcop hbL

end CFSG.LocalAnalysis.RankThreeTheoremC
