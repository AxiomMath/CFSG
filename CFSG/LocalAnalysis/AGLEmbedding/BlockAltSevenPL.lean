module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockFoundationsPL
import CFSG.LocalAnalysis.AGLEmbedding.AscEightSix
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPLAux
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique BlockAltSevenPL

namespace BlockAltSevenPL

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
  {ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut ↥(blockU L)}

theorem conj_eq_one_iff_mem_pCoreOf (hsh : IsShort2 L)
    (hρ : ∀ n u, ((ρ n u : ↥(blockU L)) : G) = n * u * n⁻¹)
    {n : ↥(Subgroup.normalizer (L : Set G))} (hn : (n : G) ∈ L) :
    ρ n = 1 ↔ (n : G) ∈ pCoreOf 2 L := by
  constructor
  · intro h1
    refine QuasithinUnique.C1.inf_centralizer_blockU_le hsh ⟨hn, ?_⟩
    show (n : G) ∈ Subgroup.centralizer (blockU L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h2 := congrArg (fun φ : MulAut ↥(blockU L) => ((φ ⟨u, hu⟩ : ↥(blockU L)) : G)) h1
    simp only [hρ, MulAut.one_apply, Subgroup.coe_inv] at h2
    calc u * n = (n * u * (n : G)⁻¹) * n := by rw [h2]
      _ = n * u := by group
  · intro hq
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [hρ, MulAut.one_apply, Subgroup.coe_inv,
      ← QuasithinUnique.C1.blockU_comm hsh u u.2 n hq, mul_inv_cancel_right]

theorem exists_mem_conj_blockU_ne_one {M S : Subgroup G} (hA : Asc81bHyp M S)
    (hL : IsWeakSBlock M S L) (hsh : IsShort2 L)
    (hρ : ∀ n u, ((ρ n u : ↥(blockU L)) : G) = n * u * n⁻¹)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    ∃ s : G, ∃ hs : s ∈ S, ρ ⟨s, hSL hs⟩ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  have key : ∀ l ∈ L, ∀ s ∈ S, l * s * l⁻¹ ∈ S := by
    intro l hl s hs
    set c : ↥(Subgroup.normalizer (L : Set G)) :=
      ⟨l, hLN hl⟩ * ⟨s, hSL hs⟩ * ⟨l, hLN hl⟩⁻¹ * ⟨s, hSL hs⟩⁻¹
    have hcL : (c : G) ∈ L := by
      have h1 : s * l⁻¹ * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hSL hs) l⁻¹).mp (L.inv_mem hl)
      have h2 : (c : G) = l * (s * l⁻¹ * s⁻¹) := by
        simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [h2]
      exact L.mul_mem hl h1
    have hc1 : ρ c = 1 := by simp only [c, map_mul, map_inv, hcon s hs]; group
    have hcS : (c : G) ∈ S := by
      have hcQ := (conj_eq_one_iff_mem_pCoreOf hsh hρ hcL).mp hc1
      rw [← hL.toIsTwoPrimeComponent.inf_twoCore] at hcQ
      exact hA.twoCore_le hcQ.2
    have h3 : l * s * l⁻¹ = c * s := by
      simp only [c, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h3]
    exact S.mul_mem hcS hs
  refine hL.not_le_normalizer fun l hl => Subgroup.mem_normalizer_iff.mpr fun h =>
    ⟨key l hl h, fun hh => ?_⟩
  have h4 := key l⁻¹ (L.inv_mem hl) _ hh
  rwa [show l⁻¹ * (l * h * l⁻¹) * l⁻¹⁻¹ = h by group] at h4

end BlockAltSevenPL

theorem citedBlockAltSevenPL_of_eightSix (h86 : Asc81bEightSix) : CitedBlockAltSevenPL := by
  intro G _ _ M S L hK hA hL _ _ h5
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
  have hbar : ∀ X : Subgroup G, X ≤ L → barM M X = (X.subgroupOf L).map π := fun X hXL => by
    rw [barM, ← map_inclusion_subgroupOf hXL hLc.le, Subgroup.map_map]
  have himg : ∀ X : Subgroup G, X ≤ L → (X.subgroupOf L).map ρL = (X.subgroupOf N).map ρ :=
    fun X hXL => by rw [← Subgroup.map_map, map_inclusion_subgroupOf hXL hLN]
  set H := (L.subgroupOf N).map ρ
  obtain ⟨θ₀⟩ := nonempty_mulEquiv_range_of_ker_eq hker
  have hHr : ρL.range = H := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self L, himg L le_rfl]
  have hπr : π.range = barM M L := by
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self L, hbar L le_rfl]
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
  set P := ((Subgroup.normalizer (S : Set G) ⊓ L).subgroupOf N).map ρ
  have hTH : T ≤ H := by
    rintro _ ⟨n, -, rfl⟩
    exact hNH n
  have hPH : P ≤ H := by
    rintro _ ⟨n, -, rfl⟩
    exact hNH n
  have hT2 : IsPGroup 2 T := (hA.twoRadical.isPGroup.comap_subtype (K := N)).map ρ
  have hT1 : T ≠ ⊥ := by
    obtain ⟨s, hs, hρs⟩ := BlockAltSevenPL.exists_mem_conj_blockU_ne_one hA hL hsh hρ hSL
    intro hbot
    have hmem : ρ ⟨s, hSL hs⟩ ∈ T := ⟨⟨s, hSL hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hρs hmem
  have hPT : P ≤ Subgroup.normalizer (T : Set (MulAut ↥(blockU L))) := by
    refine le_trans (Subgroup.map_mono fun n hn => ?_) (Subgroup.le_normalizer_map ρ)
    rw [← Subgroup.subgroupOf_normalizer_eq hSL]
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hn).1
  have h72 := card_dvd_seventyTwo_of_mulEquiv θ (T := T.subgroupOf H) (P := P.subgroupOf H)
    hT2.comap_subtype (fun h => hT1 ((Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le hTH))
    (fun p hp => by
      rw [← Subgroup.subgroupOf_normalizer_eq hTH]
      exact Subgroup.mem_subgroupOf.mpr (hPT (Subgroup.mem_subgroupOf.mp hp)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv] at h72
  rwa [hbar _ inf_le_right, card_map_eq_card_map_of_ker_eq hker, himg _ inf_le_right]

theorem citedBlockAltSevenPL_holds : CitedBlockAltSevenPL :=
  citedBlockAltSevenPL_of_eightSix
    (asc81bEightSix_of_bhs CFSG.LocalAnalysis.RankThreeTheoremC.bhsLocalCStar_proved)

end CFSG.AGLEmbedding
