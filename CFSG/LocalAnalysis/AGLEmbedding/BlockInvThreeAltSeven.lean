module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeTypes
import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeRadical
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPL
import CFSG.LocalAnalysis.AGLEmbedding.BlockAltSevenPLAux
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open BlockAltSevenPL

@[expose] def KFactAltSevenTwoLocalInv : Prop :=
  ∀ T : Subgroup (alternatingGroup (Fin 7)), IsPGroup 2 T → T ≠ ⊥ →
    ¬ IsPGroup 2 (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7)))) →
    InvThree (Subgroup.normalizer (T : Set (alternatingGroup (Fin 7))))

namespace BlockInvThree

variable {G : Type} [Group G] [Finite G] {M S L : Subgroup G}

omit [Finite G] in
theorem exists_pow_mul_eq_mul_pow {l s : G} (hl : l ∈ L)
    (hs : s ∈ Subgroup.normalizer (L : Set G)) :
    ∀ k : ℕ, ∃ l' ∈ L, (l * s) ^ k = l' * s ^ k := by
  intro k
  induction k with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨l', hl', he⟩ := ih
    have hc : s ^ k * l * (s ^ k)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (L : Set G)).pow_mem hs k) l).mp hl
    refine ⟨l' * (s ^ k * l * (s ^ k)⁻¹), L.mul_mem hl' hc, ?_⟩
    rw [pow_succ, he, pow_succ]
    group

theorem isPGroup_inf_centralizer_blockU (hsh : IsShort2 L) (hS2 : IsPGroup 2 S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    IsPGroup 2 ((L ⊔ S) ⊓ Subgroup.centralizer (blockU L : Set G) : Subgroup G) := by
  rintro ⟨w, hwLS, hwC⟩
  have hw : w ∈ ((L ⊔ S : Subgroup G) : Set G) := hwLS
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L S hSL] at hw
  obtain ⟨l, hl, s, hs, rfl⟩ := hw
  obtain ⟨a, ha⟩ := hS2 ⟨s, hs⟩
  have ha' : s ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨l', hl', he⟩ := exists_pow_mul_eq_mul_pow hl (hSL hs) (2 ^ a)
  rw [ha', mul_one] at he
  have hmem : (l * s) ^ 2 ^ a ∈ L ⊓ Subgroup.centralizer (blockU L : Set G) :=
    ⟨he ▸ hl', Subgroup.pow_mem _ hwC _⟩
  obtain ⟨b, hb⟩ :=
    (pCoreOf_isPGroup 2 L) ⟨_, CFSG.QuasithinUnique.C1.inf_centralizer_blockU_le hsh hmem⟩
  have hb' : ((l * s) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  refine ⟨a + b, Subtype.ext ?_⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [pow_add, pow_mul, hb']

theorem inf_centralizer_blockU_le_S (hA : Asc81bHyp M S) (hL : IsTwoPrimeComponent M L)
    (hsh : IsShort2 L) (hSL : S ≤ Subgroup.normalizer (L : Set G)) :
    (L ⊔ S) ⊓ Subgroup.centralizer (blockU L : Set G) ≤ S := by
  have hrad := hA.twoCore_eq_pCoreOf_normalizer_sup hL hSL
  refine le_of_two_radical le_sup_right hrad inf_le_left
    (isPGroup_inf_centralizer_blockU hsh hA.twoRadical.isPGroup hSL) ?_
  refine inf_le_left.trans ?_
  refine le_trans ?_ (Subgroup.inf_normalizer_le_normalizer_inf (H := L ⊔ S)
    (K := Subgroup.centralizer (blockU L : Set G)))
  refine le_inf Subgroup.le_normalizer ?_
  have hLSN : L ⊔ S ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSL
  intro x hx
  have hxU := CFSG.QuasithinUnique.C1.mem_normalizer_blockU (hLSN hx)
  apply Subgroup.mem_normalizer_fintype
  intro c hc
  have hc' : c ∈ Subgroup.centralizer (blockU L : Set G) := hc
  show x * c * x⁻¹ ∈ Subgroup.centralizer (blockU L : Set G)
  rw [Subgroup.mem_centralizer_iff] at hc' ⊢
  intro u hu
  have hu' : x⁻¹ * u * x⁻¹⁻¹ ∈ blockU L :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxU) u).mp hu
  have h1 := hc' _ hu'
  calc u * (x * c * x⁻¹) = x * ((x⁻¹ * u * x⁻¹⁻¹) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * u * x⁻¹⁻¹)) * x⁻¹ := by rw [h1]
    _ = x * c * x⁻¹ * u := by group

end BlockInvThree

open BlockInvThree

theorem citedBlockAltSevenInv_of (h86 : Asc81bEightSix) (hA7 : KFactAltSevenTwoLocalInv) :
    CitedBlockAltSevenInv := by
  intro G _ _ M S L hK hA hL hX hS h5
  have hPLnot := not_isPGroup_blockPL h86 hK hA hL hS
  obtain ⟨hsh, ⟨e⟩, hU⟩ := h5
  have hLc := hL.toIsTwoPrimeComponent
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    hLc.le_normalizer (h86 G M S hK hA _ hLc.component) hA.twoRadical.1
  set N := Subgroup.normalizer (L : Set G)
  have hLN : L ≤ N := Subgroup.le_normalizer
  have hNU : N ≤ Subgroup.normalizer (blockU L : Set G) := fun _ hg =>
    CFSG.QuasithinUnique.C1.mem_normalizer_blockU hg
  set ρ : ↥N →* MulAut ↥(blockU L) :=
    (blockU L).normalizerMonoidHom.comp (Subgroup.inclusion hNU)
  have hρ : ∀ (n : ↥N) (u : ↥(blockU L)), ((ρ n u : ↥(blockU L)) : G) = n * u * n⁻¹ :=
    fun _ _ => rfl
  obtain ⟨hΓ, hΓs⟩ := card_mulAut_eq_and_isSimpleGroup (W := ↥(blockU L))
    (fun a b => Subtype.ext (CFSG.QuasithinUnique.C1.blockU_comm hsh a a.2 b
      (CFSG.QuasithinUnique.C1.blockU_le_blockQ hsh b.2)))
    (fun a => Subtype.ext (CFSG.QuasithinUnique.C1.blockU_sq hsh a a.2)) hU
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
  let θ : ↥H ≃* alternatingGroup (Fin 7) := (MulEquiv.subgroupCongr hHr.symm).trans
    (θ₀.symm.trans ((MulEquiv.subgroupCongr hπr).trans e))
  set T := (S.subgroupOf N).map ρ
  set P := ((Subgroup.normalizer (S : Set G) ⊓ L).subgroupOf N).map ρ
  have hNH : ∀ n : ↥N, ρ n ∈ H := fun n => by
    have hH : Nat.card H = 2520 := by
      rw [Nat.card_congr θ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have hn : Subgroup.normalizer ((L.subgroupOf N : Subgroup ↥N) : Set ↥N) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_in_normalizer
    exact mem_of_mem_normalizer_of_index_eight hΓ hH
      (Subgroup.le_normalizer_map ρ ⟨n, by rw [hn]; trivial, rfl⟩)
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
  have hkerρ : ∀ n : ↥N, ρ n = 1 → (n : G) ∈ Subgroup.centralizer (blockU L : Set G) := by
    intro n h1
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h2 := congrArg (fun φ : MulAut ↥(blockU L) => ((φ ⟨u, hu⟩ : ↥(blockU L)) : G)) h1
    simp only [hρ, MulAut.one_apply, Subgroup.coe_inv] at h2
    calc u * n = (n * u * (n : G)⁻¹) * n := by rw [h2]
      _ = n * u := by group
  have hW := inf_centralizer_blockU_le_S hA hLc hsh hSL
  have hNP : Subgroup.normalizer (T : Set (MulAut ↥(blockU L))) ⊓ H ≤ P := by
    rintro h ⟨hhT, ⟨n, hnL, rfl⟩⟩
    have hnL' : (n : G) ∈ L := Subgroup.mem_subgroupOf.mp hnL
    refine ⟨n, Subgroup.mem_subgroupOf.mpr ⟨?_, hnL'⟩, rfl⟩
    apply Subgroup.mem_normalizer_fintype
    intro s hs
    have hsN : s ∈ N := hSL hs
    have himgT : ρ n * ρ ⟨s, hsN⟩ * (ρ n)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hhT _).mp ⟨⟨s, hsN⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    obtain ⟨s', hs', hs'e⟩ := himgT
    have hs'S : (s' : G) ∈ S := Subgroup.mem_subgroupOf.mp hs'
    set w : ↥N := s'⁻¹ * (n * ⟨s, hsN⟩ * n⁻¹) with hwdef
    have hw1 : ρ w = 1 := by
      rw [hwdef, map_mul, map_inv, hs'e, map_mul, map_mul, map_inv, inv_mul_cancel]
    have hwC := hkerρ w hw1
    have hwLS : (w : G) ∈ L ⊔ S := by
      have e2 : (w : G) = (s' : G)⁻¹ * ((n : G) * s * (n : G)⁻¹) := by
        simp [hwdef]
      rw [e2]
      refine (L ⊔ S).mul_mem ((L ⊔ S).inv_mem (Subgroup.mem_sup_right hs'S)) ?_
      exact (L ⊔ S).mul_mem ((L ⊔ S).mul_mem (Subgroup.mem_sup_left hnL')
        (Subgroup.mem_sup_right hs)) ((L ⊔ S).inv_mem (Subgroup.mem_sup_left hnL'))
    have hwS : (w : G) ∈ S := hW ⟨hwLS, hwC⟩
    have e3 : (n : G) * s * (n : G)⁻¹ = (s' : G) * w := by
      simp [hwdef]
    rw [e3]
    exact S.mul_mem hs'S hwS
  have hPiso : Nonempty (↥(barM M (Subgroup.normalizer (S : Set G) ⊓ L)) ≃* ↥P) := by
    set X := (Subgroup.normalizer (S : Set G) ⊓ L).subgroupOf L
    have hk : (π.domRestrict X).ker = (ρL.domRestrict X).ker := by
      rw [MonoidHom.ker_domRestrict, MonoidHom.ker_domRestrict, hker]
    obtain ⟨φ⟩ := nonempty_mulEquiv_range_of_ker_eq hk
    have h1 : (π.domRestrict X).range = barM M (Subgroup.normalizer (S : Set G) ⊓ L) := by
      rw [MonoidHom.domRestrict_range, hbar _ inf_le_right]
    have h2 : (ρL.domRestrict X).range = P := by
      rw [MonoidHom.domRestrict_range, himg _ inf_le_right]
    exact ⟨(MulEquiv.subgroupCongr h1.symm).trans (φ.trans (MulEquiv.subgroupCongr h2))⟩
  obtain ⟨ψ⟩ := hPiso
  have hPnot : ¬ IsPGroup 2 P := fun h2 => hPLnot (h2.of_equiv ψ.symm)
  set T' := T.subgroupOf H
  set T₇ := T'.map θ.toMonoidHom
  have hT₇2 : IsPGroup 2 T₇ := (hT2.comap_subtype (K := H)).map _
  have hT₇1 : T₇ ≠ ⊥ := by
    intro hb
    rw [Subgroup.map_eq_bot_iff_of_injective _ θ.injective] at hb
    exact hT1 ((Subgroup.subgroupOf_eq_bot.mp hb).eq_bot_of_le hTH)
  have hN₇ : Subgroup.normalizer (T₇ : Set (alternatingGroup (Fin 7))) =
      (Subgroup.normalizer (T' : Set ↥H)).map θ.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq T' θ).symm
  have hNT' : (Subgroup.normalizer (T' : Set ↥H)).map H.subtype =
      Subgroup.normalizer (T : Set (MulAut ↥(blockU L))) ⊓ H := by
    rw [← Subgroup.subgroupOf_normalizer_eq hTH, Subgroup.subgroupOf_map_subtype]
  have hN₇not : ¬ IsPGroup 2 (Subgroup.normalizer (T₇ : Set (alternatingGroup (Fin 7)))) := by
    intro h2
    rw [hN₇] at h2
    have h3 : IsPGroup 2 (Subgroup.normalizer (T' : Set ↥H)) :=
      h2.of_equiv ((Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective).symm)
    have h4 : IsPGroup 2 ((Subgroup.normalizer (T' : Set ↥H)).map H.subtype) := h3.map _
    rw [hNT'] at h4
    have hPT : P ≤ Subgroup.normalizer (T : Set (MulAut ↥(blockU L))) := by
      refine le_trans (Subgroup.map_mono fun n hn => ?_) (Subgroup.le_normalizer_map ρ)
      rw [← Subgroup.subgroupOf_normalizer_eq hSL]
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hn).1
    exact hPnot (h4.to_le (le_inf hPT hPH))
  have hInv := hA7 T₇ hT₇2 hT₇1 hN₇not
  rw [hN₇] at hInv
  have hInv' : InvThree (Subgroup.normalizer (T' : Set ↥H)) := by
    have := hInv.map_injective θ.symm.toMonoidHom θ.symm.injective
    rwa [Subgroup.map_map, show θ.symm.toMonoidHom.comp θ.toMonoidHom = MonoidHom.id _ by
      ext x; simp, Subgroup.map_id] at this
  have hInvP : InvThree P := by
    have := hInv'.map_injective H.subtype H.subtype_injective
    rw [hNT'] at this
    exact this.mono hNP
  exact InvThree.of_mulEquiv ψ hInvP.to_top

end CFSG.AGLEmbedding
