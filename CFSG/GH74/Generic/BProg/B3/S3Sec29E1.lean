module

public import CFSG.GH74.Generic.BProg.B3.S3Ctx29Defs
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Th2P61A7
public import CFSG.GH74.GLS.C3.Layer1.Th2P61L2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
  CFSG.GH74.GLS.Th2.Bal CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace S3Sec29E1

section Faithful

theorem card_map_barAct_of_faith {G : Type} [Group G] {D J : Subgroup G}
    (hDN : D ≤ normalizer (J : Set G))
    (hfaith : ∀ d ∈ D, d ≠ 1 → d ∉ centralizerSection J (pPrimeCoreOf 2 J)) :
    Nat.card ((D.subgroupOf (normalizer (J : Set G))).map (barAct J)) = Nat.card D := by
  set M : Subgroup G := normalizer (J : Set G) with hM
  have hbij : Function.Bijective ((barAct J).subgroupMap (D.subgroupOf M)) := by
    refine ⟨?_, (barAct J).subgroupMap_surjective _⟩
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro m hm
    have h1 : barAct J (m : ↥M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hm)
    have hmD : ((m : ↥M) : G) ∈ D := Subgroup.mem_subgroupOf.mp m.2
    by_contra hne
    have hm1 : ((m : ↥M) : G) ≠ 1 := by
      intro h1'
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      exact h1'
    exact hfaith _ hmD hm1 ((barAct_eq_one_iff _).1 h1)
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv

end Faithful

section Obstruction

variable {G : Type} [Group G] [Finite G]

theorem AG_inf_le_normalizer {B : Subgroup G} {b : G} {D J : Subgroup G} (h : Obs52 B b D J)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hbB : b ∈ B) :
    AG D ⊓ centralizer ({b} : Set G) ≤ normalizer (J : Set G) := by
  obtain ⟨hBc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨hDB, hDel, hDr⟩ := h.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  have hDH : D ≤ centralizer ({b} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.mpr (hBc d (hDB hd) b hbB)
  obtain ⟨d₀, hd₀D, hd₀1⟩ := Th2Sig6.exists_ne_one_of_card (k := pRank 2 ↥D) (by omega)
    (C3.Layer1.Back.card_eq_two_pow_pRank hDel)
  exact CFSG.GH74.Generic.BProg.B3.Obs.inf_AG_le_normalizer hDH hDsq h.comp h.D_norm hd₀D hd₀1

theorem centralizes_of_rank_three {B : Subgroup G} {b : G} {D J : Subgroup G} (h : Obs52 B b D J)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hbB : b ∈ B)
    (hloc : IsLocallyKBalanced 3 (kBar J)) (hD3 : 3 ≤ pRank 2 ↥D) :
    AG D ⊓ centralizer ({b} : Set G) ≤ centralizerSection J (pPrimeCoreOf 2 J) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hDB, hDel, hDr⟩ := h.D_le
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  have hYN := AG_inf_le_normalizer h hBel hbB
  intro c hc
  by_contra hcs
  set M : Subgroup G := normalizer (J : Set G) with hM
  set ρ : ↥M →* MulAut (kBar J) := barAct J with hρ
  set Z : Subgroup (MulAut (kBar J)) := ρ.range with hZ
  have hInn : innAut (kBar J) ≤ Z := innAut_le_range_barAct J
  let φ : ↥M →* ↥Z := ρ.rangeRestrict
  have hφ : Function.Surjective φ := MonoidHom.rangeRestrict_surjective ρ
  have hcM : c ∈ M := hYN hc
  have hDM : D ≤ M := h.D_norm
  set F : Subgroup ↥Z := (D.subgroupOf M).map φ with hF
  have hFeq : (D.subgroupOf M).map ρ = F.map Z.subtype := by
    rw [hF, Subgroup.map_map]
    rfl
  have hFcard : Nat.card F = Nat.card D := by
    rw [← card_map_barAct_of_faith hDM h.D_faith, hFeq,
      Subgroup.card_map_of_injective Z.subtype_injective]
  have hF2 : ∀ f ∈ F, f * f = 1 := by
    rintro _ ⟨m, hm, rfl⟩
    rw [← map_mul]
    have : m * m = 1 := Subtype.ext (hDsq m (Subgroup.mem_subgroupOf.mp hm))
    rw [this, map_one]
  have hmem : φ ⟨c, hcM⟩ ∈ deltaCore F := by
    rw [mem_deltaCore_iff]
    rintro _ ⟨m, hm, rfl⟩ hf1
    have hmD : (m : G) ∈ D := Subgroup.mem_subgroupOf.mp hm
    have hm1 : (m : G) ≠ 1 := by
      intro h1
      apply hf1
      have : m = 1 := Subtype.ext h1
      rw [this, map_one]
    have hd2 : (m : G) * (m : G) = 1 := hDsq _ hmD
    exact map_mem_involutionOddCore φ hφ m.2 hd2 hcM (AG_le_pPrimeCoreOf hmD hm1 hc.1)
  have h8 : 2 ^ 3 ≤ Nat.card F := by
    rw [hFcard, C3.Layer1.Back.card_eq_two_pow_pRank hDel]
    exact Nat.pow_le_pow_right (by norm_num) hD3
  have hbot : deltaCore F = ⊥ := hloc Z hInn F h8 hF2
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hcs ((barAct_eq_one_iff ⟨c, hcM⟩).1 (congrArg Subtype.val hmem))

theorem toObsData {B : Subgroup G} {b : G} {D J : Subgroup G} (h : Obs52 B b D J)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hbB : b ∈ B)
    (hloc : IsLocallyKBalanced 3 (kBar J)) : ObsData B b J D := by
  classical
  obtain ⟨hDB, hDel, hDr⟩ := h.D_le
  have h2 : pRank 2 ↥D = 2 ∧ ∃ c ∈ AG D ⊓ centralizer ({b} : Set G), ∃ e ∈ B,
      ⁅c, e⁆ ∉ centralizerSection J (pPrimeCoreOf 2 J) := by
    rcases h.unbal with ⟨h3, hnot⟩ | h2
    · exact absurd (centralizes_of_rank_three h hBel hbB hloc h3.ge) hnot
    · exact h2
  obtain ⟨hD2, c, hc, e, heB, hce⟩ := h2
  have hYN := AG_inf_le_normalizer h hBel hbB
  exact
    { a_mem := hbB
      a_ne := fun h1 => by simpa [h1] using h.b_ord
      comp := h.comp
      D_le := hDB
      D_card := by
        rw [C3.Layer1.Back.card_eq_two_pow_pRank hDel, hD2]
        norm_num
      D_norm := fun d hd => h.D_norm hd
      D_faith := h.D_faith
      X_norm := fun x hx => hYN (commutator_le_Y hBel hDB hbB hx)
      X_move := ⟨⁅c, e⁆, Subgroup.commutator_mem_commutator hc heB, hce⟩ }

end Obstruction

section TypeFacts

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem hasL2Model_of_nonSquare {J : Subgroup G} (h : IsL2OddNonSquare J) :
    HasL2Model (kBar J) Odd := by
  obtain ⟨r, m, hr, hr2, -, hL⟩ := h
  have hodd : Odd (r ^ m) := Odd.pow (hr.odd_of_ne_two hr2)
  obtain ⟨F, _, _, _, -, hcard⟩ := exists_l2Field_of_lieModel hodd hL
  have hm : 1 ≤ m := by
    by_contra hm0
    have hm0' : m = 0 := by omega
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hcard, hm0', pow_zero] at h1
    exact lt_irrefl _ h1
  exact ⟨r, m, hr, hm, hodd, hL⟩

theorem centerless_and_rank {X J : Subgroup G} (hcomp : IsPCompIn 2 X J)
    (ht : IsA7Bar J ∨ IsL2OddNonSquare J) : CenterlessBar J ∧ 2 ≤ pRank 2 ↥J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ?_⟩
  · rcases ht with hA | hL
    · exact centerlessBar_of_A7 hA
    · exact centerlessBar_of_hasL2Model (fun q hq => hq) (hasL2Model_of_nonSquare hL)
  · obtain ⟨P, hP⟩ := exists_isSylowOf 2 J
    have hshape : RankTwoShape P := by
      rcases ht with hA | hL
      · exact rankTwoShape_sylow_A7 hP hA
      · exact rankTwoShape_sylow_L2 hP (TwoThin.isQuasisimple_hat hcomp) (fun q hq => hq)
          (hasL2Model_of_nonSquare hL)
    obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hshape
    have hPJ : P ≤ J := by
      rcases hP with ⟨Q, hQ⟩
      rw [← hQ]
      exact Subgroup.map_subtype_le _
    have hUJ : U ≤ J := hU.1.trans hPJ
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hU.2.1
    have h2 : 2 ^ 2 ≤ 2 ^ pRank 2 ↥U := by rw [← h1, hU.2.2]; norm_num
    have h3 : 2 ≤ pRank 2 ↥U := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
    exact h3.trans (C3.Layer1.Back.pRank_mono' hUJ)

end TypeFacts

section CaseA

variable {G : Type} [Group G] [Finite G]

theorem isLocallyKBalanced_three_of_type
    {J : Subgroup G} (ht : IsA7Bar J ∨ IsL2OddNonSquare J) :
    IsLocallyKBalanced 3 (kBar J) := by
  rcases ht with hA | ⟨r, m, hr, hr2, hm, hL⟩
  · obtain ⟨e⟩ := hA
    exact isLocallyKBalanced_three_of_a7 e
  · obtain ⟨F, _, _, e, hF, -⟩ := exists_l2Field_of_lieModel (Odd.pow (hr.odd_of_ne_two hr2)) hL
    exact isLocallyKBalanced_three_of_l2 hF e

theorem caseA
    {B : Subgroup G} {b : G} {D J : Subgroup G} (h : Obs52 B b D J)
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hbB : b ∈ B) (hBN : ∀ g ∈ B, g ∈ normalizer (J : Set G))
    (ht : IsA7Bar J ∨ IsL2OddNonSquare J) :
    IsA7Bar J ∧ ∀ e : kBar J ≃* alternatingGroup (Fin 7), ∃ F₀ F₁ : Subgroup (Equiv.Perm (Fin 7)),
      IsRootFour F₀ ∧
        (F₁ = ⊥ ∨ ∃ t : Equiv.Perm (Fin 7), t.IsSwap ∧ F₁ = zpowers t ∧
          ∀ i, (∃ f ∈ F₀, f i ≠ i) → t i = i) ∧
        (B.subgroupOf (normalizer (J : Set G))).map (a7Act J e) = F₀ ⊔ F₁ := by
  have hloc := isLocallyKBalanced_three_of_type ht
  have hD := toObsData h hBel hbB hloc
  rcases ht with hA | ⟨r, m, hr, hr2, hm, hL'⟩
  · refine ⟨hA, fun e => ?_⟩
    obtain ⟨t, htw, hdisj, hEeq⟩ := obs_A7_B hD hBel hBN e
    exact ⟨_, zpowers t, obs_root hD hBel e, Or.inr ⟨t, htw, rfl, hdisj⟩, hEeq⟩
  · exfalso
    obtain ⟨F, _, _, e, hF, -⟩ := exists_l2Field_of_lieModel (Odd.pow (hr.odd_of_ne_two hr2)) hL'
    exact obs_L2_not_B hD hBel hBN hF e

end CaseA

end S3Sec29E1

end CFSG.GH74.Generic.BProg.B3
