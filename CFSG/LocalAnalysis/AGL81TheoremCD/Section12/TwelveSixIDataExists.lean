module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIData
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixIDataLift
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixNoExtraspecial
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSevenSylow
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.BarBlocks
import CFSG.LocalAnalysis.AGLEmbedding.CZeroBasic
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFBar
import CFSG.GroupTheory.CoprimeCentralizerCover
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.PGroup.CardCoprime

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

private theorem le_normalizer_of_cZero_eq_singleton {X K I : Subgroup G}
    (hX : cZero X = {I}) (hKX : K ≤ Subgroup.normalizer (X : Set G)) :
    K ≤ Subgroup.normalizer (I : Set G) := by
  intro k hk
  have hI : IsCZeroMember X I := by
    change I ∈ cZero X
    rw [hX]
    simp
  have hmem : I.map (MulAut.conj k).toMonoidHom ∈ cZero X :=
    IsCZeroMember.map_conj hI (hKX hk)
  rw [hX] at hmem
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa using hmem)

private theorem normalize_of_cZero {H L L' I I' : Subgroup G}
    (hI' : cZero (H ⊓ L') = {I'}) (hIH : I ≤ H) (hIL : I ≤ L)
    (hLL' : L ≤ Subgroup.normalizer (L' : Set G)) :
    I ≤ Subgroup.normalizer (I' : Set G) :=
  le_normalizer_of_cZero_eq_singleton hI'
    ((le_inf (hIH.trans Subgroup.le_normalizer) (hIL.trans hLL')).trans
      Subgroup.inf_normalizer_le_normalizer_inf)

private theorem commutator_I_le_pCoreOf {L L' I I' : Subgroup G}
    (hL : L ∈ weakBlockSet M H) (hL' : L' ∈ weakBlockSet M H) (hne : L ≠ L')
    (hIL : I ≤ L) (hI'L' : I' ≤ L') :
    ⁅I, I'⁆ ≤ CFSG.Open.pCoreOf 2 M :=
  (Subgroup.commutator_mono hIL hI'L').trans
    (hL.toIsTwoPrimeComponent.commutator_le hL'.toIsTwoPrimeComponent hne)

private theorem mem_pCoreOf_of_mem_bot {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈
      (⊥ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M))) :
    x ∈ CFSG.Open.pCoreOf 2 M := by
  have h1 : (⟨x, hxM⟩ : ↥M) ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.eq_one_iff]
    simpa [QuotientGroup.mk'_apply] using hmem
  exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, h1, rfl⟩

private theorem le_pCoreOf_of_barM_inf_eq_bot {M L L' : Subgroup G}
    (hbot : barM M L ⊓ barM M L' = ⊥) (hL : L ≤ M) (hL' : L' ≤ M) :
    L ⊓ L' ≤ CFSG.Open.pCoreOf 2 M := by
  intro x hx
  have hxM : x ∈ M := hL hx.1
  have hclass : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈
      barM M L ⊓ barM M L' :=
    ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx.1),
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx.2)⟩
  rw [hbot] at hclass
  exact mem_pCoreOf_of_mem_bot hxM hclass

private theorem le_pCoreOf_of_barM_sup_inf_eq_bot {M L L' L'' : Subgroup G}
    (hbot : (barM M L ⊔ barM M L') ⊓ barM M L'' = ⊥)
    (hL : L ≤ M) (hL' : L' ≤ M) (hL'' : L'' ≤ M) :
    (L ⊔ L') ⊓ L'' ≤ CFSG.Open.pCoreOf 2 M := by
  intro x hx
  have hxM : x ∈ M := hL'' hx.2
  have hxL : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈ barM M (L ⊔ L') :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx.1)
  rw [CFSG.AGLEmbedding.barM_sup hL hL'] at hxL
  have hclass : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hxM⟩ ∈
      (barM M L ⊔ barM M L') ⊓ barM M L'' :=
    ⟨hxL, Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx.2)⟩
  rw [hbot] at hclass
  exact mem_pCoreOf_of_mem_bot hxM hclass

private theorem coprime_cover {X R : Subgroup G} (hXM : X ≤ M)
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hRM : R ≤ M) (hR : IsPGroup 3 R)
    (hcomm : ⁅X, R⁆ ≤ CFSG.Open.pCoreOf 2 M) :
    X ⊓ Subgroup.centralizer (R : Set G) ⊔ (X ⊓ CFSG.Open.pCoreOf 2 M) = X := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNle : X ⊓ CFSG.Open.pCoreOf 2 M ≤ X := inf_le_left
  have hRN : R ≤ Subgroup.normalizer ((X ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) :=
    (le_inf hRX (hRM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hNp : ¬ 3 ∣ Nat.card ↥(X ⊓ CFSG.Open.pCoreOf 2 M) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M).to_le inf_le_right)
      Nat.prime_three (by norm_num)
  have hcommX : ⁅X, R⁆ ≤ X ⊓ CFSG.Open.pCoreOf 2 M :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hRX) hcomm
  exact CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le hNle hRX hRN hR hNp hcommX

private theorem conj_mem_comap_of_inv {I V W : Subgroup G} {s : G}
    (hWV : W ≤ V) (hinv : ∀ w ∈ W, s * w * s⁻¹ = w⁻¹) :
    W ≤ (V ⊔ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)).comap (MulAut.conj s).toMonoidHom := by
  intro w hw
  rw [Subgroup.mem_comap]
  change MulAut.conj s w ∈ V ⊔ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)
  rw [MulAut.conj_apply, hinv w hw]
  exact Subgroup.mem_sup_left (V.inv_mem (hWV hw))

private theorem conj_mem_comap_of_commutator {I Ii V W : Subgroup G} {s : G}
    (hIiI : Ii ≤ I) (hVI : V ≤ I) (hWV : W ≤ V) (hs : s ∈ Ii)
    (hcomm : ⁅Ii, W⁆ ≤ CFSG.Open.pCoreOf 2 M) :
    W ≤ (V ⊔ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)).comap (MulAut.conj s).toMonoidHom := by
  intro w hw
  rw [Subgroup.mem_comap]
  change MulAut.conj s w ∈ V ⊔ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)
  rw [MulAut.conj_apply]
  have hcP : ⁅s, w⁆ ∈ CFSG.Open.pCoreOf 2 M :=
    hcomm (Subgroup.commutator_mem_commutator hs hw)
  have hcI : ⁅s, w⁆ ∈ I :=
    Subgroup.commutator_le_of_le hIiI (hWV.trans hVI)
      (Subgroup.commutator_mem_commutator hs hw)
  have hcO : ⁅s, w⁆ ∈ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) := ⟨hcI, hcP⟩
  have heq : s * w * s⁻¹ = ⁅s, w⁆ * w := by
    rw [commutatorElement_def]
    group
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hcO)
    (Subgroup.mem_sup_left (hWV hw))

private theorem maps_V_into_sup {I V W W' W'' : Subgroup G} {s : G}
    (hJOIN : V = W ⊔ W' ⊔ W'')
    (hW : W ≤ (V ⊔ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)).comap
      (MulAut.conj s).toMonoidHom)
    (hW' : W' ≤ (V ⊔ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)).comap
      (MulAut.conj s).toMonoidHom)
    (hW'' : W'' ≤ (V ⊔ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)).comap
      (MulAut.conj s).toMonoidHom) :
    ∀ v ∈ V, s * v * s⁻¹ ∈ V ⊔ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) := by
  intro v hv
  have hle : V ≤ (V ⊔ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)).comap
      (MulAut.conj s).toMonoidHom := by
    have hWle : W ⊔ W' ⊔ W'' ≤ (V ⊔ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)).comap
        (MulAut.conj s).toMonoidHom :=
      sup_le (sup_le hW hW') hW''
    rwa [← hJOIN] at hWle
  exact hle hv

private theorem inf_twoCore_eq_bot {I V : Subgroup G} (hV : IsPGroup 3 V) :
    (V ⊓ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Subgroup G) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) V ((I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)) hV
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M).to_le inf_le_right)).eq_bot

private theorem exists_conj_mem_sup_data {I Ii V W W' W'' : Subgroup G} {s : G}
    (hIM : I ≤ M) (hIiI : Ii ≤ I) (hVI : V ≤ I) (hV : IsPGroup 3 V)
    (hJOIN : V = W ⊔ W' ⊔ W'')
    (hWV : W ≤ V) (hW'V : W' ≤ V) (hW''V : W'' ≤ V)
    (hs : s ∈ Ii) (hinv : ∀ w ∈ W, s * w * s⁻¹ = w⁻¹)
    (hcomm' : ⁅Ii, W'⁆ ≤ CFSG.Open.pCoreOf 2 M)
    (hcomm'' : ⁅Ii, W''⁆ ≤ CFSG.Open.pCoreOf 2 M) :
    ∃ t ∈ I, ∀ v ∈ V, t * v * t⁻¹ ∈ V ∧
      (s * v * s⁻¹)⁻¹ * (t * v * t⁻¹) ∈ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) := by
  have hOI : (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) ≤ I := inf_le_left
  have hIO : I ≤ Subgroup.normalizer
      ((I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer
      (hIM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hO : IsPGroup 2 (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M).to_le inf_le_right
  have hWcomp := conj_mem_comap_of_inv (M := M) (I := I) hWV hinv
  have hW'comp := conj_mem_comap_of_commutator (M := M) (I := I) hIiI hVI hW'V hs hcomm'
  have hW''comp := conj_mem_comap_of_commutator (M := M) (I := I) hIiI hVI hW''V hs hcomm''
  have hsV := maps_V_into_sup (M := M) (I := I) hJOIN hWcomp hW'comp hW''comp
  exact exists_conj_mem_of_conj_mem_sup hOI hIO hO hVI hV (hIiI hs) hsV

private theorem inv_of_conj_mem_sup {I V W : Subgroup G} {s t : G}
    (hWV : W ≤ V) (hV : IsPGroup 3 V)
    (hinv : ∀ w ∈ W, s * w * s⁻¹ = w⁻¹)
    (ht : ∀ v ∈ V, t * v * t⁻¹ ∈ V ∧
      (s * v * s⁻¹)⁻¹ * (t * v * t⁻¹) ∈ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)) :
    ∀ w ∈ W, t * w * t⁻¹ = w⁻¹ := by
  intro w hw
  obtain ⟨htV, htO⟩ := ht w (hWV hw)
  have hprodO : w * (t * w * t⁻¹) ∈ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) := by
    have h := htO
    rwa [hinv w hw, inv_inv] at h
  have hprodV : w * (t * w * t⁻¹) ∈ V := V.mul_mem (hWV hw) htV
  have hbot := inf_twoCore_eq_bot (M := M) (I := I) hV
  have hone : w * (t * w * t⁻¹) = 1 := by
    have hmem : w * (t * w * t⁻¹) ∈
        (V ⊓ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Subgroup G) :=
      ⟨hprodV, hprodO⟩
    rw [hbot] at hmem
    simpa using hmem
  exact eq_inv_of_mul_eq_one_right hone

private theorem commutes_of_conj_mem_sup {I Ii V W : Subgroup G} {s t : G}
    (hIiI : Ii ≤ I) (hVI : V ≤ I) (hWV : W ≤ V) (hs : s ∈ Ii)
    (hV : IsPGroup 3 V) (hcomm : ⁅Ii, W⁆ ≤ CFSG.Open.pCoreOf 2 M)
    (ht : ∀ v ∈ V, t * v * t⁻¹ ∈ V ∧
      (s * v * s⁻¹)⁻¹ * (t * v * t⁻¹) ∈ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G)) :
    ∀ w ∈ W, t * w = w * t := by
  intro w hw
  obtain ⟨htV, htO⟩ := ht w (hWV hw)
  have hc1P : ⁅w⁻¹, s⁆ ∈ CFSG.Open.pCoreOf 2 M := by
    have hmem : ⁅w⁻¹, s⁆ ∈ ⁅W, Ii⁆ :=
      Subgroup.commutator_mem_commutator (W.inv_mem hw) hs
    rw [Subgroup.commutator_comm] at hmem
    exact hcomm hmem
  have hc1I : ⁅w⁻¹, s⁆ ∈ I :=
    Subgroup.commutator_le_of_le (hWV.trans hVI) hIiI
      (Subgroup.commutator_mem_commutator (W.inv_mem hw) hs)
  have hc1O : ⁅w⁻¹, s⁆ ∈ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) := ⟨hc1I, hc1P⟩
  have hprodO : w⁻¹ * (t * w * t⁻¹) ∈ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) := by
    have heq : w⁻¹ * (t * w * t⁻¹) =
        ⁅w⁻¹, s⁆ * ((s * w * s⁻¹)⁻¹ * (t * w * t⁻¹)) := by
      rw [commutatorElement_def]
      group
    rw [heq]
    exact (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G).mul_mem hc1O htO
  have hprodV : w⁻¹ * (t * w * t⁻¹) ∈ V :=
    V.mul_mem (V.inv_mem (hWV hw)) htV
  have hbot := inf_twoCore_eq_bot (M := M) (I := I) hV
  have hone : w⁻¹ * (t * w * t⁻¹) = 1 := by
    have hmem : w⁻¹ * (t * w * t⁻¹) ∈
        (V ⊓ (I ⊓ CFSG.Open.pCoreOf 2 M : Subgroup G) : Subgroup G) :=
      ⟨hprodV, hprodO⟩
    rw [hbot] at hmem
    simpa using hmem
  have htw : t * w * t⁻¹ = w := (inv_mul_eq_one.mp hone).symm
  calc t * w = (t * w * t⁻¹) * t := by group
    _ = w * t := by rw [htw]

private theorem commute_on_sup {W' W'' : Subgroup G} {t : G}
    (h' : ∀ w ∈ W', t * w = w * t) (h'' : ∀ w ∈ W'', t * w = w * t) :
    ∀ w ∈ W' ⊔ W'', t * w = w * t := by
  have hle : W' ⊔ W'' ≤ Subgroup.centralizer ({t} : Set G) := by
    refine sup_le ?_ ?_
    · intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h' w hw
    · intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h'' w hw
  intro w hw
  exact Subgroup.mem_centralizer_iff.mp (hle hw) t (by simp)

private theorem exists_inverting_conj {I Ii V W W' W'' : Subgroup G} {s : G}
    (hIM : I ≤ M) (hIiI : Ii ≤ I) (hVI : V ≤ I) (hV : IsPGroup 3 V)
    (hJOIN : V = W ⊔ W' ⊔ W'')
    (hWV : W ≤ V) (hW'V : W' ≤ V) (hW''V : W'' ≤ V)
    (hs : s ∈ Ii) (hinv : ∀ w ∈ W, s * w * s⁻¹ = w⁻¹)
    (hcomm' : ⁅Ii, W'⁆ ≤ CFSG.Open.pCoreOf 2 M)
    (hcomm'' : ⁅Ii, W''⁆ ≤ CFSG.Open.pCoreOf 2 M) :
    ∃ t ∈ I, (∀ w ∈ W, t * w * t⁻¹ = w⁻¹) ∧
      ∀ w ∈ W' ⊔ W'', t * w = w * t := by
  obtain ⟨t, htI, ht⟩ :=
    exists_conj_mem_sup_data (M := M) hIM hIiI hVI hV hJOIN hWV hW'V hW''V hs hinv hcomm' hcomm''
  exact ⟨t, htI, inv_of_conj_mem_sup hWV hV hinv ht,
    commute_on_sup
      (commutes_of_conj_mem_sup hIiI hVI hW'V hs hV hcomm' ht)
      (commutes_of_conj_mem_sup hIiI hVI hW''V hs hV hcomm'' ht)⟩

private structure IRaw (H : Subgroup G) (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ) where
  I₁ : Subgroup G
  I₂ : Subgroup G
  I₃ : Subgroup G
  cZero₁ : cZero (H ⊓ L₁) = {I₁}
  cZero₂ : cZero (H ⊓ L₂) = {I₂}
  cZero₃ : cZero (H ⊓ L₃) = {I₃}
  type₁ : IsPSLType 2 (GaloisField 2 n₁) (modTwoCore I₁)
  type₂ : IsPSLType 2 (GaloisField 2 n₂) (modTwoCore I₂)
  type₃ : IsPSLType 2 (GaloisField 2 n₃) (modTwoCore I₃)

private structure IBasic (M : Subgroup G) (H : Subgroup G)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ)
    extends IRaw H L₁ L₂ L₃ n₁ n₂ n₃ where
  leH₁ : I₁ ≤ H
  leH₂ : I₂ ≤ H
  leH₃ : I₃ ≤ H
  leL₁ : I₁ ≤ L₁
  leL₂ : I₂ ≤ L₂
  leL₃ : I₃ ≤ L₃
  leM₁ : I₁ ≤ M
  leM₂ : I₂ ≤ M
  leM₃ : I₃ ≤ M

private structure IData (M : Subgroup G) (H : Subgroup G)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ)
    extends IBasic M H L₁ L₂ L₃ n₁ n₂ n₃ where
  normalize₁₂ : I₁ ≤ Subgroup.normalizer (I₂ : Set G)
  normalize₁₃ : I₁ ≤ Subgroup.normalizer (I₃ : Set G)
  normalize₂₁ : I₂ ≤ Subgroup.normalizer (I₁ : Set G)
  normalize₂₃ : I₂ ≤ Subgroup.normalizer (I₃ : Set G)
  normalize₃₁ : I₃ ≤ Subgroup.normalizer (I₁ : Set G)
  normalize₃₂ : I₃ ≤ Subgroup.normalizer (I₂ : Set G)
  comm₁₂ : ⁅I₁, I₂⁆ ≤ CFSG.Open.pCoreOf 2 M
  comm₁₃ : ⁅I₁, I₃⁆ ≤ CFSG.Open.pCoreOf 2 M
  comm₂₃ : ⁅I₂, I₃⁆ ≤ CFSG.Open.pCoreOf 2 M

private structure W1Data (M : Subgroup G) (H : Subgroup G)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ)
    extends IData M H L₁ L₂ L₃ n₁ n₂ n₃ where
  W₁ : Subgroup G
  s₁ : G
  leW₁ : W₁ ≤ I₁
  cardW₁ : Nat.card W₁ = 3
  mems₁ : s₁ ∈ I₁
  inv₁ : ∀ w ∈ W₁, s₁ * w * s₁⁻¹ = w⁻¹

private structure W2Data (M : Subgroup G) (H : Subgroup G)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ)
    extends W1Data M H L₁ L₂ L₃ n₁ n₂ n₃ where
  W₂ : Subgroup G
  s₂ : G
  leW₂ : W₂ ≤ I₂
  leW₂C₁ : W₂ ≤ Subgroup.centralizer (W₁ : Set G)
  cardW₂ : Nat.card W₂ = 3
  mems₂ : s₂ ∈ I₂ ⊓ Subgroup.centralizer (W₁ : Set G)
  inv₂ : ∀ w ∈ W₂, s₂ * w * s₂⁻¹ = w⁻¹

private structure W3Data (M : Subgroup G) (H : Subgroup G)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ)
    extends W2Data M H L₁ L₂ L₃ n₁ n₂ n₃ where
  W₃ : Subgroup G
  s₃ : G
  leW₃ : W₃ ≤ I₃
  leW₃C₁ : W₃ ≤ Subgroup.centralizer (W₁ : Set G)
  leW₃C₂ : W₃ ≤ Subgroup.centralizer (W₂ : Set G)
  cardW₃ : Nat.card W₃ = 3
  mems₃ : s₃ ∈ I₃ ⊓ Subgroup.centralizer (W₁ : Set G) ⊓
    Subgroup.centralizer (W₂ : Set G)
  inv₃ : ∀ w ∈ W₃, s₃ * w * s₃⁻¹ = w⁻¹

private structure VData (M : Subgroup G) (H : Subgroup G)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ)
    extends W3Data M H L₁ L₂ L₃ n₁ n₂ n₃ where
  V : Subgroup G
  joinV : V = W₁ ⊔ W₂ ⊔ W₃
  elemV : IsElemAbelian 3 V
  cardV : Nat.card V = 27

private structure T1Data (M : Subgroup G) (H : Subgroup G)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ)
    extends VData M H L₁ L₂ L₃ n₁ n₂ n₃ where
  t₁ : G
  memt₁ : t₁ ∈ I₁ ⊔ I₂ ⊔ I₃
  invt₁ : ∀ w ∈ W₁, t₁ * w * t₁⁻¹ = w⁻¹
  commt₁ : ∀ w ∈ W₂ ⊔ W₃, t₁ * w = w * t₁

private structure T2Data (M : Subgroup G) (H : Subgroup G)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ)
    extends T1Data M H L₁ L₂ L₃ n₁ n₂ n₃ where
  t₂ : G
  memt₂ : t₂ ∈ I₁ ⊔ I₂ ⊔ I₃
  invt₂ : ∀ w ∈ W₂, t₂ * w * t₂⁻¹ = w⁻¹
  commt₂ : ∀ w ∈ W₁ ⊔ W₃, t₂ * w = w * t₂

private structure T3Data (M : Subgroup G) (H : Subgroup G)
    (L₁ L₂ L₃ : Subgroup G) (n₁ n₂ n₃ : ℕ)
    extends T2Data M H L₁ L₂ L₃ n₁ n₂ n₃ where
  t₃ : G
  memt₃ : t₃ ∈ I₁ ⊔ I₂ ⊔ I₃
  invt₃ : ∀ w ∈ W₃, t₃ * w * t₃⁻¹ = w⁻¹
  commt₃ : ∀ w ∈ W₁ ⊔ W₂, t₃ * w = w * t₃

private theorem exists_IRaw (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hIM : TwelveSixIMember) : Nonempty (IRaw H L₁ L₂ L₃ n₁ n₂ n₃) := by
  obtain ⟨I₁, hcZ₁, htype₁⟩ :=
    hIM G M p Q H L₁ n₁ hc.ctx hc.data.mem₁ hc.data.odd₁ hc.data.type₁
  obtain ⟨I₂, hcZ₂, htype₂⟩ :=
    hIM G M p Q H L₂ n₂ hc.ctx hc.data.mem₂ hc.data.odd₂ hc.data.type₂
  obtain ⟨I₃, hcZ₃, htype₃⟩ :=
    hIM G M p Q H L₃ n₃ hc.ctx hc.data.mem₃ hc.data.odd₃ hc.data.type₃
  exact ⟨IRaw.mk I₁ I₂ I₃ hcZ₁ hcZ₂ hcZ₃ htype₁ htype₂ htype₃⟩

private theorem build_IBasic (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : IRaw H L₁ L₂ L₃ n₁ n₂ n₃) : Nonempty (IBasic M H L₁ L₂ L₃ n₁ n₂ n₃) := by
  have hImem₁ : IsCZeroMember (H ⊓ L₁) D.I₁ := by
    change D.I₁ ∈ cZero (H ⊓ L₁)
    rw [D.cZero₁]
    simp
  have hImem₂ : IsCZeroMember (H ⊓ L₂) D.I₂ := by
    change D.I₂ ∈ cZero (H ⊓ L₂)
    rw [D.cZero₂]
    simp
  have hImem₃ : IsCZeroMember (H ⊓ L₃) D.I₃ := by
    change D.I₃ ∈ cZero (H ⊓ L₃)
    rw [D.cZero₃]
    simp
  have hI₁H : D.I₁ ≤ H := hImem₁.le.trans inf_le_left
  have hI₂H : D.I₂ ≤ H := hImem₂.le.trans inf_le_left
  have hI₃H : D.I₃ ≤ H := hImem₃.le.trans inf_le_left
  have hI₁L₁ : D.I₁ ≤ L₁ := hImem₁.le.trans inf_le_right
  have hI₂L₂ : D.I₂ ≤ L₂ := hImem₂.le.trans inf_le_right
  have hI₃L₃ : D.I₃ ≤ L₃ := hImem₃.le.trans inf_le_right
  have hI₁M : D.I₁ ≤ M := hI₁L₁.trans hc.data.mem₁.le
  have hI₂M : D.I₂ ≤ M := hI₂L₂.trans hc.data.mem₂.le
  have hI₃M : D.I₃ ≤ M := hI₃L₃.trans hc.data.mem₃.le
  exact ⟨⟨D, hI₁H, hI₂H, hI₃H, hI₁L₁, hI₂L₂, hI₃L₃, hI₁M, hI₂M, hI₃M⟩⟩

private theorem build_IData (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : IBasic M H L₁ L₂ L₃ n₁ n₂ n₃) : Nonempty (IData M H L₁ L₂ L₃ n₁ n₂ n₃) := by
  have h₁₂ : D.I₁ ≤ Subgroup.normalizer (D.I₂ : Set G) :=
    normalize_of_cZero D.cZero₂ D.leH₁ D.leL₁
      (le_normalizer_of_mem_weakBlockSet hc.data.mem₁ hc.data.mem₂)
  have h₁₃ : D.I₁ ≤ Subgroup.normalizer (D.I₃ : Set G) :=
    normalize_of_cZero D.cZero₃ D.leH₁ D.leL₁
      (le_normalizer_of_mem_weakBlockSet hc.data.mem₁ hc.data.mem₃)
  have h₂₁ : D.I₂ ≤ Subgroup.normalizer (D.I₁ : Set G) :=
    normalize_of_cZero D.cZero₁ D.leH₂ D.leL₂
      (le_normalizer_of_mem_weakBlockSet hc.data.mem₂ hc.data.mem₁)
  have h₂₃ : D.I₂ ≤ Subgroup.normalizer (D.I₃ : Set G) :=
    normalize_of_cZero D.cZero₃ D.leH₂ D.leL₂
      (le_normalizer_of_mem_weakBlockSet hc.data.mem₂ hc.data.mem₃)
  have h₃₁ : D.I₃ ≤ Subgroup.normalizer (D.I₁ : Set G) :=
    normalize_of_cZero D.cZero₁ D.leH₃ D.leL₃
      (le_normalizer_of_mem_weakBlockSet hc.data.mem₃ hc.data.mem₁)
  have h₃₂ : D.I₃ ≤ Subgroup.normalizer (D.I₂ : Set G) :=
    normalize_of_cZero D.cZero₂ D.leH₃ D.leL₃
      (le_normalizer_of_mem_weakBlockSet hc.data.mem₃ hc.data.mem₂)
  have c₁₂ : ⁅D.I₁, D.I₂⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    commutator_I_le_pCoreOf hc.data.mem₁ hc.data.mem₂
      (TwelveFiveData.pairwise_ne hc.data hc.hcard).1 D.leL₁ D.leL₂
  have c₁₃ : ⁅D.I₁, D.I₃⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    commutator_I_le_pCoreOf hc.data.mem₁ hc.data.mem₃
      (TwelveFiveData.pairwise_ne hc.data hc.hcard).2.1 D.leL₁ D.leL₃
  have c₂₃ : ⁅D.I₂, D.I₃⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    commutator_I_le_pCoreOf hc.data.mem₂ hc.data.mem₃
      (TwelveFiveData.pairwise_ne hc.data hc.hcard).2.2 D.leL₂ D.leL₃
  exact ⟨⟨D, h₁₂, h₁₃, h₂₁, h₂₃, h₃₁, h₃₂, c₁₂, c₁₃, c₂₃⟩⟩

private theorem build_W1 (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : IData M H L₁ L₂ L₃ n₁ n₂ n₃) : Nonempty (W1Data M H L₁ L₂ L₃ n₁ n₂ n₃) := by
  obtain ⟨W₁, hW₁I₁, hcardW₁, s₁, hs₁, hinv₁⟩ :=
    exists_card_three_inverted_of_sup_pCore_eq (I := D.I₁) (C := D.I₁) (n := n₁) D.type₁
      (sup_eq_left.mpr (Subgroup.map_subtype_le (CFSG.pCore 2 ↥D.I₁)))
  exact ⟨⟨D, W₁, s₁, hW₁I₁, hcardW₁, hs₁, hinv₁⟩⟩

private theorem build_W2 (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : W1Data M H L₁ L₂ L₃ n₁ n₂ n₃) : Nonempty (W2Data M H L₁ L₂ L₃ n₁ n₂ n₃) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW₁3 : IsPGroup 3 ↥D.W₁ :=
    (CFSG.GroupTheory.isElemAbelian_of_card_prime D.cardW₁).isPGroup
  have hcomm₂W₁ : ⁅D.I₂, D.W₁⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    (Subgroup.commutator_mono le_rfl D.leW₁).trans (by
      rw [Subgroup.commutator_comm]
      exact D.comm₁₂)
  have hcov₂' : D.I₂ ⊓ Subgroup.centralizer (D.W₁ : Set G) ⊔
      (D.I₂ ⊓ CFSG.Open.pCoreOf 2 M) = D.I₂ :=
    coprime_cover D.leM₂ (D.leW₁.trans D.normalize₁₂) (D.leW₁.trans D.leM₁)
      hW₁3 hcomm₂W₁
  have hN₂ : D.I₂ ⊓ CFSG.Open.pCoreOf 2 M ≤
      (CFSG.pCore 2 ↥D.I₂).map D.I₂.subtype :=
    CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 D.leM₂
  have hcov₂ : D.I₂ ⊓ Subgroup.centralizer (D.W₁ : Set G) ⊔
      (CFSG.pCore 2 ↥D.I₂).map D.I₂.subtype = D.I₂ := by
    refine le_antisymm (sup_le inf_le_left (Subgroup.map_subtype_le _)) ?_
    calc D.I₂ = D.I₂ ⊓ Subgroup.centralizer (D.W₁ : Set G) ⊔
          (D.I₂ ⊓ CFSG.Open.pCoreOf 2 M) := hcov₂'.symm
      _ ≤ D.I₂ ⊓ Subgroup.centralizer (D.W₁ : Set G) ⊔
          (CFSG.pCore 2 ↥D.I₂).map D.I₂.subtype := sup_le_sup le_rfl hN₂
  obtain ⟨W₂, hW₂I₂C₁, hcardW₂, s₂, hs₂, hinv₂⟩ :=
    exists_card_three_inverted_of_sup_pCore_eq (I := D.I₂)
      (C := D.I₂ ⊓ Subgroup.centralizer (D.W₁ : Set G)) (n := n₂) D.type₂ hcov₂
  exact ⟨⟨D, W₂, s₂, hW₂I₂C₁.trans inf_le_left, hW₂I₂C₁.trans inf_le_right,
    hcardW₂, hs₂, hinv₂⟩⟩

private theorem sup_eq_of_two_covers {C₁ C₂ N N₁ I : Subgroup G}
    (hA : C₁ ⊔ N = I) (hB : C₂ ⊔ N₁ = C₁) (hN₁N : N₁ ≤ N) : C₂ ⊔ N = I := by
  have hC₂C₁ : C₂ ≤ C₁ := by rw [← hB]; exact le_sup_left
  have hC₁I : C₁ ≤ I := by rw [← hA]; exact le_sup_left
  have hNI : N ≤ I := by rw [← hA]; exact le_sup_right
  refine le_antisymm (sup_le (hC₂C₁.trans hC₁I) hNI) ?_
  have hC₁le : C₁ ≤ C₂ ⊔ N := by
    rw [← hB]
    exact sup_le le_sup_left (hN₁N.trans le_sup_right)
  calc I = C₁ ⊔ N := hA.symm
    _ ≤ (C₂ ⊔ N) ⊔ N := sup_le_sup hC₁le le_rfl
    _ = C₂ ⊔ N := by rw [sup_assoc, sup_idem]

private theorem cover_W3_normalizers (D : W2Data M H L₁ L₂ L₃ n₁ n₂ n₃) :
    D.W₁ ≤ Subgroup.normalizer (Subgroup.centralizer (D.W₁ : Set G) : Set G) ∧
    D.W₂ ≤ Subgroup.normalizer (Subgroup.centralizer (D.W₁ : Set G) : Set G) := by
  have hN₁C₁ : Subgroup.normalizer (D.W₁ : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (D.W₁ : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (D.W₁ : Set G))).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (D.W₁ : Set G))
  exact ⟨Subgroup.le_normalizer.trans hN₁C₁,
    (D.leW₂C₁.trans (Subgroup.centralizer_le_normalizer (D.W₁ : Set G))).trans hN₁C₁⟩

private theorem cover_W3_two_covers (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : W2Data M H L₁ L₂ L₃ n₁ n₂ n₃) :
    (D.I₃ ⊓ Subgroup.centralizer (D.W₁ : Set G) ⊓
      Subgroup.centralizer (D.W₂ : Set G)) ⊔
      (D.I₃ ⊓ CFSG.Open.pCoreOf 2 M) = D.I₃ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C₁ : Subgroup G := D.I₃ ⊓ Subgroup.centralizer (D.W₁ : Set G)
  let C₂ : Subgroup G := C₁ ⊓ Subgroup.centralizer (D.W₂ : Set G)
  let N : Subgroup G := D.I₃ ⊓ CFSG.Open.pCoreOf 2 M
  let N₁ : Subgroup G := C₁ ⊓ CFSG.Open.pCoreOf 2 M
  obtain ⟨hW₁NC₁, hW₂NC₁⟩ := cover_W3_normalizers D
  have hcomm₃W₁ : ⁅D.I₃, D.W₁⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    (Subgroup.commutator_mono le_rfl D.leW₁).trans (by
      rw [Subgroup.commutator_comm]
      exact D.comm₁₃)
  have hW₁I₃ : D.W₁ ≤ Subgroup.normalizer (D.I₃ : Set G) :=
    D.leW₁.trans D.normalize₁₃
  have hcovA : C₁ ⊔ N = D.I₃ :=
    coprime_cover D.leM₃ hW₁I₃ (D.leW₁.trans D.leM₁)
      ((CFSG.GroupTheory.isElemAbelian_of_card_prime D.cardW₁).isPGroup) hcomm₃W₁
  have hD₁M : C₁ ≤ M := inf_le_left.trans D.leM₃
  have hW₂I₃ : D.W₂ ≤ Subgroup.normalizer (D.I₃ : Set G) :=
    D.leW₂.trans D.normalize₂₃
  have hW₂NI₃C₁ : D.W₂ ≤ Subgroup.normalizer (C₁ : Set G) :=
    (le_inf hW₂I₃ hW₂NC₁).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hcommD₁W₂ : ⁅C₁, D.W₂⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      ((Subgroup.commutator_mono le_rfl D.leW₂).trans (by
        rw [Subgroup.commutator_comm]
        exact D.comm₂₃))
  have hcovB : C₂ ⊔ N₁ = C₁ :=
    coprime_cover hD₁M hW₂NI₃C₁ (D.leW₂.trans D.leM₂)
      ((CFSG.GroupTheory.isElemAbelian_of_card_prime D.cardW₂).isPGroup) hcommD₁W₂
  have hN₁N : N₁ ≤ N := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  exact sup_eq_of_two_covers hcovA hcovB hN₁N

private theorem cover_W3 (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : W2Data M H L₁ L₂ L₃ n₁ n₂ n₃) :
    (D.I₃ ⊓ Subgroup.centralizer (D.W₁ : Set G) ⊓
      Subgroup.centralizer (D.W₂ : Set G)) ⊔
      (CFSG.pCore 2 ↥D.I₃).map D.I₃.subtype = D.I₃ := by
  let C₂ : Subgroup G := D.I₃ ⊓ Subgroup.centralizer (D.W₁ : Set G) ⊓
    Subgroup.centralizer (D.W₂ : Set G)
  let N : Subgroup G := D.I₃ ⊓ CFSG.Open.pCoreOf 2 M
  have hC₂N : C₂ ⊔ N = D.I₃ := cover_W3_two_covers hc D
  refine le_antisymm (sup_le (inf_le_left.trans inf_le_left) (Subgroup.map_subtype_le _)) ?_
  calc D.I₃ = C₂ ⊔ N := hC₂N.symm
    _ ≤ C₂ ⊔ (CFSG.pCore 2 ↥D.I₃).map D.I₃.subtype :=
      sup_le_sup le_rfl (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 D.leM₃)

private theorem build_W3 (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : W2Data M H L₁ L₂ L₃ n₁ n₂ n₃) : Nonempty (W3Data M H L₁ L₂ L₃ n₁ n₂ n₃) := by
  have hcov₃ := cover_W3 hc D
  obtain ⟨W₃, hW₃I₃C₁C₂, hcardW₃, s₃, hs₃, hinv₃⟩ :=
    exists_card_three_inverted_of_sup_pCore_eq (I := D.I₃)
      (C := D.I₃ ⊓ Subgroup.centralizer (D.W₁ : Set G) ⊓
        Subgroup.centralizer (D.W₂ : Set G)) (n := n₃) D.type₃ hcov₃
  exact ⟨⟨D, W₃, s₃, hW₃I₃C₁C₂.trans (inf_le_left.trans inf_le_left),
    hW₃I₃C₁C₂.trans (inf_le_left.trans inf_le_right), hW₃I₃C₁C₂.trans inf_le_right,
    hcardW₃, hs₃, hinv₃⟩⟩

private theorem V_elem_abelian (D : W3Data M H L₁ L₂ L₃ n₁ n₂ n₃) :
    IsElemAbelian 3 (D.W₁ ⊔ D.W₂ ⊔ D.W₃) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcent₁₂ : ∀ a ∈ D.W₁, ∀ b ∈ D.W₂, Commute a b := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (D.leW₂C₁ hb) a ha
  have hcent₁₃ : ∀ a ∈ D.W₁, ∀ c ∈ D.W₃, Commute a c := by
    intro a ha c hc
    exact Subgroup.mem_centralizer_iff.mp (D.leW₃C₁ hc) a ha
  have hcent₂₃ : ∀ b ∈ D.W₂, ∀ c ∈ D.W₃, Commute b c := by
    intro b hb c hc
    exact Subgroup.mem_centralizer_iff.mp (D.leW₃C₂ hc) b hb
  have hW₃cent : D.W₃ ≤ Subgroup.centralizer ((D.W₁ ⊔ D.W₂ : Subgroup G) : Set G) :=
    CFSG.le_centralizer_sup_of_commute_both hcent₁₂
      (fun a ha b hb => (hcent₁₃ b hb a ha).symm)
      (fun a ha b hb => (hcent₂₃ b hb a ha).symm)
  have hcent₁₂₃ : ∀ a ∈ D.W₁ ⊔ D.W₂, ∀ c ∈ D.W₃, Commute a c := by
    intro a ha c hc
    exact Subgroup.mem_centralizer_iff.mp (hW₃cent hc) a ha
  have hW₁₂e : IsElemAbelian 3 (D.W₁ ⊔ D.W₂) :=
    (CFSG.GroupTheory.isElemAbelian_of_card_prime D.cardW₁).sup_of_commute
      (CFSG.GroupTheory.isElemAbelian_of_card_prime D.cardW₂)
      (fun a ha b hb => (hcent₁₂ a ha b hb).eq)
  exact hW₁₂e.sup_of_commute (CFSG.GroupTheory.isElemAbelian_of_card_prime D.cardW₃)
    (fun a ha c hc => (hcent₁₂₃ a ha c hc).eq)

private theorem W_disjoint (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : W3Data M H L₁ L₂ L₃ n₁ n₂ n₃) :
    D.W₁ ⊓ D.W₂ = ⊥ ∧ (D.W₁ ⊔ D.W₂) ⊓ D.W₃ = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩; haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hW₁3 : IsPGroup 3 ↥D.W₁ :=
    (CFSG.GroupTheory.isElemAbelian_of_card_prime D.cardW₁).isPGroup
  have hW₁₂3 : IsPGroup 3 ↥(D.W₁ ⊔ D.W₂) :=
    (V_elem_abelian D).mono (le_sup_left : D.W₁ ⊔ D.W₂ ≤ D.W₁ ⊔ D.W₂ ⊔ D.W₃) |>.isPGroup
  have hbar₁₂ : barM M L₁ ⊓ barM M L₂ = ⊥ := (hc.barM_blocks_independent).1
  have hbar₁₂₃ : (barM M L₁ ⊔ barM M L₂) ⊓ barM M L₃ = ⊥ :=
    (hc.barM_blocks_independent).2.2.2
  have hL₁L₂pc : L₁ ⊓ L₂ ≤ CFSG.Open.pCoreOf 2 M :=
    le_pCoreOf_of_barM_inf_eq_bot hbar₁₂ hc.data.mem₁.le hc.data.mem₂.le
  have hL₁₂L₃pc : (L₁ ⊔ L₂) ⊓ L₃ ≤ CFSG.Open.pCoreOf 2 M :=
    le_pCoreOf_of_barM_sup_inf_eq_bot hbar₁₂₃ hc.data.mem₁.le hc.data.mem₂.le
      hc.data.mem₃.le
  have hpc₁₂ : D.W₁ ⊓ D.W₂ ≤ CFSG.Open.pCoreOf 2 M :=
    (le_inf (inf_le_left.trans (D.leW₁.trans D.leL₁))
      (inf_le_right.trans (D.leW₂.trans D.leL₂))).trans hL₁L₂pc
  have hW₁₂L₁₂ : D.W₁ ⊔ D.W₂ ≤ L₁ ⊔ L₂ :=
    sup_le ((D.leW₁.trans D.leL₁).trans le_sup_left)
      ((D.leW₂.trans D.leL₂).trans le_sup_right)
  have hpc₁₂₃ : (D.W₁ ⊔ D.W₂) ⊓ D.W₃ ≤ CFSG.Open.pCoreOf 2 M :=
    (le_inf (inf_le_left.trans hW₁₂L₁₂)
      (inf_le_right.trans (D.leW₃.trans D.leL₃))).trans hL₁₂L₃pc
  have hOp : IsPGroup 2 (CFSG.Open.pCoreOf 2 M) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) M
  have hdisj₁₂ : D.W₁ ⊓ D.W₂ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc D.W₁ ⊓ D.W₂ ≤ D.W₁ ⊓ CFSG.Open.pCoreOf 2 M := le_inf inf_le_left hpc₁₂
      _ = ⊥ := (IsPGroup.disjoint_of_ne 3 2 (by norm_num) D.W₁
          (CFSG.Open.pCoreOf 2 M) hW₁3 hOp).eq_bot
  have hdisj₁₂₃ : (D.W₁ ⊔ D.W₂) ⊓ D.W₃ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc (D.W₁ ⊔ D.W₂) ⊓ D.W₃ ≤ (D.W₁ ⊔ D.W₂) ⊓ CFSG.Open.pCoreOf 2 M :=
          le_inf inf_le_left hpc₁₂₃
      _ = ⊥ := (IsPGroup.disjoint_of_ne 3 2 (by norm_num) (D.W₁ ⊔ D.W₂)
          (CFSG.Open.pCoreOf 2 M) hW₁₂3 hOp).eq_bot
  exact ⟨hdisj₁₂, hdisj₁₂₃⟩

private theorem V_card (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : W3Data M H L₁ L₂ L₃ n₁ n₂ n₃) :
    Nat.card ↥(D.W₁ ⊔ D.W₂ ⊔ D.W₃) = 27 := by
  obtain ⟨hdisj₁₂, hdisj₁₂₃⟩ := W_disjoint hc D
  have hcent₁₂ : ∀ a ∈ D.W₁, ∀ b ∈ D.W₂, Commute a b := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (D.leW₂C₁ hb) a ha
  have hcent₁₃ : ∀ a ∈ D.W₁, ∀ c ∈ D.W₃, Commute a c := by
    intro a ha c hc
    exact Subgroup.mem_centralizer_iff.mp (D.leW₃C₁ hc) a ha
  have hcent₂₃ : ∀ b ∈ D.W₂, ∀ c ∈ D.W₃, Commute b c := by
    intro b hb c hc
    exact Subgroup.mem_centralizer_iff.mp (D.leW₃C₂ hc) b hb
  have hcent₁₂₃ : ∀ a ∈ D.W₁ ⊔ D.W₂, ∀ c ∈ D.W₃, Commute a c := by
    intro a ha c hc
    have hW₃cent : D.W₃ ≤ Subgroup.centralizer ((D.W₁ ⊔ D.W₂ : Subgroup G) : Set G) :=
      CFSG.le_centralizer_sup_of_commute_both hcent₁₂
        (fun a ha b hb => (hcent₁₃ b hb a ha).symm)
        (fun a ha b hb => (hcent₂₃ b hb a ha).symm)
    exact Subgroup.mem_centralizer_iff.mp (hW₃cent hc) a ha
  have hcard₁₂ : Nat.card ↥(D.W₁ ⊔ D.W₂) = Nat.card D.W₁ * Nat.card D.W₂ :=
    CFSG.card_sup_eq_mul_of_commute D.W₁ D.W₂
      (fun a ha b hb => (hcent₁₂ a ha b hb).eq) hdisj₁₂
  have h12 : Nat.card ↥(D.W₁ ⊔ D.W₂ ⊔ D.W₃) =
      Nat.card ↥(D.W₁ ⊔ D.W₂) * Nat.card D.W₃ :=
    CFSG.card_sup_eq_mul_of_commute (D.W₁ ⊔ D.W₂) D.W₃
      (fun a ha c hc => (hcent₁₂₃ a ha c hc).eq) hdisj₁₂₃
  rw [h12, hcard₁₂, D.cardW₁, D.cardW₂, D.cardW₃]

private theorem build_VData (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : W3Data M H L₁ L₂ L₃ n₁ n₂ n₃) : Nonempty (VData M H L₁ L₂ L₃ n₁ n₂ n₃) :=
  ⟨⟨D, D.W₁ ⊔ D.W₂ ⊔ D.W₃, rfl, V_elem_abelian D, V_card hc D⟩⟩

private theorem build_T1 (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : VData M H L₁ L₂ L₃ n₁ n₂ n₃) : Nonempty (T1Data M H L₁ L₂ L₃ n₁ n₂ n₃) := by
  let I : Subgroup G := D.I₁ ⊔ D.I₂ ⊔ D.I₃
  have hI₁I : D.I₁ ≤ I := le_sup_left.trans le_sup_left
  have hI₂I : D.I₂ ≤ I := le_sup_right.trans le_sup_left
  have hI₃I : D.I₃ ≤ I := le_sup_right
  have hIMle : I ≤ M := sup_le (sup_le D.leM₁ D.leM₂) D.leM₃
  have hVI : D.V ≤ I := by
    rw [D.joinV]
    exact sup_le (sup_le (D.leW₁.trans hI₁I) (D.leW₂.trans hI₂I)) (D.leW₃.trans hI₃I)
  have hW₁V : D.W₁ ≤ D.V := by rw [D.joinV]; exact le_sup_left.trans le_sup_left
  have hW₂V : D.W₂ ≤ D.V := by rw [D.joinV]; exact le_sup_right.trans le_sup_left
  have hW₃V : D.W₃ ≤ D.V := by rw [D.joinV]; exact le_sup_right
  have hcomm₁W₂ : ⁅D.I₁, D.W₂⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    (Subgroup.commutator_mono le_rfl D.leW₂).trans D.comm₁₂
  have hcomm₁W₃ : ⁅D.I₁, D.W₃⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    (Subgroup.commutator_mono le_rfl D.leW₃).trans D.comm₁₃
  obtain ⟨t₁, ht₁I, hinv₁, hcomm₁⟩ :=
    exists_inverting_conj (M := M) (I := I) (Ii := D.I₁) (V := D.V)
      (W := D.W₁) (W' := D.W₂) (W'' := D.W₃) (s := D.s₁)
      hIMle hI₁I hVI D.elemV.isPGroup D.joinV hW₁V hW₂V hW₃V D.mems₁ D.inv₁
      hcomm₁W₂ hcomm₁W₃
  exact ⟨⟨D, t₁, ht₁I, hinv₁, hcomm₁⟩⟩

private theorem build_T2 (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : T1Data M H L₁ L₂ L₃ n₁ n₂ n₃) : Nonempty (T2Data M H L₁ L₂ L₃ n₁ n₂ n₃) := by
  let I : Subgroup G := D.I₁ ⊔ D.I₂ ⊔ D.I₃
  have hI₁I : D.I₁ ≤ I := le_sup_left.trans le_sup_left
  have hI₂I : D.I₂ ≤ I := le_sup_right.trans le_sup_left
  have hI₃I : D.I₃ ≤ I := le_sup_right
  have hIMle : I ≤ M := sup_le (sup_le D.leM₁ D.leM₂) D.leM₃
  have hVI : D.V ≤ I := by
    rw [D.joinV]
    exact sup_le (sup_le (D.leW₁.trans hI₁I) (D.leW₂.trans hI₂I)) (D.leW₃.trans hI₃I)
  have hW₁V : D.W₁ ≤ D.V := by rw [D.joinV]; exact le_sup_left.trans le_sup_left
  have hW₂V : D.W₂ ≤ D.V := by rw [D.joinV]; exact le_sup_right.trans le_sup_left
  have hW₃V : D.W₃ ≤ D.V := by rw [D.joinV]; exact le_sup_right
  have hcomm₂W₁ : ⁅D.I₂, D.W₁⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    (Subgroup.commutator_mono le_rfl D.leW₁).trans (by
      rw [Subgroup.commutator_comm]
      exact D.comm₁₂)
  have hcomm₂W₃ : ⁅D.I₂, D.W₃⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    (Subgroup.commutator_mono le_rfl D.leW₃).trans D.comm₂₃
  have hJOIN : D.V = D.W₂ ⊔ D.W₁ ⊔ D.W₃ := by
    rw [D.joinV, sup_comm D.W₁ D.W₂]
  obtain ⟨t₂, ht₂I, hinv₂, hcomm₂⟩ :=
    exists_inverting_conj (M := M) (I := I) (Ii := D.I₂) (V := D.V)
      (W := D.W₂) (W' := D.W₁) (W'' := D.W₃) (s := D.s₂)
      hIMle hI₂I hVI D.elemV.isPGroup hJOIN hW₂V hW₁V hW₃V D.mems₂.1
      D.inv₂ hcomm₂W₁ hcomm₂W₃
  exact ⟨⟨D, t₂, ht₂I, hinv₂, hcomm₂⟩⟩

private theorem build_T3 (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : T2Data M H L₁ L₂ L₃ n₁ n₂ n₃) : Nonempty (T3Data M H L₁ L₂ L₃ n₁ n₂ n₃) := by
  let I : Subgroup G := D.I₁ ⊔ D.I₂ ⊔ D.I₃
  have hI₁I : D.I₁ ≤ I := le_sup_left.trans le_sup_left
  have hI₂I : D.I₂ ≤ I := le_sup_right.trans le_sup_left
  have hI₃I : D.I₃ ≤ I := le_sup_right
  have hIMle : I ≤ M := sup_le (sup_le D.leM₁ D.leM₂) D.leM₃
  have hVI : D.V ≤ I := by
    rw [D.joinV]
    exact sup_le (sup_le (D.leW₁.trans hI₁I) (D.leW₂.trans hI₂I)) (D.leW₃.trans hI₃I)
  have hW₁V : D.W₁ ≤ D.V := by rw [D.joinV]; exact le_sup_left.trans le_sup_left
  have hW₂V : D.W₂ ≤ D.V := by rw [D.joinV]; exact le_sup_right.trans le_sup_left
  have hW₃V : D.W₃ ≤ D.V := by rw [D.joinV]; exact le_sup_right
  have hcomm₃W₁ : ⁅D.I₃, D.W₁⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    (Subgroup.commutator_mono le_rfl D.leW₁).trans (by
      rw [Subgroup.commutator_comm]
      exact D.comm₁₃)
  have hcomm₃W₂ : ⁅D.I₃, D.W₂⁆ ≤ CFSG.Open.pCoreOf 2 M :=
    (Subgroup.commutator_mono le_rfl D.leW₂).trans (by
      rw [Subgroup.commutator_comm]
      exact D.comm₂₃)
  have hJOIN : D.V = D.W₃ ⊔ D.W₁ ⊔ D.W₂ := by
    rw [D.joinV]
    ac_rfl
  obtain ⟨t₃, ht₃I, hinv₃, hcomm₃⟩ :=
    exists_inverting_conj (M := M) (I := I) (Ii := D.I₃) (V := D.V)
      (W := D.W₃) (W' := D.W₁) (W'' := D.W₂) (s := D.s₃)
      hIMle hI₃I hVI D.elemV.isPGroup hJOIN hW₃V hW₁V hW₂V D.mems₃.1.1
      D.inv₃ hcomm₃W₁ hcomm₃W₂
  exact ⟨⟨D, t₃, ht₃I, hinv₃, hcomm₃⟩⟩

private def toIData (D : T3Data M H L₁ L₂ L₃ n₁ n₂ n₃) :
    TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃ := {
  I₁ := D.I₁, I₂ := D.I₂, I₃ := D.I₃
  V := D.V
  W₁ := D.W₁
  W₂ := D.W₂
  W₃ := D.W₃
  t₁ := D.t₁
  t₂ := D.t₂
  t₃ := D.t₃
  cZero₁ := D.cZero₁
  cZero₂ := D.cZero₂
  cZero₃ := D.cZero₃
  type₁ := D.type₁
  type₂ := D.type₂
  type₃ := D.type₃
  le₁ := D.leW₁
  le₂ := D.leW₂
  le₃ := D.leW₃
  mem₁ := D.memt₁
  mem₂ := D.memt₂
  mem₃ := D.memt₃
  cfg := {
    card₁ := D.cardW₁
    card₂ := D.cardW₂
    card₃ := D.cardW₃
    join := D.joinV
    elem := D.elemV
    card := D.cardV
    inv₁ := D.invt₁
    inv₂ := D.invt₂
    inv₃ := D.invt₃
    comm₁ := D.commt₁
    comm₂ := D.commt₂
    comm₃ := D.commt₃ } }

theorem TwelveSixKCtx.exists_iData (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (hIM : TwelveSixIMember) : Nonempty (TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) := by
  obtain ⟨R⟩ := exists_IRaw hc hIM
  obtain ⟨D1⟩ := build_IBasic hc R
  obtain ⟨D2⟩ := build_IData hc D1
  obtain ⟨D3⟩ := build_W1 hc D2
  obtain ⟨D4⟩ := build_W2 hc D3
  obtain ⟨D5⟩ := build_W3 hc D4
  obtain ⟨D6⟩ := build_VData hc D5
  obtain ⟨D7⟩ := build_T1 hc D6
  obtain ⟨D8⟩ := build_T2 hc D7
  obtain ⟨D9⟩ := build_T3 hc D8
  exact ⟨toIData D9⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
