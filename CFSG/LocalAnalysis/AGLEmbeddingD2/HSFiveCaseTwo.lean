module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveOver
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwoTools
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveBlocks
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisTools
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeKillAux

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms CFSG.QuasithinUnique

section Transfer

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

omit [Finite G] in
theorem mem_sup_twoCore_of_mk_mem_barM {L : Subgroup G} {m : ↥M}
    (hm : QuotientGroup.mk' (CFSG.pCore 2 ↥M) m ∈ barM M L) :
    (m : G) ∈ L ⊔ pCoreOf 2 M := by
  obtain ⟨l, hl, hlm⟩ := hm
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (l⁻¹ * m) = 1 := by
    rw [map_mul, map_inv, hlm, inv_mul_cancel]
  have h2 : ((l⁻¹ * m : ↥M) : G) ∈ pCoreOf 2 M := coe_mem_pCoreOf_two_of_mk_eq_one _ h1
  have h3 : (m : G) = (l : G) * ((l⁻¹ * m : ↥M) : G) := by simp
  rw [h3]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hl) h2

theorem AGLPair.map_sup_twoCore_eq (h : AGLPair p M H R) {L : Subgroup G} (hLH : L ≤ H) :
    ((L ⊔ pCoreOf 2 M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  have hQH : pCoreOf 2 M ≤ H :=
    h.twoCore_M_le.trans (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_le 2 H)
  rw [Subgroup.subgroupOf_sup hLH hQH, Subgroup.map_sup]
  have hQ : ((pCoreOf 2 M).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro q hq
    exact (mem_glbPrimeCore_iff_mk_eq_one q).mp
      (h.twoCore_M_le_glbPrimeCore (Subgroup.mem_subgroupOf.mp hq))
  rw [hQ, sup_bot_eq]

theorem AGLPair.map_le_normalizer_of_barM_le_normalizer (h : AGLPair p M H R) {Y L : Subgroup G}
    (hYK : Y ≤ H ⊓ M) (hLK : L ≤ H ⊓ M)
    (hYL : barM M Y ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      Subgroup.normalizer (((L.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  rintro _ ⟨y, hy, rfl⟩
  have hyY : (y : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy
  have hyM : (y : G) ∈ M := (hYK hyY).2
  refine AltData.mem_normalizer_of_conj_mem fun x hx => ?_
  rw [← h.map_sup_twoCore_eq (hLK.trans inf_le_left)]
  obtain ⟨l, hl, rfl⟩ := hx
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hlM : (l : G) ∈ M := (hLK hlL).2
  have hbar : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨(y : G) * l * (y : G)⁻¹,
      M.mul_mem (M.mul_mem hyM hlM) (M.inv_mem hyM)⟩ ∈ barM M L := by
    have hyN := hYL (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyY) :
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨y, hyM⟩ ∈ barM M Y)
    have hlb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩ ∈ barM M L :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hlL)
    have := (Subgroup.mem_normalizer_iff.mp hyN _).mp hlb
    have heq : (⟨(y : G) * l * (y : G)⁻¹, M.mul_mem (M.mul_mem hyM hlM) (M.inv_mem hyM)⟩ : ↥M) =
        ⟨y, hyM⟩ * ⟨l, hlM⟩ * (⟨y, hyM⟩)⁻¹ := rfl
    rw [heq, map_mul, map_mul, map_inv]
    exact this
  refine ⟨y * l * y⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
  simpa using mem_sup_twoCore_of_mk_mem_barM hbar

theorem AGLPair.map_mem_centralizer_of_barM (h : AGLPair p M H R) {L : Subgroup G}
    (hLK : L ≤ H ⊓ M) {k : G} (hk : k ∈ H ⊓ M)
    (hkC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hk.2⟩ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨k, hk.1⟩ ∈
      Subgroup.centralizer (((L.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨l, hl, rfl⟩
  have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hlM : (l : G) ∈ M := (hLK hlL).2
  have hc := Subgroup.mem_centralizer_iff.mp hkC
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlM⟩)
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hlL))
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
      (⟨l, hlM⟩ * ⟨k, hk.2⟩ * (⟨l, hlM⟩)⁻¹ * (⟨k, hk.2⟩)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have h2 := h.twoCore_M_le_glbPrimeCore (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
  have h3 : QuotientGroup.mk' (primeComplementCore (G := H) p)
      (l * ⟨k, hk.1⟩ * l⁻¹ * (⟨k, hk.1⟩)⁻¹) = 1 :=
    (mem_glbPrimeCore_iff_mk_eq_one (l * ⟨k, hk.1⟩ * l⁻¹ * (⟨k, hk.1⟩)⁻¹)).mp (by simpa using h2)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h3
  calc QuotientGroup.mk' (primeComplementCore (G := H) p) l *
        QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨k, hk.1⟩
      = (QuotientGroup.mk' (primeComplementCore (G := H) p) l *
          QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨k, hk.1⟩ *
          (QuotientGroup.mk' (primeComplementCore (G := H) p) l)⁻¹ *
          (QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨k, hk.1⟩)⁻¹) *
          QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨k, hk.1⟩ *
          QuotientGroup.mk' (primeComplementCore (G := H) p) l := by group
    _ = _ := by rw [h3, one_mul]

theorem AGLPair.nonempty_centerQuotient_mulEquiv (h : AGLPair p M H R) {L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (hLK : L ≤ H ⊓ M) (hLN : ¬ L ≤ GLBPrimeCore p H)
    (hZ : Subgroup.center ↥((L.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))) = ⊥) :
    Nonempty (↥(barM M L) ⧸ Subgroup.center ↥(barM M L) ≃*
      ↥((L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))) := by
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set V := (L.subgroupOf H).map π with hV
  have hLM : L ≤ M := hL.le
  have hLH : L ≤ H := hLK.trans inf_le_left
  have hLb : IsComponentOf (barM M L) ⊤ := hL.component
  let bar : ↥L →* ↥(barM M L) := (barElt M hLM).codRestrict (barM M L) (barElt_mem_barM hLM)
  have hbar : Function.Surjective bar := by
    rintro ⟨x, hx⟩
    rw [← range_barElt hLM] at hx
    obtain ⟨l, rfl⟩ := hx
    exact ⟨l, rfl⟩
  let α : ↥L →* ↥(barM M L) ⧸ Subgroup.center ↥(barM M L) :=
    (QuotientGroup.mk' (Subgroup.center ↥(barM M L))).comp bar
  have hα : Function.Surjective α := (QuotientGroup.mk'_surjective _).comp hbar
  let β : ↥L →* ↥V := (π.comp (Subgroup.inclusion hLH)).codRestrict V
    (fun l => ⟨Subgroup.inclusion hLH l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩)
  have hβ : Function.Surjective β := by
    rintro ⟨x, ⟨k, hk, rfl⟩⟩
    exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
  have hβN : ∀ l : ↥L, β l = 1 ↔ (l : G) ∈ GLBPrimeCore p H := fun l => by
    have h0 := mem_glbPrimeCore_iff_mk_eq_one (p := p) (Subgroup.inclusion hLH l)
    exact ⟨fun h1 => h0.mpr (congrArg Subtype.val h1), fun h1 => Subtype.ext (h0.mp h1)⟩
  have hker : α.ker = β.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hl
      have hlc : bar l ∈ Subgroup.center ↥(barM M L) := (QuotientGroup.eq_one_iff _).mp hl
      have hlK : (l : G) ∈ H ⊓ M := hLK l.2
      have hkC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hlK.2⟩ ∈
          Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hlc ⟨y, hy⟩)
      have hπC := h.map_mem_centralizer_of_barM hLK hlK hkC
      have hβc : β l ∈ Subgroup.center ↥V := by
        rw [Subgroup.mem_center_iff]
        intro v
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hπC v v.2)
      rw [hZ, Subgroup.mem_bot] at hβc
      exact hβc
    · intro hl
      have hn : (β.ker.map bar).Normal := Subgroup.Normal.map inferInstance bar hbar
      rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hLb.2.2
          (β.ker.map bar) with hc | htop
      · exact (QuotientGroup.eq_one_iff _).mpr (hc ⟨l, hl, rfl⟩)
      · exfalso
        apply hLN
        intro x hx
        have hmem : bar ⟨x, hx⟩ ∈ β.ker.map bar := htop ▸ Subgroup.mem_top _
        obtain ⟨n, hn, hnx⟩ := hmem
        have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hLM (n⁻¹ * ⟨x, hx⟩)) =
            1 := by
          have := congrArg Subtype.val (show bar (n⁻¹ * ⟨x, hx⟩) = 1 by
            rw [map_mul, map_inv, hnx, inv_mul_cancel])
          exact this
        have hq := h.twoCore_M_le_glbPrimeCore (coe_mem_pCoreOf_two_of_mk_eq_one _ h1)
        have hnN : (n : G) ∈ GLBPrimeCore p H := (hβN n).mp hn
        have hx' : x = (n : G) * ((n⁻¹ * ⟨x, hx⟩ : ↥L) : G) := by simp
        rw [hx']
        exact (GLBPrimeCore p H).mul_mem hnN (by simpa using hq)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective α hα).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective β hβ))⟩

end Transfer

section Component

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem AGLPair.map_eq_of_component (h : AGLPair p M H R) (hD1 : D1For G)
    (hα : KFactThreeOrFiveDvd)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    {U : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hUs : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p), W ≤ U →
      U ≤ Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) → W = ⊥ ∨ W = U)
    (hUperf : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) →
        ⁅W, W⁆ = W → W ≤ U)
    {J : Subgroup G} (hJK : J ≤ H ⊓ M) (hJ : ⁅J, J⁆ = J)
    (hJU : (J.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) = U)
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) (hLK : L ≤ H ⊓ M)
    (hLN : ¬ L ≤ GLBPrimeCore p H) :
    (L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) = U := by
  have hLH : L ≤ H := hLK.trans inf_le_left
  have hle : (L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr (hLK (Subgroup.mem_subgroupOf.mp hx))
  have hperf : ⁅(L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)),
      (L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))⁆ =
      (L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL.perfect
    have hp' := Group.IsPerfect.range
      ((QuotientGroup.mk' (primeComplementCore (G := H) p)).comp (Subgroup.inclusion hLH))
    rw [range_mk_comp_inclusion hLH] at hp'
    exact Subgroup.isPerfect_iff.mp hp'
  have hnorm : U ≤ Subgroup.normalizer
      (((L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) :
        Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [← hJU]
    exact h.map_le_normalizer_of_barM_le_normalizer hJK hLK
      (h.le_normalizer_component hD1 hα hB3 hJK hJ hL.component)
  rcases hUs _ (hUperf _ hle hperf) hnorm with h0 | h0
  · exfalso
    apply hLN
    intro x hx
    have hmem : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hLH hx⟩ ∈
        (L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
      ⟨⟨x, hLH hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    rw [h0, Subgroup.mem_bot] at hmem
    exact (mem_glbPrimeCore_iff_mk_eq_one (⟨x, hLH hx⟩ : H)).mpr hmem
  · exact h0

theorem AGLPair.mem_glbPrimeCore_of_centralizer (h : AGLPair p M H R)
    {U : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hCU : Subgroup.centralizer (U : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥)
    {L : Subgroup G} (hLK : L ≤ H ⊓ M)
    (hLU : (L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) = U)
    {k : G} (hk : k ∈ H ⊓ M)
    (hkC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨k, hk.2⟩ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    k ∈ GLBPrimeCore p H := by
  have h1 := h.map_mem_centralizer_of_barM hLK hk hkC
  rw [hLU, hCU, Subgroup.mem_bot] at h1
  exact (mem_glbPrimeCore_iff_mk_eq_one (⟨k, hk.1⟩ : H)).mpr h1

theorem AGLPair.coprime_orderOf_of_centralizer (h : AGLPair p M H R)
    {U : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hCU : Subgroup.centralizer (U : Set (H ⧸ primeComplementCore (G := H) p)) = ⊥)
    {L : Subgroup G} (hLK : L ≤ H ⊓ M)
    (hLU : (L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)) = U)
    {x : ↥M ⧸ CFSG.pCore 2 ↥M} (hxK : x ∈ barM M (H ⊓ M))
    (hxC : x ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    (orderOf x).Coprime p := by
  obtain ⟨m, hm, rfl⟩ := hxK
  have hmK : (m : G) ∈ H ⊓ M := Subgroup.mem_subgroupOf.mp hm
  have hmN := h.mem_glbPrimeCore_of_centralizer hCU hLK hLU hmK hxC
  have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥M) m) ∣ Nat.card (GLBPrimeCore p H) :=
    (orderOf_map_dvd _ _).trans (by
      rw [← Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard _ hmN)
  exact Nat.Coprime.coprime_dvd_left h1 (glbPrimeCore_coprime p H).symm

end Component

@[expose] def KFactBlockThreeOrderThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    ∃ y ∈ blockPL M S L, y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

@[expose] def KFactBlockCyclicThreeFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M → Asc81bHyp M S →
    IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    (∀ E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), E ≤ barM M L → IsElemAbelian 3 E →
      Nat.card E ≤ 3) →
    ∀ V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M),
      V ≤ Subgroup.normalizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → IsElemAbelian 5 V →
      (V ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))).relIndex V ≤ 5


@[expose] def KFactHSMultiplier : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (φ : Γ →* (TauCeti.CFSGIndex.sporadic .HS).Group),
    Function.Surjective φ → φ.ker ≤ Subgroup.center Γ →
    ∀ z ∈ φ.ker ⊓ commutator Γ, ∃ k : ℕ, z ^ 2 ^ k = 1

section CenterFree

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

theorem AGLPair.commutator_mem_twoCore_of_component (h : AGLPair p M H R) {L : Subgroup G}
    (hL : IsTwoPrimeComponent M L) (hLH : L ≤ H) (hLN : ¬ L ≤ GLBPrimeCore p H) {n l : G}
    (hn : n ∈ GLBPrimeCore p H) (hl : l ∈ L) : n * l * n⁻¹ * l⁻¹ ∈ pCoreOf 2 M := by
  have hNM : GLBPrimeCore p H ≤ M := h.primeCore_le
  have hLM : L ≤ M := hL.le
  set Lb := barM M L with hLb
  set Nb := barM M (GLBPrimeCore p H) with hNb
  have hLbN : Lb ≤ Subgroup.normalizer (Nb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    barM_le_normalizer_barM (hLH.trans (le_normalizer_glbPrimeCore p H))
  set T := Lb ⊔ Nb with hT
  have hTN : T ≤ Subgroup.normalizer (Nb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    sup_le hLbN Subgroup.le_normalizer
  have : (Nb.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hTN
  have hcomp := ComponentClassification.LocalComponents.of_overgroup hL.component
    (le_sup_left : Lb ≤ T)
  rcases ComponentClassification.LocalComponents.normal_contains_or_commutes
      (Lb.subgroupOf T) (Nb.subgroupOf T) hcomp with hle | hcomm
  · exfalso
    apply hLN
    intro x hx
    have hxb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hLM hx⟩ ∈ Nb := by
      have h1 : (⟨QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨x, hLM hx⟩,
          le_sup_left (a := Lb) (b := Nb) (Subgroup.mem_map_of_mem _
            (Subgroup.mem_subgroupOf.mpr hx))⟩ : ↥T) ∈ Lb.subgroupOf T :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx))
      exact Subgroup.mem_subgroupOf.mp (hle h1)
    have h2 := mem_sup_twoCore_of_mk_mem_barM hxb
    exact (sup_le le_rfl (h.twoCore_M_le_glbPrimeCore)) h2
  · have hnb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hNM hn⟩ ∈ Nb :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hn)
    have hlb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM hl⟩ ∈ Lb :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hl)
    set lT : ↥T := ⟨_, le_sup_left (a := Lb) (b := Nb) hlb⟩ with hlT
    set nT : ↥T := ⟨_, le_sup_right (a := Lb) (b := Nb) hnb⟩ with hnT
    have hlT' : lT ∈ Lb.subgroupOf T := Subgroup.mem_subgroupOf.mpr hlb
    have hnT' : nT ∈ Nb.subgroupOf T := Subgroup.mem_subgroupOf.mpr hnb
    have hc : lT * nT = nT * lT := by
      have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hlT'
      exact (Subgroup.mem_centralizer_iff.mp hle _ hnT').symm
    have hc' : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM hl⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hNM hn⟩ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨n, hNM hn⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨l, hLM hl⟩ := congrArg Subtype.val hc
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M)
        (⟨n, hNM hn⟩ * ⟨l, hLM hl⟩ * (⟨n, hNM hn⟩)⁻¹ * (⟨l, hLM hl⟩)⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc']
      group
    simpa using coe_mem_pCoreOf_two_of_mk_eq_one _ h1

theorem AGLPair.exists_pow_two_eq_one_of_hs [Fact p.Prime] (h : AGLPair p M H R)
    (hMult : KFactHSMultiplier) {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hKtop : K = ⊤) (hKs : IsSimpleGroup ↥K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .HS).Group))
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) (hLH : L ≤ H)
    (hLN : ¬ L ≤ GLBPrimeCore p H) {l : G} (hlL : l ∈ L) (hlN : l ∈ GLBPrimeCore p H) :
    ∃ k : ℕ, l ^ 2 ^ k = 1 := by
  obtain ⟨e₀⟩ := he
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  set D : Subgroup ↥H :=
    Subgroup.normalClosure (((pCoreOf 2 M).subgroupOf H : Subgroup ↥H) : Set ↥H) with hD
  have hSn : ((pCoreOf 2 H).subgroupOf H).Normal :=
    CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_normal 2 H
  have hDS : D ≤ (pCoreOf 2 H).subgroupOf H := Subgroup.normalClosure_le_normal fun x hx =>
    Subgroup.mem_subgroupOf.mpr (h.twoCore_M_le (Subgroup.mem_subgroupOf.mp hx))
  have hDπ : D ≤ π.ker := fun x hx =>
    (mem_glbPrimeCore_iff_mk_eq_one x).mp
      (h.twoCore_le_primeCore (Subgroup.mem_subgroupOf.mp (hDS hx)))
  set q := QuotientGroup.mk' D with hq
  set π' := QuotientGroup.lift D π hDπ with hπ'
  have hπ'q : ∀ x : ↥H, π' (q x) = π x := fun x => rfl
  have hπ's : Function.Surjective π' :=
    QuotientGroup.lift_surjective_of_surjective D π (QuotientGroup.mk'_surjective _) hDπ
  set Nt : Subgroup (↥H ⧸ D) := π.ker.map q with hNt
  have : Nt.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective D)
  set Lt : Subgroup (↥H ⧸ D) := (L.subgroupOf H).map q with hLt
  have hLtC : (Lt : Set (↥H ⧸ D)) ⊆ Subgroup.centralizer (Nt : Set (↥H ⧸ D)) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, hn, rfl⟩
    have hnN : (n : G) ∈ GLBPrimeCore p H := (mem_glbPrimeCore_iff_mk_eq_one n).mpr hn
    have hc := h.commutator_mem_twoCore_of_component hL hLH hLN hnN (Subgroup.mem_subgroupOf.mp hx)
    have hcD : n * x * n⁻¹ * x⁻¹ ∈ D :=
      Subgroup.subset_normalClosure (Subgroup.mem_subgroupOf.mpr (by simpa using hc))
    have h1 : q (n * x * n⁻¹ * x⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hcD
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    calc q n * q x = (q n * q x * (q n)⁻¹ * (q x)⁻¹) * q x * q n := by group
      _ = q x * q n := by rw [h1, one_mul]
  set Γ := Subgroup.normalClosure (Lt : Set (↥H ⧸ D)) with hΓ
  have hΓC : Γ ≤ Subgroup.centralizer (Nt : Set (↥H ⧸ D)) :=
    Subgroup.normalClosure_le_normal hLtC
  have hXs : IsSimpleGroup (H ⧸ primeComplementCore (G := H) p) := by
    have := hKs
    exact ((MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv).symm.isSimpleGroup
  set ψ₀ : ↥Γ →* H ⧸ primeComplementCore (G := H) p := π'.comp Γ.subtype with hψ₀
  have hψ₀s : Function.Surjective ψ₀ := by
    rw [← MonoidHom.range_eq_top]
    have hrange : ψ₀.range = Subgroup.normalClosure (π' '' (Lt : Set (↥H ⧸ D))) := by
      rw [hψ₀, MonoidHom.range_comp, Subgroup.range_subtype, hΓ,
        Subgroup.map_normalClosure _ _ hπ's]
    rw [hrange]
    refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure (π' '' (Lt : Set (↥H ⧸ D))))).resolve_left fun h0 => ?_
    apply hLN
    intro x hx
    have hmem : π' (q ⟨x, hLH hx⟩) ∈ Subgroup.normalClosure (π' '' (Lt : Set (↥H ⧸ D))) :=
      Subgroup.subset_normalClosure ⟨q ⟨x, hLH hx⟩, ⟨⟨x, hLH hx⟩, Subgroup.mem_subgroupOf.mpr hx,
        rfl⟩, rfl⟩
    rw [h0, Subgroup.mem_bot, hπ'q] at hmem
    exact (mem_glbPrimeCore_iff_mk_eq_one (⟨x, hLH hx⟩ : H)).mpr hmem
  have hψ₀ker : ψ₀.ker ≤ Subgroup.center ↥Γ := by
    intro γ hγ
    have hγN : (γ : ↥H ⧸ D) ∈ Nt := by
      have : (γ : ↥H ⧸ D) ∈ π'.ker := hγ
      rwa [QuotientGroup.ker_lift] at this
    rw [Subgroup.mem_center_iff]
    intro γ'
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hΓC γ'.2) _ hγN).symm
  set eX : H ⧸ primeComplementCore (G := H) p ≃* (TauCeti.CFSGIndex.sporadic .HS).Group :=
    ((MulEquiv.subgroupCongr hKtop).trans Subgroup.topEquiv).symm.trans e₀ with heX
  set ψ := eX.toMonoidHom.comp ψ₀ with hψ
  have hψs : Function.Surjective ψ := eX.surjective.comp hψ₀s
  have hψker : ψ.ker ≤ Subgroup.center ↥Γ := fun γ hγ =>
    hψ₀ker (by
      rw [MonoidHom.mem_ker] at hγ ⊢
      exact eX.injective (by rw [map_one]; exact hγ))
  set tL : ↥H ⧸ D := q ⟨l, hLH hlL⟩ with htL
  have htLt : tL ∈ Lt := ⟨⟨l, hLH hlL⟩, Subgroup.mem_subgroupOf.mpr hlL, rfl⟩
  set γt : ↥Γ := ⟨tL, Subgroup.subset_normalClosure htLt⟩ with hγt
  have hLtperf : ⁅Lt, Lt⁆ = Lt := by
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL.perfect
    have hp' := Group.IsPerfect.range (q.comp (Subgroup.inclusion hLH))
    have hr : (q.comp (Subgroup.inclusion hLH)).range = Lt := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨Subgroup.inclusion hLH y, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
    rw [hr] at hp'
    exact Subgroup.isPerfect_iff.mp hp'
  have hγtc : γt ∈ commutator ↥Γ := by
    have hmap : (commutator ↥Γ).map Γ.subtype = ⁅Γ, Γ⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    have hmem : tL ∈ ⁅Γ, Γ⁆ := by
      have hle : Lt ≤ Γ := Subgroup.le_normalClosure
      exact Subgroup.commutator_mono hle hle (hLtperf.symm ▸ htLt)
    rw [← hmap] at hmem
    obtain ⟨γ, hγ, hγeq⟩ := hmem
    have : γ = γt := Subtype.ext hγeq
    rwa [← this]
  have hγtk : γt ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    change eX (π' tL) = 1
    have : π ⟨l, hLH hlL⟩ = 1 := (mem_glbPrimeCore_iff_mk_eq_one (⟨l, hLH hlL⟩ : H)).mp hlN
    rw [htL, hπ'q, this, map_one]
  obtain ⟨j, hsq⟩ := hMult _ ψ hψs hψker γt ⟨hγtk, hγtc⟩
  have hsqD : (⟨l, hLH hlL⟩ : ↥H) ^ 2 ^ j ∈ D := by
    have h1 : tL ^ 2 ^ j = 1 := by
      have := congrArg Subtype.val hsq
      simpa using this
    rw [htL, ← map_pow] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hsqS : (l ^ 2 ^ j : G) ∈ pCoreOf 2 H := by
    have := Subgroup.mem_subgroupOf.mp (hDS hsqD)
    simpa using this
  obtain ⟨k, hk⟩ := (CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H) ⟨l ^ 2 ^ j, hsqS⟩
  refine ⟨j + k, ?_⟩
  have hk' : (l ^ 2 ^ j) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [pow_add, pow_mul]
  exact hk'

theorem AGLPair.center_barM_eq_bot_of_hs [Fact p.Prime] (h : AGLPair p M H R)
    (hMult : KFactHSMultiplier) {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}
    (hKtop : K = ⊤) (hKs : IsSimpleGroup ↥K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .HS).Group))
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) (hLK : L ≤ H ⊓ M)
    (hLN : ¬ L ≤ GLBPrimeCore p H)
    (hZL : Subgroup.center ↥((L.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p))) = ⊥) :
    Subgroup.center ↥(barM M L) = ⊥ := by
  have hLH : L ≤ H := hLK.trans inf_le_left
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨m, hm, hmz⟩ := z.2
  have hmL : (m : G) ∈ L := Subgroup.mem_subgroupOf.mp hm
  have hmK : (m : G) ∈ H ⊓ M := hLK hmL
  have hzC : (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  have hmC : QuotientGroup.mk' (CFSG.pCore 2 ↥M) ⟨m, hmK.2⟩ ∈
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    have : (⟨m, hmK.2⟩ : ↥M) = m := rfl
    rw [this, hmz]
    exact hzC
  have hπC := h.map_mem_centralizer_of_barM hLK hmK hmC
  have hmN : (m : G) ∈ GLBPrimeCore p H := by
    have hc : (⟨QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨m, hmK.1⟩,
        ⟨⟨m, hmK.1⟩, Subgroup.mem_subgroupOf.mpr hmL, rfl⟩⟩ :
          ↥((L.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))) ∈
        Subgroup.center ↥((L.subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) p))) :=
      Subgroup.mem_center_iff.mpr fun v =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hπC v v.2)
    rw [hZL, Subgroup.mem_bot] at hc
    exact (mem_glbPrimeCore_iff_mk_eq_one (⟨m, hmK.1⟩ : H)).mpr (congrArg Subtype.val hc)
  obtain ⟨k, hk⟩ := h.exists_pow_two_eq_one_of_hs hMult hKtop hKs he hL hLH hLN hmL hmN
  have hzk : (z : ↥M ⧸ CFSG.pCore 2 ↥M) ^ 2 ^ k = 1 := by
    rw [← hmz, ← map_pow]
    have : m ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hodd := coprime_two_card_inf_centralizer (pCore_quotient_pCore_eq_bot' 2)
    hL.component.2.1
  have h1 : orderOf (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
  have h2 : orderOf (z : ↥M ⧸ CFSG.pCore 2 ↥M) ∣
      Nat.card (barM M L ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.orderOf_dvd_natCard _ ⟨z.2, hzC⟩
  have h3 := Nat.eq_one_of_dvd_coprimes (hodd.pow_left k) h1 h2
  exact Subgroup.mem_bot.mpr (Subtype.ext (orderOf_eq_one_iff.mp h3))

end CenterFree

theorem hsFiveCaseTwo_twoComponents {G : Type} [Group G] [Finite G] (hHS : KFactHSFiveOver)
    (hloc : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hα : KFactThreeOrFiveDvd) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hK2 : KFactParabolicThree)
    (hC3 : CitedBlockThreeTransvection) (hK5 : KFactBlockThreeAltSeven)
    (hMult : KFactHSMultiplier) (hO3 : KFactBlockThreeOrderThree)
    (hglob : AGLGlobal G) (hD1 : D1For G) (hNX : NoXBlockFor G)
    {P : Sylow 5 G} {M A H R : Subgroup G} (hesc : D2Escape 5 P M A H R)
    {Rbar : Sylow 5 (H ⧸ primeComplementCore (G := H) 5)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 5)}
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)))
    (hK : D2AlmostSimple 5 (H ⧸ primeComplementCore (G := H) 5) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5))) K)
    (he : Nonempty (K ≃* (TauCeti.CFSGIndex.sporadic .HS).Group))
    (hne : ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)) ≠
      Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) :
        Set (H ⧸ primeComplementCore (G := H) 5))))
    {L₀ : Subgroup G} (hL₀ : IsTwoPrimeComponent M L₀) (hL₀K : L₀ ≤ H ⊓ M)
    (hL₀N : ¬ L₀ ≤ GLBPrimeCore 5 H)
    (hM3 : 3 ≤ Open.pRank 3 (H ⊓ M) → Open.pRank 3 M ≤ 3) :
    AGLPair 5 M H R ∧ ∃ U : Subgroup (H ⧸ primeComplementCore (G := H) 5),
      Nonempty (↥(barM M L₀) ⧸ Subgroup.center ↥(barM M L₀) ≃* ↥U) ∧
      ¬ 5 ∣ Nat.card (Outer ↥(barM M L₀)) ∧ 5 ∣ Nat.card ↥(barM M L₀) ∧
      ∃ L₁ : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L₁ ∧ barM M L₀ ≠ barM M L₁ ∧
        (∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
          Lb = barM M L₀ ∨ Lb = barM M L₁) ∧
        (∀ F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), F ≤ barM M L₁ → IsElemAbelian 3 F →
          Nat.card F ≤ 3) ∧
        ∀ x ∈ Subgroup.centralizer
          (CFSG.ComponentClassification.Layer.subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :
            Set (↥M ⧸ CFSG.pCore 2 ↥M)), (orderOf x).Coprime 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hNX₀ : Subgroup.normalizer (((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5))) :
      Set (H ⧸ primeComplementCore (G := H) 5)) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore 5)) :=
    hK.normalizer_le_of_rank _ hK.sylow_le Rbar.isPGroup' (by rw [hK.pRank_eq])
  obtain ⟨hKtop, U, hUX₀, hX₀U, hUU, hRU, hUs, hUperf, hCU, hUout, E, hEU, hE, hEc⟩ :=
    hHS _ K hK.normal hK.centralizer_eq_bot he Rbar _ hNX₀ hK.ne_top hne
  obtain ⟨-, hcard, hC, hZ, hcomm, hexp, -, hlines⟩ :=
    hloc _ K hK.normal hK.centralizer_eq_bot he 5 rfl Rbar
  have hover := hK.heisOver_of_simple hcard hC hZ hcomm hexp hlines hUX₀ hX₀U hRU hUs hCU
  have hdata := hesc.heisDataCore_of_over hglob hRbar hK hover
  have hpair := hdata.pair
  have hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      BlockHasThree M (pCoreOf 2 H) L :=
    fun L hL => hpair.blockHasThree h85 h86 h93 hNX hK2 hC3 hK5 hL
  obtain ⟨J, hJK, hJ, hRJ, hJU⟩ :=
    hesc.exists_perfect_over hRbar hdata.heis.2.2 hUX₀ hX₀U hUU hRU
  have hKeq := hpair.inf_eq_inf_normalizer_twoCore
  have hπL₀ := hpair.map_eq_of_component hD1 hα hB3 hUs hUperf hJK hJ hJU hL₀ hL₀K hL₀N
  have hRne : (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) 5)) ≠ ⊥ := fun h0 => by
    have h1 := hcard
    rw [h0, Subgroup.card_bot] at h1
    norm_num at h1
  have hZU : Subgroup.center ↥U = ⊥ := by
    set Z' := (Subgroup.center ↥U).map U.subtype with hZ'
    have hZ'n : U ≤ Subgroup.normalizer (Z' : Set (H ⧸ primeComplementCore (G := H) 5)) := by
      intro u hu
      refine AltData.mem_normalizer_of_conj_mem fun x hx => ?_
      obtain ⟨z, hz, rfl⟩ := hx
      have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨u, hu⟩)
      have hc' : u * (z : H ⧸ primeComplementCore (G := H) 5) * u⁻¹ = z := by
        simp only [Subgroup.coe_mul] at hc
        rw [hc, mul_inv_cancel_right]
      rw [Subgroup.coe_subtype, hc']
      exact ⟨z, hz, rfl⟩
    rcases hUs Z' (Subgroup.map_subtype_le _) hZ'n with h0 | h0
    · exact (Subgroup.map_eq_bot_iff_of_injective _ U.subtype_injective).mp h0
    · exfalso
      have hab : ⁅U, U⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hxZ : x ∈ Z' := h0 ▸ hx
        obtain ⟨z, hz, rfl⟩ := hxZ
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
      rw [hUU] at hab
      exact hRne (le_bot_iff.mp (hab ▸ hRU))
  have hZπ : Subgroup.center ↥((L₀.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) 5))) = ⊥ := by
    rw [hπL₀]
    exact hZU
  have hZL₀ := hpair.center_barM_eq_bot_of_hs hMult hKtop hK.isSimpleGroup_K he hL₀ hL₀K hL₀N hZπ
  obtain ⟨φ⟩ := hpair.nonempty_centerQuotient_mulEquiv hL₀ hL₀K hL₀N hZπ
  obtain ⟨φ₀⟩ : Nonempty (↥(barM M L₀) ⧸ Subgroup.center ↥(barM M L₀) ≃* ↥U) :=
    ⟨φ.trans (MulEquiv.subgroupCongr hπL₀)⟩
  have hout₀ : ¬ 5 ∣ Nat.card (Outer ↥(barM M L₀)) := by
    have : Group.IsPerfect ↥(barM M L₀) := ⟨hL₀.component.2.2.1⟩
    refine not_dvd_card_outer_of_quotient ?_
    rw [Nat.card_congr (equivalence φ₀).toEquiv]
    exact hUout
  obtain ⟨hE3, hEnc⟩ := isPGroup_not_isCyclic_of_isElemAbelian Nat.prime_three hE hEc
  set eE := Subgroup.subgroupOfEquivOfLe hEU with heE
  obtain ⟨E₀, hE₀L, hE₀, hE₀c⟩ := exists_isElemAbelian_three_of_centerQuotient φ₀
    (E := E.subgroupOf U) (hE3.of_equiv eE.symm)
    (fun h => hEnc (isCyclic_of_surjective eE.toMonoidHom eE.surjective))
  have hX₁ : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      ∃ y ∈ blockPL M (pCoreOf 2 H) L, y ^ 3 = 1 ∧
        y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    fun L hL => hO3 G M _ L hpair.isKGroup.1 hpair.asc81bHyp hL
      (hpair.nineThree_not_one h85 hNX hL).1 (hpair.not_isSylowTwoOf_inf h85 hNX hL)
  have hPK : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      blockPL M (pCoreOf 2 H) L ≤ barM M (H ⊓ M) := fun L hL =>
    barM_mono (by rw [hKeq]; exact le_inf (inf_le_right.trans hL.le) inf_le_left)
  have hPL : ∀ L : Subgroup G, blockPL M (pCoreOf 2 H) L ≤ barM M L := fun L =>
    barM_mono inf_le_right
  have hcc : ∀ {A₀ B₀ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}, IsComponentOf A₀ ⊤ →
      IsComponentOf B₀ ⊤ → A₀ ≠ B₀ →
        A₀ ≤ Subgroup.centralizer (B₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun hA hB hAB =>
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hA hB hAB)
  have hne_blk : ∀ L L' : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      IsTwoPrimeComponent M L' → L' ≤ H ⊓ M → barM M L ≠ barM M L' := by
    intro L L' hL hL' hL'K heq
    have hLL' := hL.toIsTwoPrimeComponent.eq_of_barM_eq hL' heq
    apply hL.not_le_normalizer
    rw [hLL']
    exact (hKeq ▸ hL'K).trans inf_le_right
  have hLb₀K : barM M L₀ ≤ barM M (H ⊓ M) := barM_mono hL₀K
  obtain ⟨L₁, hL₁⟩ := hpair.exists_weakSBlock h84 hNX
  obtain ⟨y₁, hy₁P, hy₁3, hy₁C⟩ := hX₁ L₁ hL₁
  have hy₁L : y₁ ∈ barM M L₁ := hPL L₁ hy₁P
  have hy₁K : y₁ ∈ barM M (H ⊓ M) := hPK L₁ hL₁ hy₁P
  have hne₀₁ : barM M L₀ ≠ barM M L₁ := (hne_blk L₁ L₀ hL₁ hL₀ hL₀K).symm
  have hE₀C₁ : E₀ ≤ Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    hE₀L.trans (hcc hL₀.component hL₁.component hne₀₁)
  have hy₁E₀ : y₁ ∈ Subgroup.centralizer (E₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.le_centralizer_iff.mp hE₀C₁) hy₁L
  set A₁ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := E₀ ⊔ Subgroup.zpowers y₁ with hA₁
  have hA₁K : A₁ ≤ barM M (H ⊓ M) :=
    sup_le (hE₀L.trans hLb₀K) (Subgroup.zpowers_le.mpr hy₁K)
  have h3A₁ : 3 ≤ Open.pRank 3 A₁ := by
    have h1 := succ_pRank_le_of_commute (q := 3) (B := A₁) le_sup_left hE₀C₁
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers y₁)) hy₁3 hy₁C hy₁E₀
    have h2 := le_pRank_of_isElemAbelian Nat.prime_three hE₀ hE₀c
    omega
  have hK3 := hpair.pRank_inf_le_three hD1 Nat.prime_three (by decide)
  have h3K : 3 ≤ Open.pRank 3 (H ⊓ M) :=
    (h3A₁.trans (SectionRank.pRank_mono (by norm_num) hA₁K)).trans
      (pRank_barM_le Nat.prime_three (by decide) M (H ⊓ M) inf_le_right)
  have hM3 := hM3 h3K
  have hA₁C : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      Lb ≠ barM M L₀ → Lb ≠ barM M L₁ →
        A₁ ≤ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := fun Lb hLb h0 h1 =>
    sup_le (hE₀L.trans (hcc hL₀.component hLb (Ne.symm h0)))
      (Subgroup.zpowers_le.mpr ((hcc hL₁.component hLb (Ne.symm h1)) hy₁L))
  have hfour : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      Lb ≠ barM M L₀ → Lb ≠ barM M L₁ → ∀ w ∈ Lb, w ∈ barM M (H ⊓ M) → w ^ 3 = 1 →
        w ∉ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) → False := by
    intro Lb hLb h0 h1 w hwL hwK hw3 hwC
    have hwA₁ : w ∈ Subgroup.centralizer (A₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      (Subgroup.le_centralizer_iff.mp (hA₁C Lb hLb h0 h1)) hwL
    have h4 := succ_pRank_le_of_commute (q := 3) hA₁K (hA₁C Lb hLb h0 h1) hwK hw3 hwC hwA₁
    have h4' := (by omega : 4 ≤ Open.pRank 3 (barM M (H ⊓ M))).trans
      (pRank_barM_le Nat.prime_three (by decide) M (H ⊓ M) inf_le_right)
    omega
  have hblock_eq : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
      barM M L = barM M L₁ := by
    intro L hL
    by_contra hne1
    obtain ⟨y, hyP, hy3, hyC⟩ := hX₁ L hL
    exact hfour _ hL.component (hne_blk L L₀ hL hL₀ hL₀K) hne1 y (hPL L hyP) (hPK L hL hyP) hy3
      hyC
  have hK_eq : ∀ L : Subgroup G, IsTwoPrimeComponent M L → L ≤ H ⊓ M →
      barM M L = barM M L₀ := by
    intro L hL hLK
    by_contra hne0
    have hLN : L ≤ GLBPrimeCore 5 H := fun x hx =>
      hpair.mem_glbPrimeCore_of_centralizer hCU hL₀K hπL₀ (hLK hx)
        ((hcc hL.component hL₀.component hne0)
          (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)))
    have hcat := hpair.isCatalogGroup_center_quotient_component hL.component
    have hdvdN : Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∣
        Nat.card (GLBPrimeCore 5 H) := by
      have h1 : Nat.card ↥(barM M L) ∣ Nat.card ↥L := by
        have := Subgroup.card_range_dvd (barElt M hL.le)
        rwa [range_barElt hL.le] at this
      exact (Subgroup.index_dvd_card _).trans (h1.trans (Subgroup.card_dvd_of_le hLN))
    have h3 : 3 ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := by
      rcases hα _ hL.component.2.2.2
          (ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _
            hL.component.2.2) hcat with h | h
      · exact h
      · exact absurd (Nat.Coprime.eq_one_of_dvd (glbPrimeCore_coprime 5 H) (h.trans hdvdN))
          (by norm_num)
    obtain ⟨t, ht3, htZ⟩ := exists_orderOf_eq_not_mem_center Nat.prime_three (by decide)
      hL.component.2.2 h3
    have hne1 : barM M L ≠ barM M L₁ := fun h => hne_blk L₁ L hL₁ hL hLK h.symm
    refine hfour _ hL.component hne0 hne1 t t.2 (barM_mono hLK t.2) ?_ ?_
    · have h1 := pow_orderOf_eq_one t
      rw [ht3] at h1
      exact congrArg Subtype.val h1
    · intro htC
      apply htZ
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp htC g g.2)
  have hcomps : ∀ Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), IsComponentOf Lb ⊤ →
      Lb = barM M L₀ ∨ Lb = barM M L₁ := by
    intro Lb hLb
    obtain ⟨L, hL2, rfl, hL⟩ := hpair.exists_weakSBlock_or_le_inf hLb
    rcases hL with hw | hk
    · exact Or.inr (hblock_eq L hw)
    · exact Or.inl (hK_eq L hL2 hk)
  have hnoE : ∀ F : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), F ≤ barM M L₁ → IsElemAbelian 3 F →
      Nat.card F ≤ 3 := by
    intro F hFL hF
    by_contra hlt
    have hF3 : IsPGroup 3 F := fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hF3
    have hn2 : 2 ≤ n := by
      by_contra h
      interval_cases n <;> simp_all
    have h2F : 2 ≤ Open.pRank 3 F := hn2.trans (le_pRank_of_isElemAbelian Nat.prime_three hF hn)
    obtain ⟨F', hF'F, hF', hF'c⟩ :=
      exists_isElemAbelian_card_sq_of_two_le_pRank Nat.prime_three h2F
    have hdisj : E₀ ⊓ F' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxL₀ : x ∈ barM M L₀ := hE₀L hx.1
      have hxC : x ∈ Subgroup.centralizer (barM M L₀ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        (hcc hL₁.component hL₀.component hne₀₁.symm) (hFL (hF'F hx.2))
      have hxZ : (⟨x, hxL₀⟩ : ↥(barM M L₀)) ∈ Subgroup.center ↥(barM M L₀) :=
        Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC g g.2)
      rw [hZL₀, Subgroup.mem_bot] at hxZ
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxZ)
    have hcomm' : ∀ a ∈ E₀, ∀ b ∈ F', a * b = b * a := fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.mp ((hcc hL₀.component hL₁.component hne₀₁) (hE₀L ha)) b
        (hFL (hF'F hb))).symm
    have h4 := four_le_pRank_of_commute_of_inf_eq_bot hE₀ hF' hE₀c hF'c hcomm' hdisj
    have hMbar : barM M M = ⊤ := by
      rw [barM, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, QuotientGroup.range_mk']
    have h5 := pRank_barM_le Nat.prime_three (by decide) M M le_rfl
    rw [hMbar] at h5
    omega
  have hSC₁ := centralizer_layer_le_centralizer (pCore_quotient_pCore_eq_bot' 2)
    (S := barM M (pCoreOf 2 H))
    ((CFSG.PreuniquenessRankFour.Helpers.pCoreOf_isPGroup 2 H).comap_subtype.map _)
    (hpair.oddCore_le_centralizer h84 hNX)
  have hC₁5 : ∀ x ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.Layer.subgroup (↥M ⧸ CFSG.pCore 2 ↥M) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M)), (orderOf x).Coprime 5 := fun x hx =>
    hpair.coprime_orderOf_of_centralizer hCU hL₀K hπL₀
      (hpair.le_barM_inf_of_le_centralizer hSC₁ hx)
      (Subgroup.centralizer_le
        (CFSG.ComponentClassification.Layer.component_le hL₀.component) hx)
  have h5L₀ : 5 ∣ Nat.card ↥(barM M L₀) := by
    have h1 : 5 ∣ Nat.card ↥U := by
      have h2 := Subgroup.card_dvd_of_le hRU
      rw [hcard] at h2
      exact (dvd_pow_self 5 (by norm_num)).trans h2
    rw [← Nat.card_congr φ₀.toEquiv] at h1
    exact h1.trans (Subgroup.index_dvd_card _)
  exact ⟨hpair, U, ⟨φ₀⟩, hout₀, h5L₀, L₁, hL₁, hne₀₁, hcomps, hnoE, hC₁5⟩

theorem d2HSFiveCaseTwo_of (hHS : KFactHSFiveOver)
    (hloc : D2HeisLocalEqAt (.sporadic .HS) fun p => p = 5)
    (hα : KFactThreeOrFiveDvd) (h84 : Asc81bEightFour) (h85 : Asc81bEightFive)
    (h86 : Asc81bEightSix) (h93 : Asc81bNineThree) (hD2 : D1NoXBlock)
    (hK2 : KFactParabolicThree) (hC3 : CitedBlockThreeTransvection)
    (hK5 : KFactBlockThreeAltSeven) (hMult : KFactHSMultiplier)
    (hO3 : KFactBlockThreeOrderThree) (hC5 : KFactBlockCyclicThreeFive) : D2HSFiveCaseTwo := by
  intro G _ _ hglob hD1 P M A H R hesc hmax hβ Rbar K hRbar hK he hne L₀ hL₀ hL₀K hL₀N
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hNX : NoXBlockFor G := hD2.noXBlockFor hglob.toD1Global
  obtain ⟨hpair, U, ⟨φ₀⟩, hout₀, -, L₁, hL₁, hne₀₁, hcomps, hnoE, hC₁5⟩ :=
    hsFiveCaseTwo_twoComponents hHS hloc hα h84 h85 h86 h93 hK2 hC3 hK5 hMult hO3
      hglob.toAGLGlobal hD1 hNX hesc hRbar hK he hne hL₀ hL₀K hL₀N fun h3K => by
        have hβ3 : 3 ∉ GLBBetaFour G := fun h3 =>
          hesc.false_of_three_le_pRank_both hglob.toAGLGlobal.pre hβ h3 (hD1.at h3)
            (h3K.trans (pRank_mono 3 Nat.prime_three inf_le_left))
            (h3K.trans (pRank_mono 3 Nat.prime_three inf_le_right))
        by_contra hlt
        exact hβ3 ⟨Nat.prime_three, by norm_num,
          prime_dvd_card_of_positive_rank 3 Nat.prime_three M (by omega),
          (by omega : 4 ≤ Open.pRank 3 M).trans
            (le_csSup (twoLocalRank_bddAbove 3 Nat.prime_three) ⟨M, hesc.maxTwoLocal_M.1, rfl⟩)⟩
  have hC5' := hC5 G M _ L₁ hpair.isKGroup.1 hpair.asc81bHyp hL₁
    (hpair.nineThree_not_one h85 hNX hL₁).1 (hpair.not_isSylowTwoOf_inf h85 hNX hL₁) hnoE
  obtain ⟨E₅', hE₅'M, hE₅', hE₅'c⟩ := exists_isElemAbelian_card_pow_of_le_pRank (p := 5) (k := 4)
    Nat.prime_five (hesc.four_le_pRank_M hβ)
  have hE₅'p : IsPGroup 5 E₅' := fun x => ⟨1, Subtype.ext (by simpa using hE₅'.2 x x.2)⟩
  have hE₅c : Nat.card (barM M E₅') = 5 ^ 4 :=
    (hpair.card_barM_of_isPGroup hE₅'M hE₅'p).trans hE₅'c
  have hE₅el : IsElemAbelian 5 (barM M E₅') := by
    refine ⟨isMulCommutative_iff.mpr fun a b => ?_, ?_⟩
    · obtain ⟨_, ⟨ma, hma, rfl⟩⟩ := a
      obtain ⟨_, ⟨mb, hmb, rfl⟩⟩ := b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul]
      congr 1
      have := hE₅'.1
      have hc : (ma : G) * mb = mb * ma := by
        have h1 := congrArg Subtype.val
          (mul_comm' (⟨ma, Subgroup.mem_subgroupOf.mp hma⟩ : E₅')
            ⟨mb, Subgroup.mem_subgroupOf.mp hmb⟩)
        simpa using h1
      exact Subtype.ext hc
    · rintro _ ⟨m, hm, rfl⟩
      rw [← map_pow]
      have : m ^ 5 = 1 := Subtype.ext (by simpa using hE₅'.2 _ (Subgroup.mem_subgroupOf.mp hm))
      rw [this, map_one]
  have hle := card_le_of_two_components hL₀.component hL₁.component hne₀₁ hcomps hC₁5 hout₀ φ₀
    (by rw [hK.pRank_top]) hC5' hE₅el
  rw [hE₅c] at hle
  norm_num at hle

end CFSG.AGLEmbeddingD2
