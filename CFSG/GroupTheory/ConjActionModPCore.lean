module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.GroupTheory

open scoped commutatorElement

variable {G : Type*} [Group G]

noncomputable def conjAutOn (L M : Subgroup G)
    (hM : M ≤ Subgroup.normalizer (L : Set G)) : ↥M →* MulAut ↥L :=
  (Subgroup.normalizerMonoidHom (H := L)).comp (Subgroup.inclusion hM)

theorem pCore_mem_conjAutOn (p : ℕ) (L M : Subgroup G)
    (hM : M ≤ Subgroup.normalizer (L : Set G)) (m : ↥M) :
    ∀ n ∈ CFSG.Open.pCore p ↥L, conjAutOn L M hM m n ∈ CFSG.Open.pCore p ↥L := by
  intro n hn
  have hfix := Subgroup.characteristic_iff_map_eq.mp
    (CFSG.pCore_characteristic (p := p) (G := ↥L)) (conjAutOn L M hM m)
  rw [← hfix]
  exact Subgroup.mem_map_of_mem _ hn

@[expose] noncomputable def conjModPCore (p : ℕ) (L M : Subgroup G)
    (hM : M ≤ Subgroup.normalizer (L : Set G)) :
    ↥M →* MulAut (↥L ⧸ CFSG.Open.pCore p ↥L) :=
  CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
    (conjAutOn L M hM) (CFSG.Open.pCore p ↥L) (pCore_mem_conjAutOn p L M hM)

@[simp]
theorem conjModPCore_mk (p : ℕ) (L M : Subgroup G)
    (hM : M ≤ Subgroup.normalizer (L : Set G)) (m : ↥M) (x : ↥L) :
    conjModPCore p L M hM m (QuotientGroup.mk (s := CFSG.Open.pCore p ↥L) x) =
      QuotientGroup.mk (s := CFSG.Open.pCore p ↥L) (⟨(m : G) * (x : G) * (m : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hM m.2) (x : G)).mp x.2⟩ : ↥L) := by
  rw [conjModPCore, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
  refine congrArg QuotientGroup.mk (Subtype.ext ?_)
  rw [conjAutOn, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
    Subgroup.coe_inclusion]

theorem conjModPCore_apply_eq_conj_mk (p : ℕ) (L M : Subgroup G)
    (hM : M ≤ Subgroup.normalizer (L : Set G)) {m : G} (hmM : m ∈ M) (hmL : m ∈ L) :
    conjModPCore p L M hM ⟨m, hmM⟩ =
      MulAut.conj (QuotientGroup.mk (s := CFSG.Open.pCore p ↥L) (⟨m, hmL⟩ : ↥L)) := by
  apply MulEquiv.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  rw [conjModPCore_mk, MulAut.conj_apply]
  simp only [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
  congr 1

theorem mem_map_ker_conjModPCore_iff (p : ℕ) (L M : Subgroup G)
    (hM : M ≤ Subgroup.normalizer (L : Set G)) {m : G} :
    m ∈ (conjModPCore p L M hM).ker.map M.subtype ↔
      m ∈ M ∧ ∀ x ∈ L, m * x * m⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf p L := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.2, fun x hx => ?_⟩
    let xL : ↥L := ⟨x, hx⟩
    have h1 : conjModPCore p L M hM a = 1 := MonoidHom.mem_ker.mp ha
    have h2 : (QuotientGroup.mk (⟨(a : G) * (xL : G) * (a : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hM a.2) (xL : G)).mp xL.2⟩ : ↥L) :
          ↥L ⧸ CFSG.Open.pCore p ↥L) = QuotientGroup.mk xL := by
      simpa [conjModPCore_mk] using
        congrArg (fun f => f (QuotientGroup.mk xL)) h1
    have h3 : (⟨(a : G) * (xL : G) * (a : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hM a.2) (xL : G)).mp xL.2⟩ : ↥L) / xL ∈
        CFSG.Open.pCore p ↥L :=
      QuotientGroup.eq_iff_div_mem.mp h2
    rw [CFSG.Open.pCoreOf, Subgroup.mem_map]
    refine ⟨(⟨(a : G) * (xL : G) * (a : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hM a.2) (xL : G)).mp xL.2⟩ : ↥L) / xL, h3, ?_⟩
    rw [div_eq_mul_inv]
    rfl
  · rintro ⟨hm, hcomm⟩
    let a : ↥M := ⟨m, hm⟩
    have hker : a ∈ (conjModPCore p L M hM).ker := by
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro q
      refine QuotientGroup.induction_on q ?_
      intro x
      rw [conjModPCore_mk]
      simp only [MulAut.one_apply]
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hmem : (a : G) * (x : G) * (a : G)⁻¹ * (x : G)⁻¹ ∈
          (CFSG.Open.pCore p ↥L).map L.subtype := by
        simpa [CFSG.Open.pCoreOf] using hcomm (x : G) x.2
      obtain ⟨c, hc, hEq⟩ := Subgroup.mem_map.mp hmem
      have hEq' : (⟨(a : G) * (x : G) * (a : G)⁻¹,
          (Subgroup.mem_normalizer_iff.mp (hM a.2) (x : G)).mp x.2⟩ : ↥L) / x = c := by
        apply Subtype.ext
        rw [div_eq_mul_inv]
        simpa using hEq.symm
      rwa [hEq']
    exact Subgroup.mem_map.mpr ⟨a, hker, rfl⟩

theorem le_map_ker_conjModPCore_iff_commutator (p : ℕ) (L M R : Subgroup G)
    (hM : M ≤ Subgroup.normalizer (L : Set G)) (hR : R ≤ M) :
    R ≤ (conjModPCore p L M hM).ker.map M.subtype ↔
      ⁅L, R⁆ ≤ CFSG.Open.pCoreOf p L := by
  rw [Subgroup.commutator_comm]
  constructor
  · intro h
    refine Subgroup.commutator_le.mpr fun r hr x hx => ?_
    have hmem := h hr
    rw [mem_map_ker_conjModPCore_iff] at hmem
    simpa [commutatorElement_def] using hmem.2 x hx
  · intro h r hr
    rw [mem_map_ker_conjModPCore_iff]
    refine ⟨hR hr, fun x hx => ?_⟩
    have hmem := Subgroup.commutator_le.mp h r hr x hx
    simpa [commutatorElement_def] using hmem

theorem conjModPCore_comp_inclusion (p : ℕ) (L : Subgroup G) {M M' : Subgroup G}
    (hM'M : M' ≤ M) (hM : M ≤ Subgroup.normalizer (L : Set G))
    (hM' : M' ≤ Subgroup.normalizer (L : Set G)) :
    conjModPCore p L M' hM' =
      (conjModPCore p L M hM).comp (Subgroup.inclusion hM'M) := by
  apply MonoidHom.ext
  intro m
  apply MulEquiv.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  simp [conjModPCore_mk, Subgroup.coe_inclusion]

theorem map_ker_conjModPCore_mono (p : ℕ) (L : Subgroup G) {M M' : Subgroup G}
    (hM'M : M' ≤ M) (hM : M ≤ Subgroup.normalizer (L : Set G))
    (hM' : M' ≤ Subgroup.normalizer (L : Set G)) :
    (conjModPCore p L M' hM').ker.map M'.subtype =
      M' ⊓ (conjModPCore p L M hM).ker.map M.subtype := by
  ext m
  simp only [Subgroup.mem_inf, mem_map_ker_conjModPCore_iff]
  constructor
  · rintro ⟨hm', hcomm⟩
    exact ⟨hm', hM'M hm', hcomm⟩
  · rintro ⟨hm', -, hcomm⟩
    exact ⟨hm', hcomm⟩

theorem pRank_le_pRank_map_ker_add_pRank_range [Finite G] (p q : ℕ) (hq : q.Prime)
    (L M : Subgroup G) (hM : M ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.Open.pRank q M ≤
      CFSG.Open.pRank q ((conjModPCore p L M hM).ker.map M.subtype) +
        CFSG.Open.pRank q ((conjModPCore p L M hM).range) := by
  have h := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map (p := q) hq
    (conjModPCore p L M hM) (⊤ : Subgroup ↥M)
  rw [top_inf_eq, ← MonoidHom.range_eq_map] at h
  have h2 : CFSG.Open.pRank q (conjModPCore p L M hM).ker ≤
      CFSG.Open.pRank q ((conjModPCore p L M hM).ker.map M.subtype) :=
    CFSG.SectionRank.pRank_le_map hq.one_lt M.subtype M.subtype_injective
      (conjModPCore p L M hM).ker
  have h3 : CFSG.Open.pRank q M = CFSG.Open.pRank q (⊤ : Subgroup ↥M) :=
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup M
  omega

end CFSG.GroupTheory
