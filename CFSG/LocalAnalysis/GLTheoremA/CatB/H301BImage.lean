module

public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62AuxComp
public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017RedTwist
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420Lift
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BKernel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8
open CFSG.HardMathSupport.Timmesfeld.Coordinator
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem centMod_of_mem_core {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) (hXN : X ≤ Subgroup.normalizer (J : Set G)) {g : G}
    (hg : g ∈ GLAPPrimeCoreOf p X) : CentMod p J g := by
  have hOX : GLAPPrimeCoreOf p X ≤ X := by
    unfold GLAPPrimeCoreOf
    exact Subgroup.map_subtype_le _
  have hgN : g ∈ Subgroup.normalizer (J : Set G) := hXN (hOX hg)
  refine ⟨hgN, Subgroup.commutator_le.mpr fun l hl c hc => ?_⟩
  have hcO : c ∈ GLAPPrimeCoreOf p X := (Subgroup.zpowers_le.2 hg) hc
  have hcN : c ∈ Subgroup.normalizer (J : Set G) := (Subgroup.zpowers_le.2 hgN) hc
  have hA : ⁅l, c⁆ ∈ J := by
    have h4 := (Subgroup.mem_normalizer_iff.1 hcN l⁻¹).1 (J.inv_mem hl)
    simpa [commutatorElement_def, mul_assoc] using J.mul_mem hl h4
  have hB : ⁅l, c⁆ ∈ GLAPPrimeCoreOf p X := by
    have h5 := (Subgroup.mem_normalizer_iff.1 (GLTheoremB.le_normalizer_glaPPrimeCoreOf p X
      (hJ.1 hl)) c).1 hcO
    simpa [commutatorElement_def, mul_assoc] using
      (GLAPPrimeCoreOf p X).mul_mem h5 ((GLAPPrimeCoreOf p X).inv_mem hcO)
  rw [← GLTheoremB.glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hJ.2.1]
  exact ⟨hA, hB⟩

theorem card_phiImg_mul {p : ℕ} (hp : p.Prime) {X J H : Subgroup G} (hJ : GLAPComponent p X J)
    (hHN : H ≤ Subgroup.normalizer (J : Set G)) :
    Nat.card ((H.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J)) *
      Nat.card (H ⊓ centModSubgroup p J : Subgroup G) = Nat.card H := by
  set ψ := (L62.phiC p J).comp (Subgroup.inclusion hHN) with hψ
  have hrange : ψ.range = (H.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J) := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker : ψ.ker = (centModSubgroup p J).subgroupOf H := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← centMod_iff]
    exact L62.phiC_eq_one_iff hp hJ (hHN h.2)
  have hcard : Nat.card ψ.ker = Nat.card (H ⊓ centModSubgroup p J : Subgroup G) := by
    rw [hker, ← Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [← hrange, ← hcard, mul_comm]
  exact Subgroup.card_ker_mul_card_range ψ

theorem phiImg_le_range_conj (hOut : SporadicOuterLeTwo) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X J H : Subgroup G} (hJ : GLAPComponent p X J) (hsp : catalogIs (PSimple p J) isSporIndex)
    (hH : ∀ h ∈ H, h ^ p = 1) :
    (H.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J) ≤
      (MulAut.conj : PSimple p J →* MulAut (PSimple p J)).range := by
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨s, hs⟩ := H1017.exists_phiC_eq_conj hOut hp hp2 hJ hsp h
    (Subtype.ext (by simpa using hH _ (Subgroup.mem_subgroupOf.1 hh)))
  exact ⟨s, hs.symm⟩

theorem phiImg_le_range_conj_of_le {p : ℕ} {J H : Subgroup G} (hHJ : H ≤ J) :
    (H.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J) ≤
      (MulAut.conj : PSimple p J →* MulAut (PSimple p J)).range := by
  rintro _ ⟨h, hh, rfl⟩
  have hJ : ((h : ↥(Subgroup.normalizer (J : Set G))) : G) ∈ J :=
    hHJ (Subgroup.mem_subgroupOf.1 hh)
  exact ⟨_, (L62.phiC_inner p ⟨(h : G), hJ⟩ h.2).symm⟩

theorem phiImg_le_cx {p : ℕ} (hp : p.Prime) {X J H : Subgroup G} {y : G}
    (hJ : GLAPComponent p X J) (hXN : X ≤ Subgroup.normalizer (J : Set G))
    (hy : y ∈ Subgroup.normalizer (J : Set G)) (hH : H ≤ (X ⊓ cx y) ⊔ GLAPPrimeCoreOf p X) :
    (H.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J) ≤
      cx (L62.phiC p J ⟨y, hy⟩) := by
  set N := Subgroup.normalizer (J : Set G)
  set M : Subgroup G := ((cx (L62.phiC p J ⟨y, hy⟩)).comap (L62.phiC p J)).map N.subtype
  have hOX : GLAPPrimeCoreOf p X ≤ X := by
    unfold GLAPPrimeCoreOf
    exact Subgroup.map_subtype_le _
  have hM : (X ⊓ cx y) ⊔ GLAPPrimeCoreOf p X ≤ M := by
    refine sup_le (fun g hg => ⟨⟨g, hXN hg.1⟩, ?_, rfl⟩) (fun g hg => ⟨⟨g, hXN (hOX hg)⟩, ?_, rfl⟩)
    · show _ ∈ cx _
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      exact congrArg _ (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hg.2))
    · show _ ∈ cx _
      rw [(L62.phiC_eq_one_iff hp hJ (hXN (hOX hg))).2 (centMod_of_mem_core hp hJ hXN hg)]
      exact Subgroup.one_mem _
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨n, hn, hne⟩ := hM (hH (Subgroup.mem_subgroupOf.1 hh))
  have hnh : n = h := Subtype.ext hne
  subst hnh
  exact hn

theorem phiImg_le_normalizer {p : ℕ} {J H R : Subgroup G}
    (hRN : R ≤ Subgroup.normalizer (J : Set G)) (hH : H ≤ Subgroup.normalizer (R : Set G)) :
    (H.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J) ≤
      Subgroup.normalizer (((R.subgroupOf (Subgroup.normalizer (J : Set G))).map
        (L62.phiC p J) : Subgroup (MulAut (PSimple p J))) : Set (MulAut (PSimple p J))) := by
  rintro _ ⟨h, hh, rfl⟩
  apply H1420.map_mem_normalizer_of_mem
  rw [← Subgroup.subgroupOf_normalizer_eq hRN]
  exact Subgroup.mem_subgroupOf.2 (hH (Subgroup.mem_subgroupOf.1 hh))

theorem nonempty_mulEquiv_phiImg {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : G} {J R : Subgroup G}
    (ha : orderOf a = p) (hJ : GLAPComponent p (cx a) J)
    (hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → (∀ x ∈ A, CentMod p J x) → Nat.card A ≤ p)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf p (cx a)))) (hRX : R ≤ cx a) (hR : IsPGroup 2 R) :
    Nonempty (↥R ≃* ↥((R.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J))) := by
  have hRN : R ≤ Subgroup.normalizer (J : Set G) :=
    hRX.trans (cx_le_normalizer_of_rankOne hp hp2 ha hJ hrk1)
  set ψ := (L62.phiC p J).comp (Subgroup.inclusion hRN) with hψ
  have hrange : ψ.range = (R.subgroupOf (Subgroup.normalizer (J : Set G))).map (L62.phiC p J) := by
    rw [hψ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro r hr
    obtain ⟨m, hm⟩ := hR r
    exact Subtype.ext (eq_one_of_centMod_two hp hp2 ha hJ hrk1 hodd (hRX r.2)
      ⟨m, by simpa using congrArg Subtype.val hm⟩ ((L62.phiC_eq_one_iff hp hJ (hRN r.2)).1 hr))
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)⟩

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
