module

public import CFSG.LocalAnalysis.GL83PartI.I_7_13
import CFSG.Goldschmidt.Steps.Sec82PGroup
import CFSG.Goldschmidt.Steps.Sec82Tools
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

@[expose] def KFactSylowSplit : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
    (∃ a b : K, a * b ≠ b * a) → CFSG.Open.IsCatalogGroup K →
    CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1 →
    ∀ S : Sylow p (MulAut K), ∃ R : Subgroup (MulAut K), R ≤ (S : Subgroup (MulAut K)) ∧
      R ⊓ inner K = ⊥ ∧ ((S : Subgroup (MulAut K)) ⊓ inner K) ⊔ R = (S : Subgroup (MulAut K))

namespace K62BSplit

section Rank

theorem card_le_of_isCyclic {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) (hc : IsCyclic E) : Nat.card E ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ p :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
  rw [← hg]
  exact Nat.le_of_dvd hp.pos h1

theorem card_le_of_le_sylow_cyclic {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (T : Sylow p K) (hT : IsCyclic T) {F : Subgroup K} (hF : IsElemAbelian p F) :
    Nat.card F ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨T', hT'⟩ := IsPGroup.exists_le_sylow hF.isPGroup
  have hT'c : IsCyclic T' := (MulEquiv.isCyclic (T'.equiv T)).mpr hT
  have hFc : IsCyclic (F.subgroupOf T') := inferInstance
  have hFc' : IsCyclic F := isCyclic_of_surjective (subgroupOfEquivOfLe hT').toMonoidHom
    (subgroupOfEquivOfLe hT').surjective
  exact card_le_of_isCyclic hp hF hFc'

theorem pRank_le_one_of_cyclic_sylow {K : Type*} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (T : Sylow p K) (hT : IsCyclic T) : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1 := by
  refine CFSG.GH74.Uniqueness.SU.SU1.pRank_le_of fun E _ hE k hk => ?_
  have h1 := card_le_of_le_sylow_cyclic hp T hT hE
  rw [hk] at h1
  by_contra hk1
  have h2 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
  have h3 : p < p ^ 2 := by nlinarith [hp.one_lt]
  omega

end Rank

section Local

theorem conj_injective_of_center_eq_bot {K : Type*} [Group K] (h : center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  intro g h' hgh
  have h1 : (MulAut.conj : K →* MulAut K) (g⁻¹ * h') = 1 := by
    rw [map_mul, map_inv, hgh, inv_mul_cancel]
  have : g⁻¹ * h' ∈ center K := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h2 := DFunLike.congr_fun h1 z
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  rw [h, Subgroup.mem_bot] at this
  exact inv_mul_eq_one.mp this

theorem center_eq_bot_of_simple {K : Type*} [Group K] (hsimple : IsSimpleGroup K)
    (hnonab : ∃ a b : K, a * b ≠ b * a) : center K = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have : a ∈ center K := by rw [h]; exact Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp this b).symm

theorem local_split (hsplit : KFactSylowSplit) (h7131 : GL83.I_7_13_1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {K : Type} [Group K] [Finite K] (hsimple : IsSimpleGroup K)
    (hnonab : ∃ a b : K, a * b ≠ b * a) (hcat : IsCatalogGroup K)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup K) ≤ 1) {Q : Type} [Group Q] [Finite Q]
    (hQ : IsPGroup p Q) (ψ : Q →* MulAut K) (T : Sylow p K)
    (hT : ∀ a ∈ T, ∃ q : Q, ψ q = MulAut.conj a) :
    ∃ R : Subgroup (MulAut K), IsCyclic R ∧ R ⊓ inner K = ⊥ ∧
      ∀ q : Q, ∃ a ∈ T, ∃ r ∈ R, ψ q = MulAut.conj a * r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcent : center K = ⊥ := center_eq_bot_of_simple hsimple hnonab
  have hψrange : IsPGroup p ψ.range := hQ.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨S, hψS⟩ := IsPGroup.exists_le_sylow hψrange
  obtain ⟨R, hRS, hRinner, hsup⟩ := hsplit p hp hp2 K hsimple hnonab hcat hrank S
  have hSp : IsPGroup p (S : Subgroup (MulAut K)) := S.isPGroup'
  have hI : ∀ i ∈ (S : Subgroup (MulAut K)) ⊓ inner K, ∃ a ∈ T, i = MulAut.conj a := by
    intro i hi
    have hIp : IsPGroup p ((S : Subgroup (MulAut K)) ⊓ inner K : Subgroup (MulAut K)) :=
      hSp.to_le inf_le_left
    have hinj := conj_injective_of_center_eq_bot hcent
    have hI'p : IsPGroup p (((S : Subgroup (MulAut K)) ⊓ inner K).comap
        (MulAut.conj : K →* MulAut K)) := hIp.comap_of_injective _ hinj
    have hle : (T : Subgroup K) ≤ ((S : Subgroup (MulAut K)) ⊓ inner K).comap
        (MulAut.conj : K →* MulAut K) := by
      intro a ha
      obtain ⟨q, hq⟩ := hT a ha
      refine Subgroup.mem_comap.mpr ⟨?_, ⟨a, rfl⟩⟩
      rw [← hq]
      exact hψS ⟨q, rfl⟩
    have heq := T.is_maximal' hI'p hle
    obtain ⟨a, ha⟩ : ∃ a, MulAut.conj a = i := hi.2
    refine ⟨a, ?_, ha.symm⟩
    have : a ∈ ((S : Subgroup (MulAut K)) ⊓ inner K).comap (MulAut.conj : K →* MulAut K) :=
      Subgroup.mem_comap.mpr (ha ▸ hi)
    rw [heq] at this
    exact this
  have hRp : IsPGroup p R := hSp.to_le hRS
  have hRc : IsCyclic R := by
    by_contra hRc
    obtain ⟨V, hVR, -, hVcard, hVexp, hVcomm⟩ :=
      CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le hp hp2 (T := R) (R := R) hRp le_rfl
        Subgroup.le_normalizer hRc
    let φ : R →* Outer K := (QuotientGroup.mk' (inner K)).comp R.subtype
    have hφinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro r hr
      rw [MonoidHom.mem_ker] at hr
      have h1 : (r : MulAut K) ∈ inner K := (QuotientGroup.eq_one_iff _).mp hr
      have h2 : (r : MulAut K) ∈ R ⊓ inner K := ⟨r.2, h1⟩
      rw [hRinner, Subgroup.mem_bot] at h2
      exact Subgroup.mem_bot.mpr (Subtype.ext h2)
    have hVe : IsElemAbelian p V :=
      (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff).2 ⟨hVcomm, hVexp⟩
    have hV'e : IsElemAbelian p ((V.subgroupOf R).map φ) := (hVe.subgroupOf R).map φ
    have hV'card : Nat.card ((V.subgroupOf R).map φ) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective hφinj, Nat.card_congr (subgroupOfEquivOfLe hVR).toEquiv,
        hVcard]
    have h2 := CFSG.GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt
      (le_top : (V.subgroupOf R).map φ ≤ ⊤) hV'e hV'card
    have h3 := (h7131 p hp hp2 K hsimple hnonab hcat hrank).1
    omega
  refine ⟨R, hRc, hRinner, fun q => ?_⟩
  have hqS : ψ q ∈ (S : Subgroup (MulAut K)) := hψS ⟨q, rfl⟩
  rw [← hsup] at hqS
  have hRN : R ≤ normalizer (((S : Subgroup (MulAut K)) ⊓ inner K : Subgroup (MulAut K)) :
      Set (MulAut K)) := by
    intro r hr
    refine CFSG.Goldschmidt.Sec82.mem_normalizer_of_conj_mem fun v hv => ?_
    have hrS : r ∈ (S : Subgroup (MulAut K)) := hRS hr
    exact ⟨(S : Subgroup (MulAut K)).mul_mem
      ((S : Subgroup (MulAut K)).mul_mem hrS hv.1) ((S : Subgroup (MulAut K)).inv_mem hrS),
      (CFSG.ComponentClassification.OuterAutomorphisms.inner_normal K).conj_mem v hv.2 r⟩
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ R hRN] at hqS
  obtain ⟨i, hi, r, hr, hir⟩ := Set.mem_mul.mp hqS
  obtain ⟨a, haT, rfl⟩ := hI i hi
  exact ⟨a, haT, r, hr, hir.symm⟩

end Local

end K62BSplit

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
