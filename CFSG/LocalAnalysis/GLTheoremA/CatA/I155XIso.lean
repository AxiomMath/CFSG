module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I155XAct
public import CFSG.LocalAnalysis.GLTheoremA.S10.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I155X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_pSimple_equiv_compat {p : ℕ} (hp : p.Prime) {H J : Subgroup G}
    (hJ : GLAPComponent p H J) {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hna : ∃ a b : T, a * b ≠ b * a) (hbot : GLAPPrimeCore p T = ⊥) (f : ↥J →* T)
    (hf : Function.Surjective f) :
    ∃ e : PSimple p J ≃* T, ∀ j : ↥J, e (QuotientGroup.mk (QuotientGroup.mk j)) = f j := by
  have hTz : Subgroup.center T = ⊥ :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hna
  have hTq : CFSG.Open.IsQuasisimple T :=
    CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_isQuasisimple_of_simple hna
  let eB : (T ⧸ GLAPPrimeCore p T) ≃* T :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hB : CFSG.Open.IsQuasisimple (T ⧸ GLAPPrimeCore p T) :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv eB.symm hTq
  haveI : IsSimpleGroup ((T ⧸ GLAPPrimeCore p T) ⧸ Subgroup.center (T ⧸ GLAPPrimeCore p T)) :=
    hB.2
  haveI : IsSimpleGroup (PSimple p J) := (isQuasisimple_pQuot_of_glaPComponent hp hJ).2
  have hinj : Function.Injective (pSimpleMapOfSurjective hp f hf) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (pSimpleMapOfSurjective hp f hf).ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := exists_pair_ne
        ((T ⧸ GLAPPrimeCore p T) ⧸ Subgroup.center (T ⧸ GLAPPrimeCore p T))
      obtain ⟨a', rfl⟩ := pSimpleMapOfSurjective_surjective hp f hf a
      obtain ⟨b', rfl⟩ := pSimpleMapOfSurjective_surjective hp f hf b
      apply hab
      have h1 : pSimpleMapOfSurjective hp f hf a' = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      have h2 : pSimpleMapOfSurjective hp f hf b' = 1 := by
        rw [← MonoidHom.mem_ker, h]
        trivial
      rw [h1, h2]
  let φ := MulEquiv.ofBijective (pSimpleMapOfSurjective hp f hf)
    ⟨hinj, pSimpleMapOfSurjective_surjective hp f hf⟩
  let e : PSimple p J ≃* T := φ.trans ((QuotientGroup.congr _ _ eB (Subgroup.map_center_eq eB)).trans
    ((QuotientGroup.quotientMulEquivOfEq hTz).trans QuotientGroup.quotientBot))
  refine ⟨e, fun j => ?_⟩
  have h1 : φ (QuotientGroup.mk (QuotientGroup.mk j)) = QuotientGroup.mk (QuotientGroup.mk (f j)) := rfl
  have h2 : e (QuotientGroup.mk (QuotientGroup.mk j)) =
      (QuotientGroup.quotientBot : (T ⧸ (⊥ : Subgroup T)) ≃* T)
        ((QuotientGroup.quotientMulEquivOfEq hTz)
          ((QuotientGroup.congr _ _ eB (Subgroup.map_center_eq eB))
            (φ (QuotientGroup.mk (QuotientGroup.mk j))))) := rfl
  rw [h2, h1]
  have h3 : (QuotientGroup.congr _ _ eB (Subgroup.map_center_eq eB))
      (QuotientGroup.mk (QuotientGroup.mk (f j))) = QuotientGroup.mk (eB (QuotientGroup.mk (f j))) :=
    QuotientGroup.congr_mk _ _ _ _ _
  rw [h3]
  have h4 : eB (QuotientGroup.mk (f j)) = f j := by
    show (QuotientGroup.quotientBot) ((QuotientGroup.quotientMulEquivOfEq hbot) (QuotientGroup.mk (f j))) = f j
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  rw [h4]
  rfl

theorem exists_iso_of_covering {p : ℕ} (hp : p.Prime) {H X K J : Subgroup G} {y : G}
    (hK : GLAPComponent p X K) (hJ : GLAPComponent p H J)
    (hJK : J ≤ K ⊔ centModSubgroup p K) (hKJ : K ≤ J ⊔ centModSubgroup p K)
    (hyK : y ∈ Subgroup.normalizer (K : Set G)) :
    ∃ e : PSimple p J ≃* PSimple p K, IsoPresAct p y J K e := by
  classical
  have hJN : J ≤ Subgroup.normalizer (K : Set G) := hJK.trans
    (sup_le Subgroup.le_normalizer fun m hm => (mem_centModSubgroup.1 hm).1)
  have hJR : actImage p K J = (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range := by
    apply le_antisymm (actImage_le_range hp hK hJK)
    intro t ht
    rw [← actImage_K_eq_range] at ht
    obtain ⟨c, hc, hct⟩ := (mem_actImage_iff Subgroup.le_normalizer).1 ht
    rw [← hct]
    obtain ⟨j, hj, m, hm, hcjm⟩ := mem_sup_centMod' hJN (hKJ hc)
    have hmN : m ∈ Subgroup.normalizer (K : Set G) := (mem_centModSubgroup.1 hm).1
    have hcj : act p K c = act p K j := by
      rw [hcjm, act_mul (hJN hj) hmN, act_eq_one_of_centMod hp hK hm, mul_one]
    rw [hcj]
    exact (mem_actImage_iff hJN).2 ⟨j, hj, rfl⟩
  have hJ_R : ∀ j ∈ J, act p K j ∈ (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range := by
    intro j hj
    rw [← hJR]
    exact (mem_actImage_iff hJN).2 ⟨j, hj, rfl⟩
  haveI := isSimpleGroup_range hp hK
  haveI : IsSimpleGroup (PSimple p K) := (chev_pSimple_simple_nonabelian hp hK).1
  let ψ0 : ↥J →* MulAut (PSimple p K) := (chevAut p K).comp (Subgroup.inclusion hJN)
  have hψ0 : ∀ j : ↥J, ψ0 j = act p K (j : G) := fun j => (act_of_mem (hJN j.2)).symm
  let ψ : ↥J →* (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range :=
    ψ0.codRestrict _ fun j => by
      rw [hψ0]
      exact hJ_R j j.2
  let eR := MonoidHom.ofInjective (conj_injective hp hK)
  let f : ↥J →* PSimple p K := (eR.symm : _ →* PSimple p K).comp ψ
  have hf_conj : ∀ j : ↥J, MulAut.conj (f j) = act p K (j : G) := by
    intro j
    have h1 : eR (f j) = ψ j := by
      show eR (eR.symm (ψ j)) = ψ j
      exact eR.apply_symm_apply _
    have h2 : ((eR (f j) : _) : MulAut (PSimple p K)) = MulAut.conj (f j) := rfl
    rw [← h2, h1]
    show ψ0 j = act p K j
    exact hψ0 j
  have hf_surj : Function.Surjective f := by
    intro t
    obtain ⟨j, hj, hjt⟩ := (mem_actImage_iff hJN).1
      (hJR ▸ (show MulAut.conj t ∈ (MulAut.conj : PSimple p K →* MulAut (PSimple p K)).range from
        ⟨t, rfl⟩))
    refine ⟨⟨j, hj⟩, ?_⟩
    apply conj_injective hp hK
    rw [hf_conj ⟨j, hj⟩]
    exact hjt
  have hna := (chev_pSimple_simple_nonabelian hp hK).2
  have hbot := glaPPrimeCore_pSimple_eq_bot hp hK
  obtain ⟨e, he⟩ := exists_pSimple_equiv_compat hp hJ hna hbot f hf_surj
  refine ⟨e, ?_⟩
  rintro s s' ⟨q, q', ⟨l₁, l₂, hl₁, hl₂, hl⟩, rfl, rfl⟩
  subst hl₁ hl₂
  obtain ⟨k, hk, hkt⟩ : ∃ k : G, ∃ hk : k ∈ K, chevQuotHom p K ⟨k, hk⟩ = f l₁ := by
    obtain ⟨c, hc⟩ := chevQuotHom_surjective p K (f l₁)
    exact ⟨c, c.2, hc⟩
  have hyk : y⁻¹ * k * y ∈ K := by
    have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hyK) k).1 hk
    simpa [mul_assoc] using this
  have hl1N : (l₁ : G) ∈ Subgroup.normalizer (K : Set G) := hJN l₁.2
  have hl2N : (l₂ : G) ∈ Subgroup.normalizer (K : Set G) := hJN l₂.2
  have hyinvN : y⁻¹ ∈ Subgroup.normalizer (K : Set G) := Subgroup.inv_mem _ hyK
  have hkN : k ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hk
  have hact_l1 : act p K (l₁ : G) = MulAut.conj (chevQuotHom p K ⟨k, hk⟩) := by
    rw [hkt, hf_conj l₁]
  have hconj_eq : MulAut.conj (f l₂) = MulAut.conj (chevQuotHom p K ⟨y⁻¹ * k * y, hyk⟩) := by
    rw [hf_conj l₂, ← act_of_mem_K hyk, hl, act_mul (Subgroup.mul_mem _ hyinvN hl1N) hyK,
      act_mul hyinvN hl1N, hact_l1, ← act_of_mem_K hk, act_mul (Subgroup.mul_mem _ hyinvN hkN) hyK,
      act_mul hyinvN hkN]
  have hf2 : f l₂ = chevQuotHom p K ⟨y⁻¹ * k * y, hyk⟩ := by
    have := (conj_injective hp hK) hconj_eq
    exact this
  refine ⟨QuotientGroup.mk ⟨k, hk⟩, QuotientGroup.mk ⟨y⁻¹ * k * y, hyk⟩,
    ⟨⟨k, hk⟩, ⟨y⁻¹ * k * y, hyk⟩, rfl, rfl, rfl⟩, ?_, ?_⟩
  · rw [he l₁, ← hkt]
    rfl
  · rw [he l₂, hf2]
    rfl

end CFSG.LocalAnalysis.GLTheoremA.I155X
