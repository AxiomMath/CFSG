module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Assembly
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData (IsChevTwo)
open scoped commutatorElement

section Setting

variable {G : Type} [Group G] [Finite G]
variable {m p : ℕ} {M D L : Subgroup G}

theorem isTwoPrimeCompOf_subgroupOf (h : IvSetting m p M D L) :
    IsTwoPrimeCompOf (L.subgroupOf M) := by
  have hLM : L ≤ M := h.hL.1
  refine ⟨?_, ?_, ?_⟩
  · exact CFSG.Open.IsSubnormal.top_iff.2
      ((CFSG.Open.IsSubnormal.iff_subgroupOf hLM).1 h.hL.2.1)
  · rw [← subgroupOf_commutator hLM hLM, glaPComponent_perfect h.hL]
  · exact isComponentOf_tl (prime_of_standing h.standing) (ne_two_of_standing h.standing)
      h.hyp h.hL h.hn h.hnc h.hQ

theorem centralizer_pCore_le (h : IvSetting m p M D L) :
    Subgroup.centralizer (↑(CFSG.pCore 2 ↥M) : Set ↥M) ≤ CFSG.pCore 2 ↥M := by
  intro x hx
  have h1 := charTwo_of_isTwoLocal h.standing h.hyp.twoLocal
  have hc : (x : G) ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro g ⟨y, hy, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hx y hy
    exact congrArg Subtype.val this
  exact (CFSG.mem_openPCoreOf_iff x).1 (h1 ⟨x.2, hc⟩)

private theorem descent_pCore_quotient_eq_bot {X : Type*} [Group X] (q : ℕ) :
    CFSG.pCore q (X ⧸ CFSG.pCore q X) = ⊥ := by
  let Q := CFSG.pCore q X
  let K := (CFSG.pCore q (X ⧸ Q)).comap (QuotientGroup.mk' Q)
  have hKn : K.Normal := CFSG.pCore_normal.comap _
  have hKp : IsPGroup q K := IsPGroup.comap_of_ker_isPGroup CFSG.pCore_isPGroup _
    (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup)
  have hKQ : K ≤ Q := le_sSup ⟨hKn, hKp⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Q x
  exact (QuotientGroup.eq_one_iff y).mpr (hKQ hx)

private theorem descent_pCoreOf_top_eq_bot {Y : Type*} [Group Y] {q : ℕ}
    (h : CFSG.pCore q Y = ⊥) : pCoreOf q (⊤ : Subgroup Y) = ⊥ := by
  have hmap := CFSG.pCore_map_iso q (Subgroup.topEquiv : ↥(⊤ : Subgroup Y) ≃* Y)
  rw [h] at hmap
  exact hmap

theorem pCore_tl_eq_bot (h : IvSetting m p M D L) : CFSG.pCore 2 ↥(tl M L) = ⊥ := by
  have hLM : L ≤ M := h.hL.1
  have hsub : CFSG.Open.IsSubnormal (tl M L) ⊤ := by
    have h1 : CFSG.Open.IsSubnormal (L.subgroupOf M) ⊤ :=
      CFSG.Open.IsSubnormal.top_iff.2 ((CFSG.Open.IsSubnormal.iff_subgroupOf hLM).1 h.hL.2.1)
    have h2 := h1.map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  have hq : CFSG.pCore 2 (Mt M) = ⊥ := descent_pCore_quotient_eq_bot (X := ↥M) 2
  have hle := CFSG.LocalAnalysis.GLTheoremB.pCoreOf_le_of_isSubnormal 2 hsub
  rw [descent_pCoreOf_top_eq_bot hq, le_bot_iff] at hle
  exact Subgroup.map_injective (tl M L).subtype_injective (by rw [Subgroup.map_bot]; exact hle)

theorem gammaD_descends (h : IvSetting m p M D L) :
    IsPGroup 2 ↥((gammaD D).subgroupOf M) ∧
      (gammaD D).subgroupOf M ≤ Subgroup.normalizer ((L.subgroupOf M : Subgroup ↥M) : Set ↥M) ∧
      CFSG.pCore 2 ↥M ≤ (gammaD D).subgroupOf M := by
  have hΓM : gammaD D ≤ M := gammaD_le h.hyp
  refine ⟨(isPGroup_gammaD D).of_injective (Subgroup.subgroupOfEquivOfLe hΓM).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hΓM).injective,
    fun x hx => ?_, fun x hx => ?_⟩
  · have hΓL := gammaD_le_normalizer (prime_of_standing h.standing) h.hyp h.hL h.hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := Subgroup.mem_normalizer_iff.1 (hΓL (Subgroup.mem_subgroupOf.1 hx)) (y : G)
    exact this
  · exact Subgroup.mem_subgroupOf.2 (h.hyp.clause_c ((CFSG.mem_openPCoreOf_iff x).2 hx))

theorem sigmaOf_descends (h : IvSetting m p M D L) :
    IsPGroup 2 ↥((sigmaOf D).subgroupOf M) ∧ CFSG.pCore 2 ↥M ≤ (sigmaOf D).subgroupOf M := by
  have hSM : sigmaOf D ≤ M := sigmaOf_le h.hyp
  have hS2 : IsPGroup 2 (sigmaOf D) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (sigmaStar D)
  refine ⟨hS2.of_injective (Subgroup.subgroupOfEquivOfLe hSM).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hSM).injective, fun x hx => ?_⟩
  exact Subgroup.mem_subgroupOf.2
    ((gammaD_le_sigmaOf D) (h.hyp.clause_c ((CFSG.mem_openPCoreOf_iff x).2 hx)))

private theorem descent_isCharIn_map {S : Subgroup G} {So : Subgroup ↥M} (hSM : S ≤ M)
    (hSo : IsCharIn So (S.subgroupOf M)) : IsCharIn (So.map M.subtype) S := by
  unfold IsCharIn at hSo ⊢
  refine ⟨?_, fun ψ x hx => ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hSo.1 hy
  · let ι : ↥(S.subgroupOf M) ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSM
    let ψ' : ↥(S.subgroupOf M) ≃* ↥(S.subgroupOf M) := ι.trans (ψ.trans ι.symm)
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hyx' : y = ((ι.symm x : ↥(S.subgroupOf M)) : ↥M) := Subtype.ext hyx
    have hmem : ((ι.symm x : ↥(S.subgroupOf M)) : ↥M) ∈ So := by
      rw [← hyx']
      exact hy
    have hψ := hSo.2 ψ' (ι.symm x) hmem
    exact Subgroup.mem_map.2 ⟨((ψ' (ι.symm x) : ↥(S.subgroupOf M)) : ↥M), hψ, rfl⟩

theorem not_concl28d (hcov : NotCovered M D L) (h : IvSetting m p M D L) {S : Subgroup G}
    (hS : S = gammaD D ∨ S = sigmaOf D) :
    ¬ Concl28d (L.subgroupOf M) (S.subgroupOf M) := by
  rintro ⟨So, hSo1, hSoch, hSoN⟩
  have hLM : L ≤ M := h.hL.1
  have hT₀ne : So.map M.subtype ≠ ⊥ := by
    intro hbot
    exact hSo1 (Subgroup.map_injective M.subtype_injective (by rw [hbot, Subgroup.map_bot]))
  have hLN : L ≤ Subgroup.normalizer ((So.map M.subtype : Subgroup G) : Set G) := by
    intro ℓ hℓ
    have hmem : (⟨ℓ, hLM hℓ⟩ : ↥M) ∈ L.subgroupOf M := Subgroup.mem_subgroupOf.2 hℓ
    exact Subgroup.le_normalizer_map (H := So) M.subtype
      (Subgroup.mem_map_of_mem M.subtype (hSoN hmem))
  have hcont : tl M L ≤ tl M (Subgroup.normalizer ((So.map M.subtype : Subgroup G) : Set G)) := by
    unfold tl
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono M hLN)
  have hchar : IsCharIn (So.map M.subtype) (gammaD D) ∨
      IsCharIn (So.map M.subtype) (sigmaOf D) := by
    rcases hS with rfl | rfl
    · exact Or.inl (descent_isCharIn_map (gammaD_le h.hyp) hSoch)
    · exact Or.inr (descent_isCharIn_map (sigmaOf_le h.hyp) hSoch)
  exact hcov _ hT₀ne hchar hcont

theorem input28_10_applied (hcov : NotCovered M D L) (h3 : Input28_10) (h : IvSetting m p M D L)
    {S : Subgroup G} (hS : S = gammaD D ∨ S = sigmaOf D)
    (hSN : S.subgroupOf M ≤ Subgroup.normalizer ((L.subgroupOf M : Subgroup ↥M) : Set ↥M))
    (hyp : Hyp28One (CFSG.pCore 2 ↥M) (L.subgroupOf M) (S.subgroupOf M) ∨
      Hyp28Two (CFSG.pCore 2 ↥M) (L.subgroupOf M) (S.subgroupOf M) ∨
      Hyp28Three (CFSG.pCore 2 ↥M) (L.subgroupOf M) (S.subgroupOf M) ∨
      Hyp28Four (CFSG.pCore 2 ↥M) (L.subgroupOf M) (S.subgroupOf M)) :
    Concl28a (CFSG.pCore 2 ↥M) (L.subgroupOf M) (S.subgroupOf M) ∨
      Concl28b (CFSG.pCore 2 ↥M) (L.subgroupOf M) (S.subgroupOf M) ∨
      Concl28c (CFSG.pCore 2 ↥M) (L.subgroupOf M) (S.subgroupOf M) := by
  have hSP : IsPGroup 2 ↥(S.subgroupOf M) := by
    rcases hS with rfl | rfl
    · exact (gammaD_descends h).1
    · exact (sigmaOf_descends h).1
  have hSW : CFSG.pCore 2 ↥M ≤ S.subgroupOf M := by
    rcases hS with rfl | rfl
    · exact (gammaD_descends h).2.2
    · exact (sigmaOf_descends h).2
  have hcon := h3 ↥M (CFSG.pCore 2 ↥M) (L.subgroupOf M) (S.subgroupOf M)
    CFSG.pCore_isPGroup (centralizer_pCore_le h) (isTwoPrimeCompOf_subgroupOf h)
    (pCore_tl_eq_bot h) hSP hSN hSW hyp
  rcases hcon with ha | hb | hc | hd
  · exact Or.inl ha
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hc)
  · exact absurd hd (not_concl28d hcov h hS)

end Setting

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
