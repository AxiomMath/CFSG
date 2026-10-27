module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.ActionOnSub
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTheoremZ

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Quasithin
  CFSG.RankThreeCoreUniqueness.Helpers

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {M H R : Subgroup G}

omit [Finite G] in
theorem pCore_centralizes_submodule {N : Subgroup G}
    (hNQ : N ≤ Quasithin.omegaOneCenterOf (pCoreOf 2 M)) :
    ∀ q ∈ pCoreOf 2 M, q ∈ Subgroup.centralizer (N : Set G) := by
  intro q hq n hn
  have hz : n ∈ Quasithin.centerOf (pCoreOf 2 M) :=
    ((Subgroup.closure_le _).mpr fun _ hx => hx.1 :
      Quasithin.omegaOneCenterOf (pCoreOf 2 M) ≤ Quasithin.centerOf (pCoreOf 2 M)) (hNQ hn)
  exact (Subgroup.mem_centralizer_iff.mp hz.2 q hq).symm

omit [Finite G] in
theorem normalizerMonoidHom_eq_one_of_mem_pCore {N : Subgroup G}
    (hNQ : N ≤ Quasithin.omegaOneCenterOf (pCoreOf 2 M)) (x : ↥(Subgroup.normalizer (N : Set G)))
    (hx : (x : G) ∈ pCoreOf 2 M) : N.normalizerMonoidHom x = 1 := by
  ext n
  rw [show (1 : MulAut ↥N) n = n from rfl]
  have := Subgroup.mem_centralizer_iff.mp (pCore_centralizes_submodule (M := M) hNQ _ hx) n n.2
  change (x : G) * n * (x : G)⁻¹ = n
  calc (x : G) * n * (x : G)⁻¹ = (n * (x : G)) * (x : G)⁻¹ := by rw [← this]
    _ = n := by group

theorem commutator_mem_pCoreOf {L₁ L₂ : Subgroup G}
    (hL₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (hL₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₁ ≠ barM M L₂) {a b : G} (ha : a ∈ L₁) (hb : b ∈ L₂) :
    a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 M := by
  have hcomp : ⁅barM M L₁, barM M L₂⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hL₁.component hL₂.component hne
  have hC : barM M L₁ ≤ Subgroup.centralizer (barM M L₂ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hcomp
  set aM : ↥M := ⟨a, hL₁.le ha⟩
  set bM : ↥M := ⟨b, hL₂.le hb⟩
  have haM : aM ∈ L₁.subgroupOf M := ha
  have hbM : bM ∈ L₂.subgroupOf M := hb
  have hab := Subgroup.mem_centralizer_iff.mp
    (hC (Subgroup.mem_map_of_mem (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) haM))
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M) bM) (Subgroup.mem_map_of_mem _ hbM)
  have h1 : (aM * bM * aM⁻¹ * bM⁻¹ : ↥M) ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (CFSG.pCore 2 ↥M) (aM * bM * aM⁻¹ * bM⁻¹) = 1
    simp only [map_mul, map_inv]
    rw [← hab]; group
  have h2 : (((aM * bM * aM⁻¹ * bM⁻¹ : ↥M)) : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype := ⟨_, h1, rfl⟩
  have e : (((aM * bM * aM⁻¹ * bM⁻¹ : ↥M)) : G) = a * b * a⁻¹ * b⁻¹ := rfl
  rw [← e]; exact h2

theorem actHom_commute {L₁ L₂ N : Subgroup G}
    (hL₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (hL₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₁ ≠ barM M L₂) (hNQ : N ≤ Quasithin.omegaOneCenterOf (pCoreOf 2 M))
    (hN₁ : L₁ ≤ Subgroup.normalizer (N : Set G)) (hN₂ : L₂ ≤ Subgroup.normalizer (N : Set G)) :
    ∀ x ∈ (actHom N L₁ hN₁).range, ∀ y ∈ (actHom N L₂ hN₂).range, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  have hc := commutator_mem_pCoreOf hL₁ hL₂ hne a.2 b.2
  set aN : ↥(Subgroup.normalizer (N : Set G)) := ⟨a, hN₁ a.2⟩ with haN
  set bN : ↥(Subgroup.normalizer (N : Set G)) := ⟨b, hN₂ b.2⟩ with hbN
  have e1 : actHom N L₁ hN₁ a = N.normalizerMonoidHom aN := rfl
  have e2 : actHom N L₂ hN₂ b = N.normalizerMonoidHom bN := rfl
  rw [e1, e2, ← map_mul, ← map_mul]
  have hcN : N.normalizerMonoidHom (aN * bN * aN⁻¹ * bN⁻¹) = 1 :=
    normalizerMonoidHom_eq_one_of_mem_pCore hNQ _ hc
  have : aN * bN = (aN * bN * aN⁻¹ * bN⁻¹) * (bN * aN) := by group
  rw [this, map_mul, hcN, one_mul]

theorem actHom_S_le_normalizer (h : AGLPair p M H R) (h86 : Asc81bEightSix) {L N : Subgroup G}
    (hL : IsWeakSBlock M (pCoreOf 2 H) L) (hNQ : N ≤ Quasithin.omegaOneCenterOf (pCoreOf 2 M))
    (hS : pCoreOf 2 H ≤ Subgroup.normalizer (N : Set G))
    (hLN : L ≤ Subgroup.normalizer (N : Set G)) :
    (actHom N (pCoreOf 2 H) hS).range ≤
      Subgroup.normalizer ((actHom N L hLN).range : Set (MulAut ↥N)) := by
  apply le_normalizer_of_forall_map_conj_le
  rintro _ ⟨s, rfl⟩ _ ⟨y, ⟨l, rfl⟩, rfl⟩
  set sM : ↥M := ⟨s, h.twoCore_le s.2⟩ with hsM
  set lM : ↥M := ⟨l, hL.le l.2⟩ with hlM
  have hsb : QuotientGroup.mk' (CFSG.pCore 2 ↥M) sM ∈ barM M (pCoreOf 2 H) :=
    ⟨sM, Subgroup.mem_subgroupOf.mpr s.2, rfl⟩
  have hnorm := h86 G M (pCoreOf 2 H) h.isKGroup.1 h.asc81bHyp (barM M L) hL.component hsb
  have hlL : lM ∈ L.subgroupOf M := l.2
  have h1 := (Subgroup.mem_normalizer_iff.mp hnorm (QuotientGroup.mk' (CFSG.pCore 2 ↥M) lM)).mp
    (Subgroup.mem_map_of_mem _ hlL)
  obtain ⟨l'', hl'', hl''e⟩ := h1
  have hq : (l''⁻¹ * (sM * lM * sM⁻¹) : ↥M) ∈ CFSG.pCore 2 ↥M := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (CFSG.pCore 2 ↥M) (l''⁻¹ * (sM * lM * sM⁻¹)) = 1
    simp only [map_mul, map_inv]
    rw [hl''e]; group
  have hqQ : (((l''⁻¹ * (sM * lM * sM⁻¹) : ↥M)) : G) ∈ pCoreOf 2 M := by
    have h2 : (((l''⁻¹ * (sM * lM * sM⁻¹) : ↥M)) : G) ∈ (CFSG.pCore 2 ↥M).map M.subtype :=
      ⟨_, hq, rfl⟩
    assumption
  have hl''L : (l'' : G) ∈ L := Subgroup.mem_subgroupOf.mp hl''
  set sN : ↥(Subgroup.normalizer (N : Set G)) := ⟨s, hS s.2⟩ with hsN
  set lN : ↥(Subgroup.normalizer (N : Set G)) := ⟨l, hLN l.2⟩ with hlN
  set l'N : ↥(Subgroup.normalizer (N : Set G)) := ⟨l'', hLN hl''L⟩ with hl'N
  set qN : ↥(Subgroup.normalizer (N : Set G)) := l'N⁻¹ * (sN * lN * sN⁻¹) with hqN
  have hqNc : (qN : G) = (((l''⁻¹ * (sM * lM * sM⁻¹) : ↥M)) : G) := by
    simp only [hqN, hl'N, hsN, hlN, hsM, hlM]; push_cast; rfl
  have hρq : N.normalizerMonoidHom qN = 1 :=
    normalizerMonoidHom_eq_one_of_mem_pCore hNQ qN (hqNc ▸ hqQ)
  have hprod : sN * lN * sN⁻¹ = l'N * qN := by simp [hqN]
  refine ⟨⟨l'', hl''L⟩, ?_⟩
  have e1 : actHom N L hLN ⟨l'', hl''L⟩ = N.normalizerMonoidHom l'N := rfl
  have e2 : actHom N (pCoreOf 2 H) hS s = N.normalizerMonoidHom sN := rfl
  have e3 : actHom N L hLN ⟨l, l.2⟩ = N.normalizerMonoidHom lN := rfl
  rw [e1]
  change N.normalizerMonoidHom l'N = (actHom N (pCoreOf 2 H) hS s) *
    actHom N L hLN l * (actHom N (pCoreOf 2 H) hS s)⁻¹
  rw [e2, show actHom N L hLN l = N.normalizerMonoidHom lN from rfl, ← map_inv, ← map_mul,
    ← map_mul, hprod, map_mul, hρq, mul_one]

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
