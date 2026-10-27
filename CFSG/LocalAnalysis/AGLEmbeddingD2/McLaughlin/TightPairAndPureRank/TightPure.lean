module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.T2Group
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPhaseThree

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Quasithin
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank CFSG.RankThreeCoreUniqueness.Helpers

open scoped commutatorElement

section Invariance

variable {G : Type} [Group G]

theorem le_normalizer_commutator_of_actions {N L T : Subgroup G}
    (hL : L ≤ Subgroup.normalizer (N : Set G)) (hT : T ≤ Subgroup.normalizer (N : Set G))
    (hTL : (actHom N T hT).range ≤ Subgroup.normalizer ((actHom N L hL).range : Set (MulAut ↥N))) :
    T ≤ Subgroup.normalizer ((⁅N, L⁆ : Subgroup G) : Set G) := by
  refine le_normalizer_of_forall_map_conj_le fun s hs => ?_
  rw [Subgroup.map_le_iff_le_comap, Subgroup.commutator_le]
  intro n hn a ha
  have hsN : (s * n * s⁻¹ : G) ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (hT hs) n).mp hn
    exact this
  have hmem : actHom N T hT ⟨s, hs⟩ * actHom N L hL ⟨a, ha⟩ * (actHom N T hT ⟨s, hs⟩)⁻¹ ∈
      (actHom N L hL).range := by
    have := hTL ⟨⟨s, hs⟩, rfl⟩
    have h2 := Subgroup.mem_normalizer_iff.mp this (actHom N L hL ⟨a, ha⟩)
    exact h2.mp ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨⟨a', ha'⟩, hae⟩ := hmem
  have hinv : ∀ m : ↥N, (((actHom N T hT ⟨s, hs⟩)⁻¹ m : ↥N) : G) = s⁻¹ * m * s := by
    intro m
    have h1 : actHom N T hT ⟨s, hs⟩ ((actHom N T hT ⟨s, hs⟩)⁻¹ m) = m := by simp
    have h2 := congrArg (fun x : ↥N => (x : G)) h1
    simp only [actHom_apply_coe] at h2
    calc (((actHom N T hT ⟨s, hs⟩)⁻¹ m : ↥N) : G)
        = s⁻¹ * (s * (((actHom N T hT ⟨s, hs⟩)⁻¹ m : ↥N) : G) * s⁻¹) * s := by group
      _ = s⁻¹ * m * s := by rw [h2]
  have hact : ∀ m : ↥N, a' * (m : G) * a'⁻¹ = s * (a * (s⁻¹ * (m : G) * s) * a⁻¹) * s⁻¹ := by
    intro m
    have := congrArg (fun φ : MulAut ↥N => ((φ m : ↥N) : G)) hae
    simp only [actHom_apply_coe, MulAut.mul_apply] at this
    rw [this, hinv]
  have key := hact ⟨(s * n * s⁻¹)⁻¹, N.inv_mem hsN⟩
  have h3 : a' * (s * n * s⁻¹)⁻¹ * a'⁻¹ = s * (a * n⁻¹ * a⁻¹) * s⁻¹ := by
    rw [show ((⟨(s * n * s⁻¹)⁻¹, N.inv_mem hsN⟩ : ↥N) : G) = (s * n * s⁻¹)⁻¹ from rfl] at key
    rw [key]; group
  have e : s * ⁅n, a⁆ * s⁻¹ = ⁅s * n * s⁻¹, a'⁆ := by
    simp only [commutatorElement_def]
    calc s * (n * a * n⁻¹ * a⁻¹) * s⁻¹
        = (s * n * s⁻¹) * (s * (a * n⁻¹ * a⁻¹) * s⁻¹) := by group
      _ = (s * n * s⁻¹) * (a' * (s * n * s⁻¹)⁻¹ * a'⁻¹) := by rw [h3]
      _ = _ := by group
  rw [Subgroup.mem_comap]
  show s * ⁅n, a⁆ * s⁻¹ ∈ _
  rw [e]
  exact Subgroup.commutator_mem_commutator hsN ha'

end Invariance

section Pure

variable {G : Type} [Group G] [Finite G]

theorem exists_fixedVector_of_irreducibleQuotient (h86 : Asc81bEightSix)
    {P : Sylow 3 G} {M A H R : Subgroup G} (hctx : PairStrongCtx P M A H R) {L₁ L₂ : Subgroup G}
    (h₁ : IsWeakSBlock M (pCoreOf 2 H) L₁) (h₂ : IsWeakSBlock M (pCoreOf 2 H) L₂)
    (hne : barM M L₁ ≠ barM M L₂)
    (hZ₁ : ¬ 3 ∣ Nat.card (barM M L₁ ⊓
      Subgroup.centralizer (barM M L₁ : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hirr : HasIrreducibleCommutatorQuotient L₁ (vModule (pCoreOf 2 H) L₁ L₂)) :
    ∃ x ∈ Quasithin.omegaOneCenterOf (pCoreOf 2 H), x ≠ 1 ∧
      x ∈ ⁅vModule (pCoreOf 2 H) L₁ L₂, L₁⁆ ∧
      x ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      L₂ ≤ Subgroup.centralizer ({x} : Set G) ∧
      Open.pRank 3 (L₁ ⊓ Subgroup.centralizer ({x} : Set G)) + Open.pRank 3 L₂ ≤
        Open.pRank 3 (Subgroup.centralizer ({x} : Set G) ⊓ M) := by
  have hpr := hctx.pair
  set S := pCoreOf 2 H with hS
  set Q := pCoreOf 2 M with hQ
  set VM := Quasithin.omegaOneCenterOf Q with hVM
  set N := vModule S L₁ L₂ with hN
  have hVMe : IsElemAbelian 2 VM := CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf Q
  have hVMQ : VM ≤ Q := QuasithinUnique.Setup.omegaOneCenterOf_le _
  have hQS : Q ≤ S := hpr.twoCore_M_le
  have hSM : S ≤ M := hpr.twoCore_le
  have hMV : M ≤ Subgroup.normalizer (VM : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_of_characteristic_pCoreOf
      (QuasithinUnique.Setup.omegaOneCenterOf_le _)
      (QuasithinUnique.Setup.characteristic_omegaOneCenterOf _)
  have hVV : Quasithin.omegaOneCenterOf S ≤ VM := hpr.omegaOneCenter_le.1
  have hNV : N ≤ VM := vModule_le hVV (hSM.trans hMV) (h₁.le.trans hMV) (h₂.le.trans hMV)
  have hNQ : N ≤ Q := hNV.trans hVMQ
  have hNS : N ≤ S := hNQ.trans hQS
  have hcc : ∀ a ∈ VM, ∀ b ∈ VM, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVMe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hNe : IsElemAbelian 2 N :=
    ⟨⟨⟨fun a b => Subtype.ext (hcc a (hNV a.2) b (hNV b.2))⟩⟩, fun x hx => hVMe.2 x (hNV hx)⟩
  have hn₁ : L₁ ≤ Subgroup.normalizer (N : Set G) := normalizer_vModule_L₁ S L₁ L₂
  have hn₂ : L₂ ≤ Subgroup.normalizer (N : Set G) := normalizer_vModule_L₂ S L₁ L₂
  have hnS : S ≤ Subgroup.normalizer (N : Set G) := normalizer_vModule_S S L₁ L₂
  have hact := actHom_commute h₁ h₂ hne hNV hn₁ hn₂
  have hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, ∀ n ∈ N,
      a * (b * n * b⁻¹) * a⁻¹ = b * (a * n * a⁻¹) * b⁻¹ := by
    intro a ha b hb n hn
    have h := hact (actHom N L₁ hn₁ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩ (actHom N L₂ hn₂ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have h2 := congrArg (fun φ : MulAut ↥N => ((φ ⟨n, hn⟩ : ↥N) : G)) h
    simpa [actHom_apply_coe, MulAut.mul_apply] using h2
  have hcent := centralizes_commutator_of_irreducibleQuotient hNe hn₁ hn₂ hcomm
    h₁.perfect h₂.perfect hirr
  set U : Subgroup G := ⁅N, L₁⁆ with hU
  have hUN : U ≤ N := WeakBlockModuleData.commutator_le_of_le_normalizer hn₁
  have hUS : U ≤ S := hUN.trans hNS
  have hUne : U ≠ ⊥ := by
    intro h
    have h' : ⁅N, L₁⁆ = ⊥ := h
    exact hirr.1.ne (le_antisymm inf_le_left (by rw [h']; exact bot_le))
  have hSU : S ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_commutator_of_actions hn₁ hnS (actHom_S_le_normalizer hpr h86 h₁ hNV hnS hn₁)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hzU, hz1, hzC⟩ := exists_ne_one_mem_centralizer_of_pGroup (p := 2)
    (pCoreOf_isPGroup 2 H) hUS hSU hUne
  have hz2 : z ^ 2 = 1 := hVMe.2 z (hNV (hUN hzU))
  have hzV : z ∈ Quasithin.omegaOneCenterOf S :=
    Subgroup.subset_closure ⟨⟨hUS hzU, hzC⟩, hz2⟩
  have hL₂z : L₂ ≤ Subgroup.centralizer ({z} : Set G) := by
    intro b hb
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have := hcent b hb y hzU
    calc y * b = (b * y * b⁻¹) * b := by rw [this]
      _ = b * y := by group
  exact ⟨z, hzV, hz1, hzU, hzC, hL₂z,
    pRank_add_le_pRank_centralizer_of_fixedBlock h₁ h₂ hne hZ₁ hL₂z⟩

end Pure

end CFSG.AGLEmbeddingD2.McLaughlin
