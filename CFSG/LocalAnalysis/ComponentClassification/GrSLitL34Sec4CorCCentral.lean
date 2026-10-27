module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCSetup

public section

namespace CFSG.ComponentClassification.GSThmB.CorC

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_wCore {E : Subgroup X} {b : X} (hbE : ∀ e ∈ E, e * b = b * e) :
    b ∈ normalizer (wCore E : Set X) := by
  have hbN : ∀ e ∈ E, b ∈ normalizer (((pPrimeCore 2 (centralizer ({e} : Set X))).map
      (centralizer ({e} : Set X)).subtype : Subgroup X) : Set X) := fun e he =>
    UnbalancedGS.normalizer_le_normalizer_map_of_characteristic (centralizer ({e} : Set X))
      (pPrimeCore 2 (centralizer ({e} : Set X)))
      (le_normalizer (mem_centralizer_singleton_iff.mpr (hbE e he).symm))
  rw [mem_normalizer_iff]
  intro w
  simp only [wCore, mem_iInf]
  exact ⟨fun hw e he he1 => (mem_normalizer_iff.mp (hbN e he) w).mp (hw e he he1),
    fun hw e he he1 => (mem_normalizer_iff.mp (hbN e he) w).mpr (hw e he he1)⟩

theorem commutator_eq_of_simple {C K D : Subgroup X} (hKC : K ≤ C)
    (hK : IsPComponent 2 (K.subgroupOf C)) (hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K))
    (hD : D ≤ normalizer (K : Set X)) (hnot : ¬ ⁅K, D⁆ ≤ (pPrimeCore 2 K).map K.subtype) :
    ⁅K, D⁆ = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := ⁅K, D⁆ with hNdef
  have hNK : N ≤ K := GrSLit.GrS5.commutator_le_of_le_normalizer hD
  have hNn : (N.subgroupOf K).Normal := GrSLit.GrS5.commutator_subgroupOf_normal hD
  let π := QuotientGroup.mk' (pPrimeCore 2 K)
  have himgn : ((N.subgroupOf K).map π).Normal := hNn.map π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf K).map π) with hbot | htop
  · exfalso
    apply hnot
    intro y hy
    have hy' : (⟨y, hNK hy⟩ : K) ∈ N.subgroupOf K := hy
    have h1 : π ⟨y, hNK hy⟩ ∈ (N.subgroupOf K).map π := mem_map_of_mem π hy'
    rw [hbot, mem_bot] at h1
    exact ⟨⟨y, hNK hy⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩
  · have hperf : Group.IsPerfect K := by
      have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hK
      exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKC).toMonoidHom)
        (subgroupOfEquivOfLe hKC).surjective
    refine GrSLit.GrS5.eq_of_pPrimeCore_sup_eq hNK hNn hperf ?_
    apply le_antisymm (sup_le (map_subtype_le _) hNK)
    intro k hk
    have h1 : π ⟨k, hk⟩ ∈ (N.subgroupOf K).map π := by
      rw [htop]
      exact mem_top _
    obtain ⟨n, hn, hnk⟩ := h1
    have h2 : n⁻¹ * ⟨k, hk⟩ ∈ pPrimeCore 2 K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      change (π n)⁻¹ * π ⟨k, hk⟩ = 1
      rw [hnk, inv_mul_cancel]
    have hk' : k = (n : X) * ((n⁻¹ * ⟨k, hk⟩ : K) : X) := by simp
    rw [hk']
    exact mul_mem (mem_sup_right (mem_subgroupOf.mp hn)) (mem_sup_left ⟨_, h2, rfl⟩)

theorem not_le_coreActionKernel {a : X} {J E : Subgroup X} (h : Config a J E) {b : X}
    (hb : orderOf b = 2) (hab : a * b = b * a) (hbJ : b ∈ normalizer (J : Set X))
    (hJb : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    (hbE : ∀ e ∈ E, e * b = b * e) :
    ¬ centralizer ({a} : Set X) ⊓ wCore E ⊓ centralizer ({b} : Set X) ≤ coreActionKernel J := by
  set F := centralizer ({a} : Set X) ⊓ wCore E with hFdef
  have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  have hFodd : Odd (Nat.card F) := h.odd_card_wCore.of_dvd_nat (card_dvd_of_le inf_le_right)
  have hFN : F ≤ normalizer (J : Set X) := h.le_normalizer
  have hbF : b ∈ normalizer (F : Set X) :=
    normalizer_inf_mem (le_normalizer (mem_centralizer_singleton_iff.mpr hab.symm))
      (mem_normalizer_wCore hbE)
  have hbQ : b ∈ coreActionKernel J := mem_coreActionKernel.mpr ⟨hbJ, hJb⟩
  have hQN := normalizer_le_normalizer_coreActionKernel J
  have hcommQ : ∀ f ∈ F, f⁻¹ * b⁻¹ * f * b ∈ coreActionKernel J := by
    intro f hf
    exact mul_mem (conj_mem_coreActionKernel (hFN hf) (inv_mem hbQ)) hbQ
  intro hle
  have hFQ := le_of_inf_centralizer_le hbb hFodd hbF (le_normalizer hbQ)
    (fun f hf => hQN (hFN hf)) hcommQ hle
  apply h.not_le_oddIn
  calc J = ⁅J, F⁆ := h.commutator_eq.symm
    _ ≤ (pPrimeCore 2 J).map J.subtype := by
      rw [commutator_le]
      intro j hj f hf
      have h1 := (mem_coreActionKernel.mp (hFQ (inv_mem hf))).2 j⁻¹ (inv_mem hj)
      rw [commutatorElement_def]
      simpa only [inv_inv] using h1

theorem config_of_isoCorr (hSol : GrSLit.SolomonCommutingCoreInput) {a : X} {J E : Subgroup X}
    (h : Config a J E) {b : X} (hb : orderOf b = 2)
    (hbJ : ∀ j ∈ J, j⁻¹ * b⁻¹ * j * b ∈ (pPrimeCore 2 J).map J.subtype)
    (hbE : ∀ e ∈ E, e * b = b * e) {K : Subgroup X} (hK : UnbalancedGS.GSIsoCorr a J b K) :
    Config b K E := by
  obtain ⟨hAN, -, -, -, ⟨e₁, -⟩, ⟨e₂, -⟩, -, hset, -⟩ :=
    isomorphic_correspondence_sylow_growth hK rfl rfl rfl rfl
  obtain ⟨⟨-, -, hab, -, -, hKb, hKc, hbN, -, -⟩, -, -⟩ := hK
  obtain ⟨e7⟩ := h.equiv
  have eK : K ⧸ pPrimeCore 2 K ≃* alternatingGroup (Fin 7) := (e₂.symm.trans e₁).trans e7
  have hs : IsSimpleGroup (K ⧸ pPrimeCore 2 K) :=
    @MulEquiv.isSimpleGroup _ _ _ _
      (alternatingGroup.isSimpleGroup (by norm_num : 5 ≤ Nat.card (Fin 7))) eK
  have hEb : E ≤ centralizer ({b} : Set X) := fun e he =>
    mem_centralizer_singleton_iff.mpr (hbE e he)
  have hEA : E ≤ centralizer ({b} : Set X) ⊓ normalizer (J : Set X) :=
    le_inf hEb fun e he => (mem_inf.mp (h.le_H he)).2
  obtain ⟨e₀, he₀E, he₀1, he₀⟩ := h.exists_involution
  have hD : centralizer ({b} : Set X) ⊓ wCore E ≤ normalizer (K : Set X) := by
    have h1 := ((GrSLit.GrS5.solomon_involutions hSol he₀ hb (hbE e₀ he₀E)).2 K hKb hKc).1
    exact fun d hd => h1 (mem_inf.mpr ⟨wCore_le he₀E he₀1 (mem_inf.mp hd).2, (mem_inf.mp hd).1⟩)
  have hnot : ¬ ⁅K, centralizer ({b} : Set X) ⊓ wCore E⁆ ≤ (pPrimeCore 2 K).map K.subtype := by
    intro hle
    apply not_le_coreActionKernel h hb hab hbN hbJ hbE
    intro e he
    obtain ⟨heF, heb⟩ := mem_inf.mp he
    have heA : e ∈ centralizer ({b} : Set X) ⊓ normalizer (J : Set X) :=
      mem_inf.mpr ⟨heb, h.le_normalizer heF⟩
    have heK : ∀ l ∈ K, l⁻¹ * e⁻¹ * l * e ∈ (pPrimeCore 2 K).map K.subtype := by
      intro l hl
      have h1 : ⁅l⁻¹, e⁻¹⁆ ∈ ⁅K, centralizer ({b} : Set X) ⊓ wCore E⁆ :=
        commutator_mem_commutator (inv_mem hl) (inv_mem (mem_inf.mpr ⟨heb, (mem_inf.mp heF).2⟩))
      have h2 := hle h1
      rwa [commutatorElement_def, inv_inv, inv_inv] at h2
    have h1 : e ∈ {g | g ∈ centralizer ({b} : Set X) ⊓ normalizer (J : Set X) ∧
        ∀ l ∈ K, l⁻¹ * g⁻¹ * l * g ∈ (pPrimeCore 2 K).map K.subtype} := ⟨heA, heK⟩
    rw [← hset] at h1
    exact mem_coreActionKernel.mpr ⟨(mem_inf.mp heA).2, h1.2⟩
  exact ⟨hb, hKb, hKc, ⟨eK⟩, le_inf hEb fun e he => hAN (hEA he), h.four,
    commutator_eq_of_simple hKb hKc hs hD hnot⟩

end CFSG.ComponentClassification.GSThmB.CorC
