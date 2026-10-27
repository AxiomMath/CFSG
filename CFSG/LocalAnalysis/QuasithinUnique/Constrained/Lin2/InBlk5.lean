module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2412g
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk1

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups commutatorElement

section Hyps

variable {G : Type} [Group G] {L : Subgroup G} {f : G}

theorem blockV_le :
    blockU L ⊓ Subgroup.centralizer ({f} : Set G) ≤ L ⊓ Subgroup.centralizer ({f} : Set G) :=
  inf_le_inf_right _ (blockU_le L)

theorem blockV_conj (hLU : ∀ ℓ ∈ L, ∀ u ∈ blockU L, ℓ * u * ℓ⁻¹ ∈ blockU L) :
    ∀ c ∈ L ⊓ Subgroup.centralizer ({f} : Set G),
      ∀ v ∈ blockU L ⊓ Subgroup.centralizer ({f} : Set G),
        c * v * c⁻¹ ∈ blockU L ⊓ Subgroup.centralizer ({f} : Set G) := by
  intro c hc v hv
  refine ⟨hLU c hc.1 v hv.1, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
  have hcc : Commute c f := Subgroup.mem_centralizer_singleton_iff.1 hc.2
  have hvc : Commute v f := Subgroup.mem_centralizer_singleton_iff.1 hv.2
  exact Commute.mul_left (Commute.mul_left hcc hvc) hcc.inv_left

theorem blockZf_le :
    blockZ L ⊓ Subgroup.centralizer ({f} : Set G) ≤ blockU L ⊓ Subgroup.centralizer ({f} : Set G) :=
  inf_le_inf_right _ (blockZ_le_blockU L)

theorem blockZf_comm : ∀ c ∈ L ⊓ Subgroup.centralizer ({f} : Set G),
    ∀ z ∈ blockZ L ⊓ Subgroup.centralizer ({f} : Set G), c * z = z * c :=
  fun c hc _ hz => Subgroup.mem_centralizer_iff.1 hz.1.2 c hc.1

theorem mem_blockV_iff (c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G))) :
    (c : G) ∈ blockU L ⊓ Subgroup.centralizer ({f} : Set G) ↔ (c : G) ∈ blockU L :=
  ⟨fun h => h.1, fun h => ⟨h, c.2.2⟩⟩

theorem mem_blockZf_iff (v : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G))) :
    (v : G) ∈ blockZ L ⊓ Subgroup.centralizer ({f} : Set G) ↔ (v : G) ∈ blockZ L :=
  ⟨fun h => h.1, fun h => ⟨h, v.2.2⟩⟩

theorem lin2_of_blockData {m : ℕ} (hm : 2 ≤ m) {F : Type} [Field F] [Fintype F]
    (hcard : Fintype.card F = 2 ^ m) (hF2 : (2 : F) = 0)
    (hVel : IsElemAbelian 2 (blockU L))
    (hLU : ∀ ℓ ∈ L, ∀ u ∈ blockU L, ℓ * u * ℓ⁻¹ ∈ blockU L)
    (hZW : blockZ L ⊓ Subgroup.centralizer ({f} : Set G) ≤
      ⁅blockU L ⊓ Subgroup.centralizer ({f} : Set G), L ⊓ Subgroup.centralizer ({f} : Set G)⁆)
    (α : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)) →* SL(2, F))
    (β : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G)) →* Multiplicative (Fin 2 → F))
    (hαs : Function.Surjective α) (hαk : ∀ c, α c = 1 ↔ (c : G) ∈ blockU L)
    (hβs : Function.Surjective β) (hβk : ∀ v, β v = 1 ↔ (v : G) ∈ blockZ L)
    (hβe : ∀ (c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)))
        (u v : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G))),
        (v : G) = c * u * c⁻¹ →
          Multiplicative.toAdd (β v) =
            (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) :
    IsShort2 (L ⊓ Subgroup.centralizer ({f} : Set G)) ∧
      IsLin2Type (L ⊓ Subgroup.centralizer ({f} : Set G)) m ∧
      blockU L ⊓ Subgroup.centralizer ({f} : Set G) =
        blockU (L ⊓ Subgroup.centralizer ({f} : Set G)) ∧
      pCoreOf 2 (L ⊓ Subgroup.centralizer ({f} : Set G)) =
        blockU L ⊓ Subgroup.centralizer ({f} : Set G) := by
  classical
  have hF : ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
    by_contra hcon
    have hall : ∀ a : F, a = 0 ∨ a = 1 := fun a => by
      by_contra h
      exact hcon ⟨a, fun h0 => h (Or.inl h0), fun h1 => h (Or.inr h1)⟩
    have h2 : Fintype.card F ≤ 2 := by
      calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
        _ ≤ ({0, 1} : Finset F).card := Finset.card_le_card fun a _ => by simpa using hall a
        _ ≤ 2 := Finset.card_le_two
    have h4 : 4 ≤ Fintype.card F := by
      rw [hcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  have hVel' : IsElemAbelian 2 (blockU L ⊓ Subgroup.centralizer ({f} : Set G)) :=
    IsElemAbelian.mono inf_le_left hVel
  have hVn := blockV_conj (f := f) hLU
  have hαk' : ∀ c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)),
      α c = 1 ↔ (c : G) ∈ blockU L ⊓ Subgroup.centralizer ({f} : Set G) := fun c => by
    rw [hαk, mem_blockV_iff]
  have hβk' : ∀ v : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G)),
      β v = 1 ↔ (v : G) ∈ blockZ L ⊓ Subgroup.centralizer ({f} : Set G) := fun v => by
    rw [hβk, mem_blockZf_iff]
  have hns : blockU L ⊓ Subgroup.centralizer ({f} : Set G) ≤
      ⁅blockU L ⊓ Subgroup.centralizer ({f} : Set G), L ⊓ Subgroup.centralizer ({f} : Set G)⁆ := by
    intro v hv
    obtain ⟨v', hv'W, hv'β⟩ := exists_mem_commutator_of_beta hF hVn α hαs β hβs hβe (β ⟨v, hv⟩)
    have hz : ((v'⁻¹ * ⟨v, hv⟩ : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G))) : G) ∈
        blockZ L ⊓ Subgroup.centralizer ({f} : Set G) := by
      rw [← hβk', map_mul, map_inv, hv'β, inv_mul_cancel]
    have h1 : (v'⁻¹ : G) * v ∈ ⁅blockU L ⊓ Subgroup.centralizer ({f} : Set G),
        L ⊓ Subgroup.centralizer ({f} : Set G)⁆ := hZW hz
    have h2 := Subgroup.mul_mem _ hv'W h1
    simpa using h2
  obtain ⟨hP, hU, -, hshort, hlin⟩ := lin2_of_data hm hcard hF2 (blockV_le (L := L) (f := f)) hVel'
    hVn α hαs hαk' β hβs (blockZf_le (L := L) (f := f)) (blockZf_comm (L := L) (f := f)) hβk' hβe
    hns
  exact ⟨hshort, hlin, hU.symm, hP⟩


theorem perm_of_blockData [Finite G] {F : Type} [Field F] [Fintype F]
    (hcard : Fintype.card F = 2) (hF2 : (2 : F) = 0) (hVel : IsElemAbelian 2 (blockU L))
    (hLU : ∀ ℓ ∈ L, ∀ u ∈ blockU L, ℓ * u * ℓ⁻¹ ∈ blockU L) (hZ : blockZ L = ⊥)
    (α : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)) →* SL(2, F))
    (β : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G)) →* Multiplicative (Fin 2 → F))
    (hαs : Function.Surjective α) (hαk : ∀ c, α c = 1 ↔ (c : G) ∈ blockU L)
    (hβs : Function.Surjective β) (hβk : ∀ v, β v = 1 ↔ (v : G) ∈ blockZ L)
    (hβe : ∀ (c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)))
        (u v : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G))),
        (v : G) = c * u * c⁻¹ →
          Multiplicative.toAdd (β v) =
            (α c : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u))) :
    Nonempty (↥(L ⊓ Subgroup.centralizer ({f} : Set G)) ≃* Equiv.Perm (Fin 4)) ∧
      pCoreOf 2 (L ⊓ Subgroup.centralizer ({f} : Set G)) =
        blockU L ⊓ Subgroup.centralizer ({f} : Set G) := by
  have hVel' : IsElemAbelian 2 (blockU L ⊓ Subgroup.centralizer ({f} : Set G)) :=
    IsElemAbelian.mono inf_le_left hVel
  have hVn := blockV_conj (f := f) hLU
  have hαk' : ∀ c : ↥(L ⊓ Subgroup.centralizer ({f} : Set G)),
      α c = 1 ↔ (c : G) ∈ blockU L ⊓ Subgroup.centralizer ({f} : Set G) := fun c => by
    rw [hαk, mem_blockV_iff]
  have hβi : ∀ v : ↥(blockU L ⊓ Subgroup.centralizer ({f} : Set G)), β v = 1 → v = 1 := by
    intro v hv
    have h1 : (v : G) ∈ blockZ L := (hβk v).1 hv
    rw [hZ, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  exact ⟨perm_four_of_data hcard hF2 (blockV_le (L := L) (f := f)) hVel' hVn α hαs hαk' β hβs hβi
      hβe,
    pCoreOf_eq_of_data hF2 (blockV_le (L := L) (f := f)) hVel' hVn α hαs hαk'⟩

end Hyps

section Block

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

theorem Lin2Cfg.block_facts (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D) :
    pCoreOf 2 L = blockU L ∧ IsElemAbelian 2 (blockU L) ∧
      ∀ ℓ ∈ L, ∀ u ∈ blockU L, ℓ * u * ℓ⁻¹ ∈ blockU L := by
  obtain ⟨-, ⟨hOL, -⟩, -, -, -, -, h7, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨x₀, hx₀T, hx₀S⟩ := hcfg.exists_mem_T_not_mem_S
  refine ⟨hOL, (h7 x₀ hx₀T hx₀S).1, ?_⟩
  intro ℓ hℓ u hu
  have hn : L ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := by
    rw [← hOL]
    exact CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L
  exact (Subgroup.mem_normalizer_iff.1 (hn hℓ) u).1 hu

theorem Lin2Cfg.exists_normData (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D)
    {B : Subgroup G} (hB : Lin2BProps T S (thompsonJ S) D B) {f : G}
    (hf : f ∈ S ⊓ Subgroup.normalizer (B : Set G)) (hf1 : f ≠ 1) (hff : f * f = 1) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (N : NormData L (thompsonJ S) n K f),
      (2 : K) = 0 ∧ N.σ ≠ 1 := by
  obtain ⟨hQL, -, -, hF3, hF4⟩ := complement_facts h8 hcfg hB
  obtain ⟨⟨-, -, hTnR⟩, ⟨hOL, hUQ⟩, ⟨-, hRsyl, -⟩, -⟩ := h8 G T M H S L D n hcfg
  obtain ⟨K, _, _, ⟨A⟩⟩ := exists_adapted hcfg.one_pos hcfg.lin2 hRsyl
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card hcfg.one_pos A.card_eq
  have hfS : f ∈ S := hf.1
  have hfL : ∀ x ∈ L, f * x * f⁻¹ ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hcfg.S_le_normalizer hfS) x).1 hx
  have hHU : H ≤ Subgroup.normalizer ((blockU L : Subgroup G) : Set G) := by
    rw [hUQ]; exact hcfg.H_le_normalizer_Q
  have hfU : ∀ x ∈ blockU L, f * x * f⁻¹ ∈ blockU L := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hHU (hcfg.S_le_H hfS)) x).1 hx
  have hfR : ∀ x ∈ thompsonJ S, f * x * f⁻¹ ∈ thompsonJ S := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (hTnR (hcfg.S_le_T hfS)) x).1 hx
  have hFp : IsPGroup 2 ((S ⊓ Subgroup.normalizer (B : Set G) : Subgroup G)) :=
    hcfg.S_isPGroup.to_le inf_le_left
  obtain ⟨A', σ, hσ, hσσ, hα, hβ⟩ := hcfg.exists_normalized hQL hFp
    (by rw [inf_comm]; exact hF3) hF4 A hOL hf hf1 hff hfL hfU hfR
  exact ⟨K, inferInstance, inferInstance, ⟨A', σ, hff, hfL, hfU, hσσ, hα, hβ⟩, hK2, hσ⟩

theorem Lin2Cfg.block_of_Zeq1 (h8 : Lemma2_4_8) (hcfg : Lin2Cfg G T M H S L n D)
    {B : Subgroup G} (hB : Lin2BProps T S (thompsonJ S) D B) (hc : centerOf L = ⊥) {f : G}
    (hf : f ∈ S ⊓ Subgroup.normalizer (B : Set G)) (hf1 : f ≠ 1) (hf2 : f ^ 2 = 1) :
    Lin2BlockConcl L f n := by
  have hff : f * f = 1 := by rw [← sq]; exact hf2
  obtain ⟨-, -, -, hTrU⟩ := counts_Zeq1 h8 hcfg hB hc hf hf1 hf2
  obtain ⟨hOL, hUel, hLU⟩ := hcfg.block_facts h8
  obtain ⟨K, _, _, N, hK2, hσ⟩ := hcfg.exists_normData h8 hB hf hf1 hff
  have hZL : blockZ L = ⊥ := by
    rw [blockZ_eq_centerOf hcfg.charTwo_L hOL]
    exact hc
  have hTrZ : ∀ x ∈ blockZ L, (f * x) * (f * x) = 1 → ∃ m ∈ blockZ L, m⁻¹ * f * m = f * x := by
    intro x hx _
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [hZL, Subgroup.mem_bot] at hx
    rw [hx]
    simp
  obtain ⟨m, F, _, _, α, β, hnm, hcard, hF2, hαs, hαk, hβs, hβk, hβe, -⟩ :=
    N.exists_data hK2 hOL hTrU hTrZ hσ
  by_cases hm : 2 ≤ m
  · left
    obtain ⟨hshort, hlin, hU, hP⟩ := lin2_of_blockData hm hcard hF2 hUel hLU
      (by rw [hZL, bot_inf_eq]; exact bot_le) α β hαs hαk hβs hβk hβe
    exact ⟨m, by omega, by omega, hshort, hlin, hU, hP⟩
  · right
    have hm1 : m = 1 := by
      have := hcfg.one_pos
      omega
    subst hm1
    have hcard' : Fintype.card F = 2 := by simpa using hcard
    obtain ⟨hperm, hP⟩ := perm_of_blockData hcard' hF2 hUel hLU hZL α β hαs hαk hβs hβk hβe
    exact ⟨by omega, Or.inl ⟨hc, hperm, hP⟩⟩

end Block

end CFSG.QuasithinUnique.Lin2
