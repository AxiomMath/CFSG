module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDCls3

public section

namespace CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.AppC

theorem conj_swap_of' : ∀ σ ∈ Dset, σ ∉ Eset →
    σ⁻¹ * swap 0 1 * σ = swap 2 3 ∧ σ⁻¹ * swap 2 3 * σ = swap 0 1 := by
  decide +kernel

theorem exists_dset_not_eset : ∃ σ ∈ Dset, σ ∉ Eset :=
  ⟨swap 0 2 * swap 1 3, by decide +kernel, by decide +kernel⟩

variable {G : Type} [Group G] [Finite G]

namespace GCfg

variable {T M H S L : Subgroup G} (C : GCfg T M H S L)
include C

theorem exists_r : ∃ r ∈ S, r ∉ baum S := by
  obtain ⟨σ, hσD, hσE⟩ := exists_dset_not_eset
  have hσ : σ ∈ C.P.im S := by rw [C.hS]; exact (mem_Dstd σ).2 hσD
  obtain ⟨r, hrS, hrσ⟩ := (C.P.mem_im_pf le_rfl).1 hσ
  refine ⟨r, hrS, fun hrB => hσE ?_⟩
  have : C.P.pf r ∈ C.P.im (baum S) :=
    (C.P.mem_im_pf (inf_le_left)).2 ⟨r, hrB, rfl⟩
  rw [C.hB, hrσ] at this
  exact (mem_Estd σ).1 this

theorem mem_im_conj_inv {r : G} (hrS : r ∈ S) {A : Subgroup G} (hAS : A ≤ S)
    {g : Perm (Fin 5)} :
    g ∈ C.P.im (conjSubgroup A r⁻¹) ↔ (C.P.pf r)⁻¹ * g * C.P.pf r ∈ C.P.im A := by
  have hrN : r ∈ S := hrS
  have hrNS : r⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem (Subgroup.le_normalizer hrS)
  have hA'S : conjSubgroup A r⁻¹ ≤ S := by
    have := C5.conjSubgroup_mono hAS r⁻¹
    rwa [C5.conjSubgroup_eq_self hrNS] at this
  have hAN : A ≤ S := hAS
  have hA'N : conjSubgroup A r⁻¹ ≤ S := hA'S
  constructor
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (C.P.mem_im_pf hA'N).1 hg
    have hy' : r⁻¹ * y * r ∈ A := by
      have := mem_conjSubgroup_iff.1 hy
      simpa using this
    have hyN : y ∈ S := hA'N hy
    have hb : C.P.pf (r⁻¹ * y * r) = (C.P.pf r)⁻¹ * C.P.pf y * C.P.pf r := by
      rw [C.P.pf_mul (mul_mem (inv_mem hrN) hyN) hrN, C.P.pf_mul (inv_mem hrN) hyN,
        C.P.pf_inv hrN]
    rw [← hb]
    exact (C.P.mem_im_pf hAN).2 ⟨_, hy', rfl⟩
  · intro hg
    obtain ⟨b, hbA, hbp⟩ := (C.P.mem_im_pf hAN).1 hg
    have hbN : b ∈ S := hAN hbA
    refine (C.P.mem_im_pf hA'N).2 ⟨r * b * r⁻¹, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have : r⁻¹ * (r * b * r⁻¹) * r⁻¹⁻¹ = b := by group
      rw [this]; exact hbA
    · rw [C.P.pf_mul (mul_mem hrN hbN) (inv_mem hrN), C.P.pf_mul hrN hbN, C.P.pf_inv hrN, hbp]
      group

end GCfg

namespace GMate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : GCfg T M H S L) (m : GMate S T M₀ x)
include C m

theorem pf_r' {r : G} (hrS : r ∈ S) (hrB : r ∉ baum S) :
    (C.P.pf r)⁻¹ * swap 0 1 * C.P.pf r = swap 2 3 ∧
      (C.P.pf r)⁻¹ * swap 2 3 * C.P.pf r = swap 0 1 := by
  have hD : C.P.pf r ∈ Dset := by
    have : C.P.pf r ∈ C.P.im S := (C.P.mem_im_pf le_rfl).2 ⟨r, hrS, rfl⟩
    rw [C.hS] at this
    exact (mem_Dstd _).1 this
  have hnE : C.P.pf r ∉ Eset := fun h => hrB (m.mem_B_of_pf C hrS h)
  exact conj_swap_of' _ hD hnE

theorem a5_members {r v : G} (hrS : r ∈ S) (hrB : r ∉ baum S) (hv : v ∈ conjR (C.U) x)
    (hπ : C.P.pf v = swap 0 1) (B' : Subgroup G) :
    IsMaxElemAbelian S B' ↔
      B' = pCoreOf 2 H ∨ B' = conjR (pCoreOf 2 H) x ∨ B' = GYv C.U (blockD S L) v ∨
        B' = conjR (GYv C.U (blockD S L) v) r := by
  obtain ⟨hYmax, -⟩ := m.Yv_isMax C hv hπ
  obtain ⟨hσ1, hσ2⟩ := m.pf_r' C hrS hrB
  constructor
  · intro hB'
    rcases m.type_cases C hB' with h | h | h | h
    · exact Or.inl (m.eq_Q_of_type_bot C hB' h)
    · exact Or.inr (Or.inr (Or.inl (m.eq_Yv_of_type_t1 C hB' h hv hπ)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      have hrNS : r⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem (Subgroup.le_normalizer hrS)
      have hA' : IsMaxElemAbelian S (conjSubgroup B' r⁻¹) :=
        C56.isMaxElemAbelian_conjSubgroup hB' hrNS
      have hty' : ∀ g, g ∈ C.P.im (conjSubgroup B' r⁻¹) ↔ g = 1 ∨ g = swap 0 1 := by
        intro g
        rw [C.mem_im_conj_inv hrS hB'.1, h]
        constructor
        · rintro (h1 | h1)
          · left
            have : g = C.P.pf r * 1 * (C.P.pf r)⁻¹ := by
              calc g = C.P.pf r * ((C.P.pf r)⁻¹ * g * C.P.pf r) * (C.P.pf r)⁻¹ := by group
                _ = _ := by rw [h1]
            rw [this]; group
          · right
            have e2 : swap (0 : Fin 5) 1 = C.P.pf r * swap 2 3 * (C.P.pf r)⁻¹ := by
              rw [← hσ1]; group
            calc g = C.P.pf r * ((C.P.pf r)⁻¹ * g * C.P.pf r) * (C.P.pf r)⁻¹ := by group
              _ = _ := by rw [h1, ← e2]
        · rintro (h1 | h1)
          · left; rw [h1]; group
          · right
            rw [h1]; exact hσ1
      have heq := m.eq_Yv_of_type_t1 C hA' hty' hv hπ
      rw [C56.conjR_eq, ← heq]
      exact (C5.conjSubgroup_inv_conjSubgroup B' r).symm
    · exact Or.inr (Or.inl ((m.eq_VD_of_type_E C hB' h).trans (m.Qx_eq C).symm))
  · intro hB'
    rcases hB' with rfl | rfl | rfl | rfl
    · exact m.Q_isMax C
    · exact m.Qx_isMax C
    · exact hYmax
    · exact C56.isMaxElemAbelian_conjSubgroup hYmax (Subgroup.le_normalizer hrS)

theorem a5_classification {r : G} (hrS : r ∈ S) (hrB : r ∉ baum S) :
    ∃ A : Subgroup G, (A ⊓ pCoreOf 2 H).relIndex A = 2 ∧
      ∀ B' : Subgroup G, IsMaxElemAbelian S B' ↔
        B' = pCoreOf 2 H ∨ B' = conjR (pCoreOf 2 H) x ∨ B' = A ∨ B' = conjR A r := by
  have hVN : conjR (C.U) x ≤ S := (m.V_le_S C)
  have ht1 : swap (0 : Fin 5) 1 ∈ C.P.im (conjR C.U x) := by
    rw [m.im_V C]; exact (mem_Estd _).2 t1_mem_Eset
  obtain ⟨v, hv, hπ⟩ := (C.P.mem_im_pf hVN).1 ht1
  exact ⟨GYv C.U (blockD S L) v, (m.Yv_isMax C hv hπ).2, m.a5_members C hrS hrB hv hπ⟩

theorem invariant_members {A : Subgroup G} (hA : IsMaxElemAbelian S A)
    (hinv : ∀ s ∈ S, conjSubgroup A s = A) :
    A = pCoreOf 2 H ∨ A = conjR (pCoreOf 2 H) x := by
  obtain ⟨r, hrS, hrB⟩ := C.exists_r
  obtain ⟨hσ1, hσ2⟩ := m.pf_r' C hrS hrB
  have hAN : A ≤ S := hA.1
  have hconj : ∀ g, g ∈ C.P.im A ↔ (C.P.pf r)⁻¹ * g * C.P.pf r ∈ C.P.im A := fun g => by
    have := C.mem_im_conj_inv hrS hA.1 (g := g)
    rwa [hinv r⁻¹ (inv_mem hrS)] at this
  rcases m.type_cases C hA with h | h | h | h
  · exact Or.inl (m.eq_Q_of_type_bot C hA h)
  ·
    exfalso
    have ht1 : swap (0 : Fin 5) 1 ∈ C.P.im A := (h _).2 (Or.inr rfl)
    have := (hconj (swap 0 1)).1 ht1
    rw [hσ1] at this
    rcases (h _).1 this with h' | h'
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
  · exfalso
    have ht2 : swap (2 : Fin 5) 3 ∈ C.P.im A := (h _).2 (Or.inr rfl)
    have := (hconj (swap 2 3)).1 ht2
    rw [hσ2] at this
    rcases (h _).1 this with h' | h'
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
  · exact Or.inr ((m.eq_VD_of_type_E C hA h).trans (m.Qx_eq C).symm)

theorem normT_le : normT T S ≤ M₀ := by
  have hHP : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have h244 : ∀ y, y ∈ T → y ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) → y ∈ S := fun y hyT hyN => by
    have e := lemma244 G T M H S L C.hcs (pCoreOf 2 H) (C56.pCoreOf_ne_bot C.hcs) C.hQS hHP
    have : y ∈ T ⊓ Subgroup.normalizer (pCoreOf 2 H : Set G) := ⟨hyT, hyN⟩
    rwa [e] at this
  intro σ hσ
  have hσT : σ ∈ T := hσ.1
  have hσN : σ ∈ Subgroup.normalizer (S : Set G) := hσ.2
  have hQ' := C56.isMaxElemAbelian_conjSubgroup (m.Q_isMax C) hσN
  have hinv : ∀ s ∈ S, conjSubgroup (conjSubgroup (pCoreOf 2 H) σ) s =
      conjSubgroup (pCoreOf 2 H) σ := by
    intro s hs
    rw [conjSubgroup_conjSubgroup]
    have hs' : σ * s * σ⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hσN s).1 hs
    have e : σ * s = (σ * s * σ⁻¹) * σ := by group
    rw [e, ← conjSubgroup_conjSubgroup,
      C5.conjSubgroup_eq_self (hHP (C.hSH hs'))]
  rcases m.invariant_members C hQ' hinv with h | h
  · exact m.hSM (h244 σ hσT (conjSubgroup_eq_iff_mem_normalizer.mp h))
  · rw [C56.conjR_eq] at h
    have h' : conjSubgroup (pCoreOf 2 H) (σ * x⁻¹) = pCoreOf 2 H := by
      rw [← conjSubgroup_conjSubgroup, h, conjSubgroup_conjSubgroup, mul_inv_cancel,
        conjSubgroup_one]
    have hσx : σ * x⁻¹ ∈ S :=
      h244 _ (mul_mem hσT (inv_mem (m.hMT m.hx))) (conjSubgroup_eq_iff_mem_normalizer.mp h')
    have e : σ = (σ * x⁻¹) * x := by group
    rw [e]
    exact mul_mem (m.hSM hσx) m.hx

theorem normT_eq : normT T S = M₀ :=
  le_antisymm (m.normT_le C) fun _ hm' => ⟨m.hMT hm', normalizer_of_relIndex_two m.hSM m.h2 hm'⟩

end GMate

end CFSG.QuasithinUnique.AppD
