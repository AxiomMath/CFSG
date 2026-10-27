module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ReindexCaseTwo

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin
open CFSG.RankThreeCoreUniqueness.Helpers

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : Type} [Group G] [Finite G] {S M : Subgroup G}

theorem theta_S_iff_mem_blockFix_AF_of_le (hA : Asc81bHyp M S)
    (θ : ↥M →* Perm (ι × Bool))
    (hker : ∀ m : ↥M, θ m = 1 → (m : G) ∈ S)
    (T : Finset ι)
    (hW : (((thompsonJ S).subgroupOf M).map θ : Subgroup (Perm (ι × Bool))) =
      ((fsign T).ker).map (blockPermHom ι))
    (hT1 : T.card ≠ 1)
    (hSle : ((S.subgroupOf M).map θ : Subgroup (Perm (ι × Bool))) ≤ blockFix ι)
    (x : Perm (ι × Bool)) :
    (∃ s : ↥M, (s : G) ∈ S ∧ θ s = x) ↔ x ∈ blockFix ι ∧ x ∈ θ.range := by
  classical
  set W : Subgroup (Perm (ι × Bool)) := ((thompsonJ S).subgroupOf M).map θ with hWdef
  have hWF : W ≤ blockFix ι := by
    rw [hW]; rintro _ ⟨g, -, rfl⟩; exact blockPermHom_mem g
  have hWfl := exists_flip_of_AT T hT1
  rw [← hW] at hWfl
  have hbs : ∀ m : ↥M, (m : G) ∈ Subgroup.normalizer (S : Set G) → θ m ∈ blockStab ι :=
    fun m hm => blockStab_of_mem_normalizer hWF hWfl (theta_mem_normalizer_W θ m hm)
  have hWJ : ∀ σ ∈ blockFix ι, σ ∈ Subgroup.normalizer (W : Set (Perm (ι × Bool))) := by
    intro σ hσ
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hconj : ∀ y ∈ blockFix ι, σ * y * σ⁻¹ = y := fun y hy => by
      have := blockFix_mul_comm hσ hy
      rw [this]; group
    constructor
    · intro hmem; rw [hconj h (hWF hmem)]; exact hmem
    · intro hmem
      have hF : σ * h * σ⁻¹ ∈ blockFix ι := hWF hmem
      have hhF : h ∈ blockFix ι := by
        have := conj_mem_blockFix ((blockStab ι).inv_mem (blockFix_le_blockStab hσ)) hF
        simpa [mul_assoc] using this
      rw [hconj h hhF] at hmem; exact hmem
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨hSle ⟨s, Subgroup.mem_subgroupOf.2 hs, rfl⟩, ⟨s, rfl⟩⟩
  · rintro ⟨hx, m, rfl⟩
    exact ⟨m, mem_of_theta_mem_blockFix_gen hA θ hker hbs hWJ m hx, rfl⟩

variable {S L : Subgroup G}

open scoped Classical in
theorem pairActionData_of_caseTwo_of_le (hA : Asc81bHyp (L ⊔ S) S)
    (hLM : IsTwoPrimeComponent (L ⊔ S) L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hpS : pCoreOf 2 (L ⊔ S) ≤ S) (n : ℕ) (_hn : 5 ≤ n) (θ : ↥(L ⊔ S) →* Perm (Fin n × Bool))
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S))
    (hAltL : ∀ x ∈ alternatingGroup (Fin n × Bool),
      ∃ l : ↥L, θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x)
    (hWF : (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))) ≤
      blockFix (Fin n))
    (hD : ∀ i j : Fin n,
      blockTransp i ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))) →
      blockTransp j ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))) →
      blockTransp i * blockTransp j ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))))
    (hT1 : (Finset.univ.filter fun i : Fin n => blockTransp i ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool)))).card ≠ 1)
    (hSle : ((S.subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))) ≤ blockFix (Fin n)) :
    PairActionData (L ⊔ S) S L n := by
  classical
  obtain ⟨T, hTW, hts⟩ := exists_AT_of_dbl hWF hD
  have hTeq : T = Finset.univ.filter fun i : Fin n => blockTransp i ∉
      (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin n × Bool))) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hts i, not_not]
  have hSθ := theta_S_iff_mem_blockFix_AF_of_le hA θ
    (fun m h => hpS ((hker m).1 h)) T hTW (by rw [hTeq]; exact hT1) hSle
  exact pairActionData_of_theta hLM hSL hpS n θ hker hAltL hSθ

section Omega

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

open scoped Classical in
theorem pairActionData_of_theta_perm_of_le (hA : Asc81bHyp (L ⊔ S) S)
    (hLM : IsTwoPrimeComponent (L ⊔ S) L) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hpS : pCoreOf 2 (L ⊔ S) ≤ S)
    (θ : ↥(L ⊔ S) →* Perm Ω)
    (hker : ∀ m : ↥(L ⊔ S), θ m = 1 ↔ (m : G) ∈ pCoreOf 2 (L ⊔ S))
    (hAltL : ∀ x ∈ alternatingGroup Ω,
      ∃ l : ↥L, θ ⟨l, (le_sup_left : L ≤ L ⊔ S) l.2⟩ = x)
    (σ : Perm Ω) (hσ1 : ∀ x, σ x ≠ x) (hσ2 : ∀ x, σ (σ x) = x) (n : ℕ)
    (hn : Fintype.card Ω = 2 * n) (hn5 : 5 ≤ n)
    (hSF : ((S.subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)) ≤ pairPres σ hσ1 hσ2)
    (hD : ∀ x y, y ≠ x → y ≠ σ x →
      swap x (σ x) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)) →
      swap y (σ y) ∉ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)) →
      swap x (σ x) * swap y (σ y) ∈
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)))
    (hN1 : (Finset.univ.filter fun x : Ω => swap x (σ x) ∉
        (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω))).card ≠ 2 * 1) :
    PairActionData (L ⊔ S) S L n := by
  obtain ⟨e, he⟩ := exists_finBlockEquiv σ hσ1 hσ2 n hn
  let θ' : ↥(L ⊔ S) →* Perm (Fin n × Bool) := e.permCongrHom.toMonoidHom.comp θ
  have hθ' : ∀ m, θ' m = e.permCongr (θ m) := fun m => rfl
  have hW' : ((thompsonJ S).subgroupOf (L ⊔ S)).map θ' =
      (((thompsonJ S).subgroupOf (L ⊔ S)).map θ).map e.permCongrHom.toMonoidHom := by
    rw [Subgroup.map_map]
  have hS' : (S.subgroupOf (L ⊔ S)).map θ' =
      ((S.subgroupOf (L ⊔ S)).map θ).map e.permCongrHom.toMonoidHom := by
    rw [Subgroup.map_map]
  have hWS : (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm Ω)) ≤
      pairPres σ hσ1 hσ2 :=
    le_trans (Subgroup.map_mono (Subgroup.comap_mono
      (iSup_le fun A => iSup_le fun hA => hA.1 : thompsonJ S ≤ S))) hSF
  refine pairActionData_of_caseTwo_of_le hA hLM hSL hpS n hn5 θ' ?_ ?_ ?_ ?_ ?_ ?_
  · intro m
    rw [hθ', ← hker m]
    constructor
    · intro h
      exact e.permCongr.injective (by rw [h]; exact (map_one e.permCongrHom).symm)
    · intro h
      rw [h]; exact (map_one e.permCongrHom)
  · intro x hx
    have hx' : e.permCongr.symm x ∈ alternatingGroup Ω := by
      rw [mem_alternatingGroup] at hx ⊢
      rw [← hx]
      have := Equiv.Perm.sign_permCongr e (e.permCongr.symm x)
      rw [← this]
      simp
    obtain ⟨l, hl⟩ := hAltL _ hx'
    exact ⟨l, by rw [hθ', hl]; exact Equiv.apply_symm_apply _ _⟩
  · rw [hW']; exact reindex_blockFix σ hσ1 hσ2 e he hWS
  · rw [hW']; exact reindex_hD σ e he hσ1 hσ2 hD
  · rw [hW']
    intro h
    apply hN1
    rw [card_filter_swap_eq σ e he Not, h]
  · rw [hS']; exact reindex_blockFix σ hσ1 hσ2 e he hSF

end Omega

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
