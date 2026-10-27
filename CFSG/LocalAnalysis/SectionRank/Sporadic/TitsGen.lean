module

public import CFSG.LieType.Simplicity.TitsModel

public section

namespace CFSG.SectionRank.TitsGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  ReeTag

section Collection

variable {τ : Tag} {K : Type} [Field K]

theorem nrep_flatten_mem
    (Q : Subgroup (adjointGroup τ K)) :
    ∀ L : List (List (Fin τ.rank)), (coxeterSystem τ).IsReduced L.flatten →
      (∀ ω ∈ L, nrep τ K ((coxeterSystem τ).wordProd ω) ∈ Q) →
        nrep τ K ((coxeterSystem τ).wordProd L.flatten) ∈ Q
  | [], _, _ => by
    rw [List.flatten_nil, CoxeterSystem.wordProd_nil, nrep_one]
    exact one_mem Q
  | ω :: L, hred, hQ => by
    rw [List.flatten_cons] at hred ⊢
    rw [CoxeterSystem.wordProd_append, nrep_mul_of_isReduced_append K hred]
    exact mul_mem (hQ ω List.mem_cons_self) (nrep_flatten_mem Q L
      (isReduced_left_right_of_append hred).2 fun ω' hω' => hQ ω' (List.mem_cons_of_mem _ hω'))

variable [Finite K]

theorem fixed_mem_of_reduced_blocks_of_nrep
    (F : adjointGroup τ K ≃* adjointGroup τ K)
    (δ : WeylGroup τ ≃* WeylGroup τ)
    (hFU0 : ∀ u ∈ (nativeData τ K).U, F u ∈ (nativeData τ K).U)
    (hFU : ∀ w, ∀ u ∈ Uminus τ K w, F u ∈ Uminus τ K (δ w))
    (hFn : ∀ w, δ w = w → F (nrep τ K w) = nrep τ K w)
    (L : List (List (Fin τ.rank)))
    (hδL : ∀ ω ∈ L, δ ((coxeterSystem τ).wordProd ω) = (coxeterSystem τ).wordProd ω)
    (hred : (coxeterSystem τ).IsReduced L.flatten) (Q : Subgroup (adjointGroup τ K))
    (hQn : ∀ ω ∈ L, nrep τ K ((coxeterSystem τ).wordProd ω) ∈ Q)
    (hQL : ∀ ω ∈ L, ∀ y ∈ Uminus τ K ((coxeterSystem τ).wordProd ω), F y = y → y ∈ Q) :
    ∀ u ∈ Uminus τ K ((coxeterSystem τ).wordProd L.flatten), F u = u → u ∈ Q := by
  induction L with
  | nil =>
    intro u hu _
    rw [List.flatten_nil, CoxeterSystem.wordProd_nil, Uminus_one, Subgroup.mem_bot] at hu
    rw [hu]
    exact one_mem Q
  | cons ω L ih =>
    intro u hu hFu
    rw [List.flatten_cons] at hred hu
    have hlen := length_mul_of_isReduced_append hred
    rw [CoxeterSystem.wordProd_append] at hu
    obtain ⟨z, hz, y, hy, hy', rfl⟩ := exists_mem_Uminus_mul_conj_mem_Uminus hlen hu
    have hδ' := map_wordProd_flatten δ fun ω' hω' => hδL ω' (List.mem_cons_of_mem _ hω')
    have hFn' := hFn _ hδ'
    have hFz : F z ∈ Uminus τ K ((coxeterSystem τ).wordProd L.flatten) := by
      have := hFU _ z hz
      rwa [hδ'] at this
    have hconj : ∀ x, F (nrep τ K ((coxeterSystem τ).wordProd L.flatten) * x *
        (nrep τ K ((coxeterSystem τ).wordProd L.flatten))⁻¹) =
        nrep τ K ((coxeterSystem τ).wordProd L.flatten) * F x *
          (nrep τ K ((coxeterSystem τ).wordProd L.flatten))⁻¹ := fun x => by
      rw [map_mul, map_mul, map_inv, hFn']
    have hFy : nrep τ K ((coxeterSystem τ).wordProd L.flatten) * F y *
        (nrep τ K ((coxeterSystem τ).wordProd L.flatten))⁻¹ ∈ (nativeData τ K).U := by
      rw [← hconj]
      exact hFU0 _ (nrep_conj_mem_U hy)
    obtain ⟨hz1, hy1⟩ := eq_of_mul_eq_of_mem_Uminus hFz hz hFy (nrep_conj_mem_U hy)
      (by rw [← map_mul, hFu])
    have hred' := (isReduced_left_right_of_append hred).2
    have hzQ : z ∈ Q :=
      ih (fun ω' hω' => hδL ω' (List.mem_cons_of_mem _ hω')) hred'
        (fun ω' hω' => hQn ω' (List.mem_cons_of_mem _ hω'))
        (fun ω' hω' => hQL ω' (List.mem_cons_of_mem _ hω')) z hz hz1
    have hy'Q := hQL ω List.mem_cons_self _ hy' (by rw [hconj, hy1])
    have hn := nrep_flatten_mem Q L hred' fun ω' hω' => hQn ω' (List.mem_cons_of_mem _ hω')
    have hyQ : y ∈ Q := by
      have := mul_mem (mul_mem (inv_mem hn) hy'Q) hn
      simpa [mul_assoc] using this
    exact mul_mem hzQ hyQ

theorem fixed_mem_U_of_reduced_blocks_of_nrep
    (F : adjointGroup τ K ≃* adjointGroup τ K)
    (δ : WeylGroup τ ≃* WeylGroup τ)
    (hFU0 : ∀ u ∈ (nativeData τ K).U, F u ∈ (nativeData τ K).U)
    (hFU : ∀ w, ∀ u ∈ Uminus τ K w, F u ∈ Uminus τ K (δ w))
    (hFn : ∀ w, δ w = w → F (nrep τ K w) = nrep τ K w)
    (L : List (List (Fin τ.rank)))
    (hδL : ∀ ω ∈ L, δ ((coxeterSystem τ).wordProd ω) = (coxeterSystem τ).wordProd ω)
    (hred : (coxeterSystem τ).IsReduced L.flatten)
    (hneg : ∀ α : Root τ, 0 < height α.1 →
      height ((coxeterSystem τ).wordProd L.flatten • α).1 < 0)
    (Q : Subgroup (adjointGroup τ K))
    (hQn : ∀ ω ∈ L, nrep τ K ((coxeterSystem τ).wordProd ω) ∈ Q)
    (hQL : ∀ ω ∈ L, ∀ y ∈ Uminus τ K ((coxeterSystem τ).wordProd ω), F y = y → y ∈ Q) :
    ∀ u ∈ (nativeData τ K).U, F u = u → u ∈ Q := by
  rw [← Uminus_eq_U_of_forall hneg]
  exact fixed_mem_of_reduced_blocks_of_nrep F δ hFU0 hFU hFn L hδL hred Q hQn hQL

end Collection

section Tits

variable (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]

noncomputable abbrev g0
    : reeFixed ReeTag.F4 K 0 := ⟨titsG0 K, titsG0_mem_reeFixed⟩

noncomputable abbrev g1
    : reeFixed ReeTag.F4 K 0 := ⟨titsG1 K, titsG1_mem_reeFixed⟩

noncomputable abbrev z1
    : reeFixed ReeTag.F4 K 0 := ⟨titsZ1 K, titsZ1_mem_reeFixed⟩

noncomputable abbrev z2
    : reeFixed ReeTag.F4 K 0 := ⟨titsZ2 K, titsZ2_mem_reeFixed⟩

noncomputable abbrev gens
    : Set (reeFixed ReeTag.F4 K 0) := {g0 K, g1 K, z1 K, z2 K}

variable {K}

theorem closure_titsGens_eq_top
    (hK : Nat.card K = 2) : Subgroup.closure (gens K) = ⊤ := by
  set P := Subgroup.closure (gens K)
  have hg0 : g0 K ∈ P := Subgroup.subset_closure (by simp)
  have hg1 : g1 K ∈ P := Subgroup.subset_closure (by simp)
  have hz1 : z1 K ∈ P := Subgroup.subset_closure (by simp)
  have hz2 : z2 K ∈ P := Subgroup.subset_closure (by simp)
  set r₀ := ReeTag.F4.reeOrbitWord (0 : Fin 4)
  set r₁ := ReeTag.F4.reeOrbitWord (1 : Fin 4)
  have hL : [r₀, r₁, r₀, r₁, r₀, r₁, r₀, r₁].flatten = ReeTag.F4.longWord := by decide
  have h01 : ∀ ω ∈ [r₀, r₁, r₀, r₁, r₀, r₁, r₀, r₁], ω = r₀ ∨ ω = r₁ := by
    intro ω hω
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hω
    rcases hω with h | h | h | h | h | h | h | h <;> simp [h]
  have hB : reeBorelPart ReeTag.F4 K 0 ≤ P := by
    intro b hb
    have hbU : (b : adjointGroup ReeTag.F4.tag K) ∈ (nativeData ReeTag.F4.tag K).U :=
      reeBorelPart_le_reeUnipPart_of_card_eq_two hK hb
    have key := fixed_mem_U_of_reduced_blocks_of_nrep (ReeTag.F4.reeAut K 0) ReeTag.F4.weylPerm
      (fun u hu => reeAut_mem_U 0 hu) (fun w u hu => reeAut_mem_Uminus 0 w hu)
      (fun w hw => by rw [reeAut_nrep, hw]) [r₀, r₁, r₀, r₁, r₀, r₁, r₀, r₁]
      (by
        intro ω hω
        rcases h01 ω hω with rfl | rfl
        · exact (mem_relWeylRee _).1 (reeOrbitWord_mem ReeTag.F4 (0 : Fin 4))
        · exact (mem_relWeylRee _).1 (reeOrbitWord_mem ReeTag.F4 (1 : Fin 4)))
      (by rw [hL]; exact ReeTag.F4.isReduced_longWord)
      (by rw [hL]; exact height_wordProd_smul_neg_of_negCheck ReeTag.F4.negCheck_longWord)
      (P.map (reeFixed ReeTag.F4 K 0).subtype)
      (by
        intro ω hω
        rcases h01 ω hω with rfl | rfl
        · exact ⟨z1 K, hz1, rfl⟩
        · exact ⟨z2 K, hz2, rfl⟩)
      (by
        intro ω hω y hy hF
        rcases h01 ω hω with rfl | rfl
        · rcases eq_one_or_eq_titsG0 hK hy hF with rfl | rfl
          · exact one_mem _
          · exact ⟨g0 K, hg0, rfl⟩
        · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_titsG1 hK hy hF)
          exact ⟨g1 K ^ k, zpow_mem hg1 k, by simp⟩)
    obtain ⟨y, hy, hyb⟩ := key b hbU b.2
    rwa [Subtype.ext hyb] at hy
  refine eq_top_of_reeBorelPart_le hB fun i => ?_
  fin_cases i
  · exact hz1
  · exact hz2
  · exact hz2
  · exact hz1

end Tits

end CFSG.SectionRank.TitsGen
