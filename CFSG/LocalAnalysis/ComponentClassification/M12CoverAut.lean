module

public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer

public section

namespace CFSG.ComponentClassification.M12Cover

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native
open CFSG.ComponentClassification.OuterAutomorphisms

theorem blockHom_castAdd (p q : Equiv.Perm (Fin 12)) (j : Fin 12) :
    blockHom (p, q) (Fin.castAdd 12 j) = Fin.castAdd 12 (p j) := by
  change finSumFinEquiv ((p.sumCongr q) (finSumFinEquiv.symm (Fin.castAdd 12 j))) = _
  rw [finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left]

theorem blockHom_natAdd (p q : Equiv.Perm (Fin 12)) (j : Fin 12) :
    blockHom (p, q) (Fin.natAdd 12 j) = Fin.natAdd 12 (q j) := by
  change finSumFinEquiv ((p.sumCongr q) (finSumFinEquiv.symm (Fin.natAdd 12 j))) = _
  rw [finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

theorem sigma_castAdd : ∀ j : Fin 12, m12Sigma (Fin.castAdd 12 j) = Fin.natAdd 12 j := by
  decide

theorem sigma_natAdd : ∀ j : Fin 12, m12Sigma (Fin.natAdd 12 j) = Fin.castAdd 12 j := by
  decide

theorem fin24_cases :
    ∀ i : Fin 24, (∃ j : Fin 12, i = Fin.castAdd 12 j) ∨ ∃ j : Fin 12, i = Fin.natAdd 12 j := by
  decide

theorem sigma_mul_self : m12Sigma * m12Sigma = 1 := m12_sigma_check.1

theorem sigma_inv : m12Sigma⁻¹ = m12Sigma := inv_eq_of_mul_eq_one_left sigma_mul_self

theorem sigma_conj_blockHom (p q : Equiv.Perm (Fin 12)) :
    m12Sigma * blockHom (p, q) * m12Sigma⁻¹ = blockHom (q, p) := by
  rw [sigma_inv]
  ext i
  rcases fin24_cases i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp only [Equiv.Perm.mul_apply, sigma_castAdd, blockHom_natAdd, sigma_natAdd,
      blockHom_castAdd]
  · simp only [Equiv.Perm.mul_apply, sigma_natAdd, blockHom_castAdd, sigma_castAdd,
      blockHom_natAdd]

abbrev blockGroup : Subgroup (Equiv.Perm (Fin 24)) := m12D.originalSubgroup

theorem mem_blockGroup {g : Equiv.Perm (Fin 24)} :
    g ∈ blockGroup ↔ ∃ p ∈ m12Pairs, blockHom p = g := by
  rw [blockGroup, m12D_originalSubgroup]
  rfl

theorem blockHom_mem {p : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)} (hp : p ∈ m12Pairs) :
    blockHom p ∈ blockGroup :=
  mem_blockGroup.2 ⟨p, hp, rfl⟩

theorem mem_pairs_of_blockHom_mem {p : Equiv.Perm (Fin 12) × Equiv.Perm (Fin 12)}
    (hp : blockHom p ∈ blockGroup) : p ∈ m12Pairs := by
  obtain ⟨q, hq, hqp⟩ := mem_blockGroup.1 hp
  rwa [← blockHom_injective hqp]

theorem pairs_swap {x y : Equiv.Perm (Fin 12)} (h : (x, y) ∈ m12Pairs) : (y, x) ∈ m12Pairs := by
  have h2 := m12D_sigma_normalizes _ (blockHom_mem h)
  rw [sigma_conj_blockHom] at h2
  exact mem_pairs_of_blockHom_mem h2

theorem pairs_fst_mem {x y : Equiv.Perm (Fin 12)} (h : (x, y) ∈ m12Pairs) :
    x ∈ NativeSporadic.M12 := by
  rw [← m12Pairs_fst]
  exact ⟨(x, y), h, rfl⟩

theorem pairs_snd_mem {x y : Equiv.Perm (Fin 12)} (h : (x, y) ∈ m12Pairs) :
    y ∈ NativeSporadic.M12 :=
  pairs_fst_mem (pairs_swap h)

theorem m12EquivD_proj (p : m12Pairs) : (m12EquivD (m12Proj p) : Equiv.Perm (Fin 24)) =
    blockHom p := by
  have h : (MulEquiv.ofBijective m12Proj m12Proj_bijective).symm (m12Proj p) = p :=
    (MulEquiv.ofBijective m12Proj m12Proj_bijective).symm_apply_apply p
  simp only [m12EquivD, MulEquiv.trans_apply, h]
  rfl

theorem m12EquivD_apply {g : NativeSporadic.M12} {h : Equiv.Perm (Fin 12)}
    (hp : ((g : Equiv.Perm (Fin 12)), h) ∈ m12Pairs) :
    (m12EquivD g : Equiv.Perm (Fin 24)) = blockHom ((g : Equiv.Perm (Fin 12)), h) := by
  have hg : g = m12Proj ⟨_, hp⟩ := Subtype.ext rfl
  rw [hg, m12EquivD_proj]
  rfl

theorem m12EquivD_symm_apply {x y : Equiv.Perm (Fin 12)} (hp : (x, y) ∈ m12Pairs) :
    m12EquivD.symm ⟨blockHom (x, y), blockHom_mem hp⟩ = ⟨x, pairs_fst_mem hp⟩ := by
  rw [MulEquiv.symm_apply_eq]
  exact Subtype.ext (m12EquivD_apply (g := ⟨x, pairs_fst_mem hp⟩) hp).symm

theorem sigma_conj_mem {g : Equiv.Perm (Fin 24)} (hg : g ∈ blockGroup) :
    m12Sigma * g * m12Sigma ∈ blockGroup := by
  simpa only [sigma_inv] using m12D_sigma_normalizes g hg

@[expose] def autModel : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {δ | δ ∈ blockGroup ∨ m12Sigma * δ ∈ blockGroup}
  one_mem' := Or.inl blockGroup.one_mem
  mul_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact Or.inl (blockGroup.mul_mem hx hy)
    · refine Or.inr ?_
      have : m12Sigma * (x * y) = (m12Sigma * x * m12Sigma) * (m12Sigma * y) := by
        rw [show m12Sigma * x * m12Sigma * (m12Sigma * y) =
          m12Sigma * x * (m12Sigma * m12Sigma) * y by group, sigma_mul_self]
        group
      rw [this]
      exact blockGroup.mul_mem (sigma_conj_mem hx) hy
    · refine Or.inr ?_
      rw [← mul_assoc]
      exact blockGroup.mul_mem hx hy
    · refine Or.inl ?_
      have : x * y = (m12Sigma * (m12Sigma * x) * m12Sigma) * (m12Sigma * y) := by
        rw [show m12Sigma * (m12Sigma * x) * m12Sigma * (m12Sigma * y) =
          (m12Sigma * m12Sigma) * x * (m12Sigma * m12Sigma) * y by group, sigma_mul_self]
        group
      rw [this]
      exact blockGroup.mul_mem (sigma_conj_mem hx) hy
  inv_mem' {x} hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl (blockGroup.inv_mem hx)
    · refine Or.inr ?_
      have : m12Sigma * x⁻¹ = m12Sigma * (m12Sigma * x)⁻¹ * m12Sigma := by
        rw [mul_inv_rev, sigma_inv]
        rw [show m12Sigma * (x⁻¹ * m12Sigma) * m12Sigma =
          m12Sigma * x⁻¹ * (m12Sigma * m12Sigma) by group, sigma_mul_self, mul_one]
      rw [this]
      exact sigma_conj_mem (blockGroup.inv_mem hx)

theorem mem_autModel {δ : Equiv.Perm (Fin 24)} :
    δ ∈ autModel ↔ δ ∈ blockGroup ∨ m12Sigma * δ ∈ blockGroup :=
  Iff.rfl

theorem blockGroup_le_autModel : blockGroup ≤ autModel := fun _ h => Or.inl h

theorem sigma_mem_autModel : m12Sigma ∈ autModel :=
  Or.inr (by rw [sigma_mul_self]; exact blockGroup.one_mem)

theorem sigma_not_mem_blockGroup : m12Sigma ∉ blockGroup := by
  intro h
  obtain ⟨⟨p, q⟩, -, hp⟩ := mem_blockGroup.1 h
  have h0 := congrArg (fun g : Equiv.Perm (Fin 24) => g (Fin.castAdd 12 0)) hp
  simp only [blockHom_castAdd, sigma_castAdd] at h0
  have := congrArg Fin.val h0
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  omega

theorem autModel_eq_closure : autModel = Subgroup.closure {m12A1, m12B1, m12Sigma} := by
  apply le_antisymm
  · intro δ hδ
    have hD : blockGroup ≤ Subgroup.closure {m12A1, m12B1, m12Sigma} := by
      change m12D.originalSubgroup ≤ _
      rw [m12D_eq_closure, Subgroup.closure_le]
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hg
      rcases hg with rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    have hs : m12Sigma ∈ Subgroup.closure {m12A1, m12B1, m12Sigma} :=
      Subgroup.subset_closure (by simp)
    rcases hδ with h | h
    · exact hD h
    · have : δ = m12Sigma * (m12Sigma * δ) := by
        rw [← mul_assoc, sigma_mul_self, one_mul]
      rw [this]
      exact Subgroup.mul_mem _ hs (hD h)
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact Or.inl (m12_gens_memD _ (by simp))
    · exact Or.inl (m12_gens_memD _ (by simp))
    · exact sigma_mem_autModel

theorem autModel_conj_mem {δ : Equiv.Perm (Fin 24)} (hδ : δ ∈ autModel) :
    ∀ h ∈ blockGroup, δ * h * δ⁻¹ ∈ blockGroup := by
  intro h hh
  rcases hδ with hδ | hδ
  · exact blockGroup.mul_mem (blockGroup.mul_mem hδ hh) (blockGroup.inv_mem hδ)
  · have hδ' : δ = m12Sigma * (m12Sigma * δ) := by
      rw [← mul_assoc, sigma_mul_self, one_mul]
    rw [hδ', mul_inv_rev, sigma_inv]
    have := sigma_conj_mem (blockGroup.mul_mem (blockGroup.mul_mem hδ hh)
      (blockGroup.inv_mem hδ))
    simpa only [mul_assoc] using this

theorem autModel_conj_inv_mem {δ : Equiv.Perm (Fin 24)} (hδ : δ ∈ autModel) :
    ∀ h ∈ blockGroup, δ⁻¹ * h * δ ∈ blockGroup := by
  intro h hh
  simpa only [inv_inv] using autModel_conj_mem (autModel.inv_mem hδ) h hh

@[expose] def sigmaModel : autModel := ⟨m12Sigma, sigma_mem_autModel⟩

theorem sigmaModel_coe : (sigmaModel : Equiv.Perm (Fin 24)) = m12Sigma := rfl

theorem sigmaModel_mul_self : sigmaModel * sigmaModel = 1 := Subtype.ext sigma_mul_self

theorem index_blockGroup : (blockGroup.subgroupOf autModel).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨sigmaModel, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, sigmaModel_coe]
  by_cases hb : (b : Equiv.Perm (Fin 24)) ∈ blockGroup
  · refine Or.inr ⟨hb, fun h => sigma_not_mem_blockGroup ?_⟩
    have := blockGroup.mul_mem (blockGroup.inv_mem hb) h
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  · refine Or.inl ⟨?_, hb⟩
    rcases b.2 with h | h
    · exact absurd h hb
    · have := sigma_conj_mem h
      rwa [← mul_assoc, sigma_mul_self, one_mul] at this

theorem card_autModel : Nat.card autModel = 190080 := by
  have h := (blockGroup.subgroupOf autModel).card_mul_index
  rw [index_blockGroup,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe blockGroup_le_autModel).toEquiv,
    ← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2] at h
  omega

@[expose] noncomputable def autModelConj : autModel →* MulAut blockGroup where
  toFun δ := conjOn blockGroup δ (autModel_conj_mem δ.2) (autModel_conj_inv_mem δ.2)
  map_one' := MulEquiv.ext fun h => Subtype.ext (by simp [conjOn_apply])
  map_mul' δ₁ δ₂ := MulEquiv.ext fun h => Subtype.ext (by
    simp only [conjOn_apply, Subgroup.coe_mul, MulAut.mul_apply, mul_inv_rev]
    group)

@[expose] noncomputable def autModelHom : autModel →* MulAut NativeSporadic.M12 :=
  (MulAut.congr m12EquivD.symm).toMonoidHom.comp autModelConj

theorem autModelHom_apply (δ : autModel) (g : NativeSporadic.M12) :
    autModelHom δ g = m12EquivD.symm ⟨δ * m12EquivD g * (δ : Equiv.Perm (Fin 24))⁻¹,
      autModel_conj_mem δ.2 _ (m12EquivD g).2⟩ :=
  rfl

theorem autModelHom_injective : Function.Injective autModelHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro δ hδ
  have hc : ∀ h ∈ blockGroup, (δ : Equiv.Perm (Fin 24)) * h = h * δ := by
    intro h hh
    have h1 := congrArg (fun α : MulAut NativeSporadic.M12 => α (m12EquivD.symm ⟨h, hh⟩))
      (MonoidHom.mem_ker.1 hδ)
    simp only [autModelHom_apply, MulEquiv.apply_symm_apply, MulAut.one_apply] at h1
    have h2 := congrArg Subtype.val (m12EquivD.symm.injective h1)
    simp only at h2
    calc (δ : Equiv.Perm (Fin 24)) * h = δ * h * (δ : Equiv.Perm (Fin 24))⁻¹ * δ := by group
      _ = h * δ := by rw [h2]
  rcases δ.2 with hD | hσ
  · have hz : (⟨δ, hD⟩ : blockGroup) ∈ Subgroup.center blockGroup := by
      rw [Subgroup.mem_center_iff]
      intro h
      exact Subtype.ext (hc h h.2).symm
    rw [m12D_center, Subgroup.mem_bot] at hz
    have h1 := congrArg Subtype.val hz
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  · exfalso
    refine m12D_sigma_outer _ hσ fun h hh => ?_
    rw [← mul_assoc, sigma_mul_self, one_mul]
    exact hc h hh

instance instFiniteMulAutM12 : Finite (MulAut NativeSporadic.M12) :=
  Finite.of_injective (fun α : MulAut NativeSporadic.M12 => (α : NativeSporadic.M12 →
    NativeSporadic.M12)) DFunLike.coe_injective

theorem autModelHom_bijective : Function.Bijective autModelHom := by
  refine autModelHom_injective.bijective_of_nat_card_le ?_
  rw [card_autModel]
  have h := m12_mulAut_card
  rw [m12_card] at h
  exact h

@[expose] noncomputable def autModelEquiv : autModel ≃* MulAut NativeSporadic.M12 :=
  MulEquiv.ofBijective autModelHom autModelHom_bijective

theorem autModelEquiv_apply (δ : autModel) : autModelEquiv δ = autModelHom δ := rfl

@[expose] noncomputable def autModelIota : NativeSporadic.M12 →* autModel :=
  (blockGroup.subtype.comp m12EquivD.toMonoidHom).codRestrict autModel fun g =>
    blockGroup_le_autModel (m12EquivD g).2

theorem autModelIota_coe (g : NativeSporadic.M12) :
    (autModelIota g : Equiv.Perm (Fin 24)) = m12EquivD g :=
  rfl

theorem autModelIota_injective : Function.Injective autModelIota := by
  intro g h hgh
  have h1 := congrArg Subtype.val hgh
  exact m12EquivD.injective (Subtype.ext h1)

theorem autModelEquiv_iota (g : NativeSporadic.M12) :
    autModelEquiv (autModelIota g) = MulAut.conj g := by
  apply MulEquiv.ext
  intro h
  rw [autModelEquiv_apply, autModelHom_apply, MulAut.conj_apply, MulEquiv.symm_apply_eq]
  apply Subtype.ext
  simp only [autModelIota_coe, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]

theorem mem_blockGroup_iff_iota {δ : autModel} :
    (δ : Equiv.Perm (Fin 24)) ∈ blockGroup ↔ ∃ g, autModelIota g = δ := by
  constructor
  · intro h
    refine ⟨m12EquivD.symm ⟨δ, h⟩, Subtype.ext ?_⟩
    rw [autModelIota_coe, MulEquiv.apply_symm_apply]
  · rintro ⟨g, rfl⟩
    exact (m12EquivD g).2

@[expose] noncomputable def beta : MulAut NativeSporadic.M12 := autModelEquiv sigmaModel

theorem beta_apply_of_mem {g : NativeSporadic.M12} {h : Equiv.Perm (Fin 12)}
    (hp : ((g : Equiv.Perm (Fin 12)), h) ∈ m12Pairs) :
    (beta g : Equiv.Perm (Fin 12)) = h := by
  rw [beta, autModelEquiv_apply, autModelHom_apply]
  have hsw := pairs_swap hp
  have heq : (⟨(sigmaModel : Equiv.Perm (Fin 24)) * m12EquivD g *
      (sigmaModel : Equiv.Perm (Fin 24))⁻¹, autModel_conj_mem sigmaModel.2 _
        (m12EquivD g).2⟩ : blockGroup) = ⟨blockHom (h, g), blockHom_mem hsw⟩ := by
    apply Subtype.ext
    simp only [sigmaModel]
    rw [m12EquivD_apply hp, sigma_conj_blockHom]
  rw [heq, m12EquivD_symm_apply hsw]

theorem beta_m12a : beta m12a = m12a :=
  Subtype.ext (beta_apply_of_mem (Subgroup.subset_closure (Set.mem_insert _ _)))

theorem beta_m12b : (beta m12b : Equiv.Perm (Fin 12)) = m12bp :=
  beta_apply_of_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem m12bp_apply : ∀ i, m12bp i = ![5, 8, 1, 0, 7, 3, 10, 9, 2, 4, 11, 6] i := by
  decide

theorem beta_mul_self : beta * beta = 1 := by
  rw [beta, ← map_mul, sigmaModel_mul_self, map_one]

theorem beta_ne_one : beta ≠ 1 := by
  intro h
  have := congrArg (fun α : MulAut NativeSporadic.M12 => (α m12b : Equiv.Perm (Fin 12))) h
  simp only [beta_m12b, MulAut.one_apply] at this
  exact absurd (congrArg (fun g : Equiv.Perm (Fin 12) => g 0) this) (by decide)

theorem autModelEquiv_symm_conj (g : NativeSporadic.M12) :
    autModelEquiv.symm (MulAut.conj g) = autModelIota g := by
  rw [MulEquiv.symm_apply_eq, autModelEquiv_iota]

theorem beta_not_mem_inner : beta ∉ inner NativeSporadic.M12 := by
  rintro ⟨g, hg⟩
  have h := congrArg autModelEquiv.symm hg
  rw [autModelEquiv_symm_conj, beta, MulEquiv.symm_apply_apply] at h
  exact sigma_not_mem_blockGroup (by
    have := (m12EquivD g).2
    rwa [← autModelIota_coe, h] at this)

theorem m12_closure_eq_top : Subgroup.closure {m12a, m12b} = ⊤ :=
  closure_pair_eq_top m12_eq _ _

theorem eq_beta_of_apply (α : MulAut NativeSporadic.M12) (ha : α m12a = m12a)
    (hb : (α m12b : Equiv.Perm (Fin 12)) = m12bp) : α = beta := by
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.eq_of_eqOn_dense m12_closure_eq_top
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · simp only [MulEquiv.coe_toMonoidHom, ha, beta_m12a]
  · exact Subtype.ext (by simp only [MulEquiv.coe_toMonoidHom, hb, beta_m12b])

theorem autModelEquiv_symm_beta : autModelEquiv.symm beta = sigmaModel := by
  rw [beta, MulEquiv.symm_apply_apply]

theorem m12_center : Subgroup.center NativeSporadic.M12 = ⊥ := m12_center_eq_bot'

theorem conj_injective : Function.Injective (MulAut.conj : NativeSporadic.M12 →* MulAut _) := by
  intro g h hgh
  apply autModelIota_injective
  apply autModelEquiv.injective
  rw [autModelEquiv_iota, autModelEquiv_iota, hgh]

theorem exists_conj_or_conj_mul_beta (α : MulAut NativeSporadic.M12) :
    ∃ g, α = MulAut.conj g ∨ α = MulAut.conj g * beta := by
  obtain ⟨δ, rfl⟩ := autModelEquiv.surjective α
  rcases δ.2 with hD | hσ
  · obtain ⟨g, hg⟩ := mem_blockGroup_iff_iota.1 hD
    exact ⟨g, Or.inl (by rw [← hg, autModelEquiv_iota])⟩
  · have hD : (δ : Equiv.Perm (Fin 24)) * m12Sigma ∈ blockGroup := by
      have := sigma_conj_mem hσ
      rwa [← mul_assoc, sigma_mul_self, one_mul] at this
    have hD' : ((δ * sigmaModel : autModel) : Equiv.Perm (Fin 24)) ∈ blockGroup := by
      rw [Subgroup.coe_mul, sigmaModel_coe]
      exact hD
    obtain ⟨g, hg⟩ := mem_blockGroup_iff_iota.1 hD'
    refine ⟨g, Or.inr ?_⟩
    have : δ = autModelIota g * sigmaModel := by
      rw [hg, mul_assoc, sigmaModel_mul_self, mul_one]
    rw [this, map_mul, autModelEquiv_iota, beta]

theorem exists_unique_conj_mul_beta_pow (α : MulAut NativeSporadic.M12) :
    ∃! p : NativeSporadic.M12 × Fin 2, α = MulAut.conj p.1 * beta ^ (p.2 : ℕ) := by
  obtain ⟨g, hg | hg⟩ := exists_conj_or_conj_mul_beta α
  · refine ⟨(g, 0), by simpa using hg, ?_⟩
    rintro ⟨h, e⟩ he
    simp only at he
    fin_cases e
    · simp only [pow_zero, mul_one] at he
      rw [hg] at he
      rw [conj_injective he.symm]
      rfl
    · exfalso
      simp only [pow_one] at he
      apply beta_not_mem_inner
      refine ⟨h⁻¹ * g, ?_⟩
      rw [map_mul, map_inv, ← hg, he]
      group
  · refine ⟨(g, 1), by simpa using hg, ?_⟩
    rintro ⟨h, e⟩ he
    simp only at he
    fin_cases e
    · exfalso
      simp only [pow_zero, mul_one] at he
      apply beta_not_mem_inner
      refine ⟨g⁻¹ * h, ?_⟩
      rw [map_mul, map_inv, ← he, hg]
      group
    · simp only [pow_one] at he
      rw [hg] at he
      rw [conj_injective (mul_right_cancel he).symm]
      rfl

theorem card_mulAut : Nat.card (MulAut NativeSporadic.M12) = 190080 := by
  rw [← Nat.card_congr autModelEquiv.toEquiv, card_autModel]

theorem card_inner : Nat.card (inner NativeSporadic.M12) = 95040 := by
  rw [card_inner_of_center_eq_bot m12_center, m12_card]

theorem card_outer : Nat.card (Outer NativeSporadic.M12) = 2 := by
  have h := (inner NativeSporadic.M12).card_eq_card_quotient_mul_card_subgroup
  rw [card_mulAut, card_inner] at h
  change Nat.card (MulAut NativeSporadic.M12 ⧸ inner NativeSporadic.M12) = 2
  omega

@[expose] noncomputable def outerEquiv : Outer NativeSporadic.M12 ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq card_outer (by rw [Nat.card_eq_fintype_card]; rfl)

theorem orderOf_beta : orderOf beta = 2 :=
  orderOf_eq_prime (by rw [sq, beta_mul_self]) beta_ne_one

theorem mem_zpowers_beta (γ : MulAut NativeSporadic.M12) :
    γ ∈ Subgroup.zpowers beta ↔ γ = 1 ∨ γ = beta := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_beta]
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, hn, rfl⟩
    interval_cases n
    · exact Or.inl (pow_zero _)
    · exact Or.inr (pow_one _)
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, pow_zero _⟩
    · exact ⟨1, by norm_num, pow_one _⟩

theorem card_zpowers_beta : Nat.card (Subgroup.zpowers beta) = 2 := by
  rw [Nat.card_zpowers, orderOf_beta]

abbrev AutSemidirect : Type :=
  NativeSporadic.M12 ⋊[(Subgroup.zpowers beta).subtype] Subgroup.zpowers beta

theorem conj_apply_eq (γ : MulAut NativeSporadic.M12) (g : NativeSporadic.M12) :
    MulAut.conj (γ g) = γ * MulAut.conj g * γ⁻¹ := by
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, MulAut.apply_inv_self, map_inv]

@[expose] noncomputable def autSemidirectHom : AutSemidirect →* MulAut NativeSporadic.M12 :=
  SemidirectProduct.lift MulAut.conj (Subgroup.zpowers beta).subtype fun γ => by
    ext g x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      Subgroup.coe_subtype, conj_apply_eq]
    rfl

theorem autSemidirectHom_apply (p : AutSemidirect) :
    autSemidirectHom p = MulAut.conj p.left * (p.right : MulAut NativeSporadic.M12) :=
  rfl

theorem autSemidirectHom_bijective : Function.Bijective autSemidirectHom := by
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    rw [MonoidHom.mem_ker, autSemidirectHom_apply] at hp
    rcases (mem_zpowers_beta _).1 p.right.2 with h | h
    · rw [h, mul_one] at hp
      have hl : p.left = 1 := conj_injective (by rw [hp, map_one])
      have hr : p.right = 1 := Subtype.ext h
      exact Subgroup.mem_bot.2 (SemidirectProduct.ext hl hr)
    · exfalso
      rw [h] at hp
      apply beta_not_mem_inner
      refine ⟨p.left⁻¹, ?_⟩
      rw [map_inv, inv_eq_iff_mul_eq_one]
      simpa using hp
  · rw [card_mulAut]
    have : Nat.card AutSemidirect = Nat.card (NativeSporadic.M12 × Subgroup.zpowers beta) :=
      Nat.card_congr SemidirectProduct.equivProd
    rw [this, Nat.card_prod, m12_card, card_zpowers_beta]

@[expose] noncomputable def autSemidirectEquiv : AutSemidirect ≃* MulAut NativeSporadic.M12 :=
  MulEquiv.ofBijective autSemidirectHom autSemidirectHom_bijective

theorem mem_fixSub_beta_iff (g : NativeSporadic.M12) :
    g ∈ fixSub beta ↔ (m12EquivD g : Equiv.Perm (Fin 24)) ∈ centralizerIn blockGroup m12Sigma := by
  rw [mem_fixSub, mem_centralizerIn, beta, autModelEquiv_apply, autModelHom_apply,
    MulEquiv.symm_apply_eq]
  simp only [sigmaModel_coe, Subtype.ext_iff]
  constructor
  · intro h
    refine ⟨(m12EquivD g).2, ?_⟩
    calc (m12EquivD g : Equiv.Perm (Fin 24)) * m12Sigma =
        m12Sigma * m12EquivD g * m12Sigma⁻¹ * m12Sigma := by rw [h]
      _ = m12Sigma * m12EquivD g := by group
  · rintro ⟨-, h⟩
    calc m12Sigma * (m12EquivD g : Equiv.Perm (Fin 24)) * m12Sigma⁻¹ =
        m12EquivD g * m12Sigma * m12Sigma⁻¹ := by rw [h]
      _ = m12EquivD g := by group

theorem centralizerIn_blockGroup_sigma :
    centralizerIn blockGroup m12Sigma = m12SigmaCentQ.originalSubgroup := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, hsz, hord⟩ := m12_sigma_cover
  obtain ⟨hc, ho, hcomm, -⟩ := m12_sigma_cent
  have hA : m12A1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  have hB : m12B1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hK : m12SigmaCentQ.originalSubgroup ≤ centralizerIn m12D.originalSubgroup m12Sigma := by
    rw [m12SigmaCentQ, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m12_gens_memD w) hcomm
  have hKc : Nat.card m12SigmaCentQ.originalSubgroup = 120 := by
    rw [← m12SigmaCentQ.orderCertificate_eq_card hc, ho]
  have hord' : orderOf m12Sigma = 2 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hord
  obtain ⟨-, hsize⟩ := exists_conj_of_repsOK hn m12D m12D_check.1 (pairTables_spec hn hA hB)
    m12Sigma (inv_conj_mem _ m12D_sigma_normalizes m12D_sigma_sq) (by norm_num) [m12Sigma]
    (fun r hr => by
      rw [List.mem_singleton] at hr
      subst hr
      exact ⟨by simp, hord'⟩) 1000 hok
  exact centralizerIn_eq_of_le _ _ hK (hsize _ (List.mem_singleton_self _))
    (by rw [hsz, hKc, ← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2])

theorem card_fixSub_beta : Nat.card (fixSub beta) = 120 := by
  have hmap : (fixSub beta).map (blockGroup.subtype.comp m12EquivD.toMonoidHom) =
      centralizerIn blockGroup m12Sigma := by
    ext x
    simp only [Subgroup.mem_map, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, Subgroup.coe_subtype, mem_fixSub_beta_iff]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hx
      have hxD : x ∈ blockGroup := (mem_centralizerIn.1 hx).1
      refine ⟨m12EquivD.symm ⟨x, hxD⟩, ?_, ?_⟩ <;> simp [hx]
  have hinj : Function.Injective (blockGroup.subtype.comp m12EquivD.toMonoidHom) :=
    blockGroup.subtype_injective.comp m12EquivD.injective
  rw [← Subgroup.card_map_of_injective hinj, hmap, centralizerIn_blockGroup_sigma,
    ← m12SigmaCentQ.orderCertificate_eq_card m12_sigma_cent.1, m12_sigma_cent.2.1]

theorem ctuc_mathieu_m12_full_automorphism_model :
    (∃! β : MulAut NativeSporadic.M12, β m12a = m12a ∧
      ∀ i, (β m12b : Equiv.Perm (Fin 12)) i = ![5, 8, 1, 0, 7, 3, 10, 9, 2, 4, 11, 6] i) ∧
    beta m12a = m12a ∧
    (∀ i, (beta m12b : Equiv.Perm (Fin 12)) i = ![5, 8, 1, 0, 7, 3, 10, 9, 2, 4, 11, 6] i) ∧
    beta ^ 2 = 1 ∧ beta ∉ inner NativeSporadic.M12 ∧
    (∀ α : MulAut NativeSporadic.M12,
      ∃! p : NativeSporadic.M12 × Fin 2, α = MulAut.conj p.1 * beta ^ (p.2 : ℕ)) ∧
    (∀ p : AutSemidirect, autSemidirectEquiv p = MulAut.conj p.left * (p.right : MulAut _)) ∧
    Nat.card (MulAut NativeSporadic.M12) = 190080 ∧
    Nonempty (Outer NativeSporadic.M12 ≃* Multiplicative (ZMod 2)) := by
  have hb : ∀ i, (beta m12b : Equiv.Perm (Fin 12)) i =
      ![5, 8, 1, 0, 7, 3, 10, 9, 2, 4, 11, 6] i := by
    rw [beta_m12b]
    exact m12bp_apply
  refine ⟨⟨beta, ⟨beta_m12a, hb⟩, fun α ⟨ha, hα⟩ => eq_beta_of_apply α ha ?_⟩, beta_m12a, hb,
    by rw [sq, beta_mul_self], beta_not_mem_inner, exists_unique_conj_mul_beta_pow,
    fun _ => rfl, card_mulAut, ⟨outerEquiv⟩⟩
  ext i
  rw [hα, m12bp_apply]

end CFSG.ComponentClassification.M12Cover
