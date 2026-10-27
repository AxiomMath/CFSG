module

public import CFSG.GH74.Generic.BProg.B2.T4B3aModels

public section

namespace CFSG.GH74.Generic.BProg.B2.T4.P151Model

open CFSG CFSG.GH74.GLS Matrix Subgroup
open CFSG.GH74.Generic.BProg.B2.T4.L5Inv CFSG.GH74.Generic.BProg.B2.T4.L5Count
open CFSG.GH74.Generic.BProg.B2.T4.B3aGen

section Signs

variable {F : Type} [Field F]

@[expose] def sgnOn (D : Finset (Fin 5)) : Fin 5 → F := fun i => if i ∈ D then -1 else 1

theorem sgnOn_sq (D : Finset (Fin 5)) (i : Fin 5) : sgnOn (F := F) D i * sgnOn D i = 1 := by
  unfold sgnOn
  split_ifs <;> simp

theorem sgnOn_apply_mem {D : Finset (Fin 5)} {i : Fin 5} (h : i ∈ D) : sgnOn (F := F) D i = -1 := by
  simp [sgnOn, h]

theorem sgnOn_apply_not_mem {D : Finset (Fin 5)} {i : Fin 5} (h : i ∉ D) : sgnOn (F := F) D i = 1 := by
  simp [sgnOn, h]

theorem prod_sgnOn (D : Finset (Fin 5)) : ∏ i, sgnOn (F := F) D i = (-1) ^ D.card := by
  classical
  unfold sgnOn
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Finset.filter_mem_eq_inter,
    Finset.univ_inter]

theorem prod_sgnOn_of_even {D : Finset (Fin 5)} (h : Even D.card) : ∏ i, sgnOn (F := F) D i = 1 := by
  rw [prod_sgnOn, h.neg_one_pow]

theorem sgnOn_comp_symm (D : Finset (Fin 5)) (σ : Equiv.Perm (Fin 5)) :
    (sgnOn (F := F) D ∘ σ.symm) = sgnOn (D.map σ.toEmbedding) := by
  funext i
  simp only [Function.comp_apply, sgnOn, Finset.mem_map_equiv]

theorem oneAt_eq_sgnOn (m : Fin 5) : oneAt (F := F) m = sgnOn (Finset.univ.erase m) := by
  funext i
  by_cases h : i = m
  · subst h; simp [oneAt, sgnOn]
  · simp [oneAt, sgnOn, h]

theorem card_compl_pair {i j : Fin 5} (hij : i ≠ j) : (Finset.univ \ {i, j}).card = 3 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_pair hij]

theorem exists_third {U : Finset (Fin 5)} (hU : U.card = 3) {x y : Fin 5} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : x ≠ y) : ∃ w ∈ U, w ≠ x ∧ w ≠ y := by
  have hc : ((U.erase x).erase y).card = 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨Ne.symm hxy, hy⟩), Finset.card_erase_of_mem hx, hU]
  obtain ⟨w, hw⟩ := Finset.card_eq_one.1 hc
  have hwm : w ∈ (U.erase x).erase y := by
    rw [hw]
    exact Finset.mem_singleton_self w
  simp only [Finset.mem_erase] at hwm
  exact ⟨w, hwm.2.2, hwm.2.1, hwm.1⟩

@[expose] def stdPats : Finset (Finset (Fin 5)) := Finset.univ.filter fun D => 4 ∉ D ∧ Even D.card

theorem mem_stdPats {D : Finset (Fin 5)} : D ∈ stdPats ↔ 4 ∉ D ∧ Even D.card := by
  simp [stdPats]

theorem card_stdPats : stdPats.card = 8 := by decide

open scoped Classical in
theorem eq_sgnOn_filter (h2 : (2 : F) ≠ 0) {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) :
    ε = sgnOn (Finset.univ.filter fun i => ε i = -1) := by
  funext i
  rcases eq_one_or_neg_one (hε i) with h | h
  · have hne : ε i ≠ -1 := by
      rw [h]
      intro h'
      apply h2
      linear_combination h'
    rw [sgnOn_apply_not_mem (by simp [hne]), h]
  · rw [sgnOn_apply_mem (by simp [h]), h]

open scoped Classical in
theorem filter_mem_stdPats (h2 : (2 : F) ≠ 0) {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1)
    (hdet : ∏ i, ε i = 1) (h4 : ε 4 = 1) : (Finset.univ.filter fun i => ε i = -1) ∈ stdPats := by
  rw [mem_stdPats]
  refine ⟨?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, h4]
    intro h'
    apply h2
    linear_combination h'
  · have h := hdet
    rw [eq_sgnOn_filter h2 hε, prod_sgnOn] at h
    exact (neg_one_pow_eq_one_iff_even (neg_one_ne_one h2)).1 h

theorem exists_perm_pair {i j : Fin 5} (hij : i ≠ j) (hi4 : i ≠ 4) (hj4 : j ≠ 4) :
    ∃ σ : Equiv.Perm (Fin 5), σ 4 = 4 ∧ σ i = 0 ∧ σ j = 1 := by
  set j₁ := Equiv.swap i 0 j with hj₁
  have hj₁0 : j₁ ≠ 0 := by
    intro h
    apply hij
    have : Equiv.swap i 0 j = Equiv.swap i 0 i := by rw [Equiv.swap_apply_left]; exact h
    exact ((Equiv.swap i 0).injective this).symm
  have hj₁4 : j₁ ≠ 4 := by
    rw [hj₁]
    by_cases h0 : j = 0
    · rw [h0, Equiv.swap_apply_right]; exact hi4
    · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hij) h0]; exact hj4
  refine ⟨Equiv.swap j₁ 1 * Equiv.swap i 0, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hi4) (by decide),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hj₁4) (by decide)]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm hj₁0) (by decide)]
  · rw [Equiv.Perm.mul_apply, ← hj₁, Equiv.swap_apply_left]

end Signs

section Conj

variable {P : Type} [Group P]

theorem isCompIn_conj (g : P) {v : P} {L : Subgroup P} (hL : IsCompIn (centralizer ({v} : Set P)) L) :
    IsCompIn (centralizer ({g * v * g⁻¹} : Set P)) (L.map (MulAut.conj g).toMonoidHom) := by
  have h := isCompIn_map (MulAut.conj g) hL
  rwa [centralizer_map_mulEquiv, MulAut.conj_apply] at h

theorem comm_of_conj_comm (g : P) {L : Subgroup P} {w : P}
    (h : ∀ l ∈ L.map (MulAut.conj g).toMonoidHom, g * w * g⁻¹ * l = l * (g * w * g⁻¹)) :
    ∀ l ∈ L, w * l = l * w := by
  intro l hl
  have h1 := h (g * l * g⁻¹) ⟨l, hl, by simp [MulAut.conj_apply]⟩
  have h2 : g * (w * l) * g⁻¹ = g * (l * w) * g⁻¹ := by
    calc g * (w * l) * g⁻¹ = g * w * g⁻¹ * (g * l * g⁻¹) := by group
      _ = g * l * g⁻¹ * (g * w * g⁻¹) := h1
      _ = g * (l * w) * g⁻¹ := by group
  simpa using h2

theorem conj_mem_map (g : P) {L : Subgroup P} {w : P} (hw : w ∈ L) :
    g * w * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom :=
  ⟨w, hw, by simp [MulAut.conj_apply]⟩

theorem ea_sq {E : Subgroup P} (hE : CFSG.IsElementaryAbelian 2 ↥E) {e : P} (he : e ∈ E) : e * e = 1 := by
  have := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hE ⟨e, he⟩
  exact congrArg Subtype.val this

theorem ea_comm {E : Subgroup P} (hE : CFSG.IsElementaryAbelian 2 ↥E) {e f : P} (he : e ∈ E) (hf : f ∈ E) :
    e * f = f * e :=
  congrArg Subtype.val ((hE.toIsMulCommutative.is_comm).comm ⟨e, he⟩ ⟨f, hf⟩)

theorem mem_sup_zpowers_comm {E : Subgroup P} {v : P} (hvv : v * v = 1) (hvc : ∀ e ∈ E, e * v = v * e)
    {g : P} (hg : g ∈ E ⊔ zpowers v) : ∃ e ∈ E, g = e ∨ g = e * v := by
  let S : Subgroup P :=
    { carrier := {g | ∃ e ∈ E, g = e ∨ g = e * v}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨e, he, hae⟩ := ha
        obtain ⟨f, hf, hbf⟩ := hb
        refine ⟨e * f, E.mul_mem he hf, ?_⟩
        rcases hae with hae | hae <;> rcases hbf with hbf | hbf <;> rw [hae, hbf]
        · exact Or.inl rfl
        · exact Or.inr (by group)
        · refine Or.inr ?_
          calc e * v * f = e * (v * f) := by group
            _ = e * (f * v) := by rw [hvc f hf]
            _ = e * f * v := by group
        · refine Or.inl ?_
          calc e * v * (f * v) = e * (v * f) * v := by group
            _ = e * (f * v) * v := by rw [hvc f hf]
            _ = e * f * (v * v) := by group
            _ = e * f := by rw [hvv, mul_one]
      one_mem' := ⟨1, E.one_mem, Or.inl rfl⟩
      inv_mem' := by
        intro a ha
        obtain ⟨e, he, hae⟩ := ha
        refine ⟨e⁻¹, E.inv_mem he, ?_⟩
        rcases hae with hae | hae <;> rw [hae]
        · exact Or.inl rfl
        · refine Or.inr ?_
          have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
          rw [_root_.mul_inv_rev, hv']
          exact (hvc e⁻¹ (E.inv_mem he)).symm }
  have hle : E ⊔ zpowers v ≤ S := by
    refine sup_le (fun e he => ⟨e, he, Or.inl rfl⟩) ((Subgroup.zpowers_le).2 ⟨1, E.one_mem, Or.inr (by simp)⟩)
  exact hle hg

theorem isElementaryAbelian_sup_zpowers_comm {E : Subgroup P} (hE : CFSG.IsElementaryAbelian 2 ↥E) {v : P}
    (hvv : v * v = 1) (hvc : ∀ e ∈ E, e * v = v * e) : CFSG.IsElementaryAbelian 2 ↥(E ⊔ zpowers v) := by
  refine WeakSigGen.isElementaryAbelian_of_forall ?_ ?_
  · intro g hg h hh
    obtain ⟨e, he, hge⟩ := mem_sup_zpowers_comm hvv hvc hg
    obtain ⟨f, hf, hhf⟩ := mem_sup_zpowers_comm hvv hvc hh
    rcases hge with hge | hge <;> rcases hhf with hhf | hhf <;> rw [hge, hhf]
    · exact ea_comm hE he hf
    · calc e * (f * v) = (e * f) * v := by group
        _ = (f * e) * v := by rw [ea_comm hE he hf]
        _ = f * (e * v) := by group
        _ = f * (v * e) := by rw [hvc e he]
        _ = f * v * e := by group
    · calc e * v * f = e * (v * f) := by group
        _ = e * (f * v) := by rw [hvc f hf]
        _ = (e * f) * v := by group
        _ = (f * e) * v := by rw [ea_comm hE he hf]
        _ = f * (e * v) := by group
    · calc e * v * (f * v) = e * (v * f) * v := by group
        _ = e * (f * v) * v := by rw [hvc f hf]
        _ = (e * f) * (v * v) := by group
        _ = (f * e) * (v * v) := by rw [ea_comm hE he hf]
        _ = f * (e * v) * v := by group
        _ = f * (v * e) * v := by rw [hvc e he]
        _ = f * v * (e * v) := by group
  · intro g hg
    obtain ⟨e, he, hge⟩ := mem_sup_zpowers_comm hvv hvc hg
    rcases hge with hge | hge <;> rw [hge]
    · exact ea_sq hE he
    · calc e * v * (e * v) = e * (v * e) * v := by group
        _ = e * (e * v) * v := by rw [hvc e he]
        _ = (e * e) * (v * v) := by group
        _ = 1 := by rw [ea_sq hE he, hvv, one_mul]

end Conj

section Entry

variable {F : Type} [Field F]

@[expose] noncomputable def entryHomOn {S : Subgroup (GL (Fin 5) F)} (X : Subgroup ↥S) (i : Fin 5)
    (hX : ∀ c ∈ X, ∀ x, x ≠ i → (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i x = 0) :
    ↥X →* Fˣ :=
  MonoidHom.toHomUnits
    { toFun := fun c => ((((c : ↥X) : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i
      map_one' := by simp
      map_mul' := by
        intro c d
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
        rw [Finset.sum_eq_single i]
        · intro k _ hk
          rw [hX c c.2 k hk, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ i) h }

theorem entryHomOn_apply {S : Subgroup (GL (Fin 5) F)} (X : Subgroup ↥S) (i : Fin 5) (hX) (c : ↥X) :
    ((entryHomOn X i hX c : Fˣ) : F) =
      ((((c : ↥X) : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i := rfl

end Entry

section BlockMem

variable {F : Type} [Field F]

theorem permGL5_mem_blkGL {U : Finset (Fin 5)} {σ : Equiv.Perm (Fin 5)} (hσ : ∀ a, a ∉ U → σ a = a) :
    permGL5 (F := F) σ ∈ blkGL U := by
  intro a b hab
  rw [coe_permGL5]
  have key : σ⁻¹ a = b ↔ a = b := by
    rcases hab with ha | hb
    · have h1 : σ⁻¹ a = a := by
        rw [Equiv.Perm.inv_eq_iff_eq]
        exact (hσ a ha).symm
      rw [h1]
    · rw [Equiv.Perm.inv_eq_iff_eq, hσ b hb, eq_comm]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Matrix.one_apply]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (key.1 h1) h2
  · exact absurd (key.2 h2) h1
  · rfl

theorem sgnGL_mem_blkGL {U : Finset (Fin 5)} {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1)
    (hU : ∀ a, a ∉ U → ε a = 1) : sgnGL ε hε ∈ blkGL U := by
  intro a b hab
  rw [coe_sgnGL]
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rcases hab with ha | ha <;> exact hU a ha
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

end BlockMem

section Concl

variable {J J' : Type} [Group J] [Group J']

theorem isL3Odd_equiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (h : IsL3Odd K) : IsL3Odd K' := by
  obtain ⟨p, f, hp, hp2, h | h⟩ := h
  · exact ⟨p, f, hp, hp2, Or.inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)⟩
  · exact ⟨p, f, hp, hp2, Or.inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h)⟩

@[expose] def IsL3OddSD (K : Type) [Group K] : Prop :=
  ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧
    ((p ^ f % 4 = 3 ∧ CFSG.Blueprint.LieModel K .PSL 3 p f) ∨ (p ^ f % 4 = 1 ∧ CFSG.Blueprint.LieModel K .PSU 3 p f))

theorem IsL3OddSD.isL3Odd {K : Type} [Group K] (h : IsL3OddSD K) : IsL3Odd K := by
  obtain ⟨p, f, hp, hp2, ⟨-, h⟩ | ⟨-, h⟩⟩ := h
  · exact ⟨p, f, hp, hp2, Or.inl h⟩
  · exact ⟨p, f, hp, hp2, Or.inr h⟩

theorem isL3OddSD_equiv {K K' : Type} [Group K] [Group K'] (e : K ≃* K') (h : IsL3OddSD K) : IsL3OddSD K' := by
  obtain ⟨p, f, hp, hp2, ⟨h4, h⟩ | ⟨h4, h⟩⟩ := h
  · exact ⟨p, f, hp, hp2, Or.inl ⟨h4, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h⟩⟩
  · exact ⟨p, f, hp, hp2, Or.inr ⟨h4, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e h⟩⟩

theorem isL3OddSD_center_map (φ : J ≃* J') {I : Subgroup J} (h : IsL3OddSD (↥I ⧸ center ↥I)) :
    IsL3OddSD (↥(I.map φ.toMonoidHom) ⧸ center ↥(I.map φ.toMonoidHom)) :=
  isL3OddSD_equiv (CFSG.ComponentClassification.UnbalancingLocal.centerQuotientCongr (φ.subgroupMap I)) h

@[expose] def P151Concl (v : J) (A : Subgroup J) (a : J) : Prop :=
  ∃ s : J, s * s = 1 ∧ s * a = a * s ∧ (∃ g : J, g * v * g⁻¹ = s) ∧ (∃ g : J, g * v * g⁻¹ = a * s) ∧
    ∃ I : Subgroup J, IsCompIn (centralizer ({a} : Set J) ⊓ centralizer ({s} : Set J)) I ∧
      IsL3OddSD (↥I ⧸ center ↥I) ∧ (∀ z ∈ I, (∀ l ∈ I, z * l = l * z) → z * z = 1 → z = 1) ∧
      ∃ e₁ e₂ : J, e₁ ∈ I ∧ e₂ ∈ I ∧ e₁ * e₁ = 1 ∧ e₂ * e₂ = 1 ∧ e₁ * e₂ = e₂ * e₁ ∧
        e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ ≠ e₂ ∧
        (∃ g : J, g * v * g⁻¹ = a * e₁) ∧ (∃ g : J, g * v * g⁻¹ = a * e₂) ∧
        (∃ g : J, g * v * g⁻¹ = a * (e₁ * e₂)) ∧ ∃ g : J, g * e₁ * g⁻¹ ∈ A ∧ g * e₂ * g⁻¹ ∈ A

theorem conj_symm_apply (φ : J ≃* J') {g' v' : J'} {v : J} (hv : φ v = v') :
    φ.symm g' * v * (φ.symm g')⁻¹ = φ.symm (g' * v' * g'⁻¹) := by
  rw [← hv]
  simp

theorem P151Concl.of_mulEquiv (φ : J ≃* J') {v a : J} {A : Subgroup J}
    (h : P151Concl (φ v) (A.map φ.toMonoidHom) (φ a)) : P151Concl v A a := by
  obtain ⟨s', hss, hsa, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩, I', hI', hT', hZ', e₁', e₂', he₁I, he₂I, he₁₁, he₂₂, he₁₂, he₁1,
    he₂1, he₁₂', ⟨g₃, hg₃⟩, ⟨g₄, hg₄⟩, ⟨g₅, hg₅⟩, g₆, hg₆₁, hg₆₂⟩ := h
  have hφa : φ.symm (φ a) = a := φ.symm_apply_apply a
  have hφv : φ v = φ v := rfl
  refine ⟨φ.symm s', ?_, ?_, ⟨φ.symm g₁, ?_⟩, ⟨φ.symm g₂, ?_⟩, I'.map φ.symm.toMonoidHom, ?_,
    isL3OddSD_center_map φ.symm hT', ?_,
    φ.symm e₁', φ.symm e₂', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨φ.symm g₃, ?_⟩, ⟨φ.symm g₄, ?_⟩, ⟨φ.symm g₅, ?_⟩,
    φ.symm g₆, ?_, ?_⟩
  · rw [← map_mul, hss, map_one]
  · apply φ.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hsa
  · rw [conj_symm_apply φ hφv, hg₁]
  · rw [conj_symm_apply φ hφv, hg₂, map_mul, hφa]
  · have h1 := isCompIn_map φ.symm hI'
    rwa [Subgroup.map_inf_eq _ _ φ.symm.toMonoidHom φ.symm.injective, centralizer_map_mulEquiv,
      centralizer_map_mulEquiv, hφa] at h1
  · rintro z ⟨z', hz', rfl⟩ hzc hzz
    have hz'c : ∀ l ∈ I', z' * l = l * z' := by
      intro l hl
      have := hzc (φ.symm l) ⟨l, hl, rfl⟩
      apply φ.symm.injective
      simpa using this
    have hz'z' : z' * z' = 1 := by
      apply φ.symm.injective
      simpa using hzz
    rw [hZ' z' hz' hz'c hz'z']
    simp
  · exact ⟨e₁', he₁I, rfl⟩
  · exact ⟨e₂', he₂I, rfl⟩
  · rw [← map_mul, he₁₁, map_one]
  · rw [← map_mul, he₂₂, map_one]
  · rw [← map_mul, ← map_mul, he₁₂]
  · intro h1
    apply he₁1
    simpa using congrArg φ h1
  · intro h1
    apply he₂1
    simpa using congrArg φ h1
  · intro h1
    apply he₁₂'
    simpa using congrArg φ h1
  · rw [conj_symm_apply φ hφv, hg₃, map_mul, hφa]
  · rw [conj_symm_apply φ hφv, hg₄, map_mul, hφa]
  · rw [conj_symm_apply φ hφv, hg₅, map_mul, map_mul, hφa]
  · have := (Subgroup.mem_map_equiv (f := φ)).1 hg₆₁
    simpa using this
  · have := (Subgroup.mem_map_equiv (f := φ)).1 hg₆₂
    simpa using this

@[expose] def P151Fact (J : Type) [Group J] : Prop :=
  ∀ (v : J) (L A : Subgroup J), v * v = 1 → v ≠ 1 → IsCompIn (centralizer ({v} : Set J)) L →
    (∃ z₀ : J, ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z * z = 1 → z = 1 ∨ z = z₀) →
    CFSG.IsElementaryAbelian 2 ↥A → Nat.card ↥A = 8 → A ≤ L →
    ∀ a ∈ A, a ≠ 1 → a ≠ v → P151Concl v A a

theorem isElementaryAbelian_map (φ : J ≃* J') {A : Subgroup J} (hA : CFSG.IsElementaryAbelian 2 ↥A) :
    CFSG.IsElementaryAbelian 2 ↥(A.map φ.toMonoidHom) := by
  refine WeakSigGen.isElementaryAbelian_of_forall ?_ ?_
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨w, hw, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, ea_comm hA hu hw]
  · rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ea_sq hA hu, map_one]

theorem P151Fact.of_mulEquiv (φ : J ≃* J') (h : P151Fact J') : P151Fact J := by
  intro v L A hvv hv1 hL hZ hA hA8 hAL a haA ha1 hav
  apply P151Concl.of_mulEquiv φ
  obtain ⟨z₀, hz₀⟩ := hZ
  refine h (φ v) (L.map φ.toMonoidHom) (A.map φ.toMonoidHom) (by rw [← map_mul, hvv, map_one]) ?_ ?_
    ⟨φ z₀, ?_⟩ (isElementaryAbelian_map φ hA) ?_ (Subgroup.map_mono hAL) (φ a) ⟨a, haA, rfl⟩ ?_ ?_
  · intro h1
    exact hv1 (φ.injective (by rw [h1, map_one]))
  · have := isCompIn_map φ hL
    rwa [centralizer_map_mulEquiv] at this
  · rintro _ ⟨z, hz, rfl⟩ hzc hzz
    have hzc' : ∀ l ∈ L, z * l = l * z := by
      intro l hl
      have := hzc (φ l) ⟨l, hl, rfl⟩
      apply φ.injective
      simpa using this
    have hzz' : z * z = 1 := by
      apply φ.injective
      simpa using hzz
    rcases hz₀ z hz hzc' hzz' with h1 | h1
    · left; simp [h1]
    · right; simp [h1]
  · rw [← hA8]
    exact Nat.card_congr (φ.subgroupMap A).toEquiv.symm
  · intro h1
    exact ha1 (φ.injective (by simpa using h1))
  · intro h1
    exact hav (φ.injective (by simpa using h1))

end Concl

section Frame

variable {F : Type} [Field F] {P : Type} [Group P]

structure Frame5 (S N : Subgroup (GL (Fin 5) F)) (π : ↥S →* P) : Prop extends Model S π where
  le : S ≤ N
  detN : ∀ n ∈ N, (n : Matrix (Fin 5) (Fin 5) F).det = 1 → n ∈ S
  perm : ∀ σ : Equiv.Perm (Fin 5), permGL5 σ ∈ N
  sgnN : ∀ (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1), sgnGL ε hε ∈ N
  adj : ∀ n ∈ N, ∃ δ ∈ N, (δ : Matrix (Fin 5) (Fin 5) F).IsDiag ∧
    (n : Matrix (Fin 5) (Fin 5) F).det * (δ : Matrix (Fin 5) (Fin 5) F).det = 1
  lift : ∀ D : Subgroup P, CFSG.IsElementaryAbelian 2 ↥D → ∃ (B : GL (Fin 5) F) (ρ : ↥D →* ↥S),
    B ∈ N ∧ (∀ d, π (ρ d) = d) ∧
      ∀ d, ((B⁻¹ * ((ρ d : ↥S) : GL (Fin 5) F) * B : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F).IsDiag
  quasi3 : ∀ I : Finset (Fin 5), I.card = 3 → CFSG.IsQuasisimple ↥(blkP S π I)
  type3 : ∀ I : Finset (Fin 5), I.card = 3 → IsL3OddSD (↥(blkP S π I) ⧸ center ↥(blkP S π I))

namespace Frame5

variable {S N : Subgroup (GL (Fin 5) F)} {π : ↥S →* P} (M : Frame5 S N π)
include M

theorem exists_diag_mul_mem {n : GL (Fin 5) F} (hn : n ∈ N) :
    ∃ δ : GL (Fin 5) F, (δ : Matrix (Fin 5) (Fin 5) F).IsDiag ∧ n * δ ∈ S := by
  obtain ⟨δ, hδN, hδd, hdet⟩ := M.adj n hn
  refine ⟨δ, hδd, M.detN _ (N.mul_mem hn hδN) ?_⟩
  rw [Units.val_mul, Matrix.det_mul, hdet]

theorem exists_perm_conj (σ : Equiv.Perm (Fin 5)) :
    ∃ w : ↥S, ∀ (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1),
      (w : GL (Fin 5) F) * sgnGL ε hε * (w : GL (Fin 5) F)⁻¹ =
        sgnGL (ε ∘ σ.symm) (fun i => hε (σ.symm i)) := by
  obtain ⟨δ, hδd, hδS⟩ := M.exists_diag_mul_mem (M.perm σ)
  refine ⟨⟨_, hδS⟩, fun ε hε => ?_⟩
  apply Units.ext
  have hcomm : (δ : Matrix (Fin 5) (Fin 5) F) * Matrix.diagonal ε =
      Matrix.diagonal ε * (δ : Matrix (Fin 5) (Fin 5) F) :=
    commute_of_isDiag hδd (Matrix.isDiag_diagonal ε)
  have hδinv : (δ : Matrix (Fin 5) (Fin 5) F) * ((δ⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul, _root_.mul_inv_rev, coe_sgnGL]
  rw [← permGL5_conj_diagonal σ ε]
  calc ((permGL5 σ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) * (δ : Matrix (Fin 5) (Fin 5) F) *
        Matrix.diagonal ε * (((δ⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *
          (((permGL5 σ)⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))
      = ((permGL5 σ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) * Matrix.diagonal ε *
          ((δ : Matrix (Fin 5) (Fin 5) F) * ((δ⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) *
          (((permGL5 σ)⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
        rw [Matrix.mul_assoc ((permGL5 σ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F), hcomm]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hδinv, Matrix.mul_one]

theorem exists_conj_sgn (D : Subgroup P) (hD : CFSG.IsElementaryAbelian 2 ↥D) :
    ∃ g : P, ∀ d ∈ D, ∃ (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1),
      g * d * g⁻¹ = π (M.sgnS ε hε hdet) := by
  obtain ⟨B, ρ, hBN, hρπ, hdiag⟩ := M.lift D hD
  obtain ⟨δ, hδd, hBδS⟩ := M.exists_diag_mul_mem hBN
  set B' : ↥S := ⟨B * δ, hBδS⟩ with hB'
  refine ⟨(π B')⁻¹, fun d hd => ?_⟩
  set X : GL (Fin 5) F := B⁻¹ * ((ρ ⟨d, hd⟩ : ↥S) : GL (Fin 5) F) * B with hX
  have hXd : (X : Matrix (Fin 5) (Fin 5) F).IsDiag := hdiag ⟨d, hd⟩
  have hconj : ((B'⁻¹ * ρ ⟨d, hd⟩ * B' : ↥S) : GL (Fin 5) F) = X := by
    have hc : X * δ = δ * X := Units.ext (commute_of_isDiag hXd hδd)
    simp only [hB', Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev]
    calc δ⁻¹ * B⁻¹ * ((ρ ⟨d, hd⟩ : ↥S) : GL (Fin 5) F) * (B * δ) = δ⁻¹ * (X * δ) := by
          rw [hX]; group
      _ = X := by rw [hc]; group
  have hρsq : ρ ⟨d, hd⟩ * ρ ⟨d, hd⟩ = 1 := by
    rw [← map_mul]
    have : (⟨d, hd⟩ : ↥D) * ⟨d, hd⟩ = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD _
    rw [this, map_one]
  have hXsq : X * X = 1 := by
    have h := congrArg (fun z : ↥S => (z : GL (Fin 5) F)) hρsq
    simp only [Subgroup.coe_mul, Subgroup.coe_one] at h
    rw [hX]
    calc B⁻¹ * ((ρ ⟨d, hd⟩ : ↥S) : GL (Fin 5) F) * B * (B⁻¹ * ((ρ ⟨d, hd⟩ : ↥S) : GL (Fin 5) F) * B) =
          B⁻¹ * (((ρ ⟨d, hd⟩ : ↥S) : GL (Fin 5) F) * ((ρ ⟨d, hd⟩ : ↥S) : GL (Fin 5) F)) * B := by group
      _ = 1 := by rw [h]; group
  set ε : Fin 5 → F := fun i => (X : Matrix (Fin 5) (Fin 5) F) i i with hε
  have hεsq : ∀ i, ε i * ε i = 1 := by
    intro i
    have h := congrArg (fun g : GL (Fin 5) F => (g : Matrix (Fin 5) (Fin 5) F) i i) hXsq
    simp only [Units.val_mul, Units.val_one, Matrix.one_apply_eq] at h
    rw [mul_apply_self_of_isDiag hXd] at h
    exact h
  have hXS : X ∈ S := by
    rw [← hconj]
    exact (B'⁻¹ * ρ ⟨d, hd⟩ * B').2
  have hεdet : ∏ i, ε i = 1 := by
    have := M.det X hXS
    rw [det_of_isDiag hXd] at this
    exact this
  refine ⟨ε, hεsq, hεdet, ?_⟩
  have hXε : (⟨X, hXS⟩ : ↥S) = M.sgnS ε hεsq hεdet := by
    apply Subtype.ext
    apply Units.ext
    show (X : Matrix (Fin 5) (Fin 5) F) = Matrix.diagonal ε
    exact hXd.diagonal_diag.symm
  calc (π B')⁻¹ * d * (π B')⁻¹⁻¹ = π (B'⁻¹ * ρ ⟨d, hd⟩ * B') := by
        rw [map_mul, map_mul, map_inv, hρπ]; group
    _ = π ⟨X, hXS⟩ := by congr 1; exact Subtype.ext hconj
    _ = _ := by rw [hXε]

theorem exists_perm_conjP (σ : Equiv.Perm (Fin 5)) :
    ∃ g : P, ∀ (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1)
      (hdet' : ∏ i, (ε ∘ σ.symm) i = 1),
      g * π (M.sgnS ε hε hdet) * g⁻¹ = π (M.sgnS (ε ∘ σ.symm) (fun i => hε (σ.symm i)) hdet') := by
  obtain ⟨w, hw⟩ := M.exists_perm_conj σ
  refine ⟨π w, fun ε hε hdet hdet' => ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact hw ε hε

theorem sgnS_congr {ε ε' : Fin 5 → F} (h : ε = ε') (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1)
    (hε' : ∀ i, ε' i * ε' i = 1) (hdet' : ∏ i, ε' i = 1) : M.sgnS ε hε hdet = M.sgnS ε' hε' hdet' := by
  subst h
  rfl

theorem exists_conj_std_E {E : Subgroup P} (hE : CFSG.IsElementaryAbelian 2 ↥E) {v : P} (hvE : v ∈ E)
    (hv1 : v ≠ 1) :
    ∃ g : P, ∃ k, ∃ hk : k = 2 ∨ k = 4,
      g * v * g⁻¹ = π (M.sgnS (stdSign k) (stdSign_sq k) (prod_stdSign hk)) ∧
      ∀ e ∈ E, ∃ (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1),
        g * e * g⁻¹ = π (M.sgnS ε hε hdet) := by
  obtain ⟨g₁, hg₁⟩ := M.exists_conj_sgn E hE
  obtain ⟨εv, hεv, hdetv, hv⟩ := hg₁ v hvE
  have hne : negCount εv ≠ 0 := by
    intro h0
    apply hv1
    have h1 := eq_one_of_negCount_eq_zero hεv h0
    have hs1 : M.sgnS εv hεv hdetv = 1 := by
      apply Subtype.ext
      apply Units.ext
      show Matrix.diagonal εv = 1
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      exact h1 i
    rw [hs1, map_one] at hv
    calc v = g₁⁻¹ * (g₁ * v * g₁⁻¹) * g₁ := by group
      _ = 1 := by rw [hv]; group
  have hev := even_negCount M.two hεv hdetv
  have hle := negCount_le εv
  have hk : negCount εv = 2 ∨ negCount εv = 4 := by
    obtain ⟨m, hm⟩ := hev
    omega
  have hstdk : negCount εv = negCount (stdSign (F := F) (negCount εv)) := by
    rw [negCount_stdSign M.two hle]
  obtain ⟨σ, hσ⟩ := exists_perm_of_negCount hεv (stdSign_sq (negCount εv)) hstdk
  obtain ⟨g₂, hg₂⟩ := M.exists_perm_conjP σ
  refine ⟨g₂ * g₁, negCount εv, hk, ?_, ?_⟩
  · have hdet' : ∏ i, (εv ∘ σ.symm) i = 1 := by
      rw [show (∏ i, (εv ∘ σ.symm) i) = ∏ i, εv i from Equiv.prod_comp σ.symm εv]
      exact hdetv
    calc g₂ * g₁ * v * (g₂ * g₁)⁻¹ = g₂ * (g₁ * v * g₁⁻¹) * g₂⁻¹ := by group
      _ = g₂ * π (M.sgnS εv hεv hdetv) * g₂⁻¹ := by rw [hv]
      _ = π (M.sgnS (εv ∘ σ.symm) (fun i => hεv (σ.symm i)) hdet') := hg₂ εv hεv hdetv hdet'
      _ = _ := by
        congr 1
        exact M.sgnS_congr (funext fun i => (hσ i).symm) _ _ _ _
  · intro e he
    obtain ⟨ε, hε, hdet, he'⟩ := hg₁ e he
    have hdet' : ∏ i, (ε ∘ σ.symm) i = 1 := by
      rw [show (∏ i, (ε ∘ σ.symm) i) = ∏ i, ε i from Equiv.prod_comp σ.symm ε]
      exact hdet
    refine ⟨ε ∘ σ.symm, fun i => hε (σ.symm i), hdet', ?_⟩
    calc g₂ * g₁ * e * (g₂ * g₁)⁻¹ = g₂ * (g₁ * e * g₁⁻¹) * g₂⁻¹ := by group
      _ = _ := by rw [he']; exact hg₂ ε hε hdet hdet'

theorem map_ker_blk2_le (Y : Subgroup ↥S)
    (hYX : Y ≤ centralizer ({M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl))} : Set ↥S)) :
    (M.blk2Hom Y hYX).ker.map (π.comp Y.subtype) ≤ blkP S π {2, 3, 4} := by
  rw [blkP, ← Subgroup.map_map]
  refine Subgroup.map_mono ?_
  rintro _ ⟨y, hy, rfl⟩
  have hy' : M.blk2Hom Y hYX y = 1 := hy
  rw [Model.blk2Hom_apply] at hy'
  have hyX : (y : ↥S) ∈ centralizer ({M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl))} :
      Set ↥S) := hYX y.2
  have e00 : ((((y : ↥S) : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) 0 0 = 1 := by
    simpa [blk2] using congrFun (congrFun hy' 0) 0
  have e01 : ((((y : ↥S) : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) 0 1 = 0 := by
    simpa [blk2] using congrFun (congrFun hy' 0) 1
  have e10 : ((((y : ↥S) : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) 1 0 = 0 := by
    simpa [blk2] using congrFun (congrFun hy' 1) 0
  have e11 : ((((y : ↥S) : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) 1 1 = 1 := by
    simpa [blk2] using congrFun (congrFun hy' 1) 1
  have hz : ∀ i j : Fin 5, stdSign (F := F) 2 i ≠ stdSign 2 j →
      ((((y : ↥S) : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) i j = 0 :=
    fun i j hij => M.entry_eq_zero _ _ hyX hij
  simp only [Subgroup.mem_comap, Subgroup.coe_subtype, mem_blkGL]
  intro i j hij
  by_cases hs : stdSign (F := F) 2 i = stdSign 2 j
  · have hboth : i.val < 2 ∧ j.val < 2 := by
      rcases hij with hi | hj
      · have hi' := val_lt_two_of_not_mem hi
        exact ⟨hi', val_lt_two_of_sign M.two hi' hs⟩
      · have hj' := val_lt_two_of_not_mem hj
        exact ⟨val_lt_two_of_sign M.two hj' hs.symm, hj'⟩
    rcases lt_two_cases hboth.1 with rfl | rfl <;> rcases lt_two_cases hboth.2 with rfl | rfl
    · rw [e00, Matrix.one_apply_eq]
    · rw [e01, Matrix.one_apply_ne (by decide)]
    · rw [e10, Matrix.one_apply_ne (by decide)]
    · rw [e11, Matrix.one_apply_eq]
  · have hne : i ≠ j := fun h => hs (h ▸ rfl)
    rw [hz i j hs, Matrix.one_apply_ne hne]

theorem false_of_two_mem [Finite P] {L : Subgroup P}
    (hL : IsCompIn (centralizer ({π (M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl)))} :
      Set P)) L)
    (htL : π (M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl))) ∈ L)
    {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1) (hε0 : ε 0 = 1)
    (huL : π (M.sgnS ε hε hdet) ∈ L)
    (hnc : ¬ ∀ l ∈ L, π (M.sgnS ε hε hdet) * l = l * π (M.sgnS ε hε hdet)) : False := by
  set t := M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl)) with ht
  set X := centralizer ({t} : Set ↥S) with hX
  have hC : centralizer ({π t} : Set P) = (π.comp X.subtype).range := by
    rw [M.centralizer_proj (M.sgnS_sq _ _ _), MonoidHom.range_comp, Subgroup.range_subtype]
  have hq := isQuasisimple_of_isCompIn hL
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hq.1
  set ψ : ↥X →* Fˣ := (Matrix.detMonoidHom.comp (M.blk2Hom X le_rfl)).toHomUnits with hψ
  have h1 : L ≤ ψ.ker.map (π.comp X.subtype) :=
    le_map_ker_of_perfect _ ψ (by rw [← hC]; exact hL.1) hperf
  set Y : Subgroup ↥S := ψ.ker.map X.subtype with hY
  have hYX : Y ≤ X := Subgroup.map_subtype_le _
  have hLY : L ≤ Y.map π := by
    rw [hY, Subgroup.map_map]
    exact h1
  have hLY' : L ≤ (π.comp Y.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hLY
  set u := M.sgnS ε hε hdet with hu
  have huY : u ∈ Y := M.mem_of_sq (M.sgnS_sq _ _ _) (hLY huL)
  have hdetY : (blk2 (((u : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)).det = 1 := by
    obtain ⟨x, hx, hxu⟩ := huY
    have hx' : ψ x = 1 := hx
    have := congrArg Units.val hx'
    rw [← hxu]
    exact this
  have hε1 : ε 1 = 1 := by
    have : (blk2 (((u : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)).det = ε 0 * ε 1 := by
      rw [hu, Model.coe_sgnS, coe_sgnGL, blk2, Matrix.det_fin_two_of]
      simp
    rw [this, hε0, one_mul] at hdetY
    exact hdetY
  have hblk : M.blk2Hom Y hYX ⟨u, huY⟩ = 1 := by
    rw [Model.blk2Hom_apply]
    show blk2 ((((M.sgnS ε hε hdet : ↥S) : GL (Fin 5) F)) : Matrix (Fin 5) (Fin 5) F) = 1
    rw [Model.coe_sgnS, coe_sgnGL]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [blk2, hε0, hε1]
  have h2 := le_map_ker_of_quasisimple (π.comp Y.subtype) (M.blk2Hom Y hYX) hq hLY' hblk huL hnc
  have hle := h2.trans (M.map_ker_blk2_le Y hYX)
  have htB := hle htL
  have htmem := M.mem_of_sq (M.sgnS_sq _ _ _) htB
  have h00 : ((sgnGL (stdSign (F := F) 2) (stdSign_sq 2) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) 0 0 =
      (1 : Matrix (Fin 5) (Fin 5) F) 0 0 := htmem 0 0 (Or.inl (by decide))
  rw [coe_sgnGL, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h00
  have : stdSign (F := F) 2 0 = -1 := stdSign_two_lo (by decide)
  rw [this] at h00
  apply M.two
  linear_combination -h00

theorem eq_blk_of_four [Finite P] {L : Subgroup P}
    (hL : IsCompIn (centralizer ({π (M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4))} : Set P)) L) :
    L = blkP S π (Finset.univ.erase 4) := by
  set t := M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4) with ht
  set X := centralizer ({t} : Set ↥S) with hX
  have hC : centralizer ({π t} : Set P) = (π.comp X.subtype).range := by
    rw [M.centralizer_proj (M.sgnS_sq _ _ _), MonoidHom.range_comp, Subgroup.range_subtype]
  have hq := isQuasisimple_of_isCompIn hL
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hq.1
  have hLB : L ≤ blkP S π (Finset.univ.erase 4) := by
    have h1 := le_map_ker_of_perfect (π.comp X.subtype) (M.entryHom 4) (by rw [← hC]; exact hL.1) hperf
    rw [blkP, ← M.map_ker_entryHom 4, Subgroup.map_map]
    exact h1
  exact eq_of_isCompIn_le hL (M.isCompIn_blk 4) hLB

theorem apply_four_of_mem_blk {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1)
    (h : π (M.sgnS ε hε hdet) ∈ blkP S π (Finset.univ.erase 4)) : ε 4 = 1 := by
  have hm := M.mem_of_sq (M.sgnS_sq _ _ _) h
  have h44 : ((sgnGL ε hε : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) 4 4 =
      (1 : Matrix (Fin 5) (Fin 5) F) 4 4 := hm 4 4 (Or.inl (by simp))
  rw [coe_sgnGL, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h44
  exact h44

theorem exists_conj_oneAt (m : Fin 5) :
    ∃ h : P, h * π (M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4)) * h⁻¹ =
      π (M.sgnS (oneAt m) (oneAt_sq m) (prod_oneAt m)) := by
  obtain ⟨h, hh⟩ := M.exists_perm_conjP (Equiv.swap 4 m)
  have hdet' : ∏ i, (oneAt (F := F) 4 ∘ (Equiv.swap 4 m).symm) i = 1 := by
    rw [show (∏ i, (oneAt (F := F) 4 ∘ (Equiv.swap 4 m).symm) i) = ∏ i, oneAt (F := F) 4 i from
      Equiv.prod_comp (Equiv.swap 4 m).symm _]
    exact prod_oneAt 4
  refine ⟨h, (hh (oneAt 4) (oneAt_sq 4) (prod_oneAt 4) hdet').trans ?_⟩
  congr 1
  refine M.sgnS_congr ?_ _ _ _ _
  funext i
  simp only [Function.comp_apply, Equiv.symm_swap, oneAt]
  by_cases him : i = m
  · subst him; simp
  · by_cases hi4 : i = 4
    · subst hi4
      rw [Equiv.swap_apply_left]
      simp [him, Ne.symm him]
    · rw [Equiv.swap_apply_of_ne_of_ne hi4 him]
      simp [him, hi4]

theorem sgnOn_inj {D D' : Finset (Fin 5)} (hD : ∏ i, sgnOn (F := F) D i = 1) (hD' : ∏ i, sgnOn (F := F) D' i = 1)
    (h : π (M.sgnS (sgnOn D) (sgnOn_sq D) hD) = π (M.sgnS (sgnOn D') (sgnOn_sq D') hD')) : D = D' := by
  have h1 := M.eq_of_sq (M.sgnS_sq _ _ _) (M.sgnS_sq _ _ _) h
  have h2 : ∀ x, sgnOn (F := F) D x = sgnOn D' x := by
    intro x
    have := congrArg (fun c : ↥S => ((c : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) x x) h1
    simpa [Model.coe_sgnS, coe_sgnGL] using this
  ext x
  by_contra hx
  have hneq := h2 x
  have hm1 : (-1 : F) ≠ 1 := by
    intro h
    apply M.two
    linear_combination -h
  by_cases hxD : x ∈ D
  · have hxD' : x ∉ D' := fun h => hx ⟨fun _ => h, fun _ => hxD⟩
    rw [sgnOn_apply_mem hxD, sgnOn_apply_not_mem hxD'] at hneq
    exact hm1 hneq
  · have hxD' : x ∈ D' := by
      by_contra h'
      exact hx ⟨fun h => absurd h hxD, fun h => absurd h h'⟩
    rw [sgnOn_apply_not_mem hxD, sgnOn_apply_mem hxD'] at hneq
    exact hm1 hneq.symm

theorem centralizer_inf_proj {e d : ↥S} (he : e * e = 1) (hd : d * d = 1) :
    centralizer ({π e} : Set P) ⊓ centralizer ({π d} : Set P) =
      (centralizer ({e} : Set ↥S) ⊓ centralizer ({d} : Set ↥S)).map π := by
  ext y
  constructor
  · rintro ⟨hy1, hy2⟩
    have hy1' : y ∈ centralizer ({π e} : Set P) := hy1
    rw [M.centralizer_proj he] at hy1'
    obtain ⟨c, hc1, rfl⟩ := hy1'
    have hy2' : π c ∈ centralizer ({π d} : Set P) := hy2
    refine ⟨c, ⟨hc1, ?_⟩, rfl⟩
    show c ∈ centralizer ({d} : Set ↥S)
    exact Subgroup.mem_centralizer_singleton_iff.2
      (M.comm_of_comm hd (Subgroup.mem_centralizer_singleton_iff.1 hy2'))
  · rintro ⟨c, ⟨hc1, hc2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · show π c ∈ centralizer ({π e} : Set P)
      rw [M.centralizer_proj he]
      exact ⟨c, hc1, rfl⟩
    · show π c ∈ centralizer ({π d} : Set P)
      rw [M.centralizer_proj hd]
      exact ⟨c, hc2, rfl⟩

theorem isCompIn_blk_pair {i j : Fin 5} (hij : i ≠ j) {ε δ : Fin 5 → F} (hε : ∀ x, ε x * ε x = 1)
    (hdet : ∏ x, ε x = 1) (hδ : ∀ x, δ x * δ x = 1) (hdetδ : ∏ x, δ x = 1)
    (hsi : ∀ x, x ≠ i → ε x ≠ ε i ∨ δ x ≠ δ i) (hsj : ∀ x, x ≠ j → ε x ≠ ε j ∨ δ x ≠ δ j)
    (hc : ∀ x y, x ≠ i → x ≠ j → y ≠ i → y ≠ j → ε x = ε y ∧ δ x = δ y) :
    IsCompIn (centralizer ({π (M.sgnS ε hε hdet)} : Set P) ⊓ centralizer ({π (M.sgnS δ hδ hdetδ)} : Set P))
      (blkP S π (Finset.univ \ {i, j})) := by
  set e := M.sgnS ε hε hdet with he
  set d := M.sgnS δ hδ hdetδ with hd
  set X : Subgroup ↥S := centralizer ({e} : Set ↥S) ⊓ centralizer ({d} : Set ↥S) with hX
  have hC := M.centralizer_inf_proj (M.sgnS_sq ε hε hdet) (M.sgnS_sq δ hδ hdetδ)
  have hzero : ∀ c ∈ X, ∀ t : Fin 5, (t = i ∨ t = j) → ∀ x, x ≠ t →
      (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) t x = 0 ∧
        (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) x t = 0 := by
    intro c hcX t ht x hx
    have hs : ε x ≠ ε t ∨ δ x ≠ δ t := by
      rcases ht with rfl | rfl
      · exact hsi x hx
      · exact hsj x hx
    rcases hs with h | h
    · exact ⟨M.entry_eq_zero hε hdet hcX.1 (Ne.symm h), M.entry_eq_zero hε hdet hcX.1 h⟩
    · exact ⟨M.entry_eq_zero hδ hdetδ hcX.2 (Ne.symm h), M.entry_eq_zero hδ hdetδ hcX.2 h⟩
  set φi := entryHomOn X i (fun c hcX x hx => (hzero c hcX i (Or.inl rfl) x hx).1) with hφi
  set φj := entryHomOn X j (fun c hcX x hx => (hzero c hcX j (Or.inr rfl) x hx).1) with hφj
  set φ : ↥X →* Fˣ × Fˣ := φi.prod φj with hφ
  have hker : φ.ker.map X.subtype = (blkGL (Finset.univ \ {i, j})).comap S.subtype := by
    ext c
    constructor
    · rintro ⟨c', hc', rfl⟩
      have hc'' : φ c' = 1 := hc'
      have hi1 : ((((c' : ↥X) : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i = 1 := by
        have := congrArg (fun z => ((z.1 : Fˣ) : F)) hc''
        simpa [hφ, hφi, entryHomOn_apply] using this
      have hj1 : ((((c' : ↥X) : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) j j = 1 := by
        have := congrArg (fun z => ((z.2 : Fˣ) : F)) hc''
        simpa [hφ, hφj, entryHomOn_apply] using this
      simp only [Subgroup.mem_comap, Subgroup.coe_subtype, mem_blkGL, Finset.mem_sdiff,
        Finset.mem_univ, true_and, not_not, Finset.mem_insert, Finset.mem_singleton]
      intro x y hxy
      by_cases hxyeq : x = y
      · subst hxyeq
        rcases hxy with hx | hx <;> rcases hx with rfl | rfl
        all_goals first | rw [hi1, Matrix.one_apply_eq] | rw [hj1, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne hxyeq]
        rcases hxy with hx | hy
        · exact (hzero c' c'.2 x hx y (Ne.symm hxyeq)).1
        · exact (hzero c' c'.2 y hy x hxyeq).2
    · intro hcb
      have hcb' : ∀ x y, (x = i ∨ x = j ∨ y = i ∨ y = j) →
          (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) x y = (1 : Matrix (Fin 5) (Fin 5) F) x y := by
        intro x y hxy
        refine hcb x y ?_
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not, Finset.mem_insert,
          Finset.mem_singleton]
        tauto
      have hcomm : ∀ (η : Fin 5 → F) (hη : ∀ x, η x * η x = 1),
          (∀ x y, x ≠ i → x ≠ j → y ≠ i → y ≠ j → η x = η y) →
          (c : GL (Fin 5) F) * sgnGL η hη = sgnGL η hη * (c : GL (Fin 5) F) := by
        intro η hη hηc
        refine comm_of_entry hη fun x y hxy => ?_
        have hne : x ≠ y := fun h => hxy (h ▸ rfl)
        by_cases hout : x = i ∨ x = j ∨ y = i ∨ y = j
        · rw [hcb' x y hout, Matrix.one_apply_ne hne]
        · push Not at hout
          exact absurd (hηc x y hout.1 hout.2.1 hout.2.2.1 hout.2.2.2) hxy
      have hcX : c ∈ X := by
        refine ⟨?_, ?_⟩
        · show c ∈ centralizer ({e} : Set ↥S)
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply Subtype.ext
          exact hcomm ε hε (fun x y hx1 hx2 hy1 hy2 => (hc x y hx1 hx2 hy1 hy2).1)
        · show c ∈ centralizer ({d} : Set ↥S)
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply Subtype.ext
          exact hcomm δ hδ (fun x y hx1 hx2 hy1 hy2 => (hc x y hx1 hx2 hy1 hy2).2)
      refine ⟨⟨c, hcX⟩, (MonoidHom.mem_ker).2 ?_, rfl⟩
      rw [hφ, MonoidHom.prod_apply, Prod.mk_eq_one]
      constructor
      · apply Units.ext
        rw [hφi, entryHomOn_apply, Units.val_one]
        show (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) i i = 1
        rw [hcb' i i (Or.inl rfl), Matrix.one_apply_eq]
      · apply Units.ext
        rw [hφj, entryHomOn_apply, Units.val_one]
        show (((c : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) j j = 1
        rw [hcb' j j (Or.inr (Or.inl rfl)), Matrix.one_apply_eq]
  have hB : blkP S π (Finset.univ \ {i, j}) = φ.ker.map (π.comp X.subtype) := by
    rw [blkP, ← hker, Subgroup.map_map]
  have hCX : centralizer ({π e} : Set P) ⊓ centralizer ({π d} : Set P) = (π.comp X.subtype).range := by
    rw [hC, MonoidHom.range_comp, Subgroup.range_subtype]
  have hle : blkP S π (Finset.univ \ {i, j}) ≤ centralizer ({π e} : Set P) ⊓ centralizer ({π d} : Set P) := by
    rw [hB, hCX]
    exact Subgroup.map_le_range _ _
  refine ⟨hle, ?_, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
      (M.quasi3 _ (card_compl_pair hij))
  · refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : P) ∈ (π.comp X.subtype).range := hCX ▸ g.2
    obtain ⟨y, hy⟩ := hg
    rw [hB] at hn ⊢
    obtain ⟨k, hk, hkn⟩ := hn
    have hk' : φ k = 1 := hk
    refine ⟨y * k * y⁻¹, (MonoidHom.mem_ker).2 ?_, ?_⟩
    · rw [map_mul, map_mul, hk', mul_one, map_inv, mul_inv_cancel]
    · simp only [map_mul, map_inv, hy, hkn, Subgroup.coe_mul, Subgroup.coe_inv]

theorem center_blk3 {U : Finset (Fin 5)} (hU : U.card = 3) {z : P} (hz : z ∈ blkP S π U)
    (hc : ∀ l ∈ blkP S π U, z * l = l * z) (hzz : z * z = 1) : z = 1 := by
  obtain ⟨z', hz'z', hz'⟩ := M.exists_lift_sq hzz
  have hz'B : z' ∈ (blkGL U).comap S.subtype := M.mem_of_sq hz'z' (by rw [hz']; exact hz)
  have hcomm : ∀ c ∈ (blkGL U).comap S.subtype, c * z' = z' * c := by
    intro c hcB
    refine M.comm_of_comm hz'z' ?_
    rw [hz']
    exact (hc (π c) ⟨c, hcB, rfl⟩).symm
  set Z : Matrix (Fin 5) (Fin 5) F := ((z' : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) with hZ
  have hblk : ∀ x y, (x ∉ U ∨ y ∉ U) → Z x y = (1 : Matrix (Fin 5) (Fin 5) F) x y := hz'B
  have hdiag : Z.IsDiag := by
    intro x y hxy
    by_cases hxU : x ∈ U
    · by_cases hyU : y ∈ U
      · obtain ⟨w, hwU, hwx, hwy⟩ := exists_third hU hxU hyU hxy
        have hD : ∏ i, sgnOn (F := F) {x, w} i = 1 :=
          prod_sgnOn_of_even (by rw [Finset.card_pair (Ne.symm hwx)]; decide)
        have hmem : M.sgnS (sgnOn {x, w}) (sgnOn_sq _) hD ∈ (blkGL U).comap S.subtype := by
          show sgnGL (sgnOn (F := F) {x, w}) (sgnOn_sq _) ∈ blkGL U
          refine sgnGL_mem_blkGL (sgnOn_sq _) fun a ha => sgnOn_apply_not_mem ?_
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (rfl | rfl)
          · exact ha hxU
          · exact ha hwU
        have hcz : z' ∈ centralizer ({M.sgnS (sgnOn {x, w}) (sgnOn_sq _) hD} : Set ↥S) :=
          Subgroup.mem_centralizer_singleton_iff.2 (hcomm _ hmem).symm
        refine M.entry_eq_zero (sgnOn_sq _) hD hcz ?_
        rw [sgnOn_apply_mem (by simp), sgnOn_apply_not_mem (by simp [Ne.symm hxy, Ne.symm hwy])]
        intro h
        apply M.two
        linear_combination -h
      · exact (hblk x y (Or.inr hyU)).trans (Matrix.one_apply_ne hxy)
    · exact (hblk x y (Or.inl hxU)).trans (Matrix.one_apply_ne hxy)
  set ζ : Fin 5 → F := fun x => Z x x with hζ
  have hZζ : Z = Matrix.diagonal ζ := hdiag.diagonal_diag.symm
  have hζsq : ∀ x, ζ x * ζ x = 1 := by
    intro x
    have h := congrArg (fun g : ↥S => ((g : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) x x) hz'z'
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one,
      Matrix.one_apply_eq] at h
    rw [← hZ, mul_apply_self_of_isDiag hdiag] at h
    exact h
  have hζout : ∀ x, x ∉ U → ζ x = 1 := by
    intro x hx
    have := hblk x x (Or.inl hx)
    rw [Matrix.one_apply_eq] at this
    exact this
  have hζeq : ∀ x ∈ U, ∀ y ∈ U, ζ x = ζ y := by
    intro x hx y hy
    by_cases hxy : x = y
    · rw [hxy]
    have hD : ∏ i, sgnOn (F := F) {x} i = -1 := by rw [prod_sgnOn, Finset.card_singleton, pow_one]
    set τ : GL (Fin 5) F := permGL5 (Equiv.swap x y) * sgnGL (sgnOn {x}) (sgnOn_sq _) with hτ
    have hτN : τ ∈ N := N.mul_mem (M.perm _) (M.sgnN _ _)
    have hτdet : (τ : Matrix (Fin 5) (Fin 5) F).det = 1 := by
      rw [hτ, Units.val_mul, Matrix.det_mul, coe_permGL5, Matrix.det_permutation, coe_sgnGL,
        Matrix.det_diagonal, hD, Equiv.Perm.sign_inv, Equiv.Perm.sign_swap hxy]
      simp
    have hτS : τ ∈ S := M.detN τ hτN hτdet
    have hτB : τ ∈ blkGL U := by
      refine (blkGL U).mul_mem (permGL5_mem_blkGL fun a ha => ?_) (sgnGL_mem_blkGL (sgnOn_sq _) fun a ha => ?_)
      · exact Equiv.swap_apply_of_ne_of_ne (fun h => ha (h ▸ hx)) (fun h => ha (h ▸ hy))
      · exact sgnOn_apply_not_mem (by simp only [Finset.mem_singleton]; rintro rfl; exact ha hx)
    have hc' := hcomm ⟨τ, hτS⟩ hτB
    have hc'' : τ * (z' : GL (Fin 5) F) * τ⁻¹ = (z' : GL (Fin 5) F) := by
      have h := congrArg Subtype.val hc'
      simp only [Subgroup.coe_mul] at h
      rw [h]
      group
    have hmat : ((τ * (z' : GL (Fin 5) F) * τ⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
        Matrix.diagonal (ζ ∘ (Equiv.swap x y).symm) := by
      have hDZ : Matrix.diagonal (sgnOn (F := F) {x}) * Z = Z * Matrix.diagonal (sgnOn {x}) :=
        commute_of_isDiag (Matrix.isDiag_diagonal _) hdiag
      have hDinv : Matrix.diagonal (sgnOn (F := F) {x}) *
          (((sgnGL (sgnOn (F := F) {x}) (sgnOn_sq _))⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) = 1 := by
        rw [← coe_sgnGL (sgnOn (F := F) {x}) (sgnOn_sq _), ← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [← permGL5_conj_diagonal, ← hZζ, hτ]
      simp only [Units.val_mul, _root_.mul_inv_rev, coe_sgnGL]
      calc ((permGL5 (Equiv.swap x y) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *
            Matrix.diagonal (sgnOn (F := F) {x}) * ((z' : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *
            ((((sgnGL (sgnOn (F := F) {x}) (sgnOn_sq _))⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *
              (((permGL5 (Equiv.swap x y))⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F))
          = ((permGL5 (Equiv.swap x y) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) * Z *
              (Matrix.diagonal (sgnOn (F := F) {x}) *
                (((sgnGL (sgnOn (F := F) {x}) (sgnOn_sq _))⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) *
              (((permGL5 (Equiv.swap x y))⁻¹ : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
            rw [← hZ, Matrix.mul_assoc ((permGL5 (Equiv.swap x y) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F),
              hDZ]
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hDinv, Matrix.mul_one]
    rw [hc'', ← hZ, hZζ] at hmat
    have := congrFun (congrFun hmat y) y
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at this
    simp only [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_right] at this
    exact this.symm
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∈ U := Finset.card_pos.1 (by rw [hU]; norm_num)
  have hdet := M.det _ z'.2
  rw [← hZ, det_of_isDiag hdiag] at hdet
  have hprod : ∏ i, ζ i = ζ x₀ ^ 3 := by
    rw [← Finset.prod_subset (Finset.subset_univ U) (fun a _ ha => hζout a ha)]
    rw [Finset.prod_congr rfl (fun a ha => hζeq a ha x₀ hx₀), Finset.prod_const, hU]
  have h3 : ζ x₀ ^ 3 = 1 := by rw [← hprod]; exact hdet
  have h1 : ζ x₀ = 1 := by
    have := hζsq x₀
    calc ζ x₀ = ζ x₀ * (ζ x₀ * ζ x₀) := by rw [this, mul_one]
      _ = ζ x₀ ^ 3 := by ring
      _ = 1 := h3
  have hζ1 : ∀ x, ζ x = 1 := by
    intro x
    by_cases hx : x ∈ U
    · rw [hζeq x hx x₀ hx₀, h1]
    · exact hζout x hx
  have hz'1 : z' = 1 := by
    apply Subtype.ext
    apply Units.ext
    show Z = 1
    rw [hZζ, ← Matrix.diagonal_one]
    congr 1
    funext x
    exact hζ1 x
  rw [← hz', hz'1, map_one]

theorem sgnS_mul_of {ε η ζ : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1)
    (hη : ∀ i, η i * η i = 1) (hdetη : ∏ i, η i = 1) (hζ : ∀ i, ζ i * ζ i = 1) (hdetζ : ∏ i, ζ i = 1)
    (h : ∀ x, ε x * η x = ζ x) :
    M.sgnS ε hε hdet * M.sgnS η hη hdetη = M.sgnS ζ hζ hdetζ := by
  apply Subtype.ext
  apply Units.ext
  show Matrix.diagonal ε * Matrix.diagonal η = Matrix.diagonal ζ
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact h x

theorem sgnS_comm {ε η : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1)
    (hη : ∀ i, η i * η i = 1) (hdetη : ∏ i, η i = 1) :
    M.sgnS ε hε hdet * M.sgnS η hη hdetη = M.sgnS η hη hdetη * M.sgnS ε hε hdet := by
  apply Subtype.ext
  apply Units.ext
  show Matrix.diagonal ε * Matrix.diagonal η = Matrix.diagonal η * Matrix.diagonal ε
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

theorem sgnS_ne_one' {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1) {i j : Fin 5}
    (hij : ε i ≠ ε j) : π (M.sgnS ε hε hdet) ≠ 1 :=
  Model.sgnS_ne_one M.toModel hε hdet hij

theorem concl_std {A : Subgroup P}
    (h23 : π (M.sgnS (sgnOn {2, 3}) (sgnOn_sq _) (prod_sgnOn_of_even (by decide))) ∈ A)
    (h02 : π (M.sgnS (sgnOn {0, 2}) (sgnOn_sq _) (prod_sgnOn_of_even (by decide))) ∈ A) :
    P151Concl (π (M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4))) A
      (π (M.sgnS (sgnOn {0, 1}) (sgnOn_sq _) (prod_sgnOn_of_even (by decide)))) := by
  have hm1 : (1 : F) ≠ -1 := by
    intro h
    apply M.two
    linear_combination h
  have hm1' : (-1 : F) ≠ 1 := fun h => hm1 h.symm
  set a := M.sgnS (sgnOn (F := F) {0, 1}) (sgnOn_sq _) (prod_sgnOn_of_even (by decide)) with ha
  set s₀ := M.sgnS (oneAt (F := F) 1) (oneAt_sq 1) (prod_oneAt 1) with hs₀
  set e₁ := M.sgnS (sgnOn (F := F) {2, 3}) (sgnOn_sq _) (prod_sgnOn_of_even (by decide)) with he₁
  set e₂ := M.sgnS (sgnOn (F := F) {2, 4}) (sgnOn_sq _) (prod_sgnOn_of_even (by decide)) with he₂
  have hpat : ∀ (ε η ζ : Fin 5 → F), (∀ x, ε x * η x = ζ x) → ∀ (hε hdet hη hdetη hζ hdetζ),
      π (M.sgnS ε hε hdet) * π (M.sgnS η hη hdetη) = π (M.sgnS ζ hζ hdetζ) := by
    intro ε η ζ h hε hdet hη hdetη hζ hdetζ
    rw [← map_mul, M.sgnS_mul_of hε hdet hη hdetη hζ hdetζ h]
  have hU : ∀ x, x ∉ (Finset.univ \ {0, 1} : Finset (Fin 5)) → x = 0 ∨ x = 1 := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not, Finset.mem_insert,
      Finset.mem_singleton] at hx
    exact hx
  refine ⟨π s₀, ?_, ?_, M.exists_conj_oneAt 1, ?_, blkP S π (Finset.univ \ {0, 1}), ?_,
    M.type3 _ (card_compl_pair (by decide)), ?_,
    π e₁, π e₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul, M.sgnS_sq, map_one]
  · rw [← map_mul, ← map_mul, M.sgnS_comm]
  · rw [hpat (sgnOn {0, 1}) (oneAt 1) (oneAt 0) (fun x => by fin_cases x <;> simp [sgnOn, oneAt]) _ _ _ _
      (oneAt_sq 0) (prod_oneAt 0)]
    exact M.exists_conj_oneAt 0
  · refine M.isCompIn_blk_pair (i := 0) (j := 1) (by decide) _ _ _ _ (fun x hx => ?_) (fun x hx => ?_)
      (fun x y hx0 hx1 hy0 hy1 => ?_)
    · fin_cases x
      · exact absurd rfl hx
      · right; simpa [oneAt] using hm1
      · left; simpa [sgnOn] using hm1
      · left; simpa [sgnOn] using hm1
      · left; simpa [sgnOn] using hm1
    · fin_cases x
      · right; simpa [oneAt] using hm1'
      · exact absurd rfl hx
      · right; simpa [oneAt] using hm1'
      · right; simpa [oneAt] using hm1'
      · right; simpa [oneAt] using hm1'
    · fin_cases x <;> fin_cases y <;> simp_all [sgnOn, oneAt]
  · exact fun z hz hzc hzz => M.center_blk3 (card_compl_pair (by decide)) hz hzc hzz
  · refine ⟨e₁, sgnGL_mem_blkGL (sgnOn_sq _) fun x hx => sgnOn_apply_not_mem ?_, rfl⟩
    rcases hU x hx with rfl | rfl <;> decide
  · refine ⟨e₂, sgnGL_mem_blkGL (sgnOn_sq _) fun x hx => sgnOn_apply_not_mem ?_, rfl⟩
    rcases hU x hx with rfl | rfl <;> decide
  · rw [← map_mul, M.sgnS_sq, map_one]
  · rw [← map_mul, M.sgnS_sq, map_one]
  · rw [← map_mul, ← map_mul, M.sgnS_comm]
  · exact M.sgnS_ne_one' _ _ (i := 2) (j := 0) (by simp [sgnOn, hm1'])
  · exact M.sgnS_ne_one' _ _ (i := 2) (j := 0) (by simp [sgnOn, hm1'])
  · intro h
    have := M.sgnOn_inj _ _ h
    exact absurd this (by decide)
  · refine ⟨1, ?_⟩
    rw [hpat (sgnOn {0, 1}) (sgnOn {2, 3}) (oneAt 4) (fun x => by fin_cases x <;> simp [sgnOn, oneAt]) _ _ _ _
      (oneAt_sq 4) (prod_oneAt 4)]
    group
  · rw [hpat (sgnOn {0, 1}) (sgnOn {2, 4}) (oneAt 3) (fun x => by fin_cases x <;> simp [sgnOn, oneAt]) _ _ _ _
      (oneAt_sq 3) (prod_oneAt 3)]
    exact M.exists_conj_oneAt 3
  · rw [hpat (sgnOn {2, 3}) (sgnOn {2, 4}) (sgnOn {3, 4}) (fun x => by fin_cases x <;> simp [sgnOn]) _ _ _ _
      (sgnOn_sq _) (prod_sgnOn_of_even (by decide)),
      hpat (sgnOn {0, 1}) (sgnOn {3, 4}) (oneAt 2) (fun x => by fin_cases x <;> simp [sgnOn, oneAt]) _ _ _ _
      (oneAt_sq 2) (prod_oneAt 2)]
    exact M.exists_conj_oneAt 2
  · obtain ⟨g, hg⟩ := M.exists_perm_conjP (Equiv.swap 0 4)
    have hd1 : ∏ i, (sgnOn (F := F) {2, 3} ∘ (Equiv.swap 0 4).symm) i = 1 := by
      rw [show (∏ i, (sgnOn (F := F) {2, 3} ∘ (Equiv.swap 0 4).symm) i) = ∏ i, sgnOn (F := F) {2, 3} i from
        Equiv.prod_comp (Equiv.swap 0 4).symm _]
      exact prod_sgnOn_of_even (by decide)
    have hd2 : ∏ i, (sgnOn (F := F) {2, 4} ∘ (Equiv.swap 0 4).symm) i = 1 := by
      rw [show (∏ i, (sgnOn (F := F) {2, 4} ∘ (Equiv.swap 0 4).symm) i) = ∏ i, sgnOn (F := F) {2, 4} i from
        Equiv.prod_comp (Equiv.swap 0 4).symm _]
      exact prod_sgnOn_of_even (by decide)
    refine ⟨g, ?_, ?_⟩
    · rw [hg _ _ _ hd1]
      convert h23 using 2
      refine M.sgnS_congr ?_ _ _ _ _
      funext x
      fin_cases x <;> simp [sgnOn, Equiv.swap_apply_def]
    · rw [hg _ _ _ hd2]
      convert h02 using 2
      refine M.sgnS_congr ?_ _ _ _ _
      funext x
      fin_cases x <;> simp [sgnOn, Equiv.swap_apply_def]

theorem pat_mem {𝒟 : Finset (Finset (Fin 5))} (h𝒟 : ∀ D ∈ 𝒟, ∏ i, sgnOn (F := F) D i = 1) {A : Subgroup P}
    [Finite ↥A] (hcard : 𝒟.card ≤ Nat.card ↥A)
    (hsub : ∀ e ∈ A, ∃ D, ∃ hD : D ∈ 𝒟, e = π (M.sgnS (sgnOn D) (sgnOn_sq D) (h𝒟 D hD)))
    {D : Finset (Fin 5)} (hD : D ∈ 𝒟) : π (M.sgnS (sgnOn D) (sgnOn_sq D) (h𝒟 D hD)) ∈ A := by
  classical
  have hpat : ∀ e : ↥A, ∃ D' : ↥𝒟, (e : P) = π (M.sgnS (sgnOn D'.1) (sgnOn_sq _) (h𝒟 D'.1 D'.2)) := by
    intro e
    obtain ⟨D', hD', he⟩ := hsub e e.2
    exact ⟨⟨D', hD'⟩, he⟩
  choose f hf using hpat
  have hinj : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    rw [hf e, hf e', h]
  have hc : Nat.card ↥𝒟 ≤ Nat.card ↥A := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    exact hcard
  obtain ⟨e, he⟩ := (hinj.bijective_of_nat_card_le hc).2 ⟨D, hD⟩
  have h1 := hf e
  rw [he] at h1
  rw [← h1]
  exact e.2

theorem pattern01_of_mem [Finite P] {L : Subgroup P}
    (hL : IsCompIn (centralizer ({π (M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl)))} :
      Set P)) L)
    {ε : Fin 5 → F} (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1) (huL : π (M.sgnS ε hε hdet) ∈ L) :
    ε 0 = ε 1 := by
  set t := M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl)) with ht
  set X := centralizer ({t} : Set ↥S) with hX
  have hC : centralizer ({π t} : Set P) = (π.comp X.subtype).range := by
    rw [M.centralizer_proj (M.sgnS_sq _ _ _), MonoidHom.range_comp, Subgroup.range_subtype]
  have hq := isQuasisimple_of_isCompIn hL
  have hperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp hq.1
  set ψ : ↥X →* Fˣ := (Matrix.detMonoidHom.comp (M.blk2Hom X le_rfl)).toHomUnits with hψ
  have h1 : L ≤ ψ.ker.map (π.comp X.subtype) :=
    le_map_ker_of_perfect _ ψ (by rw [← hC]; exact hL.1) hperf
  set Y : Subgroup ↥S := ψ.ker.map X.subtype with hY
  have hLY : L ≤ Y.map π := by
    rw [hY, Subgroup.map_map]
    exact h1
  set u := M.sgnS ε hε hdet with hu
  have huY : u ∈ Y := M.mem_of_sq (M.sgnS_sq _ _ _) (hLY huL)
  have hdetY : (blk2 (((u : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)).det = 1 := by
    obtain ⟨x, hx, hxu⟩ := huY
    have hx' : ψ x = 1 := hx
    have := congrArg Units.val hx'
    rw [← hxu]
    exact this
  have h01 : ε 0 * ε 1 = 1 := by
    have : (blk2 (((u : ↥S) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)).det = ε 0 * ε 1 := by
      rw [hu, Model.coe_sgnS, coe_sgnGL, blk2, Matrix.det_fin_two_of]
      simp
    rw [← this]
    exact hdetY
  calc ε 0 = ε 0 * (ε 0 * ε 1) := by rw [h01, mul_one]
    _ = (ε 0 * ε 0) * ε 1 := by ring
    _ = ε 1 := by rw [hε 0, one_mul]

theorem exists_coord [Finite P] {v : P} (hvv : v * v = 1) (hv1 : v ≠ 1) {L E : Subgroup P}
    (hL : IsCompIn (centralizer ({v} : Set P)) L)
    (hZ : ∃ z₀ : P, ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z * z = 1 → z = 1 ∨ z = z₀)
    (hE : CFSG.IsElementaryAbelian 2 ↥E) (hE8 : Nat.card ↥E = 8) (hEL : E ≤ L) :
    ∃ g : P, g * v * g⁻¹ = π (M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4)) ∧
      L.map (MulAut.conj g).toMonoidHom = blkP S π (Finset.univ.erase 4) ∧
      ∀ e ∈ E, ∃ (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1), ε 4 = 1 ∧
        g * e * g⁻¹ = π (M.sgnS ε hε hdet) := by
  have hvc : ∀ e ∈ E, e * v = v * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.1 (hL.1 (hEL he))
  obtain ⟨g, k, hk, hgv, hgE'⟩ := M.exists_conj_std_E (isElementaryAbelian_sup_zpowers_comm hE hvv hvc)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers v)) hv1
  have hgE : ∀ e ∈ E, ∃ (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1),
      g * e * g⁻¹ = π (M.sgnS ε hε hdet) := fun e he => hgE' e (Subgroup.mem_sup_left he)
  have hL' := isCompIn_conj g hL
  rcases hk with rfl | rfl
  · exfalso
    rw [hgv] at hL'
    obtain ⟨z₀, hz₀⟩ := hZ
    classical
    set L' := L.map (MulAut.conj g).toMonoidHom with hL'def
    set E' := E.map (MulAut.conj g).toMonoidHom with hE'def
    set 𝒟 : Finset (Finset (Fin 5)) := Finset.univ.filter fun D => (0 ∈ D ↔ 1 ∈ D) ∧ Even D.card with h𝒟def
    have h𝒟 : ∀ D ∈ 𝒟, ∏ i, sgnOn (F := F) D i = 1 :=
      fun D hD => prod_sgnOn_of_even (Finset.mem_filter.1 hD).2.2
    have hE'8 : Nat.card ↥E' = 8 := by
      rw [← hE8]
      exact Nat.card_congr ((MulAut.conj g).subgroupMap E).toEquiv.symm
    have hcard : 𝒟.card ≤ Nat.card ↥E' := by
      rw [hE'8]
      decide
    have hsub : ∀ e ∈ E', ∃ D, ∃ hD : D ∈ 𝒟, e = π (M.sgnS (sgnOn D) (sgnOn_sq D) (h𝒟 D hD)) := by
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨ε, hε, hdet, he'⟩ := hgE e he
      have hmemL : π (M.sgnS ε hε hdet) ∈ L' := by
        rw [← he']
        exact conj_mem_map g (hEL he)
      have h01 : ε 0 = ε 1 := M.pattern01_of_mem hL' hε hdet hmemL
      have hD𝒟 : (Finset.univ.filter fun i => ε i = -1) ∈ 𝒟 := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, ?_⟩
        · simp [h01]
        · have h := hdet
          rw [eq_sgnOn_filter M.two hε, prod_sgnOn] at h
          exact (neg_one_pow_eq_one_iff_even (neg_one_ne_one M.two)).1 h
      refine ⟨_, hD𝒟, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [he']
      congr 1
      exact M.sgnS_congr (eq_sgnOn_filter M.two hε) _ _ _ _
    have hmem : ∀ D (hD : D ∈ 𝒟), π (M.sgnS (sgnOn D) (sgnOn_sq D) (h𝒟 D hD)) ∈ L' := fun D hD =>
      Subgroup.map_mono hEL (M.pat_mem h𝒟 hcard hsub hD)
    have ht : π (M.sgnS (stdSign 2) (stdSign_sq 2) (prod_stdSign (Or.inl rfl))) ∈ L' := by
      have h := hmem {0, 1} (by decide)
      convert h using 2
      refine M.sgnS_congr ?_ _ _ _ _
      funext i
      fin_cases i <;> simp [stdSign, sgnOn]
    set z₁ := g * z₀ * g⁻¹ with hz₁
    have hZ' : ∀ z ∈ L', (∀ l ∈ L', z * l = l * z) → z * z = 1 → z = 1 ∨ z = z₁ := by
      rintro _ ⟨w, hw, rfl⟩ hzc hzz
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzc hzz ⊢
      have hwc := comm_of_conj_comm g hzc
      have hww : w * w = 1 := by
        have : g * (w * w) * g⁻¹ = g * 1 * g⁻¹ := by
          calc g * (w * w) * g⁻¹ = g * w * g⁻¹ * (g * w * g⁻¹) := by group
            _ = 1 := hzz
            _ = g * 1 * g⁻¹ := by group
        simpa using this
      rcases hz₀ w hw hwc hww with h | h
      · left; rw [h]; group
      · right; rw [h]
    have hfalse : ∀ D (hD : D ∈ 𝒟), 0 ∉ D → π (M.sgnS (sgnOn D) (sgnOn_sq D) (h𝒟 D hD)) ≠ 1 →
        π (M.sgnS (sgnOn D) (sgnOn_sq D) (h𝒟 D hD)) ≠ z₁ → False := by
      intro D hD h0 h1 hz
      refine M.false_of_two_mem hL' ht (sgnOn_sq D) (h𝒟 D hD) (sgnOn_apply_not_mem h0) (hmem D hD) ?_
      intro hc
      rcases hZ' _ (hmem D hD) hc (by rw [← map_mul, M.sgnS_sq, map_one]) with h | h
      · exact h1 h
      · exact hz h
    have hne1 : ∀ D (hD : D ∈ 𝒟), (2 : Fin 5) ∈ D → 0 ∉ D →
        π (M.sgnS (sgnOn D) (sgnOn_sq D) (h𝒟 D hD)) ≠ 1 := by
      intro D hD h2 h0
      refine M.sgnS_ne_one' _ _ (i := 2) (j := 0) ?_
      rw [sgnOn_apply_mem h2, sgnOn_apply_not_mem h0]
      exact neg_one_ne_one M.two
    by_cases hz : π (M.sgnS (sgnOn {2, 3}) (sgnOn_sq _) (h𝒟 {2, 3} (by decide))) = z₁
    · refine hfalse {2, 4} (by decide) (by decide) (hne1 {2, 4} (by decide) (by decide) (by decide)) ?_
      intro h
      rw [← hz] at h
      exact absurd (M.sgnOn_inj _ _ h) (by decide)
    · exact hfalse {2, 3} (by decide) (by decide) (hne1 {2, 3} (by decide) (by decide) (by decide)) hz
  · have hstd : M.sgnS (stdSign 4) (stdSign_sq 4) (prod_stdSign (Or.inr rfl)) =
        M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4) := M.sgnS_congr stdSign_four _ _ _ _
    rw [hstd] at hgv
    rw [hgv] at hL'
    have hLB := M.eq_blk_of_four hL'
    refine ⟨g, hgv, hLB, fun e he => ?_⟩
    obtain ⟨ε, hε, hdet, he'⟩ := hgE e he
    refine ⟨ε, hε, hdet, M.apply_four_of_mem_blk hε hdet ?_, he'⟩
    rw [← hLB, ← he']
    exact conj_mem_map g (hEL he)

theorem stdPat_mem {A : Subgroup P} [Finite ↥A] (hA8 : Nat.card ↥A = 8)
    (hsub : ∀ e ∈ A, ∃ (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1), ε 4 = 1 ∧
      e = π (M.sgnS ε hε hdet))
    {D : Finset (Fin 5)} (hD : D ∈ stdPats) :
    π (M.sgnS (sgnOn D) (sgnOn_sq D) (prod_sgnOn_of_even (mem_stdPats.1 hD).2)) ∈ A := by
  classical
  have hpat : ∀ e : ↥A, ∃ D' : ↥stdPats, (e : P) =
      π (M.sgnS (sgnOn D'.1) (sgnOn_sq _) (prod_sgnOn_of_even (mem_stdPats.1 D'.2).2)) := by
    intro e
    obtain ⟨ε, hε, hdet, h4, he⟩ := hsub e e.2
    refine ⟨⟨_, filter_mem_stdPats M.two hε hdet h4⟩, ?_⟩
    rw [he]
    congr 1
    exact M.sgnS_congr (eq_sgnOn_filter M.two hε) _ _ _ _
  choose f hf using hpat
  have hinj : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    rw [hf e, hf e', h]
  have hcard : Nat.card ↥stdPats ≤ Nat.card ↥A := by
    rw [hA8, Nat.card_eq_fintype_card, Fintype.card_coe, card_stdPats]
  obtain ⟨e, he⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨D, hD⟩
  have h1 := hf e
  rw [he] at h1
  rw [← h1]
  exact e.2

theorem concl_pair {A : Subgroup P}
    (hall : ∀ (D : Finset (Fin 5)) (hD : D ∈ stdPats),
      π (M.sgnS (sgnOn D) (sgnOn_sq D) (prod_sgnOn_of_even (mem_stdPats.1 hD).2)) ∈ A)
    {i j : Fin 5} (hij : i ≠ j) (hi4 : i ≠ 4) (hj4 : j ≠ 4) (hD : ∏ x, sgnOn (F := F) {i, j} x = 1) :
    P151Concl (π (M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4))) A
      (π (M.sgnS (sgnOn {i, j}) (sgnOn_sq _) hD)) := by
  obtain ⟨σ, hσ4, hσi, hσj⟩ := exists_perm_pair hij hi4 hj4
  obtain ⟨h, hh⟩ := M.exists_perm_conjP σ
  have hdetc : ∀ ε : Fin 5 → F, ∏ x, ε x = 1 → ∏ x, (ε ∘ σ.symm) x = 1 := by
    intro ε hε
    rw [show (∏ x, (ε ∘ σ.symm) x) = ∏ x, ε x from Equiv.prod_comp σ.symm ε]
    exact hε
  have hσ4' : σ.symm 4 = 4 := by rw [Equiv.symm_apply_eq]; exact hσ4.symm
  have hv : (MulAut.conj h) (π (M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4))) =
      π (M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4)) := by
    rw [MulAut.conj_apply, hh _ _ _ (hdetc _ (prod_oneAt 4))]
    congr 1
    refine M.sgnS_congr ?_ _ _ _ _
    funext x
    simp only [Function.comp_apply, oneAt]
    by_cases hx : x = 4
    · subst hx; rw [hσ4']
    · have : σ.symm x ≠ 4 := by
        intro h'
        apply hx
        rw [Equiv.symm_apply_eq] at h'
        rw [h', hσ4]
      simp [hx, this]
  have ha : (MulAut.conj h) (π (M.sgnS (sgnOn {i, j}) (sgnOn_sq _) hD)) =
      π (M.sgnS (sgnOn {0, 1}) (sgnOn_sq _) (prod_sgnOn_of_even (by decide))) := by
    rw [MulAut.conj_apply, hh _ _ _ (hdetc _ hD)]
    congr 1
    refine M.sgnS_congr ?_ _ _ _ _
    rw [sgnOn_comp_symm]
    congr 1
    simp [Finset.map_insert, Finset.map_singleton, hσi, hσj]
  have hmem : ∀ D₀ : Finset (Fin 5), D₀ ∈ stdPats → ∀ hD₀ : ∏ x, sgnOn (F := F) D₀ x = 1,
      π (M.sgnS (sgnOn D₀) (sgnOn_sq _) hD₀) ∈ A.map (MulAut.conj h).toMonoidHom := by
    intro D₀ hD₀s hD₀
    set D' := D₀.map σ.symm.toEmbedding with hD'
    have hD's : D' ∈ stdPats := by
      rw [mem_stdPats] at hD₀s ⊢
      refine ⟨?_, by rw [hD', Finset.card_map]; exact hD₀s.2⟩
      rw [hD', Finset.mem_map_equiv, Equiv.symm_symm, hσ4]
      exact hD₀s.1
    refine ⟨_, hall D' hD's, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [MulAut.conj_apply, hh _ _ _ (hdetc _ (prod_sgnOn_of_even (mem_stdPats.1 hD's).2))]
    congr 1
    refine M.sgnS_congr ?_ _ _ _ _
    rw [sgnOn_comp_symm, hD', Finset.map_map]
    congr 1
    ext x
    simp
  have hc := M.concl_std (A := A.map (MulAut.conj h).toMonoidHom)
    (hmem {2, 3} (by decide) (prod_sgnOn_of_even (by decide)))
    (hmem {0, 2} (by decide) (prod_sgnOn_of_even (by decide)))
  rw [← hv, ← ha] at hc
  exact P151Concl.of_mulEquiv (MulAut.conj h) hc

theorem p151Fact [Finite P] : P151Fact P := by
  intro v L A hvv hv1 hL hZ hA hA8 hAL a haA ha1 hav
  obtain ⟨g, hgv, -, hgA⟩ := M.exists_coord hvv hv1 hL hZ hA hA8 hAL
  set A' := A.map (MulAut.conj g).toMonoidHom with hA'
  have hA'8 : Nat.card ↥A' = 8 := by
    rw [← hA8]
    exact Nat.card_congr ((MulAut.conj g).subgroupMap A).toEquiv.symm
  have hsub : ∀ e ∈ A', ∃ (ε : Fin 5 → F) (hε : ∀ i, ε i * ε i = 1) (hdet : ∏ i, ε i = 1), ε 4 = 1 ∧
      e = π (M.sgnS ε hε hdet) := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨ε, hε, hdet, h4, he'⟩ := hgA e he
    refine ⟨ε, hε, hdet, h4, ?_⟩
    rw [← he']
    simp [MulAut.conj_apply]
  have hall : ∀ (D : Finset (Fin 5)) (hD : D ∈ stdPats),
      π (M.sgnS (sgnOn D) (sgnOn_sq D) (prod_sgnOn_of_even (mem_stdPats.1 hD).2)) ∈ A' :=
    fun D hD => M.stdPat_mem hA'8 hsub hD
  classical
  obtain ⟨εa, hεa, hdeta, h4a, ha'⟩ := hgA a haA
  set Da := Finset.univ.filter fun x => εa x = -1 with hDa
  have hDas : Da ∈ stdPats := filter_mem_stdPats M.two hεa hdeta h4a
  have hεaD : εa = sgnOn Da := eq_sgnOn_filter M.two hεa
  have hDaD : ∏ x, sgnOn (F := F) Da x = 1 := prod_sgnOn_of_even (mem_stdPats.1 hDas).2
  have ha'' : g * a * g⁻¹ = π (M.sgnS (sgnOn Da) (sgnOn_sq _) hDaD) := by
    rw [ha']
    congr 1
    exact M.sgnS_congr hεaD _ _ _ _
  have hDa4 : Da ⊆ Finset.univ.erase 4 := by
    intro x hx
    rw [Finset.mem_erase]
    exact ⟨fun h => (mem_stdPats.1 hDas).1 (h ▸ hx), Finset.mem_univ x⟩
  have hcard_le : Da.card ≤ 4 := by
    have := Finset.card_le_card hDa4
    rwa [Finset.card_erase_of_mem (Finset.mem_univ 4), Finset.card_univ, Fintype.card_fin] at this
  have hne0 : Da.card ≠ 0 := by
    intro h0
    apply ha1
    rw [Finset.card_eq_zero] at h0
    have h1 : M.sgnS (sgnOn Da) (sgnOn_sq _) hDaD = 1 := by
      apply Subtype.ext
      apply Units.ext
      show Matrix.diagonal (sgnOn (F := F) Da) = 1
      rw [← Matrix.diagonal_one, h0]
      congr 1
    rw [h1, map_one] at ha''
    calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
      _ = 1 := by rw [ha'']; group
  have hne4 : Da.card ≠ 4 := by
    intro h4
    apply hav
    have hDeq : Da = Finset.univ.erase 4 := Finset.eq_of_subset_of_card_le hDa4 (by
      rw [Finset.card_erase_of_mem (Finset.mem_univ 4), Finset.card_univ, Fintype.card_fin, h4])
    have h1 : M.sgnS (sgnOn Da) (sgnOn_sq _) hDaD = M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4) :=
      M.sgnS_congr (by rw [hDeq, oneAt_eq_sgnOn]) _ _ _ _
    rw [h1, ← hgv] at ha''
    have := congrArg (fun z => g⁻¹ * z * g) ha''
    simpa using this
  have hDa2 : Da.card = 2 := by
    obtain ⟨m, hm⟩ := (mem_stdPats.1 hDas).2
    omega
  obtain ⟨i, j, hij, hDaij⟩ := Finset.card_eq_two.1 hDa2
  have hi4 : i ≠ 4 := fun h => (mem_stdPats.1 hDas).1 (by rw [hDaij, h]; simp)
  have hj4 : j ≠ 4 := fun h => (mem_stdPats.1 hDas).1 (by rw [hDaij, h]; simp)
  have hDij : ∏ x, sgnOn (F := F) {i, j} x = 1 := by rw [← hDaij]; exact hDaD
  have hc := M.concl_pair hall hij hi4 hj4 hDij
  have hgv' : (MulAut.conj g) v = π (M.sgnS (oneAt 4) (oneAt_sq 4) (prod_oneAt 4)) := by
    rw [MulAut.conj_apply]; exact hgv
  have hga' : (MulAut.conj g) a = π (M.sgnS (sgnOn {i, j}) (sgnOn_sq _) hDij) := by
    rw [MulAut.conj_apply, ha'']
    congr 1
    exact M.sgnS_congr (by rw [hDaij]) _ _ _ _
  rw [← hgv', ← hga'] at hc
  exact P151Concl.of_mulEquiv (MulAut.conj g) hc

end Frame5

end Frame

section Models

open CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KFU

theorem frame5_projectiveSL {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hFc : Nat.card F = p ^ f) (h4 : p ^ f % 4 = 3) :
    Frame5 (StatedSL 5 F) ⊤ (L5InvModels.projSL F) where
  toModel := B3aModels.model_projectiveSL (CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hFc)
  le := le_top
  detN := fun n _ hn => (L5InvModels.mem_statedSL_iff' n).2 hn
  perm := fun _ => Subgroup.mem_top _
  sgnN := fun _ _ => Subgroup.mem_top _
  adj := L5InvModels.adj_top
  lift := L5InvModels.lift_projectiveSL (CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp hp2 hFc)
  quasi3 := fun I hI => by
    rw [B3aModels.blkP_projSL (F := F) I]
    obtain ⟨φ⟩ := CFSG.SeitzReduction.LinearPilot.blockSL_mulEquiv (K := F) (I := I) (by rw [hI]; norm_num)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm
      (CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (by rw [hI]))
  type3 := fun I hI => by
    rw [B3aModels.blkP_projSL (F := F) I]
    obtain ⟨φ⟩ := CFSG.SeitzReduction.LinearPilot.blockSL_mulEquiv (K := F) (I := I) (by rw [hI]; norm_num)
    let e₁ := φ.trans (CFSG.SeitzReduction.LinearPilot.reindexSpecialLinear (K := F) (finCongr hI))
    let e₂ := (CFSG.ComponentClassification.UnbalancingLocal.centerQuotientCongr e₁).trans
      (projectiveSpecialLinearGroupEquivStatedProj 3 F)
    refine ⟨p, f, hp, hp2, Or.inl ⟨h4, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e₂.symm ?_⟩⟩
    exact Or.inl ⟨by decide, ⟨hp, hf, by norm_num, by simp, by simp⟩, F, inferInstance, inferInstance, hFc,
      ⟨MulEquiv.refl _⟩⟩

theorem sgnGL_mem_formU {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K) (ε : Fin 5 → K)
    (hε : ∀ i, ε i * ε i = 1) :
    sgnGL ε hε ∈ UnitaryHigher.primeFormUnitary h (1 : Matrix (Fin 5) (Fin 5) K) := by
  rw [L5InvModels.mem_formU_iff h, coe_sgnGL, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases eq_one_or_neg_one (hε i) with hi | hi
  · rw [hi, map_one, mul_one]
  · rw [hi, map_neg, map_one, neg_mul_neg, mul_one]

theorem frame5_statedSU {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (h4 : p ^ f % 4 = 1) :
    Frame5 (StatedSU 5 (p ^ f) K)
      (UnitaryHigher.primeFormUnitary (GenLocDiagU.unitaryFieldData_of_card hp hK) (1 : Matrix (Fin 5) (Fin 5) K))
      (B3aModels.projSU p f K) where
  toModel := B3aModels.model_statedSU hp hp2 hK
  le := fun s hs => (L5InvModels.mem_formU_iff _ s).2
    ((ClassicalGroups.UnitaryFlag.mem_unitarySU_iff (GenLocDiagU.unitaryFieldData_of_card hp hK)).1 hs).2
  detN := fun n hn hdet => (ClassicalGroups.UnitaryFlag.mem_unitarySU_iff _).2
    ⟨hdet, (L5InvModels.mem_formU_iff _ n).1 hn⟩
  perm := L5InvModels.permGL5_mem_unitary _
  sgnN := sgnGL_mem_formU _
  adj := L5InvModels.adj_unitary _
  lift := L5InvModels.lift_statedSU hp hp2 hK
  quasi3 := fun I hI => by
    rw [B3aModels.blkP_statedSU (p := p) (f := f) (GenLocDiagU.unitaryFieldData_of_card hp hK) I]
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((ClassicalGroups.UnitaryFlag.unitaryPSUEquiv _ (by norm_num)).subgroupMap _)
      (CFSG.SeitzReduction.UnitaryPilot.isQuasisimple_blockSU_of_three_le _ (by rw [hI]) ?_
        (by rw [hI]; norm_num))
    rw [hI]
    intro h3
    have h2 : p ^ f = 2 := congrArg Prod.snd h3
    have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    rw [h2] at hodd
    exact absurd hodd (by decide)
  type3 := fun I hI => by
    have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := by
      intro h3
      have h2 : p ^ f = 2 := congrArg Prod.snd h3
      have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
      rw [h2] at hodd
      exact absurd hodd (by decide)
    set h := GenLocDiagU.unitaryFieldData_of_card hp hK with hh
    rw [B3aModels.blkP_statedSU (p := p) (f := f) h I]
    obtain ⟨φ⟩ := CFSG.SeitzReduction.UnitaryPilot.blockSU_mulEquiv h I (by rw [hI]; norm_num)
    rw [hI] at φ
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨-, hcen⟩ := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK (n := 3) le_rfl hnq
    let e₁ := ((ClassicalGroups.UnitaryFlag.unitaryPSUEquiv h (by norm_num : 1 ≤ 5)).subgroupMap
      (CFSG.SeitzReduction.UnitaryPilot.blockSU h I)).symm.trans φ
    let e₂ := (CFSG.ComponentClassification.UnbalancingLocal.centerQuotientCongr e₁).trans
      (QuotientGroup.quotientMulEquivOfEq hcen)
    refine ⟨p, f, hp, hp2, Or.inr ⟨h4, CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e₂.symm ?_⟩⟩
    exact Or.inl ⟨by decide, ⟨hp, hf, le_rfl, hnq⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩

theorem p151Fact_of_puL5 {J : Type} [Group J] (hJ : B2.PuL5 J) : P151Fact J := by
  obtain ⟨p, f, hp, hp2, hf, ⟨h4, hm⟩ | ⟨h4, hm⟩⟩ := hJ
  · obtain ⟨⟨hprime, hf', -⟩, F, _, _, hF, ⟨e⟩⟩ := GenLocL5Out.stated_PSL hm
    let ψ : J ≃* LinearFlag.projectiveSL 5 F :=
      e.trans ((projectiveSpecialLinearGroupEquivStatedProj 5 F).symm.trans
        (LinearCover.projectiveSpecialLinearEquivProjectiveSL 5 F))
    exact P151Fact.of_mulEquiv ψ (frame5_projectiveSL hprime hp2 hf' hF h4).p151Fact
  · obtain ⟨⟨hprime, hf', -⟩, K, _, _, hK, ⟨e⟩⟩ := GenLocL5Out.stated_PSU hm
    exact P151Fact.of_mulEquiv e (frame5_statedSU hprime hp2 hf' hK h4).p151Fact

end Models

end CFSG.GH74.Generic.BProg.B2.T4.P151Model
