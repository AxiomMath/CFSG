module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen

open CFSG CFSG.AGLEmbedding

section Defs

variable {S : Type*} [Group S]

@[expose] def fixSet (E : Subgroup (MulAut S)) : Set S :=
  {s | ∃ e ∈ E, e ≠ 1 ∧ e s = s}

@[expose] def FixCube (E : Subgroup (MulAut S)) : Prop :=
  ∀ e ∈ E, ∀ s : S, s ^ 3 = 1 → MulAut.conj s ∈ E → e s = s

theorem fixSet_subset_mod_center (E : Subgroup (MulAut S)) :
    fixSet E ⊆ {s : S | ∃ e ∈ E, e ≠ 1 ∧ e s * s⁻¹ ∈ Subgroup.center S} := by
  rintro s ⟨e, he, he1, hes⟩
  exact ⟨e, he, he1, by rw [hes, mul_inv_cancel]; exact Subgroup.one_mem _⟩

theorem closure_mod_center_eq_top {E : Subgroup (MulAut S)}
    (h : Subgroup.closure (fixSet E) = ⊤) :
    Subgroup.closure {s : S | ∃ e ∈ E, e ≠ 1 ∧ e s * s⁻¹ ∈ Subgroup.center S} = ⊤ :=
  eq_top_iff.2 (h ▸ Subgroup.closure_mono (fixSet_subset_mod_center E))

end Defs

section Gens

variable {G : Type*} [Group G] {E : Subgroup G}

theorem exists_mem_not_mem_zpowers (hE : Open.IsElemAbelian 3 E) (hcard : Nat.card E = 9)
    {a : G} (ha : a ∈ E) : ∃ b ∈ E, b ∉ Subgroup.zpowers a := by
  by_contra hcon
  push Not at hcon
  have hle : E ≤ Subgroup.zpowers a := fun x hx => hcon x hx
  have hfin : Finite (Subgroup.zpowers a) := Nat.finite_of_card_ne_zero (by
    rw [Nat.card_zpowers]
    exact (isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, hE.2 a ha⟩).orderOf_pos.ne')
  have h1 : Nat.card E ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le hle
  have h2 : Nat.card (Subgroup.zpowers a) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hE.2 a ha))
  omega

theorem mul_ne_one_of_not_mem_zpowers {a b : G} (hb3 : b ^ 3 = 1)
    (hb : b ∉ Subgroup.zpowers a) : a * b ≠ 1 ∧ a * b ^ 2 ≠ 1 := by
  refine ⟨fun h => hb ?_, fun h => hb ?_⟩
  · have : b = a⁻¹ := by
      calc b = a⁻¹ * (a * b) := by group
        _ = a⁻¹ := by rw [h, mul_one]
    rw [this]
    exact inv_mem (Subgroup.mem_zpowers a)
  · have h1 : b ^ 2 = a⁻¹ := by
      calc b ^ 2 = a⁻¹ * (a * b ^ 2) := by group
        _ = a⁻¹ := by rw [h, mul_one]
    have h2 : b = (b ^ 2) ^ 2 := by
      calc b = b ^ 3 * b := by rw [hb3, one_mul]
        _ = (b ^ 2) ^ 2 := by group
    rw [h2, h1]
    exact pow_mem (inv_mem (Subgroup.mem_zpowers a)) 2

end Gens

section Transport

variable {S S' : Type*} [Group S] [Group S']

@[expose] def mapAut (ψ : S ≃* S') (E : Subgroup (MulAut S)) : Subgroup (MulAut S') :=
  E.map (MulAut.congr ψ).toMonoidHom

theorem congr_apply' (ψ : S ≃* S') (e : MulAut S) (x : S') :
    MulAut.congr ψ e x = ψ (e (ψ.symm x)) := rfl

theorem congr_symm_congr (ψ : S ≃* S') (e : MulAut S) :
    MulAut.congr ψ.symm (MulAut.congr ψ e) = e := by
  ext x
  rw [congr_apply', congr_apply']
  simp

theorem congr_congr_symm (ψ : S ≃* S') (e' : MulAut S') :
    MulAut.congr ψ (MulAut.congr ψ.symm e') = e' := by
  ext x
  rw [congr_apply', congr_apply']
  simp

theorem mem_mapAut {ψ : S ≃* S'} {E : Subgroup (MulAut S)} {e' : MulAut S'} :
    e' ∈ mapAut ψ E ↔ MulAut.congr ψ.symm e' ∈ E := by
  constructor
  · rintro ⟨e, he, rfl⟩
    have : MulAut.congr ψ.symm ((MulAut.congr ψ).toMonoidHom e) = e := congr_symm_congr ψ e
    rw [this]
    exact he
  · intro h
    exact ⟨_, h, congr_congr_symm ψ e'⟩

theorem congr_conj (ψ : S ≃* S') (s : S) :
    MulAut.congr ψ (MulAut.conj s) = MulAut.conj (ψ s) := by
  ext x
  rw [congr_apply']
  simp [MulAut.conj_apply]

theorem fixSet_mapAut (ψ : S ≃* S') (E : Subgroup (MulAut S)) :
    fixSet (mapAut ψ E) = ψ '' fixSet E := by
  ext x
  constructor
  · rintro ⟨e', ⟨e, he, rfl⟩, he'1, hex⟩
    refine ⟨ψ.symm x, ⟨e, he, fun h => he'1 (by rw [h, map_one]), ?_⟩, by simp⟩
    have h1 : ψ (e (ψ.symm x)) = x := hex
    exact ψ.injective (by rw [h1, MulEquiv.apply_symm_apply])
  · rintro ⟨s, ⟨e, he, he1, hes⟩, rfl⟩
    refine ⟨MulAut.congr ψ e, ⟨e, he, rfl⟩, fun h => he1 ?_, ?_⟩
    · exact (MulAut.congr ψ).injective (by rw [h, map_one])
    · rw [congr_apply', MulEquiv.symm_apply_apply, hes]

theorem closure_fixSet_mapAut_eq_top_iff (ψ : S ≃* S') (E : Subgroup (MulAut S)) :
    Subgroup.closure (fixSet (mapAut ψ E)) = ⊤ ↔ Subgroup.closure (fixSet E) = ⊤ := by
  rw [fixSet_mapAut]
  have hmap : Subgroup.closure (ψ '' fixSet E) = (Subgroup.closure (fixSet E)).map ψ.toMonoidHom :=
    (MonoidHom.map_closure ψ.toMonoidHom _).symm
  rw [hmap]
  constructor
  · intro h
    have := Subgroup.comap_map_eq_self_of_injective (f := ψ.toMonoidHom) ψ.injective
      (Subgroup.closure (fixSet E))
    rw [h, Subgroup.comap_top] at this
    exact this.symm
  · intro h
    rw [h]
    exact Subgroup.map_top_of_surjective _ ψ.surjective

theorem FixCube.mapAut {E : Subgroup (MulAut S)} (h : FixCube E) (ψ : S ≃* S') :
    FixCube (mapAut ψ E) := by
  rintro e' he' s' hs'3 hs'
  have he : MulAut.congr ψ.symm e' ∈ E := mem_mapAut.1 he'
  have hcj : MulAut.conj (ψ.symm s') ∈ E := by
    have := mem_mapAut.1 hs'
    rwa [congr_conj] at this
  have hs3 : (ψ.symm s') ^ 3 = 1 := by rw [← map_pow, hs'3, map_one]
  have h1 := h _ he _ hs3 hcj
  have h2 : ψ.symm (e' (ψ.symm.symm (ψ.symm s'))) = ψ.symm s' := h1
  rw [MulEquiv.symm_symm, MulEquiv.apply_symm_apply] at h2
  exact ψ.symm.injective h2.symm.symm

theorem isElemAbelian_mapAut {E : Subgroup (MulAut S)} (h : Open.IsElemAbelian 3 E)
    (ψ : S ≃* S') : Open.IsElemAbelian 3 (mapAut ψ E) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    have hxy : x * y = y * x := congrArg Subtype.val (h.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    change (a : MulAut S') * b = b * a
    rw [← hxa, ← hyb]
    change MulAut.congr ψ x * MulAut.congr ψ y = MulAut.congr ψ y * MulAut.congr ψ x
    rw [← map_mul, ← map_mul, hxy]
  · rintro _ ⟨x, hx, rfl⟩
    change (MulAut.congr ψ x) ^ 3 = 1
    rw [← map_pow, h.2 x hx, map_one]

theorem card_mapAut (E : Subgroup (MulAut S)) (ψ : S ≃* S') :
    Nat.card (mapAut ψ E) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.congr ψ).injective

end Transport

end CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
