module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Malle.E27Lie

theorem exists_fixed_perfect_of_congr {K G : Type} [Group K] [Group G] (e : K ≃* G)
    (u : MulAut K) {D : Subgroup G} (hfix : ∀ x ∈ D, MulAut.congr e u x = x) (hperf : ⁅D, D⁆ = D)
    (h3 : 3 ∣ Nat.card D) :
    ∃ D' : Subgroup K, (∀ x ∈ D', u x = x) ∧ ⁅D', D'⁆ = D' ∧ 3 ∣ Nat.card D' := by
  refine ⟨D.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have h := hfix x hx
    rw [MulAut.congr_apply] at h
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
    apply e.injective
    rw [← e.apply_symm_apply x] at h
    simpa using h
  · rw [← Subgroup.map_commutator, hperf]
  · rw [Nat.card_congr (D.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).toEquiv] at h3
    exact h3

theorem fixed_subgroup_of_congr {K G : Type} [Group K] [Group G] (e : K ≃* G) (u : MulAut K)
    {Q : Subgroup G} (hQ : ∀ x ∈ Q, MulAut.congr e u x = x) :
    ∀ x ∈ Q.map e.symm.toMonoidHom, u x = x := by
  rintro _ ⟨x, hx, rfl⟩
  have h := hQ x hx
  rw [MulAut.congr_apply] at h
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
  apply e.injective
  rw [← e.apply_symm_apply x] at h
  simpa using h

theorem noPerfect_of_congr {K G : Type} [Group K] [Group G] (e : K ≃* G) (u : MulAut K)
    (h : ∀ D : Subgroup K, (∀ x ∈ D, u x = x) → ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D) :
    ∀ D : Subgroup G, (∀ x ∈ D, MulAut.congr e u x = x) → ⁅D, D⁆ = D → ¬ 3 ∣ Nat.card D :=
  fun D hf hp h3 => by
    obtain ⟨D', hf', hp', h3'⟩ := exists_fixed_perfect_of_congr e u hf hp h3
    exact h D' hf' hp' h3'

theorem card_le_nine_of_congr {K G : Type} [Group K] [Group G] (e : K ≃* G) (u : MulAut K)
    (h : ∀ Q : Subgroup K, (∀ x ∈ Q, u x = x) → IsPGroup 3 Q → Nat.card Q ≤ 9) :
    ∀ Q : Subgroup G, (∀ x ∈ Q, MulAut.congr e u x = x) → IsPGroup 3 Q → Nat.card Q ≤ 9 :=
  fun Q hf hp => by
    have hE := Subgroup.equivMapOfInjective Q e.symm.toMonoidHom e.symm.injective
    have := h (Q.map e.symm.toMonoidHom) (fixed_subgroup_of_congr e u hf) (hp.of_equiv hE)
    rwa [← Nat.card_congr hE.toEquiv] at this

theorem exists_elemAbelian_of_congr {K G : Type} [Group K] [Group G] (e : K ≃* G) (u : MulAut K)
    (h : ∃ T : Subgroup K, (∀ x ∈ T, u x = x) ∧ CFSG.Open.IsElemAbelian 3 T ∧ Nat.card T = 9) :
    ∃ T : Subgroup G, (∀ x ∈ T, MulAut.congr e u x = x) ∧ CFSG.Open.IsElemAbelian 3 T ∧
      Nat.card T = 9 := by
  obtain ⟨T, hf, ⟨hc, hp⟩, hc9⟩ := h
  have hE := Subgroup.equivMapOfInjective T e.toMonoidHom e.injective
  refine ⟨T.map e.toMonoidHom, ?_, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    show e (u (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hf x hx]
  · obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hp x hx, map_one]
  · rw [← Nat.card_congr hE.toEquiv]
    exact hc9

theorem commutator_eq_self_of_equiv_perfect {G H : Type*} [Group G] [Group H] (D : Subgroup G)
    (e : ↥D ≃* H) [hH : Group.IsPerfect H] : ⁅D, D⁆ = D := by
  have hD : ⁅(⊤ : Subgroup ↥D), (⊤ : Subgroup ↥D)⁆ = (⊤ : Subgroup ↥D) := by
    apply Subgroup.map_injective (f := (e : ↥D →* H)) e.injective
    rw [Subgroup.map_commutator]
    have htop : (⊤ : Subgroup ↥D).map (e : ↥D →* H) = ⊤ :=
      Subgroup.map_top_of_surjective _ e.surjective
    rw [htop]
    exact hH.commutator_eq_top
  have hmap : (⊤ : Subgroup ↥D).map D.subtype = D := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hmc := Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥D)) (H₂ := ⊤) D.subtype
  rw [hmap] at hmc
  rw [← hmc, hD, hmap]

end CFSG.HardMathSupport.Malle.E27Lie
