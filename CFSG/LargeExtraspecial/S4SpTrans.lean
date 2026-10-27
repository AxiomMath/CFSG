module

public import CFSG.LargeExtraspecial.S4SpU
public import CFSG.LargeExtraspecial.S4Lin

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Module Subgroup CFSG.LargeExtraspecial.OrthoF2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {β : LinearMap.BilinForm (ZMod 2) V}

theorem conj_mem_spPointRadical (hβ : β.IsAlt) {g u : V ≃ₗ[ZMod 2] V} {c : V}
    (hg : g ∈ TauCeti.BilinForm.isometryGroup β) (hu : u ∈ spPointRadical β c) :
    g * u * g⁻¹ ∈ spPointRadical β (g c) := by
  have hg' := TauCeti.BilinForm.mem_isometryGroup_iff.mp hg
  have e1 : ∀ x w, β (g⁻¹ x) w = β x (g w) := fun x w => by
    rw [← hg' (g⁻¹ x) w, show g (g⁻¹ x) = x from g.apply_symm_apply x]
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
  refine ⟨mul_mem (mul_mem hg hu1) (inv_mem hg), ?_, fun x hx => ?_, fun v => ?_⟩
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, show g⁻¹ (g c) = c from g.symm_apply_apply c,
      hu2]
  · have hx' : β c (g⁻¹ x) = 0 := by
      rw [isAlt_symm hβ, e1, isAlt_symm hβ, hx]
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (hu3 _ hx')
    rw [Submodule.mem_span_singleton]
    refine ⟨k, ?_⟩
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show u (g⁻¹ x) = g⁻¹ x + k • c by rw [hk]; abel, map_add, map_smul,
      show g (g⁻¹ x) = x from g.apply_symm_apply x]
    abel
  · have h := hu4 (g⁻¹ v)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have e2 : g (u (g⁻¹ v)) - v = g (u (g⁻¹ v) - g⁻¹ v) := by
      rw [map_sub, show g (g⁻¹ v) = v from g.apply_symm_apply v]
    rw [e2, hg', h]

variable [FiniteDimensional (ZMod 2) V]

theorem mem_or_mul_mem_of_card {G : Type*} [Group G] [Finite G] {E U : Subgroup G} (hEU : E ≤ U)
    (hcard : Nat.card U ≤ 2 * Nat.card E) {τ : G} (hτU : τ ∈ U) (hτE : τ ∉ E) {u : G}
    (hu : u ∈ U) : u ∈ E ∨ u * τ ∈ E := by
  have hidx : E.relIndex U = 2 := by
    have h1 := relIndex_mul_card E U
    rw [inf_eq_left.mpr hEU] at h1
    have hpos : 0 < Nat.card E := Nat.card_pos
    have hle : E.relIndex U ≤ 2 := by
      by_contra h
      push Not at h
      have : 3 * Nat.card E ≤ E.relIndex U * Nat.card E := Nat.mul_le_mul_right _ h
      omega
    have hne : E.relIndex U ≠ 1 := fun h => hτE (relIndex_eq_one.mp h hτU)
    have hne0 : E.relIndex U ≠ 0 := fun h => by
      rw [h, zero_mul] at h1
      exact Nat.card_pos.ne' h1.symm
    omega
  by_contra h
  push Not at h
  have h2 := mul_mem_iff_of_index_two (H := E.subgroupOf U) hidx (a := ⟨u, hu⟩) (b := ⟨τ, hτU⟩)
  simp only [mem_subgroupOf] at h2
  exact h.2 (h2.mpr ⟨fun h' => absurd h' h.1, fun h' => absurd h' hτE⟩)

theorem exists_perp_pair_not_mem (hnd : β.Nondegenerate)
    (h5 : 5 ≤ finrank (ZMod 2) V) (b c : V) :
    ∃ e : V, β b e = 0 ∧ β c e = 0 ∧ e ∉ Submodule.span (ZMod 2) {b, c} := by
  classical
  set P := Submodule.span (ZMod 2) ({b, c} : Set V) with hP
  have h1 := LinearMap.BilinForm.finrank_orthogonal hnd P
  have h2 : finrank (ZMod 2) P ≤ 2 := by
    have := finrank_span_finset_le_card (R := ZMod 2) ({b, c} : Finset V)
    rw [Finset.coe_insert, Finset.coe_singleton] at this
    exact this.trans ((Finset.card_insert_le _ _).trans (by simp))
  have h3 : ¬ LinearMap.BilinForm.orthogonal β P ≤ P := by
    intro hle
    have := Submodule.finrank_mono hle
    have h4 := Submodule.finrank_le P
    omega
  obtain ⟨e, he, heP⟩ := Set.not_subset.mp h3
  refine ⟨e, ?_, ?_, heP⟩
  · exact (LinearMap.BilinForm.mem_orthogonal_iff.mp he) b (Submodule.subset_span (by simp))
  · exact (LinearMap.BilinForm.mem_orthogonal_iff.mp he) c (Submodule.subset_span (by simp))

theorem exists_dual_triple (hβ : β.IsAlt) (hnd : β.Nondegenerate) {b c e : V}
    (he : e ∉ Submodule.span (ZMod 2) {b, c}) :
    ∃ d : V, β b d = 0 ∧ β c d = 0 ∧ β e d = 1 := by
  set P := Submodule.span (ZMod 2) ({b, c} : Set V) with hP
  have hrefl : β.IsRefl := hβ.isRefl
  have hPP := LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl P
  rw [← hPP] at he
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at he
  push Not at he
  obtain ⟨d, hd, hde⟩ := he
  have hdP := LinearMap.BilinForm.mem_orthogonal_iff.mp hd
  refine ⟨d, ?_, ?_, ?_⟩
  · exact hdP b (Submodule.subset_span (by simp))
  · exact hdP c (Submodule.subset_span (by simp))
  · rw [isAlt_symm hβ]
    exact zmod2_eq_one_of_ne_zero hde

omit [FiniteDimensional (ZMod 2) V] in
theorem spRho_congr (hβ : β.IsAlt) {c c' d d' : V} (hcd : β c d = 0) (hcd' : β c' d' = 0)
    {l l' : ZMod 2} (hc : c = c') (hd : d = d') (hl : l = l') :
    spRho hβ hcd l = spRho hβ hcd' l' := by
  subst hc hd hl
  rfl

theorem spTransvection_mem_of_transitive (hβ : β.IsAlt) (hnd : β.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) {X : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hX : X ≤ TauCeti.BilinForm.isometryGroup β) {a : V} (ha : a ≠ 0)
    {E : Subgroup (V ≃ₗ[ZMod 2] V)} (hEX : E ≤ X) (hEU : E ≤ spPointRadical β a)
    (hidx : Nat.card (spPointRadical β a) ≤ 2 * Nat.card E)
    (hnorm : ∀ x ∈ X, x a = a → x ∈ normalizer (E : Set (V ≃ₗ[ZMod 2] V)))
    (htr : ∀ v : V, v ≠ 0 → ∃ x ∈ X, x a = v) : spTransvection β hβ a ∈ E := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (V ≃ₗ[ZMod 2] V) := finite_linearEquiv_of_finite
  by_contra hτ
  have hconj : ∀ c : V, c ≠ 0 → ∃ Ec : Subgroup (V ≃ₗ[ZMod 2] V), Ec ≤ X ∧
      Ec ≤ spPointRadical β c ∧ Nat.card (spPointRadical β c) ≤ 2 * Nat.card Ec ∧
      spTransvection β hβ c ∉ Ec ∧ ∀ y ∈ X, y c = c → y ∈ normalizer (Ec : Set _) := by
    intro c hc
    obtain ⟨x, hxX, hxa⟩ := htr c hc
    have hxI := hX hxX
    refine ⟨E.map (MulAut.conj x).toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      exact mul_mem (mul_mem hxX (hEX he)) (inv_mem hxX)
    · rintro _ ⟨e, he, rfl⟩
      have := conj_mem_spPointRadical hβ hxI (hEU he)
      rwa [hxa] at this
    · rw [card_map_of_injective (MulAut.conj x).injective,
        card_spPointRadical hβ hnd hc, ← card_spPointRadical hβ hnd ha]
      exact hidx
    · rintro ⟨e, he, hec⟩
      apply hτ
      have hx' : x⁻¹ ∈ TauCeti.BilinForm.isometryGroup β := inv_mem hxI
      have h1 := conj_spTransvection hβ c hx'
      have hxc : x⁻¹ c = a := by rw [← hxa]; exact x.symm_apply_apply a
      rw [hxc] at h1
      have he' : e = x⁻¹ * spTransvection β hβ c * x⁻¹⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hec
        rw [← hec]
        group
      rw [← h1, ← he']
      exact he
    · intro y hyX hyc
      have h1 : x⁻¹ * y * x ∈ normalizer (E : Set (V ≃ₗ[ZMod 2] V)) := by
        refine hnorm _ (mul_mem (mul_mem (inv_mem hxX) hyX) hxX) ?_
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxa, hyc, ← hxa]
        exact x.symm_apply_apply a
      have h2 := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom)
        (Subgroup.zpowers_le.mpr h1)
      rw [map_equiv_normalizer_eq _ (MulAut.conj x)] at h2
      have h3 : y ∈ (zpowers (x⁻¹ * y * x)).map (MulAut.conj x).toMonoidHom :=
        ⟨x⁻¹ * y * x, mem_zpowers _, by simp [mul_assoc]⟩
      exact h2 h3
  choose! Ec hEcX hEcU hEccard hEcτ hEcN using hconj
  have hfib : ∀ c : V, c ≠ 0 → ∀ d (hcd : β c d = 0),
      spRho hβ hcd 0 ∈ Ec c ∨ spRho hβ hcd 1 ∈ Ec c := by
    intro c hc d hcd
    rcases mem_or_mul_mem_of_card (hEcU c hc) (hEccard c hc) (spTransvection_mem_U hβ c)
      (hEcτ c hc) (spRho_mem_spPointRadical hβ hcd 0) with h | h
    · exact Or.inl h
    · rw [← spRho_one_eq] at h
      exact Or.inr h
  have key : ∀ c : V, c ≠ 0 → ∀ b (hcb : β c b = 0), b ∉ Submodule.span (ZMod 2) {c} →
      spRho hβ hcb 0 ∈ Ec c := by
    intro c hc b hcb hbc
    have hb0 : b ≠ 0 := fun h => hbc (h ▸ Submodule.zero_mem _)
    obtain ⟨e, hbe, hce, he⟩ := exists_perp_pair_not_mem hnd (by omega) b c
    obtain ⟨d, hbd, hcd, hed⟩ := exists_dual_triple hβ hnd he
    have heb : β e b = 0 := by rw [isAlt_symm hβ, hbe]
    have hbc' : β b c = 0 := by rw [isAlt_symm hβ, hcb]
    obtain ⟨l, hgE⟩ : ∃ l, spRho hβ hbd l ∈ Ec b := by
      rcases hfib b hb0 d hbd with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    set gg := spRho hβ hbd l with hgg
    have hgX : gg ∈ X := hEcX b hb0 hgE
    have hgc : gg c = c := by simp [hgg, spRho_apply, hcb, hcd]
    have hge : gg e = e + b := by simp [hgg, spRho_apply, heb, hed]
    have hgN := hEcN c hc gg hgX hgc
    obtain ⟨μ, hhE⟩ : ∃ μ, spRho hβ hce μ ∈ Ec c := by
      rcases hfib c hc e hce with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hconj' : gg * spRho hβ hce μ * gg⁻¹ ∈ Ec c :=
      (mem_normalizer_iff.mp hgN _).mp hhE
    have hceb : β c (e + b) = 0 := by rw [map_add, hce, hcb, add_zero]
    have hgI : gg ∈ TauCeti.BilinForm.isometryGroup β := hX hgX
    rw [conj_spRho hβ hce μ hgI (by rw [hgc, hge]; exact hceb)] at hconj'
    rw [spRho_congr hβ _ hceb hgc hge rfl] at hconj'
    have hprod := mul_mem hhE hconj'
    have hd2 : e + (e + b) = b := by rw [← add_assoc, vec_add_self, zero_add]
    have hc2 : β c (e + (e + b)) = 0 := by rw [hd2]; exact hcb
    have hl2 : μ + μ + β e (e + b) = 0 := by
      rw [map_add, hβ.self_eq_zero, heb, add_zero, zmod2_add_self, add_zero]
    rw [spRho_mul hβ hce hceb μ μ hc2, spRho_congr hβ hc2 hcb rfl hd2 hl2] at hprod
    exact hprod
  obtain ⟨b, hab, -, hbP⟩ := exists_perp_pair_not_mem hnd (by omega) a a
  have hbP' : b ∉ Submodule.span (ZMod 2) {a} := by
    rwa [Set.pair_eq_singleton] at hbP
  obtain ⟨b', hab', -, hbb'⟩ := exists_dual_triple hβ hnd hbP
  have hba : β b a = 0 := by rw [isAlt_symm hβ, hab]
  have hb'P : b' ∉ Submodule.span (ZMod 2) {a} := by
    intro hmem
    obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    rw [map_smul, hba, smul_zero] at hbb'
    exact zero_ne_one hbb'
  have hab2 : β a (b + b') = 0 := by rw [map_add, hab, hab', add_zero]
  have hbb'P : b + b' ∉ Submodule.span (ZMod 2) {a} := by
    intro hmem
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 : β b (b + b') = 1 := by rw [map_add, hβ.self_eq_zero, hbb', zero_add]
    rw [← hk, map_smul, hba, smul_zero] at h1
    exact zero_ne_one h1
  have h1 := key a ha b hab hbP'
  have h2 := key a ha b' hab' hb'P
  have h3 := key a ha (b + b') hab2 hbb'P
  have h12 := mul_mem h1 h2
  rw [spRho_mul hβ hab hab' 0 0 hab2,
    spRho_congr hβ hab2 hab2 rfl rfl (show (0 : ZMod 2) + 0 + β b b' = 1 by
      rw [hbb', zero_add, zero_add])] at h12
  have h123 := mul_mem h12 h3
  have h0 : β a (b + b' + (b + b')) = 0 := by rw [vec_add_self]; exact map_zero _
  have hz : β a 0 = 0 := map_zero _
  rw [spRho_mul hβ hab2 hab2 1 0 h0,
    spRho_congr hβ h0 hz rfl (vec_add_self _) (show (1 : ZMod 2) + 0 + β (b + b') (b + b') = 1 by
      rw [hβ.self_eq_zero, add_zero, add_zero]), spRho_zero_one] at h123
  exact hEcτ a ha h123

end CFSG.LargeExtraspecial.S4
