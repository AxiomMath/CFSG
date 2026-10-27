module

public import CFSG.GH74.Generic.S3.JInIw
public import CFSG.GH74.Generic.S3.FourGroup
public import CFSG.GH74.Generic.S3.L3Cover

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups

section Move

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_map_conj' (J : Subgroup G) (s x : G) :
    x ∈ J.map (MulAut.conj s).toMonoidHom ↔ s⁻¹ * x * s ∈ J := by
  rw [Subgroup.mem_map_equiv]
  simp [MulAut.conj_symm_apply]

omit [Finite G] in
theorem map_conj_map_conj_inv (J : Subgroup G) (s : G) :
    (J.map (MulAut.conj s⁻¹).toMonoidHom).map (MulAut.conj s).toMonoidHom = J := by
  ext x
  rw [mem_map_conj', mem_map_conj']
  have : s⁻¹⁻¹ * (s⁻¹ * x * s) * s⁻¹ = x := by group
  rw [this]

theorem mem_V_cases {V : Subgroup G} {w : G} (hs : Count23Setup V w) {a b : G}
    (ha : a ∈ Vsharp V) (hb : b ∈ Vsharp V) (hab : a ≠ b) {x : G} (hx : x ∈ V) :
    x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have ha2 : a * a = 1 := hs.V_sq a ha.1
  have hb2 : b * b = 1 := hs.V_sq b hb.1
  have hc : a * b = b * a := hs.V_comm a ha.1 b hb.1
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    calc a = a * (b * b) := by rw [hb2, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = b := by rw [h, one_mul]
  have hab_a : a ≠ a * b := by
    intro h
    apply hb.2
    have : a * 1 = a * b := by rw [mul_one]; exact h
    exact (mul_left_cancel this).symm
  have hab_b : b ≠ a * b := by
    intro h
    apply ha.2
    have : 1 * b = a * b := by rw [one_mul]; exact h
    exact (mul_right_cancel this).symm
  have hsub : ({1, a, b, a * b, x} : Set G) ⊆ (V : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact ha.1
    · exact hb.1
    · exact V.mul_mem ha.1 hb.1
    · exact hx
  have hcard5 : ({1, a, b, a * b, x} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
      Set.ncard_pair]
    · exact fun h => h4 h.symm
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab_b, fun h => h3 h.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hab, hab_a, fun h => h2 h.symm⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => ha.2 h.symm, fun h => hb.2 h.symm, fun h => hab1 h.symm, fun h => h1 h.symm⟩
  have hV4 : (V : Set G).ncard = 4 := by
    have h : Nat.card ↥V = (V : Set G).ncard := Nat.card_coe_set_eq (V : Set G)
    rw [← h, hs.card_V]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem exists_move {t : StatedLieTag} {p f : ℕ} {v w : G} {Iv Iw Ivw P V : Subgroup G} {v₁ : G}
    (hcfg : Config22 G t p f v w Iv Iw Ivw P V v₁)
    (h4 : ∀ a b : G, a ∈ Iw → b ∈ Iw → a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 →
      a ≠ b → ∃ g ∈ Iw, g * a * g⁻¹ = a * b ∧ g * b * g⁻¹ = a)
    {e : G} (he : e ∈ Vsharp V) :
    ∃ g ∈ Iw, g * v * g⁻¹ = e ∧ (∀ a ∈ V, g * a * g⁻¹ ∈ V) ∧ (∀ a ∈ V, g⁻¹ * a * g ∈ V) := by
  by_cases hev : e = v
  · subst hev
    exact ⟨1, Iw.one_mem, by group, fun a ha => by simpa using ha, fun a ha => by simpa using ha⟩
  · have hs := hcfg.setup
    have e2 : e * e = 1 := hs.V_sq e he.1
    have v2 : v * v = 1 := hs.V_sq v hcfg.hv.1
    have hcomm : e * v = v * e := hs.V_comm e he.1 v hcfg.hv.1
    obtain ⟨g, hgI, hg1, hg2⟩ := h4 e v (hcfg.hVIw he.1) (hcfg.hVIw hcfg.hv.1) e2 v2 hcomm he.2
      hcfg.hv.2 hev
    have hg3 : g * (e * v) * g⁻¹ = v := by
      calc g * (e * v) * g⁻¹ = (g * e * g⁻¹) * (g * v * g⁻¹) := by group
        _ = (e * v) * e := by rw [hg1, hg2]
        _ = v := by
          calc (e * v) * e = (v * e) * e := by rw [hcomm]
            _ = v * (e * e) := by rw [mul_assoc]
            _ = v := by rw [e2, mul_one]
    have hev' : e * v ∈ V := V.mul_mem he.1 hcfg.hv.1
    have k1 : g⁻¹ * e * g = v := by
      calc g⁻¹ * e * g = g⁻¹ * (g * v * g⁻¹) * g := by rw [hg2]
        _ = v := by group
    have k2 : g⁻¹ * v * g = e * v := by
      calc g⁻¹ * v * g = g⁻¹ * (g * (e * v) * g⁻¹) * g := by rw [hg3]
        _ = e * v := by group
    have k3 : g⁻¹ * (e * v) * g = e := by
      calc g⁻¹ * (e * v) * g = g⁻¹ * (g * e * g⁻¹) * g := by rw [hg1]
        _ = e := by group
    refine ⟨g, hgI, hg2, ?_, ?_⟩
    · intro a ha
      rcases mem_V_cases hs he hcfg.hv hev ha with rfl | rfl | rfl | rfl
      · simp
      · rw [hg1]; exact hev'
      · rw [hg2]; exact he.1
      · rw [hg3]; exact hcfg.hv.1
    · intro a ha
      rcases mem_V_cases hs he hcfg.hv hev ha with rfl | rfl | rfl | rfl
      · simp
      · rw [k1]; exact hcfg.hv.1
      · rw [k2]; exact hev'
      · rw [k3]; exact he.1

theorem exists_trans {t : StatedLieTag} {p f : ℕ} {v w : G} {Iv Iw Ivw P V : Subgroup G} {v₁ : G}
    (hcfg : Config22 G t p f v w Iv Iw Ivw P V v₁)
    (h4 : ∀ a b : G, a ∈ Iw → b ∈ Iw → a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 →
      a ≠ b → ∃ g ∈ Iw, g * a * g⁻¹ = a * b ∧ g * b * g⁻¹ = a)
    {w₁ e : G} (hw₁ : w₁ ∈ Wset V w) (he : e ∈ Vsharp V) :
    ∃ s : G, s * w * s⁻¹ = w₁ ∧ s * v * s⁻¹ = e ∧ (∀ a ∈ V, s * a * s⁻¹ ∈ V) ∧
      (∀ a ∈ V, s⁻¹ * a * s ∈ V) := by
  obtain ⟨n, hn, hn', hnw⟩ := hcfg.conj w₁ hw₁
  have he' : n⁻¹ * e * n ∈ Vsharp V := by
    refine ⟨?_, ?_⟩
    · have := hn' e he.1
      simpa using this
    · intro h
      apply he.2
      calc e = n * (n⁻¹ * e * n) * n⁻¹ := by group
        _ = 1 := by rw [h]; group
  obtain ⟨g, hgI, hgv, hg1, hg2⟩ := exists_move hcfg h4 he'
  have hgw : g * w * g⁻¹ = w := by
    have := mem_centralizer_singleton_iff.1 (hcfg.conf.comp_w.1.1 hgI)
    rw [this]
    group
  refine ⟨n * g, ?_, ?_, ?_, ?_⟩
  · calc n * g * w * (n * g)⁻¹ = n * (g * w * g⁻¹) * n⁻¹ := by group
      _ = n * w * n⁻¹ := by rw [hgw]
      _ = w₁ := hnw
  · calc n * g * v * (n * g)⁻¹ = n * (g * v * g⁻¹) * n⁻¹ := by group
      _ = n * (n⁻¹ * e * n) * n⁻¹ := by rw [hgv]
      _ = e := by group
  · intro a ha
    have h1 := hn _ (hg1 a ha)
    have : n * g * a * (n * g)⁻¹ = n * (g * a * g⁻¹) * n⁻¹ := by group
    rw [this]
    exact h1
  · intro a ha
    have h1 := hn' a ha
    have h2 := hg2 _ (by simpa using h1)
    have : (n * g)⁻¹ * a * (n * g) = g⁻¹ * (n⁻¹ * a * n) * g := by group
    rw [this]
    simpa using h2

end Move

section Core

variable {G : Type} [Group G] [Finite G]

theorem layers_core {F : Type} [Field F] {t : StatedLieTag} {p f : ℕ} {v w : G}
    {Iv Iw Ivw P V : Subgroup G} {v₁ : G}
    (hcfg : Config22 G t p f v w Iv Iw Ivw P V v₁)
    (h4 : ∀ a b : G, a ∈ Iw → b ∈ Iw → a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 →
      a ≠ b → ∃ g ∈ Iw, g * a * g⁻¹ = a * b ∧ g * b * g⁻¹ = a)
    (hIvC : IsSL2Comp F w v Iv)
    (hU : ∀ J : Subgroup G, IsSL2Comp F w v J → J = Iv)
    (hD0 : ∀ e ∈ Vsharp V, e ≠ v → ∃ j ∈ Iv, j * e ≠ e * j) :
    (∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∃! J : Subgroup G, IsSL2Comp F w₁ e J) ∧
    (∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J →
      ∀ e' ∈ Vsharp V, e' ≠ e → ∃ j ∈ J, j * e' ≠ e' * j) ∧
    (∀ w₁ ∈ Wset V w, ∀ e ∈ Vsharp V, ∀ J : Subgroup G, IsSL2Comp F w₁ e J → IsCompC J e) := by
  have fwd : ∀ {w₁ e s : G}, s * w * s⁻¹ = w₁ → s * v * s⁻¹ = e →
      IsSL2Comp F w₁ e (Iv.map (MulAut.conj s).toMonoidHom) := by
    intro w₁ e s hsw hsv
    have := hIvC.map_conj s
    rwa [hsw, hsv] at this
  have back : ∀ {w₁ e s : G}, s * w * s⁻¹ = w₁ → s * v * s⁻¹ = e → ∀ J : Subgroup G,
      IsSL2Comp F w₁ e J → J = Iv.map (MulAut.conj s).toMonoidHom := by
    intro w₁ e s hsw hsv J hJ
    have h1 := hJ.map_conj s⁻¹
    have e1 : s⁻¹ * w₁ * s⁻¹⁻¹ = w := by rw [← hsw]; group
    have e2 : s⁻¹ * e * s⁻¹⁻¹ = v := by rw [← hsv]; group
    rw [e1, e2] at h1
    have h2 := hU _ h1
    calc J = (J.map (MulAut.conj s⁻¹).toMonoidHom).map (MulAut.conj s).toMonoidHom :=
          (map_conj_map_conj_inv J s).symm
      _ = Iv.map (MulAut.conj s).toMonoidHom := by rw [h2]
  refine ⟨?_, ?_, ?_⟩
  · intro w₁ hw₁ e he
    obtain ⟨s, hsw, hsv, -, -⟩ := exists_trans hcfg h4 hw₁ he
    exact ⟨_, fwd hsw hsv, fun J hJ => back hsw hsv J hJ⟩
  · intro w₁ hw₁ e he J hJ e' he' hne
    obtain ⟨s, hsw, hsv, hs1, hs2⟩ := exists_trans hcfg h4 hw₁ he
    have hJeq := back hsw hsv J hJ
    have he'' : s⁻¹ * e' * s ∈ Vsharp V := by
      refine ⟨hs2 e' he'.1, fun h => he'.2 ?_⟩
      calc e' = s * (s⁻¹ * e' * s) * s⁻¹ := by group
        _ = 1 := by rw [h]; group
    have hne'' : s⁻¹ * e' * s ≠ v := by
      intro h
      apply hne
      calc e' = s * (s⁻¹ * e' * s) * s⁻¹ := by group
        _ = s * v * s⁻¹ := by rw [h]
        _ = e := hsv
    obtain ⟨j, hjIv, hjn⟩ := hD0 _ he'' hne''
    have hjJ : s * j * s⁻¹ ∈ J := by
      rw [hJeq, mem_map_conj']
      have : s⁻¹ * (s * j * s⁻¹) * s = j := by group
      rw [this]
      exact hjIv
    refine ⟨s * j * s⁻¹, hjJ, fun h => hjn ?_⟩
    calc j * (s⁻¹ * e' * s) = s⁻¹ * (s * j * s⁻¹ * e') * s := by group
      _ = s⁻¹ * (e' * (s * j * s⁻¹)) * s := by rw [h]
      _ = (s⁻¹ * e' * s) * j := by group
  · intro w₁ hw₁ e he J hJ
    obtain ⟨s, hsw, hsv, -, -⟩ := exists_trans hcfg h4 hw₁ he
    have hJeq := back hsw hsv J hJ
    have := hcfg.conf.comp_v.map_conj s
    rw [hsv] at this
    rw [hJeq]
    exact this

end Core

section Models

variable {G : Type} [Group G]

theorem orderOf_conj_eq' (a g : G) : orderOf (g * a * g⁻¹) = orderOf a := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
  simpa using this

theorem map_conj_le_of_mem {U H : Subgroup G} (hU : U ≤ H) {g : G} (hg : g ∈ H) :
    U.map (MulAut.conj g).toMonoidHom ≤ H := by
  rintro _ ⟨u, hu, rfl⟩
  have : (MulAut.conj g).toMonoidHom u = g * u * g⁻¹ := by simp
  rw [this]
  exact H.mul_mem (H.mul_mem hg (hU hu)) (H.inv_mem hg)

section Linear

theorem sl2_unique_lin {F : Type} [Field F] [Finite F] (hF4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    {α : SL(3, F) →* G} (hker : α.ker ≤ Subgroup.center SL(3, F)) {v : G} (hv : v ∈ α.range)
    (hv2 : v * v = 1) (hv1 : v ≠ 1) {J₁ J₂ : Subgroup G} (h₁ : J₁ ≤ α.range) (h₂ : J₂ ≤ α.range)
    (e₁ : SL(2, F) ≃* J₁) (e₂ : SL(2, F) ≃* J₂) (c₁ : ∀ u ∈ J₁, u * v = v * u)
    (c₂ : ∀ u ∈ J₂, u * v = v * u) : J₁ = J₂ := by
  obtain ⟨z, hz2, hzv⟩ := CFSG.GH74.GLS.LU.exists_involution_lift α hker
    CFSG.GH74.GLS.LU.center_pow_three hv hv2
  have hz1 : z ≠ 1 := fun h => hv1 (by rw [← hzv, h, map_one])
  obtain ⟨g, hg, -⟩ := CFSG.GH74.GLS.LU.isLongRootSL2_of_involution h2 hz2 hz1
  have u₁ := CFSG.GH74.GLS.LU.eq_map_longRootGroup hF4 h2 α hker hz2 hz1 (j := 0) (by omega) g hg h₁ e₁
    (by rw [hzv]; exact c₁)
  have u₂ := CFSG.GH74.GLS.LU.eq_map_longRootGroup hF4 h2 α hker hz2 hz1 (j := 0) (by omega) g hg h₂ e₂
    (by rw [hzv]; exact c₂)
  rw [u₁, u₂]

theorem sl2_noncomm_lin {F : Type} [Field F] [Finite F] (hF4 : 4 ≤ Nat.card F) (h2 : (2 : F) ≠ 0)
    {α : SL(3, F) →* G} (hker : α.ker ≤ Subgroup.center SL(3, F)) {U : Subgroup G}
    (hU : U ≤ α.range) (eU : SL(2, F) ≃* U) {a g : G} (ha : a ∈ U) (hg : g ∈ α.range)
    (ha2 : orderOf a = 2) (haU : ∀ u ∈ U, u * a = a * u) (hab : a ≠ g * a * g⁻¹)
    (hcomm : a * (g * a * g⁻¹) = (g * a * g⁻¹) * a) :
    ∃ x ∈ U, x * (g * a * g⁻¹) ≠ (g * a * g⁻¹) * x := by
  have hV'le : U.map (MulAut.conj g).toMonoidHom ≤ α.range := map_conj_le_of_mem hU hg
  have hb : g * a * g⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom := ⟨a, ha, by simp⟩
  have hb2 : orderOf (g * a * g⁻¹) = 2 := by rw [orderOf_conj_eq']; exact ha2
  have hbV : ∀ y ∈ U.map (MulAut.conj g).toMonoidHom, y * (g * a * g⁻¹) = (g * a * g⁻¹) * y := by
    rintro _ ⟨u, hu, rfl⟩
    have e1 : (MulAut.conj g).toMonoidHom u = g * u * g⁻¹ := by simp
    rw [e1]
    calc g * u * g⁻¹ * (g * a * g⁻¹) = g * (u * a) * g⁻¹ := by group
      _ = g * (a * u) * g⁻¹ := by rw [haU u hu]
      _ = g * a * g⁻¹ * (g * u * g⁻¹) := by group
  exact (CFSG.GH74.GLS.LU.linearBlockStandardPair_of_central_involutions hF4 h2 α hker hU hV'le eU
    (eU.trans (U.equivMapOfInjective _ (MulAut.conj g).injective)) ha hb ha2 hb2 haU hbV hab hcomm).2

end Linear

section Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem sl2_unique_uni (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) (hF4 : 4 ≤ p ^ f)
    {α : CFSG.ClassicalInvolution.Phan.Su K p f 3 →* G}
    (hker : α.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su K p f 3)) {v : G}
    (hv : v ∈ α.range) (hv2 : v * v = 1) (hv1 : v ≠ 1) {J₁ J₂ : Subgroup G} (h₁ : J₁ ≤ α.range)
    (h₂ : J₂ ≤ α.range) (e₁ : SL(2, F) ≃* J₁) (e₂ : SL(2, F) ≃* J₂)
    (c₁ : ∀ u ∈ J₁, u * v = v * u) (c₂ : ∀ u ∈ J₂, u * v = v * u) : J₁ = J₂ := by
  obtain ⟨z, hz2, hzv⟩ := CFSG.GH74.GLS.LU.exists_involution_lift α hker
    (CFSG.GH74.GLS.LU.center_pow_three_su hK) hv hv2
  have hz1 : z ≠ 1 := fun h => hv1 (by rw [← hzv, h, map_one])
  obtain ⟨g, hg, -⟩ := CFSG.GH74.GLS.LU.isLongRootSU2_of_involution hK hp hz2 hz1
  have u₁ := CFSG.GH74.GLS.LU.eq_map_longRootGroupSU hK hp hF hF4 α hker hz2 hz1 (j := 0)
    (by omega) g hg h₁ e₁ (by rw [hzv]; exact c₁)
  have u₂ := CFSG.GH74.GLS.LU.eq_map_longRootGroupSU hK hp hF hF4 α hker hz2 hz1 (j := 0)
    (by omega) g hg h₂ e₂ (by rw [hzv]; exact c₂)
  rw [u₁, u₂]

theorem sl2_noncomm_uni (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) (hF4 : 4 ≤ p ^ f)
    {α : CFSG.ClassicalInvolution.Phan.Su K p f 3 →* G}
    (hker : α.ker ≤ Subgroup.center (CFSG.ClassicalInvolution.Phan.Su K p f 3)) {U : Subgroup G}
    (hU : U ≤ α.range) (eU : SL(2, F) ≃* U) {a g : G} (ha : a ∈ U) (hg : g ∈ α.range)
    (ha2 : orderOf a = 2) (haU : ∀ u ∈ U, u * a = a * u) (hab : a ≠ g * a * g⁻¹)
    (hcomm : a * (g * a * g⁻¹) = (g * a * g⁻¹) * a) :
    ∃ x ∈ U, x * (g * a * g⁻¹) ≠ (g * a * g⁻¹) * x := by
  have hV'le : U.map (MulAut.conj g).toMonoidHom ≤ α.range := map_conj_le_of_mem hU hg
  have hb : g * a * g⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom := ⟨a, ha, by simp⟩
  have hb2 : orderOf (g * a * g⁻¹) = 2 := by rw [orderOf_conj_eq']; exact ha2
  have hbV : ∀ y ∈ U.map (MulAut.conj g).toMonoidHom, y * (g * a * g⁻¹) = (g * a * g⁻¹) * y := by
    rintro _ ⟨u, hu, rfl⟩
    have e1 : (MulAut.conj g).toMonoidHom u = g * u * g⁻¹ := by simp
    rw [e1]
    calc g * u * g⁻¹ * (g * a * g⁻¹) = g * (u * a) * g⁻¹ := by group
      _ = g * (a * u) * g⁻¹ := by rw [haU u hu]
      _ = g * a * g⁻¹ * (g * u * g⁻¹) := by group
  exact (CFSG.GH74.GLS.LU.unitaryBlockStandardPair_of_central_involutions hK hp hF hF4 α hker hU
    hV'le eU (eU.trans (U.equivMapOfInjective _ (MulAut.conj g).injective)) ha hb ha2 hb2 haU hbV
    hab hcomm).2

end Unitary

end Models

theorem b_S3_layers_of_cover (hcov : B_L3_cover) : B_S3_layers := by
  intro G _ _ hG t p f v w Iv Iw Ivw P V v₁ hcfg F _ _ hF
  have C := hcfg.conf
  have h4 : ∀ a b : G, a ∈ Iw → b ∈ Iw → a * a = 1 → b * b = 1 → a * b = b * a → a ≠ 1 → b ≠ 1 →
      a ≠ b → ∃ g ∈ Iw, g * a * g⁻¹ = a * b ∧ g * b * g⁻¹ = a :=
    fun a b ha hb ha2 hb2 hab ha1 hb1 hne => b_L3_fourgroup G t p f C.tag C.prime.1 C.prime.2.1
      C.prime.2.2 Iw C.comp_w.1.isQuasisimple C.odd_w C.model_w a b ha hb ha2 hb2 hab ha1 hb1 hne
  have hIvw : Iv ≤ centralizer ({w} : Set G) := fun i hi => C.comp_w.1.1 (C.le_w hi)
  obtain ⟨F', _, _, hF', ⟨eIv'⟩⟩ := C.iso_v
  obtain ⟨σ⟩ := exists_ringEquiv_of_card_eq (K := F') (F := F) (by rw [hF, hF'])
  have eIv : SL(2, F) ≃* Iv :=
    (CFSG.ClassicalModels.specialLinearFieldEquiv σ (Fin 2)).symm.trans eIv'
  have hIvC : IsSL2Comp F w v Iv := IsSL2Comp.of_isCompC C.comp_v hIvw C.v_mem ⟨eIv⟩
  have hJIw : ∀ J : Subgroup G, IsSL2Comp F w v J → J ≤ Iw := fun J hJ =>
    b_S3_J_in_Iw G hG t p f v w Iv Iw Ivw P V v₁ hcfg F inferInstance inferInstance hF v hcfg.hv J hJ
  have hv2 : v * v = 1 := hcfg.setup.V_sq v hcfg.hv.1
  have hv1 : v ≠ 1 := hcfg.hv.2
  have hvo : orderOf v = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  have hvIw : v ∈ Iw := hcfg.hVIw hcfg.hv.1
  have hF4 : 4 ≤ p ^ f := by
    have := C.prime.2.2
    omega
  rcases C.tag with rfl | rfl
  · obtain ⟨α, hker, hrange⟩ := (hcov G p f C.prime.1 C.prime.2.1 C.prime.2.2 Iw
      C.comp_w.1.isQuasisimple C.odd_w).1 C.model_w F inferInstance inferInstance hF
    have hF4' : 4 ≤ Nat.card F := by rw [hF]; exact hF4
    have h2 : (2 : F) ≠ 0 :=
      Ring.two_ne_zero (ringChar_ne_two_of_card_pow C.prime.1 C.prime.2.1 hF)
    refine layers_core hcfg h4 hIvC (fun J hJ => ?_) (fun e he hev => ?_)
    · exact sl2_unique_lin hF4' h2 hker (by rw [hrange]; exact hvIw) hv2 hv1
        (by rw [hrange]; exact hJIw J hJ) (by rw [hrange]; exact C.le_w) (Classical.choice hJ.iso) eIv
        (fun u hu => (hJ.commute u hu).2) (fun u hu => (hIvC.commute u hu).2)
    · obtain ⟨g, hgI, hgv, -, -⟩ := exists_move hcfg h4 he
      have := sl2_noncomm_lin hF4' h2 hker (U := Iv) (by rw [hrange]; exact C.le_w) eIv (a := v)
        (g := g) C.v_mem (by rw [hrange]; exact hgI) hvo (fun u hu => (hIvC.commute u hu).2)
        (by rw [hgv]; exact fun h => hev h.symm)
        (by rw [hgv]; exact hcfg.setup.V_comm v hcfg.hv.1 e he.1)
      rwa [hgv] at this
  · have : Fact p.Prime := ⟨C.prime.1⟩
    have hf : f ≠ 0 := by
      rintro rfl
      have := C.prime.2.2
      rw [pow_zero] at this
      omega
    have hF₂ : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
      rw [GaloisField.card p (2 * f) (by omega), mul_comm, pow_mul]
    obtain ⟨α₀, hker₀, hrange₀⟩ := (hcov G p f C.prime.1 C.prime.2.1 C.prime.2.2 Iw
      C.comp_w.1.isQuasisimple C.odd_w).2 C.model_w (GaloisField p (2 * f)) inferInstance
      inferInstance hF₂
    let eSU : CFSG.ClassicalInvolution.Phan.Su (GaloisField p (2 * f)) p f 3 ≃*
        ↥(StatedSU 3 (p ^ f) (GaloisField p (2 * f))) :=
      MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF₂ 3)
    obtain ⟨α, hker, hrange⟩ := exists_hom_of_mulEquiv eSU.symm α₀ hker₀
    have hrangeI : α.range = Iw := hrange.trans hrange₀
    refine layers_core hcfg h4 hIvC (fun J hJ => ?_) (fun e he hev => ?_)
    · exact sl2_unique_uni hF₂ C.prime.2.1 hF hF4 hker (by rw [hrangeI]; exact hvIw) hv2 hv1
        (by rw [hrangeI]; exact hJIw J hJ) (by rw [hrangeI]; exact C.le_w)
        (Classical.choice hJ.iso) eIv (fun u hu => (hJ.commute u hu).2)
        (fun u hu => (hIvC.commute u hu).2)
    · obtain ⟨g, hgI, hgv, -, -⟩ := exists_move hcfg h4 he
      have := sl2_noncomm_uni hF₂ C.prime.2.1 hF hF4 hker (U := Iv) (by rw [hrangeI]; exact C.le_w)
        eIv (a := v) (g := g) C.v_mem (by rw [hrangeI]; exact hgI) hvo
        (fun u hu => (hIvC.commute u hu).2) (by rw [hgv]; exact fun h => hev h.symm)
        (by rw [hgv]; exact hcfg.setup.V_comm v hcfg.hv.1 e he.1)
      rwa [hgv] at this

end CFSG.GH74.Generic.S3
