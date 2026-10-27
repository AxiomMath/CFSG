module

public import CFSG.CGT.Foote81L6.TStruct.Classes

public section

namespace CFSG.CGT.Foote81L6

open Subgroup TStruct

theorem TStruct.eq_map_conj_inv_of_map_conj_eq {G : Type*} [Group G] {E F : Subgroup G} {k : G}
    (h : E.map (MulAut.conj k).toMonoidHom = F) : E = F.map (MulAut.conj k⁻¹).toMonoidHom := by
  rw [← h, map_conj_inv_map_conj]

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem b₀_mem_of_isFourIn {V : Subgroup G} (hV : IsFourIn D.B₀ V) : D.b₀ ∈ V := by
  obtain ⟨e⟩ := D.B₀_iso
  have h := symm_zc_mem_four e D.one_le_n_sub_one hV
  rwa [symm_zc_eq e D.two_le_n_sub_one D.b₀_mem D.b₀_ne_one fun y hy => D.b₀_comm y hy] at h

theorem b₁_mem_of_isFourIn {V : Subgroup G} (hV : IsFourIn D.B₁ V) : D.b₁ ∈ V := by
  obtain ⟨e⟩ := D.B₁_iso
  have h := symm_zc_mem_four e D.one_le_n_sub_one hV
  rwa [symm_zc_eq e D.two_le_n_sub_one D.b₁_mem D.b₁_ne_one fun y hy => D.b₁_comm y hy] at h

theorem inf_A_map_conj {y : G} (hy : y ∈ T) (E : Subgroup G) :
    E.map (MulAut.conj y).toMonoidHom ⊓ D.A = (E ⊓ D.A).map (MulAut.conj y).toMonoidHom :=
  inf_map_conj (D.A_normal_T hy) fun v hv => by simpa using D.A_normal_T (inv_mem hy) v hv

theorem mem_R_of_mem_normalizer {E : Subgroup G} (hE : IsE64 T E) {α w₀ w₁ : G} (hα : α ∈ D.A)
    (hw₀ : w₀ ∈ D.B₀) (hw₁ : w₁ ∈ D.B₁) (hN : α * (w₀ * w₁) ∈ normalizer (E : Set G)) :
    α ∈ D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G) ∧
      w₀ ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G) ∧
      w₁ ∈ D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G) := by
  obtain ⟨-, hA, hB₀, hB₁⟩ := D.E64_decomp hE
  haveI := hA.finite
  haveI := hB₀.finite
  haveI := hB₁.finite
  refine ⟨mem_inf.2 ⟨hα, mem_normalizer_of_forall_conj_mem fun v hv => ?_⟩,
    mem_inf.2 ⟨hw₀, mem_normalizer_of_forall_conj_mem fun v hv => ?_⟩,
    mem_inf.2 ⟨hw₁, mem_normalizer_of_forall_conj_mem fun v hv => ?_⟩⟩
  · have h := (mem_normalizer_iff.1 hN v).1 (mem_inf.1 hv).1
    rw [D.conj_mul_of_mem_A hw₀ hw₁ (mem_inf.1 hv).2] at h
    exact mem_inf.2 ⟨h, mul_mem (mul_mem hα (mem_inf.1 hv).2) (inv_mem hα)⟩
  · have h := (mem_normalizer_iff.1 hN v).1 (mem_inf.1 hv).1
    rw [D.conj_mul_of_mem_B₀ hα hw₀ hw₁ (mem_inf.1 hv).2] at h
    exact mem_inf.2 ⟨h, mul_mem (mul_mem hw₀ (mem_inf.1 hv).2) (inv_mem hw₀)⟩
  · have h := (mem_normalizer_iff.1 hN v).1 (mem_inf.1 hv).1
    rw [D.conj_mul_of_mem_B₁ hα hw₀ hw₁ (mem_inf.1 hv).2] at h
    exact mem_inf.2 ⟨h, mul_mem (mul_mem hw₁ (mem_inf.1 hv).2) (inv_mem hw₁)⟩

theorem normalizer_E64_inf_T₁ {E : Subgroup G} (hE : IsE64 T E) :
    D.T₁ ⊓ normalizer (E : Set G) = (D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G)) ⊔
      ((D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G)) ⊔
        (D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx1, hxN⟩ := mem_inf.1 hx
    obtain ⟨α, hα, w, hw, rfl⟩ := D.mem_T₁_iff.1 hx1
    obtain ⟨w₀, hw₀, w₁, hw₁, rfl⟩ := D.mem_B₀B₁_iff.1 hw
    obtain ⟨h1, h2, h3⟩ := D.mem_R_of_mem_normalizer hE hα hw₀ hw₁ hxN
    exact mul_mem (mem_sup_left h1) (mul_mem (mem_sup_right (mem_sup_left h2))
      (mem_sup_right (mem_sup_right h3)))
  · refine sup_le (fun x hx => mem_inf.2 ⟨D.A_le_T₁ (mem_inf.1 hx).1,
      D.mem_normalizer_of_mem_R hE hx⟩) (sup_le (fun x hx => mem_inf.2
        ⟨D.B₀_le_T₁ (mem_inf.1 hx).1, D.mem_normalizer_of_mem_R₀ hE hx⟩)
      fun x hx => mem_inf.2 ⟨D.B₁_le_T₁ (mem_inf.1 hx).1, D.mem_normalizer_of_mem_R₁ hE hx⟩)

theorem symm_of_mem_normalizer {E : Subgroup G} (hE : IsE64 T E) {x : G} (hx : x ∈ D.T₀)
    (hx1 : x ∉ D.T₁) (hxN : x ∈ normalizer (E : Set G)) : (D.typ E).1 = (D.typ E).2 := by
  obtain ⟨-, -, h₀, h₁⟩ := D.E64_decomp (hE.map_conj (D.B_le_T D.s_mem_B))
  have hxs : x * D.s ∈ D.T₁ := (D.mem_T₁_or_mul_s_mem_T₁ hx).resolve_left hx1
  have e : E.map (MulAut.conj x).toMonoidHom =
      (E.map (MulAut.conj D.s).toMonoidHom).map (MulAut.conj (x * D.s)).toMonoidHom := by
    rw [map_conj_map_conj, mul_assoc, D.s_mul_s, mul_one]
  have h := D.typ_map_conj_T₁ h₀ h₁ hxs
  rw [← e, map_conj_eq_self_of_mem_normalizer hxN, D.typ_map_conj_s] at h
  generalize D.typ E = τ at h ⊢
  obtain ⟨a, b⟩ := τ
  exact (Prod.mk.injEq _ _ _ _ ▸ h).2.symm

theorem card_T₁_inf_normalizer_eq {E : Subgroup G} (hE : IsE64 T E) :
    Nat.card ↥(D.T₁ ⊓ normalizer (E : Set G)) =
      Nat.card ↥(D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G)) * 2 ^ 6 := by
  rw [D.normalizer_E64_inf_T₁ hE]
  have hR : D.A ⊓ normalizer ((E ⊓ D.A : Subgroup G) : Set G) ≤ D.A := inf_le_left
  have hR₀ : D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G) ≤ D.B₀ := inf_le_left
  have hR₁ : D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G) ≤ D.B₁ := inf_le_left
  have hc₀₁ : ∀ x ∈ D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G),
      ∀ y ∈ D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G), x * y = y * x :=
    fun x hx y hy => D.B₀_comm_B₁ x (hR₀ hx) y (hR₁ hy)
  have hle : (D.B₀ ⊓ normalizer ((E ⊓ D.B₀ : Subgroup G) : Set G)) ⊔
      (D.B₁ ⊓ normalizer ((E ⊓ D.B₁ : Subgroup G) : Set G)) ≤ D.B₀ ⊔ D.B₁ := sup_le_sup hR₀ hR₁
  rw [card_sup_of_le_normalizer
      (le_normalizer_of_comm fun x hx y hy => D.A_comm_B₀B₁ x (hR hx) y (hle hy))
      (eq_bot_iff.2 ((inf_le_inf hR hle).trans D.A_inf_B₀B₁.le)),
    card_sup_of_le_normalizer (le_normalizer_of_comm hc₀₁)
      (eq_bot_iff.2 ((inf_le_inf hR₀ hR₁).trans D.B₀_inf_B₁.le)),
    D.card_R₀ hE, D.card_R₁ hE]
  norm_num

theorem exists_conj_Frep_of_typ {E : Subgroup G} (hE : IsE64 T E) (hA : E ⊓ D.A = D.repU)
    {i j : ZMod 2} (h : D.typ E = (i, j)) :
    ∃ β ∈ D.B₀ ⊔ D.B₁, E.map (MulAut.conj β).toMonoidHom = D.Frep i j :=
  D.exists_conj_of_typ_eq hE (D.isE64_Frep i j) (by rw [hA, Frep_inf_A]) (by rw [h, typ_Frep])

theorem exists_conj_Frep_of_inf_A {E : Subgroup G} (hE : IsE64 T E) (hA : E ⊓ D.A = D.repU) :
    ∃ h ∈ D.T₀, E.map (MulAut.conj h).toMonoidHom = D.Frep 0 0 ∨
      E.map (MulAut.conj h).toMonoidHom = D.Frep 1 1 ∨
      E.map (MulAut.conj h).toMonoidHom = D.Frep 0 1 := by
  have h01 : ∀ u : ZMod 2, u = 0 ∨ u = 1 := by decide
  have hB : ∀ β ∈ D.B₀ ⊔ D.B₁, β ∈ D.T₀ := fun β hβ => D.T₁_le_T₀ (D.B₀B₁_le_T₁ hβ)
  rcases h01 (D.typ E).1 with hi | hi <;> rcases h01 (D.typ E).2 with hj | hj
  · obtain ⟨β, hβ, e⟩ := D.exists_conj_Frep_of_typ hE hA (Prod.ext hi hj)
    exact ⟨β, hB β hβ, Or.inl e⟩
  · obtain ⟨β, hβ, e⟩ := D.exists_conj_Frep_of_typ hE hA (Prod.ext hi hj)
    exact ⟨β, hB β hβ, Or.inr (Or.inr e)⟩
  · have hsT := D.B_le_T D.s_mem_B
    have hAs : E.map (MulAut.conj D.s).toMonoidHom ⊓ D.A = D.repU := by
      rw [D.inf_A_map_conj hsT, hA]
      exact map_conj_eq_self_of_comm fun x hx =>
        (D.A_comm_B x (D.isFourIn_repU.1 hx) D.s D.s_mem_B).symm
    have hts : D.typ (E.map (MulAut.conj D.s).toMonoidHom) = (0, 1) := by
      simp only [D.typ_map_conj_s, show D.typ E = (1, 0) from Prod.ext hi hj, Prod.swap_prod_mk]
    obtain ⟨β, hβ, e⟩ := D.exists_conj_Frep_of_typ (hE.map_conj hsT) hAs hts
    refine ⟨β * D.s, mul_mem (hB β hβ) (D.B_le_T₀ D.s_mem_B), Or.inr (Or.inr ?_)⟩
    rw [← map_conj_map_conj]
    exact e
  · obtain ⟨β, hβ, e⟩ := D.exists_conj_Frep_of_typ hE hA (Prod.ext hi hj)
    exact ⟨β, hB β hβ, Or.inr (Or.inl e)⟩

theorem typ_four_sConj {U' W : Subgroup G} (hU' : IsFourIn D.A U') (hW : IsFourIn D.B₀ W) :
    D.typ (U' ⊔ (W ⊔ D.sConj W)) = (D.cls W, D.cls W) := by
  obtain ⟨-, h₀, h₁⟩ := D.inf_of_four hU' hW (D.isFourIn_sConj₀ hW)
  rw [typ, h₀, h₁, sConj_sConj]

theorem exists_four_of_mem_A_sup {x : G} (hx : x ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁))
    (hx2 : x * x = 1) : ∃ U' : Subgroup G, IsFourIn D.A U' ∧
      ∀ E : Subgroup G, U' ≤ E → D.b₀ ∈ E → D.b₁ ∈ E → x ∈ E := by
  have hZB : zpowers D.b₀ ⊔ zpowers D.b₁ ≤ D.B :=
    sup_le (zpowers_le.2 D.b₀_mem_B) (zpowers_le.2 D.b₁_mem_B)
  obtain ⟨α, hα, z, hz, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
    fun u hu w hw => D.A_comm_B u hu w (hZB hw))).1 hx
  have hb₀b₁ : D.b₀ * D.b₁ = D.b₁ * D.b₀ := D.B₀_comm_B₁ _ D.b₀_mem _ D.b₁_mem
  have hz2 : z * z = 1 := mul_self_of_mem_zpowers_sup_zpowers D.b₀_mul_b₀ D.b₁_mul_b₁ hb₀b₁ hz
  have hαz : α * z = z * α := D.A_comm_B α hα z (hZB hz)
  have hα2 : α * α = 1 := by
    have : α * α * (z * z) = α * z * (α * z) := by
      calc α * α * (z * z) = α * (α * z) * z := by group
        _ = α * (z * α) * z := by rw [hαz]
        _ = α * z * (α * z) := by group
    rwa [hz2, mul_one, hx2] at this
  obtain ⟨eA⟩ := D.A_iso
  obtain ⟨U', hU'A, hU'2, hU'4, hαU'⟩ :=
    exists_four_of_mulEquiv_dihedral (by have := D.two_le_m; omega) eA hα hα2
  refine ⟨U', ⟨hU'A, hU'2, hU'4⟩, fun E hU'E hb₀ hb₁ => mul_mem (hU'E hαU') ?_⟩
  exact (sup_le (zpowers_le.2 hb₀) (zpowers_le.2 hb₁)) hz

theorem exists_symm_E64_of_mem {x : G} (hx : x ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁))
    (hx2 : x * x = 1) : ∃ E : Subgroup G, IsE64 T E ∧ (D.typ E).1 = (D.typ E).2 ∧ x ∈ E := by
  obtain ⟨U', hU', hmem⟩ := D.exists_four_of_mem_A_sup hx hx2
  have hW := D.isFourIn_repW 0
  have hE := D.isE64_of_four hU' hW (D.isFourIn_sConj₀ hW)
  refine ⟨_, hE, by rw [D.typ_four_sConj hU' hW], hmem _ le_sup_left (D.b₀_mem_E64 hE)
    (D.b₁_mem_E64 hE)⟩

end FooteCore

end CFSG.CGT.Foote81L6
