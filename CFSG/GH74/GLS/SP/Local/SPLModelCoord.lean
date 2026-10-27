module

public import CFSG.GH74.GLS.SP.Model
public import CFSG.GH74.GLS.SP.Local.SPLCoordDef
public import CFSG.GH74.GLS.SP.Local.SPLModelCoordMat

public section

namespace CFSG.GH74.GLS.SP.Local

open CFSG.GH74.GLS.SP CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Assembly.LowTwoRank CFSG.GH74.BNPair TauCeti.GLSymplecticFin
open scoped Pointwise

namespace ModelCoord

section Membership

variable {F : Type} [Field F]

theorem two_ne_zero_of_odd_card [Finite F] (hodd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  intro h2
  have hfin : Fintype F := Fintype.ofFinite F
  have hchar : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  have h := FiniteField.even_card_iff_char_two.mp (ringChar.eq F 2)
  rw [← Nat.card_eq_fintype_card] at h
  exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_iff.mpr h)

theorem stdVec_octRoot_one : stdVec (RootSubgroupIndex.difference (0 : Fin 2) 1 (by decide)) =
    toStd 2 (octRoot 1) := by
  funext k
  fin_cases k <;> simp [stdVec, toStd, octRoot]

theorem stdVec_octRoot_two : stdVec (RootSubgroupIndex.positiveLong (0 : Fin 2)) =
    toStd 2 (octRoot 2) := by
  funext k
  fin_cases k <;> simp [stdVec, toStd, octRoot]

theorem stdVec_octRoot_three : stdVec (RootSubgroupIndex.positiveSum (0 : Fin 2) 1 (by decide)) =
    toStd 2 (octRoot 3) := by
  funext k
  fin_cases k <;> simp [stdVec, toStd, octRoot]

theorem stdVec_octRoot_four : stdVec (RootSubgroupIndex.positiveLong (1 : Fin 2)) =
    toStd 2 (octRoot 4) := by
  funext k
  fin_cases k <;> simp [stdVec, toStd, octRoot]

theorem mem_octGroup_four_iff (x : StatedSp 2 F) : x ∈ octGroup F 4 ↔ ∃ s, z₁ s = x := by
  refine (mem_rootGroup_iff (F := F) stdVec_octRoot_four).trans ?_
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨-c, by simp [z₁]⟩
  · rintro ⟨s, rfl⟩
    exact ⟨-s, rfl⟩

theorem mem_octGroup_two_iff (h2 : (2 : F) ≠ 0) (x : StatedSp 2 F) :
    x ∈ octGroup F 2 ↔ ∃ c, z₂ c = x := by
  refine (mem_rootGroup_iff (F := F) stdVec_octRoot_two).trans ?_
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨-(c / 2), ?_⟩
    rw [z₂]
    congr 1
    field_simp
  · rintro ⟨c, rfl⟩
    exact ⟨-2 * c, rfl⟩

theorem mem_octGroup_three_iff (x : StatedSp 2 F) : x ∈ octGroup F 3 ↔ ∃ a, z₃ a = x := by
  refine (mem_rootGroup_iff (F := F) stdVec_octRoot_three).trans ?_
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

theorem mem_octGroup_one_iff (x : StatedSp 2 F) : x ∈ octGroup F 1 ↔ ∃ b, z₄ b = x := by
  refine (mem_rootGroup_iff (F := F) stdVec_octRoot_one).trans ?_
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, rfl⟩

theorem z₁_mem_octGroup (s : F) : z₁ s ∈ octGroup F 4 := (mem_octGroup_four_iff _).2 ⟨s, rfl⟩

theorem z₂_mem_octGroup (c : F) : z₂ c ∈ octGroup F 2 :=
  (mem_rootGroup_iff (F := F) stdVec_octRoot_two).2 ⟨-2 * c, rfl⟩

theorem z₃_mem_octGroup (a : F) : z₃ a ∈ octGroup F 3 := (mem_octGroup_three_iff _).2 ⟨a, rfl⟩

theorem z₄_mem_octGroup (b : F) : z₄ b ∈ octGroup F 1 := (mem_octGroup_one_iff _).2 ⟨b, rfl⟩

theorem z₁_mem_spU (s : F) : z₁ s ∈ spU F :=
  octGroup_le_spU F (by norm_num) (by norm_num) (z₁_mem_octGroup s)

theorem z₂_mem_spU (c : F) : z₂ c ∈ spU F :=
  octGroup_le_spU F (by norm_num) (by norm_num) (z₂_mem_octGroup c)

theorem z₃_mem_spU (a : F) : z₃ a ∈ spU F :=
  octGroup_le_spU F (by norm_num) (by norm_num) (z₃_mem_octGroup a)

theorem z₄_mem_spU (b : F) : z₄ b ∈ spU F :=
  octGroup_le_spU F (by norm_num) (by norm_num) (z₄_mem_octGroup b)

theorem exists_z_of_mem_spU (h2 : (2 : F) ≠ 0) {g : StatedSp 2 F} (hg : g ∈ spU F) :
    ∃ s c a b : F, g = z₁ s * z₂ c * z₃ a * z₄ b := by
  have h := (spOctagon F).carrier_eq
  have hr := (spOctagon F).reverse_eq 1 ((4 : ℕ) : ℤ) le_rfl (by norm_num) le_rfl
  have hmem : g ∈ chainProd (octGroup F) (intList 1 ((4 : ℕ) : ℤ)) := by
    rw [← h]
    exact hg
  rw [hr] at hmem
  have hl : (intList 1 ((4 : ℕ) : ℤ)).reverse = [4, 3, 2, 1] := by decide
  rw [hl] at hmem
  simp only [chainProd, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hmem
  obtain ⟨y4, hy4, y321, hy321, rfl⟩ := Set.mem_mul.1 hmem
  obtain ⟨y3, hy3, y21, hy21, rfl⟩ := Set.mem_mul.1 hy321
  obtain ⟨y2, hy2, y1, hy1, rfl⟩ := Set.mem_mul.1 hy21
  obtain ⟨s, rfl⟩ := (mem_octGroup_four_iff _).1 hy4
  obtain ⟨a, rfl⟩ := (mem_octGroup_three_iff _).1 hy3
  obtain ⟨c, rfl⟩ := (mem_octGroup_two_iff h2 _).1 hy2
  obtain ⟨b, rfl⟩ := (mem_octGroup_one_iff _).1 hy1
  refine ⟨s, c, a, b, ?_⟩
  calc z₁ s * (z₃ a * (z₂ c * z₄ b)) = z₁ s * (z₃ a * z₂ c) * z₄ b := by simp only [mul_assoc]
    _ = z₁ s * (z₂ c * z₃ a) * z₄ b := by rw [z₂_comm_z₃]
    _ = z₁ s * z₂ c * z₃ a * z₄ b := by simp only [mul_assoc]

theorem z₂_comm_of_mem_spU (h2 : (2 : F) ≠ 0) (c : F) {g : StatedSp 2 F} (hg : g ∈ spU F) :
    z₂ c * g = g * z₂ c := by
  obtain ⟨s, c', a, b, rfl⟩ := exists_z_of_mem_spU h2 hg
  have h22 : Commute (z₂ c) (z₂ c') := by
    unfold Commute SemiconjBy
    rw [← z₂_add, ← z₂_add, add_comm]
  have h1 : Commute (z₂ c) (z₁ s) := z₂_comm_z₁ c s
  have h3 : Commute (z₂ c) (z₃ a) := z₂_comm_z₃ c a
  have h4 : Commute (z₂ c) (z₄ b) := z₂_comm_z₄ c b
  exact (((h1.mul_right h22).mul_right h3).mul_right h4).eq

end Membership

section Coordinates

variable {F : Type} [Field F]

@[expose] noncomputable def u₁ (s : F) : ↥(spU F) := ⟨z₁ s, z₁_mem_spU s⟩

@[expose] noncomputable def u₂ (c : F) : ↥(spU F) := ⟨z₂ c, z₂_mem_spU c⟩

@[expose] noncomputable def u₃ (a : F) : ↥(spU F) := ⟨z₃ a, z₃_mem_spU a⟩

@[expose] noncomputable def u₄ (b : F) : ↥(spU F) := ⟨z₄ b, z₄_mem_spU b⟩

theorem splCoord_u (h2 : (2 : F) ≠ 0) : SPLCoord (u₁ (F := F)) u₂ u₃ u₄ where
  add₁ s s' := Subtype.ext (z₁_add s s')
  add₂ c c' := Subtype.ext (z₂_add c c')
  add₃ a a' := Subtype.ext (z₃_add a a')
  add₄ b b' := Subtype.ext (z₄_add b b')
  surj := by
    rintro ⟨g, hg⟩
    obtain ⟨s, c, a, b, rfl⟩ := exists_z_of_mem_spU h2 hg
    exact ⟨s, c, a, b, rfl⟩
  inj s c a b s' c' a' b' h := normalForm_inj h2 (congrArg Subtype.val h)
  cen₂ c := by
    rintro ⟨g, hg⟩
    exact Subtype.ext (z₂_comm_of_mem_spU h2 c hg)
  c13 s a := Subtype.ext (z₁_comm_z₃ s a)
  c34 a b := Subtype.ext (z₃_mul_z₄ a b)
  c14 s b := Subtype.ext (z₁_mul_z₄ h2 s b)

theorem mem_octGroup_four_iff_u (g : ↥(spU F)) :
    (g : StatedSp 2 F) ∈ octGroup F 4 ↔ ∃ s, u₁ s = g := by
  rw [mem_octGroup_four_iff]
  exact ⟨fun ⟨s, hs⟩ => ⟨s, Subtype.ext hs⟩, fun ⟨s, hs⟩ => ⟨s, congrArg Subtype.val hs⟩⟩

theorem mem_octGroup_two_iff_u (h2 : (2 : F) ≠ 0) (g : ↥(spU F)) :
    (g : StatedSp 2 F) ∈ octGroup F 2 ↔ ∃ c, u₂ c = g := by
  rw [mem_octGroup_two_iff h2]
  exact ⟨fun ⟨s, hs⟩ => ⟨s, Subtype.ext hs⟩, fun ⟨s, hs⟩ => ⟨s, congrArg Subtype.val hs⟩⟩

theorem mem_octGroup_three_iff_u (g : ↥(spU F)) :
    (g : StatedSp 2 F) ∈ octGroup F 3 ↔ ∃ a, u₃ a = g := by
  rw [mem_octGroup_three_iff]
  exact ⟨fun ⟨s, hs⟩ => ⟨s, Subtype.ext hs⟩, fun ⟨s, hs⟩ => ⟨s, congrArg Subtype.val hs⟩⟩

theorem mem_octGroup_one_iff_u (g : ↥(spU F)) :
    (g : StatedSp 2 F) ∈ octGroup F 1 ↔ ∃ b, u₄ b = g := by
  rw [mem_octGroup_one_iff]
  exact ⟨fun ⟨s, hs⟩ => ⟨s, Subtype.ext hs⟩, fun ⟨s, hs⟩ => ⟨s, congrArg Subtype.val hs⟩⟩

end Coordinates

section Transport

theorem splCoord_map {F : Type*} [Field F] {P P' : Type*} [Group P] [Group P'] {x₁ x₂ x₃ x₄ : F → P}
    (h : SPLCoord x₁ x₂ x₃ x₄) (φ : P ≃* P') :
    SPLCoord (fun s => φ (x₁ s)) (fun s => φ (x₂ s)) (fun s => φ (x₃ s)) (fun s => φ (x₄ s)) where
  add₁ s s' := by rw [h.add₁, map_mul]
  add₂ c c' := by rw [h.add₂, map_mul]
  add₃ a a' := by rw [h.add₃, map_mul]
  add₄ b b' := by rw [h.add₄, map_mul]
  surj g := by
    obtain ⟨s, c, a, b, hg⟩ := h.surj (φ.symm g)
    refine ⟨s, c, a, b, ?_⟩
    have := congrArg φ hg
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  inj s c a b s' c' a' b' hh := by
    have : φ (x₁ s * x₂ c * x₃ a * x₄ b) = φ (x₁ s' * x₂ c' * x₃ a' * x₄ b') := by
      simpa only [map_mul] using hh
    exact h.inj s c a b s' c' a' b' (φ.injective this)
  cen₂ c g := by
    have := congrArg φ (h.cen₂ c (φ.symm g))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  c13 s a := by
    have := congrArg φ (h.c13 s a)
    simpa only [map_mul] using this
  c34 a b := by
    have := congrArg φ (h.c34 a b)
    simpa only [map_mul] using this
  c14 s b := by
    have := congrArg φ (h.c14 s b)
    simpa only [map_mul] using this

end Transport

section Model

variable (F : Type) [Field F]

theorem subgroupMap_spProj_injective : Function.Injective ((spProj F).subgroupMap (spU F)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : spProj F (x : StatedSp 2 F) = 1 := congrArg Subtype.val hx
  have hmem : (x : StatedSp 2 F) ∈ spU F ⊓ (spProj F).ker :=
    Subgroup.mem_inf.2 ⟨x.2, (MonoidHom.mem_ker).2 hx'⟩
  rw [spU_inf_ker, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

@[expose] noncomputable def projU (hF : 4 ≤ Nat.card F) : ↥(spU F) ≃* ↥(modelSystem F hF).U :=
  (MulEquiv.ofBijective ((spProj F).subgroupMap (spU F))
    ⟨subgroupMap_spProj_injective F, MonoidHom.subgroupMap_surjective _ _⟩).trans
    (MulEquiv.subgroupCongr (modelSystem_U F hF).symm)

theorem projU_coe (hF : 4 ≤ Nat.card F) (u : ↥(spU F)) :
    ((projU F hF u : ↥(modelSystem F hF).U) : StatedProj (StatedSp 2 F)) =
      spProj F (u : StatedSp 2 F) := rfl

theorem projU_mem_map_iff (hF : 4 ≤ Nat.card F) {H : Subgroup (StatedSp 2 F)} (hH : H ≤ spU F)
    (u : ↥(spU F)) :
    ((projU F hF u : ↥(modelSystem F hF).U) : StatedProj (StatedSp 2 F)) ∈ H.map (spProj F) ↔
      (u : StatedSp 2 F) ∈ H := by
  rw [projU_coe]
  constructor
  · rintro ⟨h, hh, hhu⟩
    have hmem : h⁻¹ * (u : StatedSp 2 F) ∈ spU F ⊓ (spProj F).ker := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hH hh)) u.2, ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hhu, inv_mul_cancel]
    rw [spU_inf_ker, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    rwa [← hmem]
  · intro hu
    exact ⟨u, hu, rfl⟩

end Model

end ModelCoord

theorem model_coords (F : Type) [Field F] [Finite F] (hF : 4 ≤ Nat.card F)
    (hodd : Odd (Nat.card F)) :
    ∃ y₁ y₂ y₃ y₄ : F → ↥(SP.modelSystem F hF).U, SPLCoord y₁ y₂ y₃ y₄ ∧
      (∀ g : ↥(SP.modelSystem F hF).U,
        (g : StatedProj (StatedSp 2 F)) ∈ (SP.modelSystem F hF).root 4 ↔ ∃ s, y₁ s = g) ∧
      (∀ g : ↥(SP.modelSystem F hF).U,
        (g : StatedProj (StatedSp 2 F)) ∈ (SP.modelSystem F hF).root 2 ↔ ∃ s, y₂ s = g) ∧
      (∀ g : ↥(SP.modelSystem F hF).U,
        (g : StatedProj (StatedSp 2 F)) ∈ (SP.modelSystem F hF).root 3 ↔ ∃ s, y₃ s = g) ∧
      (∀ g : ↥(SP.modelSystem F hF).U,
        (g : StatedProj (StatedSp 2 F)) ∈ (SP.modelSystem F hF).root 1 ↔ ∃ s, y₄ s = g) := by
  have h2 := ModelCoord.two_ne_zero_of_odd_card (F := F) hodd
  have key : ∀ {i : ℤ} (hi₁ : 1 ≤ i) (hi₄ : i ≤ 4) {w : F → ↥(spU F)}
      (hw : ∀ u : ↥(spU F), (u : StatedSp 2 F) ∈ octGroup F i ↔ ∃ s, w s = u)
      (g : ↥(SP.modelSystem F hF).U),
      (g : StatedProj (StatedSp 2 F)) ∈ (SP.modelSystem F hF).root i ↔
        ∃ s, ModelCoord.projU F hF (w s) = g := by
    intro i hi₁ hi₄ w hw g
    obtain ⟨u, rfl⟩ := (ModelCoord.projU F hF).surjective g
    rw [modelSystem_root, ModelCoord.projU_mem_map_iff F hF (octGroup_le_spU F hi₁ hi₄), hw u]
    simp only [EmbeddingLike.apply_eq_iff_eq]
  exact ⟨fun s => ModelCoord.projU F hF (ModelCoord.u₁ s),
    fun c => ModelCoord.projU F hF (ModelCoord.u₂ c),
    fun a => ModelCoord.projU F hF (ModelCoord.u₃ a),
    fun b => ModelCoord.projU F hF (ModelCoord.u₄ b),
    ModelCoord.splCoord_map (ModelCoord.splCoord_u h2) (ModelCoord.projU F hF),
    key (by norm_num) (by norm_num) (ModelCoord.mem_octGroup_four_iff_u),
    key (by norm_num) (by norm_num) (ModelCoord.mem_octGroup_two_iff_u h2),
    key (by norm_num) (by norm_num) (ModelCoord.mem_octGroup_three_iff_u),
    key (by norm_num) (by norm_num) (ModelCoord.mem_octGroup_one_iff_u)⟩

end CFSG.GH74.GLS.SP.Local
