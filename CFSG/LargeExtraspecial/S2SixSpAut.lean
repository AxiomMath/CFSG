module

public import CFSG.LargeExtraspecial.S2SpB1
public import CFSG.LargeExtraspecial.S2SpC

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]

structure SpAutOn (F : Submodule (ZMod 2) V) (α : SpG f → SpG f) : Prop where
  mem : ∀ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → (α g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F
  map_mul : ∀ g h : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
    (h : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → α (g * h) = α g * α h
  inj : ∀ g h : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
    (h : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → α g = α h → g = h
  surj : ∀ h : SpG f, (h : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
    ∃ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F ∧ α g = h

@[expose] def SpMapsRad (F : Submodule (ZMod 2) V) (α : SpG f → SpG f) (a b : V) : Prop :=
  ∀ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
    ((g : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F a ↔ (α g : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F b)

omit [FiniteDimensional (ZMod 2) V] in
theorem sp_coe_mul_mem_fixGroup {F : Submodule (ZMod 2) V} {g h : SpG f}
    (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) (hh : (h : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    ((g * h : SpG f) : V ≃ₗ[ZMod 2] V) ∈ fixGroup F :=
  mul_mem hg hh

omit [FiniteDimensional (ZMod 2) V] in
theorem sp_coe_inv_mem_fixGroup {F : Submodule (ZMod 2) V} {g : SpG f}
    (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) : ((g⁻¹ : SpG f) : V ≃ₗ[ZMod 2] V) ∈ fixGroup F :=
  inv_mem hg

namespace SpAutOn

variable {F : Submodule (ZMod 2) V} {α : SpG f → SpG f}

omit [FiniteDimensional (ZMod 2) V] in
theorem map_one (hα : SpAutOn F α) : α 1 = 1 := by
  have h := hα.map_mul 1 1 (one_mem (fixGroup F)) (one_mem (fixGroup F))
  rw [mul_one] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

omit [FiniteDimensional (ZMod 2) V] in
theorem map_inv (hα : SpAutOn F α) {g : SpG f} (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    α g⁻¹ = (α g)⁻¹ := by
  have h := hα.map_mul g g⁻¹ hg (sp_coe_inv_mem_fixGroup hg)
  rw [mul_inv_cancel, hα.map_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

omit [FiniteDimensional (ZMod 2) V] in
theorem map_conj (hα : SpAutOn F α) {g t : SpG f} (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F)
    (ht : (t : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) : α (g⁻¹ * t * g) = (α g)⁻¹ * α t * α g := by
  rw [hα.map_mul _ _ (sp_coe_mul_mem_fixGroup (sp_coe_inv_mem_fixGroup hg) ht) hg,
    hα.map_mul _ _ (sp_coe_inv_mem_fixGroup hg) ht, hα.map_inv hg]

omit [FiniteDimensional (ZMod 2) V] in
theorem conj (hα : SpAutOn F α) {x : SpG f} (hx : (x : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    SpAutOn F (fun g => x * α g * x⁻¹) where
  mem g hg := sp_coe_mul_mem_fixGroup (sp_coe_mul_mem_fixGroup hx (hα.mem g hg))
    (sp_coe_inv_mem_fixGroup hx)
  map_mul g h hg hh := by
    rw [hα.map_mul g h hg hh]
    group
  inj g h hg hh e := hα.inj g h hg hh (by simpa using e)
  surj h hh := by
    obtain ⟨g, hg, hgh⟩ := hα.surj (x⁻¹ * h * x)
      (sp_coe_mul_mem_fixGroup (sp_coe_mul_mem_fixGroup (sp_coe_inv_mem_fixGroup hx) hh) hx)
    exact ⟨g, hg, by rw [hgh]; group⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem restrict (hα : SpAutOn F α) {K : Submodule (ZMod 2) V} (hKF : fixGroup K ≤ fixGroup F)
    (hK : ∀ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      ((g : V ≃ₗ[ZMod 2] V) ∈ fixGroup K ↔ (α g : V ≃ₗ[ZMod 2] V) ∈ fixGroup K)) :
    SpAutOn K α where
  mem g hg := (hK g (hKF hg)).mp hg
  map_mul g h hg hh := hα.map_mul g h (hKF hg) (hKF hh)
  inj g h hg hh := hα.inj g h (hKF hg) (hKF hh)
  surj h hh := by
    obtain ⟨g, hg, rfl⟩ := hα.surj h (hKF hh)
    exact ⟨g, (hK g hg).mpr hh, rfl⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem inner_of_conj {x y : SpG f}
    (h : ∀ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → x * α g * x⁻¹ = y * g * y⁻¹)
    (g : SpG f) (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    α g = (x⁻¹ * y) * g * (x⁻¹ * y)⁻¹ := by
  calc α g = x⁻¹ * (x * α g * x⁻¹) * x := by group
    _ = (x⁻¹ * y) * g * (x⁻¹ * y)⁻¹ := by rw [h g hg]; group

end SpAutOn

omit [FiniteDimensional (ZMod 2) V] in
theorem SpMapsRad.conj (hf : f.IsAlt) (hnd : f.Nondegenerate) {F : Submodule (ZMod 2) V}
    {α : SpG f → SpG f} {a b : V} (h : SpMapsRad F α a b) {x : SpG f}
    (hx : (x : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) (hb0 : b ≠ 0) (hbF : b ∈ spPerp f F) :
    SpMapsRad F (fun g => x * α g * x⁻¹) a ((x : V ≃ₗ[ZMod 2] V) b) := by
  intro g hg
  rw [h g hg, map_conj_spRadFix hf hnd hb0 hbF x.2 hx]
  change _ ↔ (x : V ≃ₗ[ZMod 2] V)⁻¹ * ((x : V ≃ₗ[ZMod 2] V) * (α g : V ≃ₗ[ZMod 2] V) *
    (x : V ≃ₗ[ZMod 2] V)⁻¹) * (x : V ≃ₗ[ZMod 2] V) ∈ _
  rw [show (x : V ≃ₗ[ZMod 2] V)⁻¹ * ((x : V ≃ₗ[ZMod 2] V) * (α g : V ≃ₗ[ZMod 2] V) *
    (x : V ≃ₗ[ZMod 2] V)⁻¹) * (x : V ≃ₗ[ZMod 2] V) = (α g : V ≃ₗ[ZMod 2] V) by group]

theorem sp_eq_of_forall_mem_spRadFix_iff (hf : f.IsAlt) (hnd : f.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ spPerp f F = ⊥) {a b : V} (haF : a ∈ spPerp f F)
    (hbF : b ∈ spPerp f F) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (h : ∀ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      ((g : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F a ↔ (g : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F b)) :
    a = b := by
  refine sp_eq_of_spRadFix_eq hf hnd hF haF hbF ha0 hb0 ?_
  ext t
  constructor
  · intro ht
    have htS := spRadFix_le_spFix F a ht
    exact (h ⟨t, htS.1⟩ htS.2).mp ht
  · intro ht
    have htS := spRadFix_le_spFix F b ht
    exact (h ⟨t, htS.1⟩ htS.2).mpr ht

namespace SpAutOn

variable {F : Submodule (ZMod 2) V} {α : SpG f → SpG f}

omit [FiniteDimensional (ZMod 2) V] in
theorem mapsRad_apply (hα : SpAutOn F α) (hf : f.IsAlt) (hnd : f.Nondegenerate) {a : V}
    (ha0 : a ≠ 0) (haF : a ∈ spPerp f F) (hαa : SpMapsRad F α a a) {g : SpG f}
    (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    SpMapsRad F α ((g : V ≃ₗ[ZMod 2] V) a) ((α g : V ≃ₗ[ZMod 2] V) a) := by
  intro t ht
  rw [map_conj_spRadFix hf hnd ha0 haF g.2 hg, map_conj_spRadFix hf hnd ha0 haF (α g).2
    (hα.mem g hg)]
  have h := hαa (g⁻¹ * t * g) (sp_coe_mul_mem_fixGroup (sp_coe_mul_mem_fixGroup
    (sp_coe_inv_mem_fixGroup hg) ht) hg)
  rw [hα.map_conj hg ht] at h
  exact h

theorem eq_of_mapsRad (hf : f.IsAlt) (hnd : f.Nondegenerate) (hF : F ⊓ spPerp f F = ⊥)
    {a a' b : V} (haF : a ∈ spPerp f F) (ha'F : a' ∈ spPerp f F) (ha0 : a ≠ 0) (ha'0 : a' ≠ 0)
    (h : SpMapsRad F α a b) (h' : SpMapsRad F α a' b) : a = a' :=
  sp_eq_of_forall_mem_spRadFix_iff hf hnd hF haF ha'F ha0 ha'0 fun g hg =>
    (h g hg).trans (h' g hg).symm

theorem eq_of_mapsRad' (hα : SpAutOn F α) (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hF : F ⊓ spPerp f F = ⊥) {a b b' : V} (hbF : b ∈ spPerp f F) (hb'F : b' ∈ spPerp f F)
    (hb0 : b ≠ 0) (hb'0 : b' ≠ 0) (h : SpMapsRad F α a b) (h' : SpMapsRad F α a b') :
    b = b' := by
  refine sp_eq_of_forall_mem_spRadFix_iff hf hnd hF hbF hb'F hb0 hb'0 fun s hs => ?_
  obtain ⟨t, ht, rfl⟩ := hα.surj s hs
  exact (h t ht).symm.trans (h' t ht)

omit [FiniteDimensional (ZMod 2) V] in
theorem mapsRad_inf_eq_bot_iff (hα : SpAutOn F α) {a b a' b' : V} (h1 : SpMapsRad F α a a')
    (h2 : SpMapsRad F α b b') :
    spRadFix f F a ⊓ spRadFix f F b = ⊥ ↔ spRadFix f F a' ⊓ spRadFix f F b' = ⊥ := by
  constructor
  · intro h
    rw [eq_bot_iff]
    rintro s ⟨hs, hs'⟩
    have hsS := spRadFix_le_spFix F a' hs
    obtain ⟨t, ht, hts⟩ := hα.surj ⟨s, hsS.1⟩ hsS.2
    have hta : (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F a := (h1 t ht).mpr (by rw [hts]; exact hs)
    have htb : (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F b := (h2 t ht).mpr (by rw [hts]; exact hs')
    have ht1 : t = 1 := Subtype.ext (by
      have := (show (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F a ⊓ spRadFix f F b from ⟨hta, htb⟩)
      rw [h, Subgroup.mem_bot] at this
      exact this)
    rw [ht1, hα.map_one] at hts
    rw [Subgroup.mem_bot]
    exact (congrArg Subtype.val hts).symm
  · intro h
    rw [eq_bot_iff]
    rintro t ⟨ht, ht'⟩
    have htS := spRadFix_le_spFix F a ht
    have hs := (show ((α ⟨t, htS.1⟩ : SpG f) : V ≃ₗ[ZMod 2] V) ∈
      spRadFix f F a' ⊓ spRadFix f F b' from ⟨(h1 _ htS.2).mp ht, (h2 _ htS.2).mp ht'⟩)
    rw [h, Subgroup.mem_bot] at hs
    have : α ⟨t, htS.1⟩ = α 1 := by rw [hα.map_one]; exact Subtype.ext hs
    have := hα.inj _ _ htS.2 (one_mem _) this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this

theorem mapsRad_polar_eq_one (hα : SpAutOn F α) (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hF : F ⊓ spPerp f F = ⊥) {a b a' b' : V} (haF : a ∈ spPerp f F) (hbF : b ∈ spPerp f F)
    (ha'F : a' ∈ spPerp f F) (hb'F : b' ∈ spPerp f F) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha'0 : a' ≠ 0) (hb'0 : b' ≠ 0) (hab : f a b = 1) (h1 : SpMapsRad F α a a')
    (h2 : SpMapsRad F α b b') : f a' b' = 1 := by
  have hne : a ≠ b := by
    rintro rfl
    rw [hf.self_eq_zero] at hab
    exact zero_ne_one hab
  have hne' : a' ≠ b' := by
    rintro rfl
    exact hne (eq_of_mapsRad hf hnd hF haF hbF ha0 hb0 h1 h2)
  refine (spRadFix_inf_eq_bot_iff hf hnd ha'F hb'F ha'0 hb'0 hne').mp ?_
  exact (hα.mapsRad_inf_eq_bot_iff h1 h2).mp
    ((spRadFix_inf_eq_bot_iff hf hnd haF hbF ha0 hb0 hne).mpr hab)

theorem mapsRad_polar_eq_zero (hα : SpAutOn F α) (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hF : F ⊓ spPerp f F = ⊥) {a b a' b' : V} (haF : a ∈ spPerp f F) (hbF : b ∈ spPerp f F)
    (ha'F : a' ∈ spPerp f F) (hb'F : b' ∈ spPerp f F) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha'0 : a' ≠ 0) (hb'0 : b' ≠ 0) (hne : a ≠ b) (hab : f a b = 0)
    (h1 : SpMapsRad F α a a') (h2 : SpMapsRad F α b b') : a' ≠ b' ∧ f a' b' = 0 := by
  have hne' : a' ≠ b' := by
    rintro rfl
    exact hne (eq_of_mapsRad hf hnd hF haF hbF ha0 hb0 h1 h2)
  refine ⟨hne', (zmod2_eq_zero_or_eq_one _).resolve_right fun h => ?_⟩
  have := (hα.mapsRad_inf_eq_bot_iff h1 h2).mpr
    ((spRadFix_inf_eq_bot_iff hf hnd ha'F hb'F ha'0 hb'0 hne').mpr h)
  rw [spRadFix_inf_eq_bot_iff hf hnd haF hbF ha0 hb0 hne, hab] at this
  exact zero_ne_one this

theorem exists_mapsRad_conj (hα : SpAutOn F α) (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hF : F ⊓ spPerp f F = ⊥) {p p₁ : V} (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F)
    (hpp₁ : f p p₁ = 1) (hαp : SpMapsRad F α p p) :
    ∃ E : SpG f, (E : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p ∧
      SpMapsRad F (fun g => E * α g * E⁻¹) p p ∧
      SpMapsRad F (fun g => E * α g * E⁻¹) p₁ p₁ := by
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  obtain ⟨g, hg, hgp⟩ := exists_mem_spRadGen_apply_eq hf hnd hF hpF hp₁F hp0 hp₁0
  have hgS := spRadGen_le_spFix F hg
  set g' : SpG f := ⟨g, hgS.1⟩
  have hg'F : (g' : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hgS.2
  have h1 := hα.mapsRad_apply hf hnd hp0 hpF hαp hg'F
  change SpMapsRad F α (g p) _ at h1
  rw [hgp] at h1
  set b := (α g' : V ≃ₗ[ZMod 2] V) p with hb
  have hbF : b ∈ spPerp f F := apply_mem_spPerp (α g').2 (hα.mem g' hg'F) hpF
  have hb0 : b ≠ 0 := fun h => hp0 ((α g' : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h)
  have hpb : f p b = 1 := hα.mapsRad_polar_eq_one hf hnd hF hpF hp₁F hpF hbF hp0 hp₁0 hp0 hb0
    hpp₁ hαp h1
  obtain ⟨E, hE, hEb⟩ := exists_mem_spRadFix_apply_eq hf hpF hbF hp₁F hpb hpp₁
  have hES := spRadFix_le_spFix F p hE
  refine ⟨⟨E, hES.1⟩, hE, ?_, ?_⟩
  · have := hαp.conj hf hnd (x := ⟨E, hES.1⟩) hES.2 hp0 hpF
    rwa [show E p = p from hE.1.2.1] at this
  · have := h1.conj hf hnd (x := ⟨E, hES.1⟩) hES.2 hb0 hbF
    rwa [show E b = p₁ from hEb] at this

theorem eq_self_of_forall_radFix (hα : SpAutOn F α) (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hF : F ⊓ spPerp f F = ⊥) {m : ℕ} (hdim : finrank (ZMod 2) (spPerp f F) = 2 * m)
    {p p₁ : V} (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F) (hpp₁ : f p p₁ = 1)
    (h : ∀ t : SpG f, (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p → α t = t)
    (h₁ : ∀ t : SpG f, (t : V ≃ₗ[ZMod 2] V) ∈ spRadFix f F p₁ → α t = t)
    (g : SpG f) (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) : α g = g := by
  have hcl := spFix_eq_closure_spRadFix hf hnd hF hdim hpF hp₁F hpp₁
  have hle : Subgroup.closure ((spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) ∪ spRadFix f F p₁) ≤
      spFix f F := hcl.symm.le
  have key : ∀ x ∈ Subgroup.closure ((spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) ∪
      spRadFix f F p₁), ∀ hx : x ∈ SpG f, α ⟨x, hx⟩ = ⟨x, hx⟩ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      intro hxS
      rcases hx with hx | hx
      · exact h ⟨x, hxS⟩ hx
      · exact h₁ ⟨x, hxS⟩ hx
    | one =>
      intro _
      exact hα.map_one
    | mul x y hx' hy' ihx ihy =>
      intro _
      have hxS := hle hx'
      have hyS := hle hy'
      have e : (⟨x * y, mul_mem hxS.1 hyS.1⟩ : SpG f) = ⟨x, hxS.1⟩ * ⟨y, hyS.1⟩ := rfl
      rw [e, hα.map_mul _ _ hxS.2 hyS.2, ihx hxS.1, ihy hyS.1]
    | inv x hx' ihx =>
      intro _
      have hxS := hle hx'
      have e : (⟨x⁻¹, inv_mem hxS.1⟩ : SpG f) = (⟨x, hxS.1⟩)⁻¹ := rfl
      rw [e, hα.map_inv hxS.2, ihx hxS.1]
  have hmem : (g : V ≃ₗ[ZMod 2] V) ∈
      Subgroup.closure ((spRadFix f F p : Set (V ≃ₗ[ZMod 2] V)) ∪ spRadFix f F p₁) := by
    rw [← hcl]
    exact ⟨g.2, hg⟩
  exact key g hmem g.2

theorem apply_eq_iff (hα : SpAutOn F α) (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hF : F ⊓ spPerp f F = ⊥) {a : V} (haF : a ∈ spPerp f F) (ha0 : a ≠ 0)
    (hαa : SpMapsRad F α a a) {g : SpG f} (hg : (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F) :
    (g : V ≃ₗ[ZMod 2] V) a = a ↔ (α g : V ≃ₗ[ZMod 2] V) a = a := by
  have h := hα.mapsRad_apply hf hnd ha0 haF hαa hg
  have hgaF := apply_mem_spPerp g.2 hg haF
  have hαgaF := apply_mem_spPerp (α g).2 (hα.mem g hg) haF
  have hga0 : (g : V ≃ₗ[ZMod 2] V) a ≠ 0 := fun h0 =>
    ha0 ((g : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h0)
  have hαga0 : (α g : V ≃ₗ[ZMod 2] V) a ≠ 0 := fun h0 =>
    ha0 ((α g : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h0)
  constructor
  · intro hga'
    rw [hga'] at h
    exact (hα.eq_of_mapsRad' hf hnd hF haF hαgaF ha0 hαga0 hαa h).symm
  · intro hαga'
    rw [hαga'] at h
    exact eq_of_mapsRad hf hnd hF hgaF haF hga0 ha0 h hαa

theorem restrict_levi (hα : SpAutOn F α) (hf : f.IsAlt) (hnd : f.Nondegenerate)
    (hF : F ⊓ spPerp f F = ⊥) {p p₁ : V} (hpF : p ∈ spPerp f F) (hp₁F : p₁ ∈ spPerp f F)
    (hp0 : p ≠ 0) (hp₁0 : p₁ ≠ 0) (hαp : SpMapsRad F α p p) (hαp₁ : SpMapsRad F α p₁ p₁) :
    ∀ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      ((g : V ≃ₗ[ZMod 2] V) ∈ fixGroup (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ↔
        (α g : V ≃ₗ[ZMod 2] V) ∈ fixGroup (F ⊔ Submodule.span (ZMod 2) {p, p₁})) := by
  intro g hg
  rw [mem_fixGroup_sup_span_pair, mem_fixGroup_sup_span_pair,
    hα.apply_eq_iff hf hnd hF hpF hp0 hαp hg, hα.apply_eq_iff hf hnd hF hp₁F hp₁0 hαp₁ hg]
  exact ⟨fun h => ⟨hα.mem g hg, h.2⟩, fun h => ⟨hg, h.2⟩⟩

end SpAutOn

omit [FiniteDimensional (ZMod 2) V] in
theorem SpMapsRad.restrict {F K : Submodule (ZMod 2) V} {α : SpG f → SpG f} {a b : V}
    (h : SpMapsRad F α a b) (hKF : fixGroup K ≤ fixGroup F)
    (hK : ∀ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      ((g : V ≃ₗ[ZMod 2] V) ∈ fixGroup K ↔ (α g : V ≃ₗ[ZMod 2] V) ∈ fixGroup K)) :
    SpMapsRad K α a b := by
  intro g hg
  have hgF := hKF hg
  have hαgK := (hK g hgF).mp hg
  have e := h g hgF
  constructor
  · intro hga
    exact ⟨(e.mp ⟨hga.1, hgF⟩).1, hαgK⟩
  · intro hαgb
    exact ⟨(e.mpr ⟨hαgb.1, hKF hαgK⟩).1, hg⟩

end S2

end CFSG.LargeExtraspecial
