module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Transitive
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Hexads
public import Certificates.Certificate2195
public import Certificates.Certificate2031
public import Certificates.Certificate2035
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22HexadStabilizerInputs
public import Certificates.Certificate2030
public import Certificates.Certificate3029

public noncomputable section

namespace CFSG.ComponentClassification.WittDesign

open MulAction
open scoped Pointwise

theorem count_kernel_hexad0 : m22Count (fun g => ∀ x ∈ hexad0, g x = x) = 16 :=
  Certificates.certificate2030.1

theorem count_kernel_sq_hexad0 :
    m22Count (fun g => (∀ x ∈ hexad0, g x = x) ∧ ∀ x, g (g x) = x) = 16 :=
  Certificates.certificate2030.2.1

theorem count_kernel_fix_hexad0 : m22Count (fun g => (∀ x ∈ hexad0, g x = x) ∧ g 3 = 3) = 1 :=
  Certificates.certificate2030.2.2.1

theorem count_stabilizer_D0 :
    m22Count (fun g => (∀ x ∈ hexad0, g x ∈ hexad0) ∧ ∀ x ∈ hexadD0, g x ∈ hexadD0) = 360 :=
  Certificates.certificate2030.2.2.2.1

theorem count_stabilizer_T0 :
    m22Count (fun g => (∀ x ∈ hexad0, g x ∈ hexad0) ∧ ∀ x ∈ hexadT0, g x ∈ hexadT0) = 96 :=
  Certificates.certificate2030.2.2.2.2.1

theorem hexadD0_mem : hexadD0 ∈ hexads := mem_hexads.2 (Certificates.certificate2030.2.2.2.2.2.1)

theorem hexadT0_mem : hexadT0 ∈ hexads := mem_hexads.2 (Certificates.certificate2030.2.2.2.2.2.2.1)

theorem coe_mul_apply (g h : M22) (x : Fin 22) :
    ((g * h : M22) : Equiv.Perm (Fin 22)) x =
      (g : Equiv.Perm (Fin 22)) ((h : Equiv.Perm (Fin 22)) x) := rfl

theorem coe_inv_apply_apply (g : M22) (x : Fin 22) :
    ((g⁻¹ : M22) : Equiv.Perm (Fin 22)) ((g : Equiv.Perm (Fin 22)) x) = x := by
  rw [← coe_mul_apply, inv_mul_cancel]
  rfl

theorem coe_apply_inv_apply (g : M22) (x : Fin 22) :
    (g : Equiv.Perm (Fin 22)) (((g⁻¹ : M22) : Equiv.Perm (Fin 22)) x) = x := by
  rw [← coe_mul_apply, mul_inv_cancel]
  rfl

theorem mem_smul_finset_iff (g : M22) (B : Finset (Fin 22)) (x : Fin 22) :
    x ∈ g • B ↔ ((g⁻¹ : M22) : Equiv.Perm (Fin 22)) x ∈ B := by
  rw [← Finset.inv_smul_mem_iff, Subgroup.smul_def]
  rfl

theorem apply_mem_smul_finset_iff (g : M22) (B : Finset (Fin 22)) (x : Fin 22) :
    (g : Equiv.Perm (Fin 22)) x ∈ g • B ↔ x ∈ B := by
  rw [mem_smul_finset_iff, coe_inv_apply_apply]

theorem card_subtype_conj (h : M22) {P Q : M22 → Prop} (hPQ : ∀ g, P g ↔ Q (h⁻¹ * g * h)) :
    Nat.card {g // P g} = Nat.card {g // Q g} := by
  refine Nat.card_congr ((MulAut.conj h⁻¹).toEquiv.subtypeEquiv fun g => ?_)
  rw [hPQ]
  simp

theorem fixes_smul_iff (h g : M22) (B : Finset (Fin 22)) :
    (∀ x ∈ h • B, (g : Equiv.Perm (Fin 22)) x = x) ↔
      ∀ x ∈ B, ((h⁻¹ * g * h : M22) : Equiv.Perm (Fin 22)) x = x := by
  constructor
  · intro H x hx
    rw [coe_mul_apply, coe_mul_apply, H _ ((apply_mem_smul_finset_iff h B x).2 hx),
      coe_inv_apply_apply]
  · intro H x hx
    have := H _ ((mem_smul_finset_iff h B x).1 hx)
    rw [coe_mul_apply, coe_mul_apply, coe_apply_inv_apply] at this
    rw [← coe_apply_inv_apply h ((g : Equiv.Perm (Fin 22)) x), this, coe_apply_inv_apply]

@[expose] def kernelSubgroup (B : Finset (Fin 22)) : Subgroup M22 :=
  fixingSubgroup M22 (B : Set (Fin 22))

theorem mem_kernelSubgroup {B : Finset (Fin 22)} {g : M22} :
    g ∈ kernelSubgroup B ↔ ∀ x ∈ B, (g : Equiv.Perm (Fin 22)) x = x := by
  rw [kernelSubgroup, mem_fixingSubgroup_iff]
  rfl

theorem card_kernelSubgroup_hexad0 : Nat.card (kernelSubgroup hexad0) = 16 := by
  rw [← count_kernel_hexad0, ← card_m22_subtype]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_kernelSubgroup)

theorem kernelSubgroup_hexad0_sq {g : M22} (hg : g ∈ kernelSubgroup hexad0) : g * g = 1 := by
  have hcard : Nat.card {g : M22 // g ∈ kernelSubgroup hexad0 ∧
      ∀ x, (g : Equiv.Perm (Fin 22)) ((g : Equiv.Perm (Fin 22)) x) = x} = 16 := by
    rw [← count_kernel_sq_hexad0, ← card_m22_subtype]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by rw [mem_kernelSubgroup])
  set f : {g : M22 // g ∈ kernelSubgroup hexad0 ∧
      ∀ x, (g : Equiv.Perm (Fin 22)) ((g : Equiv.Perm (Fin 22)) x) = x} →
      kernelSubgroup hexad0 := fun g => ⟨g.1, g.2.1⟩
  have hf : Function.Injective f := fun a b e =>
    Subtype.ext (congrArg (fun k : kernelSubgroup hexad0 => (k : M22)) e)
  have hbij := hf.bijective_of_nat_card_le (by rw [hcard, card_kernelSubgroup_hexad0])
  obtain ⟨⟨g', hg'⟩, e⟩ := hbij.2 ⟨g, hg⟩
  have hgg : g' = g := congrArg Subtype.val e
  subst hgg
  exact Subtype.ext (Equiv.ext fun x => hg'.2 x)

theorem card_compl_hexad0 : ({z | z ∉ hexad0} : Set (Fin 22)).ncard = 16 := by
  rw [show ({z | z ∉ hexad0} : Set (Fin 22)) = ↑(hexad0ᶜ) by ext; simp, Set.ncard_coe_finset]
  decide

theorem kernelSubgroup_hexad0_regular {x y : Fin 22} (hx : x ∉ hexad0) (hy : y ∉ hexad0) :
    ∃! g : M22, g ∈ kernelSubgroup hexad0 ∧ (g : Equiv.Perm (Fin 22)) x = y := by
  set K := kernelSubgroup hexad0
  have hstab3 : Nat.card (stabilizer K (3 : Fin 22)) = 1 := by
    rw [← count_kernel_fix_hexad0, ← card_m22_subtype]
    refine Nat.card_congr ⟨fun g => ⟨g.1.1, mem_kernelSubgroup.1 g.1.2, g.2⟩,
      fun g => ⟨⟨g.1, mem_kernelSubgroup.2 g.2.1⟩, g.2.2⟩, fun _ => rfl, fun _ => rfl⟩
  have hpres : ∀ (g : K) (z : Fin 22), z ∉ hexad0 → g • z ∉ hexad0 := by
    intro g z hz hgz
    have hfix := mem_kernelSubgroup.1 g.2
    have h1 : (g.1 : Equiv.Perm (Fin 22)) z = (g.1 : Equiv.Perm (Fin 22)) (g • z) := by
      rw [hfix _ hgz]
      rfl
    exact hz (((g.1 : Equiv.Perm (Fin 22)).injective h1) ▸ hgz)
  have horb3 : orbit K (3 : Fin 22) = {z | z ∉ hexad0} := by
    have hsub : orbit K (3 : Fin 22) ⊆ {z | z ∉ hexad0} := by
      rintro _ ⟨g, rfl⟩
      exact hpres g 3 (by decide)
    have hcard : (orbit K (3 : Fin 22)).ncard = 16 := by
      have h := natCard_orbit_mul_card_stabilizer K (3 : Fin 22)
      rw [hstab3, card_kernelSubgroup_hexad0, mul_one, Nat.card_coe_set_eq] at h
      exact h
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [card_compl_hexad0, hcard]
  have horb : ∀ z, z ∉ hexad0 → orbit K z = {z | z ∉ hexad0} := by
    intro z hz
    have : z ∈ orbit K (3 : Fin 22) := by rw [horb3]; exact hz
    rw [orbit_eq_iff.2 this, horb3]
  have hstab : ∀ z, z ∉ hexad0 → Nat.card (stabilizer K z) = 1 := by
    intro z hz
    have h := natCard_orbit_mul_card_stabilizer K z
    rw [horb z hz, card_kernelSubgroup_hexad0, Nat.card_coe_set_eq, card_compl_hexad0] at h
    omega
  obtain ⟨g, hg⟩ : y ∈ orbit K x := by rw [horb x hx]; exact hy
  refine ⟨g.1, ⟨g.2, hg⟩, ?_⟩
  rintro g' ⟨hg'K, hg'⟩
  have hmem : (⟨g.1⁻¹ * g', K.mul_mem (K.inv_mem g.2) hg'K⟩ : K) ∈ stabilizer K x := by
    rw [mem_stabilizer_iff, Subgroup.smul_def]
    change ((g.1⁻¹ * g' : M22) : Equiv.Perm (Fin 22)) x = x
    rw [coe_mul_apply, hg', ← hg]
    exact coe_inv_apply_apply g.1 x
  have hsub := (Nat.card_eq_one_iff_unique.1 (hstab x hx)).1
  have := congrArg (fun k : stabilizer K x => (k.1.1 : M22))
    (Subsingleton.elim (⟨_, hmem⟩ : stabilizer K x) 1)
  simp only [OneMemClass.coe_one] at this
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem mem_kernelSubgroup_smul {h g : M22} {B : Finset (Fin 22)} :
    g ∈ kernelSubgroup (h • B) ↔ h⁻¹ * g * h ∈ kernelSubgroup B := by
  rw [mem_kernelSubgroup, mem_kernelSubgroup, fixes_smul_iff]

theorem card_kernelSubgroup {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    Nat.card (kernelSubgroup B) = 16 := by
  obtain ⟨h, rfl⟩ := mem_hexads_iff.1 hB
  rw [← card_kernelSubgroup_hexad0]
  exact card_subtype_conj h fun g => mem_kernelSubgroup_smul

theorem kernelSubgroup_sq {B : Finset (Fin 22)} (hB : B ∈ hexads) {g : M22}
    (hg : g ∈ kernelSubgroup B) : g * g = 1 := by
  obtain ⟨h, rfl⟩ := mem_hexads_iff.1 hB
  have := kernelSubgroup_hexad0_sq (mem_kernelSubgroup_smul.1 hg)
  have e : h⁻¹ * (g * g) * h = 1 := by
    rw [← this]
    group
  calc g * g = h * (h⁻¹ * (g * g) * h) * h⁻¹ := by group
    _ = 1 := by rw [e]; group

theorem kernelSubgroup_regular {B : Finset (Fin 22)} (hB : B ∈ hexads) {x y : Fin 22}
    (hx : x ∉ B) (hy : y ∉ B) :
    ∃! g : M22, g ∈ kernelSubgroup B ∧ (g : Equiv.Perm (Fin 22)) x = y := by
  obtain ⟨h, rfl⟩ := mem_hexads_iff.1 hB
  rw [mem_smul_finset_iff] at hx hy
  obtain ⟨g₀, ⟨hg₀, hg₀x⟩, hu⟩ := kernelSubgroup_hexad0_regular hx hy
  refine ⟨h * g₀ * h⁻¹, ⟨mem_kernelSubgroup_smul.2 (by group; exact hg₀), ?_⟩, ?_⟩
  · rw [coe_mul_apply, coe_mul_apply, hg₀x, coe_apply_inv_apply]
  · rintro g ⟨hg, hgx⟩
    have e := hu (h⁻¹ * g * h) ⟨mem_kernelSubgroup_smul.1 hg, by
      rw [coe_mul_apply, coe_mul_apply, coe_apply_inv_apply, hgx]⟩
    rw [← e]
    group

theorem stabilizer_mem_iff {B : Finset (Fin 22)} (g : stabilizer M22 B) (x : Fin 22) :
    (g.1 : Equiv.Perm (Fin 22)) x ∈ B ↔ x ∈ B := by
  have h := g.2
  rw [mem_stabilizer_iff] at h
  rw [← apply_mem_smul_finset_iff g.1 B x, h]

@[expose] def resHexad (B : Finset (Fin 22)) : stabilizer M22 B →* Equiv.Perm B where
  toFun g := (g.1 : Equiv.Perm (Fin 22)).subtypePerm fun x => stabilizer_mem_iff g x
  map_one' := by
    ext
    rfl
  map_mul' _ _ := by
    ext
    rfl

theorem coe_resHexad_apply {B : Finset (Fin 22)} (g : stabilizer M22 B) (x : B) :
    ((resHexad B g x : B) : Fin 22) = (g.1 : Equiv.Perm (Fin 22)) x := rfl

theorem kernelSubgroup_le_stabilizer (B : Finset (Fin 22)) :
    kernelSubgroup B ≤ stabilizer M22 B := by
  intro g hg
  rw [mem_stabilizer_finset_iff]
  intro x hx
  rw [mem_kernelSubgroup.1 hg x hx]
  exact hx

theorem mem_ker_resHexad {B : Finset (Fin 22)} {g : stabilizer M22 B} :
    g ∈ (resHexad B).ker ↔ g.1 ∈ kernelSubgroup B := by
  rw [MonoidHom.mem_ker, mem_kernelSubgroup]
  constructor
  · intro h x hx
    have := congrArg (fun σ : Equiv.Perm B => ((σ ⟨x, hx⟩ : B) : Fin 22)) h
    exact this
  · intro h
    refine Equiv.ext fun x => Subtype.ext ?_
    exact h x x.2

@[expose] def kerEquiv (B : Finset (Fin 22)) : (resHexad B).ker ≃ kernelSubgroup B where
  toFun g := ⟨g.1.1, mem_ker_resHexad.1 g.2⟩
  invFun g := ⟨⟨g.1, kernelSubgroup_le_stabilizer B g.2⟩, mem_ker_resHexad.2 g.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_ker_resHexad {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    Nat.card (resHexad B).ker = 16 := by
  rw [Nat.card_congr (kerEquiv B), card_kernelSubgroup hB]

theorem ker_resHexad_mul_self {B : Finset (Fin 22)} (hB : B ∈ hexads) (e : (resHexad B).ker) :
    e * e = 1 := by
  have h := kernelSubgroup_sq hB (mem_ker_resHexad.1 e.2)
  exact Subtype.ext (Subtype.ext h)

theorem ker_resHexad_comm {B : Finset (Fin 22)} (hB : B ∈ hexads) (e f : (resHexad B).ker) :
    e * f = f * e := by
  have he := inv_eq_of_mul_eq_one_right (ker_resHexad_mul_self hB e)
  have hf := inv_eq_of_mul_eq_one_right (ker_resHexad_mul_self hB f)
  have hef := inv_eq_of_mul_eq_one_right (ker_resHexad_mul_self hB (e * f))
  calc e * f = (e * f)⁻¹ := hef.symm
    _ = f⁻¹ * e⁻¹ := mul_inv_rev e f
    _ = f * e := by rw [he, hf]

theorem existsUnique_ker_resHexad {B : Finset (Fin 22)} (hB : B ∈ hexads) {x y : Fin 22}
    (hx : x ∉ B) (hy : y ∉ B) :
    ∃! e : (resHexad B).ker, (e.1.1 : Equiv.Perm (Fin 22)) x = y := by
  obtain ⟨g, ⟨hg, hgx⟩, hu⟩ := kernelSubgroup_regular hB hx hy
  refine ⟨(kerEquiv B).symm ⟨g, hg⟩, hgx, fun e he => ?_⟩
  have := hu e.1.1 ⟨mem_ker_resHexad.1 e.2, he⟩
  exact (kerEquiv B).injective (Subtype.ext this)

theorem card_hexad_type {B : Finset (Fin 22)} (hB : B ∈ hexads) : Fintype.card B = 6 := by
  rw [Fintype.card_coe, card_of_mem_hexads hB]

theorem range_resHexad {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    (resHexad B).range = alternatingGroup B := by
  refine Equiv.Perm.eq_alternatingGroup_of_index_eq_two ?_
  have h1 := Subgroup.card_mul_index (resHexad B).ker
  rw [Subgroup.index_ker, card_ker_resHexad hB, card_stabilizer_hexad hB] at h1
  have h2 := Subgroup.card_mul_index (resHexad B).range
  rw [Nat.card_perm, Nat.card_eq_finsetCard, card_of_mem_hexads hB] at h2
  have h3 : Nat.card (resHexad B).range = 360 := by omega
  rw [h3] at h2
  have : (6 : ℕ).factorial = 360 * 2 := by decide
  rw [this] at h2
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2

theorem exists_complement {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    ∃ F : Subgroup (stabilizer M22 B), F ⊓ (resHexad B).ker = ⊥ ∧ F ⊔ (resHexad B).ker = ⊤ ∧
      Nonempty (F ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, x ∉ B := by
    by_contra h
    push Not at h
    have := Finset.card_le_card (fun x _ => h x : (Finset.univ : Finset (Fin 22)) ⊆ B)
    rw [Finset.card_univ, Fintype.card_fin, card_of_mem_hexads hB] at this
    omega
  set F : Subgroup (stabilizer M22 B) := stabilizer (stabilizer M22 B) x₀
  have hmemF : ∀ g : stabilizer M22 B, g ∈ F ↔ (g.1 : Equiv.Perm (Fin 22)) x₀ = x₀ := fun g =>
    Iff.rfl
  have hinf : F ⊓ (resHexad B).ker = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgF, hgK⟩
    rw [Subgroup.mem_bot]
    obtain ⟨e, -, hu⟩ := existsUnique_ker_resHexad hB hx₀ hx₀
    have h1 := hu ⟨g, hgK⟩ ((hmemF g).1 hgF)
    have h2 := hu 1 rfl
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hdecomp : ∀ g : stabilizer M22 B,
      ∃ e : (resHexad B).ker, (e : stabilizer M22 B) * g ∈ F := by
    intro g
    have hgx : (g.1 : Equiv.Perm (Fin 22)) x₀ ∉ B := fun h => hx₀ ((stabilizer_mem_iff g x₀).1 h)
    obtain ⟨e, he, -⟩ := existsUnique_ker_resHexad hB hgx hx₀
    exact ⟨e, he⟩
  have hsup : F ⊔ (resHexad B).ker = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨e, he⟩ := hdecomp g
    have : g = (e : stabilizer M22 B)⁻¹ * ((e : stabilizer M22 B) * g) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ e.2))
      (Subgroup.mem_sup_left he)
  refine ⟨F, hinf, hsup, ?_⟩
  set φ := (resHexad B).comp F.subtype
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro f hf
    rw [Subgroup.mem_bot]
    have hfK : (f : stabilizer M22 B) ∈ (resHexad B).ker := hf
    have := hinf ▸ (Subgroup.mem_inf.2 ⟨f.2, hfK⟩ : (f : stabilizer M22 B) ∈ F ⊓ _)
    exact Subtype.ext ((Subgroup.mem_bot).1 this)
  have hrange : φ.range = alternatingGroup B := by
    rw [← range_resHexad hB]
    refine le_antisymm ?_ ?_
    · rintro _ ⟨f, rfl⟩
      exact ⟨f, rfl⟩
    · rintro _ ⟨g, rfl⟩
      obtain ⟨e, he⟩ := hdecomp g
      refine ⟨⟨_, he⟩, ?_⟩
      change resHexad B ((e : stabilizer M22 B) * g) = resHexad B g
      rw [map_mul, (MonoidHom.mem_ker).1 e.2, one_mul]
  exact ⟨(MonoidHom.ofInjective hφ).trans ((MulEquiv.subgroupCongr hrange).trans
    (Equiv.altCongrHom (Fintype.equivFinOfCardEq (card_hexad_type hB))))⟩

theorem exists_stabilizer_apply_eq_iff {B : Finset (Fin 22)} (hB : B ∈ hexads) (x y : Fin 22) :
    (∃ g : stabilizer M22 B, (g.1 : Equiv.Perm (Fin 22)) x = y) ↔ (x ∈ B ↔ y ∈ B) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact (stabilizer_mem_iff g x).symm
  · intro hxy
    by_cases hx : x ∈ B
    · have hy := hxy.1 hx
      have : MulAction.IsPretransitive (alternatingGroup B) B := by
        refine alternatingGroup.isPretransitive_of_three_le_card (α := B) ?_
        rw [Nat.card_eq_finsetCard, card_of_mem_hexads hB]
        norm_num
      obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup B) (⟨x, hx⟩ : B) ⟨y, hy⟩
      obtain ⟨g, hg⟩ : (σ : Equiv.Perm B) ∈ (resHexad B).range := by
        rw [range_resHexad hB]
        exact σ.2
      refine ⟨g, ?_⟩
      have h1 : resHexad B g ⟨x, hx⟩ = ⟨y, hy⟩ := by
        rw [hg]
        exact hσ
      exact congrArg Subtype.val h1
    · have hy : y ∉ B := fun h => hx (hxy.2 h)
      obtain ⟨e, he, -⟩ := existsUnique_ker_resHexad hB hx hy
      exact ⟨e, he⟩

theorem card_inter_smul (g : M22) (B B' : Finset (Fin 22)) :
    (g • B ∩ g • B').card = (B ∩ B').card := by
  rw [← Finset.smul_finset_inter, Finset.card_smul_finset]

theorem stabilizer_smul_eq {B : Finset (Fin 22)} (g : stabilizer M22 B) : g.1 • B = B := g.2

@[expose] def stabStabEquiv (C : Finset (Fin 22)) :
    stabilizer (stabilizer M22 hexad0) C ≃
      {g : M22 // (∀ x ∈ hexad0, (g : Equiv.Perm (Fin 22)) x ∈ hexad0) ∧
        ∀ x ∈ C, (g : Equiv.Perm (Fin 22)) x ∈ C} where
  toFun g := ⟨g.1.1, mem_stabilizer_finset_iff.1 g.1.2, mem_stabilizer_finset_iff.1 g.2⟩
  invFun g := ⟨⟨g.1, mem_stabilizer_finset_iff.2 g.2.1⟩, mem_stabilizer_finset_iff.2 g.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem orbit_stabilizer_hexad0 {C : Finset (Fin 22)} (hC : C ∈ hexads) {k s : ℕ}
    (hs : Nat.card (stabilizer (stabilizer M22 hexad0) C) = s) (hsk : k * s = 5760)
    (hk : (hexads.filter fun C' => (hexad0 ∩ C').card = (hexad0 ∩ C).card).card = k) :
    orbit (stabilizer M22 hexad0) C =
      ↑(hexads.filter fun C' => (hexad0 ∩ C').card = (hexad0 ∩ C).card) := by
  have hsub : orbit (stabilizer M22 hexad0) C ⊆
      ↑(hexads.filter fun C' => (hexad0 ∩ C').card = (hexad0 ∩ C).card) := by
    rintro _ ⟨g, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_filter]
    refine ⟨smul_mem_hexads g.1 hC, ?_⟩
    have := card_inter_smul g.1 hexad0 C
    rwa [stabilizer_smul_eq g] at this
  have hcard : (orbit (stabilizer M22 hexad0) C).ncard = k := by
    have h := natCard_orbit_mul_card_stabilizer (stabilizer M22 hexad0) C
    rw [hs, card_stabilizer_hexad0, Nat.card_coe_set_eq, ← hsk] at h
    have hspos : 0 < s := by
      rw [← hs]
      exact Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hspos h
  refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
  rw [Set.ncard_coe_finset, hk, hcard]

theorem card_stabilizer_D0 : Nat.card (stabilizer (stabilizer M22 hexad0) hexadD0) = 360 := by
  rw [Nat.card_congr (stabStabEquiv hexadD0), ← count_stabilizer_D0, ← card_m22_subtype]

theorem card_stabilizer_T0 : Nat.card (stabilizer (stabilizer M22 hexad0) hexadT0) = 96 := by
  rw [Nat.card_congr (stabStabEquiv hexadT0), ← count_stabilizer_T0, ← card_m22_subtype]

theorem card_inter_hexadD0 : (hexad0 ∩ hexadD0).card = 0 :=
  Certificates.certificate2030.2.2.2.2.2.2.2.1

theorem card_inter_hexadT0 : (hexad0 ∩ hexadT0).card = 2 :=
  Certificates.certificate2030.2.2.2.2.2.2.2.2

theorem card_filter_inter_zero {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    (hexads.filter fun C' => (B ∩ C').card = 0).card = 16 := by
  have e : hexads.filter (fun C' => (B ∩ C').card = 0) = hexads.filter fun C' => Disjoint B C' :=
    Finset.filter_congr fun C' _ => by
      rw [Finset.card_eq_zero, Finset.disjoint_iff_inter_eq_empty]
  rw [e, (hexads_intersections hB).1]

theorem exists_smul_hexad0_eq {C C' : Finset (Fin 22)} (hC : C ∈ hexads) (hC' : C' ∈ hexads)
    (h : (hexad0 ∩ C).card = (hexad0 ∩ C').card) :
    ∃ g : stabilizer M22 hexad0, g.1 • C = C' := by
  have hcases : ∀ D ∈ hexads, D = hexad0 ∨ (hexad0 ∩ D).card = 0 ∨ (hexad0 ∩ D).card = 2 := by
    intro D hD
    by_cases e : D = hexad0
    · exact Or.inl e
    · exact Or.inr (isSteinerTriple_hexads.card_inter hexad0_mem hD (Ne.symm e))
  have h6 : (hexad0 ∩ hexad0).card = 6 := by
    rw [Finset.inter_self]
    exact card_of_mem_hexads hexad0_mem
  have heq : ∀ D ∈ hexads, (hexad0 ∩ D).card = 6 → D = hexad0 := by
    intro D hD hD6
    rcases hcases D hD with e | e | e
    · exact e
    · omega
    · omega
  have horbit : ∀ {D₀ : Finset (Fin 22)}, D₀ ∈ hexads → ∀ {k s : ℕ},
      Nat.card (stabilizer (stabilizer M22 hexad0) D₀) = s → k * s = 5760 →
      (hexads.filter fun D => (hexad0 ∩ D).card = (hexad0 ∩ D₀).card).card = k →
      ∀ D ∈ hexads, (hexad0 ∩ D).card = (hexad0 ∩ D₀).card →
        ∃ g : stabilizer M22 hexad0, g.1 • D₀ = D := by
    intro D₀ hD₀ k s hs hsk hk D hD hDc
    have hmem : D ∈ orbit (stabilizer M22 hexad0) D₀ := by
      rw [orbit_stabilizer_hexad0 hD₀ hs hsk hk]
      exact Finset.mem_filter.2 ⟨hD, hDc⟩
    obtain ⟨g, hg⟩ := hmem
    exact ⟨g, hg⟩
  rcases hcases C hC with rfl | hc | hc
  · have := heq C' hC' (h ▸ h6)
    exact ⟨1, by rw [this]; rfl⟩
  · have h16 : (hexads.filter fun D => (hexad0 ∩ D).card = (hexad0 ∩ hexadD0).card).card = 16 := by
      rw [card_inter_hexadD0]
      exact card_filter_inter_zero hexad0_mem
    obtain ⟨g₁, hg₁⟩ := horbit hexadD0_mem card_stabilizer_D0 (by norm_num) h16 C hC
      (by rw [hc, card_inter_hexadD0])
    obtain ⟨g₂, hg₂⟩ := horbit hexadD0_mem card_stabilizer_D0 (by norm_num) h16 C' hC'
      (by rw [← h, hc, card_inter_hexadD0])
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    rw [← hg₁, ← hg₂, Subgroup.coe_mul, mul_smul, Subgroup.coe_inv, inv_smul_smul]
  · have h60 : (hexads.filter fun D => (hexad0 ∩ D).card = (hexad0 ∩ hexadT0).card).card = 60 := by
      rw [card_inter_hexadT0]
      exact (hexads_intersections hexad0_mem).2
    obtain ⟨g₁, hg₁⟩ := horbit hexadT0_mem card_stabilizer_T0 (by norm_num) h60 C hC
      (by rw [hc, card_inter_hexadT0])
    obtain ⟨g₂, hg₂⟩ := horbit hexadT0_mem card_stabilizer_T0 (by norm_num) h60 C' hC'
      (by rw [← h, hc, card_inter_hexadT0])
    refine ⟨g₂ * g₁⁻¹, ?_⟩
    rw [← hg₁, ← hg₂, Subgroup.coe_mul, mul_smul, Subgroup.coe_inv, inv_smul_smul]

theorem exists_stabilizer_smul_hexad_eq_iff {B : Finset (Fin 22)} (hB : B ∈ hexads)
    {C C' : Finset (Fin 22)} (hC : C ∈ hexads) (hC' : C' ∈ hexads) :
    (∃ g : stabilizer M22 B, g.1 • C = C') ↔ (B ∩ C).card = (B ∩ C').card := by
  constructor
  · rintro ⟨g, rfl⟩
    have := card_inter_smul g.1 B C
    rw [stabilizer_smul_eq g] at this
    exact this.symm
  · intro h
    obtain ⟨k, rfl⟩ := mem_hexads_iff.1 hB
    have hD : k⁻¹ • C ∈ hexads := smul_mem_hexads _ hC
    have hD' : k⁻¹ • C' ∈ hexads := smul_mem_hexads _ hC'
    have e : ∀ D : Finset (Fin 22), (hexad0 ∩ k⁻¹ • D).card = (k • hexad0 ∩ D).card := by
      intro D
      rw [← card_inter_smul k, smul_inv_smul]
    obtain ⟨g₀, hg₀⟩ := exists_smul_hexad0_eq hD hD' (by rw [e, e, h])
    have hmem : k * g₀.1 * k⁻¹ ∈ stabilizer M22 (k • hexad0) := by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_smul, stabilizer_smul_eq g₀]
    refine ⟨⟨_, hmem⟩, ?_⟩
    change (k * g₀.1 * k⁻¹) • C = C'
    rw [mul_smul, mul_smul, hg₀, smul_inv_smul]

theorem exists_stabilizer_point_smul_hexad_eq_iff (a : Fin 22) {C C' : Finset (Fin 22)}
    (hC : C ∈ hexads) (hC' : C' ∈ hexads) :
    (∃ g : stabilizer M22 a, g.1 • C = C') ↔ (a ∈ C ↔ a ∈ C') := by
  constructor
  · rintro ⟨g, rfl⟩
    have hga : (g.1 : Equiv.Perm (Fin 22)) a = a := g.2
    rw [← apply_mem_smul_finset_iff g.1 C a, hga]
  · intro h
    by_cases ha : a ∈ C
    · have ha' := h.1 ha
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 (show 1 < (C.erase a).card by
        rw [Finset.card_erase_of_mem ha, card_of_mem_hexads hC]
        norm_num)
      obtain ⟨x', hx', y', hy', hxy'⟩ := Finset.one_lt_card.1 (show 1 < (C'.erase a).card by
        rw [Finset.card_erase_of_mem ha', card_of_mem_hexads hC']
        norm_num)
      rw [Finset.mem_erase] at hx hy hx' hy'
      obtain ⟨g, hga, hgx, hgy⟩ := exists_smul_eq_triple (Ne.symm hx.1) (Ne.symm hy.1) hxy
        (Ne.symm hx'.1) (Ne.symm hy'.1) hxy'
      refine ⟨⟨g, hga⟩, ?_⟩
      have hT : ({a, x', y'} : Finset (Fin 22)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [Ne.symm hx'.1, Ne.symm hy'.1]),
          Finset.card_pair hxy']
      obtain ⟨D, -, hu⟩ := isSteinerTriple_hexads.2.2 _ hT
      have hsub : ∀ E : Finset (Fin 22), a ∈ E → x' ∈ E → y' ∈ E → {a, x', y'} ⊆ E := by
        intro E h1 h2 h3 z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl <;> assumption
      have hgC : g • C ∈ hexads := smul_mem_hexads g hC
      have h1 : a ∈ g • C := by
        rw [← hga]
        exact (apply_mem_smul_finset_iff g C a).2 ha
      have h2 : x' ∈ g • C := by
        rw [← hgx]
        exact (apply_mem_smul_finset_iff g C x).2 hx.2
      have h3 : y' ∈ g • C := by
        rw [← hgy]
        exact (apply_mem_smul_finset_iff g C y).2 hy.2
      exact (hu _ ⟨hgC, hsub _ h1 h2 h3⟩).trans
        (hu C' ⟨hC', hsub _ ha' hx'.2 hy'.2⟩).symm
    · have ha' : a ∉ C' := fun h' => ha (h.2 h')
      obtain ⟨k, rfl⟩ := mem_hexads_iff.1 hC
      obtain ⟨k', rfl⟩ := mem_hexads_iff.1 hC'
      set h₀ : M22 := k' * k⁻¹
      have hC0 : h₀ • k • hexad0 = k' • hexad0 := by
        rw [smul_smul, inv_mul_cancel_right]
      have hx : (h₀ : Equiv.Perm (Fin 22)) a ∉ k' • hexad0 := by
        rw [← hC0, apply_mem_smul_finset_iff]
        exact ha
      obtain ⟨m, hm⟩ := (exists_stabilizer_apply_eq_iff hC' _ a).2 (iff_of_false hx ha')
      have hmem : m.1 * h₀ ∈ stabilizer M22 a := by
        change ((m.1 * h₀ : M22) : Equiv.Perm (Fin 22)) a = a
        rw [coe_mul_apply, hm]
      refine ⟨⟨_, hmem⟩, ?_⟩
      change (m.1 * h₀) • k • hexad0 = k' • hexad0
      rw [mul_smul, hC0, stabilizer_smul_eq m]

end CFSG.ComponentClassification.WittDesign
