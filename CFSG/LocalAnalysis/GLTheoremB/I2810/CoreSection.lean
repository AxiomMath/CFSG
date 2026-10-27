module

public import CFSG.LocalAnalysis.GLTheoremB.I2810.Defs
import CFSG.LocalAnalysis.GLTheoremB.I2810.CoreLattice
import CFSG.LocalAnalysis.GLTheoremB.I2810.InducedAux
import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeAbstract

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open CFSG.ComponentClassification.OutcomeLocal CFSG.HardMathSupport.Cooperstein.StructureLie
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux

section Sec
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem rho_triv_of_W_proof (hR : Red28 W K S) {a : X} {U₁ U₂ : Subgroup X}
    (hU : U₁ ≤ vOf W K S) {P : Type} [AddCommGroup P] [Module (ZMod 2) P]
    {ρ : ↥(K ⊔ Subgroup.zpowers a) →* LinearMap.GeneralLinearGroup (ZMod 2) P}
    {φ : ↥U₁ →* Multiplicative P} (hd : SecRepData (K ⊔ Subgroup.zpowers a) U₁ U₂ ρ φ) :
    ∀ k : ↥K, (k : X) ∈ W → ρ ⟨k, Subgroup.mem_sup_left k.2⟩ = 1 := by
  intro k hkW
  have hkw : (k : X) ∈ kerAct W K S := hR.w1_le hkW
  apply Units.ext
  apply LinearMap.ext
  intro p
  obtain ⟨u, hu⟩ := hd.surj (Multiplicative.ofAdd p)
  have hc : (u : X) = (⟨k, Subgroup.mem_sup_left k.2⟩ : ↥(K ⊔ Subgroup.zpowers a)) * (u : X) *
      (⟨k, Subgroup.mem_sup_left k.2⟩ : ↥(K ⊔ Subgroup.zpowers a))⁻¹ := by
    have := (hU u.2).2.1 (k : X) hkw
    show (u : X) = (k : X) * (u : X) * (k : X)⁻¹
    rw [← this]; group
  have := hd.equiv ⟨k, Subgroup.mem_sup_left k.2⟩ u u hc
  rw [hu] at this
  have h2 : p = (ρ ⟨k, Subgroup.mem_sup_left k.2⟩ : P →ₗ[ZMod 2] P) p := by
    simpa using this
  rw [Units.val_one, Module.End.one_apply]
  exact h2.symm

theorem rho_nontriv {V U₁ U₂ : Subgroup X} {a : X} (hb : SFBase K V U₁ U₂) {P : Type}
    [AddCommGroup P] [Module (ZMod 2) P]
    {ρ : ↥(K ⊔ Subgroup.zpowers a) →* LinearMap.GeneralLinearGroup (ZMod 2) P}
    {φ : ↥U₁ →* Multiplicative P} (hd : SecRepData (K ⊔ Subgroup.zpowers a) U₁ U₂ ρ φ) :
    ∃ k : ↥K, ρ ⟨k, Subgroup.mem_sup_left k.2⟩ ≠ 1 := by
  obtain ⟨k, hk, x, hx, hxk⟩ := hb.nontriv
  refine ⟨⟨k, hk⟩, fun h1 => hxk ?_⟩
  have hx' : x⁻¹ ∈ U₁ := U₁.inv_mem hx
  have hk' : k * x⁻¹ * k⁻¹ ∈ U₁ := hb.inv₁ k hk x⁻¹ hx'
  have h2 := hd.equiv ⟨k, Subgroup.mem_sup_left hk⟩ ⟨x⁻¹, hx'⟩ ⟨_, hk'⟩ rfl
  rw [h1] at h2
  simp only [Units.val_one, Module.End.one_apply, ofAdd_toAdd] at h2
  have h3 : φ (⟨x, hx⟩ * ⟨k * x⁻¹ * k⁻¹, hk'⟩) = 1 := by
    rw [map_mul, h2]
    have : (⟨x, hx⟩ : ↥U₁) * ⟨x⁻¹, hx'⟩ = 1 := Subtype.ext (by simp)
    rw [← map_mul, this, map_one]
  have h4 := (hd.ker _).1 h3
  have : ⁅x, k⁆ = x * (k * x⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
  rw [this]
  exact h4

theorem Mof_le_normalizer_of_mem {a : X} (haN : a ∈ Subgroup.normalizer (K : Set X)) :
    Mof K a ≤ Subgroup.normalizer (K : Set X) :=
  sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 haN)

theorem Mof_le_normalizer (h : Setup28 W K S) {a : X} (haS : a ∈ S) :
    Mof K a ≤ Subgroup.normalizer (K : Set X) :=
  Mof_le_normalizer_of_mem (h.hN haS)

theorem outer_rho_proof (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    {U₁ U₂ : Subgroup X} (hts : TransSection K (vOf W K S) U₁ U₂ a)
    (hout : ¬ IndInner W K a) {P : Type} [AddCommGroup P] [Module (ZMod 2) P]
    (ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P) (φ : ↥U₁ →* Multiplicative P)
    (hd : SecRepData (Mof K a) U₁ U₂ ρ φ) :
    ρ (aM K a) ∉ (K.subgroupOf (Mof K a)).map ρ := by
  intro hmem
  obtain ⟨m, hmK, hmρ⟩ := hmem
  have hmK' : (m : X) ∈ K := Subgroup.mem_subgroupOf.1 hmK
  have hMn : Mof K a ≤ Subgroup.normalizer (K : Set X) := Mof_le_normalizer h haS
  set c : ↥(Mof K a) := aM K a * m⁻¹ with hc
  have hρc : ρ c = 1 := by rw [hc, map_mul, map_inv, hmρ, mul_inv_cancel]
  have hcX : (c : X) = a * (m : X)⁻¹ := rfl
  let ind := InducedAux.indHom W K (Mof K a) hMn
  let incl : ↥K →* ↥(Mof K a) := Subgroup.inclusion (le_sup_left : K ≤ Mof K a)
  let ρK : ↥K →* LinearMap.GeneralLinearGroup (ZMod 2) P := ρ.comp incl
  let R : Subgroup ↥K := ρK.ker
  let Z : Subgroup ↥(bar W K) := R.map (toBar W K)
  haveI hRn : R.Normal := MonoidHom.normal_ker ρK
  haveI hZn : Z.Normal := Subgroup.Normal.map hRn (toBar W K) InducedAux.toBar_surjective
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hR.quasi hZn with hZ | hZ
  ·
    exfalso
    obtain ⟨k₀, hk₀⟩ := rho_nontriv hts.toSingleFactor.toSFBase hd
    apply hk₀
    have hmem : toBar W K k₀ ∈ Z := hZ ▸ Subgroup.mem_top _
    obtain ⟨r, hr, hrk⟩ := hmem
    have hW : ((r⁻¹ * k₀ : ↥K) : X) ∈ W := by
      rw [← InducedAux.toBar_eq_one_iff, map_mul, map_inv, hrk, inv_mul_cancel]
    have h1 := rho_triv_of_W_proof hR hts.le.2 hd (r⁻¹ * k₀) hW
    have hr1 : ρ (incl r) = 1 := hr
    have e : (⟨k₀, Subgroup.mem_sup_left k₀.2⟩ : ↥(Mof K a)) =
        incl r * ⟨((r⁻¹ * k₀ : ↥K) : X), Subgroup.mem_sup_left (r⁻¹ * k₀ : ↥K).2⟩ :=
      Subtype.ext (by simp [incl])
    rw [e, map_mul, hr1, h1, mul_one]
  ·
    have hα : ind c = 1 := by
      refine InducedAux.aut_eq_one hR.quasi.1.commutator_eq_top hZ (ind c) fun x => ?_
      obtain ⟨y, rfl⟩ := InducedAux.toBar_surjective x
      have hyc : (c : X) * (y : X) * (c : X)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.1 (hMn c.2) y).1 y.2
      have e1 : ind c (toBar W K y) = toBar W K ⟨(c : X) * y * (c : X)⁻¹, hyc⟩ := by
        apply Subtype.ext
        rw [InducedAux.indHom_toBar]; rfl
      rw [e1]
      refine ⟨y⁻¹ * ⟨_, hyc⟩, ?_, ?_⟩
      · show ρ (incl (y⁻¹ * ⟨_, hyc⟩)) = 1
        have e2 : incl ⟨(c : X) * y * (c : X)⁻¹, hyc⟩ = c * incl y * c⁻¹ := Subtype.ext (by simp [incl])
        have e3 : ρ (c * incl y * c⁻¹) = ρ (incl y) := by
          rw [map_mul, map_mul, map_inv, hρc]; simp
        rw [map_mul, map_inv, e2, map_mul, map_inv, e3, inv_mul_cancel]
      · rw [map_mul, map_inv]
    have hcomm := (InducedAux.indHom_eq_one_iff (Mof K a) hMn c).1 hα
    apply hout
    refine ⟨m, hmK', fun x hx => ?_⟩
    have hy : (m : X) * x * (m : X)⁻¹ ∈ K := K.mul_mem (K.mul_mem hmK' hx) (K.inv_mem hmK')
    have := hcomm _ hy
    have e : ⁅(c : X), (m : X) * x * (m : X)⁻¹⁆ = a * x * a⁻¹ * ((m : X) * x * (m : X)⁻¹)⁻¹ := by
      rw [hcX]; simp only [commutatorElement_def]; group
    rw [← e]; exact this

theorem rho_isF2Transvection {a : X} {U₁ U₂ : Subgroup X} {P : Type} [AddCommGroup P]
    [Module (ZMod 2) P] {ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P}
    {φ : ↥U₁ →* Multiplicative P} (hA : ASection a U₁ U₂)
    (hd : SecRepData (Mof K a) U₁ U₂ ρ φ) : IsF2Transvection (ρ (aM K a)) := by
  set t : P →ₗ[ZMod 2] P := (ρ (aM K a) : P →ₗ[ZMod 2] P) with ht
  have hx' : ∀ x : ↥U₁, a * (x : X) * a⁻¹ ∈ U₁ := fun x => hA.inv₁ x x.2
  have hcomm : ∀ x : ↥U₁, a * (x : X) * a⁻¹ * (x : X)⁻¹ ∈ U₁ := fun x =>
    U₁.mul_mem (hx' x) (U₁.inv_mem x.2)
  have key : ∀ x : ↥U₁, Multiplicative.toAdd (φ ⟨a * (x : X) * a⁻¹ * (x : X)⁻¹, hcomm x⟩) =
      t (Multiplicative.toAdd (φ x)) + Multiplicative.toAdd (φ x) := by
    intro x
    have e : (⟨a * (x : X) * a⁻¹ * (x : X)⁻¹, hcomm x⟩ : ↥U₁) =
        ⟨a * (x : X) * a⁻¹, hx' x⟩ * x⁻¹ := rfl
    have h1 := hd.equiv (aM K a) x ⟨a * (x : X) * a⁻¹, hx' x⟩ rfl
    rw [e, map_mul, map_inv, toAdd_mul, h1, toAdd_ofAdd, toAdd_inv, zmod2_neg]
  obtain ⟨u, huU₁, huU₂, htr⟩ := hA.tr
  set p₀ : P := Multiplicative.toAdd (φ ⟨u, huU₁⟩) with hp₀def
  have hp₀ : p₀ ≠ 0 := by
    intro h0
    apply huU₂
    refine (hd.ker ⟨u, huU₁⟩).1 ?_
    rw [← ofAdd_toAdd (φ ⟨u, huU₁⟩)]
    exact congrArg Multiplicative.ofAdd h0
  have hc : ∀ v : P, t v + v = 0 ∨ t v + v = p₀ := by
    intro v
    obtain ⟨x, hx⟩ := hd.surj (Multiplicative.ofAdd v)
    have hv : Multiplicative.toAdd (φ x) = v := by rw [hx]; rfl
    rcases htr x x.2 with h1 | h1
    · left
      have h2 := congrArg Multiplicative.toAdd ((hd.ker ⟨_, hcomm x⟩).2 h1)
      rw [key, hv] at h2
      simpa using h2
    · right
      have hmem : a * (x : X) * a⁻¹ * (x : X)⁻¹ * u⁻¹ ∈ U₁ :=
        U₁.mul_mem (hcomm x) (U₁.inv_mem huU₁)
      have h2 := congrArg Multiplicative.toAdd ((hd.ker ⟨_, hmem⟩).2 h1)
      have e : (⟨a * (x : X) * a⁻¹ * (x : X)⁻¹ * u⁻¹, hmem⟩ : ↥U₁) =
          ⟨a * (x : X) * a⁻¹ * (x : X)⁻¹, hcomm x⟩ * ⟨u, huU₁⟩⁻¹ := rfl
      rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, key, hv, ← hp₀def] at h2
      have h3 : t v + v + -p₀ = 0 := by simpa using h2
      exact (add_neg_eq_zero.1 h3)
  have hex : ∃ v : P, t v + v ≠ 0 := by
    obtain ⟨x, hx, hn⟩ := hA.nt
    refine ⟨Multiplicative.toAdd (φ ⟨x, hx⟩), fun h0 => hn ?_⟩
    have := (hd.ker ⟨_, hcomm ⟨x, hx⟩⟩).1 (by
      rw [← ofAdd_toAdd (φ ⟨_, hcomm ⟨x, hx⟩⟩), key, h0]; rfl)
    exact this
  have hne1 : ρ (aM K a) ≠ 1 := by
    intro h1
    obtain ⟨v, hv⟩ := hex
    apply hv
    rw [ht, h1]
    simp [zmod2_add_self]
  refine ⟨hne1, ?_⟩
  have hspan : commutatorSpace (ρ (aM K a)) = Submodule.span (ZMod 2) {p₀} := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      have hv : ((LinearMap.id + t : P →ₗ[ZMod 2] P) v) = t v + v := by
        rw [LinearMap.add_apply, LinearMap.id_apply, add_comm]
      rw [hv]
      rcases hc v with h | h
      · rw [h]; exact Submodule.zero_mem _
      · rw [h]; exact Submodule.mem_span_singleton_self p₀
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      obtain ⟨v₀, hv₀⟩ := hex
      refine ⟨v₀, ?_⟩
      have hv : ((LinearMap.id + t : P →ₗ[ZMod 2] P) v₀) = t v₀ + v₀ := by
        rw [LinearMap.add_apply, LinearMap.id_apply, add_comm]
      rw [hv]
      exact (hc v₀).resolve_left hv₀
  rw [hspan]
  exact finrank_span_singleton hp₀

theorem normal_subgroupOf_Mof_of_mem {a : X} (haN : a ∈ Subgroup.normalizer (K : Set X)) :
    (K.subgroupOf (Mof K a)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : K ≤ Mof K a)).2
    (Mof_le_normalizer_of_mem haN)

theorem normal_subgroupOf_Mof (h : Setup28 W K S) {a : X} (haS : a ∈ S) :
    (K.subgroupOf (Mof K a)).Normal :=
  normal_subgroupOf_Mof_of_mem (h.hN haS)

theorem sup_zpowers_aM_eq_top {K : Subgroup X} {a : X} :
    K.subgroupOf (Mof K a) ⊔ Subgroup.zpowers (aM K a) = ⊤ := by
  apply Subgroup.map_injective (f := (Mof K a).subtype) (Mof K a).subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le le_sup_left, MonoidHom.map_zpowers,
    Subgroup.map_top, Subgroup.range_subtype]
  rfl

theorem aM_normal_closure {K : Subgroup X} {a : X} (ha2 : a ^ 2 = 1)
    (hKc : ⁅K, Subgroup.zpowers a⁆ = K) (T : Subgroup ↥(Mof K a)) [T.Normal]
    (haT : aM K a ∈ T) : T = ⊤ := by
  let D : Subgroup X := T.map (Mof K a).subtype
  have hD : ∀ k ∈ K, ⁅k, a⁆ ∈ D := by
    intro k hk
    refine ⟨⁅(⟨k, Subgroup.mem_sup_left hk⟩ : ↥(Mof K a)), aM K a⁆, ?_, rfl⟩
    exact T.mul_mem (Subgroup.Normal.conj_mem inferInstance _ haT _) (T.inv_mem haT)
  have hKD : K ≤ D := CoreLattice.K_le_of_comm ha2 hKc hD
  have haD : a ∈ D := ⟨aM K a, haT, rfl⟩
  have hMD : Mof K a ≤ D := sup_le hKD ((Subgroup.zpowers_le).2 haD)
  rw [eq_top_iff]
  intro g _
  obtain ⟨t, ht, htg⟩ := hMD g.2
  have : t = g := Subtype.ext htg
  rw [← this]; exact ht

theorem rho_aM_mem_normalizer_of_mem {a : X} (haN : a ∈ Subgroup.normalizer (K : Set X)) {P : Type}
    [AddCommGroup P] [Module (ZMod 2) P]
    (ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P) :
    ρ (aM K a) ∈ Subgroup.normalizer
      (((K.subgroupOf (Mof K a)).map ρ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)) :
        Set (LinearMap.GeneralLinearGroup (ZMod 2) P)) := by
  haveI := normal_subgroupOf_Mof_of_mem haN
  have h1 : aM K a ∈ Subgroup.normalizer
      ((K.subgroupOf (Mof K a) : Subgroup ↥(Mof K a)) : Set ↥(Mof K a)) := by
    rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
    exact Subgroup.mem_top _
  exact Subgroup.le_normalizer_map ρ ⟨aM K a, h1, rfl⟩

theorem rho_aM_mem_normalizer (h : Setup28 W K S) {a : X} (haS : a ∈ S) {P : Type}
    [AddCommGroup P] [Module (ZMod 2) P]
    (ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P) :
    ρ (aM K a) ∈ Subgroup.normalizer
      (((K.subgroupOf (Mof K a)).map ρ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)) :
        Set (LinearMap.GeneralLinearGroup (ZMod 2) P)) :=
  rho_aM_mem_normalizer_of_mem (h.hN haS) ρ

theorem rho_K_perfect (h : Setup28 W K S) {a : X} {P : Type} [AddCommGroup P] [Module (ZMod 2) P]
    (ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P) :
    ⁅(K.subgroupOf (Mof K a)).map ρ, (K.subgroupOf (Mof K a)).map ρ⁆ =
      (K.subgroupOf (Mof K a)).map ρ := by
  have h1 : ⁅K.subgroupOf (Mof K a), K.subgroupOf (Mof K a)⁆ = K.subgroupOf (Mof K a) := by
    apply Subgroup.map_injective (f := (Mof K a).subtype) (Mof K a).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le le_sup_left, h.hK.2.1]
  rw [← Subgroup.map_commutator, h1]

theorem rho_irred {V U₁ U₂ : Subgroup X} (hsf : SingleFactor K V U₁ U₂) {a : X} {P : Type}
    [AddCommGroup P] [Module (ZMod 2) P]
    {ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P} {φ : ↥U₁ →* Multiplicative P}
    (hd : SecRepData (Mof K a) U₁ U₂ ρ φ) (U : Submodule (ZMod 2) P)
    (hU : ∀ g ∈ ρ.range, ∀ u ∈ U, (g : P →ₗ[ZMod 2] P) u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  let Yt : Subgroup ↥U₁ :=
    { carrier := {x | Multiplicative.toAdd (φ x) ∈ U}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, toAdd_mul] at hx hy ⊢
        exact U.add_mem hx hy
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq, map_inv, toAdd_inv] at hx ⊢
        exact U.neg_mem hx }
  let Y : Subgroup X := Yt.map U₁.subtype
  have hY : ∀ x : X, x ∈ Y ↔ ∃ hx : x ∈ U₁, Multiplicative.toAdd (φ ⟨x, hx⟩) ∈ U := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hxU⟩
      exact ⟨⟨x, hx⟩, hxU, rfl⟩
  have h₁ : U₂ ≤ Y := by
    intro x hx
    rw [hY]
    have hx1 : x ∈ U₁ := hsf.le.1 hx
    refine ⟨hx1, ?_⟩
    have := (hd.ker ⟨x, hx1⟩).2 hx
    rw [this]; exact U.zero_mem
  have h₂ : Y ≤ U₁ := by
    intro x hx
    exact ((hY x).1 hx).1
  have h₃ : ∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y := by
    intro k hk y hy
    obtain ⟨hy1, hyU⟩ := (hY y).1 hy
    have hky : k * y * k⁻¹ ∈ U₁ := hsf.inv₁ k hk y hy1
    rw [hY]
    refine ⟨hky, ?_⟩
    have h2 := hd.equiv ⟨k, Subgroup.mem_sup_left hk⟩ ⟨y, hy1⟩ ⟨_, hky⟩ rfl
    rw [h2, toAdd_ofAdd]
    exact hU _ ⟨_, rfl⟩ _ hyU
  rcases hsf.irred Y h₁ h₂ h₃ with h | h
  · left
    rw [eq_bot_iff]
    intro p hp
    obtain ⟨x, hx⟩ := hd.surj (Multiplicative.ofAdd p)
    have hxp : Multiplicative.toAdd (φ x) = p := by rw [hx]; rfl
    have hxY : (x : X) ∈ Y := (hY x).2 ⟨x.2, by simpa using (hxp ▸ hp : Multiplicative.toAdd (φ x) ∈ U)⟩
    rw [h] at hxY
    have := (hd.ker x).2 hxY
    rw [this] at hxp
    rw [Submodule.mem_bot, ← hxp]; rfl
  · right
    rw [eq_top_iff]
    intro p _
    obtain ⟨x, hx⟩ := hd.surj (Multiplicative.ofAdd p)
    have hxp : Multiplicative.toAdd (φ x) = p := by rw [hx]; rfl
    have hxY : (x : X) ∈ Y := by rw [h]; exact x.2
    obtain ⟨hx1, hxU⟩ := (hY x).1 hxY
    rw [← hxp]
    exact hxU

theorem shape_hyps_proof (h : Setup28 W K S) (hR : Red28 W K S) {a : X} (haS : a ∈ S)
    (ha2 : a ^ 2 = 1) {U₁ U₂ : Subgroup X} (hts : TransSection K (vOf W K S) U₁ U₂ a)
    {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    (ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P) (φ : ↥U₁ →* Multiplicative P)
    (hd : SecRepData (Mof K a) U₁ U₂ ρ φ) (hρ : ρ (aM K a) ∉ (K.subgroupOf (Mof K a)).map ρ)
    (hKc : ⁅K, Subgroup.zpowers a⁆ = K) :
    ShapeHyp ρ.range ((K.subgroupOf (Mof K a)).map ρ) ∧ IsF2Transvection (ρ (aM K a)) ∧
      ρ (aM K a) ∈ Subgroup.normalizer
        (((K.subgroupOf (Mof K a)).map ρ : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)) :
          Set (LinearMap.GeneralLinearGroup (ZMod 2) P)) := by
  have htr : IsF2Transvection (ρ (aM K a)) := rho_isF2Transvection hts.asec hd
  refine ⟨?_, htr, rho_aM_mem_normalizer h haS ρ⟩
  haveI := normal_subgroupOf_Mof h haS
  obtain ⟨φ₀, a₀, h0, -, ha₀, -⟩ := (isF2Transvection_iff _).1 htr
  haveI : Nontrivial P := ⟨⟨a₀, 0, ha₀⟩⟩
  haveI : Module.Finite (ZMod 2) P := Module.Finite.of_finite
  refine ⟨Module.finrank_pos, ?_, ?_, Subgroup.map_le_range ρ _, ?_, rho_K_perfect h ρ, ?_⟩
  · have hgen : ∀ T : Subgroup ↥(Mof K a), T.Normal → ρ.ker ≤ T → aM K a ∈ T → T = ⊤ :=
      fun T hT _ haT => by haveI := hT; exact aM_normal_closure ha2 hKc T haT
    refine ⟨_, ?_, range_eq_closure_conj ρ (aM K a) hgen⟩
    rintro _ ⟨g, -, rfl⟩
    exact isF2Transvection_conj htr g
  · exact fun U hU => rho_irred hts.toSingleFactor hd U hU
  · exact relIndex_map_eq_two ρ (K.subgroupOf (Mof K a)) (aM K a) htr
      (by rw [sup_zpowers_aM_eq_top, top_sup_eq]) hρ
  · obtain ⟨k, hk⟩ := rho_nontriv hts.toSingleFactor.toSFBase hd
    intro hbot
    apply hk
    have hmem : (⟨k, Subgroup.mem_sup_left k.2⟩ : ↥(Mof K a)) ∈ K.subgroupOf (Mof K a) :=
      Subgroup.mem_subgroupOf.2 k.2
    have := Subgroup.mem_map_of_mem ρ hmem
    rw [hbot, Subgroup.mem_bot] at this
    exact this

end Sec

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810.CoreAux
