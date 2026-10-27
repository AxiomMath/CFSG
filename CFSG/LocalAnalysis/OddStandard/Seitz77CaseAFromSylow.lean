module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAFromDefs
public import CFSG.LocalAnalysis.OddStandard.Seitz77FusionDefs
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAFromNat
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseAFromCoord
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseACloseGal
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseADefs
public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Inv

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ABGLocalTools CFSG.Open Matrix MatrixGroups

section ActLemmas

theorem conj_eq_iff_mulVec_eq_of_act {G : Type*} [Group G] {Wl : Subgroup G}
    {κ₀ : ↥Wl ≃* Multiplicative (Fin 8 → ZMod 2)}
    {ρ : ↥(normalizer (Wl : Set G)) →* GL (Fin 8) (ZMod 2)}
    (act : ∀ (n : ↥(normalizer (Wl : Set G))) (w w' : ↥Wl), (w' : G) = n * w * n⁻¹ →
      κ₀ w' = Multiplicative.ofAdd
        ((ρ n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (Multiplicative.toAdd (κ₀ w))))
    (n : ↥(normalizer (Wl : Set G))) (w : ↥Wl) :
    (n : G) * w * (n : G)⁻¹ = w ↔
      (ρ n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (Multiplicative.toAdd (κ₀ w)) =
        Multiplicative.toAdd (κ₀ w) := by
  have hconj : (n : G) * w * (n : G)⁻¹ ∈ Wl := (mem_normalizer_iff.mp n.2 (w : G)).mp w.2
  have h := act n w ⟨(n : G) * w * (n : G)⁻¹, hconj⟩ rfl
  constructor
  · intro hw
    have hw' : (⟨(n : G) * w * (n : G)⁻¹, hconj⟩ : ↥Wl) = w := Subtype.ext hw
    rw [hw'] at h
    have h2 := congrArg Multiplicative.toAdd h
    rw [toAdd_ofAdd] at h2
    exact h2.symm
  · intro hv
    rw [hv, ofAdd_toAdd] at h
    exact congrArg Subtype.val (κ₀.injective h)

theorem rho_eq_one_iff_of_act {G : Type*} [Group G] {Wl : Subgroup G}
    {κ₀ : ↥Wl ≃* Multiplicative (Fin 8 → ZMod 2)}
    {ρ : ↥(normalizer (Wl : Set G)) →* GL (Fin 8) (ZMod 2)}
    (act : ∀ (n : ↥(normalizer (Wl : Set G))) (w w' : ↥Wl), (w' : G) = n * w * n⁻¹ →
      κ₀ w' = Multiplicative.ofAdd
        ((ρ n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (Multiplicative.toAdd (κ₀ w))))
    (n : ↥(normalizer (Wl : Set G))) :
    ρ n = 1 ↔ (n : G) ∈ centralizer (Wl : Set G) := by
  have key := conj_eq_iff_mulVec_eq_of_act act n
  constructor
  · intro hρ
    rw [mem_centralizer_iff]
    intro g hg
    have hgW : g ∈ Wl := hg
    have h1 := (key ⟨g, hgW⟩).mpr (by rw [hρ]; simp)
    exact (mul_inv_eq_iff_eq_mul.mp h1).symm
  · intro hc
    rw [mem_centralizer_iff] at hc
    have hfix : ∀ v : Fin 8 → ZMod 2,
        (ρ n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v := by
      intro v
      have hwv : Multiplicative.toAdd (κ₀ (κ₀.symm (Multiplicative.ofAdd v))) = v := by simp
      have hcomm : (n : G) * (κ₀.symm (Multiplicative.ofAdd v) : ↥Wl) *
          (n : G)⁻¹ = (κ₀.symm (Multiplicative.ofAdd v) : ↥Wl) := by
        rw [mul_inv_eq_iff_eq_mul]
        exact (hc _ (κ₀.symm (Multiplicative.ofAdd v)).2).symm
      have := (key _).mp hcomm
      rwa [hwv] at this
    apply Units.ext
    rw [Units.val_one]
    exact Matrix.ext_iff_mulVec.mpr (fun v => by rw [Matrix.one_mulVec]; exact hfix v)

theorem card_centralizer_eq_card_fix_of_act {G : Type*} [Group G] {Wl : Subgroup G}
    {κ₀ : ↥Wl ≃* Multiplicative (Fin 8 → ZMod 2)}
    {ρ : ↥(normalizer (Wl : Set G)) →* GL (Fin 8) (ZMod 2)}
    (act : ∀ (n : ↥(normalizer (Wl : Set G))) (w w' : ↥Wl), (w' : G) = n * w * n⁻¹ →
      κ₀ w' = Multiplicative.ofAdd
        ((ρ n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (Multiplicative.toAdd (κ₀ w))))
    (n : ↥(normalizer (Wl : Set G))) :
    Nat.card ↥(Wl ⊓ centralizer ({(n : G)} : Set G)) =
      Nat.card {v : Fin 8 → ZMod 2 // (ρ n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v} := by
  have key := conj_eq_iff_mulVec_eq_of_act act n
  have hcomm : ∀ w : ↥Wl, (n : G) * w = w * n ↔
      (ρ n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (Multiplicative.toAdd (κ₀ w)) =
        Multiplicative.toAdd (κ₀ w) := fun w => by
    rw [← key w, mul_inv_eq_iff_eq_mul]
  have hto : ∀ w : ↥(Wl ⊓ centralizer ({(n : G)} : Set G)),
      (n : G) * (⟨w.1, (mem_inf.mp w.2).1⟩ : ↥Wl) = (⟨w.1, (mem_inf.mp w.2).1⟩ : ↥Wl) * n :=
    fun w => mem_centralizer_iff.mp (mem_inf.mp w.2).2 (n : G) (Set.mem_singleton _)
  have hinv : ∀ v : {v : Fin 8 → ZMod 2 //
      (ρ n : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = v},
      ((κ₀.symm (Multiplicative.ofAdd v.1) : ↥Wl) : G) ∈
        Wl ⊓ centralizer ({(n : G)} : Set G) := by
    intro v
    refine mem_inf.mpr ⟨(κ₀.symm (Multiplicative.ofAdd v.1)).2, ?_⟩
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hcomm (κ₀.symm (Multiplicative.ofAdd v.1))).mpr (by simpa using v.2)
  refine Nat.card_congr
    { toFun := fun w => ⟨Multiplicative.toAdd (κ₀ ⟨w.1, (mem_inf.mp w.2).1⟩),
        (hcomm ⟨w.1, (mem_inf.mp w.2).1⟩).mp (hto w)⟩
      invFun := fun v => ⟨((κ₀.symm (Multiplicative.ofAdd v.1) : ↥Wl) : G), hinv v⟩
      left_inv := fun w => by
        apply Subtype.ext
        simp
      right_inv := fun v => by
        apply Subtype.ext
        simp }

end ActLemmas

section Coordinates

variable {G : Type*} [Group G] {F : Type*} [Field F]

open Classical in
@[expose] noncomputable def coordFn (Wl : Subgroup G) (κ₀ : ↥Wl ≃* Multiplicative (Fin 8 → ZMod 2))
    (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (w : G) : F × F :=
  if hw : w ∈ Wl then (Φ (Multiplicative.toAdd (κ₀ ⟨w, hw⟩)) 0,
    Φ (Multiplicative.toAdd (κ₀ ⟨w, hw⟩)) 1) else 0

theorem coordFn_apply (Wl : Subgroup G) (κ₀ : ↥Wl ≃* Multiplicative (Fin 8 → ZMod 2))
    (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (w : ↥Wl) :
    coordFn Wl κ₀ Φ (w : G) = Nat16.coord Φ (Multiplicative.toAdd (κ₀ w)) := by
  have hpair : ∀ v : Fin 8 → ZMod 2, Nat16.coord Φ v = (Φ v 0, Φ v 1) := by
    intro v
    apply Nat16.prodEquivFin.injective
    rw [Nat16.coord_apply, Nat16.prodEquivFin_apply]
    ext i
    fin_cases i <;> rfl
  rw [hpair]
  unfold coordFn
  rw [dite_eq_left w.2]

theorem coordFn_add (Wl : Subgroup G) (κ₀ : ↥Wl ≃* Multiplicative (Fin 8 → ZMod 2))
    (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) {w w' : G} (hw : w ∈ Wl) (hw' : w' ∈ Wl) :
    coordFn Wl κ₀ Φ (w * w') = coordFn Wl κ₀ Φ w + coordFn Wl κ₀ Φ w' := by
  have h : coordFn Wl κ₀ Φ (w * w') =
      Nat16.coord Φ (Multiplicative.toAdd (κ₀ (⟨w, hw⟩ * ⟨w', hw'⟩))) :=
    coordFn_apply Wl κ₀ Φ (⟨w, hw⟩ * ⟨w', hw'⟩)
  have h1 : coordFn Wl κ₀ Φ w = Nat16.coord Φ (Multiplicative.toAdd (κ₀ ⟨w, hw⟩)) :=
    coordFn_apply Wl κ₀ Φ ⟨w, hw⟩
  have h2 : coordFn Wl κ₀ Φ w' = Nat16.coord Φ (Multiplicative.toAdd (κ₀ ⟨w', hw'⟩)) :=
    coordFn_apply Wl κ₀ Φ ⟨w', hw'⟩
  rw [h, h1, h2, map_mul, toAdd_mul, map_add]

theorem coordFn_inj (Wl : Subgroup G) (κ₀ : ↥Wl ≃* Multiplicative (Fin 8 → ZMod 2))
    (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) {w w' : G} (hw : w ∈ Wl) (hw' : w' ∈ Wl)
    (h : coordFn Wl κ₀ Φ w = coordFn Wl κ₀ Φ w') : w = w' := by
  have h1 : coordFn Wl κ₀ Φ w = Nat16.coord Φ (Multiplicative.toAdd (κ₀ ⟨w, hw⟩)) :=
    coordFn_apply Wl κ₀ Φ ⟨w, hw⟩
  have h2 : coordFn Wl κ₀ Φ w' = Nat16.coord Φ (Multiplicative.toAdd (κ₀ ⟨w', hw'⟩)) :=
    coordFn_apply Wl κ₀ Φ ⟨w', hw'⟩
  rw [h1, h2] at h
  have h3 : (⟨w, hw⟩ : ↥Wl) = ⟨w', hw'⟩ :=
    κ₀.injective (Multiplicative.toAdd.injective ((Nat16.coord Φ).injective h))
  exact congrArg Subtype.val h3

theorem coordFn_surj (Wl : Subgroup G) (κ₀ : ↥Wl ≃* Multiplicative (Fin 8 → ZMod 2))
    (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (p : F × F) :
    ∃ w ∈ Wl, coordFn Wl κ₀ Φ w = p := by
  refine ⟨(κ₀.symm (Multiplicative.ofAdd ((Nat16.coord Φ).symm p)) : G), SetLike.coe_mem _, ?_⟩
  rw [coordFn_apply]
  simp

theorem coord_eq_pair (Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → F)) (v : Fin 8 → ZMod 2) :
    Nat16.coord Φ v = (Φ v 0, Φ v 1) := by
  apply Nat16.prodEquivFin.injective
  rw [Nat16.coord_apply, Nat16.prodEquivFin_apply]
  ext i
  fin_cases i <;> rfl

end Coordinates

section Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {Wl : Subgroup G}
  {κ₀ : ↥Wl ≃* Multiplicative (Fin 8 → ZMod 2)}
  {ρ : ↥(normalizer (Wl : Set G)) →* GL (Fin 8) (ZMod 2)} {Hgl Xgl : Subgroup (GL (Fin 8) (ZMod 2))}

structure Ctx (I : ModInput d Wl κ₀ ρ Hgl Xgl) where
  S₁N : Subgroup ↥(normalizer (Wl : Set G))
  isSylow : IsSylowOf 2 S₁N ⊤
  D_le : ((d.P ⊓ A) ⊔ zpowers d.t).subgroupOf (normalizer (Wl : Set G)) ≤ S₁N
  W_le : Wl.subgroupOf (normalizer (Wl : Set G)) ≤ S₁N
  rhat : SL(2, GaloisField 2 4) →* GL (Fin 8) (ZMod 2)
  rhat_inj : Function.Injective rhat
  rhat_range : rhat.range = Hgl
  rhat_U : (uPlus (GaloisField 2 4)).map rhat = (S₁N ⊓ Hgl.comap ρ).map ρ
  Φ : (Fin 8 → ZMod 2) ≃+ (Fin 2 → GaloisField 2 4)
  φs : GaloisField 2 4 →+* Module.End (ZMod 2) (Fin 8 → ZMod 2)
  nat : NatStr rhat Φ φs

theorem ModInput.normal_comap (I : ModInput d Wl κ₀ ρ Hgl Xgl) : (Hgl.comap ρ).Normal :=
  ⟨fun y hy n => by
    show ρ (n * y * n⁻¹) ∈ Hgl
    rw [map_mul, map_mul, map_inv]
    exact I.Hgl_norm n _ hy⟩

theorem ModInput.rho_of_mem_Wl (I : ModInput d Wl κ₀ ρ Hgl Xgl) {w : G} (hw : w ∈ Wl) :
    ρ ⟨w, le_normalizer hw⟩ = 1 := by
  rw [rho_eq_one_iff_of_act I.act]
  exact mem_centralizer_iff.mpr fun x hx =>
    congrArg Subtype.val (I.elem.1.is_comm.comm ⟨x, hx⟩ ⟨w, hw⟩)

theorem exists_ctx (I : ModInput d Wl κ₀ ρ Hgl Xgl) : Nonempty (Ctx I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 4) = 16 := Weights16.nat_card_galoisField
  obtain ⟨e⟩ := I.Hgl_iso
  have hDP : (d.P ⊓ A) ⊔ zpowers d.t ≤ d.P :=
    sup_le inf_le_left (zpowers_le.mpr d.t_mem_P)
  have hD2 : IsPGroup 2 (((d.P ⊓ A) ⊔ zpowers d.t).subgroupOf (normalizer (Wl : Set G))) :=
    (d.hP.isPGroup.to_le hDP).comap_subtype
  obtain ⟨Q, hQ⟩ := hD2.exists_le_sylow
  have hQtop : IsSylowOf 2 (Q : Subgroup ↥(normalizer (Wl : Set G))) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  have hYn : (Hgl.comap ρ).Normal := I.normal_comap
  have hS₀N : IsSylowOf 2 ((Q : Subgroup ↥(normalizer (Wl : Set G))) ⊓ Hgl.comap ρ)
      (Hgl.comap ρ) :=
    hQtop.inf_of_le_normalizer le_top (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hYn).symm)
  have hS₀Nφ : IsSylowOf 2 (((Q : Subgroup ↥(normalizer (Wl : Set G))) ⊓ Hgl.comap ρ).map ρ)
      Hgl := by
    have h := IsSylowOf.map_hom ρ hS₀N
    rwa [Subgroup.map_comap_eq, inf_eq_right.mpr I.Hgl_le_range] at h
  obtain ⟨rhat, hrinj, hrrange, hrU⟩ := exists_rhohat_adapted hF e hS₀Nφ
  obtain ⟨y, hy3⟩ := exists_prime_orderOf_dvd_card' (G := ↥Xgl) 3
    (by rw [I.Xgl_card]; norm_num)
  have hyH : (y : GL (Fin 8) (ZMod 2)) ∈ rhat.range := by
    rw [hrrange]
    exact I.Xgl_le y.2
  obtain ⟨x₃, hx₃⟩ := hyH
  have hx₃ord : orderOf x₃ = 3 := by
    rw [← orderOf_injective rhat hrinj x₃, hx₃, Subgroup.orderOf_coe, hy3]
  obtain ⟨Φ, φs, hN⟩ := exists_natStr hF rhat hrinj hx₃ord (fun v hv => by
    rw [hx₃] at hv
    exact I.Xgl_fpf y y.2 (by rw [Subgroup.orderOf_coe, hy3]) v hv)
  have hWp : IsPGroup 2 (Wl.subgroupOf (normalizer (Wl : Set G))) :=
    (IsPGroup.of_card (n := 8) (by rw [I.card])).comap_subtype
  exact ⟨⟨Q, hQtop, hQ, hWp.le_sylow_of_normal Q, rhat, hrinj, hrrange, hrU, Φ, φs, hN⟩⟩

namespace Ctx

variable {I : ModInput d Wl κ₀ ρ Hgl Xgl} (C : Ctx I)

@[expose] def S₁ : Subgroup G := C.S₁N.map (normalizer (Wl : Set G)).subtype

@[expose] def S₀N : Subgroup ↥(normalizer (Wl : Set G)) := C.S₁N ⊓ Hgl.comap ρ

@[expose] def S₀ : Subgroup G := C.S₀N.map (normalizer (Wl : Set G)).subtype

theorem mem_S₁ {x : G} : x ∈ C.S₁ ↔ ∃ h : x ∈ normalizer (Wl : Set G),
    (⟨x, h⟩ : ↥(normalizer (Wl : Set G))) ∈ C.S₁N := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem mem_S₀ {x : G} : x ∈ C.S₀ ↔ ∃ h : x ∈ normalizer (Wl : Set G),
    (⟨x, h⟩ : ↥(normalizer (Wl : Set G))) ∈ C.S₁N ∧ ρ ⟨x, h⟩ ∈ Hgl := by
  constructor
  · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨y.2, hy1, hy2⟩
  · rintro ⟨h, hx1, hx2⟩
    exact ⟨⟨x, h⟩, ⟨hx1, hx2⟩, rfl⟩

theorem S₁_le_N : C.S₁ ≤ normalizer (Wl : Set G) := fun _ hx => ((C.mem_S₁).mp hx).1

theorem S₀_le_S₁ : C.S₀ ≤ C.S₁ := by
  intro x hx
  obtain ⟨h, h1, -⟩ := C.mem_S₀.mp hx
  exact C.mem_S₁.mpr ⟨h, h1⟩

theorem isPGroup_S₁ : IsPGroup 2 C.S₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (C.isSylow.isPGroup).map (normalizer (Wl : Set G)).subtype

theorem isSylowOf_S₁ : IsSylowOf 2 C.S₁ (normalizer (Wl : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (isSylowOf_map_subtype_iff (p := 2) (normalizer (Wl : Set G))).mpr C.isSylow
  rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h

theorem Wl_le_S₁ : Wl ≤ C.S₁ := fun _ hw =>
  C.mem_S₁.mpr ⟨le_normalizer hw, C.W_le (mem_subgroupOf.mpr hw)⟩

theorem W_le_S₀ : Wl ≤ C.S₀ := fun w hw =>
  C.mem_S₀.mpr ⟨le_normalizer hw, C.W_le (mem_subgroupOf.mpr hw), by
    rw [I.rho_of_mem_Wl hw]
    exact Hgl.one_mem⟩

theorem V_le_S₀ : d.P ⊓ A ≤ C.S₀ := fun v hv =>
  C.mem_S₀.mpr ⟨I.V_le hv, C.D_le (mem_subgroupOf.mpr (mem_sup_left hv)), I.V_mem v hv⟩

theorem t_mem_S₁ : d.t ∈ C.S₁ :=
  C.mem_S₁.mpr ⟨I.t_mem, C.D_le (mem_subgroupOf.mpr (mem_sup_right (mem_zpowers d.t)))⟩

theorem S₀_normal : ∀ s ∈ C.S₁, ∀ x ∈ C.S₀, s * x * s⁻¹ ∈ C.S₀ := by
  intro s hs x hx
  obtain ⟨hsN, hs1⟩ := C.mem_S₁.mp hs
  obtain ⟨hxN, hx1, hx2⟩ := C.mem_S₀.mp hx
  have hconj : s * x * s⁻¹ ∈ normalizer (Wl : Set G) :=
    mul_mem (mul_mem hsN hxN) (inv_mem hsN)
  refine C.mem_S₀.mpr ⟨hconj, ?_, ?_⟩
  · have : (⟨s * x * s⁻¹, hconj⟩ : ↥(normalizer (Wl : Set G))) = ⟨s, hsN⟩ * ⟨x, hxN⟩ * ⟨s, hsN⟩⁻¹ :=
      rfl
    rw [this]
    exact mul_mem (mul_mem hs1 hx1) (inv_mem hs1)
  · have hn := I.normal_comap
    have h1 : (⟨s * x * s⁻¹, hconj⟩ : ↥(normalizer (Wl : Set G))) =
        ⟨s, hsN⟩ * ⟨x, hxN⟩ * ⟨s, hsN⟩⁻¹ := rfl
    rw [h1]
    exact hn.conj_mem _ hx2 _

end Ctx

open Classical in
@[expose] noncomputable def kapGL (rhat : SL(2, GaloisField 2 4) →* GL (Fin 8) (ZMod 2))
    (n : GL (Fin 8) (ZMod 2)) : GaloisField 2 4 :=
  if h : ∃ c, rhat (Nat16.uE c) = n then Classical.choose h else 0

theorem kapGL_eq {rhat : SL(2, GaloisField 2 4) →* GL (Fin 8) (ZMod 2)}
    (hinj : Function.Injective rhat) {c : GaloisField 2 4} {n : GL (Fin 8) (ZMod 2)}
    (h : rhat (Nat16.uE c) = n) : kapGL rhat n = c := by
  have h' : ∃ c, rhat (Nat16.uE c) = n := ⟨c, h⟩
  have h1 : kapGL rhat n = Classical.choose h' := by
    unfold kapGL
    simp only [h', ↓reduceDIte]
  rw [h1]
  exact Nat16.uE_injective (hinj ((Classical.choose_spec h').trans h.symm))

namespace Ctx

variable {I : ModInput d Wl κ₀ ρ Hgl Xgl} (C : Ctx I)

open Classical in
@[expose] noncomputable def kap (x : G) : GaloisField 2 4 :=
  if hx : x ∈ normalizer (Wl : Set G) then kapGL C.rhat (ρ ⟨x, hx⟩) else 0

open Classical in
@[expose] noncomputable def phi (x : G) : RingAut (GaloisField 2 4) :=
  if hx : x ∈ normalizer (Wl : Set G) then semiAut C.φs (ρ ⟨x, hx⟩) else 1

@[expose] noncomputable def iota : G → GaloisField 2 4 × GaloisField 2 4 :=
  coordFn Wl κ₀ C.Φ

theorem kap_eq {s : G} (hs : s ∈ normalizer (Wl : Set G)) {c : GaloisField 2 4}
    (h : ρ ⟨s, hs⟩ = C.rhat (Nat16.uE c)) : C.kap s = c := by
  unfold kap
  simp only [hs, ↓reduceDIte]
  exact kapGL_eq C.rhat_inj h.symm

theorem exists_uE {s : G} (hs : s ∈ C.S₀) :
    ∃ (c : GaloisField 2 4) (hsN : s ∈ normalizer (Wl : Set G)),
      ρ ⟨s, hsN⟩ = C.rhat (Nat16.uE c) := by
  obtain ⟨hsN, hs1, hs2⟩ := C.mem_S₀.mp hs
  have hmem : ρ ⟨s, hsN⟩ ∈ (C.S₁N ⊓ Hgl.comap ρ).map ρ := ⟨⟨s, hsN⟩, ⟨hs1, hs2⟩, rfl⟩
  rw [← C.rhat_U] at hmem
  obtain ⟨g, ⟨c, rfl⟩, hg⟩ := hmem
  exact ⟨c, hsN, hg.symm⟩

theorem kap_add {s s' : G} (hs : s ∈ C.S₀) (hs' : s' ∈ C.S₀) :
    C.kap (s * s') = C.kap s + C.kap s' := by
  obtain ⟨c, hsN, hc⟩ := C.exists_uE hs
  obtain ⟨c', hsN', hc'⟩ := C.exists_uE hs'
  have h1 := C.kap_eq hsN hc
  have h2 := C.kap_eq hsN' hc'
  have h3 : C.kap (s * s') = c + c' := by
    refine C.kap_eq (mul_mem hsN hsN') ?_
    have : (⟨s * s', mul_mem hsN hsN'⟩ : ↥(normalizer (Wl : Set G))) = ⟨s, hsN⟩ * ⟨s', hsN'⟩ := rfl
    rw [this, map_mul, hc, hc', ← map_mul, ← Nat16.uE_add]
  rw [h3, h1, h2]

theorem kap_surj (b : GaloisField 2 4) : ∃ s ∈ C.S₀, C.kap s = b := by
  have hmem : C.rhat (Nat16.uE b) ∈ (C.S₁N ⊓ Hgl.comap ρ).map ρ := by
    rw [← C.rhat_U]
    exact ⟨Nat16.uE b, uE_mem_uPlus b, rfl⟩
  obtain ⟨y, hy, hyb⟩ := hmem
  refine ⟨(y : G), C.mem_S₀.mpr ⟨y.2, hy.1, hy.2⟩, C.kap_eq y.2 hyb⟩

theorem kap_eq_zero_iff {s : G} (hs : s ∈ C.S₀) : C.kap s = 0 ↔ s ∈ Wl := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hsN, hc⟩ := C.exists_uE hs
  have h1 := C.kap_eq hsN hc
  constructor
  · intro h0
    rw [h1] at h0
    rw [h0, Nat16.uE_zero, map_one] at hc
    have hcent : s ∈ centralizer (Wl : Set G) := (rho_eq_one_iff_of_act I.act ⟨s, hsN⟩).mp hc
    have hs1 : s ∈ C.S₁ := C.S₀_le_S₁ hs
    have hle : Wl ⊔ zpowers s ≤ C.S₁ := sup_le C.Wl_le_S₁ (zpowers_le.mpr hs1)
    have hWC : Wl ≤ centralizer (Wl : Set G) := fun x hx =>
      mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (I.elem.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
    have hQC : Wl ⊔ zpowers s ≤ centralizer (Wl : Set G) :=
      sup_le hWC (zpowers_le.mpr hcent)
    have heq := I.sylow_C.eq_of_le (le_sup_left : Wl ≤ Wl ⊔ zpowers s) hQC
      (C.isPGroup_S₁.to_le hle)
    rw [← heq]
    exact mem_sup_right (mem_zpowers s)
  · intro hsW
    exact C.kap_eq hsN (by rw [Nat16.uE_zero, map_one]; exact I.rho_of_mem_Wl hsW)

theorem iota_conj {s w : G} (hs : s ∈ C.S₀) (hw : w ∈ Wl) :
    C.iota (s * w * s⁻¹) = ((C.iota w).1 + C.kap s * (C.iota w).2, (C.iota w).2) := by
  obtain ⟨c, hsN, hc⟩ := C.exists_uE hs
  have hk := C.kap_eq hsN hc
  have hw' : s * w * s⁻¹ ∈ Wl := (mem_normalizer_iff.mp hsN w).mp hw
  have hact := I.act ⟨s, hsN⟩ ⟨w, hw⟩ ⟨s * w * s⁻¹, hw'⟩ rfl
  have key : ∀ w' : ↥Wl, C.iota (w' : G) = Nat16.coord C.Φ (Multiplicative.toAdd (κ₀ w')) :=
    fun w' => coordFn_apply Wl κ₀ C.Φ w'
  have e1 : C.iota (s * w * s⁻¹) =
      Nat16.coord C.Φ (Multiplicative.toAdd (κ₀ ⟨s * w * s⁻¹, hw'⟩)) := key ⟨s * w * s⁻¹, hw'⟩
  have e2 : C.iota w = Nat16.coord C.Φ (Multiplicative.toAdd (κ₀ ⟨w, hw⟩)) := key ⟨w, hw⟩
  rw [e1, e2, hact, toAdd_ofAdd, hc, coord_eq_pair, coord_eq_pair, C.nat.uE, hk]
  simp

theorem transvData : TransvData Wl C.S₀ C.iota C.kap where
  W_le_S₀ := C.W_le_S₀
  S₀_norm_W := fun _ hs w hw => (mem_normalizer_iff.mp (C.S₁_le_N (C.S₀_le_S₁ hs)) w).mp hw
  ι_add := fun _ hw _ hw' => coordFn_add Wl κ₀ C.Φ hw hw'
  ι_inj := fun _ hw _ hw' h => coordFn_inj Wl κ₀ C.Φ hw hw' h
  ι_surj := fun p => coordFn_surj Wl κ₀ C.Φ p
  κ_add := fun _ hs _ hs' => C.kap_add hs hs'
  κ_eq_zero_iff := fun _ hs => C.kap_eq_zero_iff hs
  κ_surj := C.kap_surj
  conj_ι := fun _ hs _ hw => C.iota_conj hs hw

end Ctx

namespace Ctx

variable {I : ModInput d Wl κ₀ ρ Hgl Xgl} (C : Ctx I)

theorem mem_Hgl_iff {n : GL (Fin 8) (ZMod 2)} : n ∈ Hgl ↔ ∃ g, C.rhat g = n :=
  (SetLike.ext_iff.mp C.rhat_range n).symm

theorem normalizes {x : G} (hx : x ∈ normalizer (Wl : Set G)) (g : SL(2, GaloisField 2 4)) :
    ∃ g' : SL(2, GaloisField 2 4), ρ ⟨x, hx⟩ * C.rhat g * (ρ ⟨x, hx⟩)⁻¹ = C.rhat g' := by
  have h1 : C.rhat g ∈ Hgl := C.mem_Hgl_iff.mpr ⟨g, rfl⟩
  obtain ⟨g', hg'⟩ := C.mem_Hgl_iff.mp (I.Hgl_norm ⟨x, hx⟩ _ h1)
  exact ⟨g', hg'.symm⟩

theorem exists_semiLin {x : G} (hx : x ∈ normalizer (Wl : Set G)) :
    ∃ j : ℕ, j < 4 ∧ SemiLin C.φs (ρ ⟨x, hx⟩) (frobPow (GaloisField 2 4) j) :=
  C.nat.exists_semiLin (C.normalizes hx)

theorem phi_apply {x : G} (hx : x ∈ normalizer (Wl : Set G)) :
    C.phi x = semiAut C.φs (ρ ⟨x, hx⟩) := by
  unfold phi
  simp only [hx, ↓reduceDIte]

theorem semiLin_phi {x : G} (hx : x ∈ normalizer (Wl : Set G)) :
    SemiLin C.φs (ρ ⟨x, hx⟩) (C.phi x) := by
  rw [C.phi_apply hx]
  obtain ⟨j, -, hj⟩ := C.exists_semiLin hx
  exact semiLin_semiAut ⟨_, hj⟩

theorem phi_eq_frobPow {x : G} (hx : x ∈ normalizer (Wl : Set G)) :
    ∃ j : ℕ, j < 4 ∧ C.phi x = frobPow (GaloisField 2 4) j ∧
      SemiLin C.φs (ρ ⟨x, hx⟩) (frobPow (GaloisField 2 4) j) := by
  obtain ⟨j, hj4, hj⟩ := C.exists_semiLin hx
  exact ⟨j, hj4, by rw [C.phi_apply hx]; exact semiAut_eq hj, hj⟩

theorem phi_one : C.phi 1 = 1 := by
  have h1 : (1 : G) ∈ normalizer (Wl : Set G) := one_mem _
  rw [C.phi_apply h1]
  refine semiAut_eq ?_
  have : ρ ⟨1, h1⟩ = 1 := map_one ρ
  rw [this]
  exact SemiLin.one

theorem phi_mul {x y : G} (hx : x ∈ normalizer (Wl : Set G)) (hy : y ∈ normalizer (Wl : Set G)) :
    C.phi (x * y) = C.phi x * C.phi y := by
  have hxy : x * y ∈ normalizer (Wl : Set G) := mul_mem hx hy
  have h1 : (⟨x * y, hxy⟩ : ↥(normalizer (Wl : Set G))) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [C.phi_apply hxy, h1, map_mul]
  have hx' := C.semiLin_phi hx
  have hy' := C.semiLin_phi hy
  rw [semiAut_mul hx' hy', ← C.phi_apply hx, ← C.phi_apply hy]

theorem phi_mul_S₁ {x y : G} (hx : x ∈ C.S₁) (hy : y ∈ C.S₁) :
    C.phi (x * y) = C.phi x * C.phi y :=
  C.phi_mul (C.S₁_le_N hx) (C.S₁_le_N hy)

theorem phi_eq_one_iff {x : G} (hx : x ∈ C.S₁) : C.phi x = 1 ↔ x ∈ C.S₀ := by
  obtain ⟨hxN, hx1⟩ := C.mem_S₁.mp hx
  constructor
  · intro h1
    have hsl := C.semiLin_phi hxN
    rw [h1] at hsl
    obtain ⟨k, hk⟩ := C.isSylow.isPGroup ⟨⟨x, hxN⟩, hx1⟩
    have hk' : (⟨x, hxN⟩ : ↥(normalizer (Wl : Set G))) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hρk : (ρ ⟨x, hxN⟩) ^ 2 ^ k = 1 := by rw [← map_pow, hk', map_one]
    obtain ⟨g, hg⟩ := C.nat.two_elt (ρ ⟨x, hxN⟩) hsl ⟨k, hρk⟩
    exact C.mem_S₀.mpr ⟨hxN, hx1, C.mem_Hgl_iff.mpr ⟨g, hg⟩⟩
  · intro hx0
    obtain ⟨hxN', -, hx2⟩ := C.mem_S₀.mp hx0
    obtain ⟨g, hg⟩ := C.mem_Hgl_iff.mp hx2
    have hg' : ρ ⟨x, hxN⟩ = C.rhat g := hg.symm
    rw [C.phi_apply hxN]
    refine semiAut_eq ?_
    intro a v
    rw [hg']
    exact C.nat.comm g a v

end Ctx

namespace Ctx

variable {I : ModInput d Wl κ₀ ρ Hgl Xgl} (C : Ctx I)

theorem exists_uE_of_mem_map {n : GL (Fin 8) (ZMod 2)}
    (hn : n ∈ (C.S₁N ⊓ Hgl.comap ρ).map ρ) : ∃ c, C.rhat (Nat16.uE c) = n := by
  rw [← C.rhat_U] at hn
  obtain ⟨g, ⟨c, rfl⟩, hg⟩ := hn
  exact ⟨c, hg⟩

theorem normalizes_U {x : G} (hx : x ∈ C.S₁) (c : GaloisField 2 4) :
    ∃ c' : GaloisField 2 4, ρ ⟨x, C.S₁_le_N hx⟩ * C.rhat (Nat16.uE c) *
      (ρ ⟨x, C.S₁_le_N hx⟩)⁻¹ = C.rhat (Nat16.uE c') := by
  obtain ⟨hxN, hx1⟩ := C.mem_S₁.mp hx
  have hmem : C.rhat (Nat16.uE c) ∈ (C.S₁N ⊓ Hgl.comap ρ).map ρ := by
    rw [← C.rhat_U]
    exact ⟨Nat16.uE c, uE_mem_uPlus c, rfl⟩
  obtain ⟨y, ⟨hy1, hy2⟩, hy⟩ := hmem
  have hy3 : (⟨x, hxN⟩ : ↥(normalizer (Wl : Set G))) * y * ⟨x, hxN⟩⁻¹ ∈
      C.S₁N ⊓ Hgl.comap ρ :=
    ⟨C.S₁N.mul_mem (C.S₁N.mul_mem hx1 hy1) (C.S₁N.inv_mem hx1),
      I.normal_comap.conj_mem _ hy2 _⟩
  obtain ⟨c', hc'⟩ := C.exists_uE_of_mem_map (⟨_, hy3, rfl⟩ :
    ρ (⟨x, hxN⟩ * y * ⟨x, hxN⟩⁻¹) ∈ (C.S₁N ⊓ Hgl.comap ρ).map ρ)
  refine ⟨c', ?_⟩
  rw [hc', map_mul, map_mul, map_inv, hy]

theorem conj_kap {x : G} (hx : x ∈ C.S₁) :
    ∃ l : GaloisField 2 4, l ≠ 0 ∧ ∀ s ∈ C.S₀, C.kap (x * s * x⁻¹) = l * C.phi x (C.kap s) := by
  obtain ⟨hxN, hx1⟩ := C.mem_S₁.mp hx
  obtain ⟨j, hj4, hphi, hsl⟩ := C.phi_eq_frobPow hxN
  have hsemi := hsl.isSemilinear C.nat.smul
  obtain ⟨p, s', t', hp, ht, -, hact⟩ :=
    Nat16.borel_normalizer_form C.nat.nat (ρ ⟨x, hxN⟩) (C.normalizes_U hx) hsemi
  refine ⟨p / t', div_ne_zero hp ht, fun s hs => ?_⟩
  obtain ⟨c, hsN, hc⟩ := C.exists_uE hs
  have hk := C.kap_eq hsN hc
  have hxs : x * s * x⁻¹ ∈ C.S₀ := C.S₀_normal x hx s hs
  have hxsN : x * s * x⁻¹ ∈ normalizer (Wl : Set G) := C.S₁_le_N (C.S₀_le_S₁ hxs)
  rw [hphi, frobPow_apply, hk]
  refine C.kap_eq hxsN ?_
  have h1 : (⟨x * s * x⁻¹, hxsN⟩ : ↥(normalizer (Wl : Set G))) =
      ⟨x, hxN⟩ * ⟨s, hsN⟩ * ⟨x, hxN⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv, hc]
  exact hact c

theorem card_fix_le_of_not_mem {s : G} (hs : s ∈ C.S₁) (hs0 : s ∉ C.S₀) :
    Nat.card ↥(Wl ⊓ centralizer ({s} : Set G)) ≤ 16 := by
  obtain ⟨hsN, hs1⟩ := C.mem_S₁.mp hs
  obtain ⟨j, hj4, hphi, hsl⟩ := C.phi_eq_frobPow hsN
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · exfalso
      apply hs0
      rw [← C.phi_eq_one_iff hs, hphi, h, frobPow_zero]
    · exact h
  have hbound := Nat16.card_fix_le (Weights16.nat_card_galoisField) C.nat.nat (ρ ⟨s, hsN⟩)
    (C.normalizes_U hs) (hsl.isSemilinear C.nat.smul) hj0 hj4
  rw [card_centralizer_eq_card_fix_of_act I.act ⟨s, hsN⟩]
  exact hbound

theorem t_not_mem_S₀ : d.t ∉ C.S₀ := by
  intro ht0
  have hF : Nat.card (GaloisField 2 4) = 16 := Weights16.nat_card_galoisField
  obtain ⟨htN, -, hρt⟩ := C.mem_S₀.mp ht0
  obtain ⟨g, hg⟩ := C.mem_Hgl_iff.mp hρt
  have hρt' : ρ ⟨d.t, I.t_mem⟩ = C.rhat g := hg.symm
  have hg2 : g * g = 1 := by
    apply C.rhat_inj
    rw [map_mul, ← hρt', ← map_mul, map_one]
    have : (⟨d.t, I.t_mem⟩ : ↥(normalizer (Wl : Set G))) * ⟨d.t, I.t_mem⟩ = 1 :=
      Subtype.ext d.t_mul_self
    rw [this, map_one]
  have hg1 : g ≠ 1 := by
    intro h1
    apply I.t_ne
    rw [hρt', h1, map_one]
  have hcard := Nat16.card_centralizer_involution hF g hg1 hg2
  set Xs : Subgroup SL(2, GaloisField 2 4) := Xgl.comap C.rhat with hXs
  have hXsmap : Xs.map C.rhat = Xgl := by
    rw [hXs, Subgroup.map_comap_eq]
    refine inf_eq_right.mpr ?_
    intro y hy
    exact (C.mem_Hgl_iff).mp (I.Xgl_le hy) |>.elim fun g' hg' => ⟨g', hg'⟩
  have hXscard : Nat.card Xs = 60 := by
    rw [← I.Xgl_card, ← hXsmap, Subgroup.card_map_of_injective C.rhat_inj]
  have hle : Xs ≤ centralizer ({g} : Set SL(2, GaloisField 2 4)) := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    apply C.rhat_inj
    have h1 := I.t_comm (C.rhat y) hy
    rw [hρt'] at h1
    rw [map_mul, map_mul]
    exact h1
  have := Subgroup.card_le_of_le hle
  rw [hXscard, hcard] at this
  omega

end Ctx

namespace Ctx

variable {I : ModInput d Wl κ₀ ρ Hgl Xgl} (C : Ctx I)

theorem phi_t : C.phi d.t = frobPow (GaloisField 2 4) 2 := by
  have hF : Nat.card (GaloisField 2 4) = 16 := Weights16.nat_card_galoisField
  have ht1 : C.phi d.t ≠ 1 := fun h => C.t_not_mem_S₀ ((C.phi_eq_one_iff C.t_mem_S₁).mp h)
  have hsq : C.phi d.t * C.phi d.t = 1 := by
    rw [← C.phi_mul_S₁ C.t_mem_S₁ C.t_mem_S₁, d.t_mul_self, C.phi_one]
  exact ringAut_eq_of_sq_eq_one hF hsq (frobPow_two_mul_self hF) ht1 (frobPow_two_ne_one hF)

theorem iota_conj_N {n : G} (hn : n ∈ normalizer (Wl : Set G)) {w : G} (hw : w ∈ Wl) :
    C.iota (n * w * n⁻¹) = Nat16.coord C.Φ
      ((ρ ⟨n, hn⟩ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec
        (Multiplicative.toAdd (κ₀ ⟨w, hw⟩))) := by
  have hw' : n * w * n⁻¹ ∈ Wl := (mem_normalizer_iff.mp hn w).mp hw
  have hact := I.act ⟨n, hn⟩ ⟨w, hw⟩ ⟨n * w * n⁻¹, hw'⟩ rfl
  have key : ∀ w' : ↥Wl, C.iota (w' : G) = Nat16.coord C.Φ (Multiplicative.toAdd (κ₀ w')) :=
    fun w' => coordFn_apply Wl κ₀ C.Φ w'
  have e1 : C.iota (n * w * n⁻¹) =
      Nat16.coord C.Φ (Multiplicative.toAdd (κ₀ ⟨n * w * n⁻¹, hw'⟩)) := key ⟨n * w * n⁻¹, hw'⟩
  rw [e1, hact, toAdd_ofAdd]

theorem iota_eq {w : G} (hw : w ∈ Wl) :
    C.iota w = Nat16.coord C.Φ (Multiplicative.toAdd (κ₀ ⟨w, hw⟩)) :=
  coordFn_apply Wl κ₀ C.Φ ⟨w, hw⟩

theorem freeSeries : FreeSeries (MulAut.conj d.t) C.S₀ := by
  have hF : Nat.card (GaloisField 2 4) = 16 := Weights16.nat_card_galoisField
  have htN : d.t ∈ normalizer (Wl : Set G) := I.t_mem
  have hsl : SemiLin C.φs (ρ ⟨d.t, htN⟩) (frobPow (GaloisField 2 4) 2) := by
    have := C.semiLin_phi htN
    rwa [C.phi_t] at this
  have hsemi := hsl.isSemilinear C.nat.smul
  have hn2 : ρ ⟨d.t, htN⟩ * ρ ⟨d.t, htN⟩ = 1 := by
    rw [← map_mul]
    have : (⟨d.t, htN⟩ : ↥(normalizer (Wl : Set G))) * ⟨d.t, htN⟩ = 1 :=
      Subtype.ext d.t_mul_self
    rw [this, map_one]
  obtain ⟨p, s', t', hp, ht', hform, hact, hpp, htt⟩ :=
    Nat16.borel_involution_mu C.nat.nat (ρ ⟨d.t, htN⟩) (C.normalizes_U C.t_mem_S₁) hsemi hn2
  have hl : (p / t') * (p / t') ^ 4 = 1 := by
    have : p / t' * (p / t') ^ 4 = (p * p ^ 4) / (t' * t' ^ 4) := by
      field_simp
    rw [this, hpp, htt, div_one]
  refine C.transvData.freeSeries (t := d.t) (p := p) (s' := s') (t' := t') (l := p / t')
    Weights16.nat_card_galoisField (fun s hs => C.S₀_normal d.t C.t_mem_S₁ s hs)
    (fun w hw => (mem_normalizer_iff.mp htN w).mp hw) hpp htt hl ?_ ?_
  · intro w hw
    rw [C.iota_conj_N htN hw, C.iota_eq hw, ← Nat16.coordMap_apply]
    have h1 := hform (Nat16.coord C.Φ (Multiplicative.toAdd (κ₀ ⟨w, hw⟩))).1
      (Nat16.coord C.Φ (Multiplicative.toAdd (κ₀ ⟨w, hw⟩))).2
    rw [h1]
    norm_num
  · intro s hs
    obtain ⟨c, hsN, hc⟩ := C.exists_uE hs
    have hk := C.kap_eq hsN hc
    have hts : d.t * s * d.t⁻¹ ∈ C.S₀ := C.S₀_normal d.t C.t_mem_S₁ s hs
    have htsN : d.t * s * d.t⁻¹ ∈ normalizer (Wl : Set G) := C.S₁_le_N (C.S₀_le_S₁ hts)
    rw [hk]
    refine C.kap_eq htsN ?_
    have h1 : (⟨d.t * s * d.t⁻¹, htsN⟩ : ↥(normalizer (Wl : Set G))) =
        ⟨d.t, htN⟩ * ⟨s, hsN⟩ * ⟨d.t, htN⟩⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv, hc, hact c]
    norm_num

end Ctx

section Torus

variable {F : Type*} [Field F]

theorem uE_mul_tE_apply (c a : F) (ha : a ≠ 0) :
    ((Nat16.uE c * Nat16.tE a ha : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![a, c * a⁻¹; 0, a⁻¹] := by
  rw [Nat16.sl_coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Nat16.uE, Nat16.tE, Matrix.mul_apply]

theorem tE_conj_uE (e a : F) (ha : a ≠ 0) :
    Nat16.tE a ha * Nat16.uE e * (Nat16.tE a ha)⁻¹ = Nat16.uE (a * a * e) := by
  rw [mul_inv_eq_iff_eq_mul, Nat16.tE_mul_uE]

theorem torus_conj (c e a : F) (ha : a ≠ 0) :
    (Nat16.uE c * Nat16.tE a ha) * Nat16.uE e * (Nat16.uE c * Nat16.tE a ha)⁻¹ =
      Nat16.uE (a * a * e) := by
  rw [mul_inv_eq_iff_eq_mul, mul_assoc (Nat16.uE c) (Nat16.tE a ha) (Nat16.uE e),
    Nat16.tE_mul_uE, ← mul_assoc, ← mul_assoc, ← Nat16.uE_add, ← Nat16.uE_add, add_comm]

theorem uE_inv (c : F) : (Nat16.uE c)⁻¹ = Nat16.uE (-c) := by
  rw [inv_eq_iff_mul_eq_one, ← Nat16.uE_add, add_neg_cancel, Nat16.uE_zero]

end Torus

namespace Ctx

variable {I : ModInput d Wl κ₀ ρ Hgl Xgl} (C : Ctx I)

theorem isSylowOf_S₀N : IsSylowOf 2 C.S₀N (Hgl.comap ρ) :=
  C.isSylow.inf_of_le_normalizer le_top
    (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr I.normal_comap).symm)

theorem exists_torus (a : GaloisField 2 4) (ha : a ≠ 0) :
    ∃ n : ↥(normalizer (Wl : Set G)), (∀ y, y ∈ C.S₀N ↔ n * y * n⁻¹ ∈ C.S₀N) ∧
      ∃ c : GaloisField 2 4, ρ n = C.rhat (Nat16.uE c * Nat16.tE a ha) := by
  have hmem : C.rhat (Nat16.tE a ha) ∈ Hgl := C.mem_Hgl_iff.mpr ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := I.Hgl_le_range hmem
  have hS : IsSylowOf 2 C.S₀N ((C.S₀N.map ρ).comap ρ) := by
    refine C.isSylowOf_S₀N.of_le (Subgroup.le_comap_map _ _) ?_
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hx
    show ρ x ∈ Hgl
    rw [← hyx]
    exact hy.2
  have hU : C.S₀N.map ρ = (uPlus (GaloisField 2 4)).map C.rhat := C.rhat_U.symm
  have hmN : ∀ z ∈ C.S₀N.map ρ, ρ m * z * (ρ m)⁻¹ ∈ C.S₀N.map ρ := by
    intro z hz
    rw [hU] at hz ⊢
    obtain ⟨g, ⟨e, rfl⟩, rfl⟩ := hz
    refine ⟨Nat16.uE (a * a * e), uE_mem_uPlus _, ?_⟩
    rw [hm, ← map_inv, ← map_mul, ← map_mul, tE_conj_uE]
  obtain ⟨k, hk, hkn⟩ := exists_mem_normalizer_of_sylow_comap ρ hS hmN
  have hk' : ρ k ∈ (uPlus (GaloisField 2 4)).map C.rhat := by
    rw [← hU]
    exact hk
  obtain ⟨g, ⟨c₀, rfl⟩, hg⟩ := hk'
  refine ⟨k⁻¹ * m, fun y => Subgroup.mem_normalizer_iff.mp hkn y, -c₀, ?_⟩
  rw [map_mul, map_inv, ← hg, hm, ← map_inv, ← map_mul, uE_inv]

end Ctx

namespace Ctx

variable {I : ModInput d Wl κ₀ ρ Hgl Xgl} (C : Ctx I)

theorem iota_torus {n : G} (hn : n ∈ normalizer (Wl : Set G)) {c a : GaloisField 2 4}
    (ha : a ≠ 0) (hρ : ρ ⟨n, hn⟩ = C.rhat (Nat16.uE c * Nat16.tE a ha)) {w : G} (hw : w ∈ Wl) :
    C.iota (n * w * n⁻¹) = (a * (C.iota w).1 + (c * a⁻¹) * (C.iota w).2, a⁻¹ * (C.iota w).2) := by
  rw [C.iota_conj_N hn hw, C.iota_eq hw, hρ, coord_eq_pair, coord_eq_pair, C.nat.nat,
    uE_mul_tE_apply]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem kap_torus {n : G} (hn : n ∈ normalizer (Wl : Set G)) {c a : GaloisField 2 4}
    (ha : a ≠ 0) (hρ : ρ ⟨n, hn⟩ = C.rhat (Nat16.uE c * Nat16.tE a ha)) {s : G}
    (hs : s ∈ C.S₀) (hnS : n * s * n⁻¹ ∈ C.S₀) : C.kap (n * s * n⁻¹) = a ^ 2 * C.kap s := by
  obtain ⟨e, hsN, he⟩ := C.exists_uE hs
  have hk := C.kap_eq hsN he
  rw [hk, sq]
  refine C.kap_eq (C.S₁_le_N (C.S₀_le_S₁ hnS)) ?_
  have h1 : (⟨n * s * n⁻¹, C.S₁_le_N (C.S₀_le_S₁ hnS)⟩ : ↥(normalizer (Wl : Set G))) =
      ⟨n, hn⟩ * ⟨s, hsN⟩ * ⟨n, hn⟩⁻¹ := rfl
  rw [h1, map_mul, map_mul, map_inv, hρ, he, ← map_inv, ← map_mul, ← map_mul, torus_conj]

theorem comm_mem_W₀ :
    ∀ s ∈ C.S₀, ∀ s' ∈ C.S₀, s * s' * s⁻¹ * s'⁻¹ ∈ Wl ⊓ centralizer (C.S₀ : Set G) := by
  have hF : Nat.card (GaloisField 2 4) = 16 := Weights16.nat_card_galoisField
  obtain ⟨z, hz⟩ := Weights16.exists_pow_four_eq hF
  have hord : orderOf z = 15 := Weights16.orderOf_eq_fifteen_of_pow_four hF hz
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hord
    simp at hord
  obtain ⟨n, hnS₀N, c, hc⟩ := C.exists_torus z hz0
  have hnS : ∀ s ∈ C.S₀, (n : G) * s * (n : G)⁻¹ ∈ C.S₀ := by
    intro s hs
    obtain ⟨hsN, hs1, hs2⟩ := C.mem_S₀.mp hs
    have h1 : (⟨s, hsN⟩ : ↥(normalizer (Wl : Set G))) ∈ C.S₀N := ⟨hs1, hs2⟩
    obtain ⟨h31, h32⟩ := (hnS₀N _).mp h1
    exact C.mem_S₀.mpr ⟨mul_mem (mul_mem n.2 hsN) (inv_mem n.2), h31, h32⟩
  exact C.transvData.comm_mem_W₀_of_torus hF hnS hord
    (fun w hw => C.iota_torus n.2 hz0 hc hw) (fun s hs => C.kap_torus n.2 hz0 hc hs (hnS s hs))

end Ctx

theorem exists_sylowA_of_module (I : ModInput d Wl κ₀ ρ Hgl Xgl) :
    ∃ (S₁ S₀ W₀ : Subgroup G) (ι : G → GaloisField 2 4 × GaloisField 2 4)
      (κ : G → GaloisField 2 4) (φ : G → RingAut (GaloisField 2 4)),
      SylowA d Wl S₁ S₀ W₀ ι κ φ := by
  obtain ⟨C⟩ := exists_ctx I
  have T := C.transvData
  exact ⟨C.S₁, C.S₀, Wl ⊓ centralizer (C.S₀ : Set G), C.iota, C.kap, C.phi,
    { card_F := Weights16.nat_card_galoisField
      sylow_S₁ := C.isSylowOf_S₁
      S₀_le_S₁ := C.S₀_le_S₁
      S₀_normal := C.S₀_normal
      W_le_S₀ := C.W_le_S₀
      V_le_S₀ := C.V_le_S₀
      t_mem_S₁ := C.t_mem_S₁
      t_not_mem_S₀ := C.t_not_mem_S₀
      ι_add := T.ι_add
      ι_inj := T.ι_inj
      ι_surj := T.ι_surj
      κ_add := T.κ_add
      κ_eq_zero_iff := T.κ_eq_zero_iff
      κ_surj := T.κ_surj
      conj_ι := T.conj_ι
      φ_mul := fun _ hx _ hy => C.phi_mul_S₁ hx hy
      φ_eq_one_iff := fun _ hx => C.phi_eq_one_iff hx
      conj_κ := fun _ hx => C.conj_kap hx
      W₀_eq := rfl
      comm_mem_W₀ := C.comm_mem_W₀
      card_fix_le := fun _ hs hs0 => C.card_fix_le_of_not_mem hs hs0
      free := C.freeSeries }⟩

end Ctx

end CFSG.OddStandard.Seitz77
