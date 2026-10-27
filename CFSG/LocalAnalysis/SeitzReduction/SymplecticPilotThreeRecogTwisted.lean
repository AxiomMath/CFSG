module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthCoordBlock
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotThreeRecogEdge

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.QuasithinUnique.Lin2.Five (tauSp)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear blockDiagSL
  mem_blockDiagSL)
open CFSG.SeitzReduction.F4Pilot (statedSpMap centralizerPerfectCore
  centralizerPerfectCore_le_centralizer)
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG)
open CFSG.Quasithin (perfectCore perfectCore_le le_perfectCore_of_perfect perfectCore_perfect)
open scoped MatrixGroups

section Generic

variable {A B : Type*} [Group A] [Group B]

theorem map_centralizer_mulEquiv (Φ : A ≃* B) (Y : Subgroup A) :
    (centralizer (Y : Set A)).map Φ.toMonoidHom =
      centralizer ((Y.map Φ.toMonoidHom : Subgroup B) : Set B) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    change Φ y * Φ a = Φ a * Φ y
    rw [← map_mul, ← map_mul, mem_centralizer_iff.1 ha y hy]
  · intro hb
    refine ⟨Φ.symm b, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro y hy
    apply Φ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_centralizer_iff.1 hb (Φ y) ⟨y, hy, rfl⟩

theorem map_perfectCore_centralizer_mulEquiv [Finite A] [Finite B] (Φ : A ≃* B)
    (Y : Subgroup A) :
    (perfectCore (centralizer (Y : Set A))).map Φ.toMonoidHom =
      perfectCore (centralizer ((Y.map Φ.toMonoidHom : Subgroup B) : Set B)) := by
  rw [CFSG.Quasithin.map_perfectCore, map_centralizer_mulEquiv]

theorem inf_centralizer_eq_of_le_sup {G : Type*} [Group G] {H X Y T : Subgroup G}
    (hHX : H ≤ centralizer (X : Set G)) (hYT : Y ≤ T) (hT : T ≤ X ⊔ Y) :
    H ⊓ centralizer (T : Set G) = H ⊓ centralizer (Y : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le hYT)
  · intro g hg
    obtain ⟨hgH, hgY⟩ := mem_inf.1 hg
    refine mem_inf.2 ⟨hgH, ?_⟩
    have hXY : X ⊔ Y ≤ centralizer ({g} : Set G) := by
      refine sup_le ?_ ?_
      · intro x hx
        rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.1 (hHX hgH) x hx
      · intro y hy
        rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.1 hgY y hy
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := hXY (hT hx)
    rw [mem_centralizer_singleton_iff] at h1
    exact h1

theorem perfectCore_inf_centralizer_eq_map {G : Type*} [Group G] [Finite G] {E Y : Subgroup G}
    (hYE : Y ≤ E) :
    perfectCore (E ⊓ centralizer (Y : Set G)) =
      (perfectCore (centralizer ((Y.subgroupOf E : Subgroup E) : Set E))).map E.subtype := by
  have hmap : (centralizer ((Y.subgroupOf E : Subgroup E) : Set E)).map E.subtype =
      E ⊓ centralizer (Y : Set G) := by
    ext g
    simp only [mem_map, mem_inf, mem_centralizer_iff, SetLike.mem_coe, coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun x hx => ?_⟩
      have h1 := hy ⟨x, hYE hx⟩ (by rw [mem_subgroupOf]; exact hx)
      exact congrArg Subtype.val h1
    · rintro ⟨hgE, hg⟩
      exact ⟨⟨g, hgE⟩, fun y hy => Subtype.ext (hg y (mem_subgroupOf.1 hy)), rfl⟩
  rw [← hmap, CFSG.Quasithin.map_perfectCore]

end Generic

section TwoBlock

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem centralizer_twTorusSL_le_blockDiagSL (hF : 4 ≤ Nat.card F) (a : Fin 2) :
    centralizer (twTorusSL F a : Set (SpecialLinearGroup (Fin (2 * 2)) F)) ≤
      blockDiagSL (K := F) (twBlockSL a) := by
  obtain ⟨κ₀, hκ₀⟩ := exists_units_ne_one_of_four_le hF
  have hne := coe_units_ne_inv_of_ne_one hκ₀
  intro x hx
  have hd : spModelSL 2 F (tauSp (rootTorusHom F 2 a κ₀)) ∈ twTorusSL F a :=
    mem_twTorusSL.2 ⟨κ₀, rfl⟩
  have hc := mem_centralizer_iff.1 hx _ hd
  have hm := congrArg (fun M : SpecialLinearGroup (Fin (2 * 2)) F =>
    (M : Matrix (Fin (2 * 2)) (Fin (2 * 2)) F)) hc
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_spModelSL_tauSp_rootTorusHom] at hm
  rw [mem_blockDiagSL]
  intro i j hij
  have hij' := congrFun (congrFun hm i) j
  rw [diagonal_mul, mul_diagonal] at hij'
  by_cases hi : i ∈ twBlockSL a
  · have hj : j ∉ twBlockSL a := hij.1 hi
    rw [ite_eq_left hi, ite_eq_right hj] at hij'
    have h1 : ((κ₀ : F) - ((κ₀⁻¹ : Fˣ) : F)) *
        (x : Matrix (Fin (2 * 2)) (Fin (2 * 2)) F) i j = 0 := by
      linear_combination hij'
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hne)
  · have hj : j ∈ twBlockSL a := by
      by_contra hj
      exact hi (hij.2 hj)
    rw [ite_eq_right hi, ite_eq_left hj] at hij'
    have h1 : ((κ₀ : F) - ((κ₀⁻¹ : Fˣ) : F)) *
        (x : Matrix (Fin (2 * 2)) (Fin (2 * 2)) F) i j = 0 := by
      linear_combination -hij'
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hne)

theorem perfectCore_centralizer_twTorusSL (hF : 4 ≤ Nat.card F) (a : Fin 2) :
    perfectCore (centralizer (twTorusSL F a : Set (SpecialLinearGroup (Fin (2 * 2)) F))) =
      blockSpecialLinear (K := F) (twBlockSL a) ⊔ blockSpecialLinear (K := F) (twBlockSL a)ᶜ := by
  apply le_antisymm
  · set C := centralizer (twTorusSL F a : Set (SpecialLinearGroup (Fin (2 * 2)) F))
    have h1 : perfectCore C ≤ ⁅C, C⁆ := by
      rw [← perfectCore_perfect C]
      exact Subgroup.commutator_mono (perfectCore_le C) (perfectCore_le C)
    exact h1.trans ((Subgroup.commutator_mono (centralizer_twTorusSL_le_blockDiagSL hF a)
      (centralizer_twTorusSL_le_blockDiagSL hF a)).trans
      (LinearPilot.commutator_blockDiagSL_le _))
  · exact sup_twBlock_le_perfectCore_centralizer_twTorusSL hF a

end TwoBlock



section Tori

variable {K : Type} [Field K]

theorem diagSp_two_eq (u : Fin 2 → Kˣ) :
    diagSp K 2 u = rootTorusHom K 2 0 (u 0) * rootTorusHom K 2 1 (u 1) := by
  rw [rootTorusHom_apply, rootTorusHom_apply, ← map_mul]
  congr 1
  funext i
  fin_cases i <;> simp

theorem coe_complSpEquiv_two_diagSp (u : Fin 2 → Kˣ) :
    ((complSpEquiv (2 : Fin 3) (diagSp K 2 u) : complSp K 2) : StatedSp 3 K) =
      diagSp K 3 ![u 0, u 1, 1] := by
  rw [diagSp_two_eq, map_mul, Subgroup.coe_mul, coe_complSpEquiv_rootTorusHom,
    coe_complSpEquiv_rootTorusHom, rootTorusHom_apply, rootTorusHom_apply, ← map_mul]
  congr 1
  funext i
  fin_cases i <;> simp [Fin.succAbove]

theorem coe_complSpEquiv_zero_diagSp (u : Fin 2 → Kˣ) :
    ((complSpEquiv (0 : Fin 3) (diagSp K 2 u) : complSp K 0) : StatedSp 3 K) =
      diagSp K 3 ![1, u 0, u 1] := by
  rw [diagSp_two_eq, map_mul, Subgroup.coe_mul, coe_complSpEquiv_rootTorusHom,
    coe_complSpEquiv_rootTorusHom, rootTorusHom_apply, rootTorusHom_apply, ← map_mul]
  congr 1
  funext i
  fin_cases i <;> simp [Fin.succAbove]

@[expose] noncomputable def complSpHom (k : Fin 3) : StatedSp 2 K →* StatedSp 3 K :=
  (complSp K k).subtype.comp (complSpEquiv k).toMonoidHom

theorem complSpHom_apply (k : Fin 3) (x : StatedSp 2 K) :
    complSpHom k x = ((complSpEquiv k x : complSp K k) : StatedSp 3 K) := rfl

theorem leviTorusSp_zero_le_sup :
    leviTorusSp K ({0} : Finset (Fin 3)) ≤
      rootTorusSp K 2 ⊔ (siegelTorus K 2).map (complSpHom (K := K) 2) := by
  rintro _ ⟨t, ht, rfl⟩
  have h01 : t 0 = t 1 := (ht 0 (Finset.mem_singleton_self 0)).1 (by decide)
  have hd : diagSp K 3 t = rootTorusHom K 3 2 (t 2) *
      complSpHom 2 (diagSp K 2 (fun _ => t 0)) := by
    rw [complSpHom_apply, coe_complSpEquiv_two_diagSp, rootTorusHom_apply, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [h01]
  rw [hd]
  exact mul_mem (mem_sup_left (rootTorusHom_mem_rootTorusSp _ _))
    (mem_sup_right ⟨_, ⟨t 0, rfl⟩, rfl⟩)

theorem map_siegelTorus_two_le_leviTorusSp_zero :
    (siegelTorus K 2).map (complSpHom (K := K) 2) ≤ leviTorusSp K ({0} : Finset (Fin 3)) := by
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  change complSpHom 2 (diagSp K 2 (fun _ => s)) ∈ _
  rw [complSpHom_apply, coe_complSpEquiv_two_diagSp]
  refine diagSp_mem_leviTorusSp ?_
  intro j hj
  rw [Finset.mem_singleton] at hj
  subst hj
  exact ⟨fun _ => rfl, fun h => absurd h (by decide)⟩

theorem leviTorusSp_one_le_sup :
    leviTorusSp K ({1} : Finset (Fin 3)) ≤
      rootTorusSp K 0 ⊔ (siegelTorus K 2).map (complSpHom (K := K) 0) := by
  rintro _ ⟨t, ht, rfl⟩
  have h12 : t 1 = t 2 := (ht 1 (Finset.mem_singleton_self 1)).1 (by decide)
  have hd : diagSp K 3 t = rootTorusHom K 3 0 (t 0) *
      complSpHom 0 (diagSp K 2 (fun _ => t 1)) := by
    rw [complSpHom_apply, coe_complSpEquiv_zero_diagSp, rootTorusHom_apply, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [h12]
  rw [hd]
  exact mul_mem (mem_sup_left (rootTorusHom_mem_rootTorusSp _ _))
    (mem_sup_right ⟨_, ⟨t 1, rfl⟩, rfl⟩)

theorem map_siegelTorus_zero_le_leviTorusSp_one :
    (siegelTorus K 2).map (complSpHom (K := K) 0) ≤ leviTorusSp K ({1} : Finset (Fin 3)) := by
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  change complSpHom 0 (diagSp K 2 (fun _ => s)) ∈ _
  rw [complSpHom_apply, coe_complSpEquiv_zero_diagSp]
  refine diagSp_mem_leviTorusSp ?_
  intro j hj
  rw [Finset.mem_singleton] at hj
  subst hj
  exact ⟨fun _ => rfl, fun h => absurd h (by decide)⟩

theorem leviTorusSp_two_le_sup :
    leviTorusSp K ({2} : Finset (Fin 3)) ≤
      rootTorusSp K 0 ⊔ (rootTorusSp K 0).map (complSpHom (K := K) 0) := by
  rintro _ ⟨t, ht, rfl⟩
  have h2 : t 2 = 1 := (ht 2 (Finset.mem_singleton_self 2)).2 (by decide)
  have hd : diagSp K 3 t = rootTorusHom K 3 0 (t 0) *
      complSpHom 0 (rootTorusHom K 2 0 (t 1)) := by
    rw [complSpHom_apply, coe_complSpEquiv_rootTorusHom, rootTorusHom_apply, rootTorusHom_apply,
      ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [h2, Fin.succAbove]
  rw [hd]
  exact mul_mem (mem_sup_left (rootTorusHom_mem_rootTorusSp _ _))
    (mem_sup_right ⟨_, rootTorusHom_mem_rootTorusSp _ _, rfl⟩)

theorem map_rootTorusSp_zero_le_leviTorusSp_two :
    (rootTorusSp K 0).map (complSpHom (K := K) 0) ≤ leviTorusSp K ({2} : Finset (Fin 3)) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
  rw [complSpHom_apply, coe_complSpEquiv_rootTorusHom, rootTorusHom_apply]
  refine diagSp_mem_leviTorusSp ?_
  intro j hj
  rw [Finset.mem_singleton] at hj
  subst hj
  refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
  simp [Fin.succAbove]

end Tori


section Images

variable {K : Type} [Field K] [Finite K] [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite K] in
theorem tauSp_diagSp_const (s : Kˣ) :
    tauSp (diagSp K 2 (fun _ => s)) = rootTorusHom K 2 0 (s * s) := by
  rw [tauSp_diagSp_two, rootTorusHom_apply]
  congr 1
  funext i
  fin_cases i <;> simp

omit [Finite F] in
theorem map_twisted_siegelTorus_eq (σ : K ≃+* F) :
    (((siegelTorus K 2).map tauSp).map (statedSpMap (σ : K →+* F) 2)).map (spModelSL 2 F) =
      stdTorusSL F 0 := by
  ext d
  constructor
  · rintro ⟨_, ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    refine mem_stdTorusSL.2 ⟨Units.map (σ : K →+* F) (s * s), ?_⟩
    change _ = spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp (diagSp K 2 (fun _ => s))))
    rw [tauSp_diagSp_const, statedSpMap_rootTorusHom]
  · intro hd
    obtain ⟨μ, rfl⟩ := mem_stdTorusSL.1 hd
    obtain ⟨r, hr⟩ := isSquare_of_charTwo' ((σ.symm : F →+* K) (μ : F))
    have hr0 : r ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hr
      exact μ.ne_zero (by simpa using congrArg σ hr)
    set s : Kˣ := Units.mk0 r hr0 with hs
    refine ⟨_, ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, rfl⟩, ?_⟩
    change spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp (diagSp K 2 (fun _ => s)))) = _
    rw [tauSp_diagSp_const, statedSpMap_rootTorusHom]
    congr 2
    ext
    simp only [Units.coe_map, MonoidHom.coe_ofClass, Units.val_mul, hs, Units.val_mk0]
    rw [← hr]
    simp

omit [Finite K] [Finite F] in
theorem map_twisted_rootTorusSp_zero_eq (σ : K ≃+* F) :
    (((rootTorusSp K 0).map tauSp).map (statedSpMap (σ : K →+* F) 2)).map (spModelSL 2 F) =
      twTorusSL F 0 := by
  ext d
  constructor
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨κ, rfl⟩ := mem_rootTorusSp.1 hx
    refine mem_twTorusSL.2 ⟨Units.map (σ : K →+* F) κ, ?_⟩
    change _ = spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp (rootTorusHom K 2 0 κ)))
    rw [statedSpMap_tauSp_rootTorusHom]
  · intro hd
    obtain ⟨μ, rfl⟩ := mem_twTorusSL.1 hd
    set κ : Kˣ := Units.map (σ.symm : F →+* K) μ with hκ
    have hμ : Units.map (σ : K →+* F) κ = μ := by
      ext
      simp [hκ]
    refine ⟨_, ⟨_, ⟨_, rootTorusHom_mem_rootTorusSp 0 κ, rfl⟩, rfl⟩, ?_⟩
    change spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (tauSp (rootTorusHom K 2 0 κ))) = _
    rw [statedSpMap_tauSp_rootTorusHom, hμ]

end Images

section Pieces

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite K] [CharP K 2] in
theorem pieceCore_eq_map_of_N1 (hK : 4 ≤ Nat.card K) (e : L ≃* StatedSp 3 K) {k : Fin 3}
    {J : Finset (Fin 3)} (hk : k ∉ spSupport J) (σ : K ≃+* F) (β : StatedSp 2 K →* StatedSp 2 K)
    (Φ : SpecialLinearGroup (Fin (2 * 2)) F ≃* neighbourCore e k)
    (hN1 : ∀ x : StatedSp 2 K,
      ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (β x))) : neighbourCore e k) : G) =
        ((e.symm (complSpEquiv k x : complSp K k) : L) : G))
    (T₄ : Subgroup (StatedSp 2 K))
    (hfact : leviTorusSp K J ≤
      rootTorusSp K k ⊔ T₄.map ((complSp K k).subtype.comp (complSpEquiv k).toMonoidHom))
    (hT₄ : T₄.map ((complSp K k).subtype.comp (complSpEquiv k).toMonoidHom) ≤ leviTorusSp K J)
    {C : Subgroup (SpecialLinearGroup (Fin (2 * 2)) F)}
    (hC : perfectCore (centralizer ((((T₄.map β).map (statedSpMap (σ : K →+* F) 2)).map
      (spModelSL 2 F) : Subgroup (SpecialLinearGroup (Fin (2 * 2)) F)) :
        Set (SpecialLinearGroup (Fin (2 * 2)) F))) = C) :
    pieceCore e J = (C.map Φ.toMonoidHom).map (neighbourCore e k).subtype := by
  set ι : StatedSp 2 K →* StatedSp 3 K :=
    (complSp K k).subtype.comp (complSpEquiv k).toMonoidHom with hι
  have hY : modelToG e (T₄.map ι) ≤ neighbourCore e k := by
    refine le_trans ?_ (modelToG_complSp_le_neighbourCore e hK (by norm_num) k)
    refine UnitaryPilot.modelToG_mono e ?_
    rintro _ ⟨x, -, rfl⟩
    exact (complSpEquiv k x).2
  rw [pieceCore_eq e hk, inf_centralizer_eq_of_le_sup (H := neighbourCore e k)
    (X := modelToG e (rootTorusSp K k))
    (Y := modelToG e (T₄.map ι)) (centralizerPerfectCore_le_centralizer _)
    (UnitaryPilot.modelToG_mono e hT₄)
    (by rw [← UnitaryPilot.modelToG_sup]; exact UnitaryPilot.modelToG_mono e hfact),
    perfectCore_inf_centralizer_eq_map hY]
  congr 1
  rw [← hC, map_perfectCore_centralizer_mulEquiv Φ]
  congr 2
  ext y
  constructor
  · intro hy
    rw [SetLike.mem_coe, mem_subgroupOf] at hy
    obtain ⟨x₀, ⟨x, hx, rfl⟩, hxy⟩ := (UnitaryPilot.mem_modelToG e).1 hy
    rw [SetLike.mem_coe]
    refine ⟨spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (β x)), ⟨_, ⟨β x, ⟨x, hx, rfl⟩, rfl⟩,
      rfl⟩, ?_⟩
    apply Subtype.ext
    change ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (β x))) : neighbourCore e k) : G) = y
    rw [hN1 x, ← hxy]
    rfl
  · rintro ⟨_, ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, mem_subgroupOf]
    change ((Φ (spModelSL 2 F (statedSpMap (σ : K →+* F) 2 (β x))) : neighbourCore e k) : G) ∈ _
    rw [hN1 x]
    exact symm_mem_modelToG e ⟨x, hx, rfl⟩

end Pieces

end CFSG.SeitzReduction.SymplecticPilot
