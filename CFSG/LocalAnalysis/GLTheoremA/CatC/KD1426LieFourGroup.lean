module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieTwoEig
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieFour
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1426LieField
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.GroupTheory.CommuteOfSqEqOne
public import CFSG.HardMathSupport.Solomon.Coordinator.L3BAutSL

public section

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.RankThree.PartTwo.Sec4

namespace CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

@[expose] def LayerTrivialOn (P : Type) [Group P] (A : Subgroup (MulAut P)) : Prop :=
  ∀ α ∈ A, α ≠ 1 → GLAPLayer 3 (fixSubgroup α) = ⊥

theorem layerTrivialOn_map_congr {G H : Type} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) {A : Subgroup (MulAut G)} (hA : LayerTrivialOn G A) :
    LayerTrivialOn H (A.map (MulAut.congr e).toMonoidHom) := by
  rintro α' hα' hα'1
  obtain ⟨α, hα, rfl⟩ := Subgroup.mem_map.1 hα'
  have hα1 : α ≠ 1 := fun h => hα'1 (by rw [h, map_one])
  change GLAPLayer 3 (fixSubgroup (MulAut.congr e α)) = ⊥
  rw [glaPLayer_fixSubgroup_congr Nat.prime_three e α, hA α hα hα1, Subgroup.map_bot]

section Step2

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.GLTheoremA.KD2027Aux
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag

private theorem false_of_not_mem_of_glaPComponent {P : Type} [Group P] [Finite P]
    {A : Subgroup (MulAut P)} (hlay : LayerTrivialOn P A) {S : Subgroup (MulAut P)}
    (h1 : (1 : MulAut P) ∈ S) {α : MulAut P} (hα : α ∈ A) (hD : α ∉ S)
    (hcomp : GLAPComponent 3 (fixSubgroup α) (GLAPLayer 3 (fixSubgroup α))) : False :=
  CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hcomp
    (hlay α hα fun h => hD (h ▸ h1))

theorem le_linearAutGroup_and_card_le_nine_projectiveSL {F : Type} [Field F] [Finite F]
    (hF : Nat.card F % 6 = 1) {A : Subgroup (MulAut (projectiveSL 3 F))}
    (hA : IsElemAbelian 3 A) (h : LayerTrivialOn (projectiveSL 3 F) A) :
    A ≤ linearAutGroup 3 F ∧ Nat.card A ≤ 9 := by
  have hmem : ∀ α ∈ A, α ∈ linearAutGroup 3 F := by
    intro α hα
    by_contra hD
    exact false_of_not_mem_of_glaPComponent h (Subgroup.one_mem _) hα hD
      (glaPComponent_fixSubgroup_of_not_mem_linearAutGroup hF (hA.2 α hα) hD).1
  refine ⟨hmem, ?_⟩
  exact CFSG.HardMathSupport.Solomon.LocalBalance.AutL3.hD9_L
    (three_dvd_sub_one_of_mod_six_eq_one hF) A hmem hA

theorem le_psuConj_range_and_card_le_nine {p f : ℕ} {F : Type} [Field F]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f F) (hq : p ^ f % 6 = 5)
    {A : Subgroup (MulAut (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU h 3))}
    (hA : IsElemAbelian 3 A)
    (hlay : LayerTrivialOn (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU h 3) A) :
    A ≤ (CFSG.RankThree.PartTwo.KFacts.psuConj h).range ∧ Nat.card A ≤ 9 := by
  haveI : Finite F := h.finite
  have hmem : ∀ α ∈ A, α ∈ (CFSG.RankThree.PartTwo.KFacts.psuConj h).range := by
    intro α hα
    by_contra hD
    exact false_of_not_mem_of_glaPComponent hlay (Subgroup.one_mem _) hα hD
      (glaPComponent_fixSubgroup_of_not_mem_psuConj_range h hq (hA.2 α hα) hD).1
  refine ⟨hmem, ?_⟩
  have h3 : 3 ∣ p ^ f + 1 := three_dvd_succ_of_mod_six_eq_five hq
  exact CFSG.HardMathSupport.Solomon.LocalBalance.AutL3.hD9_U h h3 A hmem hA

theorem card_le_nine_mulAut_of_l3Model {S : Type} [Group S] [Finite S]
    (hmodel : CFSG.LocalAnalysis.GLTheoremA.KD2027Aux.L3Model S) {A : Subgroup (MulAut S)}
    (hA : IsElemAbelian 3 A) (h : LayerTrivialOn S A) : Nat.card A ≤ 9 := by
  rcases hmodel with ⟨K, hK, hKf, hmod, ⟨e⟩⟩ | ⟨K, hK, hKf, p, f, hp, hf, hmod, hcard, ⟨e⟩⟩
  · let e' : S ≃* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
      e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K).symm
    have hb := le_linearAutGroup_and_card_le_nine_projectiveSL hmod
      (IsElemAbelian.map hA (MulAut.congr e').toMonoidHom) (layerTrivialOn_map_congr e' h)
    rw [Subgroup.card_map_of_injective (MulAut.congr e').injective] at hb
    exact hb.2
  · have hq : 2 < p ^ f := by have := five_le_of_mod_six_eq_five hmod; omega
    have hF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
      ⟨hp, hf, by rw [hcard, ← pow_mul, Nat.mul_comm]⟩
    let e' : S ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hF 3 :=
      e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hF (n := 3) (by norm_num)).symm
    have hb := le_psuConj_range_and_card_le_nine hF hmod
      (IsElemAbelian.map hA (MulAut.congr e').toMonoidHom) (layerTrivialOn_map_congr e' h)
    rw [Subgroup.card_map_of_injective (MulAut.congr e').injective] at hb
    exact hb.2

section Linear

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {F : Type} [Field F] [Finite F]

theorem zPi_true_eq_center (n q : ℕ) :
    zPi true n q F = Subgroup.center (GL (Fin n) F) := by
  have hgl : glPi true n q F = ⊤ := rfl
  rw [zPi, hgl]
  ext A
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ Subgroup.center (⊤ : Subgroup (GL (Fin n) F)) := hx
    rw [Subgroup.mem_center_iff] at hx'
    rw [Subgroup.mem_center_iff]
    intro g
    simpa using congrArg Subtype.val (hx' ⟨g, Subgroup.mem_top g⟩)
  · intro hA
    refine ⟨⟨A, Subgroup.mem_top A⟩, ?_, rfl⟩
    show (⟨A, Subgroup.mem_top A⟩ : ↥(⊤ : Subgroup (GL (Fin n) F))) ∈
      Subgroup.center (⊤ : Subgroup (GL (Fin n) F))
    rw [Subgroup.mem_center_iff] at hA ⊢
    intro y
    exact Subtype.ext (hA (y : GL (Fin n) F))

theorem ker_conjAut_eq_zPi {n : ℕ} (hn : 3 ≤ n) (q : ℕ) :
    (conjAut n F).ker = zPi true n q F := by
  rw [zPi_true_eq_center, Matrix.GeneralLinearGroup.center_eq_range_scalar]
  ext A
  rw [MonoidHom.mem_ker, CFSG.ComponentClassification.UnbalancedCatalog.conjAut_eq_one_iff hn,
    MonoidHom.mem_range]

omit [Finite F] in
theorem eq_one_of_eq_scalar_diagE {e c : Fˣ}
    (hc : (Matrix.GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) = diagE e) : e = 1 := by
  have h1 : (e : F) = (c : F) := by
    have := congrArg (fun g : GL (Fin 3) F => ((g : Matrix (Fin 3) (Fin 3) F) 0 0)) hc
    simpa [coe_diagE, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this.symm
  have h2 : (1 : F) = (c : F) := by
    have := congrArg (fun g : GL (Fin 3) F => ((g : Matrix (Fin 3) (Fin 3) F) 1 1)) hc
    simpa [coe_diagE, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this.symm
  exact Units.ext (h1.trans h2.symm)

theorem diagE_notMem_zPi_true {q : ℕ} {e : Fˣ} (he1 : e ≠ 1) : diagE e ∉ zPi true 3 q F := by
  rw [zPi_true_eq_center, Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range]
  rintro ⟨c, hc⟩
  exact he1 (eq_one_of_eq_scalar_diagE hc)


private theorem le_conjAut_range {A : Subgroup (MulAut (projectiveSL 3 F))}
    (hF : Nat.card F % 6 = 1) (hA : IsElemAbelian 3 A)
    (hlay : LayerTrivialOn (projectiveSL 3 F) A) : A ≤ (conjAut 3 F).range := by
  have h := (le_linearAutGroup_and_card_le_nine_projectiveSL hF hA hlay).1
  rwa [show linearAutGroup 3 F = (conjAut 3 F).range from
    (Subgroup.closure_eq (conjAut 3 F).range)] at h

theorem fourGroupInput_linear (hF : Nat.card F % 6 = 1) {p f : ℕ} (hK : PiField true p f F)
    (hq : ModThree true (p ^ f)) {τ : F} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {A : Subgroup (MulAut (projectiveSL 3 F))} (hA : IsElemAbelian 3 A)
    (hlay : LayerTrivialOn (projectiveSL 3 F) A) (hcard : Nat.card A = 9) :
    ∃ T : Subgroup (GL (Fin 3) F), T ≤ slPi true 3 (p ^ f) F ∧ Nat.card T = 4 ∧
      (∀ t ∈ T, t ^ 2 = 1) ∧ T ⊓ zPi true 3 (p ^ f) F = ⊥ ∧
      (∀ b ∈ A.comap (conjAut 3 F), b ∈ Subgroup.normalizer (T : Set (GL (Fin 3) F))) ∧
      ∃ b ∈ A.comap (conjAut 3 F), ⁅T, Subgroup.zpowers b⁆ = T := by
  have hcardF : Nat.card F = p ^ f := by
    have h := hK.card
    rwa [piCard, Bool.cond_true] at h
  have hp : 5 ≤ p := by
    have h6 : p ^ f % 6 = 1 := by rw [← hcardF]; exact hF
    exact five_le_of_prime_of_pow_mod_six hK.prime hK.one_le (Or.inl h6)
  have hArange : A ≤ (conjAut 3 F).range := le_conjAut_range hF hA hlay
  refine exists_fourGroup_of_pgl_nine hK hp hq hτ hτ1 le_top ?_ ?_ ?_ ?_ ?_
  ·
    rw [← ker_conjAut_eq_zPi (by norm_num) (p ^ f)]
    exact Subgroup.ker_le_comap _ A
  ·
    intro b hb
    rw [← ker_conjAut_eq_zPi (by norm_num) (p ^ f), MonoidHom.mem_ker, map_pow]
    have h3 : (conjAut 3 F b) ^ 3 = 1 := hA.2 _ hb
    rw [h3]
  ·
    intro b hb c hc
    rw [← ker_conjAut_eq_zPi (by norm_num) (p ^ f), MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (hA.1.is_comm.comm ⟨conjAut 3 F b, hb⟩ ⟨conjAut 3 F c, hc⟩)
  ·
    rw [← ker_conjAut_eq_zPi (by norm_num) (p ^ f), Subgroup.relIndex_ker,
      Subgroup.map_comap_eq, inf_eq_right.2 hArange, hcard]
  ·
    rintro b hb z hz g _ e he hEq
    have he3 : (e : F) ^ 3 = 1 := val_pow_three_eq_one_of_eq_or_eq_sq hτ he
    have he1 : e ≠ 1 := ne_one_of_val_eq_or_eq_sq hτ hτ1 he
    have hzker : z ∈ (conjAut 3 F).ker := by
      rw [ker_conjAut_eq_zPi (by norm_num) (p ^ f)]
      exact hz
    have hbz : conjAut 3 F (b * z) = conjAut 3 F b := by
      rw [map_mul, MonoidHom.mem_ker.1 hzker, mul_one]
    have hconj : conjAut 3 F b =
        MulAut.congr (conjAut 3 F g : projectiveSL 3 F ≃* projectiveSL 3 F)
          (conjAut 3 F (diagE e)) := by
      have h := congrArg (conjAut 3 F) hEq
      rw [map_mul, map_mul, map_inv, hbz] at h
      show conjAut 3 F b = conjAut 3 F g * conjAut 3 F (diagE e) * (conjAut 3 F g)⁻¹
      calc conjAut 3 F b
          = conjAut 3 F g * ((conjAut 3 F g)⁻¹ * conjAut 3 F b * conjAut 3 F g) *
              (conjAut 3 F g)⁻¹ := by group
        _ = conjAut 3 F g * conjAut 3 F (diagE e) * (conjAut 3 F g)⁻¹ := by rw [← h]
    have hne : GLAPLayer 3 (fixSubgroup (conjAut 3 F (diagE e))) ≠ ⊥ :=
      glaPLayer_fixSubgroup_conjAut_diagE_ne_bot hF he3 he1
    have hne' : GLAPLayer 3 (fixSubgroup (conjAut 3 F b)) ≠ ⊥ := by
      rw [hconj]
      exact (glaPLayer_fixSubgroup_congr_ne_bot_iff Nat.prime_three
        (conjAut 3 F g : projectiveSL 3 F ≃* projectiveSL 3 F) (conjAut 3 F (diagE e))).2 hne
    have hbne : conjAut 3 F b ≠ 1 := by
      intro h1
      have hbzZ : b * z ∈ zPi true 3 (p ^ f) F := by
        rw [← ker_conjAut_eq_zPi (by norm_num) (p ^ f), MonoidHom.mem_ker, map_mul,
          MonoidHom.mem_ker.1 hzker]
        rw [show conjAut 3 F b = 1 from h1, one_mul]
      have hcen : b * z ∈ Subgroup.center (GL (Fin 3) F) := by
        rwa [← zPi_true_eq_center]
      have hconjmem : g⁻¹ * (b * z) * g ∈ Subgroup.center (GL (Fin 3) F) := by
        have h := (inferInstance : (Subgroup.center (GL (Fin 3) F)).Normal).conj_mem
          (b * z) hcen g⁻¹
        rwa [inv_inv] at h
      rw [hEq] at hconjmem
      have hmem : diagE e ∈ zPi true 3 (p ^ f) F := by
        rw [zPi_true_eq_center]
        exact hconjmem
      exact diagE_notMem_zPi_true he1 hmem
    exact hne' (hlay _ hb hbne)

theorem fourGroup_push
    {G P N : Type*} [Group G] [Group P] [Group N]
    (π : G →* P) (act : N →* MulAut G) (projN : N →* MulAut P)
    (hcompat : ∀ (n : N) (x : G), projN n (π x) = π (act n x))
    (J : Subgroup G) (hJinf : J ⊓ π.ker = ⊥) (hJcard : Nat.card ↥J = 4)
    (hJsq : ∀ j ∈ J, j ^ 2 = 1)
    (A : Subgroup (MulAut P))
    (hind : ∀ α ∈ A, ∃ n : N, (∀ j ∈ J, act n j ∈ J) ∧ (∀ j ∈ J, act n⁻¹ j ∈ J) ∧ projN n = α)
    (n₀ : N) (hn₀A : projN n₀ ∈ A) (hn₀J : ∀ j ∈ J, act n₀ j ∈ J)
    (hsurj : ∀ j ∈ J, ∃ j' ∈ J, π j = π (act n₀ j' * j'⁻¹)) :
    ∃ T : Subgroup P, IsElemAbelian 2 T ∧ Nat.card ↥T = 4 ∧
      (∀ α ∈ A, Subgroup.map α.toMonoidHom T = T) ∧
      ∃ α ∈ A, ∀ t ∈ T, ∃ s ∈ T, t = α s * s⁻¹ := by
  classical
  haveI : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [hJcard]; norm_num)
  have hle_gen : ∀ (β : MulAut P) (n : N), (∀ j ∈ J, act n j ∈ J) → projN n = β →
      Subgroup.map β.toMonoidHom (Subgroup.map π J) ≤ Subgroup.map π J := by
    intro β n hn hβ
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hx
    change β.toMonoidHom (π j) ∈ Subgroup.map π J
    have h1 : β.toMonoidHom (π j) = π (act n j) := by
      have h2 := hcompat n j
      rw [hβ] at h2
      exact h2
    rw [h1]
    exact Subgroup.mem_map_of_mem π (hn j hj)
  refine ⟨Subgroup.map π J, ?_, ?_, ?_, ?_⟩
  ·
    have hsq : ∀ t ∈ Subgroup.map π J, t ^ 2 = 1 := by
      intro t ht
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 ht
      rw [← map_pow, hJsq j hj, map_one]
    refine ⟨IsMulCommutative.of_comm (fun x y => ?_), hsq⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.1 y.2
    rw [← hax, ← hbx, ← map_mul, ← map_mul]
    exact congrArg π (commute_of_sq_eq_one (hJsq a ha) (hJsq b hb) (hJsq (a * b) (J.mul_mem ha hb)))
  ·
    rw [card_map_eq_card_of_inf_ker_eq_bot (f := π) hJinf, hJcard]
  ·
    intro α hα
    obtain ⟨n, hnJ, hnJinv, hnα⟩ := hind α hα
    have hle : Subgroup.map α.toMonoidHom (Subgroup.map π J) ≤ Subgroup.map π J :=
      hle_gen α n hnJ hnα
    have hle2 : Subgroup.map (α⁻¹).toMonoidHom (Subgroup.map π J) ≤ Subgroup.map π J :=
      hle_gen α⁻¹ n⁻¹ hnJinv (by rw [map_inv, hnα])
    refine le_antisymm hle ?_
    intro x hx
    refine Subgroup.mem_map.2 ⟨α⁻¹ x, hle2 (Subgroup.mem_map_of_mem _ hx), ?_⟩
    simp
  ·
    refine ⟨projN n₀, hn₀A, ?_⟩
    intro t ht
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨j', hj', hjj'⟩ := hsurj j hj
    exact ⟨π j', Subgroup.mem_map_of_mem π hj', by
      rw [hcompat n₀ j', ← map_inv, ← map_mul]
      exact hjj'⟩

theorem exists_fourGroup_projectiveSL (hF : Nat.card F % 6 = 1)
    {A : Subgroup (MulAut (projectiveSL 3 F))} (hA : IsElemAbelian 3 A)
    (hlay : LayerTrivialOn (projectiveSL 3 F) A) (hcard : Nat.card A = 9) :
    ∃ T : Subgroup (projectiveSL 3 F), IsElemAbelian 2 T ∧ Nat.card ↥T = 4 ∧
      (∀ α ∈ A, Subgroup.map α.toMonoidHom T = T) ∧
      ∃ α ∈ A, ∀ t ∈ T, ∃ s ∈ T, t = α s * s⁻¹ := by
  have h3F : 3 ∣ Nat.card F - 1 := three_dvd_sub_one_of_mod_six_eq_one hF
  obtain ⟨τ, hτ3, hτ1⟩ : ∃ τ : F, τ ^ 3 = 1 ∧ τ ≠ 1 :=
    CFSG.HardMathSupport.Solomon.Coordinator.exists_primitive_cube_root F h3F
  obtain ⟨p, f, hK⟩ := exists_piField_true_of_card_mod_six hF
  have hcardF : Nat.card F = p ^ f := by
    have h := hK.card; rwa [piCard, Bool.cond_true] at h
  have hq : ModThree true (p ^ f) := mod_three_eq_one_of_mod_six_eq_one (by rw [← hcardF]; exact hF)
  obtain ⟨T, hTle, hTcard, hTsq, hTinf, hTnorm, b, hbB, hbcomm⟩ :=
    fourGroupInput_linear hF hK hq hτ3 hτ1 hA hlay hcard
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    exact CFSG.commute_of_sq_eq_one (hTsq x hx) (hTsq y hy) (hTsq (x * y) (T.mul_mem hx hy))
  set toGL := Matrix.SpecialLinearGroup.toGL (n := Fin 3) (R := F) with htoGL
  have htoGLinj : Function.Injective toGL := Matrix.SpecialLinearGroup.toGL_injective
  set J : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) := T.comap toGL with hJ
  have hJmap : J.map toGL = T := by
    rw [hJ, Subgroup.map_comap_eq, inf_eq_right.2]
    rwa [← CFSG.Open.StatedAPI.statedSL_eq_range_toGL]
  have hJcard : Nat.card ↥J = 4 := by
    rw [← hTcard, ← hJmap]
    exact (Subgroup.card_map_of_injective htoGLinj).symm
  have hJsq : ∀ j ∈ J, j ^ 2 = 1 := by
    intro j hj
    have hjT : toGL j ∈ T := hj
    apply htoGLinj
    rw [map_pow, map_one]
    exact hTsq (toGL j) hjT
  have hJinf : J ⊓ (proj 3 F).ker = ⊥ := by
    have hscal : ((proj 3 F).ker).map toGL ≤ zPi true 3 (p ^ f) F := by
      rw [zPi_true_eq_center, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      intro x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
      rw [ker_proj, mem_scalars] at hs
      obtain ⟨c, hc, hsc⟩ := hs
      refine ⟨c, ?_⟩
      have hseq : s = scalarElement (n := 3) c hc := Subtype.ext (by rw [coe_scalarElement, ← hsc])
      rw [hseq]
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
        coe_scalarElement]
    have h1 : (J ⊓ (proj 3 F).ker).map toGL ≤ T ⊓ zPi true 3 (p ^ f) F := by
      refine le_inf ?_ ?_
      · calc (J ⊓ (proj 3 F).ker).map toGL ≤ J.map toGL := Subgroup.map_mono inf_le_left
          _ = T := hJmap
      · exact (Subgroup.map_mono inf_le_right).trans hscal
    rw [hTinf] at h1
    have h2 : (J ⊓ (proj 3 F).ker).map toGL = ⊥ := le_bot_iff.1 h1
    rw [Subgroup.map_eq_bot_iff] at h2
    rw [show toGL.ker = ⊥ from MonoidHom.ker_eq_bot _ htoGLinj] at h2
    exact le_bot_iff.1 h2
  have hsl : ∀ (g : GL (Fin 3) F) (j : Matrix.SpecialLinearGroup (Fin 3) F),
      toGL (slConjugation 3 F g j) = g * toGL j * g⁻¹ := by
    intro g j
    apply Units.ext
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, coe_slConjugation]
    rfl
  have hpres : ∀ g ∈ A.comap (conjAut 3 F), ∀ j ∈ J, slConjugation 3 F g j ∈ J := by
    intro g hg j hj
    rw [hJ, Subgroup.mem_comap, hsl]
    exact (Subgroup.mem_normalizer_iff.1 (hTnorm g hg) _).1 hj
  have hArange : A ≤ (conjAut 3 F).range := le_conjAut_range hF hA hlay
  have hbN : b ∈ Subgroup.normalizer (T : Set (GL (Fin 3) F)) := hTnorm b hbB
  have hb3 : b ^ 3 ∈ Subgroup.centralizer (T : Set (GL (Fin 3) F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hbz : conjAut 3 F (b ^ 3) = 1 := by
      rw [map_pow]
      have h3 : (conjAut 3 F b) ^ 3 = 1 := hA.2 _ hbB
      rw [h3]
    have hzpi : b ^ 3 ∈ zPi true 3 (p ^ f) F := by
      rw [← ker_conjAut_eq_zPi (by norm_num) (p ^ f), MonoidHom.mem_ker]
      exact hbz
    have hcen : b ^ 3 ∈ Subgroup.center (GL (Fin 3) F) := by rwa [← zPi_true_eq_center]
    exact Subgroup.mem_center_iff.1 hcen z
  have hsurjT : ∀ t ∈ T, ∃ s ∈ T, t = b * s * b⁻¹ * s⁻¹ :=
    CFSG.exists_eq_conj_mul_inv_of_commutator_zpowers_eq_top hTcomm hTsq hTcard hbN hb3 hbcomm
  refine fourGroup_push (proj 3 F) (slConjugation 3 F) (conjAut 3 F) ?_ J hJinf hJcard hJsq A
    ?_ b hbB (hpres b hbB) ?_
  · intro g x
    exact conjAut_proj g x
  · intro α hα
    obtain ⟨g, hgen⟩ := MonoidHom.mem_range.1 (hArange hα)
    have hgB : g ∈ A.comap (conjAut 3 F) := by
      show conjAut 3 F g ∈ A
      rwa [hgen]
    exact ⟨g, hpres g hgB, fun j hj => by
      have hgB' : g⁻¹ ∈ A.comap (conjAut 3 F) := Subgroup.inv_mem _ hgB
      have := hpres g⁻¹ hgB' j hj
      rwa [show slConjugation 3 F g⁻¹ = (slConjugation 3 F g)⁻¹ from map_inv _ _] at this, hgen⟩
  · intro j hj
    have hjt : toGL j ∈ T := hj
    obtain ⟨s, hs, hse⟩ := hsurjT (toGL j) hjt
    have hsin : s ∈ toGL.range := by
      rw [← CFSG.Open.StatedAPI.statedSL_eq_range_toGL]; exact hTle hs
    obtain ⟨j', hj'⟩ := MonoidHom.mem_range.1 hsin
    refine ⟨j', ?_, ?_⟩
    · rw [hJ, Subgroup.mem_comap, hj']; exact hs
    · have hjeq : j = slConjugation 3 F b j' * j'⁻¹ := by
        apply htoGLinj
        rw [map_mul, map_inv, hsl b j']
        rw [← hj'] at hse
        exact hse
      exact congrArg (proj 3 F) hjeq

end Linear

end Step2

end CFSG.LocalAnalysis.GLTheoremA.KD1426Lie

end
