module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftDelBlockDict
public import CFSG.Quasithin.Background.F9Comp

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Layer
  CFSG.QuasithinUnique.Setup.Layer.Actor CFSG.QuasithinUnique.Setup.Offender
  CFSG.QuasithinUnique.Setup.SL2Modules
open scoped Multiplicative MatrixGroups LinearAlgebra.Projectivization

universe v

section SL2

variable {F : Type*} [Field F]

theorem sl2_eq_u_l_u (m : SL(2, F)) (hs : (m : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) :
    m = uElt (((m : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) / (m : Matrix (Fin 2) (Fin 2) F) 1 0) *
      lElt ((m : Matrix (Fin 2) (Fin 2) F) 1 0) *
      uElt (((m : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) / (m : Matrix (Fin 2) (Fin 2) F) 1 0) := by
  have hdet := m.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [uElt, lElt, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    first | ring1 | linear_combination hdet | linear_combination (-1 : F) * hdet

theorem sl2_conj_uElt_apply10 (y : SL(2, F)) (t : F) :
    ((y * uElt t * y⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 =
      -((y : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2 * t := by
  have hdet := y.2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  simp [uElt, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem sl2_uElt_neg_mul (a : F) : uElt (-a) * uElt a = (1 : SL(2, F)) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [uElt, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_overgroup_of_lower_ne (hgen : Subgroup.closure (Set.range (uElt (F := F)) ∪
      Set.range (lElt (F := F))) = ⊤) (x : SL(2, F)) (Y : Subgroup SL(2, F))
    (hY : ∀ t : F, x * uElt t * x⁻¹ ∈ Y) (y : SL(2, F)) (hy : y ∈ Y)
    (hc : ((x⁻¹ * y * x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) : Y = ⊤ := by
  set y' := x⁻¹ * y * x with hy'
  have hc2 : ((y' : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hl : ∀ s : F, x * lElt s * x⁻¹ ∈ Y := by
    intro s
    by_cases hs : s = 0
    · subst hs
      have : lElt (0 : F) = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [lElt]
      rw [this]
      simp
    · set t : F := -s / ((y' : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2 with ht
      set m : SL(2, F) := y' * uElt t * y'⁻¹ with hm
      have hm10 : ((m : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = s := by
        rw [hm, sl2_conj_uElt_apply10, ht]
        field_simp
      have hmY : x * m * x⁻¹ ∈ Y := by
        have : x * m * x⁻¹ = y * (x * uElt t * x⁻¹) * y⁻¹ := by
          rw [hm, hy']; group
        rw [this]
        exact Y.mul_mem (Y.mul_mem hy (hY t)) (Y.inv_mem hy)
      have hdec := sl2_eq_u_l_u m (by rw [hm10]; exact hs)
      rw [hm10] at hdec
      set α := (((m : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) / s
      set β := (((m : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 1 - 1) / s
      have hls : lElt s = uElt (-α) * m * uElt (-β) := by
        have h1 : uElt (-α) * uElt α = (1 : SL(2, F)) := sl2_uElt_neg_mul α
        have h2 : uElt β * uElt (-β) = (1 : SL(2, F)) := by
          have := sl2_uElt_neg_mul (-β)
          rwa [neg_neg] at this
        rw [hdec]
        calc lElt s = (uElt (-α) * uElt α) * lElt s * (uElt β * uElt (-β)) := by
              rw [h1, h2]; simp
          _ = uElt (-α) * (uElt α * lElt s * uElt β) * uElt (-β) := by group
      have hu1 : x * uElt (-α) * x⁻¹ ∈ Y := hY _
      have hu2 : x * uElt (-β) * x⁻¹ ∈ Y := hY _
      have : x * lElt s * x⁻¹ =
          (x * uElt (-α) * x⁻¹) * (x * m * x⁻¹) * (x * uElt (-β) * x⁻¹) := by
        rw [hls]; group
      rw [this]
      exact Y.mul_mem (Y.mul_mem hu1 hmY) hu2
  refine eq_top_iff.2 fun M _ => ?_
  have hM : x⁻¹ * M * x ∈ Subgroup.closure (Set.range (uElt (F := F)) ∪
      Set.range (lElt (F := F))) := by
    rw [hgen]; trivial
  have h3 : ∀ z ∈ Subgroup.closure (Set.range (uElt (F := F)) ∪ Set.range (lElt (F := F))),
      x * z * x⁻¹ ∈ Y := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · exact hY t
      · exact hl t
    | one => simp
    | mul z w _ _ hz hw =>
      have := Y.mul_mem hz hw
      rwa [show x * z * x⁻¹ * (x * w * x⁻¹) = x * (z * w) * x⁻¹ by group] at this
    | inv z _ hz =>
      have := Y.inv_mem hz
      rwa [show (x * z * x⁻¹)⁻¹ = x * z⁻¹ * x⁻¹ by group] at this
  have h4 := h3 _ hM
  rwa [show x * (x⁻¹ * M * x) * x⁻¹ = M by group] at h4

theorem sl2_conj_uElt_of_lower_zero (y : SL(2, F))
    (hy : (y : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (t : F) :
    y * uElt t * y⁻¹ = uElt (((y : Matrix (Fin 2) (Fin 2) F) 0 0) ^ 2 * t) := by
  have hdet := y.2
  rw [Matrix.det_fin_two, hy] at hdet
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv]
  fin_cases i <;> fin_cases j <;>
    simp [uElt, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, hy] <;>
    first | ring1 | linear_combination hdet

theorem sl2_mem_normalizer_of_lower_zero (x : SL(2, F)) (A : Subgroup SL(2, F))
    (hA : ∀ g, g ∈ A ↔ ∃ t, x⁻¹ * g * x = uElt t) (y : SL(2, F))
    (hy : ((x⁻¹ * y * x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    y ∈ Subgroup.normalizer (A : Set SL(2, F)) := by
  have fw : ∀ z : SL(2, F), ((x⁻¹ * z * x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
      ∀ g ∈ A, z * g * z⁻¹ ∈ A := by
    intro z hz g hg
    obtain ⟨t, ht⟩ := (hA g).1 hg
    refine (hA _).2 ⟨((x⁻¹ * z * x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * t, ?_⟩
    rw [← sl2_conj_uElt_of_lower_zero _ hz, ← ht]
    group
  have hy' : ((x⁻¹ * y⁻¹ * x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have : x⁻¹ * y⁻¹ * x = (x⁻¹ * y * x)⁻¹ := by group
    rw [this]
    generalize x⁻¹ * y * x = y' at hy ⊢
    rw [Matrix.SpecialLinearGroup.coe_inv]
    simp [Matrix.adjugate_fin_two, hy]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨fw y hy g, fun h => ?_⟩
  have := fw y⁻¹ hy' _ h
  simpa [mul_assoc] using this

end SL2

section Transport

theorem mem_normalizer_of_map_equiv {Γ K : Type*} [Group Γ] [Group K] {L U : Subgroup Γ}
    (hUL : U ≤ L) (θ : ↥L ≃* K) {y : ↥L}
    (hy : θ y ∈ Subgroup.normalizer (((U.subgroupOf L).map θ.toMonoidHom : Subgroup K) : Set K)) :
    (y : Γ) ∈ Subgroup.normalizer (U : Set Γ) := by
  have key : ∀ z : ↥L, z ∈ U.subgroupOf L ↔ y * z * y⁻¹ ∈ U.subgroupOf L := by
    intro z
    have h1 : ∀ w : ↥L, w ∈ U.subgroupOf L ↔ θ w ∈ (U.subgroupOf L).map θ.toMonoidHom := by
      intro w
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    rw [h1 z, h1 (y * z * y⁻¹), map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 hy (θ z)
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    have hgL : g ∈ L := hUL hg
    exact (key ⟨g, hgL⟩).1 hg
  · intro hg
    have hgL' : (y : Γ) * g * (y : Γ)⁻¹ ∈ L := hUL hg
    have hgL : g ∈ L := by
      have : g = (y : Γ)⁻¹ * ((y : Γ) * g * (y : Γ)⁻¹) * y := by group
      rw [this]
      exact L.mul_mem (L.mul_mem (L.inv_mem y.2) hgL') y.2
    exact (key ⟨g, hgL⟩).2 hg

theorem mem_normalizer_map_of_mem {A B : Type*} [Group A] [Group B] (e : A ≃* B) {Y : Subgroup A}
    {a : A} (ha : a ∈ Subgroup.normalizer (Y : Set A)) :
    e a ∈ Subgroup.normalizer ((Y.map e.toMonoidHom : Subgroup B) : Set B) := by
  have h : Subgroup.zpowers a ≤ Subgroup.normalizer (Y : Set A) := by
    rw [Subgroup.zpowers_le]
    exact ha
  exact map_le_normalizer_map_of_le e h ⟨a, Subgroup.mem_zpowers a, rfl⟩

end Transport

section Natural

variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] {F : Type} [Field F]
  [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))]
  {H : Subgroup (V ≃ₗ[ZMod 2] V)} {r : ℕ} {Lc : Fin r → Subgroup (V ≃ₗ[ZMod 2] V)}

omit [Fintype F] [Fintype (ℙ F (Fin 2 → F))] [DecidableEq (ℙ F (Fin 2 → F))] in
theorem natural_overgroup (hnat : NaturalFamily H F r Lc) {i : Fin r}
    {U : Subgroup (V ≃ₗ[ZMod 2] V)} (hU : IsSylowTwoOf U (Lc i))
    (Y : Subgroup (V ≃ₗ[ZMod 2] V)) (hYL : Y ≤ Lc i) (hUY : U ≤ Y)
    (hy : ∃ y ∈ Y, y ∉ Subgroup.normalizer (U : Set (V ≃ₗ[ZMod 2] V))) : Y = Lc i := by
  obtain ⟨θ, β, x, -, hline⟩ := natural_coords hnat hU
  set A := (U.subgroupOf (Lc i)).map θ.toMonoidHom with hAdef
  have hA : ∀ g, g ∈ A ↔ ∃ t, x⁻¹ * g * x = uElt t := fun g => by
    have h1 := conj_mem_range_iff_fixes_line x g
    have h2 := mem_rootGroup_iff (x⁻¹ * g * x)
    rw [hline g]
    constructor
    · intro h
      exact h2.1 (h1.2 h)
    · intro h
      exact h1.1 (h2.2 h)
  have hgen : Subgroup.closure (Set.range (uElt (F := F)) ∪ Set.range (lElt (F := F))) = ⊤ := by
    have e : Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper F) ∪
        Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower F) =
        Set.range (uElt (F := F)) ∪ Set.range (lElt (F := F)) := rfl
    rw [← e, CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
  set Y0 := (Y.subgroupOf (Lc i)).map θ.toMonoidHom with hY0def
  have hY : ∀ t : F, x * uElt t * x⁻¹ ∈ Y0 := by
    intro t
    have hmem : x * uElt t * x⁻¹ ∈ A := (hA _).2 ⟨t, by group⟩
    obtain ⟨u, hu, hu'⟩ := hmem
    exact ⟨u, Subgroup.mem_subgroupOf.2 (hUY (Subgroup.mem_subgroupOf.1 hu)), hu'⟩
  obtain ⟨y, hyY, hyn⟩ := hy
  have hyL : y ∈ Lc i := hYL hyY
  have hy0 : θ ⟨y, hyL⟩ ∈ Y0 := ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.2 hyY, rfl⟩
  have hc : ((x⁻¹ * θ ⟨y, hyL⟩ * x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 := by
    intro hzero
    apply hyn
    exact mem_normalizer_of_map_equiv hU.1 θ
      (sl2_mem_normalizer_of_lower_zero x A hA (θ ⟨y, hyL⟩) hzero)
  have htop := sl2_overgroup_of_lower_ne hgen x Y0 hY (θ ⟨y, hyL⟩) hy0 hc
  refine le_antisymm hYL fun l hl => ?_
  have hl' : θ ⟨l, hl⟩ ∈ Y0 := by rw [htop]; trivial
  obtain ⟨z, hz, hzl⟩ := hl'
  have hzl' : z = ⟨l, hl⟩ := θ.injective hzl
  rw [hzl'] at hz
  exact Subgroup.mem_subgroupOf.1 hz

end Natural

section Main

theorem mem_normalizer_of_map_normalizer {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {Y : Subgroup A} {a : A}
    (h : e a ∈ Subgroup.normalizer ((Y.map e.toMonoidHom : Subgroup B) : Set B)) :
    a ∈ Subgroup.normalizer (Y : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h1 := Subgroup.mem_normalizer_iff.1 h (e y)
  have h2 : e a * e y * (e a)⁻¹ = e (a * y * a⁻¹) := by simp
  rw [h2] at h1
  have h3 : e y ∈ Y.map e.toMonoidHom ↔ y ∈ Y := Subgroup.mem_map_iff_mem e.injective
  have h4 : e (a * y * a⁻¹) ∈ Y.map e.toMonoidHom ↔ a * y * a⁻¹ ∈ Y :=
    Subgroup.mem_map_iff_mem e.injective
  rw [h3, h4] at h1
  exact h1

variable {G : Type} [Group G] [Finite G]

structure NatFamilyData (R M V : Subgroup G) {r : ℕ} (Lc : Fin r → Subgroup (MulAut V)) : Prop where
  normS : ∀ i, autOn (baum R) V ≤ Subgroup.normalizer (Lc i : Set (MulAut V))
  decomp : autOn (baum R) V = ⨆ j, autOn R V ⊓ Lc j
  commute : ∀ i j, i ≠ j → ∀ x ∈ Lc i, ∀ y ∈ Lc j, x * y = y * x
  others : ∀ i j, j ≠ i → ∀ x ∈ Lc j, ∀ u : V, (u : G) ∈ modComm V (Lc i) → x u = u
  faithful : ∀ i, ∀ x ∈ Lc i, (∀ u : V, (u : G) ∈ modComm V (Lc i) → x u = u) → x = 1
  overgroup : ∀ i, ∀ Y : Subgroup (MulAut V), Y ≤ Lc i → autOn R V ⊓ Lc i ≤ Y →
    (∃ y ∈ Y, y ∉ Subgroup.normalizer ((autOn R V ⊓ Lc i : Subgroup (MulAut V)) :
      Set (MulAut V))) → Y = Lc i
  M_ge : ∀ φ ∈ autOn (⊤ : Subgroup G) V,
    φ ∈ Subgroup.normalizer (autOn (baum R) V : Set (MulAut V)) → φ ∈ autOn M V
  O2 : ∀ i, pCoreOf 2 (Lc i) = ⊥
  center : ∀ i, ∀ z ∈ Lc i, (∀ y ∈ Lc i, y * z = z * y) → z = 1

theorem nat_family_data
    {R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting (⊤ : Subgroup G) R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn (⊤ : Subgroup G) V) r Lc)
    (hle : autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup (⊤ : Subgroup G)) V) :
    NatFamilyData R M V Lc := by
  classical
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ F (Fin 2 → F)) := Classical.decEq _
  have hred := hS.reduced
  have hX : (⊤ : Subgroup G) ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hX)
  obtain ⟨⟨W, hW1, hW2, hW3, θ, hmax, himg⟩⟩ := even_SL2_original_images hS hLc
  have hbridge := even_SL2_original_bridge hS hLc
  have hdata := natural_original_data hS hLc hle
  set ψ := (binPsi θ).toMonoidHom with hψ
  set L := oddOrderSubgroup (⊤ : Subgroup G) with hL
  have hbK : autOn L V = oddOrderSubgroup (autOn (⊤ : Subgroup G) V) := hbridge.K_eq
  have hKL : (autOn L V).map ψ = oddGen ((autOn (⊤ : Subgroup G) V).map ψ) := by
    rw [hbK]
    exact map_closure_odd (binPsi θ) (autOn (⊤ : Subgroup G) V)
  have hnat : NaturalFamily ((autOn (⊤ : Subgroup G) V).map ψ) F r
      (fun i => (Lc i).map ψ) := by
    rcases hmax.offenders.family.alternatives with ⟨hnat, -⟩ | ⟨hdel, -⟩
    · exact hnat
    · exfalso
      apply (himg.deleted hdel).1
      rw [← hKL]
      exact Subgroup.map_mono hle
  have layer := hmax.offenders.family.layer
  obtain ⟨hD1, -, -, -⟩ := himg.natural hnat
  have hnormS : ∀ i, autOn (baum R) V ≤ Subgroup.normalizer (Lc i : Set (MulAut V)) := by
    intro i
    rw [hdata.baum_eq]
    refine hle.trans ?_
    rw [hbridge.K_eq, hbridge.K_prod]
    refine iSup_le fun j => ?_
    by_cases hji : j = i
    · subst hji
      exact Subgroup.le_normalizer
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1
        (hbridge.commute j i hji)).trans (Subgroup.centralizer_le_normalizer _)
  have hdecomp : autOn (baum R) V = ⨆ j, autOn R V ⊓ Lc j := by
    apply Subgroup.map_injective (f := ψ) (binPsi θ).injective
    have h1 : (autOn (baum R) V).map ψ = ⨆ j, (autOn R V).map ψ ⊓ (Lc j).map ψ := by
      rw [← himg.baumann_eq]
      exact hD1
    rw [h1, Subgroup.map_iSup]
    refine iSup_congr fun j => ?_
    rw [Subgroup.map_inf _ _ _ (binPsi θ).injective]
  have hcommute : ∀ i j, i ≠ j → ∀ x ∈ Lc i, ∀ y ∈ Lc j, x * y = y * x := by
    intro i j hij x hx y hy
    have h1 : Lc i ≤ Subgroup.centralizer (Lc j : Set (MulAut V)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hbridge.commute i j hij)
    exact (Subgroup.mem_centralizer_iff.1 (h1 hx) y hy).symm
  have hothers : ∀ i j, j ≠ i → ∀ x ∈ Lc j, ∀ u : V, (u : G) ∈ modComm V (Lc i) → x u = u := by
    intro i j hji x hx u hu
    have hu' := (mem_modComm_iff θ (Lc i) u).1 hu
    have h1 := layer.others_fix i j hji (ψ x) (Subgroup.mem_map_of_mem ψ hx) (vecOf θ u) hu'
    have h2 : vecOf θ (x u) = vecOf θ u := by
      rw [← binPsi_vecOf]
      exact h1
    exact vecOf_injective θ h2
  have hfaithful : ∀ i, ∀ x ∈ Lc i, (∀ u : V, (u : G) ∈ modComm V (Lc i) → x u = u) → x = 1 := by
    intro i x hx hfix
    have h0 := layer.faithful_W i (ψ x) (Subgroup.mem_map_of_mem ψ hx) (fun v hv => by
      have hv0 : binPsi θ x v = v := by
        have h1 := hfix (elOf θ v) ((mem_modComm_iff θ (Lc i) (elOf θ v)).2 (by
          rw [vecOf_elOf]; exact hv))
        have h2 : vecOf θ (x (elOf θ v)) = vecOf θ (elOf θ v) := by rw [h1]
        rw [← binPsi_vecOf, vecOf_elOf] at h2
        exact h2
      show binPsi θ x v - v ∈ fixGL ((Lc i).map ψ)
      rw [hv0, sub_self]
      exact Submodule.zero_mem _)
    exact (binPsi θ).injective (by rw [map_one]; exact h0)
  have hover : ∀ i, ∀ Y : Subgroup (MulAut V), Y ≤ Lc i → autOn R V ⊓ Lc i ≤ Y →
      (∃ y ∈ Y, y ∉ Subgroup.normalizer ((autOn R V ⊓ Lc i : Subgroup (MulAut V)) :
        Set (MulAut V))) → Y = Lc i := by
    intro i Y hYL hUY hy
    obtain ⟨y, hyY, hyn⟩ := hy
    have hU : IsSylowTwoOf ((autOn R V).map ψ ⊓ (Lc i).map ψ) ((Lc i).map ψ) := hmax.U_sylow i
    have hUimg : (autOn R V ⊓ Lc i : Subgroup (MulAut V)).map ψ =
        (autOn R V).map ψ ⊓ (Lc i).map ψ := Subgroup.map_inf _ _ _ (binPsi θ).injective
    have key := natural_overgroup hnat hU (Y.map ψ) (Subgroup.map_mono hYL)
      (by rw [← hUimg]; exact Subgroup.map_mono hUY)
      ⟨ψ y, Subgroup.mem_map_of_mem ψ hyY, fun hmem => hyn
        (mem_normalizer_of_map_normalizer (binPsi θ) (by rw [hUimg]; exact hmem))⟩
    exact Subgroup.map_injective (f := ψ) (binPsi θ).injective key
  have hMge : ∀ φ ∈ autOn (⊤ : Subgroup G) V,
      φ ∈ Subgroup.normalizer (autOn (baum R) V : Set (MulAut V)) → φ ∈ autOn M V := by
    intro φ hφ hφn
    have hS' : (autOn (baum R) V).map ψ =
        (autOn R V).map ψ ⊓ oddGen ((autOn (⊤ : Subgroup G) V).map ψ) :=
      himg.baumann_eq.symm.trans (hD1.trans hmax.D_eq.symm)
    have h1 := mem_normalizer_map_of_mem (binPsi θ) hφn
    have h1' : ψ φ ∈ Subgroup.normalizer
        ((((autOn R V).map ψ ⊓ oddGen ((autOn (⊤ : Subgroup G) V).map ψ) :
          Subgroup (W ≃ₗ[ZMod 2] W))) : Set (W ≃ₗ[ZMod 2] W)) := by
      rw [← hS']
      exact h1
    have h2 : ψ φ ∈ (autOn M V).map ψ := by
      rw [hmax.M_eq_normalizer]
      exact ⟨h1', Subgroup.mem_map_of_mem ψ hφ⟩
    exact (Subgroup.mem_map_iff_mem (binPsi θ).injective).1 h2
  have hO2 : ∀ i, pCoreOf 2 (Lc i) = ⊥ := fun i =>
    le_bot_iff.1 ((pCoreOf_le_pCoreOf_of_isSubnormal (hLc.isComp i).2.1).trans
      (pCoreOf_autOn_eq_bot hS.reduced).le)
  have hcenter : ∀ i, ∀ z ∈ Lc i, (∀ y ∈ Lc i, y * z = z * y) → z = 1 := by
    intro i z hz hcomm
    have hz' : ψ z ∈ (Lc i).map ψ := Subgroup.mem_map_of_mem ψ hz
    have hmem : (⟨ψ z, hz'⟩ : ↥((Lc i).map ψ)) ∈ Subgroup.center ↥((Lc i).map ψ) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨y', hy'⟩
      obtain ⟨y, hy, rfl⟩ := hy'
      apply Subtype.ext
      show ψ y * ψ z = ψ z * ψ y
      rw [← map_mul, ← map_mul, hcomm y hy]
    rw [layer.center_trivial i, Subgroup.mem_bot] at hmem
    have h0 : ψ z = 1 := congrArg Subtype.val hmem
    exact (binPsi θ).injective (by rw [map_one]; exact h0)
  exact ⟨hnormS, hdecomp, hcommute, hothers, hfaithful, hover, hMge, hO2, hcenter⟩

end Main

end CFSG.QuasithinUnique.Setup.Lift
