module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239CoversM23Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Covers

open CFSG.Sporadic.Schreier CFSG.Blueprint TauCeti
open scoped Pointwise

section Split

variable {E : Type*} [Group E]

theorem stabilizer_eq_closure :
    MulAction.stabilizer M23g D23 = Subgroup.closure (Set.range yM) := by
  have hle : Subgroup.closure (Set.range yM) ≤ MulAction.stabilizer M23g D23 := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    fin_cases i
    · exact alphaG_fix
    · exact betaG_fix
  have hcl : Nat.card (Subgroup.closure (Set.range yM)) = 7920 :=
    card_closure_eq yM yM_rel1 yM_rel2 yM_ne_one
  have horb : 1288 ≤ (MulAction.orbit M23g D23).ncard := by
    have hsub : ((bfs 22 : Finset (Finset (Fin 23))) : Set (Finset (Fin 23))) ⊆
        MulAction.orbit M23g D23 := by
      intro s hs
      obtain ⟨a, ha⟩ := mem_bfs_orbit 22 s hs
      exact ⟨a, ha⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_coe_finset, bfs_card] at h1
  have hprod := Subgroup.index_mul_card (MulAction.stabilizer M23g D23)
  rw [MulAction.index_stabilizer, m23_card] at hprod
  have hstab : Nat.card (MulAction.stabilizer M23g D23) ≤ 7920 := by
    by_contra h
    have h' : 7921 ≤ Nat.card (MulAction.stabilizer M23g D23) := by omega
    have : 1288 * 7921 ≤ (MulAction.orbit M23g D23).ncard *
        Nat.card (MulAction.stabilizer M23g D23) := Nat.mul_le_mul horb h'
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcl]; exact hstab)).symm

theorem exists_splitData
    (π : E →* M23g) (hπ : Function.Surjective π)
    (hz : ∀ z, π z = 1 → z ∈ Subgroup.center E) (h2 : ∀ z, π z = 1 → z * z = 1) :
    Nonempty (SplitData π D23) := by
  classical
  obtain ⟨x, hxπ, hx1, hx2⟩ := m11_exists_lifts π hπ hz h2 yM yM_rel1 yM_rel2
  set K₁ : Subgroup E := Subgroup.closure (Set.range x) with hK₁
  have hKcard : Nat.card K₁ ≤ 7920 := card_closure_le x hx1 hx2
  have hKfin : Finite K₁ := finite_closure x hx1 hx2
  have himg : π '' Set.range x = Set.range yM := by
    ext g
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hxπ i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x i, ⟨i, rfl⟩, hxπ i⟩
  have hmap : K₁.map π = MulAction.stabilizer M23g D23 := by
    rw [hK₁, MonoidHom.map_closure, himg, stabilizer_eq_closure]
  set φ : K₁ →* M23g := π.comp K₁.subtype with hφ
  have hrange : φ.range = MulAction.stabilizer M23g D23 := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  have hcard7920 : Nat.card (MulAction.stabilizer M23g D23) = 7920 := by
    rw [stabilizer_eq_closure]
    exact card_closure_eq yM yM_rel1 yM_rel2 yM_ne_one
  have hfinM : Finite M23g := CFSG.Sporadic.Mathieu.fam_m23_simplicity.1
  have hrcard : Nat.card φ.range = 7920 := by rw [hrange]; exact hcard7920
  have hbij : Function.Bijective φ.rangeRestrict :=
    (MonoidHom.rangeRestrict_surjective φ).bijective_of_nat_card_le (by rw [hrcard]; exact hKcard)
  let ψ : φ.range ≃* K₁ := (MulEquiv.ofBijective φ.rangeRestrict hbij).symm
  let σ : M23g → E := fun g => if h : g ∈ φ.range then ((ψ ⟨g, h⟩ : K₁) : E) else 1
  have hmem : ∀ g : M23g, g • D23 = D23 → g ∈ φ.range := by
    intro g hg
    rw [hrange]
    exact MulAction.mem_stabilizer_iff.mpr hg
  refine ⟨⟨hz, h2, σ, ?_, ?_⟩⟩
  · intro g hg
    have h := hmem g hg
    simp only [σ, h, ↓reduceDIte]
    have := (MulEquiv.ofBijective φ.rangeRestrict hbij).apply_symm_apply ⟨g, h⟩
    have h3 := congrArg Subtype.val this
    exact h3
  · intro g g' hg hg'
    have h := hmem g hg
    have h' := hmem g' hg'
    have hgg' := hmem (g * g') (by rw [mul_smul, hg', hg])
    simp only [σ, h, h', hgg', ↓reduceDIte]
    have : (⟨g * g', hgg'⟩ : φ.range) = ⟨g, h⟩ * ⟨g', h'⟩ := rfl
    rw [this, map_mul]
    rfl

end Split

section Main

@[expose] def cycTypes (k : Fin 7) : List (Fin 9) := (cycCells k).map Prod.snd

@[expose] def cycOdd (k : Fin 7) : List (Fin 9) :=
  (List.finRange 9).filter fun i => ¬ Even ((cycTypes k).count i)

theorem cyc_odd_even (k : Fin 7) :
    ∀ i : Fin 9, Even ((cycTypes k).count i + (cycOdd k).count i) := by
  revert k
  decide

theorem expsum0_m23 :
    ∀ i : Fin 9, expsum 0 (m23Rw i) = ![2, 0, 23, 6, 0, 12, 15, 18, 15] i := by
  decide

theorem expsum1_m23 :
    ∀ i : Fin 9, expsum 1 (m23Rw i) = ![0, 4, 23, 12, 0, 8, 4, 30, 16] i := by
  decide

theorem p23_rel {X : Type*} [Group X] (y : Fin 2 → X) (h : ∀ w ∈ m23R, wordVal y w = 1) :
    ∀ v ∈ Sporadic.m23Presentation.relatorLetters,
      CFSG.Sporadic.Bridge.wordProd (fun i => if h : i < 2 then y ⟨i, h⟩ else 1) v = 1 := by
  intro v hv
  rw [m23_relatorLetters] at hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  have himg : ∀ i : Fin 2, (fun i => if h : i < 2 then y ⟨i, h⟩ else 1) i.val = y i := by
    intro i
    have hl := i.isLt
    simp only [hl, ↓reduceDIte]
  rw [wordProd_map_natLetter _ y himg]
  exact h w hw

noncomputable def p23Hom {X : Type*} [Group X] (y : Fin 2 → X) (h : ∀ w ∈ m23R, wordVal y w = 1) :
    Sporadic.m23Presentation.Group →* X :=
  PresentedGroup.toGroup
    (f := fun i : Fin Sporadic.m23Presentation.generatorCount =>
      (fun j : ℕ => if h : j < 2 then y ⟨j, h⟩ else 1) i.val)
    (CFSG.Sporadic.Bridge.lift_relator Sporadic.m23Presentation _ (p23_rel y h))

theorem p23Hom_of {X : Type*} [Group X] (y : Fin 2 → X) (h : ∀ w ∈ m23R, wordVal y w = 1)
    (i : Fin Sporadic.m23Presentation.generatorCount) :
    p23Hom y h (PresentedGroup.of i) =
      y (Fin.cast CFSG.Sporadic.Bridge.M23.generatorCount_eq i) := by
  have hi : i.val < 2 := by
    have := CFSG.Sporadic.Bridge.M23.generatorCount_eq
    omega
  unfold p23Hom
  rw [PresentedGroup.toGroup.of]
  simp only [hi, ↓reduceDIte]
  rfl

theorem p23Hom_range {X : Type*} [Group X] (y : Fin 2 → X) (h : ∀ w ∈ m23R, wordVal y w = 1) :
    (p23Hom y h).range = Subgroup.closure (Set.range y) := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨Fin.cast CFSG.Sporadic.Bridge.M23.generatorCount_eq i, (p23Hom_of y h i).symm⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of (Fin.cast CFSG.Sporadic.Bridge.M23.generatorCount_eq.symm i), by
      rw [p23Hom_of]; rfl⟩

theorem m23_pres_card : Finite Sporadic.m23Presentation.Group ∧
    Nat.card Sporadic.m23Presentation.Group ≤ 10200960 :=
  CFSG.Sporadic.Presentation.M23.finite_card_le

theorem cyc_hw
    (k : Fin 7) : ∀ w ∈ cycWords k, wordVal gM w.2 = 1 := by
  intro w hw
  unfold cycWords at hw
  obtain ⟨p, -, rfl⟩ := List.mem_map.mp hw
  exact m23_rel_i p.2

theorem exists_m23Rw {w : List Letter} (hw : w ∈ m23R) : ∃ i : Fin 9, m23Rw i = w := by
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hw
  have hn9 : n < 9 := hn
  refine ⟨⟨n, hn9⟩, ?_⟩
  unfold m23Rw
  exact List.getD_eq_getElem _ _ hn

theorem m23_cover_exp2
    {E : Type*} [Group E] [Finite E] (π : E →* M23g)
    (hπ : Function.Surjective π) (hz : ∀ z, π z = 1 → z ∈ Subgroup.center E)
    (h2 : ∀ z, π z = 1 → z * z = 1) (hperf : commutator E = ⊤) : π.ker = ⊥ := by
  classical
  obtain ⟨S⟩ := exists_splitData π hπ hz h2
  choose x hx using fun i => hπ (gM i)
  have hxg : (fun i => π (x i)) = gM := funext hx
  set c : Fin 9 → E := fun i => wordVal x (m23Rw i) with hc
  have hcker : ∀ i, π (c i) = 1 := by
    intro i
    simp only [hc]
    rw [map_wordVal, hxg]
    exact m23_rel_i i
  have hcc : ∀ i, c i ∈ Subgroup.center E := fun i => hz _ (hcker i)
  have hcsq : ∀ i, c i * c i = 1 := fun i => h2 _ (hcker i)
  have hrel : ∀ k : Fin 7, ((cycOdd k).map c).prod = 1 := by
    intro k
    have h := cycle_relation S hπ hx (cycWords k) (cyc_hw k) (cyc_orbit k) (cyc_even k)
    have hmap : (cycWords k).map (fun w => wordVal x w.2) = (cycTypes k).map c := by
      simp [cycWords, cycTypes, List.map_map, Function.comp_def, hc]
    rw [hmap] at h
    have hev : ∀ i ∈ cycTypes k ++ cycOdd k, Even ((cycTypes k ++ cycOdd k).count i) := by
      intro i _
      rw [List.count_append]
      exact cyc_odd_even k i
    have h3 := prod_eq_one_of_even c hcc hcsq _ hev
    rw [List.map_append, List.prod_append, h, one_mul] at h3
    exact h3
  have e0 : cycOdd 0 = [5] := by decide
  have e1 : cycOdd 1 = [4] := by decide
  have e2 : cycOdd 2 = [3] := by decide
  have e3 : cycOdd 3 = [0] := by decide
  have e4 : cycOdd 4 = [1] := by decide
  have e5 : cycOdd 5 = [7] := by decide
  have e6 : cycOdd 6 = [0, 1, 3, 6, 8] := by decide
  have r0 : c 5 = 1 := by have := hrel 0; rw [e0] at this; simpa using this
  have r1 : c 4 = 1 := by have := hrel 1; rw [e1] at this; simpa using this
  have r2 : c 3 = 1 := by have := hrel 2; rw [e2] at this; simpa using this
  have r3 : c 0 = 1 := by have := hrel 3; rw [e3] at this; simpa using this
  have r4 : c 1 = 1 := by have := hrel 4; rw [e4] at this; simpa using this
  have r5 : c 7 = 1 := by have := hrel 5; rw [e5] at this; simpa using this
  have r6 : c 6 * c 8 = 1 := by
    have := hrel 6
    rw [e6] at this
    simpa [r3, r4, r2] using this
  set z : Fin 2 → E := ![c 6, c 2 * c 6] with hzdef
  have hzc : ∀ i, z i ∈ Subgroup.center E := by
    intro i
    fin_cases i
    · exact hcc 6
    · exact Subgroup.mul_mem _ (hcc 2) (hcc 6)
  have hzsq : ∀ i, z i * z i = 1 := by
    intro i
    fin_cases i
    · exact hcsq 6
    · show c 2 * c 6 * (c 2 * c 6) = 1
      have h26 : c 6 * c 2 = c 2 * c 6 := (Subgroup.mem_center_iff.mp (hcc 2) (c 6))
      calc c 2 * c 6 * (c 2 * c 6) = c 2 * (c 6 * c 2) * c 6 := by simp only [mul_assoc]
        _ = c 2 * (c 2 * c 6) * c 6 := by rw [h26]
        _ = (c 2 * c 2) * (c 6 * c 6) := by simp only [mul_assoc]
        _ = 1 := by rw [hcsq 2, hcsq 6, one_mul]
  have hzker : ∀ i, π (z i) = 1 := by
    intro i
    fin_cases i
    · exact hcker 6
    · show π (c 2 * c 6) = 1
      rw [map_mul, hcker 2, hcker 6, one_mul]
  set x' : Fin 2 → E := fun i => x i * z i with hx'def
  have hx' : ∀ i, π (x' i) = gM i := by
    intro i
    simp only [hx'def, map_mul, hx, hzker, mul_one]
  have hrel' : ∀ i : Fin 9, wordVal x' (m23Rw i) = 1 := by
    intro i
    rw [hx'def, wordVal_adjust_sq x z hzc hzsq, expsum0_m23 i, expsum1_m23 i]
    show c i * _ = 1
    fin_cases i
    · simpa [Int.even_iff] using r3
    · simpa [Int.even_iff] using r4
    ·
      simp only [Int.even_iff]
      norm_num
      show c 2 * (c 6 * (c 2 * c 6)) = 1
      have h26 : c 6 * c 2 = c 2 * c 6 := (Subgroup.mem_center_iff.mp (hcc 2) (c 6))
      calc c 2 * (c 6 * (c 2 * c 6)) = c 2 * (c 6 * c 2) * c 6 := by simp only [mul_assoc]
        _ = c 2 * (c 2 * c 6) * c 6 := by rw [h26]
        _ = (c 2 * c 2) * (c 6 * c 6) := by simp only [mul_assoc]
        _ = 1 := by rw [hcsq 2, hcsq 6, one_mul]
    · simpa [Int.even_iff] using r2
    · simpa [Int.even_iff] using r1
    · simpa [Int.even_iff] using r0
    · simp only [Int.even_iff]
      norm_num
      show c 6 * c 6 = 1
      exact hcsq 6
    · simpa [Int.even_iff] using r5
    · simp only [Int.even_iff]
      norm_num
      show c 8 * c 6 = 1
      have h68 : c 8 * c 6 = c 6 * c 8 := (Subgroup.mem_center_iff.mp (hcc 6) (c 8))
      rw [h68]
      exact r6
  have hrelx' : ∀ w ∈ m23R, wordVal x' w = 1 := by
    intro w hw
    obtain ⟨i, rfl⟩ := exists_m23Rw hw
    exact hrel' i
  have himg : π '' Set.range x' = Set.range gM := by
    ext g
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hx' i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨x' i, ⟨i, rfl⟩, hx' i⟩
  have hclos : Subgroup.closure (Set.range x') = ⊤ :=
    closure_eq_top_of_lifts π hz hperf _ (by rw [himg]; exact closure_gM)
  have hsurj : Function.Surjective (p23Hom x' hrelx') :=
    MonoidHom.range_eq_top.mp (by rw [p23Hom_range, hclos])
  obtain ⟨hfin, hcard⟩ := m23_pres_card
  have hE : Nat.card E ≤ 10200960 := (Nat.card_le_card_of_surjective _ hsurj).trans hcard
  have hprod := card_eq_card_mul_card_ker π hπ
  rw [m23_card] at hprod
  have hker : Nat.card π.ker = 1 := by
    have hpos : 0 < Nat.card π.ker := Nat.card_pos
    nlinarith
  exact Subgroup.card_eq_one.mp hker

end Main

end CFSG.QuasithinUnique.Vol2Native.L239.Covers
