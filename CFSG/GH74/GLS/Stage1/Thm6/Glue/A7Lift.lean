module

public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Rank
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.A7CoreCond
public import CFSG.GH74.GLS.Stage1.Thm6.Lift
public import CFSG.GH74.GLS.IVK.Statements.Sec1A7
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.Conf
public import CFSG.GH74.GLS.Stage1.Thm6.Glue.KFacts
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.After
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Lemma12_7
public import CFSG.GH74.GLS.Stage1.Thm6.Setup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Glue.A7

open Subgroup CFSG CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

local notation "S₇" => Equiv.Perm (Fin 7)
local notation "A₇" => alternatingGroup (Fin 7)

section Generic

theorem isEA_map_hom {X Y : Type*} [Group X] [Group Y] {V : Subgroup X} (f : X →* Y)
    (hV : Dihedral.IsEA V) : Dihedral.IsEA (V.map f) := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← map_mul, (hV a ha).1, map_one]
  · rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, (hV a ha).2 b hb]

theorem isEA_of_isElementaryAbelian {X : Type*} [Group X] {A : Subgroup X}
    (hA : IsElementaryAbelian 2 ↥A) : Dihedral.IsEA A := by
  intro a ha
  refine ⟨?_, fun b hb => ?_⟩
  · have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    rwa [pow_two] at this
  · have := (IsMulCommutative.is_comm (M := ↥A)).comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this

theorem isFourSubgroup_of_isEA {X : Type} [Group X] {U : Subgroup X} (hU : Dihedral.IsEA U)
    (hc : Nat.card U = 4) : IVK.IsFourSubgroup U := by
  refine ⟨?_, hc⟩
  have hcomm : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext ((hU a a.2).2 b b.2)⟩⟩
  exact { toIsMulCommutative := hcomm
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 (fun g => by
            have := (hU g g.2).1
            exact Subtype.ext (by simpa [pow_two] using this)) }

theorem exists_elemAb_of_pRank_eq {X : Type*} [Group X] [Finite X] {r : ℕ} (h : pRank 2 X = r) :
    ∃ A : Subgroup X, IsElementaryAbelian 2 ↥A ∧ Nat.card A = 2 ^ r := by
  have hne : {r : ℕ | ∃ A : Subgroup X, IsElementaryAbelian 2 ↥A ∧ Nat.card A = 2 ^ r}.Nonempty :=
    ⟨0, ⊥, by
      have : IsElementaryAbelian 2 ↥(⊥ : Subgroup X) :=
        isElementaryAbelian_of_isEA (fun a ha => by
          have : a = 1 := by simpa using ha
          subst this; simp)
      exact this, by simp⟩
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup X, IsElementaryAbelian 2 ↥A ∧
      Nat.card A = 2 ^ r} := by
    refine ⟨Nat.card X, ?_⟩
    rintro s ⟨B, -, hB⟩
    calc s ≤ 2 ^ s := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card X := Subgroup.card_le_card_group B
  have hmem := Nat.sSup_mem hne hbdd
  rw [show pRank 2 X = sSup {r : ℕ | ∃ A : Subgroup X, IsElementaryAbelian 2 ↥A ∧
      Nat.card A = 2 ^ r} from rfl] at h
  rw [h] at hmem
  exact hmem

theorem exists_four_of_comm_invol {A : Type*} [Group A] {s w : A} (hs : s * s = 1)
    (hw : w * w = 1) (hsw : s * w = w * s) (hs1 : s ≠ 1) (hw1 : w ≠ 1) (hne : s ≠ w) :
    ∃ V : Subgroup A, Dihedral.IsEA V ∧ Nat.card V = 4 ∧
      (∀ g ∈ V, g = 1 ∨ g = s ∨ g = w ∨ g = s * w) ∧ s ∈ V ∧ w ∈ V := by
  have hws : w * s = s * w := hsw.symm
  have h1 : s * (s * w) = w := by rw [← mul_assoc, hs, one_mul]
  have h2 : w * (s * w) = s := by rw [← mul_assoc, hws, mul_assoc, hw, mul_one]
  have h3 : s * w * s = w := by rw [mul_assoc, hws, ← mul_assoc, hs, one_mul]
  have h4 : s * w * w = s := by rw [mul_assoc, hw, mul_one]
  have h5 : s * w * (s * w) = 1 := by rw [mul_assoc, h2, hs]
  let V : Subgroup A :=
    { carrier := {g | g = 1 ∨ g = s ∨ g = w ∨ g = s * w}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq] at ha hb ⊢
        rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
          simp [hs, hw, hws, h1, h2, h3, h4, h5]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_ofPred_eq] at ha ⊢
        rcases ha with rfl | rfl | rfl | rfl
        · simp
        · rw [inv_eq_of_mul_eq_one_right hs]; simp
        · rw [inv_eq_of_mul_eq_one_right hw]; simp
        · rw [inv_eq_of_mul_eq_one_right h5]; simp }
  have hmem : ∀ g, g ∈ V ↔ g = 1 ∨ g = s ∨ g = w ∨ g = s * w := fun g => Iff.rfl
  refine ⟨V, ?_, ?_, fun g hg => (hmem g).1 hg, (hmem s).2 (Or.inr (Or.inl rfl)),
    (hmem w).2 (Or.inr (Or.inr (Or.inl rfl)))⟩
  · intro a ha
    refine ⟨?_, fun b hb => ?_⟩
    · rcases (hmem a).1 ha with rfl | rfl | rfl | rfl <;> simp [hs, hw, h5]
    · rcases (hmem a).1 ha with rfl | rfl | rfl | rfl <;>
        rcases (hmem b).1 hb with rfl | rfl | rfl | rfl <;>
        first | rfl | simp | exact hsw | exact hsw.symm | rw [h1, h3] | rw [h3, h1] | rw [h2, h4]
  · have hset : (V : Set A) = {1, s, w, s * w} := by
      ext g; simp [hmem]
    have hc : Nat.card V = (V : Set A).ncard := Nat.card_coe_set_eq _
    rw [hc, hset]
    have d1 : (1 : A) ≠ s := fun h => hs1 h.symm
    have d2 : (1 : A) ≠ w := fun h => hw1 h.symm
    have d3 : (1 : A) ≠ s * w := fun h => hne (by
      have h' := mul_eq_one_iff_eq_inv.1 h.symm
      rw [h', inv_eq_of_mul_eq_one_right hw])
    have d5 : s ≠ s * w := fun h => hw1 (mul_left_cancel (a := s) (by rw [mul_one]; exact h)).symm
    have d6 : w ≠ s * w := fun h => hs1 (mul_right_cancel (b := w) (by rw [one_mul]; exact h)).symm
    rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair d6]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, d5⟩
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨d1, d2, d3⟩

theorem exists_three_cycle_action {Y : Type*} [Group Y] {W : Subgroup Y} (hW : Dihedral.IsEA W)
    (hc : Nat.card W = 4)
    (hY : Nonempty (Y ≃* alternatingGroup (Fin 4)) ∨ Nonempty (Y ≃* Equiv.Perm (Fin 4))) :
    ∃ m : Y, m ^ 3 = 1 ∧ ∃ w ∈ W, m * w * m⁻¹ ≠ w := by
  obtain ⟨a, ha, -, -, ha1, -, -⟩ := Dihedral.exists_two_ne_one W hc
  have hcA : ∃ c : alternatingGroup (Fin 4), c ^ 3 = 1 ∧ ∀ w : alternatingGroup (Fin 4),
      w * w = 1 → w ≠ 1 → c * w * c⁻¹ ≠ w := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      by decide, by decide⟩
  have hcS : ∃ c : Equiv.Perm (Fin 4), c ^ 3 = 1 ∧ ∀ w : Equiv.Perm (Fin 4),
      w * w = 1 → w ≠ 1 → c * w * c⁻¹ ≠ w := by
    refine ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide, by decide⟩
  rcases hY with ⟨⟨e₂⟩⟩ | ⟨⟨e₂⟩⟩
  · obtain ⟨c, hc3, hcw⟩ := hcA
    refine ⟨e₂.symm c, by rw [← map_pow, hc3, map_one], a, ha, fun h => ?_⟩
    apply hcw (e₂ a) (by rw [← map_mul, (hW a ha).1, map_one])
      (fun h1 => ha1 (e₂.injective (by rw [h1, map_one])))
    have := congrArg e₂ h
    simpa using this
  · obtain ⟨c, hc3, hcw⟩ := hcS
    refine ⟨e₂.symm c, by rw [← map_pow, hc3, map_one], a, ha, fun h => ?_⟩
    apply hcw (e₂ a) (by rw [← map_mul, (hW a ha).1, map_one])
      (fun h1 => ha1 (e₂.injective (by rw [h1, map_one])))
    have := congrArg e₂ h
    simpa using this

end Generic

theorem exists_three_elem_normalizing (hf : IVK.IVK_1_1f) {U : Subgroup S₇} (hU : U ≤ A₇)
    (hEA : Dihedral.IsEA U) (hc : Nat.card U = 4) :
    ∃ m : S₇, m ^ 3 = 1 ∧ m ∈ A₇ ∧ (∀ y : S₇, y ∈ U ↔ m * y * m⁻¹ ∈ U) ∧
      ∃ w ∈ U, m * w * m⁻¹ ≠ w := by
  rcases hf U hU (isFourSubgroup_of_isEA hEA hc) with ⟨⟨hY⟩⟩ | ⟨A, X, t, hN, hUA, -, -, -, -, ⟨hA4⟩, -, -⟩
  ·
    let M : Subgroup S₇ := normalizer (U : Set S₇) ⊓ A₇
    have hUM : U ≤ M := fun u hu => ⟨le_normalizer hu, hU hu⟩
    obtain ⟨mY, hmY3, w, hw, hmw⟩ := exists_three_cycle_action (Y := ↥M) (W := U.subgroupOf M)
      (isEA_subgroupOf' hEA) (by rw [card_subgroupOf hUM]; exact hc) (Or.inr ⟨hY⟩)
    refine ⟨(mY : S₇), by simpa using congrArg Subtype.val hmY3, mY.2.2,
      fun y => Subgroup.mem_normalizer_iff.1 mY.2.1 y, (w : S₇), Subgroup.mem_subgroupOf.1 hw,
      fun hh => hmw (Subtype.ext (by simpa using hh))⟩
  ·
    have hAN : A ≤ normalizer (U : Set S₇) ⊓ A₇ := by
      rw [hN]; exact le_trans le_sup_left le_sup_left
    obtain ⟨mY, hmY3, w, hw, hmw⟩ := exists_three_cycle_action (Y := ↥A) (W := U.subgroupOf A)
      (isEA_subgroupOf' hEA) (by rw [card_subgroupOf hUA]; exact hc) (Or.inl ⟨hA4⟩)
    refine ⟨(mY : S₇), by simpa using congrArg Subtype.val hmY3, (hAN mY.2).2,
      fun y => Subgroup.mem_normalizer_iff.1 (hAN mY.2).1 y, (w : S₇),
      Subgroup.mem_subgroupOf.1 hw, fun hh => hmw (Subtype.ext (by simpa using hh))⟩

variable {G : Type} [Group G]

theorem Ox_odd [Finite G] (x : G) : ¬ 2 ∣ Nat.card (Ox x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := pPrimeCore_coprime_card (p := 2) (G := ↥(Cx x))
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 this

theorem mem_map_mk_iff {x : G} {V : Subgroup G} {y : CentralizerBar x} :
    y ∈ (V.subgroupOf (Cx x)).map (QuotientGroup.mk' (Ox x)) ↔ ∃ g ∈ V, ∃ hg : g ∈ Cx x,
      (QuotientGroup.mk ⟨g, hg⟩ : CentralizerBar x) = y := by
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g'.1, hg', g'.2, rfl⟩
  · rintro ⟨g, hg, hgC, rfl⟩
    exact ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩

theorem card_map_mk_of_inf_eq_bot {C : Type*} [Group C] (N : Subgroup C) [N.Normal]
    (A : Subgroup C) (h : A ⊓ N = ⊥) :
    Nat.card (A.map (QuotientGroup.mk' N)) = Nat.card A := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun a : A => (⟨QuotientGroup.mk' N a, a, a.2, rfl⟩ : A.map (QuotientGroup.mk' N))) ⟨?_, ?_⟩)
  · intro a b hab
    have h1 : (QuotientGroup.mk' N) (a : C) = (QuotientGroup.mk' N) (b : C) :=
      congrArg Subtype.val hab
    have h2 : (a : C)⁻¹ * b ∈ N := by
      rw [← QuotientGroup.eq]; exact h1
    have h3 : (a : C)⁻¹ * b ∈ A ⊓ N := ⟨A.mul_mem (A.inv_mem a.2) b.2, h2⟩
    rw [h, Subgroup.mem_bot] at h3
    exact Subtype.ext (inv_mul_eq_one.1 h3)
  · rintro ⟨y, a, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩

theorem exists_lift_elemAb [Finite G] (x : G) {Eb : Subgroup (CentralizerBar x)}
    (hEb : Dihedral.IsEA Eb) :
    ∃ E : Subgroup G, E ≤ Cx x ∧ IsElemAb2 E ∧ Nat.card E = Nat.card Eb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥Eb := fun g => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using (hEb g g.2).1⟩
  obtain ⟨A, -, hAE, hAN⟩ := exists_lift_pSubgroup (Ox x) (Ox_odd x) Eb hp
  have hker : ∀ a ∈ A, QuotientGroup.mk' (Ox x) a = 1 → a = 1 := by
    intro a ha h1
    have : a ∈ A ⊓ Ox x := ⟨ha, (QuotientGroup.eq_one_iff a).1 h1⟩
    rw [hAN, Subgroup.mem_bot] at this
    exact this
  have hmemE : ∀ a ∈ A, QuotientGroup.mk' (Ox x) a ∈ Eb := fun a ha => hAE ▸ ⟨a, ha, rfl⟩
  refine ⟨A.map (Cx x).subtype, fun g ⟨a, _, hag⟩ => hag ▸ a.2, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, ?_⟩
    · have : a * a = 1 := hker _ (A.mul_mem ha ha) (by
        rw [map_mul]; exact (hEb _ (hmemE a ha)).1)
      simpa using congrArg Subtype.val this
    · rintro _ ⟨b, hb, rfl⟩
      have : a * b * (b * a)⁻¹ = 1 := hker _ (A.mul_mem (A.mul_mem ha hb) (A.inv_mem (A.mul_mem hb ha)))
        (by rw [map_mul, map_mul, map_inv, map_mul, (hEb _ (hmemE a ha)).2 _ (hmemE b hb)]; group)
      have h2 := mul_inv_eq_one.1 this
      simpa using congrArg Subtype.val h2
  · rw [Subgroup.card_map_of_injective (Cx x).subtype_injective, ← hAE]
    exact (card_map_mk_of_inf_eq_bot (Ox x) A hAN).symm

theorem exists_E16 [Finite G] {x u : G} (hx : x * x = 1) (hx1 : x ≠ 1) {T : Subgroup G}
    (hT : IsSylow2In T (Cx x)) (hxT : x ∈ T) (huT : u ∈ T) (hu2 : u * u = 1)
    {Kb : Subgroup (CentralizerBar x)} [Kb.Normal] (hxK : x ∉ Kg x Kb) (huK : u ∉ Kg x Kb)
    (huxK : u * x ∉ Kg x Kb) (hux : u ≠ x) {Vb : Subgroup (CentralizerBar x)}
    (hVb : Dihedral.IsEA Vb) (hcb : Nat.card Vb = 4) (hVbK : ∀ g ∈ Vb, g ∈ Kb)
    (hcommU : ∀ g ∈ Vb, pr x u * g = g * pr x u) :
    ∃ E : Subgroup G, E ≤ Cx x ∧ IsElemAb2 E ∧ Nat.card E = 16 := by
  have huC := hT.1 huT
  have ha2 : pr x u * pr x u = 1 := by rw [← pr_mul x huC huC, hu2, pr_one]
  have hb2 : pr x x * pr x x = 1 := by rw [← pr_mul x (x_mem_Cx x) (x_mem_Cx x), hx, pr_one]
  have hab : pr x u * pr x x = pr x x * pr x u := (pr_x_central x (pr x u)).symm
  have hu1 : u ≠ 1 := fun h1 => huK (h1 ▸ (Kg x Kb).one_mem)
  have ha1 : pr x u ≠ 1 := fun h1 => hu1 (eq_one_of_pr_eq_one x hT huT huC h1)
  have hb1 : pr x x ≠ 1 := fun h1 => hx1 (eq_one_of_pr_eq_one x hT hxT (x_mem_Cx x) h1)
  have hne : pr x u ≠ pr x x := by
    intro h1
    apply hux
    have h2 : u * x⁻¹ = 1 := by
      apply eq_one_of_pr_eq_one x hT (T.mul_mem huT (T.inv_mem hxT))
        (mul_mem huC (inv_mem (x_mem_Cx x)))
      rw [pr_mul x huC (inv_mem (x_mem_Cx x)), pr_inv x (x_mem_Cx x), h1, mul_inv_cancel]
    exact mul_inv_eq_one.1 h2
  obtain ⟨D₁, hD₁, hc₁', hD₁el, haD, hbD⟩ := exists_four_of_comm_invol ha2 hb2 hab ha1 hb1 hne
  have hcomm : ∀ g ∈ D₁, ∀ v ∈ Vb, g * v = v * g := by
    intro g hg v hv
    rcases hD₁el g hg with rfl | rfl | rfl | rfl
    · simp
    · exact hcommU v hv
    · exact pr_x_central x v
    · calc pr x u * pr x x * v = pr x u * (pr x x * v) := by rw [mul_assoc]
        _ = pr x u * (v * pr x x) := by rw [pr_x_central x v]
        _ = (pr x u * v) * pr x x := by rw [← mul_assoc]
        _ = (v * pr x u) * pr x x := by rw [hcommU v hv]
        _ = v * (pr x u * pr x x) := by rw [mul_assoc]
  have hinter : D₁ ⊓ Vb = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgD, hgV⟩
    have hgK := hVbK g hgV
    rw [Subgroup.mem_bot]
    rcases hD₁el g hgD with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd ((mem_Kg x Kb).2 ⟨huC, hgK⟩) huK
    · exact absurd ((mem_Kg x Kb).2 ⟨x_mem_Cx x, hgK⟩) hxK
    · exact absurd ((mem_Kg x Kb).2 ⟨mul_mem huC (x_mem_Cx x), by
        rw [pr_mul x huC (x_mem_Cx x)]; exact hgK⟩) huxK
  let ψ : ↥D₁ × ↥Vb →* CentralizerBar x :=
    MonoidHom.noncommCoprod D₁.subtype Vb.subtype (fun m n => hcomm m m.2 n n.2)
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m, n⟩ hmn
    have h1 : (m : CentralizerBar x) * n = 1 := hmn
    have h2 : (m : CentralizerBar x) = (n : CentralizerBar x)⁻¹ := mul_eq_one_iff_eq_inv.1 h1
    have h3 : (m : CentralizerBar x) ∈ D₁ ⊓ Vb := ⟨m.2, h2 ▸ Vb.inv_mem n.2⟩
    rw [hinter, Subgroup.mem_bot] at h3
    have hm1 : m = 1 := Subtype.ext h3
    have hn1 : (n : CentralizerBar x) = 1 := by
      rw [h3, one_mul] at h1; exact h1
    exact Prod.ext hm1 (Subtype.ext hn1)
  have hEb : Dihedral.IsEA ψ.range := by
    rintro _ ⟨⟨m, n⟩, rfl⟩
    have hmm : (m : CentralizerBar x) * m = 1 := (hD₁ m m.2).1
    have hnn : (n : CentralizerBar x) * n = 1 := (hVb n n.2).1
    have hmn : (m : CentralizerBar x) * n = n * m := hcomm m m.2 n n.2
    refine ⟨?_, ?_⟩
    · show (m : CentralizerBar x) * n * ((m : CentralizerBar x) * n) = 1
      calc (m : CentralizerBar x) * n * (m * n) = m * (n * m) * n := by simp only [mul_assoc]
        _ = m * (m * n) * n := by rw [← hmn]
        _ = (m * m) * (n * n) := by simp only [mul_assoc]
        _ = 1 := by rw [hmm, hnn, mul_one]
    · rintro _ ⟨⟨m', n'⟩, rfl⟩
      show (m : CentralizerBar x) * n * ((m' : CentralizerBar x) * n') =
        (m' : CentralizerBar x) * n' * ((m : CentralizerBar x) * n)
      have c1 : (m : CentralizerBar x) * m' = m' * m := (hD₁ m m.2).2 m' m'.2
      have c2 : (n : CentralizerBar x) * n' = n' * n := (hVb n n.2).2 n' n'.2
      have c3 : (m : CentralizerBar x) * n' = n' * m := hcomm m m.2 n' n'.2
      have c4 : (m' : CentralizerBar x) * n = n * m' := hcomm m' m'.2 n n.2
      calc (m : CentralizerBar x) * n * (m' * n') = m * (n * m') * n' := by simp only [mul_assoc]
        _ = m * (m' * n) * n' := by rw [← c4]
        _ = (m * m') * (n * n') := by simp only [mul_assoc]
        _ = (m' * m) * (n' * n) := by rw [c1, c2]
        _ = m' * (m * n') * n := by simp only [mul_assoc]
        _ = m' * (n' * m) * n := by rw [c3]
        _ = m' * n' * (m * n) := by simp only [mul_assoc]
  have hcardEb : Nat.card ψ.range = 16 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv, Nat.card_prod, hc₁', hcb]
  obtain ⟨E, hEC, hE, hEcard⟩ := exists_lift_elemAb x hEb
  exact ⟨E, hEC, hE, by rw [hEcard, hcardEb]⟩

end CFSG.GH74.GLS.Stage1.Thm6.Glue.A7
