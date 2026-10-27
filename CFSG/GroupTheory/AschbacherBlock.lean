module

public import CFSG.RankThree.PartOne.S12.PushingUp
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo
import CFSG.Quasithin.H13.NQCatSubnormalCore
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.GroupTheory

open CFSG CFSG.RankThree.PartOne Subgroup
open scoped commutatorElement

@[expose] def charNormalizers {G : Type} [Group G] (T : Subgroup G) : Set (Subgroup G) :=
  {H | ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic ∧
    H = normalizer (C : Set G)}

@[expose] def IsNaturalSLTwoFactor (B : Type) [Group B] (X Y : Subgroup B) (n : ℕ) : Prop :=
  ∃ (φ : (B ⧸ pCore 2 B) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
    (ψ : ↥X →* Multiplicative (Fin 2 → GaloisField 2 n)),
    Function.Surjective ψ ∧ ψ.ker = Y.subgroupOf X ∧
    ∀ (l u : B) (hu : u ∈ X) (hu' : l * u * l⁻¹ ∈ X),
      ψ ⟨l * u * l⁻¹, hu'⟩ = Multiplicative.ofAdd
        ((φ (l : B ⧸ pCore 2 B) : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
          (Multiplicative.toAdd (ψ ⟨u, hu⟩)))

@[expose] def IsNaturalAltFactor (B : Type) [Group B] (X Y : Subgroup B) (n : ℕ) : Prop :=
  ∃ (φ : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin (2 * n + 1)))
    (ψ : ↥X →* Multiplicative (Fin (2 * n + 1) → ZMod 2)),
    (∀ u, ∑ i, Multiplicative.toAdd (ψ u) i = 0) ∧
    (∀ v : Fin (2 * n + 1) → ZMod 2, ∑ i, v i = 0 → ∃ u, ψ u = Multiplicative.ofAdd v) ∧
    ψ.ker = Y.subgroupOf X ∧
    ∀ (l u : B) (hu : u ∈ X) (hu' : l * u * l⁻¹ ∈ X),
      ψ ⟨l * u * l⁻¹, hu'⟩ = Multiplicative.ofAdd (permActionTwo
        ((φ (l : B ⧸ pCore 2 B) : alternatingGroup (Fin (2 * n + 1))) : Equiv.Perm _)
        (Multiplicative.toAdd (ψ ⟨u, hu⟩)))

structure IsAschbacherBlockGomi {Y : Type} [Group Y] (B : Subgroup Y) : Prop where
  subnormal : B.IsSubnormal
  residual : oResidualTwo B = ⊤
  quotient : IsQuasisimple (B ⧸ pCore 2 B) ∨
    ((Nat.card (B ⧸ pCore 2 B)).Prime ∧ Odd (Nat.card (B ⧸ pCore 2 B)))
  chief : ∃ X Y₀ : Subgroup B, X.Normal ∧ Y₀.Normal ∧ Y₀ < X ∧ X ≤ pCore 2 B ∧
    Y₀ ≤ center B ∧ ⁅pCore 2 B, (⊤ : Subgroup B)⁆ ≤ X ∧
    (∀ N : Subgroup B, N.Normal → Y₀ ≤ N → N ≤ X → N = Y₀ ∨ N = X) ∧
    ¬ ⁅X, (⊤ : Subgroup B)⁆ ≤ Y₀ ∧
    ((∃ n, 2 ≤ n ∧ IsNaturalSLTwoFactor B X Y₀ n) ∨ (∃ n, 1 ≤ n ∧ IsNaturalAltFactor B X Y₀ n))
  comm_oTwo : ⁅pCore 2 Y, B⁆ ≤ omegaOneCenterIn (pCore 2 Y)

section Block

variable {Y : Type} [Group Y]

private theorem isCharacteristicP_two_of_isSubnormal [Finite Y] (hY : IsCharacteristicP 2 Y)
    {X : Subgroup Y} (hX : X.IsSubnormal) : IsCharacteristicP 2 ↥X := by
  have hTop : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup Y) := by
    rw [CFSG.QuasithinUnique.charTwo_iff_internal]
    have h1 : centralizer (CFSG.Open.pCore 2 Y : Set Y) ≤ CFSG.Open.pCore 2 Y := hY
    exact CFSG.RankThreeCoreUniqueness.Helpers.self_centralizing_pCore_of_mulEquiv 2
      Subgroup.topEquiv.symm h1
  exact CFSG.QuasithinUnique.charTwo_iff_internal.mp
    (CFSG.QuasithinUnique.CharTwo.of_isSubnormal hTop le_top (hX.comap _))

private theorem shortU_le_center_of_comm {B : Subgroup Y} (hB : B.IsSubnormal)
    (h : ⁅pCore 2 Y, B⁆ ≤ omegaOneCenterIn (pCore 2 Y)) :
    shortU B ≤ (center (pCore 2 B)).map (pCore 2 B).subtype := by
  have hmap := CFSG.Quasithin.H13.NQCat.map_pCore_le_pCore_of_isSubnormal' (p := 2) hB
  intro u hu
  have hP : u ∈ pCore 2 B := commutator_le_left _ _ hu
  have hUY : (u : Y) ∈ ⁅pCore 2 Y, B⁆ := by
    have h1 : (shortU B).map B.subtype ≤ ⁅pCore 2 Y, B⁆ := by
      rw [shortU, map_commutator]
      exact commutator_mono hmap (map_subtype_le _)
    exact h1 (mem_map_of_mem _ hu)
  obtain ⟨z, hz, hzu⟩ : (u : Y) ∈ (center (pCore 2 Y)).map (pCore 2 Y).subtype :=
    (closure_le _).mpr (fun x hx => hx.1) (h hUY)
  refine ⟨⟨u, hP⟩, mem_center_iff.mpr fun r => ?_, rfl⟩
  have hr : ((r : B) : Y) ∈ pCore 2 Y := hmap (mem_map_of_mem _ r.2)
  have e := congrArg Subtype.val (mem_center_iff.mp hz ⟨_, hr⟩)
  apply Subtype.ext
  apply Subtype.ext
  simp only [coe_mul, coe_subtype] at e hzu ⊢
  rw [← hzu]
  exact e

private theorem chief_facts {B : Type} [Group B] {X Y₀ : Subgroup B} [X.Normal] [Y₀.Normal]
    (hY₀X : Y₀ < X) (hXP : X ≤ pCore 2 B) (hY₀Z : Y₀ ≤ center B) (hUX : shortU B ≤ X)
    (hmin : ∀ N : Subgroup B, N.Normal → Y₀ ≤ N → N ≤ X → N = Y₀ ∨ N = X)
    (hnc : ¬ ⁅X, (⊤ : Subgroup B)⁆ ≤ Y₀) :
    X ⊓ center B = Y₀ ∧ shortU B ⊔ Y₀ = X := by
  haveI : (shortU B).Normal := by
    unfold shortU
    infer_instance
  refine ⟨?_, ?_⟩
  · rcases hmin (X ⊓ center B) inferInstance (le_inf hY₀X.le hY₀Z) inf_le_left with h | h
    · exact h
    · refine absurd (commutator_le.mpr fun x hx g _ => ?_) hnc
      have hx' : x ∈ X ⊓ center B := by
        rw [h]
        exact hx
      rw [commutatorElement_def, ← mem_center_iff.mp hx'.2 g, mul_inv_cancel_right,
        mul_inv_cancel]
      exact one_mem _
  · rcases hmin (shortU B ⊔ Y₀) inferInstance le_sup_right (sup_le hUX hY₀X.le) with h | h
    · exact absurd ((commutator_mono hXP le_rfl).trans (le_sup_left.trans h.le)) hnc
    · exact h

private theorem exists_inclusion_eq {B : Type} [Group B] {U X Y₀ : Subgroup B} [Y₀.Normal]
    (hUX : U ≤ X) (hUY : U ⊔ Y₀ = X) {M : Type*} [Monoid M] (ψ : ↥X →* M)
    (hker : ψ.ker = Y₀.subgroupOf X) (x : ↥X) : ∃ u : ↥U, ψ (inclusion hUX u) = ψ x := by
  have hx : (x : B) ∈ ((U ⊔ Y₀ : Subgroup B) : Set B) := by rw [hUY]; exact x.2
  rw [mul_normal] at hx
  obtain ⟨u, hu, y, hy, e⟩ := hx
  refine ⟨⟨u, hu⟩, ?_⟩
  have hyX : y ∈ X := hUY ▸ mem_sup_right hy
  have hy1 : ψ ⟨y, hyX⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
    exact hy
  have hx' : x = inclusion hUX ⟨u, hu⟩ * ⟨y, hyX⟩ := Subtype.ext e.symm
  rw [hx', map_mul, hy1, mul_one]

private theorem ker_comp_inclusion {B : Type} [Group B] {X Y₀ : Subgroup B}
    (hUX : shortU B ≤ X) (hXZ : X ⊓ center B = Y₀) (hY₀Z : Y₀ ≤ center B) {M : Type*} [Monoid M]
    (ψ : ↥X →* M) (hker : ψ.ker = Y₀.subgroupOf X) :
    (ψ.comp (inclusion hUX)).ker = (shortC B).subgroupOf (shortU B) := by
  ext u
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker, mem_subgroupOf,
    mem_subgroupOf, coe_inclusion, shortC, mem_inf]
  constructor
  · intro h
    exact ⟨u.2, hY₀Z h⟩
  · rintro ⟨-, hz⟩
    rw [← hXZ]
    exact ⟨hUX u.2, hz⟩

private theorem isNaturalSLTwoModule_of_factor {B : Type} [Group B] {X Y₀ : Subgroup B}
    [Y₀.Normal] {n : ℕ} (hUX : shortU B ≤ X) (hUY : shortU B ⊔ Y₀ = X)
    (hXZ : X ⊓ center B = Y₀) (hY₀Z : Y₀ ≤ center B) (h : IsNaturalSLTwoFactor B X Y₀ n) :
    IsNaturalSLTwoModule B n := by
  obtain ⟨φ, ψ, hsurj, hker, hact⟩ := h
  refine ⟨φ, ψ.comp (inclusion hUX), fun v => ?_, ker_comp_inclusion hUX hXZ hY₀Z ψ hker,
    fun l u hu hu' => hact l u (hUX hu) (hUX hu')⟩
  obtain ⟨x, rfl⟩ := hsurj v
  obtain ⟨u, hu⟩ := exists_inclusion_eq hUX hUY ψ hker x
  exact ⟨u, hu⟩

private theorem isNaturalAltModule_of_factor {B : Type} [Group B] {X Y₀ : Subgroup B}
    [Y₀.Normal] {n : ℕ} (hUX : shortU B ≤ X) (hUY : shortU B ⊔ Y₀ = X)
    (hXZ : X ⊓ center B = Y₀) (hY₀Z : Y₀ ≤ center B) (h : IsNaturalAltFactor B X Y₀ n) :
    IsNaturalAltModule B n := by
  obtain ⟨φ, ψ, hsum, hsurj, hker, hact⟩ := h
  refine ⟨φ, ψ.comp (inclusion hUX), fun u => hsum _, fun v hv => ?_,
    ker_comp_inclusion hUX hXZ hY₀Z ψ hker, fun l u hu hu' => hact l u (hUX hu) (hUX hu')⟩
  obtain ⟨x, hx⟩ := hsurj v hv
  obtain ⟨u, hu⟩ := exists_inclusion_eq hUX hUY ψ hker x
  exact ⟨u, hu.trans hx⟩

theorem IsAschbacherBlockGomi.isBlockInX [Finite Y] (hY : IsCharacteristicP 2 Y)
    {B : Subgroup Y} (hB : IsAschbacherBlockGomi B) : IsBlockInX B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, Y₀, hXn, hYn, hY₀X, hXP, hY₀Z, hUX, hmin, hnc, htype⟩ := hB.chief
  have hUX' : shortU B ≤ X := hUX
  obtain ⟨hXZ, hUY⟩ := chief_facts hY₀X hXP hY₀Z hUX' hmin hnc
  have hnz : shortC B < shortU B := by
    refine inf_lt_left.mpr fun hUZ => hY₀X.ne ?_
    rw [← hUY, eq_comm, sup_eq_right, ← hXZ]
    exact le_inf hUX' hUZ
  have hirr : ∀ N : Subgroup B, N.Normal → N ≤ shortU B → shortC B ≤ N →
      N = shortC B ∨ N = shortU B := by
    intro N hN hNU hCN
    haveI := hN
    rcases hmin (N ⊔ Y₀) inferInstance le_sup_right (sup_le (hNU.trans hUX') hY₀X.le) with h | h
    · refine Or.inl (le_antisymm (fun n hn => ⟨hNU hn, hY₀Z ?_⟩) hCN)
      rw [← h]
      exact mem_sup_left hn
    · refine Or.inr (le_antisymm hNU fun u hu => ?_)
      have hu' : u ∈ ((N ⊔ Y₀ : Subgroup B) : Set B) := by rw [h]; exact hUX' hu
      rw [mul_normal] at hu'
      obtain ⟨n, hn, y, hy, rfl⟩ := hu'
      have hyU : y ∈ shortU B := by
        simpa using (shortU B).mul_mem ((shortU B).inv_mem (hNU hn)) hu
      exact N.mul_mem hn (hCN ⟨hyU, hY₀Z hy⟩)
  have hS : IsShortGroup B :=
    { fitting_eq := (isCharacteristicP_iff_generalizedFitting_eq_pCore B 2).mp
        (isCharacteristicP_two_of_isSubnormal hY hB.subnormal)
      residual_eq := hB.residual
      quotient_type := hB.quotient.imp_right And.left
      U_le_center := shortU_le_center_of_comm hB.subnormal hB.comm_oTwo
      nonzero := hnz
      irreducible := hirr }
  refine ⟨hB.subnormal, hS, ?_⟩
  rcases htype with ⟨n, hn, h⟩ | ⟨n, hn, h⟩
  · exact Or.inr ⟨n, by omega, isNaturalSLTwoModule_of_factor hUX' hUY hXZ hY₀Z h⟩
  · exact Or.inl ⟨n, hn, isNaturalAltModule_of_factor hUX' hUY hXZ hY₀Z h⟩

end Block

end CFSG.GroupTheory

end
