module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegreeEightRankOneExclusion
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullNormalizerSylowControl
public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsAut
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.SteinbergBX

open Subgroup
open CFSG.Semidihedral.Local
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.DegreeEight (subVal subVal_of_mem
  subVal_of_notMem subVal_conj multiplicative_zmod_two_cases one_ne_ofAdd_one rightCosetMul_one
  rightCosetMul_mul)
open CFSG.LocalAnalysis.ComponentInitial.BinarySymThreeOrbit (isElemAbelian_map
  isPGroup_of_isElemAbelian mem_map_conj card_map_conj)
open CFSG.Assembly (IsElemAbelian)
open scoped commutatorElement

namespace TwoFactor

section Transfer

variable {G : Type*} [Group G]

theorem transfer_eq_ofAdd_one_of_odd_index [Finite G] {M : Subgroup G} {z : G} (hzz : z * z = 1) (hodd : Odd M.index) (χ : M →* Multiplicative (ZMod 2))
    (hfus : ∀ x : G, x * z * x⁻¹ ∈ M → Odd (M.relIndex (centralizer {x * z * x⁻¹})) →
      subVal χ (x * z * x⁻¹) = Multiplicative.ofAdd 1) :
    χ.transfer z = Multiplicative.ofAdd 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  let _ : Fintype (Quotient (QuotientGroup.rightRel M)) := Fintype.ofFinite _
  set y : Quotient (QuotientGroup.rightRel M) → G := fun D => D.out with hy
  have hyD : ∀ D, Quotient.mk _ (y D) = D := fun D => Quotient.out_eq D
  set f := rightCosetMul M z with hf
  have hff : ∀ D, f (f D) = D := fun D => by
    rw [hf, ← rightCosetMul_mul, hzz, rightCosetMul_one]
  have key : ∀ a : G,
      rightCosetMul M z (Quotient.mk _ a) = Quotient.mk _ a ↔ a * z * a⁻¹ ∈ M := fun a => by
    rw [rightCosetMul_mk, rightCoset_mk_eq_iff, _root_.mul_inv_rev, hzinv, ← mul_assoc]
  have hfixD : ∀ D, f D = D ↔ y D * z * (y D)⁻¹ ∈ M := fun D => by
    have h := key (y D)
    rwa [hyD D] at h
  have hyg : ∀ D (g : G), ∃ m ∈ M, y (rightCosetMul M g D) = m * (y D * g) := fun D g => by
    have h : Quotient.mk (QuotientGroup.rightRel M) (y D * g) =
        Quotient.mk _ (y (rightCosetMul M g D)) := by
      rw [hyD, ← rightCosetMul_mk, hyD]
    exact ⟨_, (rightCoset_mk_eq_iff M _ _).1 h, by group⟩
  set c : Quotient (QuotientGroup.rightRel M) → Multiplicative (ZMod 2) :=
    fun D => subVal χ (y D * z * (y D)⁻¹) with hc
  have hcC : ∀ D (p : G), p * z = z * p → c (rightCosetMul M p D) = c D := fun D p hp => by
    obtain ⟨m, hm, hmy⟩ := hyg D p
    simp only [hc]
    rw [hmy, show m * (y D * p) * z * (m * (y D * p))⁻¹ = m * (y D * z * (y D)⁻¹) * m⁻¹ by
      rw [show m * (y D * p) * z = m * y D * (p * z) by group, hp]
      group, subVal_conj χ hm]
  rw [transfer_eq_prod_rightCoset M χ y hyD z]
  have hprod : ∏ D, χ ⟨y D * z * (y (rightCosetMul M z D))⁻¹, rep_mul_rep_inv_mem M y hyD z D⟩ =
      ∏ D, c D := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun D => f D = D),
      ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun D => f D = D) c]
    congr 1
    · refine Finset.prod_congr rfl fun D hD => ?_
      have hD' : f D = D := (Finset.mem_filter.1 hD).2
      simp only [hc]
      rw [subVal_of_mem χ ((hfixD D).1 hD')]
      refine congrArg χ (Subtype.ext ?_)
      show y D * z * (y (rightCosetMul M z D))⁻¹ = y D * z * (y D)⁻¹
      rw [← hf, hD']
    · have hnf : ∏ D ∈ Finset.univ.filter (fun D => ¬ f D = D), c D = 1 :=
        Finset.prod_eq_one fun D hD =>
          subVal_of_notMem χ fun h => (Finset.mem_filter.1 hD).2 ((hfixD D).2 h)
      rw [hnf]
      refine Finset.prod_involution (fun D _ => f D) (fun D _ => ?_) (fun D hD _ => ?_)
        (fun D hD => ?_) (fun D _ => hff D)
      · rw [← map_mul, ← map_one χ]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_one]
        rw [← hf, hff D]
        calc y D * z * (y (f D))⁻¹ * (y (f D) * z * (y D)⁻¹) = y D * (z * z) * (y D)⁻¹ := by
              group
          _ = 1 := by rw [hzz]; group
      · exact (Finset.mem_filter.1 hD).2
      · rw [Finset.mem_filter] at hD ⊢
        refine ⟨Finset.mem_univ _, fun e => hD.2 ?_⟩
        rw [hff] at e
        exact e.symm
  rw [hprod]
  set S := Finset.univ.filter fun D => c D = Multiplicative.ofAdd 1 with hS
  have hprodS : ∏ D, c D = Multiplicative.ofAdd ((S.card : ℕ) : ZMod 2) := by
    rw [Finset.prod_congr rfl fun D _ => (show c D =
        if c D = Multiplicative.ofAdd 1 then Multiplicative.ofAdd 1 else 1 by
      rcases multiplicative_zmod_two_cases (c D) with h | h
      · rw [h, ite_eq_right one_ne_ofAdd_one]
      · rw [h, ite_eq_left rfl]), Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
      mul_one, ← ofAdd_nsmul, nsmul_one]
  rw [hprodS]
  set Fs := Finset.univ.filter fun D => f D = D with hFs
  have hFodd : Odd Fs.card := by
    let fE : Function.End (Quotient (QuotientGroup.rightRel M)) := f
    have hf2 : fE ^ 2 ^ 1 = 1 := by
      rw [pow_one, sq]
      funext D
      exact hff D
    have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf2
    have hcard : Fintype.card (Quotient (QuotientGroup.rightRel M)) = M.index := by
      rw [Subgroup.index, ← Nat.card_eq_fintype_card,
        Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel M)]
    have hfix : Fintype.card (Function.fixedPoints fE) = Fs.card := by
      rw [hFs, ← Fintype.card_subtype]
      rfl
    rw [hcard, hfix] at hmod
    rw [Nat.odd_iff, ← hmod, ← Nat.odd_iff]
    exact hodd
  have hfg : ∀ (g : G) D, g * z = z * g → f D = D →
      f (rightCosetMul M g D) = rightCosetMul M g D := fun g D hg hD => by
    rw [hf, ← rightCosetMul_mul, hg, rightCosetMul_mul, ← hf, hD]
  set S₀ := Fs.filter fun D => c D ≠ Multiplicative.ofAdd 1 with hS₀
  have hS₀even : Even S₀.card := by
    obtain ⟨P⟩ : Nonempty (Sylow 2 (centralizer {z})) := inferInstance
    have hPz : ∀ p : P, ((p : centralizer {z}) : G) * z = z * p := fun p =>
      mem_centralizer_singleton_iff.1 (p : centralizer {z}).2
    let T := {D : Quotient (QuotientGroup.rightRel M) // f D = D ∧ c D ≠ Multiplicative.ofAdd 1}
    have hact : ∀ (p : P) (D : T),
        f (rightCosetMul M (((p : centralizer {z}) : G))⁻¹ D.1) =
          rightCosetMul M (((p : centralizer {z}) : G))⁻¹ D.1 ∧
        c (rightCosetMul M (((p : centralizer {z}) : G))⁻¹ D.1) ≠ Multiplicative.ofAdd 1 := by
      intro p D
      have hp' : (((p : centralizer {z}) : G))⁻¹ * z = z * (((p : centralizer {z}) : G))⁻¹ := by
        have h1 := hPz p
        calc (((p : centralizer {z}) : G))⁻¹ * z =
            (((p : centralizer {z}) : G))⁻¹ * (z * p) * (((p : centralizer {z}) : G))⁻¹ := by
              group
          _ = (((p : centralizer {z}) : G))⁻¹ * (p * z) * (((p : centralizer {z}) : G))⁻¹ := by
              rw [h1]
          _ = z * (((p : centralizer {z}) : G))⁻¹ := by group
      refine ⟨hfg _ D.1 hp' D.2.1, ?_⟩
      rw [hcC D.1 _ hp']
      exact D.2.2
    let _ : MulAction P T :=
      { smul := fun p D => ⟨rightCosetMul M (((p : centralizer {z}) : G))⁻¹ D.1, hact p D⟩
        one_smul := fun D => Subtype.ext (by
          change rightCosetMul M (((1 : P) : centralizer {z}) : G)⁻¹ D.1 = D.1
          rw [OneMemClass.coe_one, OneMemClass.coe_one, inv_one, rightCosetMul_one])
        mul_smul := fun p q D => Subtype.ext (by
          change rightCosetMul M ((((p * q : P) : centralizer {z}) : G))⁻¹ D.1 =
            rightCosetMul M (((p : centralizer {z}) : G))⁻¹
              (rightCosetMul M (((q : centralizer {z}) : G))⁻¹ D.1)
          rw [Subgroup.coe_mul, Subgroup.coe_mul, _root_.mul_inv_rev, rightCosetMul_mul]) }
    have hfp : MulAction.fixedPoints P T = ∅ := by
      ext D
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hD
      apply D.2.2
      have hall : ∀ p : P, y D.1 * ((p : centralizer {z}) : G) * (y D.1)⁻¹ ∈ M := fun p => by
        have h1 := congrArg Subtype.val (hD p)
        change rightCosetMul M (((p : centralizer {z}) : G))⁻¹ D.1 = D.1 at h1
        rw [← hyD D.1, rightCosetMul_mk, rightCoset_mk_eq_iff] at h1
        rwa [show y D.1 * (y D.1 * (((p : centralizer {z}) : G))⁻¹)⁻¹ =
          y D.1 * ((p : centralizer {z}) : G) * (y D.1)⁻¹ by group] at h1
      set x := y D.1 with hx
      have hu : x * z * x⁻¹ ∈ M := (hfixD D.1).1 D.2.1
      refine hfus x hu ?_
      set Q : Subgroup G := ((P : Subgroup (centralizer {z})).map (centralizer {z}).subtype).map
        (MulAut.conj x).toMonoidHom with hQ
      have hQM : Q ≤ M := by
        rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        exact hall ⟨p, hp⟩
      have hQC : Q ≤ centralizer {x * z * x⁻¹} := by
        rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
        rw [mem_centralizer_singleton_iff]
        have h1 := hPz ⟨p, hp⟩
        change x * (p : G) * x⁻¹ * (x * z * x⁻¹) = x * z * x⁻¹ * (x * p * x⁻¹)
        calc x * (p : G) * x⁻¹ * (x * z * x⁻¹) = x * ((p : G) * z) * x⁻¹ := by group
          _ = x * (z * p) * x⁻¹ := by rw [h1]
          _ = x * z * x⁻¹ * (x * p * x⁻¹) := by group
      have hCu : centralizer {x * z * x⁻¹} = (centralizer {z}).map (MulAut.conj x).toMonoidHom := by
        ext w
        rw [mem_centralizer_singleton_iff, Subgroup.mem_map]
        constructor
        · intro hw
          refine ⟨x⁻¹ * w * x, mem_centralizer_singleton_iff.2 ?_, by simp [mul_assoc]⟩
          calc x⁻¹ * w * x * z = x⁻¹ * (w * (x * z * x⁻¹)) * x := by group
            _ = x⁻¹ * ((x * z * x⁻¹) * w) * x := by rw [hw]
            _ = z * (x⁻¹ * w * x) := by group
        · rintro ⟨v, hv, rfl⟩
          have hv' := mem_centralizer_singleton_iff.1 hv
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          calc x * v * x⁻¹ * (x * z * x⁻¹) = x * (v * z) * x⁻¹ := by group
            _ = x * (z * v) * x⁻¹ := by rw [hv']
            _ = x * z * x⁻¹ * (x * v * x⁻¹) := by group
      have hcardQ : Nat.card Q = Nat.card P := by
        rw [hQ, card_map_of_injective (MulAut.conj x).injective,
          card_map_of_injective (centralizer {z}).subtype_injective]
      have hcardCu : Nat.card (centralizer {x * z * x⁻¹}) = Nat.card (centralizer {z}) := by
        rw [hCu, card_map_of_injective (MulAut.conj x).injective]
      have hQidx : Q.relIndex (centralizer {x * z * x⁻¹}) =
          (P : Subgroup (centralizer {z})).index := by
        have h1 := Q.relIndex_mul_card (centralizer {x * z * x⁻¹})
        rw [inf_of_le_left hQC, hcardQ, hcardCu] at h1
        have h2 := (P : Subgroup (centralizer {z})).index_mul_card
        have hpos : 0 < Nat.card P := Nat.card_pos
        exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
      have hPodd : Odd (P : Subgroup (centralizer {z})).index :=
        Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (P.not_dvd_index))
      exact Odd.of_dvd_nat (hQidx ▸ hPodd) (relIndex_dvd_of_le_left _ hQM)
    have hP2 : IsPGroup 2 P := P.isPGroup'
    have hmod := hP2.card_modEq_card_fixedPoints T
    rw [hfp, Nat.card_coe_set_eq, Set.ncard_empty] at hmod
    have hT : Nat.card T = S₀.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hS₀, hFs, Finset.filter_filter]
    rw [hT] at hmod
    exact Nat.even_iff.2 hmod
  have hSF : S = Fs.filter fun D => c D = Multiplicative.ofAdd 1 := by
    ext D
    simp only [hS, hFs, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hD
      refine ⟨?_, hD⟩
      by_contra hne
      apply one_ne_ofAdd_one
      rw [← hD]
      exact (subVal_of_notMem χ fun h => hne ((hfixD D).2 h)).symm
    · exact fun h => h.2
  have hsplit := Finset.card_filter_add_card_filter_not (s := Fs)
    (p := fun D => c D = Multiplicative.ofAdd 1)
  rw [← hSF] at hsplit
  have hSodd : Odd S.card := by
    have h1 : S.card + S₀.card = Fs.card := hsplit
    rcases hFodd with ⟨k, hk⟩
    rcases hS₀even with ⟨l, hl⟩
    exact ⟨k - l, by omega⟩
  obtain ⟨k, hk⟩ := hSodd
  rw [hk]
  congr 1
  push_cast
  rw [show (2 : ZMod 2) = 0 from rfl, zero_mul, zero_add]

theorem exists_hom_ne_one_of_odd_index [Finite G] {M : Subgroup G} {z : G} (hzz : z * z = 1) (hodd : Odd M.index) (χ : M →* Multiplicative (ZMod 2))
    (hfus : ∀ x : G, x * z * x⁻¹ ∈ M → Odd (M.relIndex (centralizer {x * z * x⁻¹})) →
      subVal χ (x * z * x⁻¹) = Multiplicative.ofAdd 1) :
    ∃ ν : G →* Multiplicative (ZMod 2), ν z = Multiplicative.ofAdd 1 :=
  ⟨χ.transfer, transfer_eq_ofAdd_one_of_odd_index hzz hodd χ hfus⟩

end Transfer

section CentralProduct

variable {Q : Type*} [Group Q]

theorem commutatorElement_mul_mul_of_mem_center {q q' z z' : Q} (hz : z ∈ Subgroup.center Q)
    (hz' : z' ∈ Subgroup.center Q) : ⁅q * z, q' * z'⁆ = ⁅q, q'⁆ := by
  have hzc : ∀ g : Q, g * z = z * g := fun g => (mem_center_iff.1 hz g)
  have hzc' : ∀ g : Q, g * z' = z' * g := fun g => (mem_center_iff.1 hz' g)
  rw [commutatorElement_def, commutatorElement_def]
  calc q * z * (q' * z') * (q * z)⁻¹ * (q' * z')⁻¹
      = q * (z * (q' * z')) * (z⁻¹ * q⁻¹) * (z'⁻¹ * q'⁻¹) := by group
    _ = q * ((q' * z') * z) * (z⁻¹ * q⁻¹) * (z'⁻¹ * q'⁻¹) := by rw [← hzc (q' * z')]
    _ = q * q' * (z' * q⁻¹) * (z'⁻¹ * q'⁻¹) := by group
    _ = q * q' * (q⁻¹ * z') * (z'⁻¹ * q'⁻¹) := by rw [← hzc' q⁻¹]
    _ = q * q' * q⁻¹ * q'⁻¹ := by group

theorem commutator_self_le (H : Subgroup Q) : ⁅H, H⁆ ≤ H :=
  commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem ker_eq_bot_of_perfect_central_prod [Finite Q] {S₁ S₂ : Type*} [Group S₁] [Group S₂]
    [Group.IsPerfect Q] [Group.IsPerfect S₁] [Group.IsPerfect S₂] (η : Q →* S₁ × S₂)
    (hη : Function.Surjective η) (hker : η.ker ≤ Subgroup.center Q) (hodd : Odd (Nat.card η.ker))
    (hcov₁ : ∀ E : Subgroup Q, Group.IsPerfect E → ∀ f : E →* S₁, Function.Surjective f →
      f.ker ≤ Subgroup.center E → Odd (Nat.card f.ker) → f.ker = ⊥)
    (hcov₂ : ∀ E : Subgroup Q, Group.IsPerfect E → ∀ f : E →* S₂, Function.Surjective f →
      f.ker ≤ Subgroup.center E → Odd (Nat.card f.ker) → f.ker = ⊥) :
    η.ker = ⊥ := by
  classical
  set Z := η.ker with hZ
  set L₁ : Subgroup (S₁ × S₂) := (⊤ : Subgroup S₁).prod ⊥ with hL₁
  set L₂ : Subgroup (S₁ × S₂) := (⊥ : Subgroup S₁).prod ⊤ with hL₂
  set H₁ := L₁.comap η with hH₁
  set H₂ := L₂.comap η with hH₂
  set Q₁ := ⁅H₁, H₁⁆ with hQ₁
  set Q₂ := ⁅H₂, H₂⁆ with hQ₂
  have hmapH₁ : H₁.map η = L₁ := map_comap_eq_self_of_surjective hη L₁
  have hmapH₂ : H₂.map η = L₂ := map_comap_eq_self_of_surjective hη L₂
  have hS₁ : ⁅(⊤ : Subgroup S₁), ⊤⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  have hS₂ : ⁅(⊤ : Subgroup S₂), ⊤⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  have hmapQ₁ : Q₁.map η = L₁ := by
    rw [hQ₁, map_commutator, hmapH₁, hL₁, commutator_prod_prod, hS₁, commutator_bot_left]
  have hmapQ₂ : Q₂.map η = L₂ := by
    rw [hQ₂, map_commutator, hmapH₂, hL₂, commutator_prod_prod, hS₂, commutator_bot_left]
  have hZc : ∀ z ∈ Z, z ∈ Subgroup.center Q := fun z hz => hker hz
  have hH₁₂ : ∀ x ∈ H₁, ∀ y ∈ H₂, ⁅x, y⁆ ∈ Z := by
    intro x hx y hy
    rw [hZ, MonoidHom.mem_ker, map_commutatorElement]
    have hx' : η x ∈ L₁ := hx
    have hy' : η y ∈ L₂ := hy
    obtain ⟨-, hx2⟩ := hx'
    obtain ⟨hy1, -⟩ := hy'
    apply Prod.ext
    · change ⁅(η x).1, (η y).1⁆ = 1
      rw [show (η y).1 = 1 from hy1, commutatorElement_one_right]
    · change ⁅(η x).2, (η y).2⁆ = 1
      rw [show (η x).2 = 1 from hx2, commutatorElement_one_left]
  have hQ₁H₂ : ∀ q ∈ Q₁, ∀ y ∈ H₂, q * y = y * q := by
    intro q hq y hy
    let c : H₁ →* Q :=
      { toFun := fun x => ⁅(x : Q), y⁆
        map_one' := commutatorElement_one_left y
        map_mul' := fun x x' => commutatorElement_mul_left_of_mem_center
          (hZc _ (hH₁₂ _ x'.2 y hy)) }
    have hle : Q₁ ≤ c.ker.map H₁.subtype := by
      rw [hQ₁, commutator_le]
      intro g₁ hg₁ g₂ hg₂
      refine ⟨⟨⁅g₁, g₂⁆, commutator_self_le _ (commutator_mem_commutator hg₁ hg₂)⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      have h1 : c ⟨⁅g₁, g₂⁆, commutator_self_le _ (commutator_mem_commutator hg₁ hg₂)⟩ =
          ⁅c ⟨g₁, hg₁⟩, c ⟨g₂, hg₂⟩⁆ := by
        rw [← map_commutatorElement]
        rfl
      rw [h1, commutatorElement_eq_one_iff_mul_comm]
      exact mem_center_iff.1 (hZc _ (hH₁₂ _ hg₂ y hy)) _
    obtain ⟨x, hx, rfl⟩ := hle hq
    have h1 : ⁅(x : Q), y⁆ = 1 := hx
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hQ₂H₁ : ∀ q ∈ Q₂, ∀ x ∈ H₁, q * x = x * q := by
    intro q hq x hx
    let c : H₂ →* Q :=
      { toFun := fun y => ⁅(y : Q), x⁆
        map_one' := commutatorElement_one_left x
        map_mul' := fun y y' => commutatorElement_mul_left_of_mem_center (by
          rw [← commutatorElement_inv]
          exact inv_mem (hZc _ (hH₁₂ x hx _ y'.2))) }
    have hle : Q₂ ≤ c.ker.map H₂.subtype := by
      rw [hQ₂, commutator_le]
      intro g₁ hg₁ g₂ hg₂
      refine ⟨⟨⁅g₁, g₂⁆, commutator_self_le _ (commutator_mem_commutator hg₁ hg₂)⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker]
      have h1 : c ⟨⁅g₁, g₂⁆, commutator_self_le _ (commutator_mem_commutator hg₁ hg₂)⟩ =
          ⁅c ⟨g₁, hg₁⟩, c ⟨g₂, hg₂⟩⁆ := by
        rw [← map_commutatorElement]
        rfl
      rw [h1, commutatorElement_eq_one_iff_mul_comm]
      have h2 : ⁅g₂, x⁆ ∈ Subgroup.center Q := by
        rw [← commutatorElement_inv]
        exact inv_mem (hZc _ (hH₁₂ x hx _ hg₂))
      exact mem_center_iff.1 h2 _
    obtain ⟨y, hy, rfl⟩ := hle hq
    have h1 : ⁅(y : Q), x⁆ = 1 := hy
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hHQ₁ : ∀ h ∈ H₁, ∃ q ∈ Q₁, ∃ z ∈ Z, h = q * z := by
    intro h hh
    obtain ⟨q, hq, hqh⟩ : η h ∈ Q₁.map η := hmapQ₁ ▸ hh
    refine ⟨q, hq, q⁻¹ * h, ?_, by group⟩
    rw [hZ, MonoidHom.mem_ker, map_mul, map_inv, hqh, inv_mul_cancel]
  have hHQ₂ : ∀ h ∈ H₂, ∃ q ∈ Q₂, ∃ z ∈ Z, h = q * z := by
    intro h hh
    obtain ⟨q, hq, hqh⟩ : η h ∈ Q₂.map η := hmapQ₂ ▸ hh
    refine ⟨q, hq, q⁻¹ * h, ?_, by group⟩
    rw [hZ, MonoidHom.mem_ker, map_mul, map_inv, hqh, inv_mul_cancel]
  have hQ₁H : Q₁ ≤ H₁ := commutator_self_le H₁
  have hQ₂H : Q₂ ≤ H₂ := commutator_self_le H₂
  have hperf : ∀ (Hi Qi : Subgroup Q), Qi = ⁅Hi, Hi⁆ → (∀ h ∈ Hi, ∃ q ∈ Qi, ∃ z ∈ Z, h = q * z) →
      Group.IsPerfect Qi := by
    intro Hi Qi hQi hHQi
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm (commutator_self_le Qi) ?_
    conv_lhs => rw [hQi]
    rw [commutator_le]
    intro h hh h' hh'
    obtain ⟨q, hq, z, hz, rfl⟩ := hHQi h hh
    obtain ⟨q', hq', z', hz', rfl⟩ := hHQi h' hh'
    rw [commutatorElement_mul_mul_of_mem_center (hZc z hz) (hZc z' hz')]
    exact commutator_mem_commutator hq hq'
  have hperf₁ := hperf H₁ Q₁ rfl hHQ₁
  have hperf₂ := hperf H₂ Q₂ rfl hHQ₂
  have hker₁ : ∀ q ∈ Q₁, η q = 1 → q = 1 := by
    let f : Q₁ →* S₁ := (MonoidHom.fst S₁ S₂).comp (η.comp Q₁.subtype)
    have hfs : Function.Surjective f := by
      intro s₁
      obtain ⟨q, hq, hqs⟩ : ((s₁, 1) : S₁ × S₂) ∈ Q₁.map η :=
        hmapQ₁ ▸ ⟨mem_top s₁, rfl⟩
      exact ⟨⟨q, hq⟩, by change (η q).1 = s₁; rw [hqs]⟩
    have hfker : ∀ q : Q₁, f q = 1 ↔ η q = 1 := by
      intro q
      have h2 : (η q).2 = 1 := (hQ₁H q.2).2
      constructor
      · intro h1
        exact Prod.ext h1 h2
      · intro h1
        change (η q).1 = 1
        rw [h1]
        rfl
    have hfkerc : f.ker ≤ Subgroup.center Q₁ := by
      intro q hq
      rw [mem_center_iff]
      intro g
      have hqZ : (q : Q) ∈ Z := (hfker q).1 hq
      exact Subtype.ext (mem_center_iff.1 (hZc _ hqZ) g)
    have hfodd : Odd (Nat.card f.ker) := by
      have hle : f.ker.map Q₁.subtype ≤ Z := by
        rintro _ ⟨q, hq, rfl⟩
        exact (hfker q).1 hq
      have h1 := card_dvd_of_le hle
      rw [card_map_of_injective Q₁.subtype_injective] at h1
      exact Odd.of_dvd_nat hodd h1
    have hbot := hcov₁ Q₁ hperf₁ f hfs hfkerc hfodd
    intro q hq hηq
    have h1 : (⟨q, hq⟩ : Q₁) ∈ f.ker := (hfker ⟨q, hq⟩).2 hηq
    rw [hbot, mem_bot] at h1
    exact congrArg Subtype.val h1
  have hker₂ : ∀ q ∈ Q₂, η q = 1 → q = 1 := by
    let f : Q₂ →* S₂ := (MonoidHom.snd S₁ S₂).comp (η.comp Q₂.subtype)
    have hfs : Function.Surjective f := by
      intro s₂
      obtain ⟨q, hq, hqs⟩ : ((1, s₂) : S₁ × S₂) ∈ Q₂.map η :=
        hmapQ₂ ▸ ⟨rfl, mem_top s₂⟩
      exact ⟨⟨q, hq⟩, by change (η q).2 = s₂; rw [hqs]⟩
    have hfker : ∀ q : Q₂, f q = 1 ↔ η q = 1 := by
      intro q
      have h2 : (η q).1 = 1 := (hQ₂H q.2).1
      constructor
      · intro h1
        exact Prod.ext h2 h1
      · intro h1
        change (η q).2 = 1
        rw [h1]
        rfl
    have hfkerc : f.ker ≤ Subgroup.center Q₂ := by
      intro q hq
      rw [mem_center_iff]
      intro g
      have hqZ : (q : Q) ∈ Z := (hfker q).1 hq
      exact Subtype.ext (mem_center_iff.1 (hZc _ hqZ) g)
    have hfodd : Odd (Nat.card f.ker) := by
      have hle : f.ker.map Q₂.subtype ≤ Z := by
        rintro _ ⟨q, hq, rfl⟩
        exact (hfker q).1 hq
      have h1 := card_dvd_of_le hle
      rw [card_map_of_injective Q₂.subtype_injective] at h1
      exact Odd.of_dvd_nat hodd h1
    have hbot := hcov₂ Q₂ hperf₂ f hfs hfkerc hfodd
    intro q hq hηq
    have h1 : (⟨q, hq⟩ : Q₂) ∈ f.ker := (hfker ⟨q, hq⟩).2 hηq
    rw [hbot, mem_bot] at h1
    exact congrArg Subtype.val h1
  have hdec : ∀ x : Q, ∃ q₁ ∈ Q₁, ∃ q₂ ∈ Q₂, ∃ w ∈ Z, x = q₁ * q₂ * w := by
    intro x
    obtain ⟨h₁, hh₁⟩ := hη ((η x).1, 1)
    have hh₁H : h₁ ∈ H₁ := by
      change η h₁ ∈ L₁
      rw [hh₁]
      exact ⟨mem_top _, rfl⟩
    have hh₂H : h₁⁻¹ * x ∈ H₂ := by
      change η (h₁⁻¹ * x) ∈ L₂
      rw [map_mul, map_inv, hh₁]
      exact ⟨show ((η x).1, (1 : S₂))⁻¹.1 * (η x).1 = 1 by simp, mem_top _⟩
    obtain ⟨q₁, hq₁, z₁, hz₁, he₁⟩ := hHQ₁ h₁ hh₁H
    obtain ⟨q₂, hq₂, z₂, hz₂, he₂⟩ := hHQ₂ _ hh₂H
    refine ⟨q₁, hq₁, q₂, hq₂, z₁ * z₂, mul_mem hz₁ hz₂, ?_⟩
    calc x = h₁ * (h₁⁻¹ * x) := by group
      _ = q₁ * z₁ * (q₂ * z₂) := by rw [he₂, he₁]
      _ = q₁ * (z₁ * q₂) * z₂ := by group
      _ = q₁ * (q₂ * z₁) * z₂ := by rw [(mem_center_iff.1 (hZc z₁ hz₁) q₂).symm]
      _ = q₁ * q₂ * (z₁ * z₂) := by group
  have hQle : ∀ x : Q, x ∈ Q₁ ⊔ Q₂ := by
    have htop : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Q₁ ⊔ Q₂ := by
      rw [commutator_le]
      intro x _ x' _
      obtain ⟨q₁, hq₁, q₂, hq₂, w, hw, rfl⟩ := hdec x
      obtain ⟨q₁', hq₁', q₂', hq₂', w', hw', rfl⟩ := hdec x'
      rw [commutatorElement_mul_mul_of_mem_center (hZc w hw) (hZc w' hw')]
      exact commutator_self_le _ (commutator_mem_commutator
        (mul_mem (mem_sup_left hq₁) (mem_sup_right hq₂))
        (mul_mem (mem_sup_left hq₁') (mem_sup_right hq₂')))
    intro x
    have hx : x ∈ ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := by
      have h1 : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
      rw [h1]
      exact mem_top x
    exact htop hx
  have hQ₂N : Q₂ ≤ normalizer (Q₁ : Set Q) := by
    intro q hq
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hQ₂H₁ q hq h (hQ₁H hh), mul_inv_cancel_right]
      exact hh
    · intro hh
      have hc := hQ₂H₁ q hq _ (hQ₁H hh)
      have h1 : q * h * q⁻¹ = h := by
        have h2 : q * (q * h * q⁻¹) = q * h := by rw [hc]; group
        exact mul_left_cancel h2
      rw [← h1]
      exact hh
  rw [eq_bot_iff]
  intro z hz
  have hzQ := hQle z
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left Q₁ Q₂ hQ₂N] at hzQ
  obtain ⟨q₁, hq₁, q₂, hq₂, hzq⟩ := hzQ
  have hzq' : q₁ * q₂ = z := hzq
  rw [← hzq'] at hz ⊢
  have hηz : η q₁ * η q₂ = 1 := by
    rw [← map_mul]
    exact hz
  have h1 : η q₁ = (η q₂)⁻¹ := eq_inv_of_mul_eq_one_left hηz
  have hq₁1 : η q₁ = 1 := by
    have ha : η q₁ ∈ L₁ := hQ₁H hq₁
    have hb : η q₁ ∈ L₂ := by
      rw [h1]
      exact inv_mem (hQ₂H hq₂)
    exact Prod.ext (mem_bot.1 hb.1) (mem_bot.1 ha.2)
  have hq₂1 : η q₂ = 1 := by
    rw [hq₁1, one_mul] at hηz
    exact hηz
  rw [hker₁ q₁ hq₁ hq₁1, hker₂ q₂ hq₂ hq₂1, mul_one]
  exact one_mem _

end CentralProduct

section Outer

open CFSG.ProperTwoGeneratedCore.PairedTensor CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits

variable {Y : Type*} [Group Y]

@[expose] noncomputable def transportConj (D : Subgroup Y) [D.Normal] (ψ : D ≃* K) :
    Y →* MulAut K :=
  (MulAut.congr ψ).toMonoidHom.comp MulAut.conjNormal

theorem transportConj_apply (D : Subgroup Y) [D.Normal] (ψ : D ≃* K) (y : Y) (k : K) :
    transportConj D ψ y k = ψ ⟨y * (ψ.symm k : Y) * y⁻¹,
      (inferInstance : D.Normal).conj_mem _ (ψ.symm k).2 y⟩ := by
  change ψ (MulAut.conjNormal y (ψ.symm k)) = _
  congr 1

theorem transportConj_injective (D : Subgroup Y) [D.Normal] (ψ : D ≃* K)
    (hCD : centralizer (D : Set Y) = ⊥) : Function.Injective (transportConj D ψ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  rw [← hCD, mem_centralizer_iff]
  intro d hd
  have h1 := congrArg (fun α : MulAut K => ψ.symm (α (ψ ⟨d, hd⟩))) hy
  simp only [transportConj_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h1
  have h2 : y * d * y⁻¹ = d := congrArg Subtype.val h1
  calc d * y = (y * d * y⁻¹) * y := by rw [h2]
    _ = y * d := by group

theorem transportConj_mem (D : Subgroup Y) [D.Normal] (ψ : D ≃* K) (d : D) :
    transportConj D ψ d = MulAut.conj (ψ d) := by
  apply MulEquiv.ext
  intro k
  rw [transportConj_apply, MulAut.conj_apply]
  have h : (⟨(d : Y) * (ψ.symm k : Y) * (d : Y)⁻¹, (inferInstance : D.Normal).conj_mem _
      (ψ.symm k).2 d⟩ : D) = d * ψ.symm k * d⁻¹ := Subtype.ext rfl
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem qFull_mul_eq (q r : QFull) : q * r = ⟨q.e₁ + (if q.σ = 0 then r.e₁ else r.e₂),
    q.e₂ + (if q.σ = 0 then r.e₂ else r.e₁), q.σ + r.σ⟩ :=
  QFull.mul_def q r

theorem qFull_ab : QFull.a * QFull.b = ⟨1, 1, 0⟩ := by
  rw [qFull_mul_eq]
  rfl

theorem qFull_ab_cases : ∀ q : QFull, q ≠ 1 → q ≠ QFull.s →
    q * (QFull.s * q * QFull.s) = QFull.a * QFull.b ∨
      (q * QFull.s) * (QFull.s * (q * QFull.s) * QFull.s) = QFull.a * QFull.b ∨
      q * QFull.s = QFull.a * QFull.b ∨ q = QFull.a * QFull.b := by
  rintro ⟨e₁, e₂, σ⟩
  simp only [qFull_mul_eq, QFull.one_def, QFull.s, QFull.a, QFull.b, ne_eq, QFull.mk.injEq]
  revert e₁ e₂ σ
  decide

theorem qFull_ab_comm_s : QFull.a * QFull.b * QFull.s = QFull.s * (QFull.a * QFull.b) := by
  simp only [qFull_mul_eq, QFull.s, QFull.a, QFull.b, QFull.mk.injEq]
  decide

theorem qAct_ab_apply (x : K) : qAct (QFull.a * QFull.b) x = (tau x.1, tau x.2) := by
  rw [qAct_apply, qFull_ab]
  rfl

theorem qAct_s_apply (x : K) : qAct QFull.s x = (x.2, x.1) := by
  rw [qAct_apply]
  rfl

theorem exists_swap_character [Finite Y] (D : Subgroup Y) [D.Normal] (ψ : D ≃* K)
    (hCD : centralizer (D : Set Y) = ⊥) {a : Y}
    (hψa : ∀ d : D, ψ (MulAut.conjNormal a d) = (ψ d).swap)
    (hCa : ∀ y : Y, y * a = a * y →
      ∃ g : S, y = (ψ.symm (g, g) : Y) ∨ y = a * (ψ.symm (g, g) : Y)) :
    ∃ χ : Y →* Multiplicative (ZMod 2), χ a = Multiplicative.ofAdd 1 ∧ χ.ker = D := by
  classical
  set β := transportConj D ψ with hβ
  have hβinj := transportConj_injective D ψ hCD
  let Φ : Efull ≃* MulAut K := MulEquiv.ofBijective autHom ⟨autHom_injective, autHom_surjective⟩
  have hΦ : ∀ e, Φ e = autHom e := fun _ => rfl
  let ω : Y →* QFull := (SemidirectProduct.rightHom).comp (Φ.symm.toMonoidHom.comp β)
  have hωβ : ∀ y, β y = MulAut.conj (Φ.symm (β y)).left * qAct (ω y) := fun y => by
    change β y = MulAut.conj (Φ.symm (β y)).left * qAct (Φ.symm (β y)).right
    rw [← autHom_apply, ← hΦ, MulEquiv.apply_symm_apply]
  have hβD : ∀ d : D, β d = MulAut.conj (ψ d) := transportConj_mem D ψ
  have hωD : ∀ d : D, ω d = 1 := fun d => by
    change (Φ.symm (β d)).right = 1
    have h : β d = Φ (SemidirectProduct.inl (ψ d)) := by rw [hβD, hΦ, autHom_inl]
    rw [h, MulEquiv.symm_apply_apply, SemidirectProduct.right_inl]
  have hβa : β a = qAct QFull.s := by
    apply MulEquiv.ext
    intro k
    have h1 := hψa (ψ.symm k)
    rw [MulEquiv.apply_symm_apply] at h1
    rw [hβ, transportConj_apply, qAct_s_apply, ← Prod.swap_prod_mk, ← h1]
    exact congrArg ψ (Subtype.ext rfl)
  have hωa : ω a = QFull.s := by
    change (Φ.symm (β a)).right = QFull.s
    have h : β a = Φ (SemidirectProduct.inr QFull.s) := by rw [hβa, hΦ, autHom_inr]
    rw [h, MulEquiv.symm_apply_apply, SemidirectProduct.right_inr]
  have hrange : ∀ y : Y, ω y = 1 ∨ ω y = QFull.s := by
    by_contra hcon
    push Not at hcon
    obtain ⟨y, hy1, hys⟩ := hcon
    obtain ⟨y₁, hy₁⟩ : ∃ y₁ : Y, ω y₁ = QFull.a * QFull.b := by
      rcases qFull_ab_cases (ω y) hy1 hys with h | h | h | h
      · exact ⟨y * (a * y * a), by rw [map_mul, map_mul, map_mul, hωa, h]⟩
      · exact ⟨(y * a) * (a * (y * a) * a), by
          rw [map_mul, map_mul, map_mul, map_mul, map_mul, hωa, h]⟩
      · exact ⟨y * a, by rw [map_mul, hωa, h]⟩
      · exact ⟨y, h⟩
    set k := (Φ.symm (β y₁)).left with hk
    set y₂ := ((ψ.symm k : D) : Y)⁻¹ * y₁ with hy₂
    have hβy₂ : β y₂ = qAct (QFull.a * QFull.b) := by
      rw [hy₂, map_mul, map_inv, hβD, MulEquiv.apply_symm_apply, hωβ y₁, ← hk, hy₁]
      group
    have hy₂a : y₂ * a = a * y₂ := by
      have h1 : β (y₂ * a * y₂⁻¹) = β a := by
        rw [map_mul, map_mul, map_inv, hβy₂, hβa, ← map_mul, ← map_inv, ← map_mul,
          qFull_ab_comm_s, map_mul, map_mul, map_inv]
        group
      have h2 := hβinj h1
      calc y₂ * a = (y₂ * a * y₂⁻¹) * y₂ := by group
        _ = a * y₂ := by rw [h2]
    obtain ⟨g, hg | hg⟩ := hCa y₂ hy₂a
    ·
      have h1 : β y₂ = MulAut.conj (g, g) := by
        rw [hg, hβD, MulEquiv.apply_symm_apply]
      apply tau_ne_conj g
      apply MulEquiv.ext
      intro x
      have h2 := congrArg (fun α : MulAut K => (α (x, 1)).1) (hβy₂.symm.trans h1)
      simp only [qAct_ab_apply, MulAut.conj_apply, Prod.fst_mul, Prod.fst_inv] at h2
      rw [MulAut.conj_apply]
      exact h2
    ·
      have h1 : β y₂ = qAct QFull.s * MulAut.conj (g, g) := by
        rw [hg, map_mul, hβa, hβD, MulEquiv.apply_symm_apply]
      obtain ⟨x, hx⟩ := exists_ne (1 : S)
      apply hx
      have h2 := congrArg (fun α : MulAut K => (α (x, 1)).1) (hβy₂.symm.trans h1)
      simp only [qAct_ab_apply, MulAut.mul_apply, MulAut.conj_apply, qAct_s_apply,
        Prod.snd_mul, Prod.snd_inv, mul_one, mul_inv_cancel] at h2
      have h3 : tau x = tau 1 := by rw [h2, map_one]
      exact tau.injective h3
  let σHom : QFull →* Multiplicative (ZMod 2) :=
    { toFun := fun q => Multiplicative.ofAdd q.σ
      map_one' := rfl
      map_mul' := fun q r => by
        rw [qFull_mul_eq]
        rfl }
  refine ⟨σHom.comp ω, ?_, ?_⟩
  · change Multiplicative.ofAdd (ω a).σ = Multiplicative.ofAdd 1
    rw [hωa]
    rfl
  · ext y
    rw [MonoidHom.mem_ker]
    constructor
    · intro hy
      have hσ : (ω y).σ = 0 := Multiplicative.ofAdd.injective hy
      have hω1 : ω y = 1 := by
        rcases hrange y with h | h
        · exact h
        · rw [h] at hσ
          exact absurd hσ (by decide)
      set k := (Φ.symm (β y)).left with hk
      have h1 : β y = β ((ψ.symm k : D) : Y) := by
        rw [hωβ y, hω1, map_one, mul_one, hβD, MulEquiv.apply_symm_apply]
      rw [hβinj h1]
      exact (ψ.symm k).2
    · intro hy
      change Multiplicative.ofAdd (ω (⟨y, hy⟩ : D)).σ = 1
      rw [hωD]
      rfl

end Outer

end TwoFactor

end CFSG.LocalAnalysis.ComponentInitial.SteinbergBX
