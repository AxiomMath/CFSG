module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixDegreeEight
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeCanonicalOrder512
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymmetricThreeFullNormalizerSylowControl
public import CFSG.CharacterTheory.Semidihedral.Local.TransferCosetOrbit

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

universe u

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.DegreeEight

open Subgroup Module Matrix MulAction SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits
  CFSG.Semidihedral.Local
open LinearMap (BilinForm)
open scoped Pointwise BinarySymThreeOrbit commutatorElement

section Transfer

variable {G : Type*} [Group G]

@[expose] def subVal {M : Subgroup G} (χ : M →* Multiplicative (ZMod 2)) (w : G) :
    Multiplicative (ZMod 2) :=
  open Classical in if h : w ∈ M then χ ⟨w, h⟩ else 1

theorem subVal_of_mem {M : Subgroup G} (χ : M →* Multiplicative (ZMod 2)) {w : G} (h : w ∈ M) :
    subVal χ w = χ ⟨w, h⟩ :=
  dite_eq_left h

theorem subVal_of_notMem {M : Subgroup G} (χ : M →* Multiplicative (ZMod 2)) {w : G}
    (h : w ∉ M) : subVal χ w = 1 :=
  dite_eq_right h

theorem subVal_conj {M : Subgroup G} (χ : M →* Multiplicative (ZMod 2)) {m : G} (hm : m ∈ M)
    (w : G) : subVal χ (m * w * m⁻¹) = subVal χ w := by
  by_cases hw : w ∈ M
  · have h' : m * w * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hw) (M.inv_mem hm)
    rw [subVal_of_mem χ h', subVal_of_mem χ hw]
    have h : (⟨m * w * m⁻¹, h'⟩ : M) = ⟨m, hm⟩ * ⟨w, hw⟩ * ⟨m, hm⟩⁻¹ := Subtype.ext rfl
    rw [h, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  · have h' : m * w * m⁻¹ ∉ M := fun h => hw (by
      have := M.mul_mem (M.mul_mem (M.inv_mem hm) h) hm
      rwa [show m⁻¹ * (m * w * m⁻¹) * m = w by group] at this)
    rw [subVal_of_notMem χ h', subVal_of_notMem χ hw]

theorem multiplicative_zmod_two_cases (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases h (Multiplicative.toAdd x) with h | h
  · exact Or.inl (by rw [← ofAdd_toAdd x, h, ofAdd_zero])
  · exact Or.inr (by rw [← ofAdd_toAdd x, h])

theorem one_ne_ofAdd_one : (1 : Multiplicative (ZMod 2)) ≠ Multiplicative.ofAdd 1 := fun h =>
  zero_ne_one (α := ZMod 2) (congrArg Multiplicative.toAdd h)

theorem rightCosetMul_one (M : Subgroup G) (D : Quotient (QuotientGroup.rightRel M)) :
    rightCosetMul M 1 D = D := by
  induction D using Quotient.inductionOn with
  | h a => rw [rightCosetMul_mk, mul_one]

theorem rightCosetMul_mul (M : Subgroup G) (a b : G) (D : Quotient (QuotientGroup.rightRel M)) :
    rightCosetMul M (a * b) D = rightCosetMul M b (rightCosetMul M a D) := by
  induction D using Quotient.inductionOn with
  | h x => rw [rightCosetMul_mk, rightCosetMul_mk, rightCosetMul_mk, mul_assoc]

theorem transfer_eq_of_unique_fixed_coset [Finite G] {M P : Subgroup G} {z : G} (hzM : z ∈ M)
    (hzz : z * z = 1) (hP : IsPGroup 2 P) (hPM : P ≤ M) (hPz : ∀ p ∈ P, p * z = z * p)
    (hfix : ∀ x : G, (∀ p ∈ P, x * p * x⁻¹ ∈ M) → x ∈ M) (χ : M →* Multiplicative (ZMod 2))
    (hχ : χ ⟨z, hzM⟩ = Multiplicative.ofAdd 1) :
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
  have hcP : ∀ D, ∀ p ∈ P, c (rightCosetMul M p D) = c D := fun D p hp => by
    obtain ⟨m, hm, hmy⟩ := hyg D p
    simp only [hc]
    rw [hmy, show m * (y D * p) * z * (m * (y D * p))⁻¹ = m * (y D * z * (y D)⁻¹) * m⁻¹ by
      rw [show m * (y D * p) * z = m * y D * (p * z) by group, hPz p hp]
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
  congr 1
  let S' := {D : Quotient (QuotientGroup.rightRel M) // c D = Multiplicative.ofAdd 1}
  let _ : MulAction P S' :=
    { smul := fun p D => ⟨rightCosetMul M ((p⁻¹ : P) : G) D.1, by
        rw [hcP D.1 _ (p⁻¹).2]
        exact D.2⟩
      one_smul := fun D => Subtype.ext (by
        change rightCosetMul M ((1⁻¹ : P) : G) D.1 = D.1
        rw [inv_one, OneMemClass.coe_one, rightCosetMul_one])
      mul_smul := fun p q D => Subtype.ext (by
        change rightCosetMul M (((p * q)⁻¹ : P) : G) D.1 =
          rightCosetMul M ((p⁻¹ : P) : G) (rightCosetMul M ((q⁻¹ : P) : G) D.1)
        rw [_root_.mul_inv_rev, Subgroup.coe_mul, rightCosetMul_mul]) }
  have hmk1 : c (Quotient.mk _ 1) = Multiplicative.ofAdd 1 := by
    have h1 : y (Quotient.mk _ 1) ∈ M := by
      have h := (rightCoset_mk_eq_iff M _ _).1 (hyD (Quotient.mk (QuotientGroup.rightRel M) 1))
      rw [one_mul, inv_mem_iff] at h
      exact h
    simp only [hc]
    rw [subVal_conj χ h1, subVal_of_mem χ hzM, hχ]
  have hfp : MulAction.fixedPoints P S' = {⟨Quotient.mk _ 1, hmk1⟩} := by
    ext D
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hD
      have hall : ∀ p ∈ P, y D.1 * p * (y D.1)⁻¹ ∈ M := fun p hp => by
        have h1 := congrArg Subtype.val (hD ⟨p, hp⟩)
        change rightCosetMul M ((⟨p, hp⟩⁻¹ : P) : G) D.1 = D.1 at h1
        rw [← hyD D.1, rightCosetMul_mk, rightCoset_mk_eq_iff] at h1
        rwa [show y D.1 * (y D.1 * ((⟨p, hp⟩⁻¹ : P) : G))⁻¹ = y D.1 * p * (y D.1)⁻¹ by
          rw [InvMemClass.coe_inv]; group] at h1
      have hyM := hfix _ hall
      apply Subtype.ext
      change D.1 = Quotient.mk _ 1
      rw [← hyD D.1, rightCoset_mk_eq_iff, one_mul]
      exact M.inv_mem hyM
    · rintro rfl p
      apply Subtype.ext
      change rightCosetMul M ((p⁻¹ : P) : G) (Quotient.mk _ 1) = Quotient.mk _ 1
      rw [rightCosetMul_mk, rightCoset_mk_eq_iff, one_mul, one_mul, InvMemClass.coe_inv,
        inv_inv]
      exact hPM p.2
  have hmod := hP.card_modEq_card_fixedPoints S'
  have h1 : Nat.card (MulAction.fixedPoints P S') = 1 := by
    rw [hfp, Nat.card_coe_set_eq, Set.ncard_singleton]
  have h2 : Nat.card S' = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, h2] at hmod
  rw [← ZMod.natCast_mod, hmod]
  rfl

end Transfer

section Characters

variable {G : Type*} [Group G]

theorem exists_hom_of_index_two {S K : Subgroup G} {z : G} (hzS : z ∈ S) (hzK : z ∉ K)
    (hzc : ∀ s ∈ S, s * z = z * s) (hzz : z * z ∈ K) (hcover : ∀ s ∈ S, s ∈ K ∨ s * z ∈ K) :
    ∃ χ₀ : S →* Multiplicative (ZMod 2), (∀ s : S, (s : G) ∈ K → χ₀ s = 1) ∧
      χ₀ ⟨z, hzS⟩ = Multiplicative.ofAdd 1 := by
  classical
  have hmulK : ∀ s ∈ S, ∀ t ∈ S, (s * t ∈ K ↔ (s ∈ K ↔ t ∈ K)) := by
    intro s hs t ht
    constructor
    · intro hst
      constructor
      · intro hsK
        have := K.mul_mem (K.inv_mem hsK) hst
        rwa [inv_mul_cancel_left] at this
      · intro htK
        have := K.mul_mem hst (K.inv_mem htK)
        rwa [mul_inv_cancel_right] at this
    · intro h
      by_cases hsK : s ∈ K
      · exact K.mul_mem hsK (h.1 hsK)
      · have htK : t ∉ K := fun htK => hsK (h.2 htK)
        have hs' := (hcover s hs).resolve_left hsK
        have ht' := (hcover t ht).resolve_left htK
        have h1 := K.mul_mem (K.mul_mem hs' ht') (K.inv_mem hzz)
        rwa [show s * z * (t * z) * (z * z)⁻¹ = s * t by
          rw [show s * z * (t * z) = s * (z * t) * z by group, ← hzc t ht]
          group] at h1
  let f : S → Multiplicative (ZMod 2) := fun s =>
    if (s : G) ∈ K then 1 else Multiplicative.ofAdd 1
  refine ⟨MonoidHom.mk' f fun s t => ?_, fun s hs => ite_eq_left hs, ite_eq_right hzK⟩
  have h := hmulK s s.2 t t.2
  change (if ((s * t : S) : G) ∈ K then (1 : Multiplicative (ZMod 2)) else _) =
    (if (s : G) ∈ K then (1 : Multiplicative (ZMod 2)) else _) *
      (if (t : G) ∈ K then (1 : Multiplicative (ZMod 2)) else _)
  rw [Subgroup.coe_mul]
  by_cases hs : (s : G) ∈ K <;> by_cases ht : (t : G) ∈ K
  · rw [ite_eq_left (h.2 ⟨fun _ => ht, fun _ => hs⟩), ite_eq_left hs, ite_eq_left ht, mul_one]
  · rw [ite_eq_right fun h' => ht ((h.1 h').1 hs), ite_eq_left hs, ite_eq_right ht, one_mul]
  · rw [ite_eq_right fun h' => hs ((h.1 h').2 ht), ite_eq_right hs, ite_eq_left ht, mul_one]
  · rw [ite_eq_left (h.2 ⟨fun h' => absurd h' hs, fun h' => absurd h' ht⟩), ite_eq_right hs,
      ite_eq_right ht]
    rfl

theorem exists_hom_extend {N C S : Subgroup G} (hSN : S ≤ N)
    (hCn : ∀ n ∈ N, ∀ c ∈ C, n * c * n⁻¹ ∈ C) (hNCS : ∀ n ∈ N, ∃ c ∈ C, ∃ s ∈ S, c * s = n)
    (χ₀ : S →* Multiplicative (ZMod 2)) (hker : ∀ s : S, (s : G) ∈ C → χ₀ s = 1) :
    ∃ χ : N →* Multiplicative (ZMod 2), ∀ s : S, χ ⟨s, hSN s.2⟩ = χ₀ s := by
  classical
  choose c hc s hs hcs using hNCS
  have hwd : ∀ (c₁ : G) (_ : c₁ ∈ C) (s₁ : S) (c₂ : G) (_ : c₂ ∈ C) (s₂ : S),
      c₁ * s₁ = c₂ * s₂ → χ₀ s₁ = χ₀ s₂ := by
    intro c₁ hc₁ s₁ c₂ hc₂ s₂ h
    have hmem : ((s₂ * s₁⁻¹ : S) : G) ∈ C := by
      have h' : ((s₂ * s₁⁻¹ : S) : G) = c₂⁻¹ * c₁ := by
        rw [Subgroup.coe_mul, InvMemClass.coe_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← h,
          mul_inv_cancel_right]
      rw [h']
      exact C.mul_mem (C.inv_mem hc₂) hc₁
    have h1 := hker _ hmem
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1.symm
  refine ⟨MonoidHom.mk' (fun n => χ₀ ⟨s n n.2, hs n n.2⟩) fun n n' => ?_, fun t => ?_⟩
  · have hsN : s n n.2 ∈ N := hSN (hs n n.2)
    have hc' : c n n.2 * (s n n.2 * c n' n'.2 * (s n n.2)⁻¹) ∈ C :=
      C.mul_mem (hc n n.2) (hCn _ hsN _ (hc n' n'.2))
    refine (hwd _ (hc _ (n * n').2) _ _ hc'
      (⟨s n n.2, hs n n.2⟩ * ⟨s n' n'.2, hs n' n'.2⟩) ?_).trans (map_mul _ _ _)
    rw [hcs, Subgroup.coe_mul, Subgroup.coe_mul]
    conv_lhs => rw [← hcs n n.2, ← hcs n' n'.2]
    group
  · exact hwd _ (hc _ _) _ 1 (one_mem C) t (by rw [hcs, one_mul])

end Characters

theorem consequences_of_character {G : Type*} [Group G] {z : G}
    (ν : G →* Multiplicative (ZMod 2)) (hν : ν z = Multiplicative.ofAdd 1) :
    Function.Surjective ν ∧ z ∉ commutator G ∧ ν.ker.Normal ∧ ν.ker.index = 2 ∧
      commutator G ≠ ⊤ ∧ (IsSimpleGroup G → ∀ a b : G, a * b = b * a) := by
  have hsurj : Function.Surjective ν := fun x => by
    rcases multiplicative_zmod_two_cases x with rfl | rfl
    · exact ⟨1, map_one ν⟩
    · exact ⟨z, hν⟩
  have hz : z ∉ commutator G := fun h => one_ne_ofAdd_one
    ((MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker ν h)).symm.trans hν)
  have htop : commutator G ≠ ⊤ := fun h => hz (h ▸ mem_top z)
  refine ⟨hsurj, hz, inferInstance, ?_, htop, fun hsimple a b => ?_⟩
  · rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    rfl
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · have h1 : ⁅a, b⁆ ∈ commutator G := commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
    · exact absurd h htop

section Setting

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z : G}
  (hzC : z ∈ centralizer (L : Set G)) (hsup : L ⊔ zpowers z = centralizer ({z} : Set G))
  (hinf : L ⊓ zpowers z = ⊥) (hz : orderOf z = 2)
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)
  {e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V} (he : IsSymplecticBasis b e)

local notation "𝒜" => pullSub φ (pointwiseStabilizer b (lagrangianOf e))
local notation "ℛ" => (𝒜 ⊔ zpowers z : Subgroup G)
local notation "𝒩" => normalizer ((ℛ : Subgroup G) : Set G)
local notation "𝒮" => (𝒩 ⊓ centralizer (Singleton.singleton z : Set G) : Subgroup G)
local notation "ℒ" => (normalizer ((𝒜 : Subgroup G) : Set G) ⊓ L : Subgroup G)

include hzC hsup hinf hz hb hnd hV he in
theorem exists_character_of_rankOne_orbit
    (hΩ : conjClass 𝒩 z = {x | ∃ (v : Fin 3 → ZMod 2) (a : G) (ha : a ∈ L), x = z * a ∧
      LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 (vecMulVec v v) 0 1}) :
    ∃ ν : G →* Multiplicative (ZMod 2), ν z = Multiplicative.ofAdd 1 := by
  classical
  have hrange : conjClass 𝒩 z = Set.range (fun v : Fin 3 → ZMod 2 =>
      z * tauHom φ he (Multiplicative.ofAdd (BinarySymThreeOrbit.label v))) := by
    rw [hΩ]
    ext x
    constructor
    · rintro ⟨v, a, ha, rfl, hmat⟩
      exact ⟨v, by
        rw [RadicalLabels.eq_tauHom_of_toMatrix φ he ha (BinarySymThreeOrbit.label v) hmat]⟩
    · rintro ⟨v, rfl⟩
      exact ⟨v, _, tauHom_mem φ he _, rfl, toMatrix_tauHom φ he _⟩
  have h1 : conjClass 𝒩 z = {z} ∪ z • tauSet φ e (fun B => B.rank = 1) :=
    hrange.trans (range_rankOne_labels φ he)
  have h8 : Nat.card (conjClass 𝒩 z) = 8 := by
    rw [hrange, Nat.card_range_of_injective (rankOne_labels_injective φ he)]
    simp
  obtain ⟨-, ℓ₁, hℓ₁0, hform, ρ, hρ, hKaff, -, hkerρ, -, -, D, -, hDpcore, -, -, -, -, -, hDN,
    -, hDN₀, μ, -, -, hμ', -, -⟩ :=
    degree_eight_structure hzC hsup hinf hz hb hnd hV φ he 𝒩 inf_le_left le_rfl h8
  have hℓ₁ : ∀ v, (ℓ₁ v : G) =
      z * tauHom φ he (Multiplicative.ofAdd (BinarySymThreeOrbit.label v)) := by
    rcases hform with ⟨-, hf⟩ | ⟨h2, -⟩
    · intro v
      obtain ⟨a, ha, hv, hmat⟩ := hf v
      rw [hv, RadicalLabels.eq_tauHom_of_toMatrix φ he ha (BinarySymThreeOrbit.label v) hmat]
    · exfalso
      have hv : (Pi.single 0 1 : Fin 3 → ZMod 2) ≠ 0 := fun h => by
        simpa using congrFun h 0
      have hx : z * tauHom φ he (Multiplicative.ofAdd (BinarySymThreeOrbit.label
          (Pi.single 0 1))) ∈ z • tauSet φ e (fun B => B.rank = 1) :=
        ⟨_, (mem_tauSet_iff φ he).2 ⟨_, (sym_rank_one_iff (BinarySymThreeOrbit.label
          (Pi.single 0 1))).2 ⟨_, hv, rfl⟩, rfl⟩, rfl⟩
      have hx' : z * tauHom φ he (Multiplicative.ofAdd (BinarySymThreeOrbit.label
          (Pi.single 0 1))) ∈ conjClass 𝒩 z := by
        rw [h1]
        exact Or.inr hx
      rw [h2] at hx'
      rcases hx' with h | h
      · exact notMem_smul_tauSet φ he (P := fun B => B.rank = 1) (by simp)
          (Set.mem_singleton_iff.1 h ▸ hx)
      · exact Set.disjoint_left.1 (Set.disjoint_smul_set.2 (disjoint_tauSet φ he
          fun B (h : B.rank = 1) h' => by rw [h] at h'; exact absurd h'.1 (by norm_num))) hx h
  set θ := RadicalLabels.radLabel φ he hzC hz hinf with hθ
  set ℓ : (Fin 3 → ZMod 2) → G := fun v =>
    ((θ.symm (Multiplicative.ofAdd (BinarySymThreeOrbit.label v, 1)) : ℛ) : G) with hℓdef
  have hℓ : ∀ v, ℓ v = ℓ₁ v := fun v => by
    rw [hℓ₁]
    change RadicalLabels.radHom φ he hzC hz
      (Multiplicative.ofAdd (BinarySymThreeOrbit.label v, 1)) = _
    rw [RadicalLabels.radHom_apply, RadicalLabels.zPow_one]
    exact RadicalLabels.mul_comm_z hzC (tauHom_mem φ he _)
  have hz0 : z = ℓ 0 := ((hℓ 0).trans hℓ₁0).symm
  have hℓinj : ∀ v w, ℓ v = ℓ w → v = w := fun v w h => by
    rw [hℓ, hℓ] at h
    exact ℓ₁.injective (Subtype.ext h)
  have hconjR : ∀ (m : 𝒩) (v : Fin 3 → ZMod 2), (m : G)⁻¹ * ℓ v * m = ℓ (ρ m⁻¹ v) :=
    fun m v => by rw [hℓ, hℓ, hρ, InvMemClass.coe_inv, inv_inv]
  have hΩR : ∀ m ∈ 𝒩, ∀ v, ∃ w, m⁻¹ * ℓ v * m = ℓ w := fun m hm v => ⟨_, hconjR ⟨m, hm⟩ v⟩
  have hfaith : ∀ m ∈ 𝒩, (∀ v, m⁻¹ * ℓ v * m = ℓ v) → m ∈ ℛ := fun m hm h => by
    have h1 : ρ (⟨m, hm⟩⁻¹) = 1 :=
      Equiv.ext fun v => hℓinj _ _ ((hconjR ⟨m, hm⟩ v).symm.trans (h v))
    have h2 : (⟨m, hm⟩⁻¹ : 𝒩) ∈ (ℛ).subgroupOf 𝒩 := hkerρ ▸ MonoidHom.mem_ker.2 h1
    rw [mem_subgroupOf, InvMemClass.coe_inv] at h2
    exact inv_mem_iff.1 h2
  have htrans : ∀ v w : Fin 3 → ZMod 2, ∃ m ∈ 𝒩, m⁻¹ * ℓ v * m = ℓ w := fun v w => by
    obtain ⟨m', hm'⟩ : Equiv.addLeft (w - v) ∈ ρ.range := by
      rw [hKaff]
      exact ⟨w - v, LinearEquiv.refl _ _, fun u => rfl⟩
    refine ⟨(m' : G)⁻¹, inv_mem m'.2, ?_⟩
    have h := hconjR m'⁻¹ v
    rw [inv_inv, hm'] at h
    change _ = ℓ (w - v + v) at h
    rw [sub_add_cancel] at h
    exact h
  have hstab : ∀ m ∈ 𝒩, m⁻¹ * z * m = z → ∃ Lm : GL (Fin 3) (ZMod 2),
      ∀ v, m⁻¹ * ℓ v * m = ℓ ((Lm : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := fun m hm h => by
    have h0 : ρ (⟨m, hm⟩⁻¹) 0 = 0 := hℓinj _ _ ((hconjR ⟨m, hm⟩ 0).symm.trans (by
      rw [← hz0]
      exact h))
    refine ⟨μ ⟨m, hm⟩⁻¹, fun v => ?_⟩
    rw [hconjR ⟨m, hm⟩ v, hμ', h0, zero_add]
  have hstab' : ∀ Lm : GL (Fin 3) (ZMod 2), ∃ m ∈ 𝒩,
      ∀ v, m⁻¹ * ℓ v * m = ℓ ((Lm : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v) := fun Lm => by
    obtain ⟨m', hm'⟩ : (glLin Lm).toEquiv ∈ ρ.range := by
      rw [hKaff]
      exact ⟨0, glLin Lm, fun u => (zero_add _).symm⟩
    refine ⟨(m' : G)⁻¹, inv_mem m'.2, fun v => ?_⟩
    have h := hconjR m'⁻¹ v
    rw [inv_inv, hm', LinearEquiv.coe_toEquiv, glLin_apply] at h
    exact h
  obtain ⟨⟨hRea, hR128⟩, -, -, huniq, -⟩ :=
    binary_symmetric_three_full_normalizer_sylow_control (ℛ) θ 𝒩 rfl ℓ (fun v => rfl) z hz0
      hΩR hfaith htrans hstab hstab'
  have hRN : RadicalLabels.radSub φ z e ≤ 𝒩 := le_normalizer
  set θ' := RadicalLabels.radLabelOf φ he hzC hz hinf hRN with hθ'
  have H : BinarySymThreeOrbit.IsAffineOrbit θ' :=
    { maps := fun m v => by
        obtain ⟨w, hw⟩ := hΩR m m.2 v
        exact ⟨w, Subtype.ext hw⟩
      faithful := fun m h => hfaith m m.2 fun v => congrArg Subtype.val (h v)
      transitive := fun v w => by
        obtain ⟨m, hm, h⟩ := htrans v w
        exact ⟨⟨m, hm⟩, Subtype.ext h⟩
      stab_linear := fun m h => by
        have h' : (m : G)⁻¹ * ℓ 0 * m = ℓ 0 := congrArg Subtype.val h
        rw [← hz0] at h'
        obtain ⟨Lm, hL⟩ := hstab m m.2 h'
        exact ⟨Lm, fun v => Subtype.ext (hL v)⟩
      linear_stab := fun Lm => by
        obtain ⟨m, hm, h⟩ := hstab' Lm
        exact ⟨⟨m, hm⟩, fun v => Subtype.ext (h v)⟩ }
  have : ((ℛ).subgroupOf 𝒩).Normal := Subgroup.normal_in_normalizer
  obtain ⟨-, -, -, C, ⟨hCD', -, -, -⟩, -, -, hCn, -, hAC', hDRC', hRC', -⟩ :=
    binary_symmetric_three_canonical_order512_subgroup H (BinarySymThreeOrbit.layerSub θ' ⊤)
      (BinarySymThreeOrbit.layerSub θ' BinarySymThreeOrbit.altSym) (CFSG.Assembly.pCore 2 𝒩)
      (fun _ => ⟨fun ⟨B, _, h⟩ => ⟨B, h⟩, fun ⟨B, h⟩ => ⟨B, AddSubgroup.mem_top B, h⟩⟩)
      (fun _ => ⟨fun ⟨B, hB, h⟩ => ⟨B, hB, h⟩, fun ⟨B, hB, h⟩ => ⟨B, hB, h⟩⟩) rfl
  have hA' : ∀ x : 𝒩, x ∈ BinarySymThreeOrbit.layerSub θ' ⊤ ↔ (x : G) ∈ 𝒜 := fun x => by
    rw [BinarySymThreeOrbit.mem_layerSub, mem_pullSub_iff φ he]
    constructor
    · rintro ⟨B, -, rfl⟩
      exact ⟨Multiplicative.ofAdd B, (RadicalLabels.radHom_tau φ he hzC hz B).symm⟩
    · rintro ⟨B, hB⟩
      exact ⟨Multiplicative.toAdd B, AddSubgroup.mem_top _,
        Subtype.ext (hB.symm.trans (RadicalLabels.radHom_tau φ he hzC hz _).symm)⟩
  set CG := C.map (Subgroup.subtype _) with hCG
  have hRS := radical_le_stab hzC hinf hz hb hnd hV φ he
  have hCGn : ∀ n ∈ 𝒩, ∀ c ∈ CG, n * c * n⁻¹ ∈ CG := by
    rintro n hn _ ⟨c, hc, rfl⟩
    exact ⟨⟨n, hn⟩ * c * ⟨n, hn⟩⁻¹, hCn.conj_mem c hc ⟨n, hn⟩, rfl⟩
  have hCGD : CG ≤ D := by
    rw [hDpcore]
    exact map_mono hCD'
  have hCR : ∀ x ∈ CG, x ∈ ℛ → x ∈ 𝒜 := by
    rintro _ ⟨c, hc, rfl⟩ hcR
    have h : c ∈ (ℛ).subgroupOf 𝒩 ⊓ C := mem_inf.2 ⟨mem_subgroupOf.2 hcR, hc⟩
    rw [hRC'] at h
    exact (hA' c).1 h
  have hDRC : ∀ d ∈ D, ∃ r ∈ ℛ, ∃ c ∈ CG, r * c = d := by
    intro d hd
    rw [hDpcore] at hd
    obtain ⟨d', hd', rfl⟩ := hd
    have hd'' : d' ∈ (((ℛ).subgroupOf 𝒩 : Subgroup 𝒩) : Set 𝒩) * (C : Set 𝒩) := by
      rw [← hDRC']
      exact hd'
    obtain ⟨r, hr, c, hc, rfl⟩ := Set.mem_mul.1 hd''
    exact ⟨r, mem_subgroupOf.1 hr, c, ⟨c, hc, rfl⟩, rfl⟩
  have hNCS : ∀ n ∈ 𝒩, ∃ c ∈ CG, ∃ s ∈ 𝒮, c * s = n := by
    intro n hn
    have hn' : n ∈ (D : Set G) * ((𝒮 : Subgroup G) : Set G) := by
      rw [hDN]
      exact hn
    obtain ⟨d, hd, s, hs, rfl⟩ := Set.mem_mul.1 hn'
    obtain ⟨r, hr, c, hc, rfl⟩ := hDRC d hd
    exact ⟨r * c * r⁻¹, hCGn r (le_normalizer hr) c hc, r * s, mul_mem (hRS hr) hs,
      by group⟩
  have hAJ : 𝒜 ≤ ℒ := fun a ha => mem_inf.2 ⟨le_normalizer ha, pullSub_le φ _ ha⟩
  have hCS : ∀ s : 𝒮, (s : G) ∈ CG → (s : G) ∈ ℒ := fun s hs => by
    have h : (s : G) ∈ D ⊓ 𝒮 := mem_inf.2 ⟨hCGD hs, s.2⟩
    rw [hDN₀] at h
    exact hAJ (hCR _ hs h)
  have hzS : z ∈ 𝒮 := hRS (mem_sup_right (mem_zpowers z))
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hcover : ∀ s ∈ 𝒮, s ∈ ℒ ∨ s * z ∈ ℒ := fun s hs => by
    rw [(stab_eq hzC hsup hinf φ (e := e)).1,
      mem_sup_of_le_centralizer (zpowers_le_centralizer_levi hzC φ)] at hs
    obtain ⟨l, hl, t, ht, rfl⟩ := hs
    rcases eq_one_or_eq_of_mem_zpowers hz ht with rfl | rfl
    · left
      rwa [mul_one]
    · right
      rwa [mul_assoc, hzz, mul_one]
  obtain ⟨χ₀, hχ₀K, hχ₀z⟩ := exists_hom_of_index_two (S := 𝒮) (K := ℒ) hzS
    (fun h => notMem_of_inf_eq_bot hinf hz (mem_inf.1 h).2)
    (fun s hs => mem_centralizer_singleton_iff.1 (mem_inf.1 hs).2) (hzz ▸ one_mem _) hcover
  obtain ⟨χ, hχ⟩ := exists_hom_extend (N := 𝒩) (C := CG) (S := 𝒮) inf_le_left hCGn hNCS χ₀
    fun s hs => hχ₀K s (hCS s hs)
  have hzN : z ∈ 𝒩 := (mem_inf.1 hzS).1
  have hfix : ∀ x : G, (∀ p ∈ ℛ, x * p * x⁻¹ ∈ 𝒩) → x ∈ 𝒩 := by
    intro x hx
    have hF : (ℛ).map (MulAut.conj x).toMonoidHom = ℛ :=
      huniq _ (by rintro _ ⟨p, hp, rfl⟩; exact hx p hp)
        (BinarySymThreeOrbit.isElemAbelian_map hRea _)
        (by rw [BinarySymThreeOrbit.card_map_conj, hR128])
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [← hF]
      exact ⟨h, hh, rfl⟩
    · intro hh
      rw [← hF, BinarySymThreeOrbit.mem_map_conj] at hh
      rwa [show x⁻¹ * (x * h * x⁻¹) * x = h by group] at hh
  exact ⟨χ.transfer, transfer_eq_of_unique_fixed_coset hzN hzz
    (BinarySymThreeOrbit.isPGroup_of_isElemAbelian hRea) le_normalizer
    (fun p hp => BinarySymThreeOrbit.elemAbelian_comm hRea hp (mem_sup_right (mem_zpowers z)))
    hfix χ ((hχ ⟨z, hzS⟩).trans hχ₀z)⟩

end Setting

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.DegreeEight

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Subgroup Module Matrix MulAction SymplecticFlag CFSG.Assembly.LowTwoRank FusionOrbits
  DegreeEight
open LinearMap (BilinForm)
open scoped Pointwise BinarySymThreeOrbit

theorem standard_binary_symplectic_six_full_rank_one_eight_orbit_exclusion {G : Type} [Group G]
    [Finite G] (hG : CFSG.oddCore G = ⊥) {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) (hLn : ¬ L.Normal)
    (hZ : center L = ⊥) (hmodel : CFSG.Blueprint.LieModel L .PSp 3 2 1)
    (T : Sylow 2 (centralizer (L : Set G)))
    (hT : IsCyclic (T : Subgroup (centralizer (L : Set G)))) {z : G}
    (hzT : z ∈ (T : Subgroup (centralizer (L : Set G))).map (centralizer (L : Set G)).subtype)
    (hz : orderOf z = 2) (hH : CFSG.oddCore (centralizer ({z} : Set G)) = ⊥) :
    ∀ {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
      {b : BilinForm (ZMod 2) V}, b.IsAlt → b.Nondegenerate → finrank (ZMod 2) V = 6 →
      ∀ φ : L ≃* bilinIsometryGroup b,
      ∀ {W : Submodule (ZMod 2) V}, IsTotallyIsotropic b W → finrank (ZMod 2) W = 3 →
      ∀ e : Basis (Fin 3 ⊕ Fin 3) (ZMod 2) V, IsSymplecticBasis b e → W = lagrangianOf e →
        let A := pullSub φ (pointwiseStabilizer b W)
        let R := A ⊔ zpowers z
        let M := normalizer (R : Set G)
        conjClass M z = {x | ∃ (v : Fin 3 → ZMod 2) (a : G) (ha : a ∈ L), x = z * a ∧
          LinearMap.toMatrix e e (linOf (φ ⟨a, ha⟩)) = fromBlocks 1 (vecMulVec v v) 0 1} →
        ∃ ν : G →* Multiplicative (ZMod 2), Function.Surjective ν ∧
          ν z = Multiplicative.ofAdd 1 ∧ z ∉ commutator G ∧ ν.ker.Normal ∧ ν.ker.index = 2 ∧
          commutator G ≠ ⊤ ∧ (IsSimpleGroup G → ∀ a b : G, a * b = b * a) := by
  obtain ⟨-, hzC, hsup, hinf, -⟩ :=
    standard_binary_symplectic_six_fusion_orbit_lengths.{u} hG hL hLn hZ hmodel T hT hzT hz hH
  intro V _ _ _ b hb hnd hV φ W _ _ e he hWe
  subst hWe
  intro A R M hΩ
  obtain ⟨ν, hν⟩ := exists_character_of_rankOne_orbit hzC hsup hinf hz hb hnd hV φ he hΩ
  exact ⟨ν, (consequences_of_character ν hν).1, hν, (consequences_of_character ν hν).2⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
