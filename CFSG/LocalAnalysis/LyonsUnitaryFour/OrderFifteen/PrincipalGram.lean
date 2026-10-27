module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.SixteenCharacters
public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.OddQuotient
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Blocks.SylowKernel

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators

section Orbits

variable {H : Type*} [Group H] [Finite H]

theorem normalizerMonoidHom_inv_pow_injective {P : Subgroup H}
    (hidx : ((Subgroup.centralizer (P : Set H)).subgroupOf
      (Subgroup.normalizer (P : Set H))).index = 5)
    (hirr : ∀ A : Subgroup H, A ≤ P →
      (∀ n ∈ Subgroup.normalizer (P : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) → A = ⊥ ∨ A = P)
    (n : Subgroup.normalizer (P : Set H)) (hnC : (n : H) ∉ Subgroup.centralizer (P : Set H))
    {x : P} (hx : x ≠ 1) :
    Function.Injective (fun k : Fin 5 => Subgroup.normalizerMonoidHom P (n ^ (k : ℕ))⁻¹ x) := by
  have key : ∀ a b : Fin 5, (a : ℕ) < b →
      Subgroup.normalizerMonoidHom P (n ^ (a : ℕ))⁻¹ x =
        Subgroup.normalizerMonoidHom P (n ^ (b : ℕ))⁻¹ x → False := by
    intro a b hab h
    have hcoe := congrArg Subtype.val h
    rw [coe_normalizerMonoidHom_inv_pow, coe_normalizerMonoidHom_inv_pow] at hcoe
    have hfix : (n : H) ^ ((b : ℕ) - a) * x * ((n : H) ^ ((b : ℕ) - a))⁻¹ = x := by
      have hsplit : (n : H) ^ (b : ℕ) = (n : H) ^ ((b : ℕ) - a) * (n : H) ^ (a : ℕ) := by
        rw [← pow_add, Nat.sub_add_cancel hab.le]
      calc (n : H) ^ ((b : ℕ) - a) * x * ((n : H) ^ ((b : ℕ) - a))⁻¹ =
          (n : H) ^ (b : ℕ) * (((n : H) ^ (a : ℕ))⁻¹ * x * (n : H) ^ (a : ℕ)) *
            ((n : H) ^ (b : ℕ))⁻¹ := by rw [hsplit]; group
        _ = x := by rw [hcoe]; group
    exact hx (Subtype.ext (eq_one_of_pow_conj_eq hidx hirr n.2 hnC x.2
      (by have := b.2; omega) hfix))
  intro j k hjk
  simp only at hjk
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · exact key j k h hjk
  · exact key k j h hjk.symm

theorem isConj_iff_exists_inv_pow_conj (S : Sylow 2 H)
    (hcomm : ∀ x ∈ (S : Subgroup H), ∀ y ∈ (S : Subgroup H), x * y = y * x)
    (hidx : ((Subgroup.centralizer ((S : Subgroup H) : Set H)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup H) : Set H))).index = 5)
    {n : H} (hnN : n ∈ Subgroup.normalizer ((S : Subgroup H) : Set H))
    (hnC : n ∉ Subgroup.centralizer ((S : Subgroup H) : Set H))
    {x y : H} (hx : x ∈ (S : Subgroup H)) (hy : y ∈ (S : Subgroup H)) :
    IsConj x y ↔ ∃ k < 5, (n ^ k)⁻¹ * x * n ^ k = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isConj_iff.mp h
    have : IsMulCommutative (S : Subgroup H) :=
      ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
    have hy' : c⁻¹⁻¹ * x * c⁻¹ ∈ (S : Subgroup H) := by rw [inv_inv, hc]; exact hy
    obtain ⟨m, hm, hmeq⟩ := Sylow.conj_eq_normalizer_conj_of_mem S x c⁻¹ hx hy'
    obtain ⟨k, hk, hkc⟩ := exists_pow_inv_mul_mem_centralizer hidx hnN hnC hm
    refine ⟨k, hk, ?_⟩
    have hxk : (n ^ k)⁻¹ * x * n ^ k ∈ (S : Subgroup H) := by
      have hnk := (Subgroup.normalizer ((S : Subgroup H) : Set H)).pow_mem hnN k
      have := (Subgroup.mem_normalizer_iff''.mp hnk x).mp hx
      exact this
    have hcx := (Subgroup.mem_centralizer_iff.mp hkc) _ hxk
    rw [← hc]
    calc (n ^ k)⁻¹ * x * n ^ k
        = ((n ^ k)⁻¹ * m)⁻¹ * ((n ^ k)⁻¹ * x * n ^ k * ((n ^ k)⁻¹ * m)) := by
          rw [hcx]
          group
      _ = m⁻¹ * x * m := by group
      _ = c⁻¹⁻¹ * x * c⁻¹ := hmeq.symm
      _ = c * x * c⁻¹ := by rw [inv_inv]
  · rintro ⟨k, -, hk⟩
    exact isConj_iff.mpr ⟨(n ^ k)⁻¹, by rw [inv_inv]; exact hk⟩

open scoped Classical in
theorem sum_isConj_eq_sum_inv_pow_orbit [Fintype H] (S : Sylow 2 H)
    (hcomm : ∀ x ∈ (S : Subgroup H), ∀ y ∈ (S : Subgroup H), x * y = y * x)
    (hidx : ((Subgroup.centralizer ((S : Subgroup H) : Set H)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup H) : Set H))).index = 5)
    (hirr : ∀ A : Subgroup H, A ≤ S →
      (∀ n ∈ Subgroup.normalizer ((S : Subgroup H) : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
        A = ⊥ ∨ A = S)
    (n : Subgroup.normalizer ((S : Subgroup H) : Set H))
    (hnC : (n : H) ∉ Subgroup.centralizer ((S : Subgroup H) : Set H))
    {x : (S : Subgroup H)} (hx : x ≠ 1) (g : ↥(S : Subgroup H) → ℂ) :
    ∑ y : (S : Subgroup H), (if IsConj (x : H) (y : H) then g y else 0) =
      ∑ k : Fin 5, g (Subgroup.normalizerMonoidHom (S : Subgroup H) (n ^ (k : ℕ))⁻¹ x) := by
  classical
  rw [← Finset.sum_filter]
  have himage : (Finset.univ.filter fun y : (S : Subgroup H) => IsConj (x : H) (y : H)) =
      Finset.univ.image
        (fun k : Fin 5 => Subgroup.normalizerMonoidHom (S : Subgroup H) (n ^ (k : ℕ))⁻¹ x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [isConj_iff_exists_inv_pow_conj S hcomm hidx n.2 hnC x.2 y.2]
    constructor
    · rintro ⟨k, hk, hky⟩
      refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
      rw [coe_normalizerMonoidHom_inv_pow]
      exact hky
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, by rw [coe_normalizerMonoidHom_inv_pow]⟩
  rw [himage, Finset.sum_image (fun a _ b _ h =>
    normalizerMonoidHom_inv_pow_injective hidx hirr n hnC hx h)]

theorem exists_conj_mem_sylow_ne_one (S : Sylow 2 H) {t : H} (ht : orderOf t = 2) :
    ∃ h : H, h * t * h⁻¹ ∈ (S : Subgroup H) ∧ h * t * h⁻¹ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, -, hh⟩ := exists_conj_mem_sylow_of_le S le_top (Subgroup.mem_top t)
    ⟨1, by rw [pow_one, ← ht]; exact pow_orderOf_eq_one t⟩
  refine ⟨h, hh, fun h1 => ?_⟩
  have hord : orderOf (h * t * h⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
  rw [h1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem card_involution_classes_eq_three (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Multiplicative SixteenVector)
    (hidx : ((Subgroup.centralizer ((S : Subgroup H) : Set H)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup H) : Set H))).index = 5)
    (hirr : ∀ A : Subgroup H, A ≤ S →
      (∀ n ∈ Subgroup.normalizer ((S : Subgroup H) : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
        A = ⊥ ∨ A = S)
    (n : Subgroup.normalizer ((S : Subgroup H) : Set H))
    (hnC : (n : H) ∉ Subgroup.centralizer ((S : Subgroup H) : Set H)) :
    Nat.card {c : ConjClasses H // ∃ x : H, orderOf x = 2 ∧ ConjClasses.mk x = c} = 3 := by
  classical
  have : Fintype H := Fintype.ofFinite H
  obtain ⟨hcard16, hcomm, hsq⟩ := elementarySixteen_facts e
  have hXcard : Fintype.card {x : (S : Subgroup H) // x ≠ 1} = 15 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hcard16]
  let f : {x : (S : Subgroup H) // x ≠ 1} → {x : (S : Subgroup H) // x ≠ 1} := fun x =>
    ⟨Subgroup.normalizerMonoidHom (S : Subgroup H) n⁻¹ x, fun h => x.2 (by
      have := congrArg (Subgroup.normalizerMonoidHom (S : Subgroup H) n) h
      rwa [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply,
        map_one] at this)⟩
  have hfiter : ∀ (j : ℕ) (x : {x : (S : Subgroup H) // x ≠ 1}),
      (f^[j] x).1 = Subgroup.normalizerMonoidHom (S : Subgroup H) (n ^ j)⁻¹ x.1 := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change Subgroup.normalizerMonoidHom (S : Subgroup H) n⁻¹ (f^[j] x).1 = _
      rw [ih, pow_succ, mul_inv_rev, map_mul, MulAut.mul_apply]
  have h5 : ∀ x, f^[5] x = x := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    rw [hfiter, coe_normalizerMonoidHom_inv_pow]
    have hc := (Subgroup.mem_centralizer_iff.mp (pow_five_mem_centralizer hidx n.2)) x.1 x.1.2
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hfix : ∀ x, f x ≠ x := by
    intro x h
    have hcoe := congrArg (fun y : {x : (S : Subgroup H) // x ≠ 1} => ((y.1 : _) : H)) h
    simp only [f, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inv,
      inv_inv] at hcoe
    apply x.2
    apply Subtype.ext
    apply eq_one_of_conj_eq_of_generator hidx hirr n.2 hnC x.1.2
    calc (n : H) * x.1 * (n : H)⁻¹ = (n : H) * ((n : H)⁻¹ * (x.1 : H) * n) * (n : H)⁻¹ := by
          rw [hcoe]
      _ = x.1 := by group
  obtain ⟨r, hr⟩ := exists_three_free_orbits hXcard f h5 hfix
  have hord : ∀ i, orderOf ((r i).1 : H) = 2 := by
    intro i
    apply orderOf_eq_prime
    · rw [pow_two]; exact hsq _ (r i).1.2
    · intro h1
      exact (r i).2 (Subtype.ext h1)
  let ι : Fin 3 → {c : ConjClasses H // ∃ x : H, orderOf x = 2 ∧ ConjClasses.mk x = c} :=
    fun i => ⟨ConjClasses.mk ((r i).1 : H), _, hord i, rfl⟩
  have hconj_orbit : ∀ (i : Fin 3) (y : {x : (S : Subgroup H) // x ≠ 1}),
      IsConj ((r i).1 : H) (y.1 : H) → ∃ k : Fin 5, y = f^[(k : ℕ)] (r i) := by
    intro i y hy
    obtain ⟨k, hk, hky⟩ := (isConj_iff_exists_inv_pow_conj S hcomm hidx n.2 hnC (r i).1.2
      y.1.2).mp hy
    refine ⟨⟨k, hk⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [hfiter, coe_normalizerMonoidHom_inv_pow]
    exact hky.symm
  have hbij : Function.Bijective ι := by
    constructor
    · intro i j hij
      have h := congrArg Subtype.val hij
      simp only [ι, ConjClasses.mk_eq_mk_iff_isConj] at h
      obtain ⟨k, hk⟩ := hconj_orbit i (r j) h
      obtain ⟨ik, -, huniq⟩ := hr (r j)
      have h1 := huniq (j, 0) (by simp)
      have h2 := huniq (i, k) hk
      exact (congrArg Prod.fst (h2.trans h1.symm))
    · rintro ⟨c, x, hx, rfl⟩
      obtain ⟨h, hhS, hh1⟩ := exists_conj_mem_sylow_ne_one S hx
      set y : {x : (S : Subgroup H) // x ≠ 1} := ⟨⟨h * x * h⁻¹, hhS⟩, fun h' => hh1 (by
        have := congrArg Subtype.val h'
        exact this)⟩ with hy
      obtain ⟨ik, hik, -⟩ := hr y
      refine ⟨ik.1, Subtype.ext ?_⟩
      simp only [ι, ConjClasses.mk_eq_mk_iff_isConj]
      have hxy : IsConj x (h * x * h⁻¹) := isConj_iff.mpr ⟨h, rfl⟩
      have hyr : IsConj (h * x * h⁻¹) ((r ik.1).1 : H) := by
        have hcoe := congrArg (fun z : {x : (S : Subgroup H) // x ≠ 1} => ((z.1 : _) : H)) hik
        simp only [hy] at hcoe
        rw [hcoe, hfiter, coe_normalizerMonoidHom_inv_pow]
        exact isConj_iff.mpr ⟨(n : H) ^ (ik.2 : ℕ), by group⟩
      exact (hxy.trans hyr).symm
  rw [← Nat.card_eq_of_bijective ι hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem exists_centralizer_normal_complement (S : Sylow 2 H)
    (hcomm : ∀ x ∈ (S : Subgroup H), ∀ y ∈ (S : Subgroup H), x * y = y * x)
    (hidx : ((Subgroup.centralizer ((S : Subgroup H) : Set H)).subgroupOf
      (Subgroup.normalizer ((S : Subgroup H) : Set H))).index = 5)
    (hirr : ∀ A : Subgroup H, A ≤ S →
      (∀ n ∈ Subgroup.normalizer ((S : Subgroup H) : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
        A = ⊥ ∨ A = S)
    {n : H} (hnN : n ∈ Subgroup.normalizer ((S : Subgroup H) : Set H))
    (hnC : n ∉ Subgroup.centralizer ((S : Subgroup H) : Set H))
    {u : H} (hu : u ∈ (S : Subgroup H)) (hu1 : u ≠ 1) :
    ∃ (K : Subgroup (Subgroup.centralizer ({u} : Set H))) (_ : K.Normal),
      Nat.Coprime 2 (Nat.card K) ∧ IsPGroup 2 (Subgroup.centralizer ({u} : Set H) ⧸ K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({u} : Set H) with hC
  have hSC : (S : Subgroup H) ≤ C := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm s hs u hu)
  set Q : Sylow 2 C := S.subtype hSC with hQ
  have hQcoe : (Q : Subgroup C) = (S : Subgroup H).subgroupOf C := Sylow.coe_subtype _ _
  have hle : Subgroup.normalizer ((Q : Subgroup C) : Set C) ≤
      Subgroup.centralizer ((Q : Subgroup C) : Set C) := by
    intro m hm
    have hmN : (m : H) ∈ Subgroup.normalizer ((S : Subgroup H) : Set H) := by
      have h : (m : H) ∈ (Subgroup.normalizer (((S : Subgroup H).subgroupOf C :
          Subgroup C) : Set C)).map C.subtype := ⟨m, by rw [← hQcoe]; exact hm, rfl⟩
      rw [map_normalizer_subgroupOf_eq hSC] at h
      exact h.1
    obtain ⟨k, hk, hkc⟩ := exists_pow_inv_mul_mem_centralizer hidx hnN hnC hmN
    have hk0 : k = 0 := by
      by_contra hk0
      apply hu1
      apply eq_one_of_pow_conj_eq hidx hirr hnN hnC hu (k := k) (by omega)
      have hmu : (m : H) * u = u * m := (Subgroup.mem_centralizer_singleton_iff.mp m.2)
      have hcu : ((n ^ k)⁻¹ * m) * u = u * ((n ^ k)⁻¹ * m) :=
        ((Subgroup.mem_centralizer_iff.mp hkc) u hu).symm
      have hcu' : ((n ^ k)⁻¹ * m)⁻¹ * u = u * ((n ^ k)⁻¹ * m)⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hcu, mul_assoc, mul_inv_cancel, mul_one]
      have hnk : n ^ k * u = u * n ^ k := by
        calc n ^ k * u = (m : H) * (((n ^ k)⁻¹ * m)⁻¹ * u) := by group
          _ = (m : H) * (u * ((n ^ k)⁻¹ * m)⁻¹) := by rw [hcu']
          _ = ((m : H) * u) * ((n ^ k)⁻¹ * m)⁻¹ := by group
          _ = (u * m) * ((n ^ k)⁻¹ * m)⁻¹ := by rw [hmu]
          _ = u * n ^ k := by group
      rw [hnk, mul_inv_cancel_right]
    subst hk0
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    have hq' : (q : H) ∈ (S : Subgroup H) := by
      rw [SetLike.mem_coe, hQcoe, Subgroup.mem_subgroupOf] at hq
      exact hq
    simp only [pow_zero, inv_one, one_mul] at hkc
    exact (Subgroup.mem_centralizer_iff.mp hkc) _ hq'
  have hcomp := MonoidHom.ker_transferSylow_isComplement' Q hle
  refine ⟨(MonoidHom.transferSylow Q hle).ker, inferInstance, ?_, ?_⟩
  · rw [← hcomp.index_eq_card]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr Q.not_dvd_index
  · obtain ⟨a, ha⟩ := Q.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a)
    rw [← Subgroup.index, hcomp.symm.index_eq_card, ha]

end Orbits

section Projection

open scoped Classical

variable {H : Type} [Group H] [Fintype H] (basis : FiniteIrreducibleCharacterBasis H)

@[expose] noncomputable def blocksInduction (B : Finset basis.index) (P : Subgroup H)
    (θ : P → ℂ) : H → ℂ :=
  fun g => ∑ l ∈ B, BlocksInnerProduct (inducedFunction P θ) (basis.representation l).character *
    (basis.representation l).character g

theorem basis_character_mem_blocksVChar (l : basis.index) :
    (basis.representation l).character ∈ BlocksVChar H := by
  rw [blocksVChar_eq_virtualCharacters, Submodule.mem_toAddSubgroup]
  exact character_mem_virtualCharacters _

theorem blocksInnerProduct_basis (l m : basis.index) :
    BlocksInnerProduct (basis.representation l).character (basis.representation m).character =
      if l = m then 1 else 0 := by
  rw [blocksInnerProduct_eq_characterPairing _ (basis_character_mem_blocksVChar basis m),
    characterPairing_irreducible _ _ (basis.irreducible l) (basis.irreducible m)]
  by_cases h : l = m
  · subst h
    simp
  · rw [ite_eq_right (fun h' => h (basis.distinct h')), ite_eq_right h]

theorem blocksInnerProduct_sum_sum (B : Finset basis.index) (a b : basis.index → ℂ) :
    BlocksInnerProduct (fun g => ∑ l ∈ B, a l * (basis.representation l).character g)
      (fun g => ∑ m ∈ B, b m * (basis.representation m).character g) =
      ∑ l ∈ B, a l * starRingEnd ℂ (b l) := by
  have horth := blocksInnerProduct_basis basis
  have hexp : BlocksInnerProduct (fun g => ∑ l ∈ B, a l * (basis.representation l).character g)
      (fun g => ∑ m ∈ B, b m * (basis.representation m).character g) =
      ∑ l ∈ B, ∑ m ∈ B, a l * starRingEnd ℂ (b m) *
        BlocksInnerProduct (basis.representation l).character
          (basis.representation m).character := by
    unfold BlocksInnerProduct
    have hpt : ∀ g : H, (∑ l ∈ B, a l * (basis.representation l).character g) *
        starRingEnd ℂ (∑ m ∈ B, b m * (basis.representation m).character g) =
        ∑ l ∈ B, ∑ m ∈ B, a l * starRingEnd ℂ (b m) * ((basis.representation l).character g *
          starRingEnd ℂ ((basis.representation m).character g)) := by
      intro g
      rw [map_sum, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro m _
      rw [map_mul]
      ring
    simp_rw [hpt]
    calc (Nat.card H : ℂ)⁻¹ * ∑ g : H, ∑ l ∈ B, ∑ m ∈ B, a l * starRingEnd ℂ (b m) *
          ((basis.representation l).character g *
            starRingEnd ℂ ((basis.representation m).character g))
        = ∑ g : H, ∑ l ∈ B, ∑ m ∈ B, (Nat.card H : ℂ)⁻¹ * (a l * starRingEnd ℂ (b m) *
          ((basis.representation l).character g *
            starRingEnd ℂ ((basis.representation m).character g))) := by
          simp_rw [Finset.mul_sum]
      _ = ∑ l ∈ B, ∑ g : H, ∑ m ∈ B, (Nat.card H : ℂ)⁻¹ * (a l * starRingEnd ℂ (b m) *
          ((basis.representation l).character g *
            starRingEnd ℂ ((basis.representation m).character g))) := Finset.sum_comm
      _ = ∑ l ∈ B, ∑ m ∈ B, ∑ g : H, (Nat.card H : ℂ)⁻¹ * (a l * starRingEnd ℂ (b m) *
          ((basis.representation l).character g *
            starRingEnd ℂ ((basis.representation m).character g))) :=
          Finset.sum_congr rfl (fun l _ => Finset.sum_comm)
      _ = _ := by
          apply Finset.sum_congr rfl
          intro l _
          apply Finset.sum_congr rfl
          intro m _
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro g _
          ring
  rw [hexp]
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.sum_eq_single l]
  · rw [horth, ite_eq_left rfl, mul_one]
  · intro m _ hm
    rw [horth, ite_eq_right (Ne.symm hm), mul_zero]
  · intro h
    exact absurd hl h

theorem blocksInduction_coeff (P : Subgroup H) (θ : P → ℂ) (l : basis.index) :
    BlocksInnerProduct (inducedFunction P θ) (basis.representation l).character =
      BlocksInnerProduct θ (fun x : P => (basis.representation l).character x) :=
  blocksInnerProduct_inducedFunction_left P θ _ (fun g h => Representation.char_conj _ g h)

theorem blocksInnerProduct_blocksInduction (B : Finset basis.index) (P : Subgroup H)
    (θ η : P → ℂ) :
    BlocksInnerProduct (blocksInduction basis B P θ) (blocksInduction basis B P η) =
      ∑ l ∈ B, BlocksInnerProduct θ (fun x : P => (basis.representation l).character x) *
        starRingEnd ℂ
          (BlocksInnerProduct η (fun x : P => (basis.representation l).character x)) := by
  unfold blocksInduction
  rw [blocksInnerProduct_sum_sum]
  simp_rw [blocksInduction_coeff]

theorem blocksInduction_mem_virtualCharacters (B : Finset basis.index) (P : Subgroup H)
    {θ : P → ℂ} (hθ : θ ∈ virtualCharacters P) :
    blocksInduction basis B P θ ∈ virtualCharacters H := by
  have hind := inducedFunction_mem_virtualCharacters P hθ
  have hint : ∀ l : basis.index, ∃ z : ℤ,
      BlocksInnerProduct (inducedFunction P θ) (basis.representation l).character = z := by
    intro l
    rw [blocksInnerProduct_eq_characterPairing _ (basis_character_mem_blocksVChar basis l)]
    exact characterPairing_virtual_integer _ _ hind (character_mem_virtualCharacters _)
  choose z hz using hint
  have heq : blocksInduction basis B P θ = ∑ l ∈ B, z l • (basis.representation l).character := by
    funext g
    rw [Finset.sum_apply]
    simp only [blocksInduction, hz]
    apply Finset.sum_congr rfl
    intro l _
    rw [Pi.smul_apply, zsmul_eq_mul]
  rw [heq]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (character_mem_virtualCharacters _)

variable (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
  [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]

theorem blocksInduction_eq_zero_of_odd (principal : basis.index) (P : Sylow 2 H)
    (θ : ↥(P : Subgroup H) → ℂ) (hθ : θ 1 = 0) (g : H) (hg : Odd (orderOf g)) :
    blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
      (P : Subgroup H) θ g = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  have hcol : ∀ x : (P : Subgroup H), x ≠ 1 →
      ∑ l ∈ B, starRingEnd ℂ ((basis.representation l).character x) *
        (basis.representation l).character g = 0 := by
    intro x hx
    obtain ⟨k, hk⟩ := P.isPGroup' x
    have hxk : orderOf (x : H) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      have := congrArg Subtype.val hk
      simpa using this)
    have hnc : ¬ IsConj (1 : H) (x : H) := by
      intro h
      apply hx
      apply Subtype.ext
      exact isConj_one_right.mp h
    have h := coefficientBlock_section_column_orthogonality basis ideal 2 principal 1 (x : H) g 1
      0 k (by simp) hxk (Nat.coprime_two_left.mpr hg) (by simp) (Commute.one_left g)
      (Commute.one_right _) hnc
    simp only [one_mul, mul_one] at h
    rw [← h]
    apply Finset.sum_congr rfl
    intro l _
    rw [finite_character_conjugate_inverse, mul_comm]
  unfold blocksInduction
  simp_rw [blocksInduction_coeff]
  unfold BlocksInnerProduct
  have hrearr : ∑ l ∈ B, ((Nat.card (P : Subgroup H) : ℂ)⁻¹ * ∑ x : (P : Subgroup H),
      θ x * starRingEnd ℂ ((basis.representation l).character x)) *
        (basis.representation l).character g =
      (Nat.card (P : Subgroup H) : ℂ)⁻¹ * ∑ x : (P : Subgroup H), θ x * ∑ l ∈ B,
        starRingEnd ℂ ((basis.representation l).character x) *
          (basis.representation l).character g := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hrearr, Finset.sum_eq_zero, mul_zero]
  intro x _
  by_cases hx : x = 1
  · rw [hx, hθ, zero_mul]
  · rw [hcol x hx, mul_zero]

theorem blocksInduction_gram (P : Sylow 2 H) (e : (P : Subgroup H) ≃* Multiplicative SixteenVector)
    (hidx : ((Subgroup.centralizer ((P : Subgroup H) : Set H)).subgroupOf
      (Subgroup.normalizer ((P : Subgroup H) : Set H))).index = 5)
    (hirr : ∀ A : Subgroup H, A ≤ P →
      (∀ n ∈ Subgroup.normalizer ((P : Subgroup H) : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
        A = ⊥ ∨ A = P)
    (n : Subgroup.normalizer ((P : Subgroup H) : Set H))
    (hnC : (n : H) ∉ Subgroup.centralizer ((P : Subgroup H) : Set H)) (B : Finset basis.index)
    (hK : ∀ x ∈ (P : Subgroup H), x ≠ 1 → ∀ y ∈ (P : Subgroup H),
      ∑ l ∈ B, (basis.representation l).character x *
        starRingEnd ℂ ((basis.representation l).character y) =
          if IsConj x y then 16 else 0)
    (θ η : ↥(P : Subgroup H) → ℂ) (hθ : θ 1 = 0) :
    BlocksInnerProduct (blocksInduction basis B (P : Subgroup H) θ)
        (blocksInduction basis B (P : Subgroup H) η) =
      ∑ j : Fin 5, BlocksInnerProduct θ (sylowConj n j η) := by
  obtain ⟨hcard16, hcomm, -⟩ := elementarySixteen_facts e
  set χ := fun l : basis.index => (basis.representation l).character with hχ
  set c : ℂ := (Nat.card (P : Subgroup H) : ℂ)⁻¹ with hc
  have hc16 : c * 16 = 1 := by rw [hc, hcard16]; norm_num
  have hcconj : starRingEnd ℂ c = c := by rw [hc, map_inv₀, Complex.conj_natCast]
  set D : ↥(P : Subgroup H) → ℂ := fun x => ∑ y : ↥(P : Subgroup H),
    starRingEnd ℂ (η y) * ∑ l ∈ B, starRingEnd ℂ (χ l x) * χ l y with hD
  have hDx : ∀ x : ↥(P : Subgroup H), x ≠ 1 →
      D x = 16 * ∑ j : Fin 5, starRingEnd ℂ (η (Subgroup.normalizerMonoidHom (P : Subgroup H)
        (n ^ (j : ℕ))⁻¹ x)) := by
    intro x hx
    have hinner : ∀ y : ↥(P : Subgroup H), ∑ l ∈ B, starRingEnd ℂ (χ l x) * χ l y =
        if IsConj (x : H) (y : H) then 16 else 0 := by
      intro y
      have h := hK x x.2 (fun h => hx (Subtype.ext h)) y y.2
      have h' := congrArg (starRingEnd ℂ) h
      rw [map_sum] at h'
      simp only [map_mul, Complex.conj_conj] at h'
      rw [show (∑ l ∈ B, starRingEnd ℂ (χ l x) * χ l y) =
        ∑ l ∈ B, starRingEnd ℂ ((basis.representation l).character x) *
          (basis.representation l).character y from rfl, h']
      split_ifs
      · exact map_ofNat (starRingEnd ℂ) 16
      · exact map_zero _
    simp only [hD, hinner]
    rw [Finset.mul_sum]
    have h := sum_isConj_eq_sum_inv_pow_orbit P hcomm hidx hirr n hnC hx
      (fun y => 16 * starRingEnd ℂ (η y))
    rw [← h]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> ring
  rw [blocksInnerProduct_blocksInduction]
  unfold BlocksInnerProduct
  have hLHS : ∑ l ∈ B, (c * ∑ x : ↥(P : Subgroup H), θ x * starRingEnd ℂ (χ l x)) *
      starRingEnd ℂ (c * ∑ y : ↥(P : Subgroup H), η y * starRingEnd ℂ (χ l y)) =
      c * c * ∑ x : ↥(P : Subgroup H), θ x * D x := by
    have hpt : ∀ l : basis.index,
        (c * ∑ x : ↥(P : Subgroup H), θ x * starRingEnd ℂ (χ l x)) *
          starRingEnd ℂ (c * ∑ y : ↥(P : Subgroup H), η y * starRingEnd ℂ (χ l y)) =
        c * c * ∑ x : ↥(P : Subgroup H), ∑ y : ↥(P : Subgroup H),
          θ x * (starRingEnd ℂ (η y) * (starRingEnd ℂ (χ l x) * χ l y)) := by
      intro l
      rw [map_mul, hcconj, map_sum]
      simp only [map_mul, Complex.conj_conj]
      rw [mul_mul_mul_comm, Finset.sum_mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      ring
    simp_rw [hpt]
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp only [hD, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hLHS]
  have hRHS : ∑ j : Fin 5, c * ∑ x : ↥(P : Subgroup H), θ x * starRingEnd ℂ (sylowConj n j η x) =
      c * ∑ x : ↥(P : Subgroup H), θ x * ∑ j : Fin 5, starRingEnd ℂ (η
        (Subgroup.normalizerMonoidHom (P : Subgroup H) (n ^ (j : ℕ))⁻¹ x)) := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.mul_sum]
    rfl
  rw [hRHS]
  have hterm : ∀ x : ↥(P : Subgroup H), θ x * D x = 16 * (θ x * ∑ j : Fin 5,
      starRingEnd ℂ (η (Subgroup.normalizerMonoidHom (P : Subgroup H) (n ^ (j : ℕ))⁻¹ x))) := by
    intro x
    by_cases hx : x = 1
    · rw [hx, hθ]
      ring
    · rw [hDx x hx]
      ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  calc c * c * (16 * ∑ x : ↥(P : Subgroup H), θ x * ∑ j : Fin 5, starRingEnd ℂ (η
        (Subgroup.normalizerMonoidHom (P : Subgroup H) (n ^ (j : ℕ))⁻¹ x)))
      = c * (c * 16) * ∑ x : ↥(P : Subgroup H), θ x * ∑ j : Fin 5, starRingEnd ℂ (η
        (Subgroup.normalizerMonoidHom (P : Subgroup H) (n ^ (j : ℕ))⁻¹ x)) := by ring
    _ = _ := by rw [hc16, mul_one]

end Projection

section Theorem

open scoped Classical

variable {H : Type} [Group H] [Fintype H]

theorem blocksInnerProduct_sub_left {G : Type} [Group G] [Fintype G] (f g h : G → ℂ) :
    BlocksInnerProduct (f - g) h = BlocksInnerProduct f h - BlocksInnerProduct g h := by
  unfold BlocksInnerProduct
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Pi.sub_apply, sub_mul]

theorem blocksInnerProduct_sub_right {G : Type} [Group G] [Fintype G] (f g h : G → ℂ) :
    BlocksInnerProduct f (g - h) = BlocksInnerProduct f g - BlocksInnerProduct f h := by
  unfold BlocksInnerProduct
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Pi.sub_apply, map_sub, mul_sub]

omit [Fintype H] in
theorem sylowConj_sub {P : Subgroup H} (n : Subgroup.normalizer (P : Set H)) (j : ℕ)
    (f g : P → ℂ) : sylowConj n j (f - g) = sylowConj n j f - sylowConj n j g :=
  rfl

omit [Fintype H] in
theorem conjAddChar_one {P : Subgroup H} (e : P ≃* Multiplicative SixteenVector)
    (ψ : AddChar SixteenVector ℂ) : conjAddChar e 1 ψ = ψ := by
  apply sixteenChar_injective e
  funext x
  rw [sixteenChar_conjAddChar, map_one, MulAut.one_apply]

theorem sum_fin_five_ite_and (p : Prop) [Decidable p] :
    ∑ j : Fin 5, (if p ∧ j = 0 then (1 : ℂ) else 0) = if p then 1 else 0 := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ 0) h

theorem blocksInnerProduct_orbit_rep {P : Subgroup H} (e : P ≃* Multiplicative SixteenVector)
    (n : Subgroup.normalizer (P : Set H)) (r : Fin 3 → AddChar SixteenVector ℂ)
    (hr : ∀ ψ : AddChar SixteenVector ℂ, ψ ≠ 0 →
      ∃! ik : Fin 3 × Fin 5, ψ = conjAddChar e (n ^ (ik.2 : ℕ))⁻¹ (r ik.1))
    (hr0 : ∀ i, r i ≠ 0) (i k : Fin 3) (j : Fin 5) :
    BlocksInnerProduct (sixteenChar e (r i)) (sylowConj n j (sixteenChar e (r k))) =
      if i = k ∧ j = 0 then 1 else 0 := by
  rw [sylowConj_sixteenChar, blocksInnerProduct_sixteenChar]
  have hiff : r i = conjAddChar e (n ^ (j : ℕ))⁻¹ (r k) ↔ i = k ∧ j = 0 := by
    obtain ⟨ik, -, huniq⟩ := hr (r i) (hr0 i)
    have h0 : r i = conjAddChar e (n ^ ((0 : Fin 5) : ℕ))⁻¹ (r (i, (0 : Fin 5)).1) := by
      simp only [Fin.val_zero, pow_zero, inv_one, conjAddChar_one]
    constructor
    · intro h
      have h1 := huniq (k, j) h
      have h2 := huniq (i, 0) h0
      have := h1.trans h2.symm
      exact ⟨(congrArg Prod.fst this).symm, congrArg Prod.snd this⟩
    · rintro ⟨rfl, rfl⟩
      exact h0
  by_cases h : i = k ∧ j = 0
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h]

theorem elementary_sixteen_order_five_principal_gram (P : Sylow 2 H)
    (hP : Nonempty ((P : Subgroup H) ≃* Multiplicative (Fin 4 → ZMod 2)))
    (hidx : ((Subgroup.centralizer ((P : Subgroup H) : Set H)).subgroupOf
      (Subgroup.normalizer ((P : Subgroup H) : Set H))).index = 5)
    (hirr : ∀ A : Subgroup H, A ≤ P →
      (∀ n ∈ Subgroup.normalizer ((P : Subgroup H) : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) →
        A = ⊥ ∨ A = P)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) 2]
    (basis : FiniteIrreducibleCharacterBasis H) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) :
    (∃ (n : Subgroup.normalizer ((P : Subgroup H) : Set H))
        (lam : Fin 3 → (↥(P : Subgroup H) → ℂ)),
      (∀ i, lam i ∈ CFSG.BlocksIrr (P : Subgroup H) ∧ lam i ≠ fun _ => 1) ∧
      (∀ μ ∈ CFSG.BlocksIrr (P : Subgroup H), μ ≠ (fun _ => 1) →
        ∃! ij : Fin 3 × Fin 5, μ = sylowConj n ij.2 (lam ij.1)) ∧
      (∀ θ η : ↥(P : Subgroup H) → ℂ, θ 1 = 0 →
        BlocksInnerProduct
            (blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
              principal) (P : Subgroup H) θ)
            (blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
              principal) (P : Subgroup H) η) =
          ∑ j : Fin 5, BlocksInnerProduct θ (sylowConj n j η)) ∧
      BlocksInnerProduct
          (blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (P : Subgroup H) (lam 1 - lam 0))
          (blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (P : Subgroup H) (lam 1 - lam 0)) = 2 ∧
      BlocksInnerProduct
          (blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (P : Subgroup H) (lam 2 - lam 0))
          (blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (P : Subgroup H) (lam 2 - lam 0)) = 2 ∧
      BlocksInnerProduct
          (blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (P : Subgroup H) (lam 1 - lam 0))
          (blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
            principal) (P : Subgroup H) (lam 2 - lam 0)) = 1 ∧
      blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
          principal) (P : Subgroup H) (lam 1 - lam 0) 1 = 0 ∧
      blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal)
          principal) (P : Subgroup H) (lam 2 - lam 0) 1 = 0) ∧
    (∀ θ ∈ virtualCharacters (P : Subgroup H),
      blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
        (P : Subgroup H) θ ∈ virtualCharacters H) ∧
    (∀ θ : ↥(P : Subgroup H) → ℂ, θ 1 = 0 → ∀ g : H, Odd (orderOf g) →
      blocksInduction basis (coefficientBlock basis (localizedComplexIntegerRing ideal) principal)
        (P : Subgroup H) θ g = 0) ∧
    (∀ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
      ∀ g a : H, CFSG.BlocksIsPPart 2 g a → a ≠ 1 →
        (basis.representation l).character g = (basis.representation l).character a) ∧
    (∀ x ∈ (P : Subgroup H), x ≠ 1 → ∀ y ∈ (P : Subgroup H),
      ∑ l ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation l).character x *
          starRingEnd ℂ ((basis.representation l).character y) =
        if IsConj x y then 16 else 0) ∧
    Nat.card {c : ConjClasses H // ∃ x : H, orderOf x = 2 ∧ ConjClasses.mk x = c} = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hP
  obtain ⟨hcard16, hcomm, hsq⟩ := elementarySixteen_facts e
  set Pg := (P : Subgroup H) with hPg
  set B := coefficientBlock basis (localizedComplexIntegerRing ideal) principal with hB
  obtain ⟨n, hnC⟩ : ∃ n : Subgroup.normalizer (Pg : Set H),
      (n : H) ∉ Subgroup.centralizer (Pg : Set H) := by
    by_contra hall
    push Not at hall
    have htop : (Subgroup.centralizer (Pg : Set H)).subgroupOf
        (Subgroup.normalizer (Pg : Set H)) = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_subgroupOf.mpr (hall x)
    rw [htop, Subgroup.index_top] at hidx
    norm_num at hidx
  have hPC : ∀ u ∈ Pg, Pg ≤ Subgroup.centralizer ({u} : Set H) := fun u hu s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm s hs u hu)
  obtain ⟨hconst, hker⟩ := normal_complement_principal_sylow_kernel basis ideal 2 principal
    hprincipal P
    (fun u hu _ => ⟨P.subtype (hPC u hu), by
      rw [Sylow.coe_subtype, inf_eq_left.mpr (hPC u hu)]⟩)
    (fun u hu hu1 => exists_centralizer_normal_complement P hcomm hidx hirr n.2 hnC hu hu1)
  have hK : ∀ x ∈ Pg, x ≠ 1 → ∀ y ∈ Pg,
      ∑ l ∈ B, (basis.representation l).character x *
        starRingEnd ℂ ((basis.representation l).character y) =
          if IsConj x y then 16 else 0 := by
    intro x hx hx1 y hy
    rw [hker x hx hx1 y hy, inf_eq_left.mpr (hPC x hx), hcard16]
    norm_num
  obtain ⟨r, hr0, hr⟩ := exists_three_sixteenChar_orbits e hidx hirr n hnC
  have hval : ∀ a b c d : Fin 3,
      BlocksInnerProduct (blocksInduction basis B Pg (sixteenChar e (r a) - sixteenChar e (r b)))
          (blocksInduction basis B Pg (sixteenChar e (r c) - sixteenChar e (r d))) =
        (if a = c then 1 else 0) - (if a = d then 1 else 0) - (if b = c then 1 else 0) +
          (if b = d then 1 else 0) := by
    intro a b c d
    rw [blocksInduction_gram basis P e hidx hirr n hnC B hK _ _ (by
      rw [Pi.sub_apply, sixteenChar_one, sixteenChar_one, sub_self])]
    simp_rw [sylowConj_sub, blocksInnerProduct_sub_left, blocksInnerProduct_sub_right,
      blocksInnerProduct_orbit_rep e n r hr hr0]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [sum_fin_five_ite_and]
    ring
  refine ⟨⟨n, fun i => sixteenChar e (r i), fun i => ⟨sixteenChar_mem_blocksIrr e _, fun h =>
      hr0 i ((sixteenChar_eq_one_iff e _).mp h)⟩, ?_, fun θ η hθ =>
      blocksInduction_gram basis P e hidx hirr n hnC B hK θ η hθ, ?_, ?_, ?_, ?_, ?_⟩,
    fun θ hθ => blocksInduction_mem_virtualCharacters basis B Pg hθ,
    fun θ hθ g hg => blocksInduction_eq_zero_of_odd basis ideal principal P θ hθ g hg,
    hconst, hK, card_involution_classes_eq_three P e hidx hirr n hnC⟩
  · intro μ hμ hμ1
    obtain ⟨ψ, rfl⟩ := exists_sixteenChar_of_mem_blocksIrr e hμ
    have hψ : ψ ≠ 0 := fun h => hμ1 ((sixteenChar_eq_one_iff e ψ).mpr h)
    obtain ⟨ik, hik, huniq⟩ := hr ψ hψ
    refine ⟨ik, ?_, fun jk hjk => huniq jk ?_⟩
    · dsimp only
      rw [sylowConj_sixteenChar, ← hik]
    · dsimp only at hjk ⊢
      rw [sylowConj_sixteenChar] at hjk
      exact sixteenChar_injective e hjk
  · rw [hval]; norm_num
  · rw [hval]; norm_num
  · rw [hval]; norm_num
  · exact blocksInduction_eq_zero_of_odd basis ideal principal P _ (by
      dsimp only
      rw [Pi.sub_apply, sixteenChar_one, sixteenChar_one, sub_self]) 1 (by simp)
  · exact blocksInduction_eq_zero_of_odd basis ideal principal P _ (by
      dsimp only
      rw [Pi.sub_apply, sixteenChar_one, sixteenChar_one, sub_self]) 1 (by simp)

end Theorem

end CFSG.LyonsUnitaryFour
