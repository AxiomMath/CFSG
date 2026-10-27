module

public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Blueprint.EvenStandardExact
public import CFSG.LocalAnalysis.EvenSmallLie.Setup
public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.LocalAnalysis.ComponentInitial.EvenTwoMultiplier

open Subgroup CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Multiplier

theorem exceptionalOrders_two_cases (t : StatedLieTag) (n f : ℕ) :
    exceptionalOrders t n 2 f = (1, 1) ∨ (t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨
      (t = .PSL ∧ n = 4 ∧ f = 1) ∨ (t = .PSU ∧ n = 4 ∧ f = 1) ∨ (t = .PSp ∧ n = 3 ∧ f = 1) ∨
      (t = .G2 ∧ n = 0 ∧ f = 2) ∨ (t = .F4 ∧ n = 0 ∧ f = 1) ∨
      (t = .POmegaPlus ∧ n = 4 ∧ f = 1) ∨ (t = .PSU ∧ n = 6 ∧ f = 1) ∨
      (t = .twistedB2 ∧ n = 0 ∧ f = 3) ∨ (t = .twistedE6 ∧ n = 0 ∧ f = 1) ∨
      (t = .PSL ∧ n = 3 ∧ f = 2) := by
  unfold exceptionalOrders
  split <;> simp_all

theorem genericOrders_odd (t : StatedLieTag) (n f : ℕ) (h : StatedLieAdmissible t n 2 f) :
    Odd (genericOrders t n 2 f).1 ∧ Odd (genericOrders t n 2 f).2 := by
  obtain ⟨-, hf, h⟩ := h
  have hq : Even (2 ^ f) := (Nat.even_pow' (by omega)).2 even_two
  have hq1 : Odd (2 ^ f - 1) := by
    obtain ⟨k, hk⟩ := hq
    have : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    exact ⟨k - 1, by omega⟩
  have hq2 : Odd (2 ^ f + 1) := hq.add_one
  cases t <;> simp only [genericOrders, hq, ite_true] <;>
    first
    | exact ⟨odd_one, odd_one⟩
    | exact ⟨hq1.of_dvd_nat (Nat.gcd_dvd_right _ _), odd_one⟩
    | exact ⟨hq2.of_dvd_nat (Nat.gcd_dvd_right _ _), odd_one⟩
    | exact absurd rfl h.2
    | exact ⟨((Nat.even_pow' (by have : 4 ≤ n := h; omega)).2 hq).add_one.of_dvd_nat
        (Nat.gcd_dvd_right _ _), odd_one⟩

theorem card_generic (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (generic t n p f) = (genericOrders t n p f).1 * (genericOrders t n p f).2 := by
  simp only [generic, Nat.card_prod]
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    Nat.card_zmod]

theorem card_exceptional (t : StatedLieTag) (n p f : ℕ) :
    Nat.card (exceptional t n p f) =
      (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2 := by
  simp only [exceptional, Nat.card_prod]
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
    Nat.card_zmod]

theorem sq_eq_one_two_one : ∀ b : Multiplicative (ZMod 2) × Multiplicative (ZMod 1), b ^ 2 = 1 := by
  decide

theorem sq_eq_one_two_two : ∀ b : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), b ^ 2 = 1 := by
  decide

theorem surjective_comp_inr_of_odd {A B K : Type*} [Group A] [Group B] [Group K]
    (hA : Odd (Nat.card A)) (hK : IsPGroup 2 K) (Φ : A × B →* K) (hΦ : Function.Surjective Φ) :
    Function.Surjective (Φ.comp (MonoidHom.inr A B)) := by
  intro k
  obtain ⟨⟨a, b⟩, rfl⟩ := hΦ k
  refine ⟨b, ?_⟩
  obtain ⟨m, hm⟩ := hK (Φ (a, 1))
  have h1 : Φ (a, 1) ^ Nat.card A = 1 := by
    rw [← map_pow, Prod.pow_mk, pow_card_eq_one', one_pow, Prod.mk_one_one, map_one]
  have hcop : Nat.Coprime (2 ^ m) (Nat.card A) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hA)
  have ha : Φ (a, 1) = 1 := by
    have := pow_gcd_eq_one.2 ⟨hm, h1⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hab : ((a, b) : A × B) = (a, 1) * (1, b) := by simp
  rw [MonoidHom.comp_apply, hab, map_mul, ha, one_mul]
  rfl

theorem card_le_two_of_sq_eq_one {K : Type*} [Group K] [Finite K] [IsCyclic K]
    (h : ∀ k : K, k ^ 2 = 1) : Nat.card K ≤ 2 := by
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd two_pos (Monoid.exponent_dvd_of_forall_pow_eq_one h)

variable {G : Type} [Group G]

theorem isCyclic_center [Finite G] {L : Subgroup G} (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G)))) (h2 : IsPGroup 2 (center L)) :
    IsCyclic (center L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ι : center L →* centralizer (L : Set G) :=
    { toFun := fun z => ⟨((z : L) : G), CFSG.EvenSmallLie.mem_centralizer_of_mem_center z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : centralizer (L : Set G) => (x : G)) h))
  have hnorm : ι.range.Normal := by
    constructor
    rintro _ ⟨z, rfl⟩ c
    refine ⟨z, Subtype.ext ?_⟩
    have hc := mem_centralizer_iff.mp c.2 ((z : L) : G) (z : L).2
    change ((z : L) : G) = (c : G) * ((z : L) : G) * (c : G)⁻¹
    rw [← hc, mul_inv_cancel_right]
  have hp : IsPGroup 2 ι.range := h2.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  have hle : ι.range ≤ (S : Subgroup _) := hp.le_sylow_of_normal S
  let ι' : center L →* (S : Subgroup (centralizer (L : Set G))) :=
    ι.codRestrict _ fun z => hle ⟨z, rfl⟩
  exact isCyclic_of_injective ι' fun a b h => hι (congrArg Subtype.val h)

open CFSG.Open CFSG.Blueprint.Recognition.Exact in
theorem even_exceptional_two_multiplier_cases [Finite G] {L : Subgroup G}
    (hL : standardComponentIsStandard L)
    (S : Sylow 2 (centralizer (L : Set G)))
    (hS : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (hexc : ¬ EvenStandardException (L ⧸ center L))
    (hlie : EvenLieType (L ⧸ center L))
    (h2 : IsPGroup 2 (center L)) (hne : center L ≠ ⊥) :
    (Nat.card (center L) = 2 ∧ (LieModel (L ⧸ center L) .G2 0 2 2 ∨
        LieModel (L ⧸ center L) .F4 0 2 1 ∨ LieModel (L ⧸ center L) .twistedE6 0 2 1)) ∨
      (LieModel (L ⧸ center L) .PSp 3 2 1 ∨ LieModel (L ⧸ center L) .PSU 6 2 1 ∨
        LieModel (L ⧸ center L) .POmegaPlus 4 2 1) ∨
      (Nat.card (center L) = 2 ∧ LieModel (L ⧸ center L) .twistedB2 0 2 3) := by
  obtain ⟨t, n, f, hadm, hmod⟩ := hlie
  have : Group.IsPerfect L := Group.isPerfect_def.2 hL.1.1
  have hq : Function.Surjective (QuotientGroup.mk' (center L)) := QuotientGroup.mk'_surjective _
  have hqk : (QuotientGroup.mk' (center L)).ker ≤ center L := by rw [QuotientGroup.ker_mk']
  obtain ⟨-, ⟨e⟩⟩ :=
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models (L ⧸ center L) t n 2 f hmod
  let Φ : generic t n 2 f × exceptional t n 2 f →* center L :=
    (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (center L))).toMonoidHom.comp
      ((CFSG.RankThree.PerfectCover.hopfMultiplierToKer _ hq hqk).comp
        ((CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toMonoidHom.comp
          e.symm.toMonoidHom))
  have hΦ : Function.Surjective Φ :=
    (MulEquiv.surjective (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' (center L)))).comp
      ((CFSG.RankThree.PerfectCover.hopfMultiplierToKer_surjective _ hq hqk).comp
        ((MulEquiv.surjective (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _)).comp
          (MulEquiv.surjective e.symm)))
  have hodd : Odd (Nat.card (generic t n 2 f)) := by
    obtain ⟨h1, h2⟩ := genericOrders_odd t n f hadm
    rw [card_generic]
    exact h1.mul h2
  have hψ := surjective_comp_inr_of_odd hodd h2 Φ hΦ
  have := isCyclic_center S hS h2
  have hcard1 : Nat.card (center L) ≠ 1 := fun h => hne (Subgroup.card_eq_one.1 h)
  have htwo : (∀ b : exceptional t n 2 f, b ^ 2 = 1) → Nat.card (center L) = 2 := fun hb => by
    have hle : Nat.card (center L) ≤ 2 := card_le_two_of_sq_eq_one fun k => by
      obtain ⟨b, rfl⟩ := hψ k
      rw [← map_pow, hb, map_one]
    have hpos : 0 < Nat.card (center L) := Nat.card_pos
    omega
  rcases exceptionalOrders_two_cases t n f with h11 | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    exfalso
    have hc : Nat.card (exceptional t n 2 f) = 1 := by rw [card_exceptional, h11]; rfl
    have : Subsingleton (exceptional t n 2 f) := (Nat.card_eq_one_iff_unique.1 hc).1
    apply hcard1
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
    obtain ⟨a', rfl⟩ := hψ a
    obtain ⟨b', rfl⟩ := hψ b
    rw [Subsingleton.elim a' b']
  · exact absurd (Or.inl hmod) hexc
  · exact absurd (Or.inr (Or.inl hmod)) hexc
  · exact absurd (Or.inr (Or.inr (Or.inl hmod))) hexc
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmod)))))) hexc
  · exact Or.inr (Or.inl (Or.inl hmod))
  · exact Or.inl ⟨htwo sq_eq_one_two_one, Or.inl hmod⟩
  · exact Or.inl ⟨htwo sq_eq_one_two_one, Or.inr (Or.inl hmod)⟩
  · exact Or.inr (Or.inl (Or.inr (Or.inr hmod)))
  · exact Or.inr (Or.inl (Or.inr (Or.inl hmod)))
  · exact Or.inr (Or.inr ⟨htwo sq_eq_one_two_two, hmod⟩)
  · exact Or.inl ⟨htwo sq_eq_one_two_two, Or.inr (Or.inr hmod)⟩
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmod))))))) hexc

end CFSG.LocalAnalysis.ComponentInitial.EvenTwoMultiplier
