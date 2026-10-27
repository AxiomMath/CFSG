module

public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81E6PXT

public section

namespace CFSG.ComponentClassification.GSThmB

namespace P211Y

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer P211 P211X

variable {X : Type} [Group X]

theorem outer_solvable_of_equiv {G P : Type*} [Group G] [Group P] (e : G ≃* P)
    (h : Group.IsSolvable (OuterAutomorphisms.Outer P)) :
    Group.IsSolvable (OuterAutomorphisms.Outer G) :=
  (LocalAnalysis.ComponentInitial.outer_isomorphism e).2.2 h

theorem le_fstar_of_solvable (hC : centralizer (generalizedFitting X : Set X) = ⊥)
    (hsolv : Group.IsSolvable (OuterAutomorphisms.Outer ↥(generalizedFitting X)))
    {b : X} {K : Subgroup X} (hKC : K ≤ centralizer ({b} : Set X))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set X)))) :
    K ≤ generalizedFitting X := by
  obtain ⟨N, hN⟩ := exists_derivedSeries_le_of_isSolvable (OuterAutomorphisms.inner _) hsolv
  exact le_fstar_of_perfect hC (MulEquiv.refl _) hN (commutator_eq_of_isPComp hKC hK)

theorem conjNormal_eq_self_iff (N : Subgroup X) [N.Normal] (b : X) (y : N) :
    MulAut.conjNormal b y = y ↔ (y : X) ∈ centralizer ({b} : Set X) := by
  rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, MulAut.conjNormal_apply,
    mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem card_fixed_conjNormal (N : Subgroup X) [N.Normal] (b : X) :
    Nat.card {y : N // MulAut.conjNormal b y = y} =
      Nat.card ↥(N ⊓ centralizer ({b} : Set X)) :=
  Nat.card_congr
    { toFun := fun y => ⟨y.1, mem_inf.mpr ⟨y.1.2, (conjNormal_eq_self_iff N b y.1).1 y.2⟩⟩
      invFun := fun z => ⟨⟨z, (mem_inf.mp z.2).1⟩,
        (conjNormal_eq_self_iff N b _).2 (mem_inf.mp z.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_fixed_congr {S T : Type*} [Group S] [Group T] (e : S ≃* T) (α : MulAut S) :
    Nat.card {x : T // MulAut.congr e α x = x} = Nat.card {y : S // α y = y} := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)).symm
  have h : MulAut.congr e α (e y) = e (α y) := by
    rw [MulAut.congr_apply]
    simp
  change α y = y ↔ MulAut.congr e α (e y) = e y
  rw [h, e.injective.eq_iff]

theorem p211_of_fixed_lt [Finite X] (hC : centralizer (generalizedFitting X : Set X) = ⊥)
    (hsolv : Group.IsSolvable (OuterAutomorphisms.Outer ↥(generalizedFitting X)))
    (hfix : ∀ α : MulAut ↥(generalizedFitting X), α * α = 1 → α ≠ 1 →
      Nat.card {y : ↥(generalizedFitting X) // α y = y} < 20160)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {b : X} {K : Subgroup X}
    (hb : b * b = 1) (hb1 : b ≠ 1) (hKC : K ≤ centralizer ({b} : Set X))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({b} : Set X))))
    (hKt : IsSec8Socle (K ⧸ pPrimeCore 2 K) p f) : False := by
  have : (generalizedFitting X).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := X)).2
  have hKF := le_fstar_of_solvable hC hsolv hKC hK
  have hα2 : MulAut.conjNormal b * MulAut.conjNormal b =
      (1 : MulAut ↥(generalizedFitting X)) := by
    rw [← map_mul, hb, map_one]
  have hα1 : (MulAut.conjNormal b : MulAut ↥(generalizedFitting X)) ≠ 1 := fun h =>
    hb1 (conjNormal_injective' _ hC (h.trans (map_one _).symm))
  have h1 := hfix _ hα2 hα1
  rw [card_fixed_conjNormal] at h1
  have h2 := le_card_of_socle hp hp2 hf hKt
  have h3 : Nat.card K ≤ Nat.card ↥(generalizedFitting X ⊓ centralizer ({b} : Set X)) :=
    card_le_of_le (le_inf hKF hKC)
  omega

theorem not_mem_of_center_socle [Finite X] {K : Subgroup X} {b : X} (hb : orderOf b = 2)
    (hKC : K ≤ centralizer ({b} : Set X)) (hKs : center (K ⧸ pPrimeCore 2 K) = ⊥) : b ∉ K := by
  intro hbK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : (⟨b, hbK⟩ : K) ∈ center K := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hKC y.2))
  have hZO : (⟨b, hbK⟩ : K) ∈ pPrimeCore 2 K := by
    have h1 : (QuotientGroup.mk' (pPrimeCore 2 K)) ⟨b, hbK⟩ ∈ center (K ⧸ pPrimeCore 2 K) :=
      map_center_le_center (QuotientGroup.mk'_surjective _) (mem_map_of_mem _ hZ)
    rw [hKs, mem_bot] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have h2 : 2 ∣ Nat.card (pPrimeCore 2 K) := by
    have h3 := orderOf_dvd_natCard (⟨⟨b, hbK⟩, hZO⟩ : pPrimeCore 2 K)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hb] at h3
  exact (Nat.coprime_two_left.mp pPrimeCore_coprime_card).not_two_dvd_nat h2

theorem sq_mem_of_card_le_two_mul {G : Type*} [Group G] [Finite G] {K C : Subgroup G}
    (hKC : K ≤ C) (hcard : Nat.card C ≤ 2 * Nat.card K) {g : G} (hg : g ∈ C) : g * g ∈ K := by
  have hK : Nat.card (K.subgroupOf C) = Nat.card K :=
    Nat.card_congr (subgroupOfEquivOfLe hKC).toEquiv
  have hidx := (K.subgroupOf C).card_mul_index
  rw [hK] at hidx
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hne := (K.subgroupOf C).index_ne_zero_of_finite
  have hle : (K.subgroupOf C).index ≤ 2 := by
    by_contra h
    have h3 : Nat.card K * 3 ≤ Nat.card K * (K.subgroupOf C).index :=
      Nat.mul_le_mul_left _ (by omega)
    rw [hidx] at h3
    omega
  have hmem : (⟨g, hg⟩ : C) ^ 2 ∈ K.subgroupOf C := by
    rcases (by omega : (K.subgroupOf C).index = 1 ∨ (K.subgroupOf C).index = 2) with h1 | h2
    · rw [index_eq_one.mp h1]
      exact mem_top _
    · exact sq_mem_of_index_two h2 _
  rw [mem_subgroupOf, pow_two] at hmem
  exact hmem

open CFSG.Sporadic.SmallOddCore in
theorem card_fixed_lt_of_autModel {M : Type*} [Group M] {P R : Subgroup M} (h : AutModel P R)
    {N : ℕ} (hrows : ∀ τ ∈ R, orderOf τ = 2 → Nat.card ↥(P ⊓ centralizer ({τ} : Set M)) < N)
    (β : MulAut P) (hβ2 : β * β = 1) (hβ1 : β ≠ 1) : Nat.card {p : P // β p = p} < N := by
  have hxR : h.elt β ∈ R := h.elt_mem β
  have hspec : ∀ p : P, ((β p : P) : M) = h.elt β * p * (h.elt β)⁻¹ := h.elt_spec β
  have hxx : h.elt β * h.elt β = 1 := by
    refine h.inj _ (R.mul_mem hxR hxR) fun p hp => ?_
    have h1 := congrArg Subtype.val (congrArg (fun γ : MulAut P => γ ⟨p, hp⟩) hβ2)
    simp only [MulAut.mul_apply, MulAut.one_apply] at h1
    rw [hspec, hspec] at h1
    calc h.elt β * h.elt β * p =
        h.elt β * (h.elt β * p * (h.elt β)⁻¹) * (h.elt β)⁻¹ * (h.elt β * h.elt β) := by group
      _ = p * (h.elt β * h.elt β) := by rw [h1]
  have hx1 : h.elt β ≠ 1 := fun h1 =>
    hβ1 (MulEquiv.ext fun p => Subtype.ext (by rw [hspec, h1]; simp))
  have hxo : orderOf (h.elt β) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  have hiff : ∀ p : P, β p = p ↔ (p : M) ∈ centralizer ({h.elt β} : Set M) := by
    intro p
    rw [mem_centralizer_singleton_iff, ← Subtype.coe_inj, hspec, mul_inv_eq_iff_eq_mul]
    exact eq_comm
  have hcard : Nat.card {p : P // β p = p} =
      Nat.card ↥(P ⊓ centralizer ({h.elt β} : Set M)) :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1, mem_inf.mpr ⟨p.1.2, (hiff p.1).1 p.2⟩⟩
        invFun := fun z => ⟨⟨z, (mem_inf.mp z.2).1⟩, (hiff _).2 (mem_inf.mp z.2).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hcard]
  exact hrows _ hxR hxo

end P211Y

end CFSG.ComponentClassification.GSThmB
