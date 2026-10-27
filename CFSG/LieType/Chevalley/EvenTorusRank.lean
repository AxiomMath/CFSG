module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.LieType.Chevalley.EvenTorusRank

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K]

section Torus


theorem mul_comm_of_mem_subsystemTorus {A : Set (Fin τ.rank)} {a b : ModGL τ K}
    (ha : a ∈ subsystemTorus τ K A) (hb : b ∈ subsystemTorus τ K A) : a * b = b * a := by
  have hc : IsMulCommutative (subsystemTorus τ K A) := by
    refine Subgroup.isMulCommutative_closure ?_
    rintro _ ⟨i, -, s, rfl⟩ _ ⟨j, -, t, rfl⟩ -
    exact torusElt_mul_comm i j s t
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : subsystemTorus τ K A) ⟨b, hb⟩)

end Torus

section Certified


theorem torusEltHom_injective [CharP K 2] (i : Fin τ.rank) :
    Function.Injective (torusEltHom (τ := τ) (K := K) i) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  have h : (t : K) ^ 2 = 1 := sq_eq_one_of_torusElt_eq_one i ht
  exact Units.ext (CharTwo.sq_injective (by simpa using h))

theorem two_le_pRank_of_dvd_card_units [Finite K] [CharP K 2] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hdvd : ℓ ∣ Nat.card Kˣ) {i j : Fin τ.rank} (hij : i ≠ j)
    (hdet : ¬ (ℓ : ℤ) ∣ 4 - τ.cartan i j * τ.cartan j i) :
    2 ≤ CFSG.Open.pRank ℓ (⊤ : Subgroup ↥(adjointGroup τ K)) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : Finite ↥(adjointGroup τ K) := Subtype.finite
  have hinj : ∀ k : Fin τ.rank, Function.Injective (xUnit τ K k) :=
    fun k _ _ h => xOp_injective k (congrArg Units.val h)
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  let φ : Fin τ.rank → Kˣ →* ↥(adjointGroup τ K) := fun k =>
    (torusEltHom τ K k).codRestrict (adjointGroup τ K) (fun t => torusElt_mem_adjointGroup k t)
  have hφ : ∀ k, Function.Injective (φ k) := fun k a b h =>
    torusEltHom_injective k (congrArg Subtype.val h)
  have hφord : ∀ k, orderOf (φ k ζ) = ℓ := fun k => (orderOf_injective (φ k) (hφ k) ζ).trans hζ
  refine CFSG.GroupTheory.two_le_pRank_of_commute (x := φ i ζ) (y := φ j ζ)
    (Subgroup.mem_top _) (Subgroup.mem_top _) (hφord i) (hφord j)
    (Subtype.ext (torusElt_mul_comm i j ζ ζ)) ?_
  intro hy
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h : torusElt τ K i (ζ ^ a) = torusElt τ K j ζ := by
    have h1 : φ i (ζ ^ a) = φ j ζ := by rw [map_zpow]; exact ha
    exact congrArg Subtype.val h1
  have e1 : (ζ ^ a) ^ τ.cartan i i = ζ ^ τ.cartan j i := by
    have c1 := (simple_torus_root_conjugation τ K j i ζ 1).1
    have c2 := (simple_torus_root_conjugation τ K i i (ζ ^ a) 1).1
    rw [← h] at c1
    exact Units.ext (by simpa only [mul_one] using hinj i (c2.symm.trans c1))
  have e2 : (ζ ^ a) ^ τ.cartan i j = ζ ^ τ.cartan j j := by
    have c1 := (simple_torus_root_conjugation τ K j j ζ 1).1
    have c2 := (simple_torus_root_conjugation τ K i j (ζ ^ a) 1).1
    rw [← h] at c1
    exact Units.ext (by simpa only [mul_one] using hinj j (c2.symm.trans c1))
  rw [Tag.cartan_self, ← zpow_mul] at e1
  rw [Tag.cartan_self, ← zpow_mul] at e2
  have d1 : (ℓ : ℤ) ∣ τ.cartan j i - a * 2 := by
    have := (orderOf_dvd_sub_iff_zpow_eq_zpow (x := ζ)).2 e1.symm
    rwa [hζ] at this
  have d2 : (ℓ : ℤ) ∣ a * τ.cartan i j - 2 := by
    have := (orderOf_dvd_sub_iff_zpow_eq_zpow (x := ζ)).2 e2
    rwa [hζ] at this
  refine hdet ?_
  have : 4 - τ.cartan i j * τ.cartan j i =
      -(τ.cartan i j * (τ.cartan j i - a * 2) + 2 * (a * τ.cartan i j - 2)) := by ring
  rw [this]
  exact (dvd_neg.2 (dvd_add (d1.mul_left _) (d2.mul_left _)))

theorem pow_card_units_eq_one_of_mem_subsystemTorus [Finite K] {A : Set (Fin τ.rank)}
    {x : ModGL τ K} (hx : x ∈ subsystemTorus τ K A) : x ^ Nat.card Kˣ = 1 := by
  refine Subgroup.closure_induction (p := fun y _ => y ^ Nat.card Kˣ = 1) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, -, t, rfl⟩
    have h1 : t ^ Nat.card Kˣ = 1 := pow_card_eq_one'
    calc torusElt τ K i t ^ Nat.card Kˣ = torusEltHom τ K i (t ^ Nat.card Kˣ) :=
          (map_pow (torusEltHom τ K i) t _).symm
      _ = 1 := by rw [h1, map_one]
  · exact one_pow _
  · intro y z hy hz ihy ihz
    rw [(show Commute y z from mul_comm_of_mem_subsystemTorus hy hz).mul_pow, ihy, ihz, one_mul]
  · intro y _ ih
    rw [inv_pow, ih, inv_one]

end Certified

end CFSG.LieType.Chevalley.EvenTorusRank
