module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open scoped commutatorElement

section CommutingFamily

variable {G : Type*} [Group G] {ι : Type*}

theorem perfect_le_iSup_commutator (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, Commute x y) {P : Subgroup G} (hP : ⁅P, P⁆ = P)
    (hPA : P ≤ ⨆ i, A i) : P ≤ ⨆ i, ⁅A i, A i⁆ := by
  have h : ⁅P, P⁆ ≤ ⁅(⨆ i, A i), (⨆ i, A i)⁆ := Subgroup.commutator_mono hPA hPA
  rw [CFSG.RankThree.PartOne.KCUnitary.commutator_iSup_commuting A hc, hP] at h
  exact h

theorem mem_centralizer_of_noncommPiCoprod_eq_one [Fintype ι] [DecidableEq ι]
    (A : ι → Subgroup G)
    (hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ A i → y ∈ A j → Commute x y)
    (s : ∀ i, A i) (h1 : Subgroup.noncommPiCoprod hcomm s = 1) (i : ι) :
    ((s i : A i) : G) ∈ Subgroup.centralizer (A i : Set G) := by
  set P := (Finset.univ.erase i).noncommProd (fun j => ((s j : A j) : G))
    (fun j _ k _ h => hcomm h _ _ (s j).2 (s k).2)
  have h2 : ((s i : A i) : G) * P = Subgroup.noncommPiCoprod hcomm s := by
    rw [Subgroup.noncommPiCoprod_apply]
    exact Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i)
      (fun j => ((s j : A j) : G)) _
  rw [h1] at h2
  have hPC : P ∈ Subgroup.centralizer (A i : Set G) :=
    Subgroup.noncommProd_mem _ _ fun j hj => by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (hcomm (Finset.ne_of_mem_erase hj).symm g _ hg (s j).2).eq
  have hsi : ((s i : A i) : G) = P⁻¹ := eq_inv_of_mul_eq_one_left h2
  rw [hsi]
  exact inv_mem hPC

private theorem commutator_mul_left_of_commute {z u b : G} (hzu : Commute z u)
    (hzb : Commute z b) : ⁅z * u, b⁆ = ⁅u, b⁆ := by
  have h : z * (u * b * u⁻¹) = (u * b * u⁻¹) * z :=
    ((hzu.mul_right hzb).mul_right hzu.inv_right).eq
  calc ⁅z * u, b⁆ = (z * (u * b * u⁻¹)) * z⁻¹ * b⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = ((u * b * u⁻¹) * z) * z⁻¹ * b⁻¹ := by rw [h]
    _ = ⁅u, b⁆ := by simp only [commutatorElement_def]; group

private theorem commutator_mul_mul_of_commute {z w u v : G} (hzu : Commute z u)
    (hzv : Commute z v) (hzw : Commute z w) (hwu : Commute w u) (hwv : Commute w v) :
    ⁅z * u, w * v⁆ = ⁅u, v⁆ := by
  rw [commutator_mul_left_of_commute hzu (hzw.mul_right hzv), ← commutatorElement_inv,
    commutator_mul_left_of_commute hwv hwu, commutatorElement_inv]

theorem commutator_mem_iSup_inf_fixed [Finite ι] (F : G →* G) (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, Commute x y) (hF : ∀ i, ∀ x ∈ A i, F x ∈ A i)
    {x y : G} (hx : x ∈ ⨆ i, A i) (hxF : F x = x) (hy : y ∈ ⨆ i, A i) (hyF : F y = y) :
    ⁅x, y⁆ ∈ ⨆ i, A i ⊓ F.eqLocus (MonoidHom.id G) := by
  classical
  cases nonempty_fintype ι
  have hcomm : Pairwise fun i j : ι => ∀ x y : G, x ∈ A i → y ∈ A j → Commute x y :=
    fun i j hij x y hx hy => hc i j hij x hx y hy
  set ν := Subgroup.noncommPiCoprod hcomm with hν
  have hrange : ν.range = ⨆ i, A i := Subgroup.noncommPiCoprod_range
  have key : ∀ f : ∀ i, A i, F (ν f) = ν f →
      ∀ i, F (f i) * ((f i : A i) : G)⁻¹ ∈ Subgroup.centralizer (A i : Set G) := by
    intro f hf i
    let Ff : ∀ i, A i := fun i => ⟨F (f i), hF i _ (f i).2⟩
    have hFν : ν Ff = F (ν f) := by
      rw [hν, Subgroup.noncommPiCoprod_apply, Subgroup.noncommPiCoprod_apply]
      exact (Finset.map_noncommProd Finset.univ (fun i => ((f i : A i) : G)) _ F).symm
    have h1 : ν (Ff * f⁻¹) = 1 := by rw [map_mul, map_inv, hFν, hf, mul_inv_cancel]
    exact mem_centralizer_of_noncommPiCoprod_eq_one A hcomm (Ff * f⁻¹) h1 i
  obtain ⟨f, rfl⟩ : x ∈ ν.range := hrange ▸ hx
  obtain ⟨g, rfl⟩ : y ∈ ν.range := hrange ▸ hy
  have hkf := key f hxF
  have hkg := key g hyF
  rw [← map_commutatorElement ν f g, hν, Subgroup.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
  refine Subgroup.mem_iSup_of_mem i ⟨(⁅f, g⁆ i).2, ?_⟩
  have hz := hkf i
  have hw := hkg i
  set u : G := ((f i : A i) : G)
  set v : G := ((g i : A i) : G)
  have hAu : u ∈ A i := (f i).2
  have hAv : v ∈ A i := (g i).2
  have hzA : F u * u⁻¹ ∈ A i := mul_mem (hF i u hAu) (inv_mem hAu)
  have hwA : F v * v⁻¹ ∈ A i := mul_mem (hF i v hAv) (inv_mem hAv)
  have hcz : ∀ h ∈ A i, Commute (F u * u⁻¹) h := fun h hh =>
    (Subgroup.mem_centralizer_iff.1 hz h hh).symm
  have hcw : ∀ h ∈ A i, Commute (F v * v⁻¹) h := fun h hh =>
    (Subgroup.mem_centralizer_iff.1 hw h hh).symm
  have hFu : F u = (F u * u⁻¹) * u := (inv_mul_cancel_right _ _).symm
  have hFv : F v = (F v * v⁻¹) * v := (inv_mul_cancel_right _ _).symm
  show F ⁅u, v⁆ = ⁅u, v⁆
  rw [map_commutatorElement, hFu, hFv]
  exact commutator_mul_mul_of_commute (hcz u hAu) (hcz v hAv) (hcz _ hwA) (hcw u hAu)
    (hcw v hAv)

theorem perfect_le_iSup_inf_fixed [Finite ι] (F : G →* G) (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, Commute x y) (hF : ∀ i, ∀ x ∈ A i, F x ∈ A i)
    {P : Subgroup G} (hP : ⁅P, P⁆ = P) (hPA : P ≤ ⨆ i, A i) (hPF : ∀ x ∈ P, F x = x) :
    P ≤ ⨆ i, A i ⊓ F.eqLocus (MonoidHom.id G) := by
  have h : ⁅P, P⁆ ≤ ⨆ i, A i ⊓ F.eqLocus (MonoidHom.id G) :=
    Subgroup.commutator_le.2 fun x hx y hy =>
      commutator_mem_iSup_inf_fixed F A hc hF (hPA hx) (hPF x hx) (hPA hy) (hPF y hy)
  rwa [hP] at h

theorem isSolvable_sup_quotient_of_comm {H N : Subgroup G} [(N.subgroupOf (H ⊔ N)).Normal]
    (hH : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hLE : H ≤ Subgroup.normalizer (N : Set G)) :
    Group.IsSolvable (↥(H ⊔ N) ⧸ N.subgroupOf (H ⊔ N)) := by
  haveI : (N.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLE
  haveI : Group.IsSolvable ↥H := Group.isSolvable_of_comm fun x y => Subtype.ext (hH x x.2 y y.2)
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hLE
  exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

private def dsub (H : Subgroup G) : ℕ → Subgroup G
  | 0 => H
  | n + 1 => ⁅dsub H n, dsub H n⁆

private theorem dsub_mono {H K : Subgroup G} (h : H ≤ K) (n : ℕ) : dsub H n ≤ dsub K n := by
  induction n with
  | zero => exact h
  | succ n ih => exact Subgroup.commutator_mono ih ih

private theorem dsub_eq_of_perfect {P : Subgroup G} (hP : ⁅P, P⁆ = P) (n : ℕ) : dsub P n = P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [dsub, ih, hP]

private theorem dsub_anti (H : Subgroup G) : Antitone (dsub H) :=
  antitone_nat_of_succ_le fun n => Subgroup.commutator_le_self (dsub H n)

private theorem map_subtype_derivedSeries (H : Subgroup G) (n : ℕ) :
    (derivedSeries ↥H n).map H.subtype = dsub H n := by
  induction n with
  | zero => rw [derivedSeries_zero, dsub, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  | succ n ih => rw [derivedSeries_succ, dsub, Subgroup.map_commutator, ih]

private theorem dsub_iSup (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, Commute a b) (n : ℕ) :
    dsub (⨆ i, A i) n = ⨆ i, dsub (A i) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [dsub, ih]
    exact CFSG.RankThree.PartOne.KCUnitary.commutator_iSup_commuting (fun i => dsub (A i) n)
      (fun i j hij a ha b hb => hc i j hij a (dsub_anti (A i) (Nat.zero_le n) ha) b
        (dsub_anti (A j) (Nat.zero_le n) hb))

theorem perfect_le_iSup_of_solvable [Finite ι] (A : ι → Subgroup G)
    (hc : ∀ i j, i ≠ j → ∀ x ∈ A i, ∀ y ∈ A j, Commute x y) (Q : ι → Prop)
    (hQ : ∀ i, Q i → ⁅A i, A i⁆ = A i) (hs : ∀ i, ¬ Q i → Group.IsSolvable ↥(A i))
    {P : Subgroup G} (hP : ⁅P, P⁆ = P) (hPA : P ≤ ⨆ i, A i) :
    P ≤ ⨆ i, ⨆ (_ : Q i), A i := by
  classical
  have hk : ∀ i, ∃ k : ℕ, ¬ Q i → dsub (A i) k = ⊥ := by
    intro i
    by_cases hi : Q i
    · exact ⟨0, fun h => absurd hi h⟩
    · obtain ⟨k, hk⟩ := (hs i hi).solvable
      refine ⟨k, fun _ => ?_⟩
      rw [← map_subtype_derivedSeries, hk, Subgroup.map_bot]
  choose k hk using hk
  cases nonempty_fintype ι
  have h1 : P ≤ dsub (⨆ i, A i) (Finset.univ.sup k) := by
    rw [← dsub_eq_of_perfect hP (Finset.univ.sup k)]
    exact dsub_mono hPA _
  rw [dsub_iSup A hc] at h1
  refine h1.trans (iSup_le fun i => ?_)
  by_cases hi : Q i
  · rw [dsub_eq_of_perfect (hQ i hi)]
    exact (le_iSup (fun _ : Q i => A i) hi).trans (le_iSup (fun i => ⨆ (_ : Q i), A i) i)
  · exact ((dsub_anti (A i) (Finset.le_sup (Finset.mem_univ i))).trans (hk i hi).le).trans bot_le

end CommutingFamily

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
