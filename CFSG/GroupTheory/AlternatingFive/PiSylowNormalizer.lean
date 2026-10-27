module

public import CFSG.GroupTheory.AlternatingFive.SylowTwo
import TauCeti.GroupTheory.PGroup
import CFSG.RankThree.PartOne.S10.TransitiveSemisimpleOddKernel
import CFSG.Assembly.InCatalog

public section

namespace CFSG.GroupTheory.AlternatingFive

open scoped Pointwise

noncomputable section

private abbrev A5 : Type := alternatingGroup (Fin 5)

variable {ι : Type} [Finite ι]

private def coordSylow (S : Sylow 2 (ι → A5)) (i : ι) : Sylow 2 A5 :=
  S.mapSurjective (f := Pi.evalMonoidHom (fun _ : ι => A5) i)
    (by simpa only [Pi.coe_evalMonoidHom] using (Function.surjective_eval i))

private lemma coe_coordSylow (S : Sylow 2 (ι → A5)) (i : ι) :
    (coordSylow S i : Subgroup A5) =
      (S : Subgroup (ι → A5)).map (Pi.evalMonoidHom (fun _ : ι => A5) i) := by
  rw [coordSylow, Sylow.coe_mapSurjective]

private def piSylow (S : Sylow 2 (ι → A5)) : Subgroup (ι → A5) :=
  Subgroup.pi Set.univ (fun i => (coordSylow S i : Subgroup A5))

private lemma le_piSylow (S : Sylow 2 (ι → A5)) :
    (S : Subgroup (ι → A5)) ≤ piSylow S := by
  intro x hx
  rw [piSylow, Subgroup.mem_pi]
  intro i _
  have hxi : x i ∈ (S : Subgroup (ι → A5)).map (Pi.evalMonoidHom (fun _ : ι => A5) i) :=
    ⟨x, hx, rfl⟩
  simpa only [coe_coordSylow] using hxi

private def piSylowToProd (S : Sylow 2 (ι → A5)) :
    piSylow S →* (∀ i, (coordSylow S i : Subgroup A5)) where
  toFun x i := ⟨x.1 i, (Subgroup.mem_pi Set.univ).mp x.2 i (Set.mem_univ i)⟩
  map_one' := by
    ext i
    rfl
  map_mul' := by
    intro x y
    ext i
    rfl

private lemma injective_piSylowToProd (S : Sylow 2 (ι → A5)) :
    Function.Injective (piSylowToProd S) := by
  intro x y h
  apply Subtype.ext
  funext i
  simpa only [piSylowToProd, MonoidHom.coe_mk, OneHom.coe_mk] using
    congrArg (fun f => (f i : A5)) h

private lemma isPGroup_piSylow (S : Sylow 2 (ι → A5)) : IsPGroup 2 (piSylow S) :=
  (IsPGroup.pi (fun i => (coordSylow S i).isPGroup')).of_injective
    (piSylowToProd S) (injective_piSylowToProd S)

private lemma piSylow_eq (S : Sylow 2 (ι → A5)) :
    piSylow S = (S : Subgroup (ι → A5)) :=
  S.is_maximal' (isPGroup_piSylow S) (le_piSylow S)

private lemma nat_card_coordSylow (S : Sylow 2 (ι → A5)) (i : ι) :
    Nat.card (coordSylow S i) = 4 :=
  card_sylow_two_eq (coordSylow S i)

private lemma nat_card_S (S : Sylow 2 (ι → A5)) :
    Nat.card S = 4 ^ Nat.card ι := by
  rw [← piSylow_eq S, piSylow,
    @CFSG.RankThree.PartOne.TransitiveSemisimple.natCard_pi_univ_subgroup ι
      (Fintype.ofFinite ι)]
  simp only [nat_card_coordSylow, Finset.prod_const, Finset.card_univ]
  rw [← @Nat.card_eq_fintype_card ι (Fintype.ofFinite ι)]

private lemma normalizer_pi_eq {η : Type} {G : η → Type} [∀ i, Group (G i)]
    (H : ∀ i, Subgroup (G i)) :
    Subgroup.normalizer (Subgroup.pi Set.univ H : Set (∀ i, G i)) =
      Subgroup.pi Set.univ (fun i => Subgroup.normalizer (H i : Set (G i))) := by
  classical
  ext x
  rw [Subgroup.mem_pi]
  constructor
  · intro hx i _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hsingle : Pi.mulSingle i y ∈ Subgroup.pi Set.univ H := by
        rw [Subgroup.mulSingle_mem_pi]
        exact fun _ => hy
      have hmem : x * Pi.mulSingle i y * x⁻¹ ∈ Subgroup.pi Set.univ H :=
        (Subgroup.mem_normalizer_iff.mp hx _).mp hsingle
      have := (Subgroup.mem_pi Set.univ).mp hmem i (Set.mem_univ i)
      simpa using this
    · intro hy
      have hxinv : x⁻¹ ∈ Subgroup.normalizer
          (Subgroup.pi Set.univ H : Set (∀ i, G i)) :=
        (Subgroup.normalizer (Subgroup.pi Set.univ H : Set (∀ i, G i))).inv_mem hx
      have hsingle : Pi.mulSingle i (x i * y * (x i)⁻¹) ∈ Subgroup.pi Set.univ H := by
        rw [Subgroup.mulSingle_mem_pi]
        exact fun _ => hy
      have hmem : x⁻¹ * Pi.mulSingle i (x i * y * (x i)⁻¹) * x ∈
          Subgroup.pi Set.univ H := by
        simpa using (Subgroup.mem_normalizer_iff.mp hxinv _).mp hsingle
      have hz : x⁻¹ i * (x i * y * (x i)⁻¹) * x i ∈ H i := by
        have := (Subgroup.mem_pi Set.univ).mp hmem i (Set.mem_univ i)
        simpa using this
      have hz' : (x i)⁻¹ * (x i * y * (x i)⁻¹) * x i ∈ H i := by
        simpa only [Pi.inv_apply] using hz
      have hy_eq : y = (x i)⁻¹ * (x i * y * (x i)⁻¹) * x i := by group
      rw [hy_eq]
      exact hz'
  · intro hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_pi] at hy ⊢
      intro i _
      exact (Subgroup.mem_normalizer_iff.mp (hx i (Set.mem_univ i)) (y i)).mp
        (hy i (Set.mem_univ i))
    · intro hy
      rw [Subgroup.mem_pi] at hy ⊢
      intro i _
      exact (Subgroup.mem_normalizer_iff.mp (hx i (Set.mem_univ i)) (y i)).mpr
        (hy i (Set.mem_univ i))

private lemma normalizer_piSylow (S : Sylow 2 (ι → A5)) :
    Subgroup.normalizer (piSylow S : Set (ι → A5)) =
      Subgroup.pi Set.univ (fun i =>
        Subgroup.normalizer ((coordSylow S i : Subgroup A5) : Set A5)) := by
  rw [piSylow, normalizer_pi_eq]

private lemma nat_card_normalizer_piSylow (S : Sylow 2 (ι → A5)) :
    Nat.card (Subgroup.normalizer (piSylow S : Set (ι → A5))) =
      12 ^ Nat.card ι := by
  rw [normalizer_piSylow,
    @CFSG.RankThree.PartOne.TransitiveSemisimple.natCard_pi_univ_subgroup ι
      (Fintype.ofFinite ι)]
  have hfac : ∀ i, Nat.card (Subgroup.normalizer
      ((coordSylow S i : Subgroup A5) : Set A5)) = 12 := by
    intro i
    simpa using card_normalizer_sylow_two (coordSylow S i)
  simp only [hfac, Finset.prod_const, Finset.card_univ]
  rw [← @Nat.card_eq_fintype_card ι (Fintype.ofFinite ι)]

private lemma pow_three_eq_one_of_pow_three_pow_eq_one {x : A5} {n : ℕ}
    (hx : x ^ 3 ^ n = 1) : x ^ 3 = 1 := by
  have hdiv : orderOf x ∣ 3 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hx
  have hdiv60 : orderOf x ∣ 60 := by
    have h := orderOf_dvd_natCard x
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    exact h
  obtain ⟨k, -, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv
  rw [hk_eq] at hdiv60
  have hk : k ≤ 1 := by
    by_contra h
    have hk2 : 2 ≤ k := by omega
    have h9 : 9 ∣ 60 := (pow_dvd_pow 3 hk2).trans hdiv60
    norm_num at h9
  have h3 : 3 ^ k ∣ 3 := by
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp
  rw [← hk_eq] at h3
  exact orderOf_dvd_iff_pow_eq_one.mp h3

omit [Finite ι] in
private lemma normalizer_pow_three (S : Sylow 2 (ι → A5)) :
    ∀ x ∈ Subgroup.normalizer (S : Set (ι → A5)),
      ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1 := by
  intro x _ n hn
  funext i
  have hpow : (x i) ^ 3 ^ n = 1 := by
    have := congrArg (fun f : ι → A5 => f i) hn
    simpa using this
  exact pow_three_eq_one_of_pow_three_pow_eq_one hpow

theorem sylow_two_pi_normalizer_facts
    {ι : Type} [Finite ι]
    (S : Sylow 2 (ι → alternatingGroup (Fin 5))) :
    Nat.card S = 4 ^ Nat.card ι ∧
    Nat.card (Subgroup.normalizer
      (S : Set (ι → alternatingGroup (Fin 5)))) = 12 ^ Nat.card ι ∧
    ∀ x ∈ Subgroup.normalizer
      (S : Set (ι → alternatingGroup (Fin 5))),
      ∀ n : ℕ, x ^ 3 ^ n = 1 → x ^ 3 = 1 := by
  refine ⟨nat_card_S S, ?_, normalizer_pow_three S⟩
  rw [show (S : Set (ι → A5)) = (piSylow S : Set (ι → A5)) from by rw [piSylow_eq S]; rfl]
  exact nat_card_normalizer_piSylow S

end

end CFSG.GroupTheory.AlternatingFive
