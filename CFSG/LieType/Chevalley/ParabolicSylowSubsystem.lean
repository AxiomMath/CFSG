module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.Open.RankThreeDefs
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LieType.Chevalley.ParSylow

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

variable {τ : Tag} {K : Type} [Field K]

section GroupTheory

variable {G : Type*} [Group G]

theorem relIndex_sup_of_le_normalizer {H N : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hH
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hH
  exact Nat.card_congr
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N hH).toEquiv.symm

theorem le_of_isPGroup_two_of_not_dvd_relIndex [Finite G] {N P U : Subgroup G}
    (hNP : N ≤ P) (hP : P ≤ Subgroup.normalizer (N : Set G)) (hU : U ≤ P)
    (hUp : IsPGroup 2 U) (hodd : ¬ 2 ∣ N.relIndex P) : U ≤ N := by
  have h1 : N.relIndex (U ⊔ N) = N.relIndex U := relIndex_sup_of_le_normalizer (hU.trans hP)
  have h2 : N.relIndex (U ⊔ N) ∣ N.relIndex P := by
    rw [← Subgroup.relIndex_mul_relIndex N (U ⊔ N) P le_sup_right (sup_le hU hNP)]
    exact dvd_mul_right _ _
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hUp
  have h3 : N.relIndex U ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card N U
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
  refine Subgroup.relIndex_eq_one.1 ?_
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · simpa using hi
  · exfalso
    refine hodd ((dvd_pow_self 2 hipos.ne').trans (hi ▸ h1 ▸ h2))

theorem not_dvd_card_sup_of_isPGroup_two [Finite G] {R L : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hR : IsPGroup 2 R) (hL : L ≤ Subgroup.normalizer (R : Set G))
    (hpL : ¬ p ∣ Nat.card L) : ¬ p ∣ Nat.card ↥(R ⊔ L) := by
  have h1 : R.relIndex (L ⊔ R) = R.relIndex L := relIndex_sup_of_le_normalizer hL
  have h2 := Subgroup.relIndex_mul_card R (L ⊔ R)
  rw [inf_of_le_left le_sup_right, h1, sup_comm L R] at h2
  intro hdvd
  rw [← h2] at hdvd
  rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
  · exact hpL (h.trans (Subgroup.relIndex_dvd_card R L))
  · obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hR
    rw [hk] at h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

theorem not_two_dvd_card_units (F : Type*) [Field F] [Finite F] [CharP F 2] :
    ¬ 2 ∣ Nat.card Fˣ := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_units, Nat.card_eq_fintype_card, hn]
  have h1 : 2 ∣ 2 ^ (n : ℕ) := dvd_pow_self 2 n.pos.ne'
  have h2 : 0 < 2 ^ (n : ℕ) := by positivity
  omega

end GroupTheory

section Torus


theorem torusElt_mem_normalizer_subsystemGroup (A : Set (Fin τ.rank)) (i : Fin τ.rank)
    (t : Kˣ) :
    torusElt τ K i t ∈ Subgroup.normalizer (subsystemGroup τ K A : Set (ModGL τ K)) := by
  have h : (torusEltHom τ K i).range ≤
      Subgroup.normalizer (subsystemGroup τ K A : Set (ModGL τ K)) := by
    refine Subgroup.le_normalizer_closure_iff.2 ?_
    rintro _ ⟨s, rfl⟩ _ ⟨j, hj, c, rfl | rfl⟩
    · change torusElt τ K i s * xUnit τ K j c * (torusElt τ K i s)⁻¹ ∈ _
      rw [(simple_torus_root_conjugation τ K i j s c).1]
      exact xUnit_mem_subsystemGroup hj _
    · change torusElt τ K i s * yUnit τ K j c * (torusElt τ K i s)⁻¹ ∈ _
      rw [(simple_torus_root_conjugation τ K i j s c).2]
      exact yUnit_mem_subsystemGroup hj _
  exact h ⟨t, rfl⟩

theorem torusGroup_le_normalizer_subsystemGroup (A : Set (Fin τ.rank)) :
    torusGroup τ K ≤ Subgroup.normalizer (subsystemGroup τ K A : Set (ModGL τ K)) :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact torusElt_mem_normalizer_subsystemGroup A i t)

theorem torusGroup_pow_card_units {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    h ^ Nat.card Kˣ = 1 := by
  refine Subgroup.closure_induction (p := fun h _ => h ^ Nat.card Kˣ = 1) ?_ ?_ ?_ ?_ hh
  · rintro _ ⟨⟨i, t⟩, rfl⟩
    change torusEltHom τ K i t ^ Nat.card Kˣ = 1
    rw [← map_pow, pow_card_eq_one', map_one]
  · exact one_pow _
  · intro x y hx hy ihx ihy
    have hxy : Commute x y := mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hx)
      (torusGroup_le_diagonalGroup hy)
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  · intro x _ ihx
    rw [inv_pow, ihx, inv_one]

theorem not_two_dvd_card_torusGroup [Finite K] [CharP K 2] :
    ¬ 2 ∣ Nat.card (torusGroup τ K) := by
  intro h2
  haveI : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have h1 : orderOf (x : ModGL τ K) ∣ Nat.card Kˣ :=
    orderOf_dvd_of_pow_eq_one (torusGroup_pow_card_units x.2)
  rw [Subgroup.orderOf_coe, hx] at h1
  exact not_two_dvd_card_units K h1

end Torus

section Certified


theorem dvd_card_subsystemGroup_of_sylowHyp [Finite K] [CharP K 2] (J : Set (Fin τ.rank))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsyl : ∀ U : Subgroup (ModGL τ K),
      CFSG.ABGLocalTools.IsSylowOf 2 U (parabolicSubgroup τ K J) →
        ¬ U ≤ rankThreePrimeCore p (parabolicSubgroup τ K J)) :
    p ∣ Nat.card (subsystemGroup τ K J) := by
  haveI : Finite (Module.End K (RootModule τ K)) := Module.finite_of_finite K
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hpL
  have hRP : parabolicRadical τ K J ≤ parabolicSubgroup τ K J :=
    (parabolicRadical_le_posUnipotent J).trans (posUnipotent_le_parabolicSubgroup J)
  have hPR : parabolicSubgroup τ K J ≤
      Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) :=
    parabolicSubgroup_le_normalizer_parabolicRadical J
  have hLP : subsystemGroup τ K J ≤ parabolicSubgroup τ K J :=
    (le_sup_right : subsystemGroup τ K J ≤ parabolicLevi τ K J).trans
      (parabolicLevi_le_parabolicSubgroup J)
  have hPsup : parabolicSubgroup τ K J = torusGroup τ K ⊔
      (parabolicRadical τ K J ⊔ subsystemGroup τ K J) := by
    rw [← parabolicRadical_sup_parabolicLevi J]
    exact sup_left_comm _ _ _
  have hHR : torusGroup τ K ≤
      Subgroup.normalizer (parabolicRadical τ K J : Set (ModGL τ K)) :=
    torusGroup_le_normalizer_rootSpan fun _ hα => hα.1.1
  have hHN : torusGroup τ K ≤ Subgroup.normalizer
      ((parabolicRadical τ K J ⊔ subsystemGroup τ K J : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) :=
    (le_inf hHR (torusGroup_le_normalizer_subsystemGroup J)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hNP : parabolicRadical τ K J ⊔ subsystemGroup τ K J ≤ parabolicSubgroup τ K J :=
    sup_le hRP hLP
  have hPN : parabolicSubgroup τ K J ≤ Subgroup.normalizer
      ((parabolicRadical τ K J ⊔ subsystemGroup τ K J : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) := by
    rw [hPsup]
    exact sup_le hHN Subgroup.le_normalizer
  have hodd : ¬ 2 ∣ (parabolicRadical τ K J ⊔ subsystemGroup τ K J).relIndex
      (parabolicSubgroup τ K J) := by
    intro h
    have hrel := relIndex_sup_of_le_normalizer hHN
    rw [← hPsup] at hrel
    rw [hrel] at h
    exact not_two_dvd_card_torusGroup (h.trans (Subgroup.relIndex_dvd_card _ _))
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hRfin⟩ := parabolic_root_radical_Levi_factors τ K J
  have hRp : IsPGroup 2 (parabolicRadical τ K J) := (hRfin 2).2.1
  have hcop : Nat.Coprime p (Nat.card ↥(parabolicRadical τ K J ⊔ subsystemGroup τ K J)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2
      (not_dvd_card_sup_of_isPGroup_two hp hp2 hRp (hLP.trans hPR) hpL)
  have hNcore : parabolicRadical τ K J ⊔ subsystemGroup τ K J ≤
      rankThreePrimeCore p (parabolicSubgroup τ K J) :=
    le_sSup ⟨hNP, Subgroup.normal_subgroupOf_of_le_normalizer hPN, hcop⟩
  obtain ⟨U, hU⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (parabolicSubgroup τ K J)
  exact hsyl U hU
    ((le_of_isPGroup_two_of_not_dvd_relIndex hNP hPN hU.le hU.isPGroup hodd).trans hNcore)

end Certified

end CFSG.LieType.Chevalley.ParSylow
