module

public import CFSG.RankThree.PartOne.K1327.Trick
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free

open CFSG.Open CFSG.AGLEmbedding Subgroup

variable {A : Type} [Group A] [Finite A] {p : ℕ}

theorem one_le_pRank_zpowers (hp : p.Prime) {f : A} (hfp : f ^ p = 1) (hf1 : f ≠ 1) :
    1 ≤ Open.pRank p (zpowers f) := by
  have : Fact p.Prime := ⟨hp⟩
  refine CFSG.GH74.Uniqueness.SU.SU1.le_pRank hp.one_lt le_rfl
    (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hfp) ?_
  rw [Nat.card_zpowers, pow_one]
  exact orderOf_eq_prime hfp hf1

theorem mem_normalizer_zpowers_of_commute {f o : A} (h : o * f = f * o) :
    o ∈ normalizer ((zpowers f : Subgroup A) : Set A) := by
  refine centralizer_le_normalizer _ ?_
  rw [mem_centralizer_iff]
  intro w hw
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
  exact (Commute.zpow_left (show Commute f o from h.symm) k).eq

theorem rankThreePrimeCore_le_of_plane (hp : p.Prime) {X Y F : Subgroup A} (hFX : F ≤ X)
    (hF : IsElemAbelian p F) (hFcard : Nat.card F = p ^ 2)
    (hN : ∀ f ∈ F, f ≠ 1 → normalizer ((zpowers f : Subgroup A) : Set A) ⊓ X ≤ Y) :
    rankThreePrimeCore p X ≤ Y := by
  have : Fact p.Prime := ⟨hp⟩
  have hOX : rankThreePrimeCore p X ≤ X := glbPrimeCore_le p X
  have hFN : F ≤ normalizer (rankThreePrimeCore p X : Set A) :=
    hFX.trans (le_normalizer_glbPrimeCore p X)
  have hcop : ¬ p ∣ Nat.card (rankThreePrimeCore p X) := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (glbPrimeCore_coprime p X) h)
  refine (CFSG.RankThree.PartOne.K1327.le_iSup_centralizers hp hF hFcard hFN hcop).trans ?_
  refine iSup_le fun ⟨f, hf1⟩ => ?_
  have hf1' : (f : A) ≠ 1 := fun h => hf1 (Subtype.ext h)
  intro o ho
  obtain ⟨hoO, hof⟩ := mem_inf.mp ho
  exact hN f f.2 hf1' ⟨mem_normalizer_zpowers_of_commute (mem_centralizer_singleton_iff.mp hof),
    hOX hoO⟩

theorem rankThreePrimeCore_le_of_gammaOne_cube (hp : p.Prime) {X Y Q : Subgroup A} (hQX : Q ≤ X)
    (h3 : 3 ≤ Open.pRank p Q)
    (hΓ1 : ∀ E : Subgroup A, E ≤ Q → IsElemAbelian p E → Nat.card E = p ^ 3 →
      ∀ S : Subgroup A, S ≤ E → 1 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y) :
    rankThreePrimeCore p X ≤ Y := by
  obtain ⟨E, hEQ, hE, hEcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp h3
  obtain ⟨F, hFE, hF, hFcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_subgroup_card hp hE (j := 2) (by norm_num) hEcard
  refine rankThreePrimeCore_le_of_plane hp (hFE.trans (hEQ.trans hQX)) hF hFcard
    fun f hf hf1 => ?_
  exact hΓ1 E hEQ hE hEcard _ (zpowers_le.mpr (hFE hf)) (one_le_pRank_zpowers hp (hF.2 f hf) hf1)

theorem rankThreePrimeCore_le_of_gammaOne_plane (hp : p.Prime) {X Y U : Subgroup A} (hUX : U ≤ X)
    (hU : IsElemAbelian p U) (hUcard : Nat.card U = p ^ 2)
    (hΓ1 : ∀ S : Subgroup A, S ≤ U → 1 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y) :
    rankThreePrimeCore p X ≤ Y :=
  rankThreePrimeCore_le_of_plane hp hUX hU hUcard fun f hf hf1 =>
    hΓ1 _ (zpowers_le.mpr hf) (one_le_pRank_zpowers hp (hU.2 f hf) hf1)

theorem mem_normalizer_of_mem_normalizer_subgroupOf {X K : Subgroup A} (hKX : K ≤ X) {y : X}
    (hy : y ∈ normalizer ((K.subgroupOf X : Subgroup X) : Set X)) :
    (y : A) ∈ normalizer (K : Set A) := by
  rw [mem_normalizer_iff] at hy ⊢
  intro g
  constructor
  · intro hg
    have h1 := (hy ⟨g, hKX hg⟩).mp (mem_subgroupOf.mpr hg)
    exact mem_subgroupOf.mp h1
  · intro hg
    have hgX : g ∈ X := by
      have h1 : (y : A) * g * (y : A)⁻¹ ∈ X := hKX hg
      have h2 : g = (y : A)⁻¹ * ((y : A) * g * (y : A)⁻¹) * y := by group
      rw [h2]
      exact X.mul_mem (X.mul_mem (X.inv_mem y.2) h1) y.2
    exact mem_subgroupOf.mp ((hy ⟨g, hgX⟩).mpr (mem_subgroupOf.mpr hg))

theorem le_sup_of_normal_of_gammaTwo (hp : p.Prime) {X Y Q N : Subgroup A} (hNX : N ≤ X)
    (hXN : X ≤ normalizer (N : Set A)) (hQX : Q ≤ X) (hQ : IsPGroup p Q)
    (hQsyl : ¬ p ∣ (Q.subgroupOf X).index) (h2 : 2 ≤ Open.pRank p (Q ⊓ N))
    (hΓ2 : ∀ S : Subgroup A, S ≤ Q → 2 ≤ Open.pRank p S → normalizer (S : Set A) ⊓ X ≤ Y) :
    X ≤ N ⊔ Y := by
  have : Fact p.Prime := ⟨hp⟩
  set N' : Subgroup X := N.subgroupOf X
  have : N'.Normal := (normal_subgroupOf_iff_le_normalizer hNX).mpr hXN
  set S : Sylow p X := (hQ.comap_subtype (K := X)).toSylow hQsyl
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S
    (Subgroup.Normal.isSubnormal (H := N') inferInstance)
  have hD : (S : Subgroup X) ⊓ N' = (Q ⊓ N).subgroupOf X := by
    ext y
    simp [S, N', mem_subgroupOf]
  have hNY : normalizer (((Q ⊓ N).subgroupOf X : Subgroup X) : Set X) ≤ Y.comap X.subtype :=
    fun y hy => hΓ2 _ inf_le_left h2
      ⟨mem_normalizer_of_mem_normalizer_subgroupOf (inf_le_right.trans hNX) hy, y.2⟩
  have htop := Sylow.normalizer_sup_eq_top P
  rw [hP, hD] at htop
  intro x hx
  have hmem : (⟨x, hx⟩ : X) ∈ normalizer (((Q ⊓ N).subgroupOf X : Subgroup X) : Set X) ⊔ N' := by
    rw [htop]
    exact mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ := mem_sup_of_normal_right.mp hmem
  have hx' : x = (y : A) * z := (congrArg Subtype.val hyz).symm
  rw [hx', sup_comm]
  exact mul_mem_sup (hNY hy) (mem_subgroupOf.mp hz)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free
