module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

theorem derivedSeries_eq_top_of_perfect {X : Type} [Group X] (h : Group.IsPerfect X) (n : ℕ) :
    derivedSeries X n = ⊤ := by
  induction n with
  | zero => exact derivedSeries_zero X
  | succ n ih =>
    rw [derivedSeries_succ, ih]
    exact h.commutator_eq_top

theorem map_eq_one_of_solvable {Y : Type} [Group Y] (P : Subgroup Y) [P.Normal]
    (hP : IsPGroup 2 P) (hperf : Group.IsPerfect (Y ⧸ P)) (T : Subgroup Y)
    (hT : ∀ y : Y, ∃ t ∈ T, ∃ p ∈ P, y = t * p) {Q : Type} [Group Q] [Group.IsSolvable Q]
    (ψ : T →* Q) (t : T) (ht : ¬ 2 ∣ orderOf t) : ψ t = 1 := by
  let π : T →* Y ⧸ P := (QuotientGroup.mk' P).comp T.subtype
  have hπ : Function.Surjective π := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨t, htT, p, hp, rfl⟩ := hT y
    refine ⟨⟨t, htT⟩, ?_⟩
    change (QuotientGroup.mk' P) t = _
    simp only [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    simpa using P.inv_mem hp
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := Q)
  have hmap : (derivedSeries T n).map π = ⊤ := by
    rw [map_derivedSeries_eq hπ, derivedSeries_eq_top_of_perfect hperf]
  have hmem : π t ∈ (derivedSeries T n).map π := by rw [hmap]; trivial
  obtain ⟨u, hu, hut⟩ := hmem
  have hψu : ψ u = 1 := by
    have : ψ u ∈ derivedSeries Q n := map_derivedSeries_le_derivedSeries ψ n ⟨u, hu, rfl⟩
    rwa [hn, Subgroup.mem_bot] at this
  have hw : ((u⁻¹ * t : T) : Y) ∈ P := by
    have : π (u⁻¹ * t) = 1 := by rw [map_mul, map_inv, hut, inv_mul_cancel]
    change (QuotientGroup.mk' P) ((u⁻¹ * t : T) : Y) = 1 at this
    exact (QuotientGroup.eq_one_iff _).1 this
  obtain ⟨k, hk⟩ := hP ⟨_, hw⟩
  have hk' : (u⁻¹ * t) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have e : ψ t = ψ (u⁻¹ * t) := by rw [map_mul, map_inv, hψu, inv_one, one_mul]
  have h1 : orderOf (ψ t) ∣ 2 ^ k := by
    rw [e]; exact orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk', map_one])
  have h2 : orderOf (ψ t) ∣ orderOf t := orderOf_map_dvd ψ t
  have h3 : Nat.Coprime (2 ^ k) (orderOf t) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 ht)
  have : orderOf (ψ t) = 1 := Nat.eq_one_of_dvd_coprimes h3 h1 h2
  exact orderOf_eq_one_iff.1 this

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
