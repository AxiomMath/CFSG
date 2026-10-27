module

public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.PPrime
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.ClassicalInvolution.ModelFacts.OddCover

open Matrix CFSG.SectionRank.OddCover CFSG.LieType.Steinberg

universe u

theorem sl2_noCover {K : Type} [Field K] {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    NoCover.{u} (fun n => Odd n ∧ ¬ p ∣ n) (SpecialLinearGroup (Fin 2) K) := by
  intro E _ _ _ π hπ hcen ⟨hodd, hpC⟩
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let ρ : E →* ProjectiveSpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) K))).comp π
  have hρsurj : Function.Surjective ρ := (QuotientGroup.mk'_surjective _).comp hπ
  have hρker : ρ.ker = Subgroup.center E := by
    rw [← ComponentClassification.Quasisimple.center_comap_of_central_kernel π hπ hcen]
    ext x
    exact QuotientGroup.eq_one_iff _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Subgroup.center E)) := inferInstance
  set T : Subgroup E := (P : Subgroup (Subgroup.center E)).map (Subgroup.center E).subtype
    with hT
  have hTc : T ≤ Subgroup.center E := Subgroup.map_subtype_le _
  have : T.Normal := Subgroup.normal_of_le_center hTc
  have hTp : IsPGroup 2 T := P.isPGroup'.map (Subgroup.center E).subtype
  have hTker : T ≤ ρ.ker := hρker ▸ hTc
  let ψ : E ⧸ T →* ProjectiveSpecialLinearGroup (Fin 2) K := QuotientGroup.lift T ρ hTker
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨j, hj⟩ := hρsurj y
    exact ⟨(j : E ⧸ T), hj⟩
  have hψker : ψ.ker = (Subgroup.center E).map (QuotientGroup.mk' T) := by
    rw [QuotientGroup.ker_lift, hρker]
  have hψcentral : ψ.ker ≤ Subgroup.center (E ⧸ T) := by
    rw [hψker]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective T q
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g]
  have hψodd : Odd (Nat.card ψ.ker) := by
    let ρ' : Subgroup.center E →* E ⧸ T := (QuotientGroup.mk' T).comp (Subgroup.center E).subtype
    have hker' : ρ'.ker = (P : Subgroup (Subgroup.center E)) := by
      ext x
      change QuotientGroup.mk' T x.1 = 1 ↔ x ∈ (P : Subgroup (Subgroup.center E))
      rw [show QuotientGroup.mk' T x.1 = 1 ↔ x.1 ∈ T from QuotientGroup.eq_one_iff _]
      exact Subgroup.mem_map_iff_mem (Subgroup.center E).subtype_injective
    have hrange : ρ'.range = ψ.ker := by
      rw [hψker]
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨z.1, z.2, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨z, hz⟩, rfl⟩
    have hcard : Nat.card ψ.ker = (P : Subgroup (Subgroup.center E)).index := by
      rw [← hrange, ← hker', Subgroup.index_eq_card]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ').toEquiv).symm
    rw [hcard]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      (fun h => P.not_dvd_index (by simpa using h)) |> fun h => by omega)
  have : Group.IsPerfect (E ⧸ T) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' T) (QuotientGroup.mk'_surjective T)
  have hcov := psl_two_perfect_odd_cover_kernel hp2 hK ψ hψsurj hψcentral hψodd
  have hmem : ∀ c ∈ π.ker, QuotientGroup.mk' T c ∈ ψ.ker := fun c hc => by
    change ψ (QuotientGroup.mk' T c) = 1
    change ρ c = 1
    rw [show ρ c = QuotientGroup.mk' _ (π c) from rfl, MonoidHom.mem_ker.1 hc, map_one]
  let emb : π.ker →* ψ.ker :=
    ((QuotientGroup.mk' T).comp π.ker.subtype).codRestrict ψ.ker fun c => hmem c c.2
  have hemb : Function.Injective emb := by
    rw [injective_iff_map_eq_one]
    intro c hc
    have hcT : (c : E) ∈ T := (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hc)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hTp) ⟨(c : E), hcT⟩
    have hk' : orderOf (c : E) = 2 ^ k := (Subgroup.orderOf_coe ⟨(c : E), hcT⟩).trans hk
    have hodd' : Odd (orderOf (c : E)) := by
      have h1 : orderOf (c : E) ∣ Nat.card π.ker := by
        rw [Subgroup.orderOf_coe]
        exact orderOf_dvd_natCard c
      exact Odd.of_dvd_nat hodd h1
    exact Subtype.ext (eq_one_of_odd_orderOf hodd' hk')
  have hdvd : Nat.card π.ker ∣ Nat.card ψ.ker := Subgroup.card_dvd_of_injective emb hemb
  by_cases h9 : p ^ f = 9
  · obtain ⟨hp3, -⟩ := eq_three_of_pow_eq_nine (Fact.out : p.Prime) h9
    have hle : Nat.card ψ.ker ≤ 3 := (hcov.2 h9).2
    have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
    have hle' : Nat.card π.ker ≤ 3 := (Nat.le_of_dvd hpos hdvd).trans hle
    have hpos' : 0 < Nat.card π.ker := Nat.card_pos
    have h1 : Nat.card π.ker = 1 := by
      subst hp3
      obtain ⟨m, hm⟩ := hodd
      interval_cases hc : Nat.card π.ker
      · rfl
      · omega
      · exact absurd (dvd_refl 3) hpC
    exact Subgroup.card_eq_one.1 h1
  · have hbot : ψ.ker = ⊥ := (hcov.1 h9)
    have h1 : Nat.card ψ.ker = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h2 : Nat.card π.ker = 1 := Nat.eq_one_of_dvd_one (h1 ▸ hdvd)
    exact Subgroup.card_eq_one.1 h2

end CFSG.ClassicalInvolution.ModelFacts.OddCover
