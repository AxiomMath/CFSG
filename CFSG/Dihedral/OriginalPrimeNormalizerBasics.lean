module

public import CFSG.Dihedral.OriginalSylowControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
import all CFSG.Dihedral.BlueprintDefs

public noncomputable section

namespace CFSG.DihedralBlueprint

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_mapped_center (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((Subgroup.center P).map P.subtype : Set G) := by
  intro g hg
  let a : MulAut P := P.normalizerMonoidHom ⟨g, hg⟩
  have h := congrArg (Subgroup.map P.subtype) (Subgroup.map_center_eq a)
  have hcomp : P.subtype.comp a.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp P.subtype := by
    ext x
    exact Subgroup.normalizerMonoidHom_apply_apply_coe P ⟨g, hg⟩ x
  simp only [Subgroup.map_map] at h
  change (Subgroup.center P).map (P.subtype.comp a.toMonoidHom) =
    (Subgroup.center P).map P.subtype at h
  rw [hcomp, ← Subgroup.map_map] at h
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

theorem isSylowIn_ne_bot_of_dvd (p : ℕ) (hp : p.Prime) (P H : Subgroup G)
    (hP : IsSylowIn p P H) (hdiv : p ∣ Nat.card H) : P ≠ ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQ⟩ := (isSylowIn_iff_exists_sylow p P H).mp hP
  rw [← hQ]
  exact fun hbot => Q.ne_bot_of_dvd_card hdiv
    ((Subgroup.map_eq_bot_iff_of_injective (Q : Subgroup H) H.subtype_injective).mp hbot)

namespace OriginalData

variable (d : OriginalData G)

theorem prime_sylow_ne_bot (p : ℕ) (hp : p ∈ primeSupport d.R)
    (P : Subgroup G) (hP : IsSylowIn p P d.R) : P ≠ ⊥ :=
  isSylowIn_ne_bot_of_dvd p hp.1 P d.R hP hp.2

theorem prime_sylow_isSylowIn_C (p : ℕ) (hp : p ∈ primeSupport d.R)
    (P : Subgroup G) (hP : IsSylowIn p P d.R) : IsSylowIn p P d.C := by
  let : Fact p.Prime := ⟨hp.1⟩
  refine ⟨hP.1.trans d.R_le, hP.2.1, ?_⟩
  intro Q hQC hQp hPQ
  have hpodd : Odd p := d.R_odd.of_dvd_nat hp.2
  obtain ⟨a, ha⟩ := hQp.exists_card_eq
  have hQodd : Odd (Nat.card Q) := ha ▸ hpodd.pow
  exact hP.2.2 Q (d.odd_subgroup_le_R_of_le_C Q hQC hQodd) hQp hPQ

theorem normalizer_le_HP (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ d.HP P :=
  normalizer_le_normalizer_mapped_center P

theorem sylow_le_HP (P : Subgroup G) (hPS : NormalizedBy P (d.S : Subgroup G)) :
    (d.S : Subgroup G) ≤ d.HP P :=
  hPS.trans (d.normalizer_le_HP P)

theorem prime_center_ne_bot (p : ℕ) (hp : p ∈ primeSupport d.R)
    (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    (Subgroup.center P).map P.subtype ≠ ⊥ := by
  let : Fact p.Prime := ⟨hp.1⟩
  let : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr (d.prime_sylow_ne_bot p hp P hP)
  exact fun hbot => hP.2.1.bot_lt_center.ne'
    ((Subgroup.map_eq_bot_iff_of_injective (Subgroup.center P) P.subtype_injective).mp hbot)

theorem HP_ne_top_of_prime_sylow [IsSimpleGroup G] (p : ℕ)
    (hp : p ∈ primeSupport d.R) (P : Subgroup G) (hP : IsSylowIn p P d.R) :
    d.HP P ≠ ⊤ := by
  intro htop
  let Z : Subgroup G := (Subgroup.center P).map P.subtype
  have hnormal : Z.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases hnormal.eq_bot_or_eq_top with hbot | hfull
  · exact d.prime_center_ne_bot p hp P hP hbot
  · have hZodd : Odd (Nat.card Z) := d.R_odd.of_dvd_nat
      (Subgroup.card_dvd_of_le ((Subgroup.map_subtype_le _).trans hP.1))
    rw [hfull, Subgroup.card_top] at hZodd
    have htwo : 2 ∣ Nat.card G := by
      simpa only [d.t_order] using orderOf_dvd_natCard d.t
    exact hZodd.not_two_dvd_nat htwo

end OriginalData

end CFSG.DihedralBlueprint
