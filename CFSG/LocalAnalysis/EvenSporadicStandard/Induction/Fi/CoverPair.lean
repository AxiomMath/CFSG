module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.CoverLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiCoverLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.OddQuot
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.FiDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Induction.Fi

open Subgroup Cover CFSG.EvenSporadicStandard.Solomon78 CFSG.EvenSporadicStandard.Induction.Hyp

theorem isPerfect_of_commutator_eq_self {G : Type} [Group G] {K : Subgroup G} (h : ⁅K, K⁆ = K) :
    Group.IsPerfect ↥K := by
  refine Group.isPerfect_def.2 ?_
  apply Subgroup.map_injective K.subtype_injective
  rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, h]

theorem isQuasisimple_of_perfect_cover {A B : Type} [Group A] [Group B]
    (hA : Group.IsPerfect A) (hB : CFSG.IsQuasisimple B) (π : A →* B)
    (hπ : Function.Surjective π) (hker : π.ker ≤ center A) : CFSG.IsQuasisimple A := by
  obtain ⟨e⟩ := cqEquiv_of_cover π hπ hker
  refine ⟨hA, ?_, ?_⟩
  · have := hB.2.1
    exact MulEquiv.isSimpleGroup e
  · obtain ⟨a, b, hab⟩ := hB.2.2
    exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective (by simpa [map_mul] using h))⟩

theorem exists_fiLoc_of_cover {H : Type} [Group H] [Finite H] {L : Subgroup H} {n : ℕ}
    (hodd : Odd (Nat.card (center ↥L))) {ū : ↥L ⧸ center ↥L} (hū : ū * ū = 1) (hū1 : ū ≠ 1)
    {Kb : Subgroup (↥L ⧸ center ↥L)} (hKb : Kb ≤ centralizer ({ū} : Set (↥L ⧸ center ↥L)))
    (hq : CFSG.IsQuasisimple ↥Kb) (hn : n ≤ Nat.card (↥Kb ⧸ CFSG.oddCore ↥Kb)) :
    ∃ (K : Subgroup H) (u : H), fiLoc n H L K u := by
  obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective ū
  obtain ⟨u₀, -, hu₀2, hu₀q⟩ := exists_involution_lift hodd (K := ⊤)
    (kt := (QuotientGroup.mk x₀ : ↥L ⧸ center ↥L)) ⟨x₀, Subgroup.mem_top _, rfl⟩ hū
  have hu₀1 : u₀ ≠ 1 := fun h => hū1 (by rw [← hu₀q, h, map_one])
  set P : Subgroup ↥L := Kb.comap (q ↥L) with hP
  have hPmap : P.map (q ↥L) = Kb :=
    Subgroup.map_comap_eq_self_of_surjective QuotientGroup.mk_surjective Kb
  have hKbperf : ⁅Kb, Kb⁆ = Kb := Cover.commutator_eq_self_of_isPerfect hq.1
  set K₀ : Subgroup ↥L := ⁅P, P⁆ with hK₀
  have hK₀map : K₀.map (q ↥L) = Kb := by
    rw [hK₀, Subgroup.map_commutator, hPmap, hKbperf]
  have hK₀P : K₀ ≤ P := commutator_self_le P
  have hPC : P ≤ centralizer ({u₀} : Set ↥L) := fun p hp =>
    (mem_centralizer_singleton_iff_mk hodd hu₀2).2 (by rw [hu₀q]; exact hKb hp)
  have hPle : P ≤ K₀ ⊔ center ↥L := by
    intro c hc
    rw [← comap_map_q K₀, hK₀map]
    exact hc
  have hK₀perf : ⁅K₀, K₀⁆ = K₀ := by
    refine le_antisymm (commutator_self_le K₀) ?_
    calc K₀ = ⁅P, P⁆ := rfl
      _ ≤ ⁅K₀ ⊔ center ↥L, K₀ ⊔ center ↥L⁆ := Subgroup.commutator_mono hPle hPle
      _ ≤ ⁅K₀, K₀⁆ := commutator_sup_center_le K₀
  let g : ↥K₀ →* ↥Kb :=
    ((q ↥L).comp K₀.subtype).codRestrict Kb (fun k => by
      rw [← hK₀map]
      exact ⟨k, k.2, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨d, hd⟩
    rw [← hK₀map] at hd
    obtain ⟨k, hk, rfl⟩ := hd
    exact ⟨⟨k, hk⟩, rfl⟩
  have hgker : ∀ k : ↥K₀, k ∈ g.ker ↔ (k : ↥L) ∈ center ↥L := fun k => by
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      exact q_eq_one_iff.1 (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext (q_eq_one_iff.2 h)
  have hgc : g.ker ≤ center ↥K₀ := fun k hk => by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext ((Subgroup.mem_center_iff.1 ((hgker k).1 hk) w))
  have hgodd : Odd (Nat.card g.ker) := by
    let f : ↥g.ker →* ↥(center ↥L) :=
      { toFun := fun k => ⟨((k : ↥K₀) : ↥L), (hgker k.1).1 k.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := fun a b h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ↥(center ↥L) => (z : ↥L)) h))
    exact hodd.of_dvd_nat (Subgroup.card_dvd_of_injective f hf)
  have hK₀q : CFSG.IsQuasisimple ↥K₀ :=
    isQuasisimple_of_perfect_cover (isPerfect_of_commutator_eq_self hK₀perf) hq g hg hgc
  have hnK₀ : n ≤ Nat.card (↥K₀ ⧸ CFSG.oddCore ↥K₀) := by
    obtain ⟨e⟩ := oddQuot_equiv_of_surj g hg hgodd
    rw [Nat.card_congr e.toEquiv]
    exact hn
  let ι : ↥K₀ ≃* ↥(K₀.map L.subtype) := K₀.equivMapOfInjective L.subtype L.subtype_injective
  have hu2 : orderOf (u₀ : H) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hu₀2) hu₀1
  refine ⟨K₀.map L.subtype, (u₀ : H), u₀.2, hu2, Subgroup.map_subtype_le _, ?_,
    CFSG.LocalCores.isQuasisimple_of_mulEquiv ι hK₀q, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hPC (hK₀P hk))
    exact congrArg Subtype.val this
  · obtain ⟨e⟩ := oddQuot_equiv_of_surj ι.toMonoidHom ι.surjective (by
      have : ι.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 ι.injective
      rw [this, Subgroup.card_bot]
      exact odd_one)
    rw [← Nat.card_congr e.toEquiv]
    exact hnK₀

end CFSG.EvenSporadicStandard.Induction.Fi
