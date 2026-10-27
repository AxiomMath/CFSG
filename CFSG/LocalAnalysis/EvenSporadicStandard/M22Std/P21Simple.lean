module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Layer
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.P21Gl8
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResFinal

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std CFSG.EvenSporadicStandard.M23Std

theorem gl8_dvd_gl12 : gl8 ∣ gl12 := by
  unfold gl8 gl12
  norm_num [Finset.prod_range_succ]

variable {G : Type} [Group G] [Finite G]

theorem exists_cover_of_eData (hG : Nat.card G ∣ gl8)
    (hE : EData ↥(egaLayer (G ⧸ fusionOddCore G))) :
    ∃ U : Subgroup G, U.Normal ∧ U ⊓ fusionOddCore G = ⊥ ∧
      Nonempty (U ≃* ↥(egaLayer (G ⧸ fusionOddCore G))) ∧ egaLayer G = U := by
  set E := egaLayer (G ⧸ fusionOddCore G) with hEdef
  have hEn : E.Normal := egaLayer_normal _
  have hEperf : commutator E = ⊤ := commutator_eq_top_of_simple hE.chief.simple hE.nonab
  obtain ⟨U, hUn, hUperf, q, hq, hqU⟩ := exists_perfect_cover (fusionOddCore G) E hEperf
  have hodd : Odd (Nat.card q.ker) := by
    have hle : q.ker.map U.subtype ≤ fusionOddCore G := by
      rintro _ ⟨u, hu, rfl⟩
      have h1 : QuotientGroup.mk (u : G) = (1 : G ⧸ fusionOddCore G) := by
        rw [← hqU u, MonoidHom.mem_ker.1 hu]
        rfl
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hd : Nat.card q.ker ∣ Nat.card (fusionOddCore G) := by
      rw [← Subgroup.card_map_of_injective U.subtype_injective (K := q.ker)]
      exact Subgroup.card_dvd_of_le hle
    exact Odd.of_dvd_nat (natCard_fusionOddCore_odd G) hd
  have hUcard : Nat.card U ∣ gl12 :=
    (Subgroup.card_subgroup_dvd_card U).trans (hG.trans gl8_dvd_gl12)
  have hk := card_ker_eq_one_of_chiefData oddSolv elemAbH1 elemAbH2 hUperf q hq hodd hUcard
    hE.chief hE.hopf
  have hinj : Function.Injective q := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have : u ∈ q.ker := hu
    rw [Subgroup.eq_bot_of_card_eq q.ker hk] at this
    exact Subgroup.mem_bot.1 this
  let e : U ≃* E := MulEquiv.ofBijective q ⟨hinj, hq⟩
  obtain ⟨a, b, hab⟩ := hE.nonab
  have hnt : Nontrivial E :=
    ⟨⟨a, 1, fun h => hab (by rw [h]; simp)⟩⟩
  have hsimp : IsSimpleGroup E := ⟨fun N hN => hE.chief.simple N hN⟩
  have hsimpU : IsSimpleGroup U := MulEquiv.isSimpleGroup e
  have hnabU : ∃ x y : U, x * y ≠ y * x := by
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  refine ⟨U, hUn, ?_, ⟨e⟩, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    have h1 : q ⟨x, (mem_inf.1 hx).1⟩ = 1 := by
      apply Subtype.ext
      have := hqU ⟨x, (mem_inf.1 hx).1⟩
      rw [this]
      exact (QuotientGroup.eq_one_iff _).2 (mem_inf.1 hx).2
    have := hinj (h1.trans (map_one q).symm)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  · refine egaLayer_eq_of_cover (U := U) hnabU ?_
    intro y hy
    obtain ⟨u, hu⟩ := hq ⟨y, hy⟩
    refine ⟨u, u.2, ?_⟩
    have := hqU u
    rw [hu] at this
    exact this.symm

omit [Finite G] in
theorem isSimpleGroup_of_eData {E : Type} [Group E] (hE : EData E) : IsSimpleGroup E := by
  obtain ⟨a, b, hab⟩ := hE.nonab
  have hnt : Nontrivial E := ⟨⟨a, 1, fun h => hab (by rw [h]; simp)⟩⟩
  exact ⟨fun N hN => hE.chief.simple N hN⟩

end CFSG.EvenSporadicStandard.M22Std
