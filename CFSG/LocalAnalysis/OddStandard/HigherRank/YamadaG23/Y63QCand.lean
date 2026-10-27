module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63QCen

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Y63Chk Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {D : Data} {k : ℕ} {G : Type} [Group G] {P Q : Subgroup G} {Θ : ℕ → G}

private theorem card_mem_list {l : List ℕ} (hnd : l.Nodup) :
    Nat.card {a : ℕ // a ∈ l} = l.length := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun a => (List.mem_toFinset (l := l)).symm)),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd]

private theorem comm_eq_of_mul {g₁ g₂ c : G} (h : g₁ * g₂ = c * (g₂ * g₁)) : ⁅g₁, g₂⁆ = c := by
  rw [commutatorElement_def, h]
  group

theorem y63_cand (hΘ : Y63Model D k P Q Θ) (hC : D.CenSpec k) (hCand : D.CandSpec k)
    {U : Subgroup G} (hUd : ∀ g : G, g ∈ U ↔ ∃ a ∈ D.u0 k, Θ a = g) :
    ∀ x ∈ P, orderOf x = 2 → 2 ^ 7 ≤ Nat.card ↥(centEl Q x) →
      x ∉ ⁅centEl Q x, centEl Q x⁆ → x ∈ U ∧ cen Q ≤ ⁅centEl Q x, centEl Q x⁆ := by
  intro x hxP hord hcard hnc
  obtain ⟨i, hi512, rfl⟩ := hΘ.surjP x hxP
  have hi : i < 1024 := by omega
  have hcomm : ∀ j < 1024, Θ i * Θ j = Θ j * Θ i ↔ D.mq k i j = D.mq k j i := by
    intro j hj
    rw [← hΘ.mul i hi j hj, ← hΘ.mul j hj i hi]
    exact ⟨fun h => hΘ.inj _ (hΘ.mq_lt i hi j hj) _ (hΘ.mq_lt j hj i hi) h, fun h => by rw [h]⟩
  have hx2 : Θ i ^ 2 = 1 := by
    have := pow_orderOf_eq_one (Θ i)
    rwa [hord] at this
  have hx1 : Θ i ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hmqii : D.mq k i i = 0 := by
    apply hΘ.inj _ (hΘ.mq_lt i hi i hi) 0 (by norm_num)
    rw [hΘ.mul i hi i hi, hΘ.one, ← pow_two, hx2]
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hx1 hΘ.one
  have hmem : ∀ j, j ∈ D.Cen k i ↔ j < 1024 ∧ D.mq k i j = D.mq k j i := by
    intro j
    simp [Data.Cen]
  have hmemC : ∀ g, g ∈ centEl Q (Θ i) ↔ ∃ j ∈ D.Cen k i, Θ j = g := by
    intro g
    constructor
    · intro hg
      obtain ⟨hgQ, hgC⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨j, hj, rfl⟩ := hΘ.surj g hgQ
      refine ⟨j, (hmem j).mpr ⟨hj, ?_⟩, rfl⟩
      exact (hcomm j hj).mp (Subgroup.mem_centralizer_iff.mp hgC (Θ i) (Set.mem_singleton _))
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨hj1, hj2⟩ := (hmem j).mp hj
      refine Subgroup.mem_inf.mpr ⟨hΘ.mem j hj1, Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)⟩
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (hcomm j hj1).mpr hj2
  have hcardeq : Nat.card ↥(centEl Q (Θ i)) = (D.Cen k i).length := by
    have hnd : (D.Cen k i).Nodup := List.nodup_range.filter _
    rw [← card_mem_list hnd]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun j => ⟨Θ j.1, (hmemC _).mpr ⟨j.1, j.2, rfl⟩⟩) ⟨?_, ?_⟩)
    · intro j j' h
      exact Subtype.ext (hΘ.inj _ ((hmem j.1).mp j.2).1 _ ((hmem j'.1).mp j'.2).1
        (congrArg Subtype.val h))
    · rintro ⟨g, hg⟩
      obtain ⟨j, hj, rfl⟩ := (hmemC g).mp hg
      exact ⟨⟨j, hj⟩, rfl⟩
  have hlen : 128 ≤ (D.Cen k i).length := by
    rw [← hcardeq]
    exact hcard
  obtain ⟨hwit, hex⟩ := hCand
  obtain ⟨w, hw, hwx⟩ := hex i hi512 hi0 hmqii hlen
  obtain ⟨ha, hb, hxa, hxb, hcase⟩ := hwit w hw
  rw [hwx] at hxa hxb hcase
  have hΘa : Θ w.a ∈ centEl Q (Θ i) := (hmemC _).mpr ⟨w.a, (hmem _).mpr ⟨ha, hxa⟩, rfl⟩
  have hΘb : Θ w.b ∈ centEl Q (Θ i) := (hmemC _).mpr ⟨w.b, (hmem _).mpr ⟨hb, hxb⟩, rfl⟩
  have hcb : D.mq k w.b w.a < 1024 := hΘ.mq_lt _ hb _ ha
  rcases hcase with ⟨-, hab⟩ | ⟨-, hiu, hab⟩
  · exfalso
    apply hnc
    have h : Θ w.a * Θ w.b = Θ i * (Θ w.b * Θ w.a) := by
      rw [← hΘ.mul _ ha _ hb, hab, hΘ.mul _ hi _ hcb, hΘ.mul _ hb _ ha]
    have hmemc := Subgroup.commutator_mem_commutator hΘa hΘb
    rwa [comm_eq_of_mul h] at hmemc
  · have hz : D.z < 1024 := hC.1
    have h : Θ w.a * Θ w.b = Θ D.z * (Θ w.b * Θ w.a) := by
      rw [← hΘ.mul _ ha _ hb, hab, hΘ.mul _ hz _ hcb, hΘ.mul _ hb _ ha]
    refine ⟨(hUd _).mpr ⟨i, hiu, rfl⟩, fun g hg => ?_⟩
    rcases (y63_mem_cen hΘ hC g).mp hg with rfl | rfl
    · exact one_mem _
    · have hmemc := Subgroup.commutator_mem_commutator hΘa hΘb
      rwa [comm_eq_of_mul h] at hmemc

end CFSG.OddStandard.HigherRank.YamadaG23
