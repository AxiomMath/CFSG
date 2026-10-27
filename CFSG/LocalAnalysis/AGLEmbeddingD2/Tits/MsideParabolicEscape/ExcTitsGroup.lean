module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Sporadic.Schreier.TitsPrim

public section

namespace CFSG.Sporadic.Schreier.Tits


theorem mem_titsS_iff_flag (g : titsH) :
    (g : Equiv.Perm (Fin 1755)) ∈ titsS ↔ titsHFlag g 0 = 0 := by
  rw [titsS_eq_stab]
  constructor
  · rintro ⟨d, hd, e⟩
    have : Subgroup.inclusion titsH_le_titsD g = d := Subtype.ext e.symm
    show titsDFlagAct (Subgroup.inclusion titsH_le_titsD g) 0 = 0
    rw [this]
    exact hd
  · intro h
    exact ⟨Subgroup.inclusion titsH_le_titsD g, h, rfl⟩

theorem card_titsS : Nat.card titsS = 2048 := titsQS_facts.2.2.2

theorem card_titsH : Nat.card titsH = 10240 := titsQH_facts.2.2.2

theorem card_titsJ : Nat.card titsJ = 512 := titsQJ_facts.2.2.2

theorem exists_titsHFlag_eq {j : Fin 8775} (hj : j ∈ titsF5) : ∃ h : titsH, titsHFlag h 0 = j := by
  let _ : MulAction titsH (Fin 8775) := MulAction.compHom _ titsHFlag
  have h0F : (0 : Fin 8775) ∈ titsF5 := by
    show titsBeta 0 = 0
    exact titsBeta_zero
  have hsub : MulAction.orbit titsH (0 : Fin 8775) ⊆ titsF5 := by
    rintro _ ⟨h, rfl⟩
    exact (titsHFlag_mem h 0).2 h0F
  have hstab : MulAction.stabilizer titsH (0 : Fin 8775) = titsS.subgroupOf titsH := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_titsS_iff_flag]
    rfl
  have hcard : (MulAction.orbit titsH (0 : Fin 8775)).ncard = 5 := by
    rw [← MulAction.index_stabilizer, hstab]
    have h1 := Subgroup.card_mul_index (titsS.subgroupOf titsH)
    rw [card_subgroupOf_eq titsS_le_titsH, card_titsS, card_titsH] at h1
    omega
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [titsF5_ncard, hcard])
  rw [← heq] at hj
  obtain ⟨h, rfl⟩ := hj
  exact ⟨h, rfl⟩

theorem not_normal_titsS : ¬ (titsS.subgroupOf titsH).Normal := by
  intro hn
  have hfix : ∀ s : titsH, (s : Equiv.Perm (Fin 1755)) ∈ titsS → titsH5 s = 1 := by
    intro s hs
    rw [titsH5_eq_one_iff]
    intro j hj
    obtain ⟨h, rfl⟩ := exists_titsHFlag_eq hj
    have hconj : h⁻¹ * s * h ∈ titsS.subgroupOf titsH := by
      have := hn.conj_mem s hs h⁻¹
      simpa using this
    have h0 : titsHFlag (h⁻¹ * s * h) 0 = 0 := (mem_titsS_iff_flag _).1 hconj
    show titsHFlag s (titsHFlag h 0) = titsHFlag h 0
    have e : titsHFlag s (titsHFlag h 0) = titsHFlag h (titsHFlag (h⁻¹ * s * h) 0) := by
      rw [map_mul, map_mul, map_inv]
      simp [Equiv.Perm.mul_apply]
    rw [e, h0]
  have hle : titsS.subgroupOf titsH ≤ titsJ.subgroupOf titsH := by
    intro s hs
    rw [← titsH5_range_ker.2]
    exact hfix s hs
  have := Subgroup.card_le_of_le hle
  rw [card_subgroupOf_eq titsS_le_titsH, card_subgroupOf_eq titsJ_le_titsH, card_titsS,
    card_titsJ] at this
  omega

theorem mem_titsS_of_normalizes (g : titsH)
    (hg : g ∈ Subgroup.normalizer ((titsS.subgroupOf titsH : Subgroup titsH) : Set titsH)) :
    (g : Equiv.Perm (Fin 1755)) ∈ titsS := by
  by_contra hgS
  set S' := titsS.subgroupOf titsH with hS'
  set NS := Subgroup.normalizer (S' : Set titsH) with hNS
  have hle : S' ≤ NS := Subgroup.le_normalizer
  have hlt : S' < NS := lt_of_le_of_ne hle fun h => hgS (by
    have : g ∈ S' := h ▸ hg
    exact Subgroup.mem_subgroupOf.mp this)
  have h1 : Nat.card S' ∣ Nat.card NS := Subgroup.card_dvd_of_le hle
  have h2 : Nat.card NS ∣ Nat.card titsH := Subgroup.card_subgroup_dvd_card NS
  have h3 : Nat.card S' < Nat.card NS := Subgroup.card_lt_of_lt hlt
  rw [card_subgroupOf_eq titsS_le_titsH, card_titsS] at h1 h3
  rw [card_titsH] at h2
  obtain ⟨k, hk⟩ := h1
  have hk5 : k ≤ 5 := by
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have h4 : Nat.card NS = 10240 := by
    rw [hk] at h2 h3 ⊢
    interval_cases k <;> simp_all
  have htop : NS = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h4, card_titsH])
  exact not_normal_titsS (Subgroup.normalizer_eq_top_iff.mp htop)

theorem eq_zero_of_titsS_fix {y : Fin 1755} (hy : ∀ s ∈ titsS, s y = y) : y = 0 := by
  by_contra hy0
  obtain ⟨c, hc5, hyc⟩ := titsH0_orbit_cover y
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨⟨h, hh⟩, e⟩ := hyc
    apply hy0
    rw [← e]
    show h (finPt 1755 titsH0Reps[0]!) = 0
    have : finPt 1755 titsH0Reps[0]! = 0 := rfl
    rw [this]
    exact titsH0_fix h hh
  have hsize : 10 ≤ (MulAction.orbit titsH0 y).ncard := by
    have : MulAction.orbit titsH0 y = MulAction.orbit titsH0 (finPt 1755 titsH0Reps[c]!) :=
      MulAction.orbit_eq_iff.mpr hyc
    rw [this, titsH0_orbit_ncard hc5]
    interval_cases c <;> simp [titsStabSizes] at hc0 ⊢
  have hH0H : titsH0 ≤ titsH := by
    rw [titsH_eq_stab]
    intro g hg
    exact ⟨⟨g, titsH0_le_titsD hg⟩, titsH0_fix g hg, rfl⟩
  have horb : (MulAction.orbit titsH0 y).ncard ≤ (MulAction.orbit titsH y).ncard := by
    apply Set.ncard_le_ncard
    · rintro _ ⟨⟨g, hg⟩, rfl⟩
      exact ⟨⟨g, hH0H hg⟩, rfl⟩
    · exact Set.toFinite _
  have hstab : titsS.subgroupOf titsH ≤ MulAction.stabilizer titsH y := by
    intro s hs
    rw [MulAction.mem_stabilizer_iff]
    exact hy s hs
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer titsH y)
  rw [MulAction.index_stabilizer, card_titsH] at h1
  have h2 := Subgroup.card_le_of_le hstab
  rw [card_subgroupOf_eq titsS_le_titsH, card_titsS] at h2
  nlinarith

theorem mem_titsS_of_normalizes_D {g : Equiv.Perm (Fin 1755)} (hgD : g ∈ titsD)
    (hg : g ∈ Subgroup.normalizer (titsS : Set (Equiv.Perm (Fin 1755)))) : g ∈ titsS := by
  have hfix : ∀ s ∈ titsS, s (g 0) = g 0 := by
    intro s hs
    have hs' : g⁻¹ * s * g ∈ titsS := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) s).mp hs
      simpa using this
    have h0 : (g⁻¹ * s * g) 0 = 0 := titsH_fix ⟨_, titsS_le_titsH hs'⟩
    calc s (g 0) = g ((g⁻¹ * s * g) 0) := by simp [Equiv.Perm.mul_apply]
      _ = g 0 := by rw [h0]
  have hg0 : g 0 = 0 := eq_zero_of_titsS_fix hfix
  have hgH : g ∈ titsH := by
    rw [titsH_eq_stab]
    exact ⟨⟨g, hgD⟩, hg0, rfl⟩
  refine mem_titsS_of_normalizes ⟨g, hgH⟩ ?_
  rw [Subgroup.mem_normalizer_iff]
  intro s
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using Subgroup.mem_normalizer_iff.mp hg s

end CFSG.Sporadic.Schreier.Tits
