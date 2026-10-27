module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FSetup
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IPocketL
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7Helpers
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2FiveInv
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem sec4F_inducesTypeSome_i4 {L : Subgroup G} (hL : IsOmega7Group L) {w : G}
    (hw : IsI4PlusIn L w) : InducesTypeSome L w 7 1 4 1 := by
  obtain ⟨e⟩ := sec4I_exists_model hL
  obtain ⟨hwL, -, hty⟩ := (sec4I_isI4PlusIn_iff hL e).mp hw
  exact (sec4I_inducesTypeSome_mem_iff e hwL (Or.inr (Or.inl rfl))).mpr hty

theorem Sec4FSetup.not_outer6_of_mem_B (h : Sec4FSetup t L S z A B φ) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) : ¬ InducesTypeSome L b 7 1 6 1 := by
  intro h6
  have hL := h.omega7
  obtain ⟨v, hv, hvφ⟩ := (h.data.bdata.perm.2.2.1 b).mp hb
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hb1 (by rw [← hvφ, IsPermModuleVia.map_zero h.data.bdata.perm])
  rcases sec4I_vecWeight_cases hv hv0 with h2 | h4 | h6'
  · have := (h.data.bdata.type2 v hv hv0).mp h2
    rw [hvφ] at this
    have := sec4F_type_excl hL (Or.inl rfl) (Or.inr (Or.inr rfl)) this h6
    exact absurd this.1 (by norm_num)
  · have := sec4F_inducesTypeSome_i4 hL ((h.data.bdata.type4 v hv hv0).mp h4)
    rw [hvφ] at this
    have := sec4F_type_excl hL (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) this h6
    exact absurd this.1 (by norm_num)
  · have := (h.data.bdata.type6 v hv hv0).mp h6'
    rw [hvφ] at this
    have := sec4F_type_excl hL (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl)) this h6
    exact absurd this.2 (by decide)

theorem Sec4FSetup.pt_mem_conj (h : Sec4FSetup t L S z A B φ) (p : Option (Fin 7)) :
    sec4MPt t φ p ∈ conjClassIn ⊤ t := by
  cases p with
  | none =>
    have hpt : sec4MPt t φ none = t := by
      dsimp only [sec4MPt, sec4MV]
      rw [IsPermModuleVia.map_zero h.data.bdata.perm, mul_one]
    rw [hpt]
    exact ⟨1, Subgroup.mem_top 1, by simp⟩
  | some i =>
    have hv : IsEvenVec (sec4MW i) := sec4MW_even i
    have hw6 : vecWeight (sec4MW i) = 6 := sec4MW_weight i
    have hv0 : sec4MW i ≠ 0 := by
      intro h0
      have hw : vecWeight (sec4MW i) = 0 := by rw [h0]; simp [vecWeight]
      omega
    have hφB : φ (sec4MW i) ∈ B := h.data.bdata.perm.mem hv
    have hφL : φ (sec4MW i) ∈ L := h.B_le_L hφB
    have hφ2 : orderOf (φ (sec4MW i)) = 2 := h.data.bdata.perm.orderOf_eq_two hv hv0
    have hφ6 : InducesTypeSome L (φ (sec4MW i)) 7 1 6 (-1) :=
      (h.data.bdata.type6 (sec4MW i) hv hv0).mp hw6
    obtain ⟨g, hg⟩ := h.tu6 (φ (sec4MW i)) hφL hφ2 hφ6
    have hconj : ∃ g : G, sec4MPt t φ (some i) = g⁻¹ * t * g := ⟨g, hg⟩
    exact (conj_iff_mem_conjClassIn_top (t := t)).mp hconj

theorem Sec4FSetup.conj_cap_A (h : Sec4FSetup t L S z A B φ) :
    conjClassIn ⊤ t ∩ (A : Set G) = Set.range (sec4MPt t φ) := by
  have hpt : sec4MPt t φ none = t := by
    dsimp only [sec4MPt, sec4MV]
    rw [IsPermModuleVia.map_zero h.data.bdata.perm, mul_one]
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxconj, hxA⟩
    have hxcomm : x ∈ centralizer ({t} : Set G) := h.mem_cent_t_of_mem_A hxA
    have hxconj' : ∃ g : G, x = g⁻¹ * t * g := by
      obtain ⟨g, -, hgx⟩ := hxconj
      exact ⟨g⁻¹, by simpa using hgx⟩
    by_cases hxt : x = t
    · exact ⟨none, by rw [hxt, hpt]⟩
    rcases sec4_conj_tri h.inputs.h36 h.inputs.h39 h.inputs.h42 h.inputs.h43 h.inputs.hf43c
      h.inputs.hf214 h.inputs.hin6 h.inputs.hk6 h.ctx hxconj' hxcomm hxt with
      hz | ⟨u', hu'L, hu'2, hu'6, hxu⟩ | hx6
    · exact absurd hz h.not_tz
    · have hu'_tx : u' = t * x := by rw [hxu, ← mul_assoc, h.t_sq, one_mul]
      have hu'_A : u' ∈ A := by
        rw [hu'_tx]
        exact A.mul_mem h.t_mem_A hxA
      have hu'_B : u' ∈ B := by
        rw [← h.data.B_eq]
        exact ⟨hu'_A, hu'L⟩
      obtain ⟨w, hw, hwφ⟩ := (h.data.bdata.perm.2.2.1 u').mp hu'_B
      have hw0 : w ≠ 0 := by
        intro h0
        have h1 : φ w = 1 := by rw [h0, IsPermModuleVia.map_zero h.data.bdata.perm]
        have h2 : u' = 1 := by rw [← hwφ, h1]
        have h3 : orderOf u' = 1 := by rw [h2]; simp
        omega
      have hw6 : vecWeight w = 6 :=
        (h.data.bdata.type6 w hw hw0).mpr (by rw [hwφ]; exact hu'6)
      obtain ⟨i, hwi⟩ := exists_sec4MW_of_weight_six hw hw6
      refine ⟨some i, ?_⟩
      rw [hxu, ← hwφ, hwi]
      dsimp only [sec4MPt, sec4MV]
    · exfalso
      have hx2 : orderOf x = 2 := by
        obtain ⟨g, hg⟩ := hxconj'
        rw [hg, orderOf_conjugate_eq, h.ctx.involution]
      obtain ⟨b, hb, hxb⟩ := h.mem_A_cases hxA
      have hL := h.omega7
      have htc : t ∈ centralizer (L : Set G) := h.t_mem_cent
      rcases hxb with rfl | rfl
      · have hx1 : x ≠ 1 := by
          intro h1
          rw [h1, orderOf_one] at hx2
          exact absurd hx2 (by norm_num)
        exact h.not_outer6_of_mem_B hb hx1 hx6
      · have hb6 : InducesTypeSome L b 7 1 6 1 :=
          (sec4F_type_mul_cent_iff hL htc (Or.inr (Or.inr rfl))).mp hx6
        have hb1 : b ≠ 1 := by
          rintro rfl
          exact hxt (one_mul t)
        exact h.not_outer6_of_mem_B hb hb1 hb6
  · rintro x ⟨p, rfl⟩
    exact ⟨Sec4FSetup.pt_mem_conj h p, sec4MPt_mem_A h.data p⟩

theorem Sec4FSetup.A_eq_closure (h : Sec4FSetup t L S z A B φ) :
    A = Subgroup.closure (Set.range (sec4MPt t φ)) := by
  let Δ : Set G := Set.range (sec4MPt t φ)
  change A = Subgroup.closure Δ
  have ht : sec4MPt t φ none = t := by
    dsimp only [sec4MPt, sec4MV]
    rw [IsPermModuleVia.map_zero h.data.bdata.perm, mul_one]
  have ht_mem : t ∈ Subgroup.closure Δ := by
    rw [← ht]
    exact Subgroup.subset_closure ⟨none, rfl⟩
  have hφw_mem : ∀ v : Fin 7 → ZMod 2, IsEvenVec v → vecWeight v = 6 →
      φ v ∈ Subgroup.closure Δ := by
    intro v hv hv6
    obtain ⟨i, rfl⟩ := exists_sec4MW_of_weight_six hv hv6
    have hmul : sec4MPt t φ none * sec4MPt t φ (some i) = φ (sec4MW i) := by
      simpa [sec4MV] using sec4MPt_mul h.data none (some i)
    rw [← hmul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨none, rfl⟩)
      (Subgroup.subset_closure ⟨some i, rfl⟩)
  have hpos : 0 < Nat.card {v : Fin 7 → ZMod 2 // IsEvenVec v ∧ vecWeight v = 6} := by
    rw [card_evenVec_weight_six]
    norm_num
  obtain ⟨v₀⟩ := Finite.card_pos_iff.mp hpos
  have hB : B ≤ Subgroup.closure Δ := by
    rw [← h.data.bdata.perm.closure_conjClassIn v₀.2.1 (Or.inr (Or.inr v₀.2.2))]
    refine (Subgroup.closure_le (Subgroup.closure Δ)).mpr ?_
    intro x hx
    rw [h.data.bdata.perm.conjClassIn_eq v₀.2.1] at hx
    obtain ⟨w, hw, hwt, rfl⟩ := hx
    exact hφw_mem w hw (hwt.trans v₀.2.2)
  refine le_antisymm ?_ ?_
  · rw [h.data.A_eq]
    exact sup_le hB (Subgroup.zpowers_le.mpr ht_mem)
  · refine (Subgroup.closure_le A).mpr ?_
    rintro x ⟨p, rfl⟩
    exact sec4MPt_mem_A h.data p

theorem Sec4FSetup.exists_pt_of_conj (h : Sec4FSetup t L S z A B φ) {x : G}
    (hx : ∃ g : G, x = g⁻¹ * t * g) (hxA : x ∈ A) : ∃ p : Option (Fin 7), x = sec4MPt t φ p := by
  have hx' : x ∈ conjClassIn ⊤ t := (conj_iff_mem_conjClassIn_top (t := t)).mp hx
  have hx'' : x ∈ Set.range (sec4MPt t φ) := by
    rw [← Sec4FSetup.conj_cap_A h]
    exact ⟨hx', hxA⟩
  obtain ⟨p, hp⟩ := hx''
  exact ⟨p, hp.symm⟩

theorem Sec4FSetup.exists_conj_pt (h : Sec4FSetup t L S z A B φ) (p : Option (Fin 7)) :
    ∃ n ∈ normalizer (A : Set G), sec4MPt t φ p = n * t * n⁻¹ := by
  have hmem : sec4MPt t φ p ∈ conjClassIn ⊤ t ∩ (A : Set G) :=
    ⟨Sec4FSetup.pt_mem_conj h p, sec4MPt_mem_A h.data p⟩
  rw [h.weak] at hmem
  simpa only [conjClassIn, Set.mem_setOf_eq] using hmem

theorem Sec4FSetup.pt_injective (h : Sec4FSetup t L S z A B φ) :
    Function.Injective (sec4MPt t φ) :=
  sec4MPt_injective h.data

end CFSG.OddStandard.SmallF3.Omega
