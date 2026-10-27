module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CCheck6Tau
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.A6CPairK
public import Certificates.Data.A6CMatK

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Certificates.A6C

theorem a6c_facts_of_parts {Γ : Type} [Group Γ] (m : A6CModel 6 Γ)
    (hΓ : Nat.card Γ = 26127360) {rA rCA rT rCT rF : Rec} (h61 : part61 rA rCA = true)
    (h62 : part62 rT rCT = true) (h63 : part63 () = true) (h64 : part64 rA rCT = true)
    (hK1 : partK1 rF = true) (hK2 : partK2 rA rCT rF = true) :
    A6CPairFactsK Γ (fun a => IsConj (A6CElt m (a0M6 ())) a)
      (fun y => IsConj (A6CElt m (refl0M6 ())) y) 40 4 := by
  classical
  haveI : Finite Γ := Nat.finite_of_card_ne_zero (by omega)
  have hrefl : ∀ y ∈ rF.L.toList, A6CSimArr 6 y ∧ IsConj (A6CElt m (refl0M6 ())) (A6CElt m y) :=
    (a6c_classOK_sound m hK1).2.2
  have hinR : ∀ c : Mat, A6CSimArr 6 c → inRefl rF c = true →
      IsConj (A6CElt m (refl0M6 ())) (A6CElt m c) := by
    intro c hc hin
    unfold inRefl at hin
    obtain ⟨z, hz, hzc⟩ := List.any_eq_true.mp hin
    obtain ⟨hzsim, hzconj⟩ := hrefl z hz
    rw [← (a6cElt_eq_iff m hzsim hc).mp hzc]
    exact hzconj
  have h61' := h61
  unfold part61 at h61'
  rw [Bool.and_eq_true] at h61'
  obtain ⟨hcl, hce⟩ := h61'
  have hcomplete : ∀ s, IsConj (A6CElt m (a0M6 ())) s → s ∈ rA.L.toList.map (A6CElt m) :=
    (a6c_complete m hcl hce (by rw [hΓ])).1
  obtain ⟨hg0sim, hg0pow, hg0ne, hrCTnd, hrCTsim, hCmem, hk0len⟩ := a6c_check6_tau m hΓ h62
  have hcent : Nat.card (Subgroup.centralizer ({A6CElt m (g0M6 ())} : Set Γ)) = 40 := by
    have hS : ∀ c : Γ,
        c ∈ (Subgroup.centralizer ({A6CElt m (g0M6 ())} : Set Γ) : Set Γ) ↔
          ∃ y ∈ rCT.L.toList, commP 6 y (g0M6 ()) = true ∧ A6CElt m y = c := by
      intro c
      constructor
      · intro hc
        have hcomm : c * A6CElt m (g0M6 ()) = A6CElt m (g0M6 ()) * c :=
          Subgroup.mem_centralizer_singleton_iff.mp hc
        obtain ⟨y, hyk, hyc⟩ := (hCmem c).mp hcomm
        rw [k0Of] at hyk
        exact ⟨y, (List.mem_filter.mp hyk).1, (List.mem_filter.mp hyk).2, hyc⟩
      · rintro ⟨y, hyL, hp, hyc⟩
        rw [← hyc]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((a6cElt_commP m (hrCTsim y hyL) hg0sim).mp hp)
    have hcnt := a6c_natCard_eq_length_filter m hrCTnd (fun y => commP 6 y (g0M6 ())) hS
    change Nat.card (↑(Subgroup.centralizer ({A6CElt m (g0M6 ())} : Set Γ)) : Set Γ) = 40
    rw [hcnt]
    simpa only [k0Of] using hk0len
  have h63' := h63
  unfold part63 at h63'
  dsimp at h63'
  rw [Bool.and_eq_true] at h63'
  obtain ⟨hsimN, hnmul⟩ := h63'
  have hsimN' : A6CSimArr 6 (nM6 ()) := A6CSimArr.of_simOK hsimN
  have hng0 : A6CElt m (nM6 ()) * A6CElt m (g0M6 ()) =
      A6CElt m (g0M6 ()) * A6CElt m (g0M6 ()) * A6CElt m (nM6 ()) := by
    have heq : A6CElt m (mulN 6 (nM6 ()) (g0M6 ())) =
        A6CElt m (mulN 6 (mulN 6 (g0M6 ()) (g0M6 ())) (nM6 ())) :=
      (a6cElt_eq_iff m (A6CSimArr.mulN hsimN' hg0sim)
        (A6CSimArr.mulN (A6CSimArr.mulN hg0sim hg0sim) hsimN')).mp hnmul
    rwa [a6cElt_mulN m hsimN' hg0sim,
      a6cElt_mulN m (A6CSimArr.mulN hg0sim hg0sim) hsimN',
      a6cElt_mulN m hg0sim hg0sim] at heq
  have hnconj : A6CElt m (nM6 ()) * A6CElt m (g0M6 ()) * (A6CElt m (nM6 ()))⁻¹ =
      (A6CElt m (g0M6 ())) ^ 2 := by
    rw [hng0, pow_two]
    group
  unfold A6CPairFactsK
  refine ⟨A6CElt m (g0M6 ()), A6CElt m (nM6 ()), hg0pow, hg0ne, hnconj, hcent, ?_⟩
  intro a hPa haa ha4 hgag
  obtain ⟨ℓ, hℓL, hℓa⟩ := List.mem_map.mp (hcomplete a hPa)
  have hℓSim : A6CSimArr 6 ℓ := ((a6c_classOK_sound m hcl).2.2 ℓ hℓL).1
  have hrel : relP 6 ℓ (g0M6 ()) = true := by
    rw [a6cElt_relP m hℓSim hg0sim]
    exact ⟨by rw [hℓa]; exact haa, by rw [hℓa]; exact ha4, by rw [hℓa]; exact hgag⟩
  have hS' : ∀ c ∈ (Subgroup.centralizer ({a, A6CElt m (g0M6 ())} : Set Γ) : Set Γ),
      ∃ y ∈ (k0Of 6 (g0M6 ()) rCT).filter (fun c => commP 6 c ℓ), A6CElt m y = c := by
    intro c hc
    have hc' : ∀ h ∈ ({a, A6CElt m (g0M6 ())} : Set Γ), h * c = c * h :=
      Subgroup.mem_centralizer_iff.mp hc
    have hcg0 : c * A6CElt m (g0M6 ()) = A6CElt m (g0M6 ()) * c :=
      (hc' (A6CElt m (g0M6 ())) (by simp)).symm
    have hca : c * a = a * c := (hc' a (by simp)).symm
    obtain ⟨y, hyk, hyc⟩ := (hCmem c).mp hcg0
    have hySim : A6CSimArr 6 y := hrCTsim y (List.mem_of_mem_filter hyk)
    have hyl : commP 6 y ℓ = true := by
      rw [a6cElt_commP m hySim hℓSim, hyc, hℓa]
      exact hca
    exact ⟨y, List.mem_filter.mpr ⟨hyk, hyl⟩, hyc⟩
  have hKsim : ∀ y ∈ (k0Of 6 (g0M6 ()) rCT).filter (fun c => commP 6 c ℓ), A6CSimArr 6 y :=
    fun y hy => hrCTsim y (List.mem_of_mem_filter (List.mem_of_mem_filter hy))
  refine ⟨⟨?_, fun c hc => ?_⟩, ?_⟩
  · have h64' := h64
    unfold part64 at h64'
    dsimp at h64'
    have h64ℓ := List.all_eq_true.mp h64' ℓ hℓL
    rw [hrel, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h64ℓ
    have hbound : ((k0Of 6 (g0M6 ()) rCT).filter (fun c => commP 6 c ℓ)).length ≤ 4 :=
      of_decide_eq_true h64ℓ.1
    exact le_trans (a6c_natCard_le_length_filter m (L := k0Of 6 (g0M6 ()) rCT)
      (fun c => commP 6 c ℓ) (fun c hc => by
        obtain ⟨y, hy, hyc⟩ := hS' c hc
        exact ⟨y, (List.mem_filter.mp hy).1, (List.mem_filter.mp hy).2, hyc⟩)) hbound
  · have h64' := h64
    unfold part64 at h64'
    dsimp at h64'
    have h64ℓ := List.all_eq_true.mp h64' ℓ hℓL
    rw [hrel, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h64ℓ
    obtain ⟨y, hyK, hyc⟩ := hS' c hc
    have hySim := hKsim y hyK
    have hsq : eqP (mulN 6 y y) (idN 6) = true := List.all_eq_true.mp h64ℓ.2 y hyK
    have h1 : A6CElt m y * A6CElt m y = 1 := by
      have h2 := (a6cElt_eq_iff m (A6CSimArr.mulN hySim hySim) (A6CSimArr.idN 6)).mp hsq
      rwa [a6cElt_mulN m hySim hySim, a6cElt_idN m] at h2
    rw [← hyc]
    exact h1
  · intro y₁ hy₁ y₂ hy₂ hne h1 h2
    obtain ⟨z₁, hz₁K, hz₁⟩ := hS' y₁ hy₁
    obtain ⟨z₂, hz₂K, hz₂⟩ := hS' y₂ hy₂
    have hs₁ := hKsim z₁ hz₁K
    have hs₂ := hKsim z₂ hz₂K
    have hK2' := hK2
    unfold partK2 at hK2'
    dsimp at hK2'
    have hK2ℓ := List.all_eq_true.mp hK2' ℓ hℓL
    rw [hrel, Bool.not_true, Bool.false_or] at hK2ℓ
    have hpair := List.all_eq_true.mp (List.all_eq_true.mp hK2ℓ z₁ hz₁K) z₂ hz₂K
    simp only [Bool.or_eq_true] at hpair
    rcases hpair with ((((hp1 | hp2) | hp3) | hp4) | hp5) | hp6
    · exact absurd (by rw [← hz₁, ← a6cElt_idN m]; exact (a6cElt_eq_iff m hs₁
        (A6CSimArr.idN 6)).mp hp1) h1
    · exact absurd (by rw [← hz₂, ← a6cElt_idN m]; exact (a6cElt_eq_iff m hs₂
        (A6CSimArr.idN 6)).mp hp2) h2
    · exact absurd (by rw [← hz₁, ← hz₂]; exact (a6cElt_eq_iff m hs₁ hs₂).mp hp3) hne
    · exact Or.inl (by rw [← hz₁]; exact hinR z₁ hs₁ hp4)
    · exact Or.inr (Or.inl (by rw [← hz₂]; exact hinR z₂ hs₂ hp5))
    · refine Or.inr (Or.inr ?_)
      rw [← hz₁, ← hz₂, ← a6cElt_mulN m hs₁ hs₂]
      exact hinR _ (A6CSimArr.mulN hs₁ hs₂) hp6

end CFSG.OddStandard.SmallF3.Omega
