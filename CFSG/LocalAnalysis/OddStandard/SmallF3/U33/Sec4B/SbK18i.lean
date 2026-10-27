module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18h

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

theorem k18_E8_card (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    Nat.card ↥(closure ({t, tau, lam} : Set G)) = 8 := by
  have hrel := ctx13_relations hc
  have ht2 : t ^ 2 = 1 := hrel.1
  have ht2m : t * t = 1 := by simpa [pow_two] using ht2
  have ht1 : t ≠ 1 := hrel.2.1
  have htau2 : tau ^ 2 = 1 := hrel.2.2.2.1
  have htau_not : tau ∉ zpowers t := hrel.2.2.2.2.1
  have ht_tau : t * tau = tau * t := hrel.2.2.2.2.2.1
  have hlam2 : lam ^ 2 = 1 := (ctx13_lam_facts hc).1
  have hlam1 : lam ≠ 1 := fun h =>
    l18_lam_not_mem_OK hc (by rw [h]; exact Subgroup.one_mem _)
  have hlam_ord : orderOf lam = 2 := orderOf_eq_prime hlam2 hlam1
  have hcard_lam : Nat.card (zpowers lam) = 2 := by rw [Nat.card_zpowers, hlam_ord]
  have hEeq : closure ({t, tau, lam} : Set G) =
      closure ({t, tau} : Set G) ⊔ zpowers lam := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro g (hg : g ∈ ({t, tau, lam} : Set G))
      rcases hg with hg | hg | hg
      · rw [hg]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · rw [hg]; exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
      · rw [hg]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)
    · refine sup_le ?_ ?_
      · refine Subgroup.closure_mono ?_
        intro x hx
        rcases hx with rfl | rfl <;> simp
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have htT : t ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
  have homT : om ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
  have htauT : tau ∈ closure ({t, om} : Set G) := by
    have h1 : om * t * om⁻¹ ∈ closure ({t, om} : Set G) :=
      mul_mem (mul_mem homT htT) (inv_mem homT)
    have h2 : t * (om * t * om⁻¹) ∈ closure ({t, om} : Set G) :=
      mul_mem htT h1
    have heq : t * (om * t * om⁻¹) = tau := by
      rw [hrel.2.2.2.2.2.2, ← mul_assoc, ht2m, one_mul]
    rwa [heq] at h2
  have hH_le_T : closure ({t, tau} : Set G) ≤ closure ({t, om} : Set G) := by
    rw [Subgroup.closure_le]
    rintro x (hx : x ∈ ({t, tau} : Set G))
    rcases hx with rfl | rfl
    · exact htT
    · exact htauT
  have hnorm : ∀ k ∈ zpowers lam, ∀ h ∈ closure ({t, tau} : Set G),
      k * h * k⁻¹ ∈ closure ({t, tau} : Set G) := by
    intro k hk h hh
    have hcomm : k * h = h * k := by
      have hx : h * lam = lam * h := (ctx13_lam_facts hc).2 h (hH_le_T hh)
      have hle : zpowers lam ≤ Subgroup.centralizer ({h} : Set G) :=
        Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hx.symm)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hHOK : closure ({t, tau} : Set G) ≤ ctxOK t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    rintro x (hx : x ∈ ({t, tau} : Set G))
    rcases hx with rfl | rfl
    · exact (l18_tau_om_mem_OK hc).1
    · exact (l18_tau_om_mem_OK hc).2.1
  have hHK : closure ({t, tau} : Set G) ⊓ zpowers lam = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxH, hxlam⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_zpowers_iff] at hxlam
    obtain ⟨n, rfl⟩ := hxlam
    have hpar : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by
      simpa using Int.emod_two_eq_zero_or_one n
    rcases hpar with hn | hn
    · rw [zpow_eq_zpow_emod' (x := lam) (n := 2) n hlam2, hn]; simp
    · rw [zpow_eq_zpow_emod' (x := lam) (n := 2) n hlam2, hn] at hxH
      simp only [zpow_one] at hxH
      exact absurd (hHOK hxH) (l18_lam_not_mem_OK hc)
  have hcard := card_sup_eq_mul (H := closure ({t, tau} : Set G))
    (K := zpowers lam) hnorm hHK
  rw [card_closure_pair ht2 ht1 htau2 ht_tau htau_not, hcard_lam] at hcard
  rw [hEeq, hcard]

theorem k18_E8_le (hc : Ctx18S t L S x₁ x₂ lam rho tau om 𝒮) :
    closure ({t, tau, lam} : Set G) ≤ 𝒮 ⊓ centralizer ({lam * t} : Set G) := by
  have hrel := ctx13_relations hc.toCtx13
  have htc : lam * t = t * lam := (l17_lam_comm hc.toCtx13).1
  have hlamtau : lam * tau = tau * lam := (l17_lam_comm hc.toCtx13).2.1
  have ht_tau : t * tau = tau * t := hrel.2.2.2.2.2.1
  have ht2 : t * t = 1 := by simpa [pow_two] using hrel.1
  have hlam2 : lam * lam = 1 := by
    simpa [pow_two] using (ctx13_lam_facts hc.toCtx13).1
  have hut : (lam * t) * t = t * (lam * t) := by
    have h1 : (lam * t) * t = lam := by rw [mul_assoc, ht2, mul_one]
    have h2 : t * (lam * t) = lam := by
      rw [← mul_assoc, ← htc, mul_assoc, ht2, mul_one]
    exact h1.trans h2.symm
  have hu_tau : (lam * t) * tau = tau * (lam * t) := by
    rw [mul_assoc, ht_tau, ← mul_assoc, hlamtau, mul_assoc]
  have hu_lam : (lam * t) * lam = lam * (lam * t) := by
    have hA : (lam * t) * lam = t := by
      calc (lam * t) * lam = lam * (t * lam) := by rw [mul_assoc]
        _ = lam * (lam * t) := by rw [← htc]
        _ = (lam * lam) * t := by rw [mul_assoc]
        _ = t := by rw [hlam2, one_mul]
    have hB : lam * (lam * t) = t := by rw [← mul_assoc, hlam2, one_mul]
    exact hA.trans hB.symm
  rw [Subgroup.closure_le]
  rintro g (hg : g ∈ ({t, tau, lam} : Set G))
  rcases hg with hg | hg | hg
  · rw [hg]; refine Subgroup.mem_inf.mpr ⟨(l18_T_le_sylow hc).1, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hut)
  · rw [hg]; refine Subgroup.mem_inf.mpr ⟨(l18_T_le_sylow hc).2.1, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hu_tau)
  · rw [hg]; refine Subgroup.mem_inf.mpr ⟨(l18_T_le_sylow hc).2.2.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hu_lam)

theorem k18_E8_inf_Xi (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) :
    closure ({t, tau, lam} : Set G) ⊓ ctxXi t tau x₁ x₂ rho = ⊥ := by
  have hc13 := hc.toCtx13
  have hrel := ctx13_relations hc13
  have ht2 : t * t = 1 := by simpa [pow_two] using hrel.1
  have hlam2 : lam ^ 2 = 1 := (ctx13_lam_facts hc13).1
  have htT : t ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
  have homT : om ∈ closure ({t, om} : Set G) := Subgroup.subset_closure (by simp)
  have htauT : tau ∈ closure ({t, om} : Set G) := by
    have h1 : om * t * om⁻¹ ∈ closure ({t, om} : Set G) :=
      mul_mem (mul_mem homT htT) (inv_mem homT)
    have h2 : t * (om * t * om⁻¹) ∈ closure ({t, om} : Set G) :=
      mul_mem htT h1
    have heq : t * (om * t * om⁻¹) = tau := by
      rw [hrel.2.2.2.2.2.2, ← mul_assoc, ht2, one_mul]
    rwa [heq] at h2
  have hE_le : closure ({t, tau, lam} : Set G) ≤
      closure ({t, om} : Set G) ⊔ zpowers lam := by
    rw [Subgroup.closure_le]
    rintro g (hg : g ∈ ({t, tau, lam} : Set G))
    rcases hg with hg | hg | hg
    · rw [hg]; exact Subgroup.mem_sup_left htT
    · rw [hg]; exact Subgroup.mem_sup_left htauT
    · rw [hg]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers lam)
  have hnorm : ∀ k ∈ zpowers lam, ∀ h ∈ closure ({t, om} : Set G),
      k * h * k⁻¹ ∈ closure ({t, om} : Set G) := by
    intro k hk h hh
    have hx : h * lam = lam * h := (ctx13_lam_facts hc13).2 h hh
    have hcomm : k * h = h * k := by
      have hle : zpowers lam ≤ Subgroup.centralizer ({h} : Set G) :=
        Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hx.symm)
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hk)
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hHOK : closure ({t, om} : Set G) ≤ ctxOK t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    rintro g (hg : g ∈ ({t, om} : Set G))
    rcases hg with rfl | rfl
    · exact (l18_tau_om_mem_OK hc13).1
    · exact (l18_tau_om_mem_OK hc13).2.2
  refine le_antisymm ?_ bot_le
  intro e he
  rw [Subgroup.mem_bot]
  obtain ⟨heE, heXi⟩ := Subgroup.mem_inf.mp he
  have heSup : e ∈ closure ({t, om} : Set G) ⊔ zpowers lam := hE_le heE
  obtain ⟨h', hh', k, hk, heq⟩ := (mem_sup_iff_of_normalizes hnorm).mp heSup
  rw [Subgroup.mem_zpowers_iff] at hk
  obtain ⟨n, rfl⟩ := hk
  have hpar : n % ((2 : ℕ) : ℤ) = 0 ∨ n % ((2 : ℕ) : ℤ) = 1 := by
    simpa using Int.emod_two_eq_zero_or_one n
  rcases hpar with hn | hn
  · have hk1 : lam ^ n = 1 := by
      rw [zpow_eq_zpow_emod' (x := lam) (n := 2) n hlam2, hn]; simp
    rw [hk1, mul_one] at heq
    have hh'Xi : h' ∈ ctxXi t tau x₁ x₂ rho := by rw [← heq]; exact heXi
    have hmem : h' ∈ ctxXi t tau x₁ x₂ rho ⊓ closure ({t, om} : Set G) :=
      ⟨hh'Xi, hh'⟩
    have hbot : h' ∈ (⊥ : Subgroup G) := by rwa [k18_Xi_cap_tom hc] at hmem
    rw [Subgroup.mem_bot.mp hbot] at heq
    exact heq
  · have hklam : lam ^ n = lam := by
      rw [zpow_eq_zpow_emod' (x := lam) (n := 2) n hlam2, hn]; simp
    rw [hklam] at heq
    have hlamOK : lam ∈ ctxOK t tau x₁ x₂ rho := by
      have hlt : h'⁻¹ * e = lam := by rw [heq]; group
      rw [← hlt]
      exact mul_mem (inv_mem (hHOK hh')) (l18_Xi_le_OK hc13 heXi)
    exact absurd hlamOK (l18_lam_not_mem_OK hc13)

theorem k18_card_Csylow_u (hc : Ctx18 t L S x₁ x₂ lam rho tau om 𝒮) {V' : Subgroup G}
    {v₁ v₂ : G} (hV : Ctx13V t tau x₁ x₂ lam rho om V' v₁ v₂) :
    2 ^ 7 ≤ Nat.card ↥(𝒮 ⊓ centralizer ({lam * t} : Set G)) := by
  have hc13 := hc.toCtx13
  have hc18S := hc.toCtx18S
  have hEle := k18_E8_le hc18S
  have hcardE : Nat.card (closure ({t, tau, lam} : Set G)) = 8 := k18_E8_card hc13
  have hcardD : 16 ≤ Nat.card ↥(ctxXi t tau x₁ x₂ rho ⊓
      centralizer ({lam * t} : Set G)) := k18_card_CXi_u hc hV
  have hDE : (ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) ⊓
      closure ({t, tau, lam} : Set G) = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    obtain ⟨hxΞC, hxE⟩ := Subgroup.mem_inf.mp hx
    have hxΞ : x ∈ ctxXi t tau x₁ x₂ rho := hxΞC.1
    have hmem : x ∈ closure ({t, tau, lam} : Set G) ⊓ ctxXi t tau x₁ x₂ rho :=
      ⟨hxE, hxΞ⟩
    have hbot : x ∈ (⊥ : Subgroup G) := by rwa [k18_E8_inf_Xi hc] at hmem
    exact hbot
  have hnorm : ∀ k ∈ closure ({t, tau, lam} : Set G),
      ∀ h ∈ ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G),
        k * h * k⁻¹ ∈ ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G) := by
    intro k hk h hh
    obtain ⟨hkS, hkcent⟩ := Subgroup.mem_inf.mp (hEle hk)
    obtain ⟨hhXi, hhcent⟩ := Subgroup.mem_inf.mp hh
    have hkK : k ∈ ctxK t tau x₁ x₂ rho := hc.sylow.1 hkS
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (l18_Xi_normal hc13).2 k hkK h hhXi
    · have hcu : Commute (lam * t) k :=
        (Subgroup.mem_centralizer_iff.mp hkcent) (lam * t) (by simp)
      have hch : Commute (lam * t) h :=
        (Subgroup.mem_centralizer_iff.mp hhcent) (lam * t) (by simp)
      have hcomm : Commute (lam * t) (k * h * k⁻¹) :=
        (hcu.mul_right hch).mul_right hcu.inv_right
      exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hcomm)
  have hcard : Nat.card ↥((ctxXi t tau x₁ x₂ rho ⊓
      centralizer ({lam * t} : Set G)) ⊔ closure ({t, tau, lam} : Set G)) =
      Nat.card ↥(ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) *
        Nat.card ↥(closure ({t, tau, lam} : Set G)) :=
    card_sup_eq_mul hnorm hDE
  have hle : (ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) ⊔
      closure ({t, tau, lam} : Set G) ≤ 𝒮 ⊓ centralizer ({lam * t} : Set G) := by
    refine sup_le ?_ ?_
    · exact le_inf (inf_le_left.trans (l18_Xi_le_sylow hc18S)) inf_le_right
    · exact hEle
  calc 2 ^ 7 = 16 * 8 := by norm_num
    _ ≤ Nat.card ↥(ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) *
          Nat.card ↥(closure ({t, tau, lam} : Set G)) :=
        Nat.mul_le_mul hcardD (le_of_eq hcardE.symm)
    _ = Nat.card ↥((ctxXi t tau x₁ x₂ rho ⊓ centralizer ({lam * t} : Set G)) ⊔
          closure ({t, tau, lam} : Set G)) := hcard.symm
    _ ≤ Nat.card ↥(𝒮 ⊓ centralizer ({lam * t} : Set G)) :=
        Subgroup.card_le_of_le hle

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
