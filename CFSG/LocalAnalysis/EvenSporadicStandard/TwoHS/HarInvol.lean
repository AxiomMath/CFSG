module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarCentre
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.HarRLevel

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

section Tables

theorem hsRows_permOK : ∀ r ∈ hsRows, permOK 3850 r.rep = true := by
  intro r hr
  exact (hs_rows_facts r hr).1

end Tables

section Words

variable
  {E : Type} [Group E]
  (M : CoverModel E)

theorem CoverModel.z1E_eq : M.z1E = wordVal M.uE [3, 3, 3, 3] := by
  apply M.ρ_inj
  exact rep_unique M.rep_z1E (M.rep_tU _ (by decide))

theorem CoverModel.y2E_eq : M.y2E = wordVal M.uE [1, 2, 1, 2, 3] := by
  apply M.ρ_inj
  exact rep_unique M.rep_y2E (M.rep_tU _ (by decide))

theorem harLiftOK_parts :
    conjOK 3850 hsSift (harConj 0) (hsCentTbl 5) (tUX [3, 3, 3, 3]) = true ∧
    conjOK 3850 hsSift (harConj 1) (hsCentTbl 12) (tUX [1, 2, 1, 2, 3]) = true ∧
    tblEq 11200 (compT 11200 (tU [1, 2, 1, 2, 3]) (tU [1, 2, 1, 2, 3])) harC0 = true := by
  have hl := harLiftOK_true
  simp only [harLiftOK, Bool.and_eq_true] at hl
  exact ⟨hl.1.1.1.2, hl.1.1.2, hl.1.2⟩

theorem CoverModel.y2E_sq : M.y2E * M.y2E = M.tE := by
  apply M.ρ_inj
  rw [map_mul]
  exact (tblEq_iff_eq (Rep.compT M.rep_y2E M.rep_y2E) M.rep_tE).1 harLiftOK_parts.2.2

theorem CoverMaps.eq_or_eq_mul_tE (M : CoverMaps E) (hZ : Nat.card (center E) = 2) {a b : E}
    (h : M.π a = M.π b) : b = a ∨ b = a * M.tE := by
  have hker : a⁻¹ * b ∈ center E := by
    rw [← M.ker_pi_eq, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  rcases (M.mem_center_iff hZ).1 hker with h1 | h1
  · left
    exact (inv_mul_eq_one.1 h1).symm
  · right
    rw [← h1]
    group

theorem CoverMaps.exists_conj_mul_tE (M : CoverMaps E) (hZ : Nat.card (center E) = 2) {x u : E}
    {c g t₁ : Equiv.Perm (Fin 3850)} (hc : c ∈ hsP) (hg : g ∈ hsP)
    (hxc : (M.π x : Equiv.Perm (Fin 3850)) = c * t₁ * c⁻¹)
    (hug : (M.π u : Equiv.Perm (Fin 3850)) = g * t₁ * g⁻¹) :
    ∃ e : E, e * x * e⁻¹ = u ∨ e * x * e⁻¹ = u * M.tE := by
  obtain ⟨e, he⟩ := M.π_surj ⟨g * c⁻¹, hsP.mul_mem hg (hsP.inv_mem hc)⟩
  have he' : (M.π e : Equiv.Perm (Fin 3850)) = g * c⁻¹ := congrArg Subtype.val he
  have h1 : M.π u = M.π (e * x * e⁻¹) := by
    apply Subtype.ext
    rw [map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [he', hxc, hug]
    group
  refine ⟨e, ?_⟩
  rcases M.eq_or_eq_mul_tE hZ h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

end Words

section Classification

variable
  {E : Type} [Group E] (M : CoverModel E)

theorem CoverModel.exists_conj_of_involution (hZ : Nat.card (center E) = 2) {u : E}
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1) (hut : u ≠ M.tE) :
    ∃ e : E, e * u * e⁻¹ = M.z1E ∨ e * u * e⁻¹ = M.tE * M.z1E := by
  have hsift : ∀ (T : Table) (g : Equiv.Perm (Fin 3850)), Rep 3850 T g →
      (hsSift T = true ↔ g ∈ hsP) := fun T g hT => hs_groupData.sift T g hT
  have hπu1 : M.π u ≠ 1 := fun h => by
    rcases (M.mem_center_iff hZ).1 ((M.π_ker u).1 h) with h1 | h1
    exacts [hu1 h1, hut h1]
  have hsq : (M.π u : Equiv.Perm (Fin 3850)) * (M.π u : Equiv.Perm (Fin 3850)) = 1 := by
    have : M.π u * M.π u = 1 := by rw [← map_mul, ← pow_two, hu2, map_one]
    exact congrArg Subtype.val this
  have hord : orderOf (M.π u : Equiv.Perm (Fin 3850)) = 2 :=
    orderOf_eq_prime (by rwa [pow_two]) (fun h => hπu1 (Subtype.ext h))
  have hR : (M.π u : Equiv.Perm (Fin 3850)) ∈ hsR := (le_sup_left : hsP ≤ hsR) (M.π u).2
  obtain ⟨-, -, -, hrows, hcover, -⟩ := hs_involution_centralizers
  obtain ⟨r, hr, g, hg, hrg⟩ := hcover _ hR hord
  have hmem : tp 3850 r.rep ∈ hsP := by
    have h1 : tp 3850 r.rep = g⁻¹ * (M.π u : Equiv.Perm (Fin 3850)) * g := by rw [hrg]; group
    rw [h1]
    exact hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hg) (M.π u).2) hg
  have hrouter : r.outer = false := by
    cases hro : r.outer
    · rfl
    · exact absurd hmem ((hrows r hr).2.2.1.1 hro)
  have hrepr : Rep 3850 r.rep (tp 3850 r.rep) := rep_tp (hsRows_permOK r hr)
  have htcentral : ∀ y : E, M.tE * y = y * M.tE := fun y =>
    ((Subgroup.mem_center_iff.1 M.tE_mem_center) y).symm
  have htt : M.tE * M.tE = 1 := by rw [← pow_two]; exact M.tE_sq
  have hcases : (r.rep = hsCentTbl 5 ∨ r.rep = hsCentTbl 12) ∨ r.outer = true := by
    simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with h | h | h | h
    · exact Or.inl (Or.inl (by simp [h]))
    · exact Or.inl (Or.inr (by simp [h]))
    · exact Or.inr (by simp [h])
    · exact Or.inr (by simp [h])
  rcases hcases with (hrep | hrep) | hout
  ·
    rw [hrep] at hrg hrepr
    obtain ⟨c, hcP, hc⟩ := conjOK_spec hsift hrepr harLiftOK_parts.1
    have hz1 : Rep 3850 (tUX [3, 3, 3, 3]) (M.π M.z1E : Equiv.Perm (Fin 3850)) := by
      rw [M.z1E_eq]
      exact M.rep_tUX _ (by decide)
    obtain ⟨e, he⟩ := M.toCoverMaps.exists_conj_mul_tE hZ hcP hg (rep_unique hz1 hc) hrg
    refine ⟨e⁻¹, ?_⟩
    rcases he with h | h
    · left
      rw [← h]
      group
    · right
      have h1 : (e⁻¹ * u * e⁻¹⁻¹) * M.tE = M.z1E := by
        calc (e⁻¹ * u * e⁻¹⁻¹) * M.tE = e⁻¹ * u * (e * M.tE) := by group
          _ = e⁻¹ * u * (M.tE * e) := by rw [htcentral e]
          _ = e⁻¹ * (u * M.tE) * e := by group
          _ = e⁻¹ * (e * M.z1E * e⁻¹) * e := by rw [h]
          _ = M.z1E := by group
      have h2 : e⁻¹ * u * e⁻¹⁻¹ = M.z1E * M.tE := by
        rw [← h1, mul_assoc, mul_assoc, htt]
        group
      rw [h2]
      exact (htcentral M.z1E).symm
  ·
    exfalso
    rw [hrep] at hrg hrepr
    obtain ⟨c, hcP, hc⟩ := conjOK_spec hsift hrepr harLiftOK_parts.2.1
    have hy2 : Rep 3850 (tUX [1, 2, 1, 2, 3]) (M.π M.y2E : Equiv.Perm (Fin 3850)) := by
      rw [M.y2E_eq]
      exact M.rep_tUX _ (by decide)
    obtain ⟨e, he⟩ := M.toCoverMaps.exists_conj_mul_tE hZ hcP hg (rep_unique hy2 hc) hrg
    have hsqe : (e * M.y2E * e⁻¹) * (e * M.y2E * e⁻¹) = M.tE := by
      calc (e * M.y2E * e⁻¹) * (e * M.y2E * e⁻¹) = e * (M.y2E * M.y2E) * e⁻¹ := by group
        _ = e * M.tE * e⁻¹ := by rw [M.y2E_sq]
        _ = e * (M.tE * e⁻¹) := by group
        _ = e * (e⁻¹ * M.tE) := by rw [htcentral e⁻¹]
        _ = M.tE := by group
    have hu : u * u = 1 := by rw [← pow_two]; exact hu2
    rcases he with h | h
    · rw [h, hu] at hsqe
      exact M.tE_ne_one hsqe.symm
    · rw [h] at hsqe
      have : u * M.tE * (u * M.tE) = (u * u) * (M.tE * M.tE) := by
        calc u * M.tE * (u * M.tE) = u * (M.tE * u) * M.tE := by group
          _ = u * (u * M.tE) * M.tE := by rw [htcentral u]
          _ = (u * u) * (M.tE * M.tE) := by group
      rw [this, hu, htt, mul_one] at hsqe
      exact M.tE_ne_one hsqe.symm
  · rw [hout] at hrouter
    exact absurd hrouter (by decide)

end Classification

end CFSG.EvenSporadicStandard.TwoHS
