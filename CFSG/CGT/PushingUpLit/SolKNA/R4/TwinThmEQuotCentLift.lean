module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEQuotCentConj
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQuotCentPf

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open scoped commutatorElement

namespace ThmE

section QuotCentLift


variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {N : Subgroup G} [N.Normal]
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem quotCent_inf_sylow_eq {S : Sylow 2 G} {M R' : Subgroup G} (hR' : IsSylow2In R' M)
    (hR'S : R' ≤ (S : Subgroup G)) : M ⊓ (S : Subgroup G) = R' :=
  hR'.eq_of_le (S.isPGroup'.to_le inf_le_right) inf_le_left (le_inf hR'.1 hR'S)

theorem MinCex.quotCent_sup_inf_eq_bot (c : MinCex r Ω K S R W H) (hN2 : IsPGroup 2 ↥N)
    (hNc : N ≤ Subgroup.center G) (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥) {M J R₁ R₂ : Subgroup G}
    (hM : M ∈ dstarComp Ω K) (hJ : J ∈ KPerp Ω M) (hR₁ : R₁ ∈ RSet Ω) (hR₁M : R₁ ≤ M)
    (hR₂ : R₂ ∈ RSet Ω) (hR₂J : R₂ ≤ J) (hcomm : Commutes R₁ R₂ ∨ R₂ = R₁) :
    (R₁ ⊔ R₂) ⊓ N = ⊥ := by
  by_contra hne
  have hΩ := c.stand.hyp
  have hMΩ : M ∈ Ω := quotCent_mem_of_mem_dstarComp c.stand.mem hM
  obtain ⟨e, he, he1, he2⟩ := AscE186.exists_involution_of_ne_bot (hN2.to_le inf_le_right) hne
  have hcen : ∀ g : G, g * e = e * g := Subgroup.mem_center_iff.mp (hNc he.2)
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hMΩ
  rcases hJ with hJM | hJn
  ·
    have heM : e ∈ M ⊓ N := ⟨(sup_le hR₁M (hJM ▸ hR₂J)) he.1, he.2⟩
    rw [hmeet M hMΩ, Subgroup.mem_bot] at heM
    exact he1 heM
  · have hJΩ : J ∈ Ω := hJn.1
    obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJΩ
    have hR₁syl : IsSylow2In R₁ M := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hMΩ hR₁ hR₁M
    have hR₂syl : IsSylow2In R₂ J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hR₂ hR₂J
    have hcm : Commutes R₁ R₂ := by
      rcases hcomm with h | h
      · exact h
      · exfalso
        have h2 := Sec6Gen.card_le_two_of_le_inf hΩ hMΩ hJΩ hJn.2.1.symm hR₁syl.2.1 hR₁M
          (h ▸ hR₂J)
        have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR₁
        omega
    rcases quotCent_central_involution_cases hΩ hMΩ hJΩ hR₁syl hR₂syl hcm hz ht he.1 he1 he2
      hcen with h | h | h
    · have h' : e ∈ M ⊓ N := ⟨h ▸ hz.mem, he.2⟩
      rw [hmeet M hMΩ, Subgroup.mem_bot] at h'
      exact he1 h'
    · have h' : e ∈ J ⊓ N := ⟨h ▸ ht.mem, he.2⟩
      rw [hmeet J hJΩ, Subgroup.mem_bot] at h'
      exact he1 h'
    · subst h
      have hC := c.quotCent_centralizer_le_mul hM hJn hz ht he1 he2
      apply c.proper
      rw [eq_top_iff]
      intro g _
      exact hC (Subgroup.mem_centralizer_singleton_iff.mpr (hcen g))

theorem MinCex.quotCent_exists_lift (c : MinCex r Ω K S R W H)
    (hN2 : IsPGroup 2 ↥N) (hNc : N ≤ Subgroup.center G) (hmeet : ∀ J ∈ Ω, J ⊓ N = ⊥)
    {M J R₁ R₂ : Subgroup G} (hMΩ : M ∈ Ω) (hMW : M ⊓ W ∈ USet Ω) (hJ : J ∈ KPerp Ω M)
    (hR₁ : R₁ ∈ RSet Ω) (hR₁M : R₁ ≤ M) (hR₁S : R₁ ≤ (S : Subgroup G))
    (hR₂ : R₂ ∈ RSet Ω) (hR₂J : R₂ ≤ J) (hR₂S : R₂ ≤ (S : Subgroup G))
    (hcomm : Commutes R₁ R₂ ∨ R₂ = R₁) {y w : G} (hy : y ∈ R₁ ⊔ R₂) (hw : w ∈ W)
    (hyw : QuotientGroup.mk' N y = QuotientGroup.mk' N w) (hy1 : QuotientGroup.mk' N y ≠ 1)
    (hy2 : QuotientGroup.mk' N y * QuotientGroup.mk' N y = 1) :
    y ≠ 1 ∧ y * y = 1 ∧ y ∈ W ∧ Subgroup.centralizer ({y} : Set G) ≤ H ∧
      ∃ u ∈ M, orderOf u = 4 ∧ u * y = y * u := by
  have hΩ := c.stand.hyp
  obtain ⟨hWmem, hWS, hWn⟩ := c.stand.hW
  have hK := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have habel := habel_of_WSet hΩ hWmem
  have hKW : K ⊓ W ∈ USet Ω := inf_W_mem_USet' hΩ hWmem hWS hK hRR hRK hRS
  have hMsg : M ∈ dstarComp Ω K := mem_dstarComp_of_inf_W hΩ hWmem hK hMΩ hKW hMW
  have hJΩ : J ∈ Ω := by
    rcases hJ with rfl | hJn
    · exact hMΩ
    · exact hJn.1
  have hR₁syl : IsSylow2In R₁ M := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hMΩ hR₁ hR₁M
  have hR₂syl : IsSylow2In R₂ J := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hR₂ hR₂J
  have hbot : (R₁ ⊔ R₂) ⊓ N = ⊥ :=
    c.quotCent_sup_inf_eq_bot hN2 hNc hmeet hMsg hJ hR₁ hR₁M hR₂ hR₂J hcomm
  obtain ⟨-, -, -, -, -, -, hUc, -, h4⟩ := hΩ.exists_data_of_mem_USet hMW
  have hU2 : IsPGroup 2 ↥(M ⊓ W) := hΩ.isPGroup_of_mem_USet hMW
  obtain ⟨u, huMW, hu4⟩ := exists_orderOf_eq_four_of_isPGroup_of_isCyclic hU2 hUc h4
  have hn' : w⁻¹ * y ∈ N := by
    have h0 : QuotientGroup.mk' N (w⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hyw, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h0
  have hy' : y = w * (w⁻¹ * y) := by group
  have hycomm : ∀ v ∈ W, y * v = v * y := by
    intro v hv
    calc y * v = w * ((w⁻¹ * y) * v) := by rw [hy']; group
      _ = w * (v * (w⁻¹ * y)) := by rw [← Subgroup.mem_center_iff.mp (hNc hn') v]
      _ = (w * v) * (w⁻¹ * y) := by group
      _ = (v * w) * (w⁻¹ * y) := by rw [habel w hw v hv]
      _ = v * (w * (w⁻¹ * y)) := by group
      _ = v * y := by rw [← hy']
  have hy1' : y ≠ 1 := fun h => hy1 (by rw [h, map_one])
  have hyyN : y * y ∈ N := by
    have h0 : QuotientGroup.mk' N (y * y) = 1 := by rw [map_mul]; exact hy2
    exact (QuotientGroup.eq_one_iff _).mp h0
  have hyy : y * y = 1 := by
    have h : y * y ∈ (R₁ ⊔ R₂) ⊓ N := ⟨(R₁ ⊔ R₂).mul_mem hy hy, hyyN⟩
    rwa [hbot, Subgroup.mem_bot] at h
  have hyW : y ∈ W := by
    rcases hcomm with hcm | hR₂R₁
    · obtain ⟨a, ha, b, hb, hyab⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hcm hy
      have hUR₁ : M ⊓ W ≤ R₁ := fun x hx => by
        have : x ∈ M ⊓ (S : Subgroup G) := ⟨hx.1, hWS hx.2⟩
        rwa [quotCent_inf_sylow_eq hR₁syl hR₁S] at this
      have hacomm : ∀ x ∈ M ⊓ W, a * x = x * a := by
        intro x hx
        have h1 := hycomm x hx.2
        have h2 : x * b = b * x := hcm x (hUR₁ hx) b hb
        rw [← hyab] at h1
        have h3 : a * x * b = x * a * b := by
          calc a * x * b = a * (x * b) := by group
            _ = a * (b * x) := by rw [h2]
            _ = a * b * x := by group
            _ = x * (a * b) := h1
            _ = x * a * b := by group
        exact mul_right_cancel h3
      have haU : a ∈ M ⊓ W :=
        quotCent_mem_inf_W_of_commutes hΩ hMΩ hR₁syl hR₁S hWS hMW ha hacomm
      have hJW : J ⊓ W ∈ USet Ω := inf_W_mem_USet' hΩ hWmem hWS hJΩ hR₂ hR₂J hR₂S
      have hUR₂ : J ⊓ W ≤ R₂ := fun x hx => by
        have : x ∈ J ⊓ (S : Subgroup G) := ⟨hx.1, hWS hx.2⟩
        rwa [quotCent_inf_sylow_eq hR₂syl hR₂S] at this
      have hbcomm : ∀ x ∈ J ⊓ W, b * x = x * b := by
        intro x hx
        have h1 := hycomm x hx.2
        have h2 : a * x = x * a := hcm a ha x (hUR₂ hx)
        rw [← hyab] at h1
        have h3 : a * (b * x) = a * (x * b) := by
          calc a * (b * x) = a * b * x := by group
            _ = x * (a * b) := h1
            _ = x * a * b := by group
            _ = a * x * b := by rw [h2]
            _ = a * (x * b) := by group
        exact mul_left_cancel h3
      have hbU : b ∈ J ⊓ W :=
        quotCent_mem_inf_W_of_commutes hΩ hJΩ hR₂syl hR₂S hWS hJW hb hbcomm
      rw [← hyab]
      exact W.mul_mem haU.2 hbU.2
    · have hyR₁ : y ∈ R₁ := by
        rw [hR₂R₁, sup_idem] at hy
        exact hy
      exact (quotCent_mem_inf_W_of_commutes hΩ hMΩ hR₁syl hR₁S hWS hMW hyR₁
        fun x hx => hycomm x hx.2).2
  have hCy : Subgroup.centralizer ({y} : Set G) ≤ H :=
    c.hyp.cent M hMΩ hMW J hJ R₁ R₂ hR₁ hR₁M hR₁S hR₂ hR₂J hR₂S hcomm y hy hyW hy1' hyy
  exact ⟨hy1', hyy, hyW, hCy, u, huMW.1, hu4, (hycomm u huMW.2).symm⟩

end QuotCentLift

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
