module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S7EM02

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight

section Core

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}

theorem commutator_mem_oddCore_of_system (hsys : Hat2A7.A7SystemMod Λ) {M : Subgroup Y}
    (hM : M ∈ Λ) {u : Y} (huM : u ∈ M) (hu : ∀ a ∈ M, a * u = u * a) (y : Y) :
    u * y * u⁻¹ * y⁻¹ ∈ classicalInvolutionOddCore Y := by
  obtain ⟨D⟩ := hsys
  set π := QuotientGroup.mk' (classicalInvolutionOddCore Y) with hπ
  have hmem : M.map π ∈ Hat2A7.oddQuotientFamily2A7 Λ := ⟨M, hM, rfl⟩
  rw [D.members] at hmem
  obtain ⟨i, hi⟩ := hmem
  have huc : π u ∈ D.comp i := by
    rw [hi]
    exact ⟨u, huM, rfl⟩
  have hcomm : ∀ q ∈ (⨆ k, D.comp k : Subgroup _), π u * q = q * π u := by
    intro q hq
    induction hq using Subgroup.iSup_induction' with
    | hp k q hq =>
      by_cases hki : k = i
      · subst hki
        rw [hi] at hq
        obtain ⟨a, ha, rfl⟩ := hq
        show π u * π a = π a * π u
        rw [← map_mul, ← map_mul, ← hu a ha]
      · exact D.commute i k (Ne.symm hki) _ huc q hq
    | h1 => simp
    | hmul x y _ _ hx hy =>
      rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  have hyq : π y ∈ (⨆ k, D.comp k : Subgroup _) := by
    rw [D.generate]
    trivial
  have h1 := hcomm _ hyq
  apply (QuotientGroup.eq_one_iff _).mp
  show π (u * y * u⁻¹ * y⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]
  group

theorem e189_second_alt_core {n : ℕ} (hB : Hat2A7.CITBelow2A7 n) (hY : Nat.card Y < n)
    (hΛ : HypOmegaGen Λ) (hcl : ∀ L ∈ Λ, ∃ u : Y, Hat2A7.IsClassical2A7 ⊤ L u)
    (hgen : (⨆ L ∈ Λ, L) = ⊤) {K J : Subgroup Y} (hK : K ∈ Λ) (hJ : J ∈ Λ) {z t : Y}
    (hz : IsUniqueInvolution K z) (ht : IsUniqueInvolution J t) (hzt : z * t = t * z)
    (hne : conjSub t K ≠ K) :
    ∃ x : Y, ∃ M' ∈ twinSet Λ (conjSub x K), M' ≠ conjSub x K ∧ ∃ R₁ R₂ : Subgroup Y,
      IsSylow2In R₁ (conjSub x K) ∧ IsSylow2In R₂ M' ∧ Commutes R₁ R₂ ∧
        ∀ w ∈ R₁ ⊔ R₂, w * (z * t) = (z * t) * w := by
  have hsys : Hat2A7.A7SystemMod Λ :=
    hB Y hY Λ ⟨⟨K, hK⟩, hΛ.conjInvariant, hgen, hcl⟩
  have hNn : (classicalInvolutionOddCore Y).Normal := inferInstance
  have hNodd : Odd (Nat.card (classicalInvolutionOddCore Y)) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hzN := commutator_mem_oddCore_of_system hsys hK hz.mem
    (fun a ha => (hz.commute_of_mem ha).symm)
  have htN := commutator_mem_oddCore_of_system hsys hJ ht.mem
    (fun a ha => (ht.commute_of_mem ha).symm)
  obtain ⟨a, hadef⟩ : ∃ a : Y, a = z * t := ⟨_, rfl⟩
  have hz2 : z * z = 1 := hz.sq
  have ht2 : t * t = 1 := ht.sq
  have ha2 : a * a = 1 := by
    rw [hadef]
    calc z * t * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [hzt]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [hz2, ht2, mul_one]
  have haN : ∀ y : Y, a * y * a⁻¹ * y⁻¹ ∈ classicalInvolutionOddCore Y := by
    intro y
    have e : a * y * a⁻¹ * y⁻¹ =
        (z * (t * y * t⁻¹ * y⁻¹) * z⁻¹) * (z * y * z⁻¹ * y⁻¹) := by
      rw [hadef]
      group
    rw [e]
    exact (classicalInvolutionOddCore Y).mul_mem (hNn.conj_mem _ (htN y) z) (hzN y)
  have hzt1 : z ≠ t := by
    intro h
    apply hne
    rw [← h]
    exact conjSub_eq_self_of_mem hz.mem
  have ha1 : a ≠ 1 := by
    intro h
    apply hzt1
    have h' : z * t = 1 := hadef ▸ h
    exact (eq_inv_of_mul_eq_one_left h').trans (inv_eq_of_mul_eq_one_right ht2)
  have hK't : conjSub t K ∈ Λ := hΛ.conjInvariant t K hK
  have hz' : IsUniqueInvolution (conjSub t K) z := by
    have h1 := hz.conj t
    have e : t * z * t⁻¹ = z := by rw [← hzt]; group
    rwa [e] at h1
  obtain ⟨R₁, hR₁, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := Y)) (bot_le : ⊥ ≤ K)
  have hKN : K ≤ Subgroup.normalizer ((conjSub t K : Subgroup Y) : Set Y) :=
    Sec6Gen.le_normalizer_of_twin hΛ hK hK't hne.symm hz hz'
  obtain ⟨R₂, hR₂, hR₂fix⟩ := Asc77.exists_sylow_normalized hR₁.2.1 (hR₁.1.trans hKN)
  have hR₁n : R₁ ≤ Subgroup.normalizer (R₂ : Set Y) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hR₂fix r hr)
  have hV2 : IsPGroup 2 ↥(R₁ ⊔ R₂) := hR₁.2.1.to_sup_of_normal_right' hR₂.2.1 hR₁n
  have hcomm : Commutes R₁ R₂ :=
    Sec6Gen.commutes_of_twin_of_isPGroup hΛ hK hK't hne.symm hz hz' hR₁.1 hR₂.1 hV2
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hconjz : ∀ g c : Y, conjSub g (Subgroup.zpowers c) = Subgroup.zpowers (g * c * g⁻¹) := by
    intro g c
    simp [conjSub, MonoidHom.map_zpowers, MulAut.conj_apply]
  obtain ⟨m, hmN, hVm⟩ := exists_conj_normalizer_of_perm (N := classicalInvolutionOddCore Y)
    hNodd (Subgroup.zpowers a) hV2 (fun v _ => by
      have hc : QuotientGroup.mk' (classicalInvolutionOddCore Y) a =
          QuotientGroup.mk' (classicalInvolutionOddCore Y) (v * a * v⁻¹) := by
        show (a : Y ⧸ classicalInvolutionOddCore Y) =
          ((v * a * v⁻¹ : Y) : Y ⧸ classicalInvolutionOddCore Y)
        apply QuotientGroup.eq.mpr
        have e : a⁻¹ * (v * a * v⁻¹) = a * v * a⁻¹ * v⁻¹ := by
          rw [hainv]
          group
        rw [e]
        exact haN v
      have hvsq : (v * a * v⁻¹) * (v * a * v⁻¹) = 1 := by
        calc (v * a * v⁻¹) * (v * a * v⁻¹) = v * (a * a) * v⁻¹ := by group
          _ = 1 := by rw [ha2]; group
      obtain ⟨n, hn, hne'⟩ := exists_conj_eq_of_map_eq hNodd ha2 hvsq hc
      refine ⟨n⁻¹, (classicalInvolutionOddCore Y).inv_mem hn, ?_⟩
      rw [hconjz, hconjz]
      congr 1
      calc v * a * v⁻¹ = n⁻¹ * (n * (v * a * v⁻¹) * n⁻¹) * n := by group
        _ = n⁻¹ * a * (n⁻¹)⁻¹ := by rw [hne', inv_inv])
  have hcent : ∀ v ∈ R₁ ⊔ R₂, v * (m * a * m⁻¹) = (m * a * m⁻¹) * v := by
    intro v hv
    have h1 := hVm hv
    have h2 : v * (m * a * m⁻¹) * v⁻¹ ∈ conjSub m (Subgroup.zpowers a) := by
      rw [Subgroup.mem_normalizer_iff] at h1
      exact (h1 _).mp ⟨a, Subgroup.mem_zpowers a, by simp [MulAut.conj_apply]⟩
    rw [hconjz] at h2
    have ha'2 : orderOf (m * a * m⁻¹) = 2 := by
      rw [orderOf_conj_eq]
      exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha1
    rcases T7A.eq_one_or_eq_of_mem_zpowers ha'2 h2 with h3 | h3
    · exfalso
      exact ha1 (conj_eq_one_iff.mp (conj_eq_one_iff.mp h3))
    · calc v * (m * a * m⁻¹) = (v * (m * a * m⁻¹) * v⁻¹) * v := by group
        _ = (m * a * m⁻¹) * v := by rw [h3]
  refine ⟨m⁻¹, conjSub m⁻¹ (conjSub t K), ?_, ?_, conjSub m⁻¹ R₁, conjSub m⁻¹ R₂, ?_, ?_, ?_, ?_⟩
  · exact ⟨hΛ.conjInvariant _ _ hK't, _, hz.conj m⁻¹, hz'.conj m⁻¹⟩
  · intro h
    exact hne (conjSub_injective m⁻¹ h)
  · exact hR₁.conj m⁻¹
  · exact hR₂.conj m⁻¹
  · exact hcomm.conjSub m⁻¹
  · intro w hw
    rw [← T7A.conjSub_sup_eq, mem_conjSub_iff, inv_inv] at hw
    have h1 := hcent _ hw
    rw [← hadef]
    have e1 : m * w * m⁻¹ * (m * a * m⁻¹) = m * (w * a) * m⁻¹ := by group
    have e2 : m * a * m⁻¹ * (m * w * m⁻¹) = m * (a * w) * m⁻¹ := by group
    rw [e1, e2] at h1
    have h2 : w * a = a * w := mul_left_cancel (mul_right_cancel h1)
    exact h2

end Core

end CFSG.ClassicalInvolution.Hat2A7S

namespace CFSG.ClassicalInvolution.Hat2A7E.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

theorem e189Sect_proved : E189Sect := by
  intro n hB Y _ _ hY Λ hΛ hgen _ K hK J hJ z t hz ht hzt hne
  right
  have hcl : ∀ L ∈ Λ, ∃ u : Y, Hat2A7.IsClassical2A7 ⊤ L u := fun L hL => by
    obtain ⟨u, hu⟩ := hΛ.classical L hL
    exact ⟨u, hu.to2A7⟩
  exact Hat2A7S.e189_second_alt_core hB hY hΛ.toGen hcl hgen hK hJ hz ht hzt hne

end CFSG.ClassicalInvolution.Hat2A7E.Asc77
