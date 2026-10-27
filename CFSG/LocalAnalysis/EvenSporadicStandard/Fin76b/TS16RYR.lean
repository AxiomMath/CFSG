module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RN
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16R7
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RNIso
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYL3
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYR0
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYFive2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RYProd

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

namespace OuterS16Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
  (c : OuterS16Ctx G L z t T E Q x B β S)

include c

theorem s16Gen_inv_mul {s : G} (hS : S16Gen S s z t) : S16Gen S s (s⁻¹ * z) t := by
  have hzs' : z * s⁻¹ * z⁻¹ = s := by
    calc z * s⁻¹ * z⁻¹ = (z * s * z⁻¹)⁻¹ := by group
      _ = s := by rw [hS.hzs]; group
  refine ⟨hS.hs, S.mul_mem (S.inv_mem hS.hs) hS.hzS, hS.hs8, hS.hs4, ?_, ?_, hS.hord, ?_, ?_⟩
  · calc s⁻¹ * z * (s⁻¹ * z) = s⁻¹ * (z * s⁻¹ * z⁻¹) * (z * z) := by group
      _ = 1 := by rw [hzs', hS.hz2]; group
  · calc s⁻¹ * z * s * (s⁻¹ * z)⁻¹ = s⁻¹ * (z * s * z⁻¹) * s := by group
      _ = s⁻¹ := by rw [hS.hzs]; group
  · intro hmem
    apply hS.hzns
    have : z = s * (s⁻¹ * z) := by group
    rw [this]
    exact mul_mem (mem_zpowers s) hmem
  · intro y hy
    obtain ⟨i, j, rfl⟩ := hS.hgen y hy
    obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' j
    · exact ⟨i, 0, by rw [z_pow_two_mul hS.hz2 r, pow_zero]⟩
    · refine ⟨i + 1, 1, ?_⟩
      rw [z_pow_two_mul_add_one hS.hz2 r, pow_one, pow_succ]
      group

theorem exists_R {s σ v ξ : G} (hS : S16Gen S s z t) (hD : S16LData G L z t β E σ v ξ)
    (hσs : σ * s * σ⁻¹ = s ^ 5) :
    ∃ R : Subgroup G, IsPGroup 2 R ∧ R ≤ centralizer ({ξ} : Set G) ∧ ξ ∈ R ∧
      ∀ X : Finset G, (↑X : Set G) ⊆ ↑R → X.card ≤ 4 →
        Subgroup.closure (X : Set G) ⊔ Subgroup.zpowers ξ ≠ R := by
  classical
  have hcfg := c.hyp.outerE.cfg
  have hz2 : z * z = 1 := hcfg.z_sq
  have ht2 : t * t = 1 := hcfg.t_sq
  have ht1 : t ≠ 1 := hcfg.t_ne
  obtain ⟨C, hCle, hCξ, htC, hξC, hCcard, hCsq, hCcomm⟩ := hD.rank5
  set A : Subgroup G := L ⊓ centralizer ({t} : Set G) with hA
  have hS' : S16Gen S s (s⁻¹ * z) t := c.s16Gen_inv_mul hS
  set z' : G := s⁻¹ * z with hz'
  set D' : Subgroup G := Dsub s z' with hD'
  have hD'card : Nat.card ↥D' = 8 :=
    card_Dsub hS.hs hS'.hzS hS.hs8 hS'.hz2 hS'.hzs hS.hord hS'.hzns hS'.hgen c.card16
  have hD'S : D' ≤ S := Dsub_le hS.hs hS'.hzS
  have htD' : t ∈ D' := t_mem_Dsub hS.hs4
  have hD'z : z ∈ D' := by
    have : z = s * z' := by rw [hz']; group
    rw [this]
    exact b_mem_Dsub
  have hσ2 := hD.σ_sq
  have hσt := hD.σ_t
  have hσt' : σ * t = t * σ := by
    calc σ * t = (σ * t * σ⁻¹) * σ := by group
      _ = t * σ := by rw [hσt]
  have hσit : σ⁻¹ * t = t * σ⁻¹ := by
    calc σ⁻¹ * t = σ⁻¹ * (t * σ) * σ⁻¹ := by group
      _ = σ⁻¹ * (σ * t) * σ⁻¹ := by rw [hσt']
      _ = t * σ⁻¹ := by group
  have hσA : ∀ a ∈ A, σ * a * σ⁻¹ ∈ A := by
    intro a ha
    refine ⟨hD.σ_L a ha.1, ?_⟩
    show σ * a * σ⁻¹ ∈ centralizer ({t} : Set G)
    rw [mem_centralizer_singleton_iff]
    have hat : a * t = t * a := mem_centralizer_singleton_iff.1 ha.2
    calc σ * a * σ⁻¹ * t = σ * a * (σ⁻¹ * t) := by group
      _ = σ * a * (t * σ⁻¹) := by rw [hσit]
      _ = σ * (a * t) * σ⁻¹ := by group
      _ = σ * (t * a) * σ⁻¹ := by rw [hat]
      _ = (σ * t) * a * σ⁻¹ := by group
      _ = (t * σ) * a * σ⁻¹ := by rw [hσt']
      _ = t * (σ * a * σ⁻¹) := by group
  have hAD : ∀ a ∈ A, ∀ d ∈ D', d * a = a * d := fun a ha d hd =>
    mem_centralizer_iff.1 (c.EB_le_centS ha) d (hD'S hd)
  have hσD : ∀ d ∈ D', σ * d = d * σ := by
    have hgen : D' ≤ centralizer ({σ} : Set G) := by
      rw [hD', Dsub, Subgroup.closure_le]
      rintro y (rfl | rfl)
      · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        have h1 : σ * (s * s) * σ⁻¹ = s * s := by
          calc σ * (s * s) * σ⁻¹ = (σ * s * σ⁻¹) * (σ * s * σ⁻¹) := by group
            _ = s ^ 5 * s ^ 5 := by rw [hσs]
            _ = s ^ 8 * (s * s) := by group
            _ = s * s := by rw [hS.hs8, one_mul]
        calc s * s * σ = (σ * (s * s) * σ⁻¹) * σ := by rw [h1]
          _ = σ * (s * s) := by group
      · rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
        have hsz : s * z' = z := by rw [hz']; group
        rw [hsz]
        exact hD.σ_z.symm
    exact fun d hd => (mem_centralizer_singleton_iff.1 (hgen hd)).symm
  have hCmem : ∀ x ∈ C, ∃ a ∈ A, x = a ∨ x = a * σ := fun x hx =>
    exists_mul_of_mem_sup_sigma' hσ2 hσA (hCle hx)
  have hDC : ∀ d ∈ D', ∀ x ∈ C, d * x = x * d := by
    intro d hd x hx
    obtain ⟨a, ha, hxa | hxa⟩ := hCmem x hx
    · rw [hxa]; exact hAD a ha d hd
    · rw [hxa]
      calc d * (a * σ) = (d * a) * σ := by group
        _ = (a * d) * σ := by rw [hAD a ha d hd]
        _ = a * (d * σ) := by group
        _ = a * (σ * d) := by rw [hσD d hd]
        _ = a * σ * d := by group
  have hDinter : ∀ y ∈ D', y ∈ C → y = 1 ∨ y = t := by
    intro y hyD hyC
    have hyS : y ∈ S := hD'S hyD
    obtain ⟨a, ha, hya | hya⟩ := hCmem y hyC
    · rw [hya] at hyS ⊢
      exact c.hyp.wFacts.cent a ha.1 fun e he => (mem_centralizer_iff.1 (c.SC hyS) e he).symm
    · rw [hya] at hyS
      exfalso
      have hxz : a * σ * z = z * (a * σ) := by
        calc a * σ * z = a * (σ * z) := by group
          _ = a * (z * σ) := by rw [hD.σ_z]
          _ = (a * z) * σ := by group
          _ = (z * a) * σ := by rw [hcfg.z_comm_of_mem_A ha.1]
          _ = z * (a * σ) := by group
      have hmem : a * σ ∈ L ⊔ zpowers z ∨ True := Or.inr trivial
      have hcases := c.hyp.centZ (a * σ) (c.SC hyS) hxz
      apply hD.σ_notL
      have hσeq : σ = a⁻¹ * (a * σ) := by group
      rw [hσeq]
      refine mul_mem (mem_sup_left (inv_mem ha.1)) ?_
      rcases hcases with h | h | h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_sup_right (mem_zpowers z)
      · rw [h]; exact mem_sup_left hcfg.t_mem_A
      · rw [h]; exact mul_mem (mem_sup_left hcfg.t_mem_A) (mem_sup_right (mem_zpowers z))
  have hDCle : D' ≤ centralizer (C : Set G) := fun d hd =>
    mem_centralizer_iff.2 fun x hx => (hDC d hd x hx).symm
  have hRcard : Nat.card ↥(D' ⊔ C) = 128 := by
    have := card_sup_commuting_two hDCle hDinter ht2 ht1 htD' htC
    rw [hD'card, hCcard] at this
    omega
  set R : Subgroup G := D' ⊔ C with hR
  have hRt : R ≤ centralizer ({t} : Set G) := by
    refine sup_le (fun d hd => ?_) (fun x hx => ?_)
    · exact mem_centralizer_singleton_iff.2 (c.t_comm_S d (hD'S hd))
    · have : A ⊔ zpowers σ ≤ centralizer ({t} : Set G) :=
        sup_le inf_le_right (zpowers_le.2 (mem_centralizer_singleton_iff.2 hσt'))
      exact this (hCle hx)
  have hξA : ξ ∈ A := ⟨hD.ξ_L, mem_centralizer_singleton_iff.2 hD.ξ_t⟩
  have hRξ : R ≤ centralizer ({ξ} : Set G) := by
    refine sup_le (fun d hd => ?_) hCξ
    exact mem_centralizer_singleton_iff.2 (hAD ξ hξA d hd)
  have hξR : ξ ∈ R := mem_sup_right hξC
  have htR : t ∈ R := mem_sup_left htD'
  set F : Subgroup G := closure ({t, ξ} : Set G) with hF
  have htF : t ∈ F := subset_closure (by simp)
  have hξF : ξ ∈ F := subset_closure (by simp)
  have hF4 : Nat.card ↥F = 4 :=
    card_closure_pair ht2 hD.ξ_sq hD.ξ_t.symm ht1 hD.ξ_ne_one (fun h => hD.ξ_ne_t h.symm)
  have hFR : F ≤ R := by
    rw [hF, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact htR
    · exact hξR
  have hFc : ∀ x ∈ F, ∀ r ∈ R, r * x = x * r := by
    have hFle : F ≤ centralizer (R : Set G) := by
      rw [hF, Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact mem_centralizer_iff.2 fun r hr => mem_centralizer_singleton_iff.1 (hRt hr)
      · exact mem_centralizer_iff.2 fun r hr => mem_centralizer_singleton_iff.1 (hRξ hr)
    exact fun x hx r hr => mem_centralizer_iff.1 (hFle hx) r hr
  have hquadF : ∀ y : G, (y = 1 ∨ y = t ∨ y = ξ ∨ y = t * ξ) → y ∈ F := by
    intro y hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact htF
    · exact hξF
    · exact mul_mem htF hξF
  obtain ⟨φ, -, -⟩ := exists_dihedral4_equiv (a := s * s) (b := s * z')
    (by rw [← pow_two, ← pow_mul]; exact hS.hs8) (b_sq hS'.hz2 hS'.hzs)
    (b_inv_a hS'.hz2 hS'.hzs) hD'card
  have hD'sq : ∀ d ∈ D', d * d ∈ F := by
    intro d hd
    rcases Dsub_parity hS'.hz2 hS'.hzs hS.hs8 d hd with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have : s ^ (2 * i) * s ^ (2 * i) = t ^ i := by
        rw [← pow_add, ← hS.hs4, ← pow_mul]
        congr 1
        ring
      rw [this]
      exact pow_mem htF i
    · have h1 := sz_mul_sz hS'.hz2 hS'.hzs hS.hs8 (2 * i + 1) (2 * i + 1)
      have h2 : s ^ (2 * i + 1 + 7 * (2 * i + 1)) = 1 := by
        rw [show 2 * i + 1 + 7 * (2 * i + 1) = 8 * (2 * i + 1) by ring, pow_mul, hS.hs8, one_pow]
      rw [h1, h2]
      exact one_mem _
  have hD'cm : ∀ d ∈ D', ∀ d' ∈ D', d * d' * d⁻¹ * d'⁻¹ ∈ F := by
    intro d hd d' hd'
    rcases dihedral_comm htD' ht1 (fun y hy => c.t_comm_S y (hD'S hy)) φ d hd d' hd' with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact htF
  have hCsq' : ∀ y ∈ C, y * y ∈ F := fun y hy => hquadF _ (hCsq y hy)
  have hCcomm' : ∀ y ∈ C, ∀ y' ∈ C, y * y' * y⁻¹ * y'⁻¹ ∈ F :=
    fun y hy y' hy' => hquadF _ (hCcomm y hy y' hy')
  obtain ⟨hsq, hcomm⟩ := sq_comm_sup hDCle hD'sq hCsq' hD'cm hCcomm'
  refine ⟨R, IsPGroup.of_card (n := 7) (by rw [hRcard]; norm_num), hRξ, hξR, ?_⟩
  exact needsFive_of_quot hξR hξF hFR hFc hsq hcomm (by rw [hRcard, hF4])

end OuterS16Ctx

end CFSG.EvenSporadicStandard.Fin76b
