module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbQ13c1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbTSyl

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

private def pcj (g : G) (H : Subgroup G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

private theorem mem_pcj {g x : G} {H : Subgroup G} :
    x ∈ pcj g H ↔ g⁻¹ * x * g ∈ H := by
  simp only [pcj, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    convert hy using 1
    group
  · intro hx
    exact ⟨g⁻¹ * x * g, hx, by group⟩

private theorem mem_pcj_inv_iff {g x : G} {H : Subgroup G} :
    x ∈ H ↔ g⁻¹ * x * g ∈ pcj g⁻¹ H := by
  rw [mem_pcj]
  rw [show (g⁻¹)⁻¹ * (g⁻¹ * x * g) * g⁻¹ = x by group]

private theorem card_pcj (g : G) (H : Subgroup G) : Nat.card (pcj g H) = Nat.card H := by
  simpa only [pcj] using Subgroup.card_map_of_injective (K := H) (MulAut.conj g).injective

private theorem isPGroup_pcj {p : ℕ} {g : G} {H : Subgroup G} (h : IsPGroup p H) :
    IsPGroup p (pcj g H) := by
  have e : ↥H ≃* ↥(pcj g H) :=
    Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact h.of_equiv e

private theorem smul_conj_eq_pcj (g : G) (P : Subgroup G) : MulAut.conj g • P = pcj g P := rfl

private theorem exists_pcj_of_isSylowIn {P P' H : Subgroup G} (hP : IsSylowIn 2 P H)
    (hP' : IsSylowIn 2 P' H) : ∃ c ∈ H, pcj c P = P' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 (P.subgroupOf H) :=
    hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm
  have hP'2 : IsPGroup 2 (P'.subgroupOf H) :=
    hP'.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP'.1).symm
  have hPidx : ¬ 2 ∣ (P.subgroupOf H).index := by
    simpa only [Subgroup.relIndex] using hP.2.2
  have hP'idx : ¬ 2 ∣ (P'.subgroupOf H).index := by
    simpa only [Subgroup.relIndex] using hP'.2.2
  haveI : Finite (Sylow 2 ↥H) := Sylow.finite_of_finiteIndex (hP2.toSylow hPidx)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥H) (hP2.toSylow hPidx) (hP'2.toSylow hP'idx)
  have hg' : MulAut.conj g • (P.subgroupOf H) = P'.subgroupOf H := by
    have h := congrArg (fun S : Sylow 2 ↥H => (S : Subgroup ↥H)) hg
    rw [Sylow.smul_def, Sylow.pointwise_smul_def] at h
    simpa only [IsPGroup.toSylow_coe] using h
  refine ⟨(g : G), g.2, ?_⟩
  have hsub : (pcj (g : G) P).subgroupOf H = P'.subgroupOf H := by
    rw [← smul_conj_eq_pcj, ← Subgroup.conj_smul_subgroupOf hP.1 g]
    exact hg'
  have hle : pcj (g : G) P ≤ H := by
    rw [← smul_conj_eq_pcj]
    exact Subgroup.conj_smul_le_of_le hP.1 g
  have hinf : pcj (g : G) P ⊓ H = P' ⊓ H := Subgroup.subgroupOf_inj.mp hsub
  rw [inf_eq_left.mpr hle, inf_eq_left.mpr hP'.1] at hinf
  exact hinf

private theorem conj_inv_mem_invCent {g₀ d : G} (hg₀ : g₀ * t * g₀⁻¹ = t * lam)
    (hd : d ∈ centralizer ({t * lam} : Set G)) : g₀⁻¹ * d * g₀ ∈ invCent t := by
  rw [S4A.mem_invCent_iff]
  have hcomm : d * (t * lam) = (t * lam) * d :=
    Subgroup.mem_centralizer_singleton_iff.mp hd
  have h1 : g₀ * t = (t * lam) * g₀ := by rw [← hg₀]; group
  have h2 : g₀⁻¹ * (t * lam) * g₀ = t := by rw [← hg₀]; group
  calc (g₀⁻¹ * d * g₀) * t = g₀⁻¹ * d * (g₀ * t) := by group
    _ = g₀⁻¹ * d * ((t * lam) * g₀) := by rw [h1]
    _ = g₀⁻¹ * (d * (t * lam)) * g₀ := by group
    _ = g₀⁻¹ * ((t * lam) * d) * g₀ := by rw [hcomm]
    _ = (g₀⁻¹ * (t * lam) * g₀) * (g₀⁻¹ * d * g₀) := by group
    _ = t * (g₀⁻¹ * d * g₀) := by rw [h2]

theorem q13c_sylowIn_conj {P P' H : Subgroup G} (hP : IsSylowIn 2 P H) (hP' : IsSylowIn 2 P' H) :
    ∃ c ∈ H, ∀ x : G, x ∈ P' ↔ c⁻¹ * x * c ∈ P := by
  obtain ⟨c, hcH, hc⟩ := exists_pcj_of_isSylowIn hP hP'
  refine ⟨c, hcH, fun x => ?_⟩
  rw [← hc, mem_pcj]

theorem q13c_card_le (h : Q13Om t L S x₁ x₂ lam rho tau om) {D : Subgroup G}
    (hD2 : IsPGroup 2 D) (hDc : D ≤ centralizer ({t * lam} : Set G)) : Nat.card D ≤ 2 ^ 7 := by
  obtain ⟨g₀, hg₀⟩ := q13c_exists_conj h
  set D' : Subgroup G := pcj g₀⁻¹ D with hD'def
  have hD'2 : IsPGroup 2 D' := by rw [hD'def]; exact isPGroup_pcj hD2
  have hD'le : D' ≤ invCent t := by
    intro x hx
    rw [hD'def, mem_pcj] at hx
    have hx' : g₀ * x * g₀⁻¹ ∈ D := by convert hx using 1; group
    have := conj_inv_mem_invCent (t := t) (lam := lam) hg₀ (hDc hx')
    convert this using 1
    group
  have hD'card : Nat.card D' = Nat.card D := by rw [hD'def]; exact card_pcj _ _
  obtain ⟨P, hPsylow, hD'P⟩ := exists_isSylowIn_of_le hD'le hD'2
  have hS : IsSylowIn 2 S (invCent t) :=
    ⟨h.c11.le_invCent, h.c11.isPGroup, h.c11.relIndex_odd⟩
  obtain ⟨c, _hcH, hcP⟩ := exists_pcj_of_isSylowIn hS hPsylow
  have hPcard : Nat.card P = 2 ^ 7 := by
    rw [← hcP, card_pcj, Ctx4.card_S_seven h.c11.toCtx10.toCtx4]
  calc Nat.card D = Nat.card D' := hD'card.symm
    _ ≤ Nat.card P := Subgroup.card_le_of_le hD'P
    _ = 2 ^ 7 := hPcard

theorem q13c_sylow_conj (h : Q13Om t L S x₁ x₂ lam rho tau om) {D : Subgroup G}
    (hD2 : IsPGroup 2 D) (hDc : D ≤ centralizer ({t * lam} : Set G))
    (hD : Nat.card D = 2 ^ 7) :
    ∃ g : G, g * t * g⁻¹ = t * lam ∧ ∀ x : G, x ∈ D ↔ g⁻¹ * x * g ∈ S := by
  obtain ⟨g₀, hg₀⟩ := q13c_exists_conj h
  set D' : Subgroup G := pcj g₀⁻¹ D with hD'def
  have hD'2 : IsPGroup 2 D' := by rw [hD'def]; exact isPGroup_pcj hD2
  have hD'le : D' ≤ invCent t := by
    intro x hx
    rw [hD'def, mem_pcj] at hx
    have hx' : g₀ * x * g₀⁻¹ ∈ D := by convert hx using 1; group
    have := conj_inv_mem_invCent (t := t) (lam := lam) hg₀ (hDc hx')
    convert this using 1
    group
  have hD'card : Nat.card D' = Nat.card D := by rw [hD'def]; exact card_pcj _ _
  obtain ⟨P, hPsylow, hD'P⟩ := exists_isSylowIn_of_le hD'le hD'2
  have hS : IsSylowIn 2 S (invCent t) :=
    ⟨h.c11.le_invCent, h.c11.isPGroup, h.c11.relIndex_odd⟩
  obtain ⟨c, hcH, hcP⟩ := exists_pcj_of_isSylowIn hS hPsylow
  have hPcard : Nat.card P = 2 ^ 7 := by
    rw [← hcP, card_pcj, Ctx4.card_S_seven h.c11.toCtx10.toCtx4]
  have hD'eqP : D' = P := by
    refine Subgroup.eq_of_le_of_card_ge hD'P ?_
    rw [hPcard, hD'card, hD]
  refine ⟨g₀ * c, ?_, fun x => ?_⟩
  · have hct : c * t = t * c := S4A.mem_invCent_iff.mp hcH
    have hcH' : c * t * c⁻¹ = t := by rw [hct]; group
    calc g₀ * c * t * (g₀ * c)⁻¹ = g₀ * (c * t * c⁻¹) * g₀⁻¹ := by group
      _ = g₀ * t * g₀⁻¹ := by rw [hcH']
      _ = t * lam := hg₀
  · rw [show (g₀ * c)⁻¹ * x * (g₀ * c) = c⁻¹ * (g₀⁻¹ * x * g₀) * c by group]
    rw [← mem_pcj, hcP, ← hD'eqP, hD'def]
    exact mem_pcj_inv_iff (g := g₀) (x := x) (H := D)

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
