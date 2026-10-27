module

public import CFSG.LocalAnalysis.OddStandard.ONanFusAB

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

@[expose] def wDE : AlpE := ⟨0, 1, 2, 3⟩

set_option maxRecDepth 100000 in
theorem wDE_cent : ∀ g ∈ genCentE 0, g * wDE = wDE * g := by decide +kernel

theorem wDE_sq : wDE * wDE = zc := by decide

theorem wDE_comm_rep : wDE * invE 3 = invE 3 * wDE := by decide

set_option maxRecDepth 100000 in
theorem cent_genCent_one_sq : ∀ w : AlpE, (∀ g ∈ genCentE 1, g * w = w * g) →
    w * w = 1 ∨ w * w = zc := by
  decide +kernel

theorem card_rep_le (j : Fin 7) (hj : 3 ≤ j.val) :
    (![512, 256, 128, 32, 16, 32, 32] : Fin 7 → ℕ) j ≤ 32 := by
  revert j
  decide

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem card_cent_of_inClass {i : Fin 7} {x : G} (hx : D.InClass i x) :
    Nat.card (alpP v1 v2 v3 s t ⊓ centralizer ({x} : Set G) : Subgroup G) =
      (![512, 256, 128, 32, 16, 32, 32] : Fin 7 → ℕ) i := by
  obtain ⟨c, hc, rfl⟩ := hx
  rw [← AlpEmb.card_centralizer_invRep D.E D.hF i]
  have h : alpP v1 v2 v3 s t ⊓ centralizer ({c⁻¹ * invRep v1 v2 v3 s t i * c} : Set G) =
      (alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t i} : Set G)).map
        (MulAut.conj c⁻¹).toMonoidHom := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyP, hyC⟩ := Subgroup.mem_inf.1 hy
      refine ⟨c * y * c⁻¹, Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hc hyP) (inv_mem hc), ?_⟩, ?_⟩
      · rw [mem_centralizer_singleton_iff] at hyC ⊢
        calc c * y * c⁻¹ * invRep v1 v2 v3 s t i =
            c * (y * (c⁻¹ * invRep v1 v2 v3 s t i * c)) * c⁻¹ := by group
          _ = c * ((c⁻¹ * invRep v1 v2 v3 s t i * c) * y) * c⁻¹ := by rw [hyC]
          _ = invRep v1 v2 v3 s t i * (c * y * c⁻¹) := by group
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
    · rintro ⟨y0, hy0, rfl⟩
      obtain ⟨hy0P, hy0C⟩ := Subgroup.mem_inf.1 hy0
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hc) hy0P) hc, ?_⟩
      rw [mem_centralizer_singleton_iff] at hy0C ⊢
      calc c⁻¹ * y0 * c * (c⁻¹ * invRep v1 v2 v3 s t i * c) =
          c⁻¹ * (y0 * invRep v1 v2 v3 s t i) * c := by group
        _ = c⁻¹ * (invRep v1 v2 v3 s t i * y0) * c := by rw [hy0C]
        _ = c⁻¹ * invRep v1 v2 v3 s t i * c * (c⁻¹ * y0 * c) := by group
  rw [h, card_map_of_injective (MulAut.conj c⁻¹).injective]

theorem isSylowOf_rep (i : Fin 7)
    (h : ∀ j : Fin 7, D.Fus i j → (![512, 256, 128, 32, 16, 32, 32] : Fin 7 → ℕ) j ≤
      (![512, 256, 128, 32, 16, 32, 32] : Fin 7 → ℕ) i) :
    IsSylowOf 2 (alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t i} : Set G))
      (centralizer ({invRep v1 v2 v3 s t i} : Set G)) := by
  refine isSylowOf_of_card_le D.isSylowOf_P (AlpEmb.invRep_mem D.E i) fun g hg => ?_
  have hx2 : g⁻¹ * invRep v1 v2 v3 s t i * g * (g⁻¹ * invRep v1 v2 v3 s t i * g) = 1 := by
    calc g⁻¹ * invRep v1 v2 v3 s t i * g * (g⁻¹ * invRep v1 v2 v3 s t i * g) =
        g⁻¹ * (invRep v1 v2 v3 s t i * invRep v1 v2 v3 s t i) * g := by group
      _ = 1 := by rw [D.rep_sq i]; group
  have hx1 : g⁻¹ * invRep v1 v2 v3 s t i * g ≠ 1 := by
    intro h1
    apply D.rep_ne_one i
    calc invRep v1 v2 v3 s t i = g * (g⁻¹ * invRep v1 v2 v3 s t i * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨j, hj⟩ := D.exists_inClass hg hx2 hx1
  rw [D.card_cent_of_inClass hj, AlpEmb.card_centralizer_invRep D.E D.hF i]
  exact h j (D.inClass_fus (D.inClass_rep i) hj g rfl)

theorem centCount_ne_zero {k : Fin 3} {j : Fin 7} {x : G}
    (hx : x ∈ alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t (![3, 5, 6] k)} : Set G))
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hj : D.InClass j x) : centCount k j ≠ 0 := by
  rw [← AlpEmb.card_involutions_genCent D.E D.hF k j]
  rw [AlpEmb.centralizer_genCent D.E D.hF k] at hx
  have : Nonempty {u : G // u ∈ closure {g : G | g ∈ genCent v1 v2 v3 s t k} ∧ u * u = 1 ∧
      u ≠ 1 ∧ ∃ c ∈ alpP v1 v2 v3 s t, c⁻¹ * invRep v1 v2 v3 s t j * c = u} :=
    ⟨⟨x, hx, hx2, hx1, hj⟩⟩
  exact Nat.card_pos.ne'

theorem wD_facts :
    D.E.φ wDE ∈ alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t 3} : Set G) ∧
      (∀ c ∈ alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t 3} : Set G),
        c * D.E.φ wDE = D.E.φ wDE * c) ∧
      D.E.φ wDE * D.E.φ wDE = invRep v1 v2 v3 s t 0 := by
  refine ⟨Subgroup.mem_inf.2 ⟨AlpEmb.φ_mem D.E _, ?_⟩, fun c hc => ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff, D.invRep_eq 3, ← map_mul, ← map_mul, wDE_comm_rep]
  · have hc' := hc
    rw [show (3 : Fin 7) = ![3, 5, 6] 0 from rfl, AlpEmb.centralizer_genCent D.E D.hF 0,
      AlpEmb.closure_genCent D.E] at hc'
    obtain ⟨c0, hc0, rfl⟩ := Subgroup.mem_map.1 hc'
    rw [← map_mul, ← map_mul]
    congr 1
    have hle : subE (genCentE 0) ≤ centralizer ({wDE} : Set AlpE) := by
      rw [Subgroup.closure_le]
      intro g hg
      exact mem_centralizer_singleton_iff.2 (wDE_cent g hg)
    exact mem_centralizer_singleton_iff.1 (hle hc0)
  · rw [← map_mul, wDE_sq, D.invRep_eq 0, invE_zero]

theorem fusABC_DFG (hAB : D.Fus 0 1) (hAC : ¬ D.Fus 0 2) :
    D.FusABC 3 ∧ D.FusABC 5 ∧ D.FusABC 6 := by
  suffices hD : D.FusABC 3 by
    refine ⟨hD, ?_, ?_⟩
    · by_contra hF
      exact hF (FusABC.of_fus D (D.fus_F hF).1 hD)
    · by_contra hG
      exact hG (FusABC.of_fus D (D.fus_G hG).1 hD)
  by_contra hD
  obtain ⟨hDF, hDG⟩ := D.fus_D hD
  have hnot : ∀ j : Fin 7, D.Fus 3 j → 3 ≤ j.val := fun j hj => by
    by_contra hlt
    exact hD (D.fusABC_of_le_two (by omega) hj)
  have hextF := D.isSylowOf_rep 5 fun j hj => card_rep_le j (hnot j (hDF.trans D hj))
  obtain ⟨h, hh⟩ := id hDF
  obtain ⟨g, hg1, hg2⟩ := exists_conj_extremal D.isPGroup_P hextF (h := h⁻¹)
    (u := invRep v1 v2 v3 s t 3) (by rw [inv_inv, ← hh]; group)
  set Cd := alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t 3} : Set G) with hCd
  set Ct := alpP v1 v2 v3 s t ⊓ centralizer ({invRep v1 v2 v3 s t 5} : Set G) with hCt
  have hle : Cd.map (MulAut.conj g⁻¹).toMonoidHom ≤ Ct := by
    rintro _ ⟨c, hc, rfl⟩
    simpa [MulAut.conj_apply] using hg2 c hc
  have hcd : Nat.card Cd = 32 := by
    rw [hCd, AlpEmb.card_centralizer_invRep D.E D.hF 3]
    rfl
  have hct : Nat.card Ct = 32 := by
    rw [hCt, AlpEmb.card_centralizer_invRep D.E D.hF 5]
    rfl
  have heq : Cd.map (MulAut.conj g⁻¹).toMonoidHom = Ct :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g⁻¹).injective, hcd, hct])
  obtain ⟨hwCd, hwZ, hwsq⟩ := D.wD_facts
  have hw'Ct : g⁻¹ * D.E.φ wDE * g ∈ Ct := by simpa [MulAut.conj_apply] using hle ⟨_, hwCd, rfl⟩
  have hw'Z : ∀ c ∈ Ct, c * (g⁻¹ * D.E.φ wDE * g) = (g⁻¹ * D.E.φ wDE * g) * c := by
    intro c hc
    rw [← heq] at hc
    obtain ⟨c0, hc0, rfl⟩ := hc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * c0 * g * (g⁻¹ * D.E.φ wDE * g) = g⁻¹ * (c0 * D.E.φ wDE) * g := by group
      _ = g⁻¹ * (D.E.φ wDE * c0) * g := by rw [hwZ c0 hc0]
      _ = g⁻¹ * D.E.φ wDE * g * (g⁻¹ * c0 * g) := by group
  have hzg : g⁻¹ * invRep v1 v2 v3 s t 0 * g = invRep v1 v2 v3 s t 0 := by
    obtain ⟨y, hy⟩ := (AlpEmb.mem_alpP_iff D.E).1 hw'Ct.1
    have hyc : ∀ k ∈ genCentE 1, k * y = y * k := by
      intro k hk
      apply D.E.inj
      rw [map_mul, map_mul, hy]
      apply hw'Z
      rw [hCt, show (5 : Fin 7) = ![3, 5, 6] 1 from rfl, AlpEmb.centralizer_genCent D.E D.hF 1,
        AlpEmb.closure_genCent D.E]
      exact Subgroup.mem_map_of_mem _ (subset_closure hk)
    have hsq : g⁻¹ * invRep v1 v2 v3 s t 0 * g = D.E.φ (y * y) := by
      rw [map_mul, hy, ← hwsq]
      group
    rcases cent_genCent_one_sq y hyc with h1 | h1
    · exfalso
      rw [h1, map_one] at hsq
      apply D.rep_ne_one 0
      calc invRep v1 v2 v3 s t 0 = g * (g⁻¹ * invRep v1 v2 v3 s t 0 * g) * g⁻¹ := by group
        _ = 1 := by rw [hsq]; group
    · rw [hsq, h1, AlpEmb.φ_zc D.E]
      rfl
  have hbCd : invRep v1 v2 v3 s t 1 ∈ Cd := by
    rw [hCd, show (3 : Fin 7) = ![3, 5, 6] 0 from rfl, AlpEmb.centralizer_genCent D.E D.hF 0]
    exact subset_closure (by simp [genCent, invRep])
  set x := g⁻¹ * invRep v1 v2 v3 s t 1 * g with hx
  have hxCt : x ∈ Ct := by simpa [MulAut.conj_apply] using hle ⟨_, hbCd, rfl⟩
  have hx2 : x * x = 1 := by
    calc x * x = g⁻¹ * (invRep v1 v2 v3 s t 1 * invRep v1 v2 v3 s t 1) * g := by rw [hx]; group
      _ = 1 := by rw [D.rep_sq 1]; group
  have hx1 : x ≠ 1 := by
    intro h1
    apply D.rep_ne_one 1
    calc invRep v1 v2 v3 s t 1 = g * x * g⁻¹ := by rw [hx]; group
      _ = 1 := by rw [h1]; group
  obtain ⟨j, hj⟩ := D.exists_inClass hxCt.1 hx2 hx1
  have hcc := D.centCount_ne_zero (k := 1) hxCt hx2 hx1 hj
  have hfus : D.Fus 1 j := D.inClass_fus (D.inClass_rep 1) hj g rfl
  have key : ∀ j : Fin 7, centCount 1 j ≠ 0 → j = 0 ∨ j = 2 ∨ j = 3 ∨ j = 5 ∨ j = 6 := by
    decide
  have hj' := key j hcc
  rcases hj' with rfl | rfl | rfl | rfl | rfl
  ·
    obtain ⟨c, hc, hcx⟩ := hj
    rw [D.z_central hc, ← hzg] at hcx
    have : invRep v1 v2 v3 s t 1 = invRep v1 v2 v3 s t 0 := by
      have := congrArg (fun y => g * y * g⁻¹) hcx
      simpa [hx, mul_assoc] using this.symm
    exact absurd (InClass.unique D (this ▸ D.inClass_rep 1) (D.inClass_rep 0)) (by decide)
  · exact hAC (hAB.trans D hfus)
  · exact hD (FusABC.of_fus D (Fus.symm D hfus) (Or.inr (Or.inl (Fus.refl D 1))))
  · exact hD (FusABC.of_fus D (hDF.trans D (Fus.symm D hfus)) (Or.inr (Or.inl (Fus.refl D 1))))
  · exact hD (FusABC.of_fus D (hDG.trans D (Fus.symm D hfus)) (Or.inr (Or.inl (Fus.refl D 1))))

end FusCtx

end CFSG.OddStandard.ONanRec
