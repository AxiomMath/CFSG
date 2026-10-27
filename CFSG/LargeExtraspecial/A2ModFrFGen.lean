module

public import CFSG.LargeExtraspecial.A2ModFrFShort

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrF

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.ExclNS
open scoped commutatorElement

abbrev a3v : Fin 4 → ℤ := ![0, 0, 0, 1]
abbrev s1221 : Fin 4 → ℤ := ![0, 1, 2, 1]

namespace F4Frame

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : F4Frame G R}

theorem rootGroup_weylAction_le {P : Subgroup F.K} {g : F.K} {w : (coxeterMatrix F.hA).Group}
    (hg : ActsAs F.D g w) (hgP : g ∈ P) {γ : Fin 4 → ℤ} (hγ : γ ∈ roots F.hA ∅)
    (hP : F.X γ ≤ P) : F.X (weylAction F.hA w γ) ≤ P := by
  have e : F.X (weylAction F.hA w γ) = (F.X γ).map (MulAut.conj g).toMonoidHom :=
    (hg γ hγ).symm
  rw [e]
  rintro _ ⟨y, hy, rfl⟩
  exact mul_mem (mul_mem hgP (hP hy)) (inv_mem hgP)

theorem conj_n_mem {P : Subgroup F.K} {g : F.K} {v : (coxeterMatrix F.hA).Group}
    (hg : ActsAs F.D g v) (i : Fin 4) (h1 : F.X (weylAction F.hA v (Pi.single i 1)) ≤ P)
    (h2 : F.X (weylAction F.hA v (-Pi.single i 1)) ≤ P) : g * F.n i * g⁻¹ ∈ P := by
  have hα := (RootSystem.ofCartan F.hA ∅).single_mem i
  have hα' := (RootSystem.ofCartan F.hA ∅).neg_mem _ hα
  have hle : (CFSG.LieType.CurtisTits.rankOne F.X i).map (MulAut.conj g).toMonoidHom ≤ P := by
    rw [CFSG.LieType.CurtisTits.rankOne, Subgroup.map_sup]
    exact sup_le ((hg _ hα).trans_le h1) ((hg _ hα').trans_le h2)
  exact hle ⟨F.n i, F.hct.n_mem i, rfl⟩

theorem n_mem_of_le {P : Subgroup F.K} (i : Fin 4) (h1 : F.X (Pi.single i 1) ≤ P)
    (h2 : F.X (-Pi.single i 1) ≤ P) : F.n i ∈ P :=
  (sup_le h1 h2) (F.hct.n_mem i)

theorem eq_top_of_single_le {P : Subgroup F.K} (h : ∀ i : Fin 4, F.X (Pi.single i 1) ≤ P ∧
    F.X (-Pi.single i 1) ≤ P) : P = ⊤ := by
  have hn : ∀ i, F.n i ∈ P := fun i => n_mem_of_le i (h i).1 (h i).2
  have hnrep : ∀ w : (coxeterMatrix F.hA).Group, nrep F.hct w ∈ P := by
    intro w
    obtain ⟨ω, hω, rfl⟩ := (coxeterMatrix F.hA).toCoxeterSystem.exists_isReduced w
    rw [nrep_wordProd F.hct hω]
    refine P.list_prod_mem fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hn i
  rw [eq_top_iff, ← F.hct.iSup_eq_top]
  refine iSup₂_le fun γ hγ => ?_
  obtain ⟨w, i, rfl⟩ := exists_eq_weylAction_single (D := F.D) rfl hγ
  exact rootGroup_weylAction_le (actsAs_nrep w) (hnrep w)
    ((RootSystem.ofCartan F.hA ∅).single_mem i) (h i).1

theorem actsAs_mw : ActsAs F.D (F.n 2 * F.n 3) (F.s 2 * F.s 3) :=
  (actsAs_n (D := F.D) F.hct 2).mul (actsAs_n (D := F.D) F.hct 3)

theorem actsAs_mβ :
    ActsAs F.D (F.n 2 * F.n 1 * (F.n 2)⁻¹) (F.s 2 * F.s 1 * (F.s 2)⁻¹) :=
  ((actsAs_n (D := F.D) F.hct 2).mul (actsAs_n (D := F.D) F.hct 1)).mul
    (actsAs_n (D := F.D) F.hct 2).inv

theorem actsAs_mδ₀ :
    ActsAs F.D (F.n 3 * F.n 2 * F.n 1 * (F.n 3 * F.n 2)⁻¹)
      (F.s 3 * F.s 2 * F.s 1 * (F.s 3 * F.s 2)⁻¹) :=
  ((((actsAs_n (D := F.D) F.hct 3).mul (actsAs_n (D := F.D) F.hct 2)).mul
    (actsAs_n (D := F.D) F.hct 1)).mul
    ((actsAs_n (D := F.D) F.hct 3).mul (actsAs_n (D := F.D) F.hct 2)).inv)

variable {D : Set G} (hR : IsRootClass R) (hRD : ∀ E ∈ R, ∃ d ∈ D, E = Subgroup.zpowers d)
include hR hRD

theorem eq_top_of_le [Finite G] {P : Subgroup F.K}
    (hlong : ∀ γ : Fin 4 → ℤ, (γ = r0 ∨ γ = r1 ∨ γ = r2 ∨ γ = r3) → F.X γ ≤ P ∧ F.X (-γ) ≤ P)
    (he : ∀ c ∈ F.X a2v, c * F.xL r2 * c⁻¹ ∈ P)
    (he' : ∀ c ∈ F.X a2v, (F.n 2 * F.n 3) * (c * F.xL r2 * c⁻¹) * (F.n 2 * F.n 3)⁻¹ ∈ P) :
    P = ⊤ := by
  have hr0 := hlong r0 (Or.inl rfl)
  have hr1 := hlong r1 (Or.inr (Or.inl rfl))
  have hr2 := hlong r2 (Or.inr (Or.inr (Or.inl rfl)))
  have hr3 := hlong r3 (Or.inr (Or.inr (Or.inr rfl)))
  have hL2 := isLong_r2 (F := F)
  have hL3 := isLong_r3 (F := F)
  have h12 : F.X s12 ≤ P :=
    rootGroup_s12_le hR hRD (hr2.1 (xL_mem hL2.mem_roots)) hr3.1 he
  have hmw := actsAs_mw (F := F)
  have h1221 : F.X s1221 ≤ P := by
    set m := F.n 2 * F.n 3
    let P' := P.comap (MulAut.conj m).toMonoidHom
    have hx' : F.xL r2 ∈ P' := by
      change m * F.xL r2 * m⁻¹ ∈ P
      rw [conj_xL hR hRD hmw hL2, weylAction_mul_apply, weylAction_simple_eq F.hA,
        weylAction_simple_eq F.hA,
        show reflF f4M 2 (reflF f4M 3 r2) = r3 by decide]
      exact hr3.1 (xL_mem hL3.mem_roots)
    have hZ' : F.X r3 ≤ P' := fun y hy => by
      change m * y * m⁻¹ ∈ P
      have := hmw.conj_mem hL3.mem_roots hy
      rw [weylAction_mul_apply, weylAction_simple_eq F.hA, weylAction_simple_eq F.hA,
        show reflF f4M 2 (reflF f4M 3 r3) = r0 by decide] at this
      exact hr0.1 this
    have h := rootGroup_s12_le hR hRD (P := P') hx' hZ' he'
    have e := hmw s12 (s12_mem_roots F.hA)
    rw [weylAction_mul_apply, weylAction_simple_eq F.hA, weylAction_simple_eq F.hA,
      show reflF f4M 2 (reflF f4M 3 s12) = s1221 by decide] at e
    change (F.X s12).map (MulAut.conj m).toMonoidHom = F.X s1221 at e
    rw [← e, Subgroup.map_le_iff_le_comap]
    exact h
  have e0 : (Pi.single 0 1 : Fin 4 → ℤ) = r1 := by decide
  have e1 : (Pi.single 1 1 : Fin 4 → ℤ) = r2 := by decide
  have e0' : (-Pi.single 0 1 : Fin 4 → ℤ) = -r1 := by decide
  have e1' : (-Pi.single 1 1 : Fin 4 → ℤ) = -r2 := by decide
  have hn1 : F.n 1 ∈ P := n_mem_of_le 1 (e1 ▸ hr2.1) (e1' ▸ hr2.2)
  have hmβ : F.n 2 * F.n 1 * (F.n 2)⁻¹ ∈ P :=
    conj_n_mem (actsAs_n (D := F.D) F.hct 2) 1
      (by rw [weylAction_simple_eq F.hA,
        show reflF f4M 2 (Pi.single 1 1) = r3 by decide]; exact hr3.1)
      (by rw [weylAction_simple_eq F.hA,
        show reflF f4M 2 (-Pi.single 1 1) = -r3 by decide]; exact hr3.2)
  have hmδ : F.n 3 * F.n 2 * F.n 1 * (F.n 3 * F.n 2)⁻¹ ∈ P :=
    conj_n_mem ((actsAs_n (D := F.D) F.hct 3).mul (actsAs_n (D := F.D) F.hct 2)) 1
      (by rw [weylAction_mul_apply, weylAction_simple_eq F.hA, weylAction_simple_eq F.hA,
        show reflF f4M 3 (reflF f4M 2 (Pi.single 1 1)) = r0 by decide]; exact hr0.1)
      (by rw [weylAction_mul_apply, weylAction_simple_eq F.hA, weylAction_simple_eq F.hA,
        show reflF f4M 3 (reflF f4M 2 (-Pi.single 1 1)) = -r0 by decide]; exact hr0.2)
  have ha2 : F.X a2v ≤ P := by
    have := rootGroup_weylAction_le (actsAs_n (D := F.D) F.hct 1) hn1 (s12_mem_roots F.hA) h12
    rwa [weylAction_simple_eq F.hA, show reflF f4M 1 s12 = a2v by decide] at this
  have ha2' : F.X (-a2v) ≤ P := by
    have := rootGroup_weylAction_le ((actsAs_n (D := F.D) F.hct 1).mul actsAs_mβ)
      (mul_mem hn1 hmβ) (a2v_mem_roots F.hA) ha2
    rwa [CoxeterSystem.inv_simple, weylAction_mul_apply, weylAction_mul_apply,
      weylAction_mul_apply, weylAction_simple_eq F.hA,
      weylAction_simple_eq F.hA, weylAction_simple_eq F.hA, weylAction_simple_eq F.hA,
      show reflF f4M 1 (reflF f4M 2 (reflF f4M 1 (reflF f4M 2 a2v))) = -a2v by decide] at this
  have ha3 : F.X a3v ≤ P := by
    have := rootGroup_weylAction_le actsAs_mβ hmβ
      (mem_roots_of_eq F.hA (F.s 2 * F.s 1 * F.s 2) 3 (by
        rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_simple_eq F.hA,
          weylAction_simple_eq F.hA, weylAction_simple_eq F.hA]; decide) :
          (![0, 1, 2, 1] : Fin 4 → ℤ) ∈ roots F.hA ∅) h1221
    rwa [CoxeterSystem.inv_simple, weylAction_mul_apply, weylAction_mul_apply,
      weylAction_simple_eq F.hA, weylAction_simple_eq F.hA,
      weylAction_simple_eq F.hA,
        show reflF f4M 2 (reflF f4M 1 (reflF f4M 2 s1221)) = a3v by decide] at this
  have ha3' : F.X (-a3v) ≤ P := by
    have h1221R : s1221 ∈ roots F.hA ∅ :=
      mem_roots_of_eq F.hA (F.s 2 * F.s 1 * F.s 2) 3 (by
        rw [weylAction_mul_apply, weylAction_mul_apply, weylAction_simple_eq F.hA,
          weylAction_simple_eq F.hA, weylAction_simple_eq F.hA]; decide)
    have := rootGroup_weylAction_le actsAs_mδ₀ hmδ h1221R h1221
    simp only [mul_inv_rev, CoxeterSystem.inv_simple, weylAction_mul_apply,
      weylAction_simple_eq F.hA] at this
    rwa [show reflF f4M 3 (reflF f4M 2 (reflF f4M 1 (reflF f4M 2 (reflF f4M 3 s1221)))) = -a3v by
      decide] at this
  have e2 : (Pi.single 2 1 : Fin 4 → ℤ) = a2v := by decide
  have e3 : (Pi.single 3 1 : Fin 4 → ℤ) = a3v := by decide
  have e2' : (-Pi.single 2 1 : Fin 4 → ℤ) = -a2v := by decide
  have e3' : (-Pi.single 3 1 : Fin 4 → ℤ) = -a3v := by decide
  refine eq_top_of_single_le fun i => ?_
  fin_cases i
  · exact ⟨e0 ▸ hr1.1, e0' ▸ hr1.2⟩
  · exact ⟨e1 ▸ hr2.1, e1' ▸ hr2.2⟩
  · exact ⟨e2 ▸ ha2, e2' ▸ ha2'⟩
  · exact ⟨e3 ▸ ha3, e3' ▸ ha3'⟩

end F4Frame

end CFSG.LargeExtraspecial.A2Mod.FrF
