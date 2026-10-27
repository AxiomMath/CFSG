module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore2
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsGeneric
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

@[expose] def perm6 (cs : List (List (Fin 6))) : Equiv.Perm (Fin 6) := (cs.map List.formPerm).prod

@[expose] def pslGens6 : List (Equiv.Perm (Fin 6)) :=
  [perm6 [[2, 4, 3]], perm6 [[0, 4, 1, 2], [3, 5]], perm6 [[2, 4], [3, 5]]]

@[expose] def tau : Equiv.Perm (Fin 6) := perm6 [[0, 1]]

theorem pslGens6_code : pslGens6.map (codeN 6) = Core.pslGen6 := by decide +kernel

theorem pslGens6_sign : ∀ g ∈ pslGens6, Equiv.Perm.sign g = 1 := by decide +kernel

theorem tau_code : codeN 6 tau = Core.tau6 := by decide +kernel

theorem tau_mul_self : tau * tau = 1 := by decide +kernel

theorem tFrob_code : code A6Models.tFrob = Core.tFrobC := by decide +kernel

theorem tFrob_mul_self : A6Models.tFrob * A6Models.tFrob = 1 := by decide +kernel

@[expose] def PslRel (x : P10) (y : Equiv.Perm (Fin 6)) : Prop :=
  ∃ i : ℕ, Core.pslLit[i]? = some (code x) ∧ Core.pslLit6[i]? = some (codeN 6 y)

theorem pslRel_one : PslRel 1 1 := by
  refine ⟨0, ?_, ?_⟩
  · rw [Core.psl_head.1, code_one]
  · rw [Core.psl_head.2, codeN_one]

theorem pslGenC_getElem (k : ℕ) (hk : k < Core.pslGenC.length) (hk' : k < pslGens.length) :
    Core.pslGenC[k]'hk = code (pslGens[k]'hk') := by
  have h := List.getElem_of_eq pslGens_code.symm hk
  rw [h, List.getElem_map]

theorem pslGen6_getElem (k : ℕ) (hk : k < Core.pslGen6.length) (hk' : k < pslGens6.length) :
    Core.pslGen6[k]'hk = codeN 6 (pslGens6[k]'hk') := by
  have h := List.getElem_of_eq pslGens6_code.symm hk
  rw [h, List.getElem_map]

theorem pslRel_step {x : P10} {y : Equiv.Perm (Fin 6)} (h : PslRel x y) {k : ℕ}
    (hk : k < pslGens.length) (hk6 : k < pslGens6.length) :
    PslRel (x * pslGens[k]) (y * pslGens6[k]) := by
  obtain ⟨i, h1, h2⟩ := h
  rw [List.getElem?_eq_some_iff] at h1 h2
  obtain ⟨hi1, e1⟩ := h1
  obtain ⟨hi2, e2⟩ := h2
  have hkc : k < Core.pslGenC.length := by rw [← pslGens_code]; simpa using hk
  have hkc6 : k < Core.pslGen6.length := by rw [← pslGens6_code]; simpa using hk6
  obtain ⟨hj1, ej1⟩ := tbl_spec (e := Core.cid) Core.psl_tbl i hi1 k hkc
  obtain ⟨hj2, ej2⟩ := tbl_spec (e := List.range 6) Core.psl_tbl6 i hi2 k hkc6
  refine ⟨(Core.pslTbl.getD i []).getD k 0, ?_, ?_⟩
  · rw [List.getElem?_eq_some_iff]
    refine ⟨hj1, ?_⟩
    rw [ej1, e1, code_mul, pslGenC_getElem k hkc hk]
    rfl
  · rw [List.getElem?_eq_some_iff]
    refine ⟨hj2, ?_⟩
    rw [ej2, e2, codeN_mul, pslGen6_getElem k hkc6 hk6]

theorem pslRel_step_gen {g : P10} (hg : g ∈ pslGens) :
    ∃ g6 ∈ pslGens6, ∀ {x : P10} {y : Equiv.Perm (Fin 6)}, PslRel x y → PslRel (x * g) (y * g6) := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk6 : k < pslGens6.length := by
    have h1 : pslGens.length = 3 := rfl
    have h2 : pslGens6.length = 3 := rfl
    omega
  exact ⟨pslGens6[k], List.getElem_mem hk6, fun h => pslRel_step h hk hk6⟩

theorem pslRel_functional {x : P10} {y y' : Equiv.Perm (Fin 6)} (h : PslRel x y) (h' : PslRel x y') :
    y = y' := by
  obtain ⟨i, h1, h2⟩ := h
  obtain ⟨i', h1', h2'⟩ := h'
  have hlt : i < Core.pslLit.length := (List.getElem?_eq_some_iff.mp h1).1
  have hi : i = i' := (List.Nodup.getElem?_inj hlt Core.psl_nodup).mp (h1.trans h1'.symm)
  subst hi
  rw [h2] at h2'
  exact codeN_injective (Option.some.inj h2')

theorem pslRel_injective {x x' : P10} {y : Equiv.Perm (Fin 6)} (h : PslRel x y) (h' : PslRel x' y) :
    x = x' := by
  obtain ⟨i, h1, h2⟩ := h
  obtain ⟨i', h1', h2'⟩ := h'
  have hlt : i < Core.pslLit6.length := (List.getElem?_eq_some_iff.mp h2).1
  have hi : i = i' := (List.Nodup.getElem?_inj hlt Core.psl_nodup6).mp (h2.trans h2'.symm)
  subst hi
  rw [h1] at h1'
  exact code_injective (Option.some.inj h1')

theorem pslGens6_closure_exists {c : List ℕ} (hc : c ∈ Core.pslLit6) :
    ∃ y ∈ Subgroup.closure {g | g ∈ pslGens6}, codeN 6 y = c := by
  have h := (mem_closure_iff_of_tblN (gens := pslGens6) pslGens6_code (tree := Core.pslTree)
    (T := Core.pslTbl) (by rw [← Core.psl_build6]; exact Core.psl_tbl6)).2 c
    (by rw [← Core.psl_build6]; exact hc)
  exact h

theorem pslRel_total {x : P10} (hx : x ∈ A6Models.psl29) :
    ∃ y ∈ Subgroup.closure {g | g ∈ pslGens6}, PslRel x y := by
  have hc := (mem_psl29_iff x).1 hx
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hc
  have hi6 : i < Core.pslLit6.length := by
    rw [Core.psl_length6]; rw [Core.psl_length] at hi; exact hi
  obtain ⟨y, hy, hyc⟩ := pslGens6_closure_exists (List.getElem_mem hi6)
  refine ⟨y, hy, i, ?_, ?_⟩
  · rw [List.getElem?_eq_some_iff]; exact ⟨hi, hix⟩
  · rw [List.getElem?_eq_some_iff]; exact ⟨hi6, hyc.symm⟩

theorem pslRel_mul_aux {x' : P10} (hx' : x' ∈ A6Models.psl29) :
    ∀ (x : P10) (y : Equiv.Perm (Fin 6)), PslRel x y → ∀ y', PslRel x' y' →
      PslRel (x * x') (y * y') := by
  rw [psl29_eq] at hx'
  have hsub : (Subgroup.closure {g | g ∈ pslGens}).toSubmonoid =
      Submonoid.closure {g | g ∈ pslGens} := Subgroup.closure_toSubmonoid_of_finite
  have hx'' : x' ∈ Submonoid.closure {g | g ∈ pslGens} := by rw [← hsub]; exact hx'
  refine Submonoid.closure_induction_right
    (motive := fun m _ => ∀ x y, PslRel x y → ∀ y', PslRel m y' → PslRel (x * m) (y * y')) ?_ ?_ hx''
  · intro x y hxy y' h1
    have : y' = 1 := pslRel_functional h1 pslRel_one
    rw [this, mul_one, mul_one]; exact hxy
  · intro m hm g hg ih x y hxy y' h1
    have hms : m ∈ A6Models.psl29 := by
      have : m ∈ (Subgroup.closure {g | g ∈ pslGens}).toSubmonoid := by rw [hsub]; exact hm
      rw [psl29_eq]; exact this
    obtain ⟨ym, -, hym⟩ := pslRel_total hms
    obtain ⟨g6, -, hstep⟩ := pslRel_step_gen hg
    have e : y' = ym * g6 := pslRel_functional h1 (hstep hym)
    have h3 := hstep (ih x y hxy ym hym)
    rw [e, ← mul_assoc, ← mul_assoc]
    exact h3

theorem pslRel_mul {x : P10} {y : Equiv.Perm (Fin 6)} (hxy : PslRel x y) {x' : P10}
    (hx' : x' ∈ A6Models.psl29) {y' : Equiv.Perm (Fin 6)} (h : PslRel x' y') :
    PslRel (x * x') (y * y') := pslRel_mul_aux hx' x y hxy y' h

theorem pslRel_gen {k : ℕ} (hk : k < 3) : PslRel pslGens[k] pslGens6[k] := by
  have h1 : k < pslGens.length := hk
  have h2 : k < pslGens6.length := hk
  have := pslRel_step pslRel_one h1 h2
  rwa [one_mul, one_mul] at this

theorem tFrob_inv : A6Models.tFrob⁻¹ = A6Models.tFrob := inv_eq_of_mul_eq_one_right tFrob_mul_self

theorem tau_inv : tau⁻¹ = tau := inv_eq_of_mul_eq_one_right tau_mul_self

theorem pslGenC_getD (k : ℕ) (hk : k < pslGens.length) :
    Core.pslGenC.getD k [] = code pslGens[k] := by
  rw [← pslGens_code, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  rfl

theorem pslGen6_getD (k : ℕ) (hk : k < pslGens6.length) :
    Core.pslGen6.getD k [] = codeN 6 pslGens6[k] := by
  rw [← pslGens6_code, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]
  rfl

theorem frob_rel {k : ℕ} (hk : k < 3) :
    PslRel (A6Models.tFrob * pslGens[k]'(by simp [pslGens]; omega) * A6Models.tFrob⁻¹)
      (tau * pslGens6[k]'(by simp [pslGens6]; omega) * tau⁻¹) := by
  obtain ⟨i, hi, h1, h2⟩ := Core.frob_conj k hk
  refine ⟨i, ?_, ?_⟩
  · rw [h1]
    congr 1
    rw [code_mul, code_mul, tFrob_inv, tFrob_code, pslGenC_getD k (by simp [pslGens]; omega)]
  · rw [h2]
    congr 1
    rw [codeN_mul, codeN_mul, tau_inv, tau_code, pslGen6_getD k (by simp [pslGens6]; omega)]

theorem exists_psl_hom : ∃ ψ : ↥A6Models.psl29 →* Equiv.Perm (Fin 6), Function.Injective ψ ∧
    (∀ x, ψ x ∈ alternatingGroup (Fin 6)) ∧
    ∀ (x : P10) (hx : x ∈ A6Models.psl29), ∃ hy : A6Models.tFrob * x * A6Models.tFrob⁻¹ ∈
      A6Models.psl29, ψ ⟨A6Models.tFrob * x * A6Models.tFrob⁻¹, hy⟩ = tau * ψ ⟨x, hx⟩ * tau⁻¹ := by
  classical
  choose f hfmem hfrel using fun x : ↥A6Models.psl29 => pslRel_total x.2
  let ψ : ↥A6Models.psl29 →* Equiv.Perm (Fin 6) :=
    { toFun := f
      map_one' := pslRel_functional (hfrel 1) pslRel_one
      map_mul' := fun a b =>
        pslRel_functional (hfrel (a * b)) (pslRel_mul (hfrel a) b.2 (hfrel b)) }
  have hgen : ∀ k (hk : k < 3), ψ ⟨pslGens[k]'(by simp [pslGens]; omega), by
      rw [psl29_eq]; exact Subgroup.subset_closure (List.getElem_mem _)⟩ =
        pslGens6[k]'(by simp [pslGens6]; omega) := by
    intro k hk
    exact pslRel_functional (hfrel _) (pslRel_gen hk)
  have hnorm : ∀ x ∈ A6Models.psl29, A6Models.tFrob * x * A6Models.tFrob⁻¹ ∈ A6Models.psl29 :=
    fun x hx => psl29_normal _ (s6_le_autA6 (Subgroup.subset_closure (by simp [s6Gens]))) x hx
  refine ⟨ψ, ?_, ?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    have h1 : PslRel (b : P10) (f a) := by
      have : f a = f b := hab
      rw [this]; exact hfrel b
    exact pslRel_injective (hfrel a) h1
  · intro x
    obtain ⟨x, hx⟩ := x
    have hx' := hx
    unfold A6Models.psl29 at hx'
    suffices h : ∀ (x : P10) (hx : x ∈ A6Models.psl29), ψ ⟨x, hx⟩ ∈ alternatingGroup (Fin 6) from h x hx
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x hx => ψ ⟨x, hx⟩ ∈ alternatingGroup (Fin 6)) ?_ ?_ ?_ ?_ hx
    · intro g hg
      have hgs : ∃ k, ∃ hk : k < 3, pslGens[k]'(by simp [pslGens]; omega) = g := by
        rcases hg with rfl | rfl | rfl
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨1, by omega, rfl⟩
        · exact ⟨2, by omega, rfl⟩
      obtain ⟨k, hk, hkg⟩ := hgs
      subst hkg
      rw [hgen k hk, Equiv.Perm.mem_alternatingGroup]
      exact pslGens6_sign _ (List.getElem_mem _)
    · have : ψ ⟨1, Subgroup.one_mem _⟩ = 1 := ψ.map_one
      rw [this]; exact Subgroup.one_mem _
    · intro a b ha hb iha ihb
      have : ψ ⟨a * b, Subgroup.mul_mem _ ha hb⟩ = ψ ⟨a, ha⟩ * ψ ⟨b, hb⟩ := ψ.map_mul ⟨a, ha⟩ ⟨b, hb⟩
      rw [this]
      exact Subgroup.mul_mem _ iha ihb
    · intro a ha iha
      have : ψ ⟨a⁻¹, Subgroup.inv_mem _ ha⟩ = (ψ ⟨a, ha⟩)⁻¹ := ψ.map_inv ⟨a, ha⟩
      rw [this]
      exact Subgroup.inv_mem _ iha
  · intro x hx
    unfold A6Models.psl29 at hx
    suffices h : ∀ (x : P10) (hx : x ∈ A6Models.psl29), ∃ hy : A6Models.tFrob * x * A6Models.tFrob⁻¹ ∈
        A6Models.psl29, ψ ⟨A6Models.tFrob * x * A6Models.tFrob⁻¹, hy⟩ = tau * ψ ⟨x, hx⟩ * tau⁻¹ from
      h x hx
    intro x hx
    refine Subgroup.closure_induction
      (p := fun x hx => ∃ hy : A6Models.tFrob * x * A6Models.tFrob⁻¹ ∈ A6Models.psl29,
        ψ ⟨A6Models.tFrob * x * A6Models.tFrob⁻¹, hy⟩ = tau * ψ ⟨x, hx⟩ * tau⁻¹) ?_ ?_ ?_ ?_ hx
    · intro g hg
      have hgs : ∃ k, ∃ hk : k < 3, pslGens[k]'(by simp [pslGens]; omega) = g := by
        rcases hg with rfl | rfl | rfl
        · exact ⟨0, by omega, rfl⟩
        · exact ⟨1, by omega, rfl⟩
        · exact ⟨2, by omega, rfl⟩
      obtain ⟨k, hk, hkg⟩ := hgs
      subst hkg
      have hgm : pslGens[k]'(by simp [pslGens]; omega) ∈ A6Models.psl29 := by
        rw [psl29_eq]; exact Subgroup.subset_closure (List.getElem_mem _)
      refine ⟨hnorm _ hgm, ?_⟩
      have e1 := pslRel_functional (hfrel ⟨_, hnorm _ hgm⟩) (frob_rel hk)
      have e2 := hgen k hk
      show f ⟨_, hnorm _ hgm⟩ = _
      rw [e1, e2]
    · refine ⟨by simp, ?_⟩
      have h1 : (⟨A6Models.tFrob * 1 * A6Models.tFrob⁻¹, by simp⟩ :
          ↥A6Models.psl29) = 1 := by apply Subtype.ext; simp
      have h2 : (⟨1, Subgroup.one_mem _⟩ : ↥A6Models.psl29) = 1 := rfl
      rw [h1, h2, ψ.map_one]; group
    · intro a b ha hb ⟨hya, iha⟩ ⟨hyb, ihb⟩
      have hyab : A6Models.tFrob * (a * b) * A6Models.tFrob⁻¹ ∈ A6Models.psl29 := by
        have : A6Models.tFrob * (a * b) * A6Models.tFrob⁻¹ =
            (A6Models.tFrob * a * A6Models.tFrob⁻¹) * (A6Models.tFrob * b * A6Models.tFrob⁻¹) := by
          group
        rw [this]; exact Subgroup.mul_mem _ hya hyb
      refine ⟨hyab, ?_⟩
      have e : (⟨A6Models.tFrob * (a * b) * A6Models.tFrob⁻¹, hyab⟩ : ↥A6Models.psl29) =
          ⟨_, hya⟩ * ⟨_, hyb⟩ := by
        apply Subtype.ext; show _ = (A6Models.tFrob * a * A6Models.tFrob⁻¹) *
          (A6Models.tFrob * b * A6Models.tFrob⁻¹); group
      have e' : (⟨a * b, Subgroup.mul_mem _ ha hb⟩ : ↥A6Models.psl29) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [e, e', ψ.map_mul, ψ.map_mul, iha, ihb]
      group
    · intro a ha ⟨hya, iha⟩
      have hyai : A6Models.tFrob * a⁻¹ * A6Models.tFrob⁻¹ ∈ A6Models.psl29 := by
        have : A6Models.tFrob * a⁻¹ * A6Models.tFrob⁻¹ = (A6Models.tFrob * a * A6Models.tFrob⁻¹)⁻¹ := by
          group
        rw [this]; exact Subgroup.inv_mem _ hya
      refine ⟨hyai, ?_⟩
      have e : (⟨A6Models.tFrob * a⁻¹ * A6Models.tFrob⁻¹, hyai⟩ : ↥A6Models.psl29) =
          (⟨_, hya⟩ : ↥A6Models.psl29)⁻¹ := by
        apply Subtype.ext; show _ = (A6Models.tFrob * a * A6Models.tFrob⁻¹)⁻¹; group
      have e' : (⟨a⁻¹, Subgroup.inv_mem _ ha⟩ : ↥A6Models.psl29) = (⟨a, ha⟩ : ↥A6Models.psl29)⁻¹ := rfl
      rw [e, e', ψ.map_inv, ψ.map_inv, iha]
      group

theorem tFrob_mem_s6 : A6Models.tFrob ∈ s6 := Subgroup.subset_closure (by simp [s6Gens])

theorem tFrob_not_mem_psl : A6Models.tFrob ∉ A6Models.psl29 := by
  intro h
  have h1 := (mem_psl29_iff _).1 h
  rw [tFrob_code] at h1
  have h2 : Core.pslLit.contains Core.tFrobC = true := List.contains_iff_mem.mpr h1
  rw [Core.frob_not_psl] at h2
  exact Bool.false_ne_true h2

theorem tau_sign : Equiv.Perm.sign tau = -1 := by decide +kernel

theorem s6_cases {x : P10} (hx : x ∈ s6) :
    x ∈ A6Models.psl29 ∨ x * A6Models.tFrob ∈ A6Models.psl29 := by
  obtain ⟨r, hr, hxr⟩ := (mem_s6_iff_exists x).1 hx
  simp only [s6RepsP, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left; simpa using hxr
  · right; simpa [tFrob_inv] using hxr

section Extension

variable {G H : Type*} [Group G] [Group H] (P : Subgroup G) (ψ : ↥P →* H) (F : G) (τ : H)

open Classical in
@[expose] noncomputable def psiTot (x : G) : H := if hx : x ∈ P then ψ ⟨x, hx⟩ else 1

open Classical in
@[expose] noncomputable def thetaTot (x : G) : H :=
  if x ∈ P then psiTot P ψ x else psiTot P ψ (x * F) * τ

variable {P ψ F τ}

theorem psiTot_of_mem {x : G} (hx : x ∈ P) : psiTot P ψ x = ψ ⟨x, hx⟩ := by
  simp only [psiTot, hx, dite_true]

theorem psiTot_mul {a b : G} (ha : a ∈ P) (hb : b ∈ P) :
    psiTot P ψ (a * b) = psiTot P ψ a * psiTot P ψ b := by
  rw [psiTot_of_mem (Subgroup.mul_mem _ ha hb), psiTot_of_mem ha, psiTot_of_mem hb]
  exact ψ.map_mul ⟨a, ha⟩ ⟨b, hb⟩

theorem thetaTot_of_mem {x : G} (hx : x ∈ P) : thetaTot P ψ F τ x = ψ ⟨x, hx⟩ := by
  simp only [thetaTot, hx, ite_true]
  exact psiTot_of_mem hx

theorem thetaTot_of_not_mem {x : G} (hx : x ∉ P) :
    thetaTot P ψ F τ x = psiTot P ψ (x * F) * τ := by
  simp only [thetaTot, hx, ite_false]

theorem thetaTot_mul (hFF : F * F = 1) (hττ : τ * τ = 1) (hFn : ∀ x ∈ P, F * x * F⁻¹ ∈ P)
    (hψ : ∀ x ∈ P, psiTot P ψ (F * x * F⁻¹) = τ * psiTot P ψ x * τ⁻¹)
    {a b : G} (ha : a ∈ P ∨ a * F ∈ P) (hb : b ∈ P ∨ b * F ∈ P) :
    thetaTot P ψ F τ (a * b) = thetaTot P ψ F τ a * thetaTot P ψ F τ b := by
  have hFi : F⁻¹ = F := inv_eq_of_mul_eq_one_right hFF
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have haF : a ∉ P → a * F ∈ P := fun h => ha.resolve_left h
  have hbF : b ∉ P → b * F ∈ P := fun h => hb.resolve_left h
  by_cases hap : a ∈ P <;> by_cases hbp : b ∈ P
  ·
    rw [thetaTot_of_mem (Subgroup.mul_mem _ hap hbp), thetaTot_of_mem hap, thetaTot_of_mem hbp]
    exact ψ.map_mul ⟨a, hap⟩ ⟨b, hbp⟩
  ·
    have hbF' := hbF hbp
    have hab : a * b ∉ P := by
      intro hab; apply hbp
      have : b = a⁻¹ * (a * b) := by group
      rw [this]; exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hap) hab
    have habF : a * (b * F) ∈ P := Subgroup.mul_mem _ hap hbF'
    rw [thetaTot_of_mem hap, thetaTot_of_not_mem hbp, thetaTot_of_not_mem hab, mul_assoc a b F,
      psiTot_mul hap hbF', psiTot_of_mem hap, mul_assoc]
  ·
    have haF' := haF hap
    have hab : a * b ∉ P := by
      intro hab; apply hap
      have : a = (a * b) * b⁻¹ := by group
      rw [this]; exact Subgroup.mul_mem _ hab (Subgroup.inv_mem _ hbp)
    have e : a * b * F = (a * F) * (F * b * F⁻¹) := by
      rw [hFi]
      calc a * b * F = a * (F * F) * b * F := by rw [hFF]; group
        _ = _ := by group
    have hFb := hFn b hbp
    rw [thetaTot_of_not_mem hap, thetaTot_of_mem hbp, thetaTot_of_not_mem hab, e,
      psiTot_mul haF' hFb, hψ b hbp, psiTot_of_mem hbp]
    calc psiTot P ψ (a * F) * (τ * ψ ⟨b, hbp⟩ * τ⁻¹) * τ
        = psiTot P ψ (a * F) * τ * ψ ⟨b, hbp⟩ * (τ⁻¹ * τ) := by group
      _ = _ := by rw [inv_mul_cancel, mul_one]
  ·
    have haF' := haF hap
    have hbF' := hbF hbp
    have hFbF : F * (b * F) * F⁻¹ ∈ P := hFn _ hbF'
    have e : a * b = (a * F) * (F * (b * F) * F⁻¹) := by
      rw [hFi]
      calc a * b = a * (F * F) * b * (F * F) := by rw [hFF]; group
        _ = _ := by group
    have hab : a * b ∈ P := by rw [e]; exact Subgroup.mul_mem _ haF' hFbF
    rw [thetaTot_of_not_mem hap, thetaTot_of_not_mem hbp, thetaTot_of_mem hab,
      ← psiTot_of_mem hab, e, psiTot_mul haF' hFbF, hψ (b * F) hbF', hτi]
    group

end Extension

theorem exists_s6_hom : ∃ θ : ↥s6 →* Equiv.Perm (Fin 6), Function.Injective θ ∧
    ∀ x : ↥s6, (x : P10) ∈ A6Models.psl29 → θ x ∈ alternatingGroup (Fin 6) := by
  classical
  obtain ⟨ψ, hψinj, hψeven, hψconj⟩ := exists_psl_hom
  have hFF := tFrob_mul_self
  have hnorm : ∀ x ∈ A6Models.psl29, A6Models.tFrob * x * A6Models.tFrob⁻¹ ∈ A6Models.psl29 :=
    fun x hx => psl29_normal _ (s6_le_autA6 tFrob_mem_s6) x hx
  have hpsiconj : ∀ x ∈ A6Models.psl29, psiTot A6Models.psl29 ψ (A6Models.tFrob * x * A6Models.tFrob⁻¹) =
      tau * psiTot A6Models.psl29 ψ x * tau⁻¹ := by
    intro x hx
    obtain ⟨hy, h⟩ := hψconj x hx
    rw [psiTot_of_mem hy, psiTot_of_mem hx]
    exact h
  let θ : ↥s6 →* Equiv.Perm (Fin 6) :=
    { toFun := fun x => thetaTot A6Models.psl29 ψ A6Models.tFrob tau (x : P10)
      map_one' := by
        show thetaTot A6Models.psl29 ψ A6Models.tFrob tau (1 : P10) = 1
        rw [thetaTot_of_mem (Subgroup.one_mem _)]
        exact ψ.map_one
      map_mul' := fun a b =>
        thetaTot_mul hFF tau_mul_self hnorm hpsiconj (s6_cases a.2) (s6_cases b.2) }
  refine ⟨θ, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx1
    by_cases hxp : (x : P10) ∈ A6Models.psl29
    · have h1 : θ x = ψ ⟨x, hxp⟩ := thetaTot_of_mem hxp
      rw [h1] at hx1
      have h2 : (⟨x, hxp⟩ : ↥A6Models.psl29) = 1 := hψinj (hx1.trans ψ.map_one.symm)
      apply Subtype.ext
      have h3 := congrArg (fun y : ↥A6Models.psl29 => (y : P10)) h2
      simpa using h3
    · exfalso
      have h1 : θ x = psiTot A6Models.psl29 ψ ((x : P10) * A6Models.tFrob) * tau :=
        thetaTot_of_not_mem hxp
      have hxF := (s6_cases x.2).resolve_left hxp
      rw [psiTot_of_mem hxF] at h1
      have h2 := congrArg Equiv.Perm.sign (h1.symm.trans hx1)
      rw [map_mul, tau_sign, (Equiv.Perm.mem_alternatingGroup).1 (hψeven _), map_one] at h2
      exact absurd h2 (by decide)
  · intro x hx
    have h1 : θ x = ψ ⟨x, hx⟩ := thetaTot_of_mem hx
    rw [h1]
    exact hψeven _

end CFSG.QuasithinUnique.A6Facts
