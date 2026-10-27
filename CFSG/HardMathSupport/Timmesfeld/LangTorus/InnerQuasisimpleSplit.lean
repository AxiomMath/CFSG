module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedCells
public import CFSG.LieType.Chevalley.SL2OppositeRootScalar
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Root

public section

namespace CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped commutatorElement

set_option linter.unusedSectionVars false


section Basic

variable {τ : Tag} {L : Type} [Field L] (σ : L ≃+* L)

noncomputable abbrev frobGL : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom σ.toRingHom)

theorem frobGL_pinnedX (γ : Fin τ.rank → ℤ) (c : L) :
    frobGL σ (pinnedX τ L γ c) = pinnedX τ L γ (σ c) :=
  Units.ext (by
    rw [Units.coe_map]
    exact entrywise_pinnedX σ.toRingHom γ c)

theorem frobGL_mem_rootSpan {S : Set (Fin τ.rank → ℤ)} {g : ModGL τ L}
    (hg : g ∈ rootSpan τ L S) : frobGL σ g ∈ rootSpan τ L S :=
  entrywise_mem_rootSpan hg

theorem frobGL_mem_torusGroup {g : ModGL τ L} (hg : g ∈ torusGroup τ L) :
    frobGL σ g ∈ torusGroup τ L :=
  entrywise_mem_torusGroup hg

theorem sq_eq_one_fixed {ε : L} (h : ε * ε = 1) : σ ε = ε := by
  have : (ε - 1) * (ε + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h1 | h1
  · rw [sub_eq_zero.1 h1, map_one]
  · rw [eq_neg_of_add_eq_zero_left h1, map_neg, map_one]

theorem rootWeylOne_eq {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ∃ a b : L, σ a = a ∧ σ b = b ∧
      rootWeylOne τ L β = pinnedX τ L β a * pinnedX τ L (-β) b * pinnedX τ L β a := by
  obtain ⟨ε, hε, hv⟩ := exists_rootSL2_vSL_eq (K := L) hβ
  refine ⟨(pinnedData τ β).2.2 • (1 : L), ε * (-1), by simp, ?_, ?_⟩
  · rw [map_mul, sq_eq_one_fixed σ hε, map_neg, map_one]
  · unfold rootWeylOne rootWeylSL2
    rw [nSL_one, WSL_eq_uSL_mul_vSL_mul_uSL, map_mul, map_mul, rootSL2_uSL_eq, hv]

theorem frobGL_rootWeylOne {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    frobGL σ (rootWeylOne τ L β) = rootWeylOne τ L β := by
  obtain ⟨a, b, ha, hb, h⟩ := rootWeylOne_eq σ hβ
  rw [h, map_mul, map_mul, frobGL_pinnedX, frobGL_pinnedX, ha, hb]

end Basic

section Fixed

variable {τ : Tag} {L : Type} [Field L] (σ : L ≃+* L) {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)

@[expose] noncomputable def CQ : Subgroup (ModGL τ L) :=
  Subgroup.closure {x | ∃ γ ∈ unionRoots χ ({i} : Set (KernelComponent χ)), ∃ c : L, σ c = c ∧
    x = pinnedX τ L γ c}

variable {σ i}

theorem pinnedX_mem_CQ {γ : Fin τ.rank → ℤ} (hγ : γ ∈ unionRoots χ ({i} : Set (KernelComponent χ)))
    {c : L} (hc : σ c = c) : pinnedX τ L γ c ∈ CQ σ i :=
  Subgroup.subset_closure ⟨γ, hγ, c, hc, rfl⟩

theorem unionRoots_singleton : unionRoots χ ({i} : Set (KernelComponent χ)) = componentRoots χ i := by
  ext α
  rw [mem_unionRoots_iff]
  simp

theorem rootWeylOne_mem_CQ {β : Fin τ.rank → ℤ}
    (hβ : β ∈ unionRoots χ ({i} : Set (KernelComponent χ))) : rootWeylOne τ L β ∈ CQ σ i := by
  have hneg : -β ∈ unionRoots χ ({i} : Set (KernelComponent χ)) := neg_mem_unionRoots hβ
  obtain ⟨a, b, ha, hb, h⟩ := rootWeylOne_eq σ (isRoot_of_mem_unionRoots hβ)
  rw [h]
  exact mul_mem (mul_mem (pinnedX_mem_CQ hβ ha) (pinnedX_mem_CQ hneg hb)) (pinnedX_mem_CQ hβ ha)

theorem mem_CQ_of_fixed_rootSpan {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S)
    (hSΨ : S ⊆ unionRoots χ ({i} : Set (KernelComponent χ))) {x : ModGL τ L}
    (hx : x ∈ rootSpan τ L S) (hfix : frobGL σ x = x) : x ∈ CQ σ i := by
  classical
  have hfin : S.Finite := (finite_setOf_isRoot τ).subset fun a ha => (hS a ha).1
  obtain ⟨m, α, hrange⟩ := hfin.fin_embedding
  have hbij := (positive_root_collection τ L).1 S hS hclosed (m := m) α α.injective hrange
  obtain ⟨c, -, hc⟩ := hbij.surjOn hx
  have hmem : ∀ j, α j ∈ S := fun j => hrange ▸ Set.mem_range_self j
  have hσc : frobGL σ (List.ofFn fun j => pinnedX τ L (α j) (c j)).prod =
      (List.ofFn fun j => pinnedX τ L (α j) (σ (c j))).prod := by
    rw [map_list_prod, List.map_ofFn]
    congr 1
    exact List.ofFn_inj.2 (funext fun j => frobGL_pinnedX σ (α j) (c j))
  have hinj := hbij.injOn
  have hcc : (fun j => σ (c j)) = c := by
    refine hinj (Set.mem_univ _) (Set.mem_univ _) ?_
    show (List.ofFn fun j => pinnedX τ L (α j) (σ (c j))).prod = (List.ofFn fun j => pinnedX τ L (α j) (c j)).prod
    rw [← hσc]
    show frobGL σ _ = _
    rw [show (List.ofFn fun j => pinnedX τ L (α j) (c j)).prod = x from hc, hfix]
  rw [← hc]
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy
  exact pinnedX_mem_CQ (hSΨ (hmem j)) (congrFun hcc j)

theorem posRoots_closed {S : Set (Fin τ.rank → ℤ)} (hS : S = posRoots (unionRoots χ ({i} : Set (KernelComponent χ)))) :
    ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ S := by
  subst hS
  intro α hα β hβ a b ha hb hr
  exact nsmul_add_mem_posRoots_unionRoots hα hβ a b ha hb hr

theorem inversionRoots_closed (w : WeylGroup τ) :
    ∀ α ∈ unionInversionRoots χ ({i} : Set (KernelComponent χ)) w,
      ∀ β ∈ unionInversionRoots χ ({i} : Set (KernelComponent χ)) w, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
      IsRoot τ (a • α + b • β) →
      a • α + b • β ∈ unionInversionRoots χ ({i} : Set (KernelComponent χ)) w := by
  intro α hα β hβ a b ha hb hr
  refine ⟨nsmul_add_mem_posRoots_unionRoots hα.1 hβ.1 a b ha hb hr, ?_⟩
  have h1 : w • (a • α + b • β) = a • (w • α) + b • (w • β) := by
    rw [smul_add, smul_comm w a α, smul_comm w b β]
  rw [h1, height_nsmul_add_nsmul]
  have h2 := hα.2
  have h3 := hβ.2
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  nlinarith


theorem hn_rootWeylOne {J : Set (KernelComponent χ)} :
    ∀ β ∈ unionSimpleRoots χ J, rootWeylOne τ L β ∈ rootSubgroup τ L β ⊔ rootSubgroup τ L (-β) ∧
      rootWeylOne τ L β ∈ monomialSubgroup τ L ∧
      MapsRootLines (rootWeylOne τ L β) (rootReflection β) :=
  fun _ hβ => rootWeylOne_spec (isRoot_of_mem_unionSimpleRoots hβ)

theorem exists_fixedLift {w : WeylGroup τ}
    (hw : w ∈ unionWeylGroup χ ({i} : Set (KernelComponent χ))) :
    ∃ g, g ∈ unionLifts L χ ({i} : Set (KernelComponent χ)) (rootWeylOne τ L) w ∧
      g ∈ CQ σ i ∧ frobGL σ g = g := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨β, hβ, rfl⟩ := hx
    exact ⟨rootWeylOne τ L β, lift_mem_unionLifts hn_rootWeylOne hβ,
      rootWeylOne_mem_CQ (mem_unionRoots_of_mem_unionSimpleRoots hβ),
      frobGL_rootWeylOne σ (isRoot_of_mem_unionSimpleRoots hβ)⟩
  | one => exact ⟨1, one_mem_unionLifts, one_mem _, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨g, hg, hgC, hgf⟩ := hx
    obtain ⟨g', hg', hgC', hgf'⟩ := hy
    exact ⟨g * g', mul_mem_unionLifts hg hg', mul_mem hgC hgC', by rw [map_mul, hgf, hgf']⟩
  | inv x _ hx =>
    obtain ⟨g, hg, hgC, hgf⟩ := hx
    exact ⟨g⁻¹, inv_mem_unionLifts hg, inv_mem hgC, by rw [map_inv, hgf]⟩

theorem conj_mem_unionUnipotent {J : Set (KernelComponent χ)} {b u : ModGL τ L}
    (hb : b ∈ unionBorel L χ J) (hu : u ∈ unionUnipotent L χ J) :
    b * u * b⁻¹ ∈ unionUnipotent L χ J := by
  rw [← SetLike.mem_coe, coe_unionBorel] at hb
  obtain ⟨t, ht, u₀, hu₀, rfl⟩ := hb
  have h1 : u₀ * u * u₀⁻¹ ∈ unionUnipotent L χ J := mul_mem (mul_mem hu₀ hu) (inv_mem hu₀)
  have := (Subgroup.mem_normalizer_iff.1 (unionTorus_le_normalizer ht) _).1 h1
  simpa [mul_assoc] using this

theorem frobGL_mem_unionTorus {J : Set (KernelComponent χ)} {g : ModGL τ L}
    (hg : g ∈ unionTorus L χ J) : frobGL σ g ∈ unionTorus L χ J :=
  Subgroup.mem_inf.2 ⟨frobGL_mem_rootSpan σ (Subgroup.mem_inf.1 hg).1,
    frobGL_mem_torusGroup σ (Subgroup.mem_inf.1 hg).2⟩

theorem frobGL_mem_unionUnipotent {J : Set (KernelComponent χ)} {g : ModGL τ L}
    (hg : g ∈ unionUnipotent L χ J) : frobGL σ g ∈ unionUnipotent L χ J :=
  frobGL_mem_rootSpan σ hg

theorem frobGL_mem_unionBorel {J : Set (KernelComponent χ)} {g : ModGL τ L}
    (hg : g ∈ unionBorel L χ J) : frobGL σ g ∈ unionBorel L χ J := by
  rw [← SetLike.mem_coe, coe_unionBorel] at hg ⊢
  obtain ⟨t, ht, u, hu, rfl⟩ := hg
  exact ⟨_, frobGL_mem_unionTorus ht, _, frobGL_mem_unionUnipotent hu, (map_mul _ _ _).symm⟩

theorem central_mem_unionBorel {c : ModGL τ L}
    (hcS : c ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)))
    (hc : ∀ a ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)), a * c = c * a) :
    c ∈ unionBorel L χ ({i} : Set (KernelComponent χ)) := by
  have hn := hn_rootWeylOne (τ := τ) (L := L) (χ := χ) (J := ({i} : Set (KernelComponent χ)))
  have hmem : c ∈ ⋃ w ∈ unionWeylGroup χ ({i} : Set (KernelComponent χ)),
      unionCell L χ ({i} : Set (KernelComponent χ)) (rootWeylOne τ L) w := by
    rw [← coe_unionRootSpan_eq_iUnion hn]
    exact hcS
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨w, hw, hcw⟩ := hmem
  obtain ⟨_, ⟨b₁, hb₁, g, hg, rfl⟩, b₂, hb₂, hcgb⟩ := hcw
  by_cases hw1 : w = 1
  · subst hw1
    have hgT := mem_unionTorus_of_mapsRootLines_one hn hg.1 hg.2
    rw [← hcgb]
    exact mul_mem (mul_mem hb₁ (unionTorus_le_unionBorel hgT)) hb₂
  · exfalso
    obtain ⟨β, hβ, hneg⟩ := exists_unionSimpleRoots_smul_mem_negRoots hw hw1
    have hβpos := mem_posRoots_of_mem_unionSimpleRoots hβ
    set u : ModGL τ L := pinnedX τ L β 1 with hu
    have huU : u ∈ unionUnipotent L χ ({i} : Set (KernelComponent χ)) :=
      pinnedX_mem_rootSpan hβpos 1
    have hgc : g = b₁⁻¹ * c * b₂⁻¹ := by
      rw [← hcgb]; group
    have hb₂u : b₂⁻¹ * u * b₂ ∈ unionUnipotent L χ ({i} : Set (KernelComponent χ)) := by
      have := conj_mem_unionUnipotent (inv_mem hb₂) huU
      simpa using this
    have hcomm : c * (b₂⁻¹ * u * b₂) = (b₂⁻¹ * u * b₂) * c :=
      (hc _ (unionUnipotent_le_unionRootSpan hb₂u)).symm
    have hguU : g * u * g⁻¹ ∈ unionUnipotent L χ ({i} : Set (KernelComponent χ)) := by
      have e : g * u * g⁻¹ = b₁⁻¹ * (b₂⁻¹ * u * b₂) * b₁ := by
        rw [hgc]
        calc b₁⁻¹ * c * b₂⁻¹ * u * (b₁⁻¹ * c * b₂⁻¹)⁻¹
            = b₁⁻¹ * (c * (b₂⁻¹ * u * b₂)) * c⁻¹ * b₁ := by group
          _ = b₁⁻¹ * ((b₂⁻¹ * u * b₂) * c) * c⁻¹ * b₁ := by rw [hcomm]
          _ = _ := by group
      rw [e]
      have := conj_mem_unionUnipotent (inv_mem hb₁) hb₂u
      simpa using this
    have hgM := unionMonomial_le_monomialSubgroup hn hg.1
    have hneg' : ∀ α ∈ (fun α => w • α) '' ({β} : Set (Fin τ.rank → ℤ)),
        IsRoot τ α ∧ height α < 0 := by
      rintro _ ⟨a, ha, rfl⟩
      rw [Set.mem_singleton_iff] at ha
      subst ha
      refine ⟨IsRoot.smul (isRoot_of_mem_unionSimpleRoots hβ) w, ?_⟩
      show height (w • a) < 0
      have h1 := hneg.2
      rw [height_neg] at h1
      omega
    have hgun : g * u * g⁻¹ ∈ negUnipotent τ L :=
      rootSpan_le_negUnipotent hneg'
        (conj_mem_rootSpan_of_mapsRootLines hgM hg.2 (S := {β})
          (fun α hα => by rw [Set.mem_singleton_iff] at hα; subst hα;
                          exact isRoot_of_mem_unionSimpleRoots hβ)
          (pinnedX_mem_rootSpan (Set.mem_singleton β) 1))
    obtain ⟨w₁, hw₁, -⟩ := weyl_longest_element τ
    have h1 : g * u * g⁻¹ ∈ borelGroup τ L ⊓ negUnipotent τ L :=
      Subgroup.mem_inf.2 ⟨unionBorel_le_borelGroup (unionUnipotent_le_unionBorel hguU), hgun⟩
    rw [(opposite_Borel_intersection τ L w₁ hw₁).2.2.2, Subgroup.mem_bot] at h1
    have hu1 : u = 1 := by
      have : g * u * g⁻¹ = 1 := h1
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    rw [hu, ← pinnedX_zero τ L β] at hu1
    exact one_ne_zero (pinnedX_injective τ L β hu1)


theorem central_mem_unionTorus (hs : ∃ s : Lˣ, s ^ 2 ≠ 1) {c : ModGL τ L}
    (hcS : c ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)))
    (hc : ∀ a ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)), a * c = c * a) :
    c ∈ unionTorus L χ ({i} : Set (KernelComponent χ)) := by
  have hcB := central_mem_unionBorel hcS hc
  rw [← SetLike.mem_coe, coe_unionBorel] at hcB
  obtain ⟨t, ht, u, hu, rfl⟩ := hcB
  suffices hu1 : u = 1 by subst hu1; simpa using ht
  set S : Set (Fin τ.rank → ℤ) := posRoots (unionRoots χ ({i} : Set (KernelComponent χ))) with hSdef
  have hS : ∀ α ∈ S, IsRoot τ α ∧ 0 < height α := fun α hα =>
    isRoot_height_pos_of_mem_posRoots_unionRoots hα
  have hclosed := posRoots_closed (i := i) hSdef
  have hfin : S.Finite := (finite_setOf_isRoot τ).subset fun a ha => (hS a ha).1
  obtain ⟨m, α, hrange⟩ := hfin.fin_embedding
  have hbij := (positive_root_collection τ L).1 S hS hclosed (m := m) α α.injective hrange
  obtain ⟨a, -, hua⟩ := hbij.surjOn hu
  have hmem : ∀ j, α j ∈ S := fun j => hrange ▸ Set.mem_range_self j
  have hzero : ∀ j₀, a j₀ = 0 := by
    intro j₀
    obtain ⟨s, hs2⟩ := hs
    obtain ⟨w, k, hwk⟩ := isRoot_iff_exists_smul_single.1 (hS _ (hmem j₀)).1
    have hk : w • (Pi.single k 1 : Fin τ.rank → ℤ) ∈ componentRoots χ i := by
      rw [hwk, ← unionRoots_singleton]
      exact (hmem j₀).1
    have hh' := canonicalRep_conj_torusElt_mem (K := L) hk s
    set h := canonicalRep (coxeterSystem τ) L w * torusElt τ L k s *
      (canonicalRep (coxeterSystem τ) L w)⁻¹ with hh
    have hhT : h ∈ unionTorus L χ ({i} : Set (KernelComponent χ)) :=
      Subgroup.mem_inf.2 ⟨componentRootSpan_le_unionRootSpan (Set.mem_singleton i)
        (Subgroup.mem_inf.1 hh').1, (Subgroup.mem_inf.1 hh').2⟩
    have hcomm := hc h (unionTorus_le_unionRootSpan hhT)
    have hht : h * t = t * h := mul_comm_of_mem_unionTorus hhT ht
    have hhu : h * u * h⁻¹ = u := by
      have e : t * (h * u) = t * (u * h) := by
        calc t * (h * u) = (t * h) * u := by group
          _ = (h * t) * u := by rw [hht]
          _ = h * (t * u) := by group
          _ = (t * u) * h := hcomm
          _ = t * (u * h) := by group
      have := mul_left_cancel e
      calc h * u * h⁻¹ = (u * h) * h⁻¹ := by rw [this]
        _ = u := by group
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup hhT)
    have hua' : (List.ofFn fun j => pinnedX τ L (α j) (a j)).prod = u := hua
    have hconj : h * u * h⁻¹ =
        (List.ofFn fun j => pinnedX τ L (α j) ((rootChar l (α j) : L) * a j)).prod := by
      rw [← hua']
      have : h * (List.ofFn fun j => pinnedX τ L (α j) (a j)).prod * h⁻¹ =
          ((List.ofFn fun j => pinnedX τ L (α j) (a j)).map (MulAut.conj h)).prod := by
        rw [← MulAut.conj_apply, map_list_prod]
      rw [this, List.map_ofFn]
      congr 1
      refine List.ofFn_inj.2 (funext fun j => ?_)
      simp only [Function.comp_apply, MulAut.conj_apply]
      rw [hl]
      exact rootDiagUnit_conj_pinnedX l (hS _ (hmem j)).1 (a j)
    have hinj := hbij.injOn
    have hcc : (fun j => (rootChar l (α j) : L) * a j) = a := by
      refine hinj (Set.mem_univ _) (Set.mem_univ _) ?_
      show (List.ofFn fun j => pinnedX τ L (α j) ((rootChar l (α j) : L) * a j)).prod =
        (List.ofFn fun j => pinnedX τ L (α j) (a j)).prod
      rw [← hconj, hhu, hua']
    have hr : (rootChar l (α j₀) : L) = ((s ^ 2 : Lˣ) : L) := by
      have h1 := canonicalRep_conj_torusElt_conj_pinnedX_self (K := L) w k s 1
      rw [← hh, hwk] at h1
      have h2 : h * pinnedX τ L (α j₀) 1 * h⁻¹ =
          pinnedX τ L (α j₀) ((rootChar l (α j₀) : L) * 1) := by
        rw [hl]
        exact rootDiagUnit_conj_pinnedX l (hS _ (hmem j₀)).1 1
      have h3 := pinnedX_injective τ L (α j₀) (h2.symm.trans h1)
      simpa using h3
    have h4 := congrFun hcc j₀
    simp only [hr] at h4
    have h5 : (((s ^ 2 : Lˣ) : L) - 1) * a j₀ = 0 := by linear_combination h4
    have h6 : ((s ^ 2 : Lˣ) : L) - 1 ≠ 0 := fun h0 => hs2 (Units.ext (by simpa [sub_eq_zero] using h0))
    exact (mul_eq_zero.1 h5).resolve_left h6
  have : a = 0 := funext hzero
  have hua'' : (List.ofFn fun j => pinnedX τ L (α j) (a j)).prod = u := hua
  rw [← hua'']
  subst this
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
  simp [pinnedX_zero]


theorem exists_decomp {y c : ModGL τ L}
    (hy : y ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)))
    (hc : c ∈ unionTorus L χ ({i} : Set (KernelComponent χ)))
    (hyc : frobGL σ y = c * y) :
    ∃ t ∈ unionTorus L χ ({i} : Set (KernelComponent χ)), ∃ x ∈ CQ σ i,
      y = t * x ∧ frobGL σ t = c * t := by
  have hn := hn_rootWeylOne (τ := τ) (L := L) (χ := χ) (J := ({i} : Set (KernelComponent χ)))
  have hmem : y ∈ ⋃ w ∈ unionWeylGroup χ ({i} : Set (KernelComponent χ)),
      unionCell L χ ({i} : Set (KernelComponent χ)) (rootWeylOne τ L) w := by
    rw [← coe_unionRootSpan_eq_iUnion hn]
    exact hy
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨w, hw, hyw⟩ := hmem
  obtain ⟨g, hg, hgC, hgf⟩ := exists_fixedLift (σ := σ) (i := i) hw
  rw [← doubleCoset_eq_unionCell hn hg] at hyw
  have hbij := bijOn_mul_unionCell hn hw hg
  obtain ⟨⟨b, u⟩, ⟨hb0, hu0⟩, hbu⟩ := hbij.surjOn hyw
  have hb : b ∈ unionBorel L χ ({i} : Set (KernelComponent χ)) := hb0
  have hu : u ∈ rootSpan τ L (unionInversionRoots χ ({i} : Set (KernelComponent χ)) w) := hu0
  have hyb : b * g * u = y := hbu
  have hfy : frobGL σ b * g * frobGL σ u = (c * b) * g * u := by
    have : frobGL σ y = frobGL σ b * g * frobGL σ u := by
      rw [← hyb, map_mul, map_mul, hgf]
    rw [← this, hyc, ← hyb]
    group
  have hdom1 : (frobGL σ b, frobGL σ u) ∈
      (unionBorel L χ ({i} : Set (KernelComponent χ)) : Set (ModGL τ L)) ×ˢ
        (rootSpan τ L (unionInversionRoots χ ({i} : Set (KernelComponent χ)) w) : Set (ModGL τ L)) :=
    ⟨frobGL_mem_unionBorel hb, frobGL_mem_rootSpan σ hu⟩
  have hdom2 : (c * b, u) ∈
      (unionBorel L χ ({i} : Set (KernelComponent χ)) : Set (ModGL τ L)) ×ˢ
        (rootSpan τ L (unionInversionRoots χ ({i} : Set (KernelComponent χ)) w) : Set (ModGL τ L)) :=
    ⟨mul_mem (unionTorus_le_unionBorel hc) hb, hu⟩
  have hinj := hbij.injOn hdom1 hdom2 hfy
  have hb' : frobGL σ b = c * b := congrArg Prod.fst hinj
  have hu' : frobGL σ u = u := congrArg Prod.snd hinj
  have huC : u ∈ CQ σ i := by
    refine mem_CQ_of_fixed_rootSpan (S := unionInversionRoots χ ({i} : Set (KernelComponent χ)) w)
      (fun α hα => isRoot_height_pos_of_mem_posRoots_unionRoots hα.1) ?_ (fun α hα => hα.1.1) hu hu'
    exact inversionRoots_closed w
  rw [← SetLike.mem_coe, coe_unionBorel] at hb
  obtain ⟨t, ht, u₀, hu₀, rfl⟩ := hb
  have hfac := eq_and_eq_of_mul_eq_mul (frobGL_mem_unionTorus ht) (mul_mem hc ht)
    (frobGL_mem_unionUnipotent hu₀) hu₀ (by
      have : frobGL σ (t * u₀) = frobGL σ t * frobGL σ u₀ := map_mul _ _ _
      rw [← this, hb']
      group)
  have hu₀C : u₀ ∈ CQ σ i := by
    refine mem_CQ_of_fixed_rootSpan (S := posRoots (unionRoots χ ({i} : Set (KernelComponent χ))))
      (fun α hα => isRoot_height_pos_of_mem_posRoots_unionRoots hα) (posRoots_closed rfl)
      (fun α hα => hα.1) hu₀ hfac.2
  refine ⟨t, ht, u₀ * g * u, mul_mem (mul_mem hu₀C hgC) huC, ?_, hfac.1⟩
  rw [← hyb]
  group

theorem torus_fixed_char {t c : ModGL τ L} {l : Fin τ.rank → Lˣ} (hl : t = rootDiagUnit τ l)
    (ht : t ∈ unionTorus L χ ({i} : Set (KernelComponent χ)))
    (hc : ∀ a ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)), a * c = c * a)
    (hφ : frobGL σ t = c * t) :
    ∀ γ ∈ unionRoots χ ({i} : Set (KernelComponent χ)), σ (rootChar l γ : L) = rootChar l γ := by
  have htS : t ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := unionTorus_le_unionRootSpan ht
  intro γ hγ
  have hγr := isRoot_of_mem_unionRoots hγ
  have h1 : t * pinnedX τ L γ 1 * t⁻¹ = pinnedX τ L γ ((rootChar l γ : L) * 1) := by
    rw [hl]; exact rootDiagUnit_conj_pinnedX l hγr 1
  have hS1 : t * pinnedX τ L γ 1 * t⁻¹ ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) :=
    mul_mem (mul_mem htS (pinnedX_mem_rootSpan hγ 1)) (inv_mem htS)
  have h2 := congrArg (frobGL σ) h1
  rw [map_mul, map_mul, map_inv, hφ, frobGL_pinnedX, frobGL_pinnedX, map_one] at h2
  have h3 : c * t * pinnedX τ L γ 1 * (c * t)⁻¹ = t * pinnedX τ L γ 1 * t⁻¹ := by
    have := hc _ hS1
    calc c * t * pinnedX τ L γ 1 * (c * t)⁻¹ = c * (t * pinnedX τ L γ 1 * t⁻¹) * c⁻¹ := by group
      _ = (t * pinnedX τ L γ 1 * t⁻¹) * c * c⁻¹ := by rw [← this]
      _ = t * pinnedX τ L γ 1 * t⁻¹ := by group
  rw [h3, h1] at h2
  have h4 := pinnedX_injective τ L γ h2
  simpa using h4.symm


theorem torus_normalizes_CQ {t c : ModGL τ L}
    (ht : t ∈ unionTorus L χ ({i} : Set (KernelComponent χ)))
    (hc : ∀ a ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)), a * c = c * a)
    (hφ : frobGL σ t = c * t) :
    (∀ x ∈ CQ σ i, t * x * t⁻¹ ∈ CQ σ i) ∧ ∀ x ∈ CQ σ i, t⁻¹ * x * t ∈ CQ σ i := by
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup ht)
  have htS : t ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) := unionTorus_le_unionRootSpan ht
  have hfixchar := torus_fixed_char hl ht hc hφ
  have hconj : ∀ γ ∈ unionRoots χ ({i} : Set (KernelComponent χ)), ∀ d : L, σ d = d →
      t * pinnedX τ L γ d * t⁻¹ ∈ CQ σ i ∧ t⁻¹ * pinnedX τ L γ d * t ∈ CQ σ i := by
    intro γ hγ d hd
    have hγr := isRoot_of_mem_unionRoots hγ
    have hr := hfixchar γ hγ
    constructor
    · rw [hl, rootDiagUnit_conj_pinnedX l hγr d]
      exact pinnedX_mem_CQ hγ (by rw [map_mul, hr, hd])
    · have hu : IsUnit (rootChar l γ : L) := (rootChar l γ).isUnit
      have e : t⁻¹ * pinnedX τ L γ d * t = pinnedX τ L γ (((rootChar l γ)⁻¹ : Lˣ) * d) := by
        have h1 : t * pinnedX τ L γ (((rootChar l γ)⁻¹ : Lˣ) * d) * t⁻¹ = pinnedX τ L γ d := by
          rw [hl, rootDiagUnit_conj_pinnedX l hγr, ← mul_assoc]
          simp
        calc t⁻¹ * pinnedX τ L γ d * t
            = t⁻¹ * (t * pinnedX τ L γ (((rootChar l γ)⁻¹ : Lˣ) * d) * t⁻¹) * t := by rw [h1]
          _ = _ := by group
      rw [e]
      refine pinnedX_mem_CQ hγ ?_
      have : σ (((rootChar l γ)⁻¹ : Lˣ) : L) = (((rootChar l γ)⁻¹ : Lˣ) : L) := by
        rw [Units.val_inv_eq_inv_val, map_inv₀, hr]
      rw [map_mul, this, hd]
  constructor
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨γ, hγ, d, hd, rfl⟩ := hx
      exact (hconj γ hγ d hd).1
    | one => simp
    | mul x y _ _ hx hy =>
      have : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      rw [this]; exact mul_mem hx hy
    | inv x _ hx =>
      have : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
      rw [this]; exact inv_mem hx
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨γ, hγ, d, hd, rfl⟩ := hx
      exact (hconj γ hγ d hd).2
    | one => simp
    | mul x y _ _ hx hy =>
      have : t⁻¹ * (x * y) * t = (t⁻¹ * x * t) * (t⁻¹ * y * t) := by group
      rw [this]; exact mul_mem hx hy
    | inv x _ hx =>
      have : t⁻¹ * x⁻¹ * t = (t⁻¹ * x * t)⁻¹ := by group
      rw [this]; exact inv_mem hx


theorem commutator_mem_of_normalizing {G : Type*} [Group G] {C : Subgroup G} {t t' x x' : G}
    (hx : x ∈ C) (hx' : x' ∈ C) (hcomm : t * t' = t' * t)
    (ht : ∀ z ∈ C, t * z * t⁻¹ ∈ C) (ht' : ∀ z ∈ C, t' * z * t'⁻¹ ∈ C)
    (ht2 : ∀ z ∈ C, t⁻¹ * z * t ∈ C) (ht2' : ∀ z ∈ C, t'⁻¹ * z * t' ∈ C) :
    ⁅t * x, t' * x'⁆ ∈ C := by
  have hP : (t'⁻¹ * x * t') * x' ∈ C := mul_mem (ht2' x hx) hx'
  have hQ : (t⁻¹ * x' * t) * x ∈ C := mul_mem (ht2 x' hx') hx
  have key : (t * x) * (t' * x') = (t * t') * ((t'⁻¹ * x * t') * x') := by group
  have key2 : (t' * x') * (t * x) = (t * t') * ((t⁻¹ * x' * t) * x) := by
    calc (t' * x') * (t * x) = (t' * t) * ((t⁻¹ * x' * t) * x) := by group
      _ = _ := by rw [← hcomm]
  have e : ⁅t * x, t' * x'⁆ = (t * t') * (((t'⁻¹ * x * t') * x') * ((t⁻¹ * x' * t) * x)⁻¹) *
      (t * t')⁻¹ := by
    calc ⁅t * x, t' * x'⁆ = ((t * x) * (t' * x')) * ((t' * x') * (t * x))⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = _ := by rw [key, key2]; group
  rw [e]
  have h1 := mul_mem hP (inv_mem hQ)
  have h2 := ht _ (ht' _ h1)
  have e2 : (t * t') * (((t'⁻¹ * x * t') * x') * ((t⁻¹ * x' * t) * x)⁻¹) * (t * t')⁻¹ =
      t * (t' * (((t'⁻¹ * x * t') * x') * ((t⁻¹ * x' * t) * x)⁻¹) * t'⁻¹) * t⁻¹ := by group
  rw [e2]
  exact h2

theorem commutator_mem_CQ (hs : ∃ s : Lˣ, s ^ 2 ≠ 1) {Z : Subgroup (ModGL τ L)}
    (hZ : ∀ z ∈ Z, ∀ a ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)), a * z = z * a)
    {y y' : ModGL τ L} (hy : y ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)))
    (hy' : y' ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)))
    (hZy : frobGL σ y * y⁻¹ ∈ Z) (hZy' : frobGL σ y' * y'⁻¹ ∈ Z) : ⁅y, y'⁆ ∈ CQ σ i := by
  have hcS : frobGL σ y * y⁻¹ ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) :=
    mul_mem (frobGL_mem_rootSpan σ hy) (inv_mem hy)
  have hcS' : frobGL σ y' * y'⁻¹ ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) :=
    mul_mem (frobGL_mem_rootSpan σ hy') (inv_mem hy')
  have hc := hZ _ hZy
  have hc' := hZ _ hZy'
  have hcT := central_mem_unionTorus hs hcS hc
  have hcT' := central_mem_unionTorus hs hcS' hc'
  obtain ⟨t, ht, x, hx, hyt, hφ⟩ := exists_decomp (σ := σ) hy hcT (by group)
  obtain ⟨t', ht', x', hx', hyt', hφ'⟩ := exists_decomp (σ := σ) hy' hcT' (by group)
  have n1 := torus_normalizes_CQ (σ := σ) ht hc hφ
  have n2 := torus_normalizes_CQ (σ := σ) ht' hc' hφ'
  rw [hyt, hyt']
  exact commutator_mem_of_normalizing hx hx' (mul_comm_of_mem_unionTorus ht ht') n1.1 n2.1 n1.2 n2.2

theorem torus_centralizes_CQ (hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1) {t c : ModGL τ L}
    (ht : t ∈ unionTorus L χ ({i} : Set (KernelComponent χ)))
    (hc : ∀ a ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)), a * c = c * a)
    (hφ : frobGL σ t = c * t) :
    ∀ x ∈ CQ σ i, t * x * t⁻¹ = x := by
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (unionTorus_le_torusGroup ht)
  have hfixchar := torus_fixed_char hl ht hc hφ
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, d, hd, rfl⟩ := hx
    have hγr := isRoot_of_mem_unionRoots hγ
    have h1 : (rootChar l γ : L) = 1 :=
      hF _ (hfixchar γ hγ) (rootChar l γ).ne_zero
    rw [hl, rootDiagUnit_conj_pinnedX l hγr d, h1, one_mul]
  | one => simp
  | mul x y _ _ hx hy =>
    have : t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
    rw [this, hx, hy]
  | inv x _ hx =>
    have : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
    rw [this, hx]

theorem commutator_mul_of_commute {G : Type*} [Group G] {t t' x x' : G} (h1 : Commute t x)
    (h2 : Commute t x') (h3 : Commute t' x) (h4 : Commute t' x') (h5 : Commute t t') :
    ⁅t * x, t' * x'⁆ = ⁅x, x'⁆ := by
  have hx : Commute (t * t') x := h1.mul_left h3
  have hx' : Commute (t * t') x' := h2.mul_left h4
  have hc : Commute (t * t') ⁅x, x'⁆ := by
    rw [commutatorElement_def]
    exact ((hx.mul_right hx').mul_right hx.inv_right).mul_right hx'.inv_right
  have e1 : t * x * (t' * x') = (t * t') * (x * x') := by
    calc t * x * (t' * x') = t * (x * t') * x' := by group
      _ = t * (t' * x) * x' := by rw [← h3.eq]
      _ = (t * t') * (x * x') := by group
  have e2 : t' * x' * (t * x) = (t * t') * (x' * x) := by
    calc t' * x' * (t * x) = t' * (x' * t) * x := by group
      _ = t' * (t * x') * x := by rw [← h2.eq]
      _ = (t' * t) * (x' * x) := by group
      _ = (t * t') * (x' * x) := by rw [← h5.eq]
  have e : ⁅t * x, t' * x'⁆ = (t * x * (t' * x')) * (t' * x' * (t * x))⁻¹ := by
    rw [commutatorElement_def]; group
  rw [e, e1, e2]
  calc (t * t') * (x * x') * ((t * t') * (x' * x))⁻¹
      = (t * t') * (x * x' * x⁻¹ * x'⁻¹) * (t * t')⁻¹ := by group
    _ = ⁅x, x'⁆ := by
      rw [← commutatorElement_def, hc.eq]; group

theorem commutator_mem_commutator_CQ (hs : ∃ s : Lˣ, s ^ 2 ≠ 1)
    (hF : ∀ d : L, σ d = d → d ≠ 0 → d = 1) {Z : Subgroup (ModGL τ L)}
    (hZ : ∀ z ∈ Z, ∀ a ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)), a * z = z * a)
    {y y' : ModGL τ L} (hy : y ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)))
    (hy' : y' ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)))
    (hZy : frobGL σ y * y⁻¹ ∈ Z) (hZy' : frobGL σ y' * y'⁻¹ ∈ Z) :
    ⁅y, y'⁆ ∈ ⁅CQ σ i, CQ σ i⁆ := by
  have hcS : frobGL σ y * y⁻¹ ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) :=
    mul_mem (frobGL_mem_rootSpan σ hy) (inv_mem hy)
  have hcS' : frobGL σ y' * y'⁻¹ ∈ unionRootSpan L χ ({i} : Set (KernelComponent χ)) :=
    mul_mem (frobGL_mem_rootSpan σ hy') (inv_mem hy')
  have hc := hZ _ hZy
  have hc' := hZ _ hZy'
  have hcT := central_mem_unionTorus hs hcS hc
  have hcT' := central_mem_unionTorus hs hcS' hc'
  obtain ⟨t, ht, x, hx, hyt, hφ⟩ := exists_decomp (σ := σ) hy hcT (by group)
  obtain ⟨t', ht', x', hx', hyt', hφ'⟩ := exists_decomp (σ := σ) hy' hcT' (by group)
  have n1 := torus_centralizes_CQ hF ht hc hφ
  have n2 := torus_centralizes_CQ hF ht' hc' hφ'
  have cm : ∀ {u v : ModGL τ L}, u * v * u⁻¹ = v → Commute u v := by
    intro u v h
    exact mul_inv_eq_iff_eq_mul.1 h
  rw [hyt, hyt', commutator_mul_of_commute (cm (n1 x hx)) (cm (n1 x' hx')) (cm (n2 x hx))
    (cm (n2 x' hx')) (show Commute t t' from mul_comm_of_mem_unionTorus ht ht')]
  exact Subgroup.commutator_mem_commutator hx hx'

end Fixed

end CFSG.HardMathSupport.Timmesfeld.LangTorus
