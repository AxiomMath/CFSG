module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGGE6Lang
public import CFSG.LocalAnalysis.SeitzReduction.EPilotFusionEntrywise

public noncomputable section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.E6Pilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction.EPilot (pinnedElt entrywiseAdjointAut_pinnedElt)
open scoped Pointwise

set_option linter.unusedSectionVars false

@[expose] def posRootsE6 : Set (Fin Tag.E6.rank → ℤ) := {γ | IsRoot Tag.E6 γ ∧ 0 < height γ}

@[expose] def IsIdealE6 (J : Set (Fin Tag.E6.rank → ℤ)) : Prop :=
  J ⊆ posRootsE6 ∧ ∀ α ∈ posRootsE6, ∀ β ∈ J, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    IsRoot Tag.E6 (a • α + b • β) → a • α + b • β ∈ J

theorem isIdealE6_erase_min {J : Set (Fin Tag.E6.rank → ℤ)} (hJ : IsIdealE6 J)
    {α : Fin Tag.E6.rank → ℤ} (hmin : ∀ β ∈ J, height α ≤ height β) :
    IsIdealE6 (J \ {α}) := by
  refine ⟨fun γ hγ => hJ.1 hγ.1, ?_⟩
  intro γ hγ β hβ a b ha hb hroot
  refine ⟨hJ.2 γ hγ β hβ.1 a b ha hb hroot, ?_⟩
  intro heq
  rw [Set.mem_singleton_iff] at heq
  have h1 : height (a • γ + b • β) = a * height γ + b * height β :=
    height_nsmul_add_nsmul a b γ β
  have hγpos : 0 < height γ := hγ.2
  have hβpos : 0 < height β := (hJ.1 hβ.1).2
  have hαβ : height α ≤ height β := hmin β hβ.1
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  rw [heq] at h1
  nlinarith

theorem exists_trace_one {F : Type} [Field F] [CharP F 2] {δ : F ≃+* F} (hδ2 : δ * δ = 1)
    (hδ1 : δ ≠ 1) : ∃ ω : F, ω + δ ω = 1 := by
  obtain ⟨e, he⟩ : ∃ e : F, δ e ≠ e := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hδ1 (RingEquiv.ext fun x => h x)
  have hδδ : ∀ x, δ (δ x) = x := fun x => by
    have := congrArg (fun φ : F ≃+* F => φ x) hδ2
    simpa using this
  have ht : e + δ e ≠ 0 := by
    intro h
    apply he
    have : δ e = -e := by linear_combination h
    rw [this, CharTwo.neg_eq]
  have htδ : δ (e + δ e) = e + δ e := by rw [map_add, hδδ, add_comm]
  refine ⟨e / (e + δ e), ?_⟩
  rw [map_div₀, htδ, ← add_div, div_self ht]

section Layers

variable {F : Type} [Field F]

theorem isIdealE6_closed {J : Set (Fin Tag.E6.rank → ℤ)} (hJ : IsIdealE6 J) :
    ∀ α ∈ J, ∀ β ∈ J, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot Tag.E6 (a • α + b • β) →
      a • α + b • β ∈ J :=
  fun α hα β hβ a b ha hb hr => hJ.2 α (hJ.1 hα) β hβ a b ha hb hr

@[expose] def UJ (F : Type) [Field F] (J : Set (Fin Tag.E6.rank → ℤ)) : Subgroup (C6 F) :=
  (rootSpan Tag.E6 F J).subgroupOf (adjointGroup Tag.E6 F)

theorem mem_UJ {J : Set (Fin Tag.E6.rank → ℤ)} {g : C6 F} :
    g ∈ UJ F J ↔ (g : ModGL Tag.E6 F) ∈ rootSpan Tag.E6 F J := Iff.rfl

theorem UJ_mono {J J' : Set (Fin Tag.E6.rank → ℤ)} (h : J' ⊆ J) : UJ F J' ≤ UJ F J := by
  intro g hg
  rw [mem_UJ] at hg ⊢
  exact (iSup₂_le fun β hβ => le_iSup₂_of_le β (h hβ) le_rfl : rootSpan Tag.E6 F J' ≤
    rootSpan Tag.E6 F J) hg

theorem pinnedElt_mem_UJ {J : Set (Fin Tag.E6.rank → ℤ)} {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ J)
    (c : F) : pinnedElt Tag.E6 α c ∈ UJ F J :=
  pinnedX_mem_rootSpan hα c

theorem pinnedElt_add (α : Fin Tag.E6.rank → ℤ) (c d : F) :
    pinnedElt Tag.E6 α (c + d) = pinnedElt Tag.E6 α c * pinnedElt Tag.E6 α d :=
  Subtype.ext (pinnedX_add Tag.E6 F α c d)

theorem pinnedElt_zero (α : Fin Tag.E6.rank → ℤ) : pinnedElt Tag.E6 α (0 : F) = 1 :=
  Subtype.ext (pinnedX_zero Tag.E6 F α)

theorem pinnedElt_neg (α : Fin Tag.E6.rank → ℤ) (c : F) :
    (pinnedElt Tag.E6 α c)⁻¹ = pinnedElt Tag.E6 α (-c) :=
  Subtype.ext (pinnedX_neg Tag.E6 F α c)

theorem UJ_conj_mem {J J' : Set (Fin Tag.E6.rank → ℤ)} (hJ : IsIdealE6 J) (hJ' : IsIdealE6 J')
    (hsub : J' ⊆ J) {x n : C6 F} (hx : x ∈ UJ F J) (hn : n ∈ UJ F J') : x * n * x⁻¹ ∈ UJ F J' := by
  have hN := (positive_root_ideal_normality Tag.E6 F hsub (fun α hα => hJ.1 hα)
    (fun α hα β hβ a b ha hb hr => hJ'.2 α (hJ.1 hα) β hβ a b ha hb hr)).2
  have h1 : (⟨(n : ModGL Tag.E6 F), (UJ_mono hsub hn : n ∈ UJ F J)⟩ : ↥(rootSpan Tag.E6 F J)) ∈
      (rootSpan Tag.E6 F J').subgroupOf (rootSpan Tag.E6 F J) := hn
  have h2 := hN.conj_mem _ h1 (⟨(x : ModGL Tag.E6 F), hx⟩ : ↥(rootSpan Tag.E6 F J))
  exact h2

theorem UJ_decomp {J : Set (Fin Tag.E6.rank → ℤ)} (hJ : IsIdealE6 J) (hfin : J.Finite)
    {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ J) {g : C6 F} (hg : g ∈ UJ F J) :
    ∃ (c : F) (n : C6 F), n ∈ UJ F (J \ {α}) ∧ g = pinnedElt Tag.E6 α c * n := by
  classical
  have hfin' : (J \ {α}).Finite := hfin.subset Set.diff_subset
  obtain ⟨m, β, hβinj, hβrange⟩ : ∃ (m : ℕ) (β : Fin m → Fin Tag.E6.rank → ℤ),
      Function.Injective β ∧ Set.range β = J \ {α} := by
    obtain ⟨β, h1, h2⟩ := exists_rootEnum hfin'
    exact ⟨_, β, h1, h2⟩
  have hαβ : α ∉ Set.range β := by rw [hβrange]; simp
  let γ : Fin (m + 1) → (Fin Tag.E6.rank → ℤ) := Fin.cons α β
  have hγinj : Function.Injective γ := Fin.cons_injective_iff.mpr ⟨hαβ, hβinj⟩
  have hγrange : Set.range γ = J := by
    rw [Fin.range_cons, hβrange]
    exact Set.insert_diff_singleton.trans (Set.insert_eq_of_mem hα)
  have hbij := bijOn_prod_pinnedX (τ := Tag.E6) F (fun x hx => hJ.1 hx) (isIdealE6_closed hJ) γ
    hγinj hγrange
  obtain ⟨c, -, hc⟩ := hbij.surjOn (show (g : ModGL Tag.E6 F) ∈ rootSpan Tag.E6 F J from hg)
  simp only [List.ofFn_succ, List.prod_cons, γ, Fin.cons_zero, Fin.cons_succ] at hc
  refine ⟨c 0, (pinnedElt Tag.E6 α (c 0))⁻¹ * g, ?_, by group⟩
  show ((pinnedX Tag.E6 F α (c 0))⁻¹ * (g : ModGL Tag.E6 F)) ∈ rootSpan Tag.E6 F (J \ {α})
  rw [← hc, inv_mul_cancel_left]
  exact list_prod_pinnedX_mem_rootSpan β (fun k => by rw [← hβrange]; exact Set.mem_range_self k)
    (fun k => c k.succ)

theorem eq_zero_of_pinnedElt_mem {J : Set (Fin Tag.E6.rank → ℤ)} (hJ : IsIdealE6 J)
    (hfin : J.Finite) {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ J) (hJ' : IsIdealE6 (J \ {α})) {c : F}
    (h : pinnedElt Tag.E6 α c ∈ UJ F (J \ {α})) : c = 0 := by
  classical
  have hfin' : (J \ {α}).Finite := hfin.subset Set.diff_subset
  obtain ⟨m, β, hβinj, hβrange⟩ : ∃ (m : ℕ) (β : Fin m → Fin Tag.E6.rank → ℤ),
      Function.Injective β ∧ Set.range β = J \ {α} := by
    obtain ⟨β, h1, h2⟩ := exists_rootEnum hfin'
    exact ⟨_, β, h1, h2⟩
  have hαβ : α ∉ Set.range β := by rw [hβrange]; simp
  have hbij' := bijOn_prod_pinnedX (τ := Tag.E6) F (fun x hx => hJ'.1 hx) (isIdealE6_closed hJ')
    β hβinj hβrange
  obtain ⟨d, -, hd⟩ := hbij'.surjOn (show (pinnedX Tag.E6 F α c : ModGL Tag.E6 F) ∈
    rootSpan Tag.E6 F (J \ {α}) from h)
  let γ : Fin (m + 1) → (Fin Tag.E6.rank → ℤ) := Fin.cons α β
  have hγinj : Function.Injective γ := Fin.cons_injective_iff.mpr ⟨hαβ, hβinj⟩
  have hγpos : ∀ i, IsRoot Tag.E6 (γ i) ∧ 0 < height (γ i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hJ.1 hα
    · exact hJ'.1 (by rw [← hβrange]; exact Set.mem_range_self k)
  have hinj := (positive_root_product_injectivity Tag.E6 F γ hγinj hγpos).2
  have e1 : (List.ofFn fun i : Fin (m + 1) => pinnedX Tag.E6 F (γ i)
      ((Fin.cons c (0 : Fin m → F) : Fin (m + 1) → F) i)).prod = pinnedX Tag.E6 F α c := by
    rw [List.ofFn_succ, List.prod_cons]
    simp only [γ, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, pinnedX_zero Tag.E6 F]
    simp
  have e2 : (List.ofFn fun i : Fin (m + 1) => pinnedX Tag.E6 F (γ i)
      ((Fin.cons 0 d : Fin (m + 1) → F) i)).prod = pinnedX Tag.E6 F α c := by
    rw [List.ofFn_succ, List.prod_cons]
    simp only [γ, Fin.cons_zero, Fin.cons_succ, pinnedX_zero Tag.E6 F, one_mul]
    exact hd
  have key := @hinj (Fin.cons c (0 : Fin m → F) : Fin (m + 1) → F) (Fin.cons 0 d)
    (e1.trans e2.symm)
  simpa using congrFun key 0

end Layers

section Induction

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem fieldAutE6_eq_entrywise (δ : F ≃+* F) :
    fieldAutE6 F δ = entrywiseAdjointAut Tag.E6 δ :=
  FieldGraphFieldPointwise.exactNormalAut_one_zero_eq δ

theorem fieldAutE6_pinnedElt (δ : F ≃+* F) (α : Fin Tag.E6.rank → ℤ) (c : F) :
    fieldAutE6 F δ (pinnedElt Tag.E6 α c) = pinnedElt Tag.E6 α (δ c) := by
  rw [fieldAutE6_eq_entrywise]
  exact entrywiseAdjointAut_pinnedElt δ α c

theorem fieldAutE6_mem_UJ {δ : F ≃+* F} {J : Set (Fin Tag.E6.rank → ℤ)} {g : C6 F}
    (hg : g ∈ UJ F J) : fieldAutE6 F δ g ∈ UJ F J := by
  rw [mem_UJ] at hg ⊢
  rw [fieldAutE6_eq_entrywise, coe_entrywiseAdjointAut]
  exact entrywise_mem_rootSpan hg

theorem ulang_ideal {δ : F ≃+* F} (hδ2 : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ (n : ℕ) (J : Set (Fin Tag.E6.rank → ℤ)), J.ncard = n → J.Finite → IsIdealE6 J →
      ∀ g ∈ UJ F J, g * fieldAutE6 F δ g = 1 →
        ∃ w ∈ UJ F J, g = w * (fieldAutE6 F δ w)⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro J hn hfin hJ g hg hcoc
    by_cases hJe : J = ∅
    · subst hJe
      have hg1 : g = 1 := by
        have h1 : (g : ModGL Tag.E6 F) ∈ rootSpan Tag.E6 F (∅ : Set (Fin Tag.E6.rank → ℤ)) := hg
        have h2 : rootSpan Tag.E6 F (∅ : Set (Fin Tag.E6.rank → ℤ)) = ⊥ := by simp [rootSpan]
        rw [h2, Subgroup.mem_bot] at h1
        exact Subtype.ext h1
      refine ⟨1, (UJ F ∅).one_mem, ?_⟩
      rw [hg1, map_one]
      group
    · obtain ⟨α, hα, hmin⟩ := Set.exists_min_image J height hfin (Set.nonempty_iff_ne_empty.mpr hJe)
      have hJ' : IsIdealE6 (J \ {α}) := isIdealE6_erase_min hJ hmin
      have hfin' : (J \ {α}).Finite := hfin.subset Set.diff_subset
      have hlt : (J \ {α}).ncard < n := hn ▸ Set.ncard_diff_singleton_lt_of_mem hα hfin
      have hα2 : ∀ x : C6 F, fieldAutE6 F δ (fieldAutE6 F δ x) = x := fun x => by
        have := fieldAutE6_sq hδ2
        simpa using congrArg (fun φ : MulAut (C6 F) => φ x) this
      have hle : UJ F (J \ {α}) ≤ UJ F J := UJ_mono Set.diff_subset
      have hbase : ∀ m ∈ UJ F (J \ {α}), m * fieldAutE6 F δ m = 1 →
          ∃ w ∈ UJ F (J \ {α}), m = w * (fieldAutE6 F δ w)⁻¹ :=
        fun m hm hmc => ih _ hlt (J \ {α}) rfl hfin' hJ' m hm hmc
      have hquot : ∀ g ∈ UJ F J, g * fieldAutE6 F δ g = 1 →
          ∃ w ∈ UJ F J, w⁻¹ * g * fieldAutE6 F δ w ∈ UJ F (J \ {α}) := by
        intro g hg hcoc
        obtain ⟨c, n, hn, rfl⟩ := UJ_decomp hJ hfin hα hg
        have hδg : fieldAutE6 F δ (pinnedElt Tag.E6 α c * n) =
            pinnedElt Tag.E6 α (δ c) * fieldAutE6 F δ n := by
          rw [map_mul, fieldAutE6_pinnedElt]
        have hm : fieldAutE6 F δ n ∈ UJ F (J \ {α}) := fieldAutE6_mem_UJ hn
        have hYU : pinnedElt Tag.E6 α (δ c) ∈ UJ F J := pinnedElt_mem_UJ hα _
        have hconj : (pinnedElt Tag.E6 α (δ c))⁻¹ * n * pinnedElt Tag.E6 α (δ c) ∈
            UJ F (J \ {α}) := by
          have := UJ_conj_mem hJ hJ' Set.diff_subset ((UJ F J).inv_mem hYU) hn
          simpa using this
        have h1 : (pinnedElt Tag.E6 α c * pinnedElt Tag.E6 α (δ c)) *
            (((pinnedElt Tag.E6 α (δ c))⁻¹ * n * pinnedElt Tag.E6 α (δ c)) *
              fieldAutE6 F δ n) = 1 := by
          rw [hδg] at hcoc
          calc (pinnedElt Tag.E6 α c * pinnedElt Tag.E6 α (δ c)) *
                (((pinnedElt Tag.E6 α (δ c))⁻¹ * n * pinnedElt Tag.E6 α (δ c)) *
                  fieldAutE6 F δ n)
              = pinnedElt Tag.E6 α c * n * (pinnedElt Tag.E6 α (δ c) * fieldAutE6 F δ n) := by
                group
            _ = 1 := hcoc
        have hXY : pinnedElt Tag.E6 α c * pinnedElt Tag.E6 α (δ c) ∈ UJ F (J \ {α}) := by
          have : pinnedElt Tag.E6 α c * pinnedElt Tag.E6 α (δ c) =
              (((pinnedElt Tag.E6 α (δ c))⁻¹ * n * pinnedElt Tag.E6 α (δ c)) *
                fieldAutE6 F δ n)⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [this]
          exact (UJ F (J \ {α})).inv_mem ((UJ F (J \ {α})).mul_mem hconj hm)
        have hc0 : c + δ c = 0 := by
          apply eq_zero_of_pinnedElt_mem hJ hfin hα hJ'
          rw [pinnedElt_add]
          exact hXY
        have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
        have hδc : δ c = c := by linear_combination hc0 - c * h2
        obtain ⟨ω, hω⟩ := exists_trace_one hδ2 hδ1
        have hd : c * ω + δ (c * ω) = c := by
          rw [map_mul, hδc, ← mul_add, hω, mul_one]
        refine ⟨pinnedElt Tag.E6 α (c * ω), pinnedElt_mem_UJ hα _, ?_⟩
        rw [fieldAutE6_pinnedElt]
        have hVU : pinnedElt Tag.E6 α (δ (c * ω)) ∈ UJ F J := pinnedElt_mem_UJ hα _
        have hconj2 : (pinnedElt Tag.E6 α (δ (c * ω)))⁻¹ * n *
            pinnedElt Tag.E6 α (δ (c * ω)) ∈ UJ F (J \ {α}) := by
          have := UJ_conj_mem hJ hJ' Set.diff_subset ((UJ F J).inv_mem hVU) hn
          simpa using this
        have hWXV : (pinnedElt Tag.E6 α (c * ω))⁻¹ * pinnedElt Tag.E6 α c *
            pinnedElt Tag.E6 α (δ (c * ω)) = 1 := by
          rw [pinnedElt_neg, ← pinnedElt_add, ← pinnedElt_add]
          have : -(c * ω) + c + δ (c * ω) = 0 := by
            linear_combination (-1 : F) * hd + (δ (c * ω)) * h2
          rw [this, pinnedElt_zero]
        have hfinal : (pinnedElt Tag.E6 α (c * ω))⁻¹ * (pinnedElt Tag.E6 α c * n) *
            pinnedElt Tag.E6 α (δ (c * ω)) =
            (pinnedElt Tag.E6 α (δ (c * ω)))⁻¹ * n * pinnedElt Tag.E6 α (δ (c * ω)) := by
          calc (pinnedElt Tag.E6 α (c * ω))⁻¹ * (pinnedElt Tag.E6 α c * n) *
                pinnedElt Tag.E6 α (δ (c * ω))
              = ((pinnedElt Tag.E6 α (c * ω))⁻¹ * pinnedElt Tag.E6 α c *
                  pinnedElt Tag.E6 α (δ (c * ω))) *
                ((pinnedElt Tag.E6 α (δ (c * ω)))⁻¹ * n * pinnedElt Tag.E6 α (δ (c * ω))) := by
                group
            _ = _ := by rw [hWXV, one_mul]
        rw [hfinal]
        exact hconj2
      exact cocycle_two_step (fieldAutE6 F δ) hα2 hle hbase hquot g hg hcoc

theorem ulang_holds {δ : F ≃+* F} (hδ2 : δ * δ = 1) (hδ1 : δ ≠ 1) : ULang F δ := by
  intro u hu hcoc
  have hΦ : IsIdealE6 posRootsE6 := by
    refine ⟨subset_rfl, ?_⟩
    intro α hα β hβ a b ha hb hroot
    refine ⟨hroot, ?_⟩
    rw [height_nsmul_add_nsmul]
    have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
    have h1 : 0 < height α := hα.2
    have h2 : 0 < height β := hβ.2
    nlinarith
  have hfin : posRootsE6.Finite := finite_of_forall_isRoot_pos (fun γ hγ => hγ)
  obtain ⟨w, hw, hwu⟩ := ulang_ideal hδ2 hδ1 _ posRootsE6 rfl hfin hΦ u hu hcoc
  exact ⟨w, hw, hwu⟩

end Induction

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongKGG

