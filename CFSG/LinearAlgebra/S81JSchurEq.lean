module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LinearAlgebra.S81JSchur

open Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def mulSpan (N : Submodule K (V →ₗ[K] V)) (X : Submodule K V) : Submodule K V :=
  span K {v | ∃ y ∈ N, ∃ x ∈ X, y x = v}

theorem eq_bot_of_le_mulSpan {N : Submodule K (V →ₗ[K] V)} {F : ℕ → Submodule K V}
    {m : ℕ} (hF0 : F 0 = ⊥) (hFm : F m = ⊤) (hF : ∀ y ∈ N, ∀ i, ∀ v ∈ F (i + 1), y v ∈ F i)
    {X : Submodule K V} (hX : X ≤ mulSpan N X) : X = ⊥ := by
  have key : ∀ i, X ≤ F (i + 1) → X ≤ F i := by
    intro i hi
    refine hX.trans (span_le.mpr ?_)
    rintro _ ⟨y, hy, x, hx, rfl⟩
    exact hF y hy i x (hi hx)
  have hall : ∀ j, X ≤ F (m - j) := by
    intro j
    induction j with
    | zero => simp [hFm]
    | succ j ih =>
      rcases Nat.lt_or_ge j m with h | h
      · have e : m - j = (m - (j + 1)) + 1 := by omega
        rw [e] at ih
        exact key _ ih
      · have e : m - (j + 1) = m - j := by omega
        rw [e]
        exact ih
  have h0 := hall m
  rw [Nat.sub_self, hF0] at h0
  exact eq_bot_iff.mpr h0

theorem eq_zero_of_forall_mem_compl {N : Submodule K (V →ₗ[K] V)}
    (hcomm : ∀ y ∈ N, ∀ z ∈ N, Commute y z) {F : ℕ → Submodule K V} {m : ℕ}
    (hF0 : F 0 = ⊥) (hFm : F m = ⊤) (hF : ∀ y ∈ N, ∀ i, ∀ v ∈ F (i + 1), y v ∈ F i)
    {C : Submodule K V} (hC : IsCompl (mulSpan N ⊤) C) {y : V →ₗ[K] V} (hy : y ∈ N)
    (hyC : ∀ c ∈ C, y c = 0) : y = 0 := by
  have hX : LinearMap.range y ≤ mulSpan N (LinearMap.range y) := by
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ mulSpan N ⊤ ⊔ C := by
      rw [hC.sup_eq_top]
      trivial
    obtain ⟨w, hw, c, hc, rfl⟩ := mem_sup.mp hv
    rw [map_add, hyC c hc, add_zero]
    clear hv
    rw [mulSpan] at hw
    induction hw using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨z, hz, x, -, rfl⟩ := hu
      have hyz : y (z x) = z (y x) := by
        have := LinearMap.congr_fun (hcomm y hy z hz).eq x
        simpa only [Module.End.mul_apply] using this
      rw [hyz]
      exact subset_span ⟨z, hz, y x, LinearMap.mem_range_self y x, rfl⟩
    | zero => simp
    | add a c _ _ ha hc =>
      rw [map_add]
      exact add_mem ha hc
    | smul r a _ ha =>
      rw [map_smul]
      exact Submodule.smul_mem _ r ha
  exact LinearMap.range_eq_bot.mp (eq_bot_of_le_mulSpan hF0 hFm hF hX)

private theorem kills_of_surj_aux {N : Submodule K (V →ₗ[K] V)}
    (hcomm : ∀ y ∈ N, ∀ z ∈ N, Commute y z) {W C : Submodule K V}
    (hdim : 2 ≤ finrank K C) (hNW : ∀ y ∈ N, ∀ v : V, y v ∈ W)
    (hinj : ∀ y ∈ N, (∀ c ∈ C, y c = 0) → y = 0)
    (hsurj : ∀ f : C →ₗ[K] W, ∃ y ∈ N, ∀ c : C, y c = (f c : V)) :
    ∀ y ∈ N, ∀ w ∈ W, y w = 0 := by
  have h0 : 0 < finrank K C := by omega
  haveI : Module.Finite K C := Module.finite_of_finrank_pos h0
  let b : Basis (Fin (finrank K C)) K C := Module.finBasis K C
  let i₁ : Fin (finrank K C) := ⟨0, h0⟩
  let i₂ : Fin (finrank K C) := ⟨1, by omega⟩
  have hne : i₁ ≠ i₂ := by
    intro h
    have := congrArg Fin.val h
    simp [i₁, i₂] at this
  let lam : C →ₗ[K] K := b.coord i₁
  let mu : C →ₗ[K] K := b.coord i₂
  have hlam1 : lam (b i₁) = 1 := by simp [lam]
  have hlam2 : lam (b i₂) = 0 := by simp [lam, Finsupp.single_apply, hne, hne.symm]
  have hmu2 : mu (b i₂) = 1 := by simp [mu]
  have hev : ∀ c : C, ∀ μ' : C →ₗ[K] K, μ' c = 1 → ∀ w ∈ W, ∃ a ∈ N, a (c : V) = w := by
    intro c μ' hμ' w hw
    obtain ⟨a, ha, hac⟩ := hsurj (μ'.smulRight (⟨w, hw⟩ : W))
    exact ⟨a, ha, by simpa [hμ'] using hac c⟩
  have hkill : ∀ u ∈ N, ∀ c : C, ∀ μ' : C →ₗ[K] K, μ' c = 1 → u (c : V) = 0 →
      ∀ w ∈ W, u w = 0 := by
    intro u hu c μ' hμ' hu0 w hw
    obtain ⟨a, ha, hac⟩ := hev c μ' hμ' w hw
    have hcomp : u (a (c : V)) = a (u (c : V)) := by
      have := LinearMap.congr_fun (hcomm u hu a ha).eq (c : V)
      simpa [Module.End.mul_apply] using this
    rw [← hac, hcomp, hu0, map_zero]
  intro y hy w hw
  let g : C →ₗ[K] W := LinearMap.codRestrict W (y.comp C.subtype) (fun c => hNW y hy c)
  let g₂ : C →ₗ[K] W := lam.smulRight (g (b i₁))
  let g₁ : C →ₗ[K] W := g - g₂
  obtain ⟨y₁, hy₁, hy₁g⟩ := hsurj g₁
  obtain ⟨y₂, hy₂, hy₂g⟩ := hsurj g₂
  have hdec : y - y₁ - y₂ = 0 := by
    refine hinj _ (sub_mem (sub_mem hy hy₁) hy₂) ?_
    intro c hc
    have e1 : y₁ c = ((g₁ ⟨c, hc⟩ : W) : V) := hy₁g ⟨c, hc⟩
    have e2 : y₂ c = ((g₂ ⟨c, hc⟩ : W) : V) := hy₂g ⟨c, hc⟩
    have e3 : ((g₁ ⟨c, hc⟩ : W) : V) = ((g ⟨c, hc⟩ : W) : V) - ((g₂ ⟨c, hc⟩ : W) : V) := by
      simp [g₁]
    have e4 : y c = ((g ⟨c, hc⟩ : W) : V) := rfl
    rw [LinearMap.sub_apply, LinearMap.sub_apply, e1, e2, e3, e4]
    abel
  have hyeq : y = y₁ + y₂ := by
    rw [sub_sub] at hdec
    exact sub_eq_zero.mp hdec
  have hy₁c : y₁ (b i₁ : V) = 0 := by
    rw [hy₁g (b i₁)]
    simp [g₁, g₂, hlam1]
  have hy₂c : y₂ (b i₂ : V) = 0 := by
    rw [hy₂g (b i₂)]
    simp [g₂, hlam2]
  rw [hyeq, LinearMap.add_apply, hkill y₁ hy₁ (b i₁) lam hlam1 hy₁c w hw,
    hkill y₂ hy₂ (b i₂) mu hmu2 hy₂c w hw, add_zero]

theorem schur_eq_case [FiniteDimensional K V] (hV : finrank K V = 6)
    {N : Submodule K (V →ₗ[K] V)} (hcomm : ∀ y ∈ N, ∀ z ∈ N, Commute y z)
    {F : ℕ → Submodule K V} {m : ℕ} (hF0 : F 0 = ⊥) (hFm : F m = ⊤)
    (hF : ∀ y ∈ N, ∀ i, ∀ v ∈ F (i + 1), y v ∈ F i) (h9 : 9 ≤ finrank K N) :
    finrank K N = 9 ∧ ∃ W : Submodule K V, finrank K W = 3 ∧ (∀ y ∈ N, ∀ v, y v ∈ W) ∧
      ∀ y ∈ N, ∀ w ∈ W, y w = 0 := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (mulSpan N ⊤)
  set W := mulSpan N ⊤ with hW
  have hmemW : ∀ y ∈ N, ∀ v : V, y v ∈ W := fun y hy v =>
    subset_span ⟨y, hy, v, trivial, rfl⟩
  let Φ : N →ₗ[K] (C →ₗ[K] W) :=
    { toFun := fun y =>
        { toFun := fun c => ⟨(y : V →ₗ[K] V) c, hmemW y y.2 c⟩
          map_add' := fun c c' => Subtype.ext (map_add (y : V →ₗ[K] V) (c : V) (c' : V))
          map_smul' := fun r c => Subtype.ext (map_smul (y : V →ₗ[K] V) r (c : V)) }
      map_add' := fun y z => LinearMap.ext fun c => Subtype.ext rfl
      map_smul' := fun r y => LinearMap.ext fun c => Subtype.ext rfl }
  have hΦ : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    have hyC : ∀ c ∈ C, (y : V →ₗ[K] V) c = 0 := by
      intro c hc
      exact congrArg Subtype.val (LinearMap.congr_fun hy ⟨c, hc⟩)
    exact Subtype.ext (eq_zero_of_forall_mem_compl hcomm hF0 hFm hF hC y.2 hyC)
  have hdimWC : finrank K W + finrank K C = 6 := by
    rw [← hV]
    exact Submodule.finrank_add_eq_of_isCompl hC
  have hle : finrank K N ≤ finrank K C * finrank K W := by
    have h1 : finrank K N ≤ finrank K (C →ₗ[K] W) :=
      LinearMap.finrank_le_finrank_of_injective hΦ
    rwa [Module.finrank_linearMap] at h1
  have hW3 : finrank K W = 3 := by
    have hprod : 9 ≤ finrank K C * finrank K W := le_trans h9 hle
    generalize finrank K W = a at hdimWC hprod ⊢
    generalize finrank K C = c at hdimWC hprod
    have ha : a ≤ 6 := by omega
    interval_cases a <;> omega
  have hC3 : finrank K C = 3 := by omega
  have hN9 : finrank K N = 9 := by
    rw [hC3, hW3] at hle
    omega
  have hdimEq : finrank K N = finrank K (C →ₗ[K] W) := by
    rw [Module.finrank_linearMap, hC3, hW3]
    exact hN9
  have hΦs : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimEq).mp hΦ
  refine ⟨hN9, W, hW3, hmemW, ?_⟩
  have hsurj : ∀ f : C →ₗ[K] W, ∃ y ∈ N, ∀ c : C, y c = (f c : V) := by
    intro f
    obtain ⟨y, hy⟩ := hΦs f
    refine ⟨(y : V →ₗ[K] V), y.2, fun c => ?_⟩
    have h := LinearMap.congr_fun hy c
    exact congrArg Subtype.val h
  exact kills_of_surj_aux hcomm (by omega) hmemW
    (fun y hy hyC => eq_zero_of_forall_mem_compl hcomm hF0 hFm hF hC hy hyC) hsurj

end CFSG.LinearAlgebra.S81JSchur
