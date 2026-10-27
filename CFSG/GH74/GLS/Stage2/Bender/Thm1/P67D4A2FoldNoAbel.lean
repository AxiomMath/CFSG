module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldRGD
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldGen
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2FoldN
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4A2Tits
public import CFSG.GH74.GLS.SP.Local.SPLRestrict

public section

open CFSG.GH74.BNPair
open scoped Pointwise

namespace CFSG.GH74.GLS.SP

variable {X : Type*} [Group X] {H : Subgroup X} {r₁ r₂ : X} {U : Subgroup X}
  {root : ℤ → Subgroup X}

theorem RGD2.restrict_gen {n : ℕ} (R : RGD2 n H r₁ r₂ U root) (G₀ : Subgroup X) (hH : H ≤ G₀)
    (h₁ : r₁ ∈ G₀) (h₂ : r₂ ∈ G₀) (hU : U ≤ G₀) (hroot : ∀ i, IsRoot n i → root i ≤ G₀)
    (hgen : ∀ x ∈ G₀, x ∈ (H ⊔ U) ⊔ R.N) :
    (H.subgroupOf G₀ ⊔ U.subgroupOf G₀) ⊔ (R.restrict G₀ hH h₁ h₂ hU hroot).N = ⊤ := by
  classical
  set R₀ := R.restrict G₀ hH h₁ h₂ hU hroot with hR₀
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup ↥G₀, K' = (H.subgroupOf G₀ ⊔ U.subgroupOf G₀) ⊔ R₀.N :=
    ⟨_, rfl⟩
  rw [eq_top_iff]
  intro x _
  rw [← hK']
  have hGle : (H ⊔ U) ⊔ R.N ≤ K'.map G₀.subtype := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro y hy
      refine ⟨⟨y, hH hy⟩, ?_, rfl⟩
      rw [hK']
      exact le_trans (le_sup_left : H.subgroupOf G₀ ≤ H.subgroupOf G₀ ⊔ U.subgroupOf G₀)
        le_sup_left (show (⟨y, hH hy⟩ : ↥G₀) ∈ H.subgroupOf G₀ from hy)
    · intro y hy
      refine ⟨⟨y, hU hy⟩, ?_, rfl⟩
      rw [hK']
      exact le_trans (le_sup_right : U.subgroupOf G₀ ≤ H.subgroupOf G₀ ⊔ U.subgroupOf G₀)
        le_sup_left (show (⟨y, hU hy⟩ : ↥G₀) ∈ U.subgroupOf G₀ from hy)
    · refine (Subgroup.closure_le _).2 ?_
      rintro y (hy | hy)
      · refine ⟨⟨y, hH hy⟩, ?_, rfl⟩
        rw [hK']
        exact le_trans (le_sup_left : H.subgroupOf G₀ ≤ H.subgroupOf G₀ ⊔ U.subgroupOf G₀)
          le_sup_left (show (⟨y, hH hy⟩ : ↥G₀) ∈ H.subgroupOf G₀ from hy)
      · rcases hy with rfl | rfl
        · refine ⟨⟨y, h₁⟩, ?_, rfl⟩
          rw [hK']
          exact (le_sup_right : R₀.N ≤ H.subgroupOf G₀ ⊔ U.subgroupOf G₀ ⊔ R₀.N)
            (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
        · refine ⟨⟨y, h₂⟩, ?_, rfl⟩
          rw [hK']
          exact (le_sup_right : R₀.N ≤ H.subgroupOf G₀ ⊔ U.subgroupOf G₀ ⊔ R₀.N)
            (Subgroup.subset_closure (Or.inr (Or.inr rfl)))
  obtain ⟨y, hy, hyx⟩ := hGle (hgen x.1 x.2)
  have : y = x := Subtype.ext hyx
  rwa [this] at hy


namespace FoldData

variable {R : RGD2 6 H r₁ r₂ U root} {φ : X ≃* X}

theorem generation (hf : FoldData R φ) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot 6 i → ∀ x ∈ root i, g * x = x * g) → g = 1)
    (hz : ∀ h ∈ H, φ ((r₁ * r₂) ^ 3 * h) ≠ (r₁ * r₂) ^ 3 * h)
    {r₁' r₂' : X} (h1 : φ r₁' = r₁') (h1H : r₁⁻¹ * r₁' ∈ H)
    (h2 : φ r₂' = r₂') (h2H : (r₂ * r₁ * r₂⁻¹)⁻¹ * r₂' ∈ H) {x : X} (hx : φ x = x) :
    x ∈ ((H ⊓ foldFix φ) ⊔ (U ⊓ foldFix φ)) ⊔
      Subgroup.closure (((H ⊓ foldFix φ : Subgroup X) : Set X) ∪ {r₁', r₂'}) := by
  obtain ⟨v, hv, n, hn, u, hu, rfl⟩ := hf.toStab.cell hgen hZ hx
  have hnG := hf.fixed_N_mem hz h1 h1H h2 h2H hn.1 hn.2
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · exact (le_sup_left : _ ≤ ((H ⊓ foldFix φ) ⊔ (U ⊓ foldFix φ)) ⊔ _)
      ((le_sup_right : U ⊓ foldFix φ ≤ (H ⊓ foldFix φ) ⊔ (U ⊓ foldFix φ)) hv)
  · exact (le_sup_right : _ ≤ ((H ⊓ foldFix φ) ⊔ (U ⊓ foldFix φ)) ⊔ _) hnG
  · exact (le_sup_left : _ ≤ ((H ⊓ foldFix φ) ⊔ (U ⊓ foldFix φ)) ⊔ _)
      ((le_sup_right : U ⊓ foldFix φ ≤ (H ⊓ foldFix φ) ⊔ (U ⊓ foldFix φ)) hu)

theorem noAbel (hf : FoldData R φ) (hgen : (H ⊔ U) ⊔ R.N = ⊤)
    (hZ : ∀ g ∈ H, (∀ i, IsRoot 6 i → ∀ x ∈ root i, g * x = x * g) → g = 1)
    (hz : ∀ h ∈ H, φ ((r₁ * r₂) ^ 3 * h) ≠ (r₁ * r₂) ^ 3 * h)
    (hns : ¬ Group.IsSolvable ↥(foldFix φ))
    (hC : ∀ t ∈ H ⊓ foldFix φ, (∀ u ∈ U ⊓ foldFix φ, t * u = u * t) → t = 1)
    (A : Subgroup ↥(foldFix φ)) [A.Normal] (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : A = ⊥ := by
  obtain ⟨r₁', r₂', h1, h2, h1H, h2H, R'⟩ := hf.exists_rgd2
  have hr₁ : r₁' ∈ foldFix φ := h1
  have hr₂ : r₂' ∈ foldFix φ := h2
  have hroot : ∀ i, IsRoot 3 i → foldRoot φ root i ≤ foldFix φ := fun i _ => inf_le_right
  have hgen'' := R'.restrict_gen (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hroot
    (fun x hx => hf.generation hgen hZ hz h1 h1H h2 h2H hx)
  have R'' := R'.restrict (foldFix φ) inf_le_right hr₁ hr₂ inf_le_right hroot
  have := R''.cartan_normal
  refine R''.eq_bot_of_normal_abelian hgen'' hns ?_ A hA
  intro t ht htc
  apply Subtype.ext
  exact hC t.1 ⟨(Subgroup.mem_subgroupOf.1 ht).1, t.2⟩ (fun u hu => by
    have := htc ⟨u, hu.2⟩ hu
    exact congrArg Subtype.val this)

end FoldData

end CFSG.GH74.GLS.SP
