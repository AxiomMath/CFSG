module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S6Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S7Fusion

public section

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

structure Sect7Facts {G : Type*} [Group G] (L : Subgroup G) (f y : G)
    (T U E E₁ K : Subgroup G) (P : Set G) : Prop where
  pgroup : IsPGroup 2 T
  sylow : ¬ 2 ∣ T.index
  f_mem : f ∈ T
  U_le : U ≤ T
  U_index : U.relIndex T = 2
  f_not_mem : f ∉ U
  E₁_le : E₁ ≤ U
  core : ∀ x ∈ T, (∀ z ∈ T, (z * x * z⁻¹) * f ^ 2 = f ^ 2 * (z * x * z⁻¹)) → x ∈ K
  K_cent : ∀ x ∈ K, x * f = f * x → x ∈ E
  sq_fusion : ∀ g : G, g⁻¹ * f ^ 2 * g ∈ E → g⁻¹ * f ^ 2 * g ∈ P
  sq_coset : ∀ x ∈ E, x * x ∈ P → f⁻¹ * x ∈ E₁
  inv_conj : ∀ x ∈ T, x ∉ U → x * x = 1 →
    ∃ z ∈ T, (z * x * z⁻¹) * f ^ 2 = f ^ 2 * (z * x * z⁻¹) ∧ z * x * z⁻¹ ∉ U
  U_inter : ∀ w ∈ T, w * f ^ 2 = f ^ 2 * w → w ∉ U → w ∉ L ⊔ zpowers y
  fy_fusion : ∀ w : G, w * f ^ 2 = f ^ 2 * w → w ∉ L ⊔ zpowers y → w ∉ L ⊔ zpowers f →
    ∀ g : G, w ≠ g⁻¹ * f ^ 2 * g

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {f y : G}
  {T U E E₁ K : Subgroup G} {P : Set G}

namespace Sect7Facts

theorem conj_not_mem (hf : orderOf f = 4)
    (hN : ∀ x : G, x * f ^ 2 = f ^ 2 * x → x * f * x⁻¹ ∈ zpowers f)
    (h : Sect7Facts L f y T U E E₁ K P) (g : G) : g⁻¹ * f * g ∉ U := by
  intro hU
  have hxT : g⁻¹ * f * g ∈ T := h.U_le hU
  have hconj : ∀ z ∈ T, f * (z * (g⁻¹ * f * g) * z⁻¹) = (z * (g⁻¹ * f * g) * z⁻¹) * f := by
    intro z hz
    refine commute_of_isConj_of_centralizer_le hf hN h.pgroup (IsConj.refl f) ?_ h.f_mem ?_
    · exact isConj_iff.2 ⟨z * g⁻¹, by group⟩
    · exact T.mul_mem (T.mul_mem hz hxT) (T.inv_mem hz)
  have hK : g⁻¹ * f * g ∈ K := by
    refine h.core _ hxT fun z hz => ?_
    have h1 := (Commute.pow_left (a := f) (b := z * (g⁻¹ * f * g) * z⁻¹) (hconj z hz) 2).eq
    exact h1.symm
  have hcomm : (g⁻¹ * f * g) * f = f * (g⁻¹ * f * g) := by
    have := hconj 1 T.one_mem
    simpa using this.symm
  have hE : g⁻¹ * f * g ∈ E := h.K_cent _ hK hcomm
  have hsq : g⁻¹ * f ^ 2 * g ∈ E := by
    have : g⁻¹ * f ^ 2 * g = (g⁻¹ * f * g) * (g⁻¹ * f * g) := by rw [sq]; group
    rw [this]; exact E.mul_mem hE hE
  have hP : (g⁻¹ * f * g) * (g⁻¹ * f * g) ∈ P := by
    have : (g⁻¹ * f * g) * (g⁻¹ * f * g) = g⁻¹ * f ^ 2 * g := by rw [sq]; group
    rw [this]; exact h.sq_fusion g hsq
  have hE₁ := h.E₁_le (h.sq_coset _ hE hP)
  apply h.f_not_mem
  have : f = (g⁻¹ * f * g) * (f⁻¹ * (g⁻¹ * f * g))⁻¹ := by group
  rw [this]
  exact U.mul_mem hU (U.inv_mem hE₁)

theorem sq_mem (hf : orderOf f = 4)
    (hN : ∀ x : G, x * f ^ 2 = f ^ 2 * x → x * f * x⁻¹ ∈ zpowers f)
    (hcom : ∀ l ∈ L, l * f = f * l) (hf2 : f ^ 2 ∈ L) (hfL : f ∉ L)
    (hC : ∀ x : G, x * f = f * x → x ∈ L ⊔ zpowers f)
    (h : Sect7Facts L f y T U E E₁ K P) (g : G)
    (hg : g⁻¹ * f ^ 2 * g ∈ T) : g⁻¹ * f ^ 2 * g ∈ U := by
  by_contra hnU
  have hf4 : f ^ 4 = 1 := by rw [← hf]; exact pow_orderOf_eq_one f
  have hxx : (g⁻¹ * f ^ 2 * g) * (g⁻¹ * f ^ 2 * g) = 1 := by
    have : (g⁻¹ * f ^ 2 * g) * (g⁻¹ * f ^ 2 * g) = g⁻¹ * f ^ 4 * g := by
      rw [show f ^ 4 = f ^ 2 * f ^ 2 by rw [← pow_add]]; group
    rw [this, hf4]; group
  obtain ⟨z, hzT, hzC, hzU⟩ := h.inv_conj _ hg hnU hxx
  exact no_fusion_of_fy hf hN hcom hf2 hfL hC h.fy_fusion h.U_inter _ hzC
    (T.mul_mem (T.mul_mem hzT hg) (T.inv_mem hzT)) hzU (g * z⁻¹) (by group)

theorem conclusion (hf : orderOf f = 4)
    (hN : ∀ x : G, x * f ^ 2 = f ^ 2 * x → x * f * x⁻¹ ∈ zpowers f)
    (hcom : ∀ l ∈ L, l * f = f * l) (hf2 : f ^ 2 ∈ L) (hfL : f ∉ L)
    (hC : ∀ x : G, x * f = f * x → x ∈ L ⊔ zpowers f)
    (h : Sect7Facts L f y T U E E₁ K P) :
    ∃ T U : Subgroup G, IsPGroup 2 T ∧ ¬ 2 ∣ T.index ∧ f ∈ T ∧ U ≤ T ∧ U.relIndex T = 2 ∧
      f ∉ U ∧ (∀ g : G, g⁻¹ * f * g ∉ U) ∧
      ∀ g : G, g⁻¹ * f ^ 2 * g ∈ T → g⁻¹ * f ^ 2 * g ∈ U :=
  ⟨T, U, h.pgroup, h.sylow, h.f_mem, h.U_le, h.U_index, h.f_not_mem, h.conj_not_mem hf hN,
    h.sq_mem hf hN hcom hf2 hfL hC⟩

end Sect7Facts

@[expose] def Sect7Existence : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (f s y : G) (S₀ : Subgroup G) (n : G),
    CFSG.EvenSporadicStandard.StdHyp G L → Nat.card (center L) = 2 →
    IsSporadic (L ⧸ center L) .HS → FourHyp G L f → IsTight L s → y * y = 1 → y * f * y⁻¹ = f⁻¹ →
    y ∉ L ⊔ zpowers f → centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y →
    (∃ g : G, y = g * f ^ 2 * g⁻¹) → (∃ g : G, s ^ 2 = g * f ^ 2 * g⁻¹) →
    (¬ ∃ g : G, s ^ 2 * f ^ 2 = g * f ^ 2 * g⁻¹) →
    (∃ u : L, (u : G) = s ^ 2 ∧ u * u = 1 ∧ u ∉ center L) → f ∈ S₀ →
    S₀ ≤ centralizer ({f ^ 2} : Set G) → S₀ ≤ centralizer ({s ^ 2} : Set G) → IsPGroup 2 S₀ →
    ¬ 2 ∣ S₀.relIndex (centralizer ({f ^ 2} : Set G)) →
    (∀ x : G, x ∈ S₀ ↔ n * x * n⁻¹ ∈ S₀) → n * f ^ 2 * n⁻¹ = s ^ 2 →
    ∃ (T U E E₁ K : Subgroup G) (P : Set G), Sect7Facts L f y T U E E₁ K P

omit [Finite G] in
theorem mem_normalizer_zpowers_of_centralizer_eq {L : Subgroup G} {y : G}
    (hcL : f ∈ centralizer (L : Set G)) (hyf : y * f * y⁻¹ = f⁻¹)
    (hN : centralizer ({f ^ 2} : Set G) = (L ⊔ zpowers f) ⊔ zpowers y) {x : G}
    (hx : x * f ^ 2 = f ^ 2 * x) : x * f * x⁻¹ ∈ zpowers f := by
  have hxC : x ∈ centralizer ({f ^ 2} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]; exact hx.symm
  rw [hN] at hxC
  have hle : (L ⊔ zpowers f) ⊔ zpowers y ≤ normalizer (zpowers f : Set G) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro l hl
      rw [mem_normalizer_iff]
      intro h
      have hlf : Commute l f := (Subgroup.mem_centralizer_iff.1 hcL) l hl
      have hc : ∀ k : ℤ, Commute l (f ^ k) := fun k => hlf.zpow_right k
      constructor
      · intro hh
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
        rw [(hc k).eq, mul_inv_cancel_right]
        exact zpow_mem (mem_zpowers f) k
      · intro hh
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
        have : h = f ^ k := by
          calc h = l⁻¹ * (l * h * l⁻¹) * l := by group
            _ = l⁻¹ * f ^ k * l := by rw [hk]
            _ = f ^ k := by
              rw [((hc k).inv_left).eq, inv_mul_cancel_right]
        rw [this]; exact zpow_mem (mem_zpowers f) k
    · intro a ha
      rw [mem_normalizer_iff]
      intro h
      obtain ⟨k, rfl⟩ := ha
      constructor
      · intro hh
        have : f ^ k * h * (f ^ k)⁻¹ = f ^ k * h * f ^ (-k) := by rw [zpow_neg]
        rw [this]
        exact mul_mem (mul_mem (zpow_mem (mem_zpowers f) k) hh) (zpow_mem (mem_zpowers f) _)
      · intro hh
        have h1 : (f ^ k)⁻¹ * (f ^ k * h * (f ^ k)⁻¹) * f ^ k = h := by group
        rw [← h1]
        exact mul_mem (mul_mem (inv_mem (zpow_mem (mem_zpowers f) k)) hh)
          (zpow_mem (mem_zpowers f) k)
    · refine zpowers_le.2 ?_
      rw [mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨k, rfl⟩ := hh
        have : y * f ^ k * y⁻¹ = (y * f * y⁻¹) ^ k := by rw [← conj_zpow]
        rw [this, hyf]
        exact zpow_mem (inv_mem (mem_zpowers f)) k
      · intro hh
        have h1 : y⁻¹ * (y * h * y⁻¹) * y = h := by group
        have h2 : y⁻¹ * f * y = f⁻¹ := by
          calc y⁻¹ * f * y = y⁻¹ * (f⁻¹)⁻¹ * y := by rw [inv_inv]
            _ = y⁻¹ * (y * f * y⁻¹)⁻¹ * y := by rw [hyf]
            _ = f⁻¹ := by group
        have h3 : y⁻¹ * (y * h * y⁻¹) * y ∈ zpowers f := by
          obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
          rw [← hk]
          have : y⁻¹ * f ^ k * y = (y⁻¹ * f * y) ^ k := by
            simpa using (conj_zpow (a := y⁻¹) (b := f) (i := k)).symm
          rw [this, h2]
          exact zpow_mem (inv_mem (mem_zpowers f)) k
        rwa [h1] at h3
  have := (mem_normalizer_iff.1 (hle hxC)) f
  exact this.1 (mem_zpowers f)

theorem sect6LocalAnalysis_of_sect7 (h : Sect7Existence) : Sect6LocalAnalysis := by
  intro G _ _ L f s y S₀ n hL hZ hq H hs hyy hyf hy hN hyc hsc hn hu hfS₀ hS₀f hS₀s hS₀2
    hS₀rel hn1 hn2
  obtain ⟨T, U, E, E₁, K, P, hF⟩ := h G L f s y S₀ n hL hZ hq H hs hyy hyf hy hN hyc hsc hn hu
    hfS₀ hS₀f hS₀s hS₀2 hS₀rel hn1 hn2
  have hfC : f ∈ centralizer (L : Set G) := H.mem_cent
  have hcom : ∀ l ∈ L, l * f = f * l := fun l hl => Subgroup.mem_centralizer_iff.1 hfC l hl
  have hf2 : f ^ 2 ∈ L := by
    obtain ⟨τ, -, hτ⟩ := H.exists_center_gen
    rw [← hτ]; exact τ.2
  have hfL : f ∉ L := by
    intro hfL
    have hz : (⟨f, hfL⟩ : L) ∈ center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hcom l l.2)
    have h2 := congrArg Subtype.val (H.sq_center _ hz)
    have h3 : f ^ 2 = 1 := h2
    have := orderOf_dvd_of_pow_eq_one h3
    rw [H.order] at this
    omega
  have hyL : y ∈ normalizer (L : Set G) := by
    rw [← H.norm, hN]
    exact Subgroup.mem_sup_right (mem_zpowers y)
  have hC : ∀ x : G, x * f = f * x → x ∈ L ⊔ zpowers f := fun x hx =>
    mem_sup_zpowers_of_commute_of_centralizer_eq H.order hcom hyy hyf hyL hN hx
  exact hF.conclusion H.order (fun x hx => mem_normalizer_zpowers_of_centralizer_eq hfC hyf hN hx)
    hcom hf2 hfL hC

end CFSG.EvenSporadicStandard.TwoHS
