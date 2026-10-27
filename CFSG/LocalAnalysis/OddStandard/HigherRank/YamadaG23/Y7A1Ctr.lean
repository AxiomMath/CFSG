module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1CtrA
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1CtrB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7A1CtrC

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A V P3 C : Subgroup G} {a₁ b₁ a₂ b₂ z : G}

private lemma not_le_of_inf_eq_zpowers {G : Type} [Group G] {H V : Subgroup G} {z : G}
    (hz : z ≠ 1) (hz2 : z ^ 2 = 1) (hHV : H ⊓ V = zpowers z) (hHcard : Nat.card ↥H ≠ 2) :
    ¬ H ≤ V := by
  intro hle
  have hH : H = zpowers z := by rw [← inf_eq_left.mpr hle, hHV]
  have hcard : Nat.card ↥H = 2 := by
    rw [hH, Nat.card_zpowers]
    exact orderOf_eq_prime hz2 hz
  exact hHcard hcard

private lemma conj_mem_sup {G : Type} [Group G] {U V : Subgroup G} {c : G}
    (hU : ∀ u ∈ U, c * u * c⁻¹ ∈ U ⊔ V) (hV : ∀ v ∈ V, c * v * c⁻¹ ∈ V) :
    ∀ x ∈ U ⊔ V, c * x * c⁻¹ ∈ U ⊔ V := by
  intro x hx
  rw [sup_eq_closure] at hx
  refine Subgroup.closure_induction (p := fun g _ => c * g * c⁻¹ ∈ U ⊔ V) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hy | hy
    · exact hU y hy
    · exact mem_of_le_of_mem le_sup_right (hV y hy)
  · simpa using one_mem (U ⊔ V)
  · intro y z _ _ ihy ihz
    rw [show c * (y * z) * c⁻¹ = (c * y * c⁻¹) * (c * z * c⁻¹) by group]
    exact mul_mem ihy ihz
  · intro y _ ihy
    rw [show c * y⁻¹ * c⁻¹ = (c * y * c⁻¹)⁻¹ by group]
    exact inv_mem ihy

theorem y7a_central_AV (hA : A = closure {a₁, b₁, a₂, b₂}) (hrel : Y6ARel a₁ b₁ a₂ b₂ z)
    (hz : z ≠ 1) (hA32 : Nat.card ↥A = 32) (hVA : A ⊓ V = zpowers z)
    (hVc : ∀ a ∈ A, ∀ v ∈ V, a * v = v * a) (hVab : ∀ v ∈ V, ∀ v' ∈ V, v * v' = v' * v)
    (hP3z : ∀ k ∈ P3, k * z * k⁻¹ = z)
    (hU : IsOrbitMod P3 (zpowers z) ((closure {a₁, b₁} : Set G) \ (zpowers z : Set G)))
    (hW : IsOrbitMod P3 (zpowers z) ((closure {a₂, b₂} : Set G) \ (zpowers z : Set G)))
    (h9 : IsOrbitMod P3 (zpowers z) ((A : Set G) \
      ((closure {a₁, b₁} : Set G) ∪ (closure {a₂, b₂} : Set G))))
    (hC : IsPGroup 2 C) (hAVC : A ⊔ V ≤ C)
    (hCV : ∀ c ∈ C, ∀ v ∈ V, c * v * c⁻¹ ∈ V)
    (hCAV : ∀ c ∈ C, ∀ x ∈ A ⊔ V, c * x * c⁻¹ ∈ A ⊔ V)
    (hP3V : ∀ k ∈ P3, ∀ v ∈ V, k * v * k⁻¹ ∈ V)
    (hP3AV : ∀ k ∈ P3, ∀ x ∈ A ⊔ V, k * x * k⁻¹ ∈ A ⊔ V)
    (hP3C : ∀ k ∈ P3, ∀ c ∈ C, k * c * k⁻¹ ∈ C) :
    ∀ c ∈ C, ∀ x ∈ A ⊔ V, ⁅c, x⁆ ∈ V := by
  have hcentAV : A ⊔ V ≤ Subgroup.centralizer (V : Set G) :=
    sup_le
      (fun a ha => Subgroup.mem_centralizer_iff.mpr (fun v hv => (hVc a ha v hv).symm))
      (fun v hv => Subgroup.mem_centralizer_iff.mpr (fun v' hv' => (hVab v hv v' hv').symm))
  have hcommV : ∀ x ∈ A ⊔ V, ∀ w ∈ V, x * w * x⁻¹ = w := by
    intro x hx w hw
    have h1 : w * x = x * w := (Subgroup.mem_centralizer_iff.mp (hcentAV hx)) w hw
    rw [← h1]; group
  let D : Subgroup G :=
    { carrier := {x | x ∈ A ⊔ V ∧ ∀ c ∈ C, ⁅c, x⁆ ∈ V}
      mul_mem' := by
        intro x y hx hy
        refine ⟨mul_mem hx.1 hy.1, ?_⟩
        intro c hc
        have hy' : ⁅c, y⁆ ∈ V := hy.2 c hc
        have hconj : x * ⁅c, y⁆ * x⁻¹ ∈ V := by
          rw [hcommV x hx.1 (⁅c, y⁆) hy']; exact hy'
        rw [show ⁅c, x * y⁆ = ⁅c, x⁆ * (x * ⁅c, y⁆ * x⁻¹) by
          simp only [commutatorElement_def]; group]
        exact mul_mem (hx.2 c hc) hconj
      one_mem' := ⟨one_mem _, by intro c _; rw [commutatorElement_one_right]; exact one_mem V⟩
      inv_mem' := by
        intro x hx
        refine ⟨inv_mem hx.1, ?_⟩
        intro c hc
        have hx' : ⁅c, x⁆ ∈ V := hx.2 c hc
        rw [show ⁅c, x⁻¹⁆ = x⁻¹ * ⁅c, x⁆⁻¹ * x by
          simp only [commutatorElement_def]; group]
        have hconj : x⁻¹ * ⁅c, x⁆⁻¹ * x = ⁅c, x⁆⁻¹ := by
          have h := hcommV x⁻¹ (inv_mem hx.1) (⁅c, x⁆⁻¹) (inv_mem hx')
          rwa [inv_inv] at h
        rw [hconj]; exact inv_mem hx' }
  have hDmem : ∀ x, x ∈ D ↔ x ∈ A ⊔ V ∧ ∀ c ∈ C, ⁅c, x⁆ ∈ V := fun _ => Iff.rfl
  have hVD : V ≤ D := by
    intro v hv
    rw [hDmem v]
    refine ⟨mem_of_le_of_mem le_sup_right hv, ?_⟩
    intro c hc
    rw [commutatorElement_def]
    exact mul_mem (hCV c hc v hv) (inv_mem hv)
  have hDA : D ≤ A ⊔ V := fun x hx => ((hDmem x).mp hx).1
  have hDinv : ∀ k ∈ P3, ∀ x ∈ D, k * x * k⁻¹ ∈ D := by
    intro k hk x hx
    rw [hDmem x] at hx
    rw [hDmem (k * x * k⁻¹)]
    obtain ⟨hxAV, hxcomm⟩ := hx
    refine ⟨hP3AV k hk x hxAV, ?_⟩
    intro c hc
    have hcinC : k⁻¹ * c * k ∈ C := by
      simpa using hP3C k⁻¹ (inv_mem hk) c hc
    have hcomm' : ⁅k⁻¹ * c * k, x⁆ ∈ V := hxcomm _ hcinC
    rw [show ⁅c, k * x * k⁻¹⁆ = k * ⁅k⁻¹ * c * k, x⁆ * k⁻¹ by
      simp only [commutatorElement_def]; group]
    exact hP3V k hk _ hcomm'
  have hA32' : Nat.card ↥(closure {a₁, b₁, a₂, b₂} : Subgroup G) = 32 := by
    rw [← hA]; exact hA32
  obtain ⟨hUcard, hWcard, _⟩ := y6q8_card_UW hrel hz hA32'
  have hA_UW : A = (closure {a₁, b₁} : Subgroup G) ⊔ (closure {a₂, b₂} : Subgroup G) := by
    rw [hA, ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hU_le_A : (closure {a₁, b₁} : Subgroup G) ≤ A :=
    le_trans y6q8_U_le_A (le_of_eq hA.symm)
  have hW_le_A : (closure {a₂, b₂} : Subgroup G) ≤ A :=
    le_trans y6q8_W_le_A (le_of_eq hA.symm)
  have hzU : z ∈ (closure {a₁, b₁} : Subgroup G) := by
    rw [← hrel.a1_sq]; exact pow_mem (Subgroup.subset_closure (by simp)) 2
  have hzW : z ∈ (closure {a₂, b₂} : Subgroup G) := by
    rw [← hrel.b2_sq]; exact pow_mem (Subgroup.subset_closure (by simp)) 2
  have hzpV : zpowers z ≤ V := (le_of_eq hVA.symm).trans inf_le_right
  have hzV : z ∈ V := hzpV (Subgroup.mem_zpowers z)
  have hUV : (closure {a₁, b₁} : Subgroup G) ⊓ V = zpowers z := by
    refine le_antisymm ?_ (le_inf (Subgroup.zpowers_le.mpr hzU) hzpV)
    intro x hx
    have hx' : x ∈ A ⊓ V := ⟨by rw [hA]; exact y6q8_U_le_A hx.1, hx.2⟩
    rwa [hVA] at hx'
  have hWV : (closure {a₂, b₂} : Subgroup G) ⊓ V = zpowers z := by
    refine le_antisymm ?_ (le_inf (Subgroup.zpowers_le.mpr hzW) hzpV)
    intro x hx
    have hx' : x ∈ A ⊓ V := ⟨by rw [hA]; exact y6q8_W_le_A hx.1, hx.2⟩
    rwa [hVA] at hx'
  have hUnotV : ¬ (closure {a₁, b₁} : Subgroup G) ≤ V :=
    not_le_of_inf_eq_zpowers hz hrel.z_sq hUV (by rw [hUcard]; decide)
  have hWnotV : ¬ (closure {a₂, b₂} : Subgroup G) ≤ V :=
    not_le_of_inf_eq_zpowers hz hrel.z_sq hWV (by rw [hWcard]; decide)
  have hUc : ∀ u ∈ (closure {a₁, b₁} : Subgroup G), ∀ v ∈ V, u * v = v * u :=
    fun u hu v hv => hVc u (hU_le_A hu) v hv
  have hWc : ∀ w ∈ (closure {a₂, b₂} : Subgroup G), ∀ v ∈ V, w * v = v * w :=
    fun w hw v hv => hVc w (hW_le_A hw) v hv
  have hAnotV : ¬ A ≤ V :=
    not_le_of_inf_eq_zpowers hz hrel.z_sq hVA (by rw [hA32]; decide)
  have hne : ∃ x ∈ D, x ∉ V := by
    obtain ⟨a, ha, haV⟩ := IsConcreteLE.not_le_iff_exists.mp hAnotV
    have hMV : ∀ m ∈ A ⊔ V, ∀ v ∈ V, m * v * m⁻¹ ∈ V := by
      intro m hm v hv; rw [hcommV m hm v hv]; exact hv
    obtain ⟨x, hxM, hxV, hxc⟩ :=
      y7a_pgroup_fixed hC (hC.to_le hAVC) le_sup_right hMV hCV hCAV
        ⟨a, mem_of_le_of_mem le_sup_left ha, haV⟩
    exact ⟨x, (hDmem x).mpr ⟨hxM, hxc⟩, hxV⟩
  have hUW := y7a_inv_UW hA hrel hz hA32 hP3z hU hW h9 hVA hVc hVD hDA hDinv hne
  have hAD : A ≤ D := by
    rw [hA_UW]
    rcases hUW with hUD | hWD
    ·
      refine sup_le hUD ?_
      have hWVC : (closure {a₂, b₂} : Subgroup G) ⊔ V ≤ C :=
        sup_le (le_trans hW_le_A (le_trans le_sup_left hAVC)) (le_trans le_sup_right hAVC)
      have hWAV : (closure {a₂, b₂} : Subgroup G) ⊔ V ≤ A ⊔ V :=
        sup_le (le_trans hW_le_A le_sup_left) le_sup_right
      have hMV : ∀ m ∈ (closure {a₂, b₂} : Subgroup G) ⊔ V, ∀ v ∈ V, m * v * m⁻¹ ∈ V := by
        intro m hm v hv; rw [hcommV m (hWAV hm) v hv]; exact hv
      have hCnUV : ∀ c ∈ C, ∀ x ∈ (closure {a₁, b₁} : Subgroup G) ⊔ V,
          c * x * c⁻¹ ∈ (closure {a₁, b₁} : Subgroup G) ⊔ V := by
        intro c hc
        refine conj_mem_sup (fun u hu => ?_) (fun v hv => hCV c hc v hv)
        have hcu : c * u * c⁻¹ = ⁅c, u⁆ * u := by
          simpa using (conj_eq_commutatorElement_mul (g₁ := c) (g₂ := u))
        rw [hcu]
        exact mul_mem (mem_of_le_of_mem le_sup_right (((hDmem u).mp (hUD hu)).2 c hc))
          (mem_of_le_of_mem le_sup_left hu)
      have hcent := y7a_cent_UV hA hrel hz hA32 hVA hVc hVab
      have hCnWV : ∀ c ∈ C, ∀ x ∈ (closure {a₂, b₂} : Subgroup G) ⊔ V,
          c * x * c⁻¹ ∈ (closure {a₂, b₂} : Subgroup G) ⊔ V := by
        intro c hc x hx
        have hxAV : x ∈ A ⊔ V := hWAV hx
        have hxcomm : ∀ y' ∈ (closure {a₁, b₁} : Subgroup G) ⊔ V, x * y' = y' * x :=
          (hcent x hxAV).mpr hx
        refine (hcent (c * x * c⁻¹) (hCAV c hc x hxAV)).mp ?_
        intro y hy
        have hcy : c⁻¹ * y * c ∈ (closure {a₁, b₁} : Subgroup G) ⊔ V := by
          have := hCnUV c⁻¹ (inv_mem hc) y hy
          simpa using this
        have hxy : x * (c⁻¹ * y * c) = (c⁻¹ * y * c) * x := hxcomm _ hcy
        calc (c * x * c⁻¹) * y = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by group
          _ = c * ((c⁻¹ * y * c) * x) * c⁻¹ := by rw [hxy]
          _ = y * (c * x * c⁻¹) := by group
      have hneWV : ∃ m ∈ (closure {a₂, b₂} : Subgroup G) ⊔ V, m ∉ V := by
        obtain ⟨m, hm, hmV⟩ := IsConcreteLE.not_le_iff_exists.mp hWnotV
        exact ⟨m, mem_of_le_of_mem le_sup_left hm, hmV⟩
      obtain ⟨x, hxWV, hxV, hxcomm⟩ :=
        y7a_pgroup_fixed hC (hC.to_le hWVC) le_sup_right hMV hCV hCnWV hneWV
      have hxD : x ∈ D := (hDmem x).mpr ⟨hWAV hxWV, hxcomm⟩
      exact y7a_inv_W hrel hz hP3z hW hzV hVD hDinv hWc hWV ⟨x, hxD, hxWV, hxV⟩
    ·
      refine sup_le ?_ hWD
      have hUVC : (closure {a₁, b₁} : Subgroup G) ⊔ V ≤ C :=
        sup_le (le_trans hU_le_A (le_trans le_sup_left hAVC)) (le_trans le_sup_right hAVC)
      have hUAV : (closure {a₁, b₁} : Subgroup G) ⊔ V ≤ A ⊔ V :=
        sup_le (le_trans hU_le_A le_sup_left) le_sup_right
      have hMV : ∀ m ∈ (closure {a₁, b₁} : Subgroup G) ⊔ V, ∀ v ∈ V, m * v * m⁻¹ ∈ V := by
        intro m hm v hv; rw [hcommV m (hUAV hm) v hv]; exact hv
      have hCnWV : ∀ c ∈ C, ∀ x ∈ (closure {a₂, b₂} : Subgroup G) ⊔ V,
          c * x * c⁻¹ ∈ (closure {a₂, b₂} : Subgroup G) ⊔ V := by
        intro c hc
        refine conj_mem_sup (fun w hw => ?_) (fun v hv => hCV c hc v hv)
        have hcw : c * w * c⁻¹ = ⁅c, w⁆ * w := by
          simpa using (conj_eq_commutatorElement_mul (g₁ := c) (g₂ := w))
        rw [hcw]
        exact mul_mem (mem_of_le_of_mem le_sup_right (((hDmem w).mp (hWD hw)).2 c hc))
          (mem_of_le_of_mem le_sup_left hw)
      have hcent := y7a_cent_WV hA hrel hz hA32 hVA hVc hVab
      have hCnUV : ∀ c ∈ C, ∀ x ∈ (closure {a₁, b₁} : Subgroup G) ⊔ V,
          c * x * c⁻¹ ∈ (closure {a₁, b₁} : Subgroup G) ⊔ V := by
        intro c hc x hx
        have hxAV : x ∈ A ⊔ V := hUAV hx
        have hxcomm : ∀ y' ∈ (closure {a₂, b₂} : Subgroup G) ⊔ V, x * y' = y' * x :=
          (hcent x hxAV).mpr hx
        refine (hcent (c * x * c⁻¹) (hCAV c hc x hxAV)).mp ?_
        intro y hy
        have hcy : c⁻¹ * y * c ∈ (closure {a₂, b₂} : Subgroup G) ⊔ V := by
          have := hCnWV c⁻¹ (inv_mem hc) y hy
          simpa using this
        have hxy : x * (c⁻¹ * y * c) = (c⁻¹ * y * c) * x := hxcomm _ hcy
        calc (c * x * c⁻¹) * y = c * (x * (c⁻¹ * y * c)) * c⁻¹ := by group
          _ = c * ((c⁻¹ * y * c) * x) * c⁻¹ := by rw [hxy]
          _ = y * (c * x * c⁻¹) := by group
      have hneUV : ∃ m ∈ (closure {a₁, b₁} : Subgroup G) ⊔ V, m ∉ V := by
        obtain ⟨m, hm, hmV⟩ := IsConcreteLE.not_le_iff_exists.mp hUnotV
        exact ⟨m, mem_of_le_of_mem le_sup_left hm, hmV⟩
      obtain ⟨x, hxUV, hxV, hxcomm⟩ :=
        y7a_pgroup_fixed hC (hC.to_le hUVC) le_sup_right hMV hCV hCnUV hneUV
      have hxD : x ∈ D := (hDmem x).mpr ⟨hUAV hxUV, hxcomm⟩
      exact y7a_inv_U hrel hz hP3z hU hzV hVD hDinv hUc hUV ⟨x, hxD, hxUV, hxV⟩
  have hAVD : A ⊔ V ≤ D := sup_le hAD hVD
  intro c hc x hx
  exact ((hDmem x).mp (hAVD hx)).2 c hc

end CFSG.OddStandard.HigherRank.YamadaG23
