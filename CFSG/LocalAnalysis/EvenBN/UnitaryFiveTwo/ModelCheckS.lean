module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckZ2

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup CFSG.Fischer Certificates.U52Yamada
open scoped commutatorElement

theorem mem_ZX₁sub_sup_X₃sub_sup_X₄sub_iff {g : SU52} :
    g ∈ ZX₁sub ⊔ X₃sub ⊔ X₄sub ↔ g ∈ Ssub ∧ mat g 2 1 = 0 ∧ mat g 1 0 = 0 := by
  constructor
  · intro hg
    let T : Subgroup SU52 :=
      { carrier := {g | g ∈ Ssub ∧ mat g 2 1 = 0 ∧ mat g 1 0 = 0}
        mul_mem' := fun {g h} ⟨hg, hg0, hg1⟩ ⟨hh, hh0, hh1⟩ =>
          ⟨mul_mem hg hh, by rw [mat_mul_two_one hg hh, hg0, hh0, add_zero],
            by rw [mat_mul_one_zero hg hh, hg1, hh1, add_zero]⟩
        one_mem' := ⟨one_mem _, rfl, rfl⟩
        inv_mem' := fun {g} ⟨hg, hg0, hg1⟩ =>
          ⟨inv_mem hg, inv_entry_eq_zero (by decide) (mat_mul_two_one hg (inv_mem hg)) hg0,
            inv_entry_eq_zero (by decide) (mat_mul_one_zero hg (inv_mem hg)) hg1⟩ }
    have hle : ZX₁sub ⊔ X₃sub ⊔ X₄sub ≤ T := by
      refine sup_le (sup_le ?_ ?_) ?_ <;> intro x hx
      · obtain ⟨a, b, ha, hx'⟩ := mem_x₁Sub.1 hx
        subst ha
        exact ⟨mem_sup_left (mem_sup_left (mem_sup_left (ZX₁sub_le_X₁sub hx))),
          by rw [hx']; rfl, by rw [hx']; rfl⟩
      · obtain ⟨a, hx'⟩ := mem_X₃sub.1 hx
        exact ⟨mem_sup_left (mem_sup_right hx), by rw [hx']; rfl, by rw [hx']; rfl⟩
      · obtain ⟨a, b, hx'⟩ := mem_X₄sub.1 hx
        exact ⟨mem_sup_right hx, by rw [hx']; rfl, by rw [hx']; rfl⟩
    exact hle hg
  · rintro ⟨hg, h0, h1⟩
    obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, k₂, k₁, -, -⟩ :=
      exists_eq_nf_coord hg
    rw [h1] at k₂
    rw [h0] at k₁
    rw [← k₂] at e₂
    rw [← k₁] at e₁
    rw [eq_one_of_x₂ e₂, mul_one]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left (mem_x₁Sub.2 ⟨0, b₁, rfl, e₁⟩)))
      (mem_sup_left (mem_sup_right (mem_X₃sub.2 ⟨a₃, e₃⟩))))
      (mem_sup_right (mem_X₄sub.2 ⟨a₄, b₄, e₄⟩))

theorem entry_commutator_eq_zero {e : SU52 → F4}
    (hadd : ∀ {g h : SU52}, g ∈ Ssub → h ∈ Ssub → e (g * h) = e g + e h)
    {g h : SU52} (hg : g ∈ Ssub) (hh : h ∈ Ssub) : e ⁅g, h⁆ = 0 := by
  have h0 : e 1 = 0 := by
    have := hadd (one_mem Ssub) (one_mem Ssub)
    rw [one_mul] at this
    linear_combination -this
  have hinv : ∀ {x : SU52}, x ∈ Ssub → e x⁻¹ = - e x := fun {x} hx => by
    have h1 := hadd hx (inv_mem hx)
    rw [mul_inv_cancel, h0] at h1
    linear_combination -h1
  rw [commutatorElement_def, hadd (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh),
    hadd (mul_mem hg hh) (inv_mem hg), hadd hg hh, hinv hg, hinv hh]
  ring

theorem ZX₁sub_le_commutator_Ssub : ZX₁sub ≤ ⁅Ssub, Ssub⁆ := by
  have hX₁ : X₁sub ≤ Ssub := le_sup_left.trans (le_sup_left.trans le_sup_left)
  intro g hg
  obtain ⟨a, b, ha, hgm⟩ := mem_x₁Sub.1 hg
  subst ha
  rcases eq_zero_or_one_of_valid b (x₁_coord_rel hgm) with rfl | rfl
  · rw [eq_one_of_x₁ hgm]
    exact one_mem _
  · rw [show g = x₁SU 0 1 zero_one_rel from ext_mat hgm, ← commutator_x₁_x₁_eq]
    exact commutator_mem_commutator (inv_mem (hX₁ (x₁SU_mem _ _ _)))
      (inv_mem (hX₁ (x₁SU_mem _ _ _)))

theorem X₃sub_le_commutator_Ssub : X₃sub ≤ ⁅Ssub, Ssub⁆ := by
  have hX₁ : X₁sub ≤ Ssub := le_sup_left.trans (le_sup_left.trans le_sup_left)
  intro g hg
  obtain ⟨γ, hgm⟩ := mem_X₃sub.1 hg
  obtain ⟨δ, hδ⟩ := exists_valid γ
  have e : g = ⁅(x₁SU 1 F4.ω one_omega_rel)⁻¹, (x₄SU γ δ hδ)⁻¹⁆ := by
    refine ext_mat ?_
    have h := commutator_x₁_x₄ (mat_x₁SU 1 F4.ω one_omega_rel) (mat_x₄SU γ δ hδ)
    rw [map_one, one_mul] at h
    rw [commutatorElement_def, inv_inv, inv_inv, h, hgm]
  rw [e]
  exact commutator_mem_commutator (inv_mem (hX₁ (x₁SU_mem _ _ _)))
    (inv_mem (mem_sup_right (x₄SU_mem _ _ _)))

theorem ZX₄sub_le_commutator_Ssub : ZX₄sub ≤ ⁅Ssub, Ssub⁆ := by
  intro g hg
  obtain ⟨a, b, ha, hgm⟩ := mem_x₄Sub.1 hg
  subst ha
  rcases eq_zero_or_one_of_valid b (x₄_coord_rel hgm) with rfl | rfl
  · rw [show g = 1 from ext_mat (by rw [hgm, x₄Mat_zero, mat_one])]
    exact one_mem _
  · rw [show g = x₄SU 0 1 zero_one_rel from ext_mat hgm, ← commutator_x₂_x₃_eq]
    exact commutator_mem_commutator
      (mem_sup_left (mem_sup_left (mem_sup_right (x₂SU_mem 1))))
      (mem_sup_left (mem_sup_right (x₃SU_mem _)))

theorem X₄sub_le_commutator_Ssub : X₄sub ≤ ⁅Ssub, Ssub⁆ := by
  have hX₁ : X₁sub ≤ Ssub := le_sup_left.trans (le_sup_left.trans le_sup_left)
  intro g hg
  obtain ⟨α, β, hgm⟩ := mem_X₄sub.1 hg
  have hcm : mat ⁅(x₁SU 1 F4.ω one_omega_rel)⁻¹, (x₂SU α)⁻¹⁆ =
      x₃Mat (bar F4.ω * α) * x₄Mat (1 * α) (F4.ω * α * bar α) := by
    rw [commutatorElement_def, inv_inv, inv_inv]
    exact commutator_x₁_x₂ (mat_x₁SU 1 F4.ω one_omega_rel) (mat_x₂SU α)
  have hcS : ⁅(x₁SU 1 F4.ω one_omega_rel)⁻¹, (x₂SU α)⁻¹⁆ ∈ ⁅Ssub, Ssub⁆ :=
    commutator_mem_commutator (inv_mem (hX₁ (x₁SU_mem _ _ _)))
      (inv_mem (mem_sup_left (mem_sup_left (mem_sup_right (x₂SU_mem α)))))
  set y := x₃SU (bar F4.ω * α) * ⁅(x₁SU 1 F4.ω one_omega_rel)⁻¹, (x₂SU α)⁻¹⁆ with hy
  have hym : mat y = x₄Mat α (F4.ω * α * bar α) := by
    rw [hy, mat_mul, mat_x₃SU, hcm, ← Matrix.mul_assoc, x₃Mat_mul, CharTwo.add_self_eq_zero,
      x₃Mat_zero, Matrix.one_mul, one_mul]
  have hyS : y ∈ ⁅Ssub, Ssub⁆ := mul_mem (X₃sub_le_commutator_Ssub (x₃SU_mem _)) hcS
  have hw : y⁻¹ * g ∈ ZX₄sub := by
    refine mem_x₄Sub.2 ⟨α + α, F4.ω * α * bar α + α * bar α + β + bar α * α,
      CharTwo.add_self_eq_zero α, ?_⟩
    rw [mat_mul, mat_inv_of_x₄ hym, hgm, x₄Mat_mul]
  rw [show g = y * (y⁻¹ * g) by group]
  exact mul_mem hyS (ZX₄sub_le_commutator_Ssub hw)

theorem commutator_Ssub : ⁅Ssub, Ssub⁆ = ZX₁sub ⊔ X₃sub ⊔ X₄sub := by
  refine le_antisymm (commutator_le.2 fun g hg h hh => ?_)
    (sup_le (sup_le ZX₁sub_le_commutator_Ssub X₃sub_le_commutator_Ssub)
      X₄sub_le_commutator_Ssub)
  refine mem_ZX₁sub_sup_X₃sub_sup_X₄sub_iff.2 ⟨?_, ?_, ?_⟩
  · rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  · exact entry_commutator_eq_zero (e := fun x => mat x 2 1) (fun hg hh => mat_mul_two_one hg hh)
      hg hh
  · exact entry_commutator_eq_zero (e := fun x => mat x 1 0) (fun hg hh => mat_mul_one_zero hg hh)
      hg hh

theorem commutator_Ssub_eq_X₄sub_sup_Fsub : ⁅Ssub, Ssub⁆ = X₄sub ⊔ Fsub := by
  rw [commutator_Ssub, Fsub]
  refine le_antisymm (sup_le (sup_le ?_ ?_) le_sup_left)
    (sup_le le_sup_right (sup_le (sup_le ?_ ?_) ?_))
  · exact le_sup_left.trans (le_sup_left.trans le_sup_right)
  · exact le_sup_right.trans (le_sup_left.trans le_sup_right)
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact ZX₄sub_le_X₄sub.trans le_sup_right

theorem card_commutator_Ssub : Nat.card (⁅Ssub, Ssub⁆ : Subgroup SU52) = 2 ^ 6 := by
  rw [commutator_Ssub]
  have h := card_of_nf (H := ZX₁sub ⊔ X₃sub ⊔ X₄sub) (Y₂ := ⊥) ZX₁sub_le_X₁sub bot_le le_rfl
    le_rfl
    (fun y₁ hy₁ y₂ hy₂ y₃ hy₃ y₄ hy₄ => by
      rw [Subgroup.mem_bot.1 hy₂, mul_one]
      exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hy₁))
        (mem_sup_left (mem_sup_right hy₃))) (mem_sup_right hy₄))
    (fun g hg => by
      obtain ⟨hgS, h0, h1⟩ := mem_ZX₁sub_sup_X₃sub_sup_X₄sub_iff.1 hg
      obtain ⟨a₁, b₁, a₂, a₃, a₄, b₄, g₁, g₂, g₃, g₄, e₁, e₂, e₃, e₄, rfl, k₂, k₁, -, -⟩ :=
        exists_eq_nf_coord hgS
      rw [h1] at k₂
      rw [h0] at k₁
      rw [← k₂] at e₂
      rw [← k₁] at e₁
      exact ⟨g₁, mem_x₁Sub.2 ⟨0, b₁, rfl, e₁⟩, g₂, Subgroup.mem_bot.2 (eq_one_of_x₂ e₂), g₃,
        mem_X₃sub.2 ⟨a₃, e₃⟩, g₄, mem_X₄sub.2 ⟨a₄, b₄, e₄⟩, rfl⟩)
  rw [h, card_ZX₁sub, Subgroup.card_bot, card_X₃sub, card_X₄sub]
  norm_num

theorem Fsub_le_commutator_Ssub : Fsub ≤ ⁅Ssub, Ssub⁆ := by
  rw [commutator_Ssub, Fsub]
  exact sup_le_sup_left ZX₄sub_le_X₄sub _

theorem commutator_Ssub_le_A₂sub : ⁅Ssub, Ssub⁆ ≤ A₂sub := by
  rw [commutator_Ssub, A₂sub]
  exact sup_le_sup_right (sup_le_sup_right ZX₁sub_le_X₁sub _) _

theorem commutator_Ssub_le_Ssub : ⁅Ssub, Ssub⁆ ≤ Ssub :=
  commutator_Ssub_le_A₂sub.trans A₂sub_le_Ssub

theorem mem_Fsub_of_mem_A₂sub_of_comm_X₄ {s : SU52} (hs : s ∈ A₂sub)
    (h : ∀ y ∈ X₄sub, s * y = y * s) : s ∈ Fsub := by
  obtain ⟨hsS, h10⟩ := mem_A₂sub.1 hs
  obtain ⟨hlow, hdiag⟩ := mem_Ssub.1 hsS
  have e1 : mat s * x₄Mat 1 F4.ω = x₄Mat 1 F4.ω * mat s := by
    have := congrArg mat (h _ (x₄SU_mem 1 F4.ω one_omega_rel))
    rwa [mat_mul, mat_mul, mat_x₄SU] at this
  have e2 : mat s * x₄Mat F4.ω F4.ω = x₄Mat F4.ω F4.ω * mat s := by
    have := congrArg mat (h _ (x₄SU_mem F4.ω F4.ω omega_omega_rel))
    rwa [mat_mul, mat_mul, mat_x₄SU] at this
  have u01 := hlow 0 1 (by decide)
  have d0 := hdiag 0
  have d1 := hdiag 1
  have d4 := hdiag 4
  have a41 : (mat s * x₄Mat 1 F4.ω) 4 1 = (x₄Mat 1 F4.ω * mat s) 4 1 := by rw [e1]
  have a40 : (mat s * x₄Mat 1 F4.ω) 4 0 = (x₄Mat 1 F4.ω * mat s) 4 0 := by rw [e1]
  have b40 : (mat s * x₄Mat F4.ω F4.ω) 4 0 = (x₄Mat F4.ω F4.ω * mat s) 4 0 := by rw [e2]
  simp [Matrix.mul_apply, Fin.sum_univ_five, x₄Mat, u01, d0, d1, d4] at a41 a40 b40
  have m20 : mat s 2 0 = 0 := by linear_combination F4.ω * a40 - b40 - mat s 2 0 * bar_ω
  exact mem_Fsub.2 ⟨hsS, a41, h10, m20⟩

theorem mem_Fsub_of_comm_commutator_Ssub {s : SU52} (hs : s ∈ Ssub)
    (h : ∀ y ∈ ⁅Ssub, Ssub⁆, s * y = y * s) : s ∈ Fsub :=
  mem_Fsub_of_mem_A₂sub_of_comm_X₄
    (mem_A₂sub_of_comm_Fsub hs fun z hz => h z (Fsub_le_commutator_Ssub hz))
    fun y hy => h y (X₄sub_le_commutator_Ssub hy)

theorem Ssub_inf_centralizer_commutator_Ssub :
    Ssub ⊓ centralizer ((⁅Ssub, Ssub⁆ : Subgroup SU52) : Set SU52) = Fsub := by
  refine le_antisymm (fun s hs => ?_)
    (le_inf (Fsub_le_A₂sub.trans A₂sub_le_Ssub) fun f hf => ?_)
  · obtain ⟨hsS, hsC⟩ := mem_inf.1 hs
    exact mem_Fsub_of_comm_commutator_Ssub hsS fun y hy => (mem_centralizer_iff.1 hsC y hy).symm
  · exact mem_centralizer_iff.2 fun y hy => Fsub_comm_A₂ (commutator_Ssub_le_A₂sub hy) hf

theorem Ssub_inf_centralizer_Ssub : Ssub ⊓ centralizer (Ssub : Set SU52) = ZX₄sub := by
  refine le_antisymm (fun s hs => ?_) (le_inf (ZX₄sub_le_X₄sub.trans le_sup_right) fun z hz =>
    mem_centralizer_iff.2 fun g hg => ZX₄sub_comm hz hg)
  obtain ⟨hsS, hsC⟩ := mem_inf.1 hs
  have hc : ∀ g ∈ Ssub, s * g = g * s := fun g hg => (mem_centralizer_iff.1 hsC g hg).symm
  have hX₂ : X₂sub ≤ Ssub := le_sup_right.trans (le_sup_left.trans le_sup_left)
  exact mem_ZX₄sub_of_comm
    (mem_Fsub_of_comm_commutator_Ssub hsS fun y hy => hc y (commutator_Ssub_le_Ssub hy))
    (hc _ (hX₂ (x₂SU_mem 1))) (hc _ (hX₂ (x₂SU_mem F4.ω)))

theorem mat_commutator_two_zero {g s : SU52} (hg : g ∈ Ssub) (hs : s ∈ Ssub) :
    mat ⁅g, s⁆ 2 0 = mat g 2 1 * mat s 1 0 - mat s 2 1 * mat g 1 0 := by
  have hgi := inv_mem hg
  have hsi := inv_mem hs
  have hgs := mul_mem hg hs
  have hgsg := mul_mem hgs hgi
  have f1 := mat_mul_two_zero hg hs
  have f2 := mat_mul_two_zero hgs hgi
  have f3 := mat_mul_two_zero hgsg hsi
  have fg := mat_mul_two_zero hg hgi
  have fs := mat_mul_two_zero hs hsi
  have a1 := mat_mul_two_one hg hs
  have a2 := mat_mul_two_one hgs hgi
  have ag := mat_mul_two_one hg hgi
  have bg := mat_mul_one_zero hg hgi
  rw [mul_inv_cancel, mat_one, Matrix.one_apply_ne (by decide)] at fg fs ag bg
  rw [commutatorElement_def, f3, f2, f1]
  linear_combination -fg - fs + mat g⁻¹ 1 0 * a1 + mat s⁻¹ 1 0 * (a2 + a1 - ag) -
    mat s 2 1 * bg

theorem mem_X₄sub_sup_Fsub_iff {s : SU52} :
    s ∈ X₄sub ⊔ Fsub ↔ s ∈ Ssub ∧ ∀ g ∈ Ssub, g * s * g⁻¹ * s⁻¹ ∈ Fsub := by
  rw [← commutator_Ssub_eq_X₄sub_sup_Fsub, commutator_Ssub, mem_ZX₁sub_sup_X₃sub_sup_X₄sub_iff]
  constructor
  · rintro ⟨hs, h21, h10⟩
    refine ⟨hs, fun g hg => ?_⟩
    have hc : ⁅g, s⁆ ∈ ZX₁sub ⊔ X₃sub ⊔ X₄sub := commutator_Ssub ▸ commutator_mem_commutator hg hs
    obtain ⟨hcS, hc21, hc10⟩ := mem_ZX₁sub_sup_X₃sub_sup_X₄sub_iff.1 hc
    have hc20 := mat_commutator_two_zero hg hs
    rw [h21, h10, mul_zero, zero_mul, sub_zero] at hc20
    exact mem_Fsub.2 ⟨hcS, hc21, hc10, hc20⟩
  · rintro ⟨hs, h⟩
    have hX₁ : x₁SU 1 F4.ω one_omega_rel ∈ Ssub :=
      mem_sup_left (mem_sup_left (mem_sup_left (x₁SU_mem _ _ _)))
    have e1 := (mem_Fsub.1 (h _ (X₂sub_le_Ssub (x₂SU_mem 1)))).2.2.2
    have e2 := (mem_Fsub.1 (h _ hX₁)).2.2.2
    change mat ⁅x₂SU 1, s⁆ 2 0 = 0 at e1
    change mat ⁅x₁SU 1 F4.ω one_omega_rel, s⁆ 2 0 = 0 at e2
    rw [mat_commutator_two_zero (X₂sub_le_Ssub (x₂SU_mem 1)) hs, mat_x₂SU] at e1
    rw [mat_commutator_two_zero hX₁ hs, mat_x₁SU] at e2
    simp [x₂Mat, x₁Mat] at e1 e2
    exact ⟨hs, e1, e2⟩

theorem Ssub_conj_mem_Fsub {s f : SU52} (hs : s ∈ Ssub) (hf : f ∈ Fsub) : s * f * s⁻¹ ∈ Fsub := by
  have hf' : f ∈ X₄sub ⊔ Fsub := mem_sup_right hf
  rw [show s * f * s⁻¹ = s * f * s⁻¹ * f⁻¹ * f by group]
  exact mul_mem ((mem_X₄sub_sup_Fsub_iff.1 hf').2 s hs) hf

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
