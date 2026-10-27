module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.ModelRadicals
public import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.OddStandard.Seitz77
open CFSG.LieType.Chevalley (SL2 uSL vSL HSL WSL)
open scoped commutatorElement

section Unip

variable {K : Type} [Field K]

theorem uelt_commutator (a x y : K) :
    ⁅(uelt a 0 x : unipAll K), uelt 0 1 y⁆ = uelt 0 0 a := by
  rw [commutatorElement_def, uelt_inv, uelt_inv, uelt_mul, uelt_mul, uelt_mul, uelt_inj]
  refine ⟨by ring, by ring, by ring⟩

theorem center_le_of_sup_eq_top {P Q : Subgroup (unipAll K)} (hsup : P ⊔ Q = ⊤)
    (hPZ : P ≤ center (unipAll K)) : center (unipAll K) ≤ Q := by
  have hPn : P.Normal := ⟨fun x hx g => by rw [mem_center_iff.1 (hPZ hx) g]; simpa using hx⟩
  have hlift : ∀ g : unipAll K, ∃ q ∈ Q, coordA q = coordA g ∧ coordB q = coordB g := by
    intro g
    have hg : g ∈ P ⊔ Q := hsup ▸ mem_top g
    rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
    obtain ⟨p, hp, q, hq, rfl⟩ := hg
    obtain ⟨hpa, hpb⟩ := (mem_center_unipAll p).1 (hPZ hp)
    exact ⟨q, hq, by rw [coordA_mul, hpa, zero_add], by rw [coordB_mul, hpb, zero_add]⟩
  intro z hz
  obtain ⟨a, b, c, rfl⟩ := exists_uelt z
  rw [mem_center_unipAll, coordA_uelt, coordB_uelt] at hz
  obtain ⟨rfl, rfl⟩ := hz
  obtain ⟨q₁, hq₁, h1a, h1b⟩ := hlift (uelt c 0 0)
  obtain ⟨q₂, hq₂, h2a, h2b⟩ := hlift (uelt 0 1 0)
  have e : (uelt 0 0 c : unipAll K) = ⁅q₁, q₂⁆ := by
    rw [← uelt_coords q₁, ← uelt_coords q₂, h1a, h1b, h2a, h2b]
    simp only [coordA_uelt, coordB_uelt]
    rw [uelt_commutator]
  rw [e, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hq₁ hq₂) (inv_mem hq₁)) (inv_mem hq₂)

theorem centralizer_le_of_commute {p r : unipAll K} (hr : ¬ (coordA r = 0 ∧ coordB r = 0))
    (hpr : p * r = r * p) : centralizer ({r} : Set (unipAll K)) ≤ centralizer {p} := by
  intro g hg
  rw [mem_centralizer_singleton_iff] at hg ⊢
  have h1 := (commute_unipAll_iff' g r).1 hg
  have h2 := (commute_unipAll_iff' r p).1 hpr.symm
  refine (commute_unipAll_iff' g p).2 ?_
  by_cases hc : coordA r = 0
  · have hd : coordB r ≠ 0 := fun hd => hr ⟨hc, hd⟩
    rw [hc, zero_mul] at h1 h2
    have hx : coordA g = 0 := (mul_eq_zero.1 h1).resolve_right hd
    have ha : coordA p = 0 := (mul_eq_zero.1 h2.symm).resolve_right hd
    rw [hx, ha, zero_mul, zero_mul]
  · refine mul_left_cancel₀ hc ?_
    linear_combination (coordA g) * h2 + (coordA p) * h1

theorem unipAll_eq_bot_or_eq_bot {P Q : Subgroup (unipAll K)}
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) :
    P = ⊥ ∨ Q = ⊥ := by
  have central : ∀ {P Q : Subgroup (unipAll K)}, P ⊓ Q = ⊥ → P ⊔ Q = ⊤ →
      P ≤ center (unipAll K) → P = ⊥ := fun hinf hsup hPZ => by
    have hPQ := hPZ.trans (center_le_of_sup_eq_top hsup hPZ)
    rw [← inf_eq_left.2 hPQ, hinf]
  by_cases hP : ∀ x ∈ P, coordA x = 0 ∧ coordB x = 0
  · exact Or.inl (central hinf hsup fun x hx => (mem_center_unipAll x).2 (hP x hx))
  by_cases hQ : ∀ y ∈ Q, coordA y = 0 ∧ coordB y = 0
  · exact Or.inr (central (by rw [inf_comm, hinf]) (by rw [sup_comm, hsup])
      fun y hy => (mem_center_unipAll y).2 (hQ y hy))
  exfalso
  push Not at hP hQ
  obtain ⟨p, hp, hp0⟩ := hP
  obtain ⟨r, hr, hr0⟩ := hQ
  have hp0' : ¬ (coordA p = 0 ∧ coordB p = 0) := fun h => hp0 h.1 h.2
  have hr0' : ¬ (coordA r = 0 ∧ coordB r = 0) := fun h => hr0 h.1 h.2
  have hle : P ⊔ Q ≤ centralizer {p} := by
    refine sup_le (fun x hx => ?_) fun y hy => mem_centralizer_singleton_iff.2 (hc p hp y hy).symm
    exact centralizer_le_of_commute hr0' (hc p hp r hr)
      (mem_centralizer_singleton_iff.2 (hc x hx r hr))
  rw [hsup] at hle
  refine hp0' (coords_eq_zero_of_commute fun h => ?_)
  exact (mem_centralizer_singleton_iff.1 (hle (mem_top h))).symm

end Unip

namespace Frame

variable {G : Type} [Group G] {A V : Subgroup G} {K : Type} [Field K]

@[expose] noncomputable def ψ (F : Frame A V K) : unipAll K →* G := F.φ.comp (unipEmb K)

theorem ψ_injective (F : Frame A V K) : Function.Injective F.ψ :=
  F.injective.comp unipEmb_injective

theorem ψ_uelt (F : Frame A V K) (a b c : K) :
    F.ψ (uelt a b c) = F.φ (proj 3 K (unipU K a b c)) := rfl

theorem map_top_ψ (F : Frame A V K) : (⊤ : Subgroup (unipAll K)).map F.ψ = V := by
  rw [ψ, ← Subgroup.map_map, map_top_unipEmb, F.map_projUnip]

theorem map_radOne_ψ (F : Frame A V K) : (radOne K).map F.ψ = (projRad K 0).map F.φ := by
  rw [ψ, ← Subgroup.map_map, map_radOne_unipEmb]

theorem map_radTwo_ψ (F : Frame A V K) : (radTwo K).map F.ψ = (projRad K 1).map F.φ := by
  rw [ψ, ← Subgroup.map_map, map_radTwo_unipEmb]

theorem mem_V_iff (F : Frame A V K) {x : G} : x ∈ V ↔ ∃ u, F.ψ u = x := by
  constructor
  · intro hx
    have h : x ∈ (⊤ : Subgroup (unipAll K)).map F.ψ := by rw [F.map_top_ψ]; exact hx
    obtain ⟨u, -, rfl⟩ := h
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    have h : F.ψ u ∈ (⊤ : Subgroup (unipAll K)).map F.ψ := ⟨u, mem_top u, rfl⟩
    rwa [F.map_top_ψ] at h

theorem ψ_mem_V (F : Frame A V K) (u : unipAll K) : F.ψ u ∈ V := F.mem_V_iff.2 ⟨u, rfl⟩

theorem inf_centralizer_V₀ [Finite K] [CharP K 2] (F : Frame A V K) :
    V ⊓ centralizer (((projRad K 0).map F.φ : Subgroup G) : Set G) = (projRad K 0).map F.φ := by
  apply le_antisymm
  · rintro x ⟨hxV, hxC⟩
    obtain ⟨u, rfl⟩ := F.mem_V_iff.1 hxV
    have h1 : F.ψ (uelt 1 0 0) ∈ (projRad K 0).map F.φ := by
      rw [← F.map_radOne_ψ]
      exact ⟨_, (mem_radOne _).2 (coordB_uelt 1 0 0), rfl⟩
    have hu : u ∈ centralizer {(uelt 1 0 0 : unipAll K)} := by
      rw [mem_centralizer_singleton_iff]
      refine F.ψ_injective ?_
      rw [map_mul, map_mul]
      exact (mem_centralizer_iff.1 hxC _ h1).symm
    rw [CFSG.OddStandard.Seitz77.centralizer_radOne (coordB_uelt 1 0 0)
      (by rw [coordA_uelt]; exact one_ne_zero)] at hu
    rw [← F.map_radOne_ψ]
    exact ⟨u, hu, rfl⟩
  · intro x hx
    exact ⟨F.radicals.le₁ hx, mem_centralizer_iff.2 fun y hy =>
      comm_of_isElemAbelian F.radicals.elem₁ hy hx⟩

theorem inf_centralizer_V₁ [Finite K] [CharP K 2] (F : Frame A V K) :
    V ⊓ centralizer (((projRad K 1).map F.φ : Subgroup G) : Set G) = (projRad K 1).map F.φ := by
  apply le_antisymm
  · rintro x ⟨hxV, hxC⟩
    obtain ⟨u, rfl⟩ := F.mem_V_iff.1 hxV
    have h1 : F.ψ (uelt 0 1 0) ∈ (projRad K 1).map F.φ := by
      rw [← F.map_radTwo_ψ]
      exact ⟨_, (mem_radTwo _).2 (coordA_uelt 0 1 0), rfl⟩
    have hu : u ∈ centralizer {(uelt 0 1 0 : unipAll K)} := by
      rw [mem_centralizer_singleton_iff]
      refine F.ψ_injective ?_
      rw [map_mul, map_mul]
      exact (mem_centralizer_iff.1 hxC _ h1).symm
    rw [CFSG.OddStandard.Seitz77.centralizer_radTwo (coordA_uelt 0 1 0)
      (by rw [coordB_uelt]; exact one_ne_zero)] at hu
    rw [← F.map_radTwo_ψ]
    exact ⟨u, hu, rfl⟩
  · intro x hx
    exact ⟨F.radicals.le₂ hx, mem_centralizer_iff.2 fun y hy =>
      comm_of_isElemAbelian F.radicals.elem₂ hy hx⟩

theorem eq_bot_or_eq_bot (F : Frame A V K) {P Q : Subgroup G}
    (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = V) :
    P = ⊥ ∨ Q = ⊥ := by
  have hPV : P ≤ V := hsup ▸ le_sup_left
  have hQV : Q ≤ V := hsup ▸ le_sup_right
  have hP : P = (P.comap F.ψ).map F.ψ := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_map, F.map_top_ψ, inf_eq_right.2 hPV]
  have hQ : Q = (Q.comap F.ψ).map F.ψ := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_map, F.map_top_ψ, inf_eq_right.2 hQV]
  rcases unipAll_eq_bot_or_eq_bot (P := P.comap F.ψ) (Q := Q.comap F.ψ)
      (fun x hx y hy => F.ψ_injective (by rw [map_mul, map_mul]; exact hc _ hx _ hy))
      (by rw [← Subgroup.comap_inf, hinf, MonoidHom.comap_bot,
        (MonoidHom.ker_eq_bot_iff _).2 F.ψ_injective])
      (by
        rw [eq_top_iff]
        intro u _
        have hu : F.ψ u ∈ P ⊔ Q := hsup ▸ F.ψ_mem_V u
        rw [hP, hQ, ← Subgroup.map_sup] at hu
        obtain ⟨v, hv, he⟩ := hu
        rwa [← F.ψ_injective he]) with h | h
  · left
    rw [hP, h, Subgroup.map_bot]
  · right
    rw [hQ, h, Subgroup.map_bot]

section Levi

theorem leviOne_uSL (s : K) : leviOne K (uSL s) = unipU K 0 s 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_leviOne, coe_unipU, CFSG.LieType.Chevalley.coe_uSL]

theorem leviTwo_uSL (s : K) : leviTwo K (uSL s) = unipU K s 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_leviTwo, coe_unipU, CFSG.LieType.Chevalley.coe_uSL]

theorem leviOne_HSL_mul_unipU (l : Kˣ) (a b c : K) :
    leviOne K (HSL l) * unipU K a b c =
      unipU K (((l⁻¹ : Kˣ) : K) * a) ((l : K) ^ 2 * b) ((l : K) * c) * leviOne K (HSL l) := by
  have hl : (l : K) ≠ 0 := l.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_leviOne, coe_unipU, CFSG.LieType.Chevalley.coe_HSL, Matrix.mul_apply,
      Fin.sum_univ_three] <;> field_simp

theorem range_leviTwo : (leviTwo K).range = CFSG.ClassicalInvolution.WeakCT.B12 K := by
  have h : leviTwo K = CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 0 (by omega) := by
    ext B i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_leviTwo, CFSG.ClassicalInvolution.WeakCT.coe_blockSL,
        CFSG.ClassicalInvolution.Phan.blockMat_apply]
  rw [h]
  rfl

theorem range_leviOne : (leviOne K).range = CFSG.ClassicalInvolution.WeakCT.B23 K := by
  have h : leviOne K = CFSG.ClassicalInvolution.WeakCT.blockSL K 3 2 1 (by omega) := by
    ext B i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_leviOne, CFSG.ClassicalInvolution.WeakCT.coe_blockSL,
        CFSG.ClassicalInvolution.Phan.blockMat_apply]
  rw [h]
  rfl

theorem leviOne_leviTwo_braid :
    leviOne K WSL * leviTwo K WSL * leviOne K WSL =
      leviTwo K WSL * leviOne K WSL * leviTwo K WSL := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_leviOne, coe_leviTwo, CFSG.LieType.Chevalley.coe_WSL, Matrix.mul_apply,
      Fin.sum_univ_three]

variable [Finite K] [CharP K 2]

theorem lev_zero_uSL (F : Frame A V K) (s : K) :
    (F.leviData 0).lev (uSL s) = F.ψ (uelt 0 s 0) := by
  rw [Frame.leviData_lev, MonoidHom.comp_apply, leviProj_zero_apply, leviOne_uSL]
  rfl

theorem lev_one_uSL (F : Frame A V K) (s : K) :
    (F.leviData 1).lev (uSL s) = F.ψ (uelt s 0 0) := by
  rw [Frame.leviData_lev, MonoidHom.comp_apply, leviProj_one_apply, leviTwo_uSL]
  rfl

theorem ι_zero_apply (F : Frame A V K) (w : Multiplicative (Fin 2 → K)) :
    (F.leviData 0).ι w =
      F.ψ (uelt (-(Multiplicative.toAdd w) 1) 0 (Multiplicative.toAdd w 0)) := by
  rw [Frame.leviData_ι]
  rfl

theorem ι_one_apply (F : Frame A V K) (w : Multiplicative (Fin 2 → K)) :
    (F.leviData 1).ι w = F.ψ (uelt 0 (Multiplicative.toAdd w 1) (Multiplicative.toAdd w 0)) := by
  rw [Frame.leviData_ι]
  rfl

theorem exists_mul_lev_zero (F : Frame A V K) {v : G} (hv : v ∈ V) :
    ∃ x ∈ (projRad K 0).map F.φ, ∃ s : K, v = x * (F.leviData 0).lev (uSL s) := by
  obtain ⟨u, rfl⟩ := F.mem_V_iff.1 hv
  obtain ⟨a, b, c, rfl⟩ := exists_uelt u
  refine ⟨F.ψ (uelt a 0 (c - a * b)), ?_, b, ?_⟩
  · rw [← F.map_radOne_ψ]
    exact ⟨_, (mem_radOne _).2 (coordB_uelt _ _ _), rfl⟩
  · rw [lev_zero_uSL, ← map_mul, uelt_mul]
    congr 1
    rw [uelt_inj]
    refine ⟨by ring, by ring, by ring⟩

theorem exists_mul_lev_one (F : Frame A V K) {v : G} (hv : v ∈ V) :
    ∃ x ∈ (projRad K 1).map F.φ, ∃ s : K, v = x * (F.leviData 1).lev (uSL s) := by
  obtain ⟨u, rfl⟩ := F.mem_V_iff.1 hv
  obtain ⟨a, b, c, rfl⟩ := exists_uelt u
  refine ⟨F.ψ (uelt 0 b c), ?_, a, ?_⟩
  · rw [← F.map_radTwo_ψ]
    exact ⟨_, (mem_radTwo _).2 (coordA_uelt _ _ _), rfl⟩
  · rw [lev_one_uSL, ← map_mul, uelt_mul]
    congr 1
    rw [uelt_inj]
    refine ⟨by ring, by ring, by ring⟩

theorem exists_mul_lev (F : Frame A V K) (i : Fin 2) {v : G} (hv : v ∈ V) :
    ∃ x ∈ (projRad K i).map F.φ, ∃ s : K, v = x * (F.leviData i).lev (uSL s) :=
  match i with
  | 0 => F.exists_mul_lev_zero hv
  | 1 => F.exists_mul_lev_one hv

theorem lev_uSL_mem_V (F : Frame A V K) (i : Fin 2) (s : K) : (F.leviData i).lev (uSL s) ∈ V :=
  match i with
  | 0 => by rw [lev_zero_uSL]; exact F.ψ_mem_V _
  | 1 => by rw [lev_one_uSL]; exact F.ψ_mem_V _

theorem lev_zero_HSL_conj (F : Frame A V K) (l : Kˣ) (a b c : K) :
    (F.leviData 0).lev (HSL l) * F.ψ (uelt a b c) * ((F.leviData 0).lev (HSL l))⁻¹ =
      F.ψ (uelt (((l⁻¹ : Kˣ) : K) * a) ((l : K) ^ 2 * b) ((l : K) * c)) := by
  rw [Frame.leviData_lev, MonoidHom.comp_apply, ψ_uelt, ψ_uelt, leviProj_zero_apply,
    ← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul, leviOne_HSL_mul_unipU,
    mul_inv_cancel_right]

theorem lev_zero_HSL_conj_mem_V (F : Frame A V K) (l : Kˣ) {v : G} (hv : v ∈ V) :
    (F.leviData 0).lev (HSL l) * v * ((F.leviData 0).lev (HSL l))⁻¹ ∈ V := by
  obtain ⟨u, rfl⟩ := F.mem_V_iff.1 hv
  obtain ⟨a, b, c, rfl⟩ := exists_uelt u
  rw [lev_zero_HSL_conj]
  exact F.ψ_mem_V _

theorem lev_zero_HSL_conj_mem_V₁ (F : Frame A V K) (l : Kˣ) {v : G}
    (hv : v ∈ (projRad K 1).map F.φ) :
    (F.leviData 0).lev (HSL l) * v * ((F.leviData 0).lev (HSL l))⁻¹ ∈ (projRad K 1).map F.φ := by
  rw [← F.map_radTwo_ψ] at hv ⊢
  obtain ⟨u, hu, rfl⟩ := hv
  obtain ⟨a, b, c, rfl⟩ := exists_uelt u
  rw [SetLike.mem_coe, mem_radTwo, coordA_uelt] at hu
  subst hu
  rw [lev_zero_HSL_conj]
  exact ⟨_, (mem_radTwo _).2 (by rw [coordA_uelt, mul_zero]), rfl⟩

theorem eq_one_of_lev_zero_HSL_conj (F : Frame A V K) {l : Kˣ} (hl : (l : K) ≠ 1) {v : G}
    (hv : v ∈ V)
    (hfix : (F.leviData 0).lev (HSL l) * v * ((F.leviData 0).lev (HSL l))⁻¹ = v) : v = 1 := by
  obtain ⟨u, rfl⟩ := F.mem_V_iff.1 hv
  obtain ⟨a, b, c, rfl⟩ := exists_uelt u
  rw [lev_zero_HSL_conj] at hfix
  obtain ⟨ha, hb, hc⟩ := uelt_inj.1 (F.ψ_injective hfix)
  have hl' : ((l⁻¹ : Kˣ) : K) ≠ 1 := fun h => hl (by
    rw [Units.val_inv_eq_inv_val, inv_eq_one] at h; exact h)
  have hl2 : (l : K) ^ 2 ≠ 1 := fun h => hl (by
    have h' : ((l : K) - 1) ^ 2 = 0 := by
      rw [sub_sq, h, mul_one, CharTwo.two_eq_zero, zero_mul, sub_zero, one_pow]
      exact CharTwo.add_self_eq_zero 1
    exact sub_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h'))
  have ha0 : a = 0 := by
    have : (((l⁻¹ : Kˣ) : K) - 1) * a = 0 := by rw [sub_mul, one_mul, ha, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl')
  have hb0 : b = 0 := by
    have : ((l : K) ^ 2 - 1) * b = 0 := by rw [sub_mul, one_mul, hb, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl2)
  have hc0 : c = 0 := by
    have : ((l : K) - 1) * c = 0 := by rw [sub_mul, one_mul, hc, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hl)
  rw [ha0, hb0, hc0, uelt_zero, map_one]

theorem braid (F : Frame A V K) :
    (F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL =
      (F.leviData 1).lev WSL * (F.leviData 0).lev WSL * (F.leviData 1).lev WSL := by
  simp only [Frame.leviData_lev, MonoidHom.comp_apply, leviProj_zero_apply, leviProj_one_apply,
    ← map_mul, leviOne_leviTwo_braid]

theorem sup_lev_range (F : Frame A V K) :
    (F.leviData 0).lev.range ⊔ (F.leviData 1).lev.range = A := by
  have h0 : (F.leviData 0).lev.range = (leviOne K).range.map (F.φ.comp (proj 3 K)) := by
    rw [Frame.leviData_lev, MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
    rfl
  have h1 : (F.leviData 1).lev.range = (leviTwo K).range.map (F.φ.comp (proj 3 K)) := by
    rw [Frame.leviData_lev, MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
    rfl
  rw [h0, h1, ← Subgroup.map_sup, range_leviOne, range_leviTwo, sup_comm,
    CFSG.ClassicalInvolution.WeakCT.B12_sup_B23, ← MonoidHom.range_eq_map,
    MonoidHom.range_comp, MonoidHom.range_eq_top.2 (proj_surjective 3 K), ← MonoidHom.range_eq_map,
    F.range_eq]

end Levi

end Frame

end CFSG.LocalAnalysis.EvenBN.LinearThree
