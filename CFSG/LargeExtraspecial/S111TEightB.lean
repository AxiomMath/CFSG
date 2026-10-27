module

public import CFSG.LargeExtraspecial.S111TEightA
public import CFSG.LargeExtraspecial.S111BEF
public import CFSG.LargeExtraspecial.S111TNoOdd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial.S4
open CFSG.RankThree.OrthogonalInvolutions

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

theorem perp_le_perp {U V : Submodule (ZMod 2) S.Qt} (h : U ≤ V) : perp S V ≤ perp S U :=
  fun _ hv => mem_perp_iff.mpr fun u hu => mem_perp_iff.mp hv u (h hu)

theorem finrank_le_two_mul_width (U : Submodule (ZMod 2) S.Qt) :
    finrank (ZMod 2) U ≤ 2 * S.width := by
  have := Submodule.finrank_le U
  rwa [S.finrank_Qt_eq_two_mul_width] at this

theorem perp_perp (U : Submodule (ZMod 2) S.Qt) : perp S (perp S U) = U := by
  symm
  refine Submodule.eq_of_le_of_finrank_eq (fun u hu => mem_perp_iff.mpr fun v hv => ?_) ?_
  · rw [polar_comm]
    exact mem_perp_iff.mp hv u hu
  · have h1 := finrank_perp (S := S) U
    have h2 := finrank_perp (S := S) (perp S U)
    have h3 := finrank_le_two_mul_width (S := S) U
    omega

theorem sup_perp_eq_top {W B : Submodule (ZMod 2) S.Qt}
    (hW : ∀ u ∈ W, ∀ v ∈ W, polar S.q u v = 0) (hWn : finrank (ZMod 2) W = S.width)
    (hWB : W ⊓ B = ⊥) : W ⊔ perp S B = ⊤ := by
  have hWW : perp S W = W := by
    symm
    refine Submodule.eq_of_le_of_finrank_eq (fun u hu => mem_perp_iff.mpr fun v hv =>
      hW v hv u hu) ?_
    have := finrank_perp (S := S) W
    omega
  have hbot : perp S (W ⊔ perp S B) = ⊥ := by
    rw [eq_bot_iff, ← hWB]
    intro v hv
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hWW]
      exact perp_le_perp le_sup_left hv
    · rw [← perp_perp B]
      exact perp_le_perp le_sup_right hv
  have h1 := finrank_perp (S := S) (W ⊔ perp S B)
  rw [hbot, finrank_bot] at h1
  have h2 := finrank_le_two_mul_width (S := S) (W ⊔ perp S B)
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [S.finrank_Qt_eq_two_mul_width]
  omega

variable {g : G} {A : Subgroup G} {h k k' : G} {m : S.M}

namespace Pair111

variable (P : Pair111 S g A h k k')
include P

theorem finrank_Wt_of_mem {j : G} (hj : j * S.z * j⁻¹ ∈ A) (hjz : j * S.z * j⁻¹ ≠ S.z) :
    finrank (ZMod 2) (Wt S j) = S.width :=
  finrank_Wt (P.cfg.hy.of_conj (P.cfg.inc.le_QG hj) hjz).cons (P.cfg.inc.le_QG hj) hjz

theorem Wt_inf_clSub' {j : G} (hj : j * S.z * j⁻¹ ∈ A) (hjz : j * S.z * j⁻¹ ≠ S.z) :
    Wt S j ⊓ S.clSub (A.map (MulAut.conj h).toMonoidHom) = ⊥ :=
  Wt_inf_clSub_eq_bot (P.cfg.inc.le_QG hj) hjz (P.inf_Qa_le hj hjz)

theorem Wt_sup_perp_eq_top {j : G} (hj : j * S.z * j⁻¹ ∈ A) (hjz : j * S.z * j⁻¹ ≠ S.z) :
    Wt S j ⊔ perp S (S.clSub (A.map (MulAut.conj h).toMonoidHom)) = ⊤ :=
  sup_perp_eq_top (fun _ hu _ hv => polar_Wt hjz hu hv) (P.finrank_Wt_of_mem hj hjz)
    (P.Wt_inf_clSub' hj hjz)

theorem finrank_Wt_sup (h8 : Nat.card A = 8) {j : G} (hj : j * S.z * j⁻¹ ∈ A)
    (hjz : j * S.z * j⁻¹ ≠ S.z) :
    finrank (ZMod 2) ↥(Wt S j ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom)) =
      S.width + 2 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Wt S j)
    (S.clSub (A.map (MulAut.conj h).toMonoidHom))
  rw [P.Wt_inf_clSub' hj hjz, finrank_bot, add_zero, P.finrank_Wt_of_mem hj hjz,
    P.finrank_clSub' h8] at h1
  exact h1

theorem finrank_Y_le (W : Ord3 S k m) (h8 : Nat.card A = 8) :
    finrank (ZMod 2) ↥((Wt S k ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom)) ⊓
      (Wt S ((m : G) * k) ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom))) ≤ 6 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq
    (Wt S k ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom))
    (Wt S ((m : G) * k) ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom))
  have h2 := P.finrank_Wt_sup h8 P.mem P.ne
  have h3 := P.finrank_Wt_sup h8 (P.mem_A₂ W) (conj_ne_z' S m.2 P.ne)
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq (Wt S k) (Wt S ((m : G) * k))
  have h5 := (Submodule.finrank_mono (W.Wt_inf_le P.cfg P.mem P.ne)).trans
    (P.finrank_clSub h8).le
  have h6 := Submodule.finrank_mono (sup_le_sup
    (le_sup_left : Wt S k ≤ Wt S k ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom))
    (le_sup_left : Wt S ((m : G) * k) ≤
      Wt S ((m : G) * k) ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom)))
  rw [P.finrank_Wt_of_mem P.mem P.ne,
    P.finrank_Wt_of_mem (P.mem_A₂ W) (conj_ne_z' S m.2 P.ne)] at h4
  omega

theorem clSub_sup_le (W : Ord3 S k m) :
    S.clSub A ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom) ≤
      (Wt S k ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom)) ⊓
        (Wt S ((m : G) * k) ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom)) :=
  sup_le (le_inf ((P.cfg.inc.clSub_le_Wt P.mem).trans le_sup_left)
      ((P.cfg.inc.clSub_le_Wt (P.mem_A₂ W)).trans le_sup_left))
    (le_inf le_sup_right le_sup_right)

theorem finrank_clSub_sup (h8 : Nat.card A = 8) :
    finrank (ZMod 2) ↥(S.clSub A ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom)) = 4 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (S.clSub A)
    (S.clSub (A.map (MulAut.conj h).toMonoidHom))
  have h0 : S.clSub A ⊓ S.clSub (A.map (MulAut.conj h).toMonoidHom) = ⊥ := by
    rw [eq_bot_iff, ← P.Wt_inf_clSub' P.mem P.ne]
    exact inf_le_inf_right _ (P.cfg.inc.clSub_le_Wt P.mem)
  rw [h0, finrank_bot, add_zero, P.finrank_clSub h8, P.finrank_clSub' h8] at h1
  exact h1

variable {m : S.M}

theorem apply_sub_mem_Wt_sup (W : Ord3 S k m) (W' : Ord3 S k' m)
    (hc : ∀ n ∈ Ebar S k k' ⊔ Ebar S k' k, n * S.ρ m = S.ρ m * n) (h8 : Nat.card A = 8)
    {f : S.O} (hf : f ∈ Ebar S k' k) {j : G} (hj : j * S.z * j⁻¹ ∈ A)
    (hjz : j * S.z * j⁻¹ ≠ S.z) (v : S.Qt) :
    (f : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈
      Wt S j ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom) := by
  have hv : v ∈ Wt S j ⊔ perp S (S.clSub (A.map (MulAut.conj h).toMonoidHom)) := by
    rw [P.Wt_sup_perp_eq_top hj hjz]
    exact Submodule.mem_top
  obtain ⟨y, hy, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
  have e : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (y + u) - (y + u) =
      ((f : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) + ((f : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) := by
    rw [map_add]
    abel
  rw [e]
  exact Submodule.add_mem_sup (sub_mem (P.apply_mem_Wt_of_mem_F W hc h8 hf hj hjz hy) hy)
    (P.sub_mem_clSub'_of_mem_F W' hc hf hu)

theorem mem_clSub'_cases (W' : Ord3 S k' m) (h8 : Nat.card A = 8) {v : S.Qt}
    (hv : v ∈ S.clSub (A.map (MulAut.conj h).toMonoidHom)) :
    v = 0 ∨ v = S.cl (k' * S.z * k'⁻¹) ∨
      v = ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k' * S.z * k'⁻¹)) ∨
      v = S.cl (k' * S.z * k'⁻¹) +
        ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k' * S.z * k'⁻¹)) := by
  have hbB := S.cl_mem_clSub P.mem' P.memQ'
  have hb0 := cl_conj_z_ne_zero S P.memQ' P.ne'
  refine mem_four (P.card_clSub' h8) hbB (W'.apply_mem_clSub P.swap.cfg P.mem' P.ne' hbB) hb0
    (fun h0 => hb0 ((LinearEquiv.map_eq_zero_iff _).mp h0)) (fun e => ?_) hv
  apply W'.cl_ne P.swap.cfg P.mem' P.ne'
  rw [← ρ_cl_conj_z S m P.memQ']
  exact e.symm

theorem mem_perp_clSub' (W' : Ord3 S k' m) (h8 : Nat.card A = 8) {u : S.Qt}
    (h1 : polar S.q (S.cl (k' * S.z * k'⁻¹)) u = 0)
    (h2 : polar S.q (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k' * S.z * k'⁻¹))) u = 0) :
    u ∈ perp S (S.clSub (A.map (MulAut.conj h).toMonoidHom)) := by
  rw [mem_perp_iff]
  intro c hc
  rcases P.mem_clSub'_cases W' h8 hc with rfl | rfl | rfl | rfl
  · exact polar_zero_left S.q u
  · exact h1
  · exact h2
  · rw [polar_add_left, h1, h2, add_zero]

theorem exists_vec (W' : Ord3 S k' m) :
    ∃ x₀ : S.Qt, polar S.q (S.cl (k' * S.z * k'⁻¹)) x₀ = 0 ∧
      polar S.q (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k' * S.z * k'⁻¹))) x₀ = 1 := by
  have hb0 := cl_conj_z_ne_zero S P.memQ' P.ne'
  have hwb0 : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k' * S.z * k'⁻¹)) ≠ 0 :=
    fun h0 => hb0 ((LinearEquiv.map_eq_zero_iff _).mp h0)
  have hne : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k' * S.z * k'⁻¹)) ≠
      S.cl (k' * S.z * k'⁻¹) := by
    rw [ρ_cl_conj_z S m P.memQ']
    exact W'.cl_ne P.swap.cfg P.mem' P.ne'
  obtain ⟨ℓ, hℓ1, hℓ0⟩ := exists_form_eq_one (p := (ZMod 2) ∙ S.cl (k' * S.z * k'⁻¹))
    (x := ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k' * S.z * k'⁻¹))) (by
      rw [mem_span_cl_iff]
      rintro (e | e)
      · exact hwb0 e
      · exact hne e)
  set x₀ := (LinearMap.BilinForm.toDual S.q.polarBilin S.q_nondegenerate).symm ℓ with hx₀
  have hx : ∀ u, polar S.q x₀ u = ℓ u := fun u => by
    rw [← QuadraticMap.polarBilin_apply_apply]
    exact LinearMap.BilinForm.apply_toDual_symm_apply _ u
  refine ⟨x₀, ?_, ?_⟩
  · rw [polar_comm, hx]
    exact hℓ0 _ (Submodule.mem_span_singleton_self _)
  · rw [polar_comm, hx]
    exact hℓ1

theorem polar_apply_vec (W' : Ord3 S k' m) {x₀ : S.Qt}
    (h1 : polar S.q (S.cl (k' * S.z * k'⁻¹)) x₀ = 0)
    (h2 : polar S.q (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k' * S.z * k'⁻¹))) x₀ = 1) :
    polar S.q (S.cl (k' * S.z * k'⁻¹)) (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀) = 1 ∧
      polar S.q (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k' * S.z * k'⁻¹)))
        (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀) = 0 := by
  set w := ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hw
  set b := S.cl (k' * S.z * k'⁻¹) with hb
  have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (S.ρ m).2
  refine ⟨?_, by rw [hiso, h1]⟩
  have h3 := W'.add_add_eq_zero P.swap.cfg P.mem' P.ne' b
  have hww : w (w b) = b + w b := by
    have := eq_neg_of_add_eq_zero_right h3
    rwa [neg_eq_of_add_eq_zero_right (ZModModule.add_self _)] at this
  have hb3 : w (w (w b)) = b := W'.apply_apply_apply b
  calc polar S.q b (w x₀) = polar S.q (w (w (w b))) (w x₀) := by rw [hb3]
    _ = polar S.q (w (w b)) x₀ := hiso _ _
    _ = 1 := by rw [hww, polar_add_left, h1, h2, zero_add]

theorem exists_decomp (W' : Ord3 S k' m) (h8 : Nat.card A = 8) {x₀ : S.Qt}
    (h1 : polar S.q (S.cl (k' * S.z * k'⁻¹)) x₀ = 0)
    (h2 : polar S.q (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k' * S.z * k'⁻¹))) x₀ = 1)
    (v : S.Qt) :
    ∃ u ∈ perp S (S.clSub (A.map (MulAut.conj h).toMonoidHom)), ∃ c₀ c₁ : ZMod 2,
      v = u + c₁ • x₀ + c₀ • ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ := by
  obtain ⟨h3, h4⟩ := P.polar_apply_vec W' h1 h2
  set w := ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hw
  set b := S.cl (k' * S.z * k'⁻¹) with hb
  set c₀ := polar S.q b v with hc₀
  set c₁ := polar S.q (w b) v with hc₁
  refine ⟨v + c₁ • x₀ + c₀ • w x₀, P.mem_perp_clSub' W' h8 ?_ ?_, c₀, c₁, ?_⟩
  · rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right, h1, h3,
      smul_eq_mul, smul_eq_mul, mul_zero, mul_one, add_zero, ← hc₀]
    exact ZModModule.add_self c₀
  · rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right, h2, h4,
      smul_eq_mul, smul_eq_mul, mul_zero, mul_one, add_zero, ← hc₁]
    exact ZModModule.add_self c₁
  · have e : v + c₁ • x₀ + c₀ • w x₀ + c₁ • x₀ + c₀ • w x₀ =
        v + (c₁ • x₀ + c₁ • x₀) + (c₀ • w x₀ + c₀ • w x₀) := by abel
    rw [e, ZModModule.add_self, ZModModule.add_self, add_zero, add_zero]

theorem mem_clSub'_of_mem_Wt {v : S.Qt}
    (hv : v ∈ S.clSub A ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom)) (hvW : v ∈ Wt S k') :
    v ∈ S.clSub (A.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hbW : b ∈ Wt S k' := (P.cfg.inc.map_conj P.hM).clSub_le_Wt P.mem' hb
  have haW : a ∈ Wt S k' := by
    have := sub_mem hvW hbW
    rwa [add_sub_cancel_right] at this
  have ha0 : a ∈ Wt S k' ⊓ S.clSub A := Submodule.mem_inf.mpr ⟨haW, ha⟩
  rw [Wt_inf_clSub_eq_bot P.memQ' P.ne' P.inf_Qa_le', Submodule.mem_bot] at ha0
  rw [ha0, zero_add]
  exact hb

theorem eq_one_of_comm_mem (W' : Ord3 S k' m)
    (hc : ∀ n ∈ Ebar S k k' ⊔ Ebar S k' k, n * S.ρ m = S.ρ m * n) (h8 : Nat.card A = 8)
    {x₀ : S.Qt} (h1 : polar S.q (S.cl (k' * S.z * k'⁻¹)) x₀ = 0)
    (h2 : polar S.q (((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (k' * S.z * k'⁻¹))) x₀ = 1)
    {f : S.O} (hf : f ∈ Ebar S k' k)
    (hfx : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ∈
      S.clSub A ⊔ S.clSub (A.map (MulAut.conj h).toMonoidHom)) : f = 1 := by
  set B := S.clSub (A.map (MulAut.conj h).toMonoidHom) with hB
  set w := ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) with hw
  have hW : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ∈ Wt S k' := by
    obtain ⟨x, hxQ, rfl⟩ := S.exists_cl x₀
    refine P.hy'.cons.comm_le x (mem_inf.mpr ⟨hxQ, mem_centralizer_singleton_iff.mpr ?_⟩) f hf.1
    rw [polar_comm] at h1
    exact (S.polar_cl_eq_zero_iff hxQ P.memQ').mp h1
  have hB0 := P.mem_clSub'_of_mem_Wt hfx hW
  have hfw : f * S.ρ m = S.ρ m * f := hc f (mem_sup_right hf)
  have hB1 : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (w x₀) - w x₀ ∈ B := by
    have e : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (w x₀) - w x₀ =
        w ((f : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) := by
      rw [map_sub, hw, ← coe_mul_apply, ← coe_mul_apply, hfw]
    rw [e]
    exact W'.apply_mem_clSub P.swap.cfg P.mem' P.ne' hB0
  have hall : ∀ v : S.Qt, (f : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ B := by
    intro v
    obtain ⟨u, hu, c₀, c₁, rfl⟩ := P.exists_decomp W' h8 h1 h2 v
    have e : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) (u + c₁ • x₀ + c₀ • w x₀) - (u + c₁ • x₀ + c₀ • w x₀) =
        ((f : S.Qt ≃ₗ[ZMod 2] S.Qt) u - u) + c₁ • ((f : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) +
          c₀ • ((f : S.Qt ≃ₗ[ZMod 2] S.Qt) (w x₀) - w x₀) := by
      rw [map_add, map_add, map_smul, map_smul, smul_sub, smul_sub]
      abel
    rw [e]
    exact add_mem (add_mem (P.sub_mem_clSub'_of_mem_F W' hc hf hu) (Submodule.smul_mem _ _ hB0))
      (Submodule.smul_mem _ _ hB1)
  have hcomm : commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ B := fun x hx => by
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    exact hall v
  have hq0 : ∀ x ∈ commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt), S.q x = 0 := fun x hx => by
    obtain ⟨y, hy, hyQ, rfl⟩ := S.mem_clSub_iff.mp (hcomm hx)
    exact (S.q_cl_eq_zero_iff hyQ).mpr (by
      rw [pow_two]
      exact (P.cfg.inc.map_conj P.hM).mul_self hy)
  have hff : (f : S.Qt ≃ₗ[ZMod 2] S.Qt) * f = 1 := by
    rw [← Subgroup.coe_mul, mul_self_of_mem_Lbar S P.memQ' hf.1]
    rfl
  have hev := even_finrank_commSpace_of_forall_eq_zero S.q_nondegenerate f.2 hff hq0
  have hle := Submodule.finrank_mono hcomm
  rw [P.finrank_clSub' h8] at hle
  by_contra hf1
  have h0 : finrank (ZMod 2) (commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≠ 0 := by
    intro h0
    apply hf1
    refine Subtype.ext (LinearEquiv.ext fun v => ?_)
    have hv := sub_mem_commSpace (f : S.Qt ≃ₗ[ZMod 2] S.Qt) v
    rw [Submodule.finrank_eq_zero.mp h0, Submodule.mem_bot, sub_eq_zero] at hv
    exact hv
  obtain ⟨y, hyL0, rfl⟩ := (mem_Lbar S).mp hf.1
  have hyQ : (y : G) ∉ S.QG := fun hq => hf1 ((S.ρ_eq_one_iff y).mpr hq)
  apply P.hy'.noA2' y (L0_le_La S k' hyL0) hyQ
  obtain ⟨e, he⟩ := hev
  exact ⟨fun v => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (S.ρ y).2 v,
    fun h1 => hf1 (Subtype.ext h1), hff, by omega, hq0⟩

theorem card_F_le_four (W : Ord3 S k m) (W' : Ord3 S k' m)
    (hc : ∀ n ∈ Ebar S k k' ⊔ Ebar S k' k, n * S.ρ m = S.ρ m * n) (h8 : Nat.card A = 8) :
    Nat.card (Ebar S k' k) ≤ 4 := by
  obtain ⟨x₀, h1, h2⟩ := P.exists_vec W'
  set B := S.clSub (A.map (MulAut.conj h).toMonoidHom) with hB
  set Y := (Wt S k ⊔ B) ⊓ (Wt S ((m : G) * k) ⊔ B) with hY
  set Q' : Submodule (ZMod 2) Y := (S.clSub A ⊔ B).comap Y.subtype with hQ'
  have hmem : ∀ f : Ebar S k' k, ((f : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ∈ Y := fun f =>
    Submodule.mem_inf.mpr ⟨P.apply_sub_mem_Wt_sup W W' hc h8 f.2 P.mem P.ne x₀,
      P.apply_sub_mem_Wt_sup W W' hc h8 f.2 (P.mem_A₂ W) (conj_ne_z' S m.2 P.ne) x₀⟩
  have hfix : ∀ f : Ebar S k' k, ∀ v ∈ S.clSub A ⊔ B,
      ((f : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro f v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, P.fix_clSub_of_mem_F W hc h8 f.2 ha, P.fix_clSub'_of_mem_F W' hc f.2 hb]
  let Φ : Ebar S k' k → Y ⧸ Q' := fun f => Submodule.Quotient.mk ⟨_, hmem f⟩
  have hinj : Function.Injective Φ := by
    intro f f' he
    have he' := (Submodule.Quotient.eq Q').mp he
    rw [hQ', Submodule.mem_comap] at he'
    have hd : ((f : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - ((f' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ ∈
        S.clSub A ⊔ B := by
      have e : (((f : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) -
          (((f' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀) =
          ((f : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - ((f' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ := by
        abel
      rw [← e]
      simpa using he'
    have hg : ((((f' : S.O))⁻¹ * f : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ ∈ S.clSub A ⊔ B := by
      have e : ((((f' : S.O))⁻¹ * f : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - x₀ =
          ((((f' : S.O))⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((f : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - ((f' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀) := by
        rw [coe_mul_apply, map_sub, inv_apply_apply_O]
      have e2 : ((((f' : S.O))⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
          (((f : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - ((f' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀) =
          ((f : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ - ((f' : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x₀ := by
        conv_lhs => rw [← hfix f' _ hd]
        exact inv_apply_apply_O _ _
      rw [e, e2]
      exact hd
    have h3 := P.eq_one_of_comm_mem W' hc h8 h1 h2 (mul_mem (inv_mem f'.2) f.2) hg
    exact Subtype.ext (inv_mul_eq_one.mp h3).symm
  have : Finite (Y ⧸ Q') := Finite.of_surjective _ (Submodule.Quotient.mk_surjective Q')
  have hcard := Nat.card_le_card_of_injective Φ hinj
  have hQfr : finrank (ZMod 2) Q' = 4 := by
    rw [hQ', LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (P.clSub_sup_le W))]
    exact P.finrank_clSub_sup h8
  have hfr := Submodule.finrank_quotient_add_finrank Q'
  have hYfr : finrank (ZMod 2) Y ≤ 6 := P.finrank_Y_le W h8
  have h4 : finrank (ZMod 2) (Y ⧸ Q') ≤ 2 := by omega
  have hQc : Nat.card (Y ⧸ Q') = 2 ^ finrank (ZMod 2) (Y ⧸ Q') := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  calc Nat.card (Ebar S k' k) ≤ Nat.card (Y ⧸ Q') := hcard
    _ = 2 ^ finrank (ZMod 2) (Y ⧸ Q') := hQc
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h4
    _ = 4 := by norm_num

theorem card_Lbar_le_mul (hE : Ebar S k k' ≠ ⊥) :
    Nat.card (S.Lbar k) ≤ Nat.card (Ebar S k k') * Nat.card (Ebar S k k') := by
  have hF : Ebar S k' k ≠ ⊥ := fun h0 => hE (by
    have h1 := P.card_Ebar_eq
    rw [h0, Subgroup.card_bot] at h1
    exact Subgroup.eq_bot_of_card_eq _ h1)
  obtain ⟨⟨f, hf⟩, hf1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF
  have hf1' : f ≠ 1 := fun h1 => hf1 (Subtype.ext h1)
  have hkQ := P.memQ
  have hc : ∀ x ∈ S.Lbar k, f * x⁻¹ * f⁻¹ ∈ S.Lbar k := fun x hx =>
    (mem_normalizer_iff.mp hf.2 x⁻¹).mp (inv_mem hx)
  let θ : S.Lbar k →* S.Lbar k :=
    { toFun := fun x => ⟨(x : S.O) * f * (x : S.O)⁻¹ * f⁻¹, (P.comm_mem_Ebar x.2 hf).1⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => by
        refine Subtype.ext ?_
        change ((x * y : S.Lbar k) : S.O) * f * ((x * y : S.Lbar k) : S.O)⁻¹ * f⁻¹ =
          ((x : S.O) * f * (x : S.O)⁻¹ * f⁻¹) * ((y : S.O) * f * (y : S.O)⁻¹ * f⁻¹)
        rw [Subgroup.coe_mul]
        have hcd := Lbar_comm S hkQ (hc x x.2) (mul_mem y.2 (hc y y.2))
        calc (x : S.O) * y * f * ((x : S.O) * y)⁻¹ * f⁻¹ =
            x * ((y * (f * (y : S.O)⁻¹ * f⁻¹)) * (f * (x : S.O)⁻¹ * f⁻¹)) := by group
          _ = x * ((f * (x : S.O)⁻¹ * f⁻¹) * (y * (f * (y : S.O)⁻¹ * f⁻¹))) := by rw [← hcd]
          _ = x * f * (x : S.O)⁻¹ * f⁻¹ * (y * f * (y : S.O)⁻¹ * f⁻¹) := by group }
  have hker : θ.ker ≤ (Ebar S k k').subgroupOf (S.Lbar k) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : (x : S.O) * f * (x : S.O)⁻¹ * f⁻¹ = 1 := congrArg Subtype.val hx
    rw [mem_subgroupOf]
    by_contra hxE
    apply hf1'
    refine P.eq_one_of_commute x.2 hxE hf ?_
    calc (x : S.O) * f = ((x : S.O) * f * (x : S.O)⁻¹ * f⁻¹) * (f * x) := by group
      _ = f * x := by rw [h1, one_mul]
  have hran : θ.range ≤ (Ebar S k k').subgroupOf (S.Lbar k) := by
    rintro _ ⟨x, rfl⟩
    exact mem_subgroupOf.mpr (P.comm_mem_Ebar x.2 hf)
  have hEc : Nat.card ((Ebar S k k').subgroupOf (S.Lbar k)) = Nat.card (Ebar S k k') :=
    Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range θ
  have h2 := Subgroup.card_le_of_le hker
  have h3 := Subgroup.card_le_of_le hran
  rw [hEc] at h2 h3
  rw [← h1]
  exact Nat.mul_le_mul h2 h3

theorem false_of_ord3 (h6 : 6 ≤ S.width) (W : Ord3 S k m) (W' : Ord3 S k' m)
    (hc : ∀ n ∈ Ebar S k k' ⊔ Ebar S k' k, n * S.ρ m = S.ρ m * n) (h8 : Nat.card A = 8)
    (hE : Ebar S k k' ≠ ⊥) : False := by
  have h1 := P.card_F_le_four W W' hc h8
  have h2 := P.card_Lbar_le_mul hE
  have h3 := P.card_Ebar_eq
  have h4 := P.hy.cons.card_Lbar
  have h5 : 2 ^ 5 ≤ 2 ^ (S.width - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [h3] at h2
  nlinarith

end Pair111

end CFSG.LargeExtraspecial.S11
