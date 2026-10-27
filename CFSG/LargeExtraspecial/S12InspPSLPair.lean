module

public import CFSG.LargeExtraspecial.S12InspPSLDec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module Submodule QuadraticMap CFSG.RankThree.OrthogonalInvolutions S12InspPSL

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem psl_polar_eq_zero_of_sing {W : Submodule (ZMod 2) S.Qt} (hW : ∀ w ∈ W, S.q w = 0)
    {v w : S.Qt} (hv : v ∈ W) (hw : w ∈ W) : polar S.q v w = 0 := by
  rw [polar, hW _ (W.add_mem hv hw), hW v hv, hW w hw, sub_zero, sub_zero]

theorem psl_polar_apply_apply (x : S.O) (v w : S.Qt) :
    polar S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) = polar S.q v w :=
  TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup x.2 v w

theorem psl_q_apply (x : S.O) (v : S.Qt) : S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = S.q v :=
  TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup x.2 v

theorem psl_apply_inv_apply (x : S.O) (v : S.Qt) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
  rfl

theorem psl_inv_apply_apply (x : S.O) (v : S.Qt) :
    ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v := by
  rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, inv_mul_cancel]
  rfl

theorem psl_exists_apply_eq_of_lift {g : G} {W : Submodule (ZMod 2) S.Qt}
    (hlift : ∀ (ψ : S.Qt →ₗ[ZMod 2] ZMod 2) (u : S.Qt), u ∈ W → ψ u = 0 →
      ∃ x ∈ S.Xbar12 g, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + ψ w • u)
    {v w : S.Qt} (hv : v ∈ W) (hw : w ∈ W) (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    ∃ x ∈ S.Xbar12 g, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = w := by
  by_cases hvw : v = w
  · exact ⟨1, one_mem _, by rw [hvw]; rfl⟩
  have hv' : v ∉ span (ZMod 2) {w - v} := by
    rw [mem_span_singleton_iff]
    rintro (h | h)
    · exact hv0 h
    · apply hw0
      have : w = v + v := by
        calc w = (w - v) + v := (sub_add_cancel w v).symm
          _ = v + v := by rw [← h]
      rw [this, self_add_self]
  obtain ⟨ψ, hψ, hψv⟩ := exists_functional hv'
  obtain ⟨x, hx, hxw⟩ := hlift ψ (w - v) (W.sub_mem hw hv) (hψ _ (mem_span_singleton_self _))
  refine ⟨x, hx, ?_⟩
  rw [hxw v hv, hψv, one_smul, add_sub_cancel]

theorem psl_sing_of_lift {g : G} {W : Submodule (ZMod 2) S.Qt}
    (hlift : ∀ (ψ : S.Qt →ₗ[ZMod 2] ZMod 2) (u : S.Qt), u ∈ W → ψ u = 0 →
      ∃ x ∈ S.Xbar12 g, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + ψ w • u)
    {c : S.Qt} (hc : c ∈ W) (hc0 : c ≠ 0) (hqc : S.q c = 0) : ∀ w ∈ W, S.q w = 0 := by
  intro w hw
  by_cases hw0 : w = 0
  · rw [hw0, map_zero]
  obtain ⟨x, -, hx⟩ := psl_exists_apply_eq_of_lift hlift hc hw hc0 hw0
  rw [← hx, psl_q_apply, hqc]

theorem psl_finrank_eq_width_of_compl {W W' : Submodule (ZMod 2) S.Qt} (hinf : W ⊓ W' = ⊥)
    (hsup : W ⊔ W' = ⊤) (hdim : finrank (ZMod 2) W = finrank (ZMod 2) W') :
    finrank (ZMod 2) W = S.width := by
  have h := finrank_sup_add_finrank_inf_eq W W'
  rw [hinf, hsup, finrank_bot, finrank_top, S.finrank_Qt_eq_two_mul_width] at h
  omega

theorem psl_mem_of_polar_eq_zero {W : Submodule (ZMod 2) S.Qt} (hW : ∀ w ∈ W, S.q w = 0)
    (hdim : finrank (ZMod 2) W = S.width) {v : S.Qt} (hv : ∀ w ∈ W, polar S.q w v = 0) :
    v ∈ W := by
  have hle : W ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin W := fun u hu =>
    (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun w hw => by
      change polar S.q w u = 0
      exact psl_polar_eq_zero_of_sing hW hw hu
  have hfin := LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate W
  rw [S.finrank_Qt_eq_two_mul_width, hdim] at hfin
  have heq : W = LinearMap.BilinForm.orthogonal S.q.polarBilin W :=
    eq_of_le_of_finrank_eq hle (by rw [hfin, hdim]; omega)
  rw [heq]
  exact (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun w hw => hv w hw

theorem psl_eq_zero_of_polar_compl {W W' : Submodule (ZMod 2) S.Qt} (hW : ∀ w ∈ W, S.q w = 0)
    (hsup : W ⊔ W' = ⊤) {v : S.Qt} (hv : v ∈ W) (h : ∀ w ∈ W', polar S.q v w = 0) : v = 0 := by
  refine S.q_nondegenerate.1 v fun u => ?_
  have hu : u ∈ W ⊔ W' := hsup ▸ mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hu
  change polar S.q v (y + z) = 0
  rw [polar_add_right, psl_polar_eq_zero_of_sing hW hv hy, h z hz, add_zero]

theorem psl_eq_one_of_fix {W W' : Submodule (ZMod 2) S.Qt} (hW : ∀ w ∈ W, S.q w = 0)
    (hdim : finrank (ZMod 2) W = S.width) (hinf : W ⊓ W' = ⊥) (hsup : W ⊔ W' = ⊤) {x : S.O}
    (hxW' : ∀ w ∈ W', (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W')
    (hfix : ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) : x = 1 := by
  have hfix' : ∀ w ∈ W', (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
    intro w' hw'
    have hmem : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w' - w' ∈ W := by
      refine psl_mem_of_polar_eq_zero hW hdim fun w hw => ?_
      rw [polar_sub_right, ← psl_polar_apply_apply x w w', hfix w hw, sub_self]
    have hmem' : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w' - w' ∈ W' := W'.sub_mem (hxW' w' hw') hw'
    have h0 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w' - w' ∈ W ⊓ W' := ⟨hmem, hmem'⟩
    rw [hinf, Submodule.mem_bot, sub_eq_zero] at h0
    exact h0
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ W ⊔ W' := hsup ▸ mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hv
  rw [map_add, hfix y hy, hfix' z hz]
  rfl

theorem psl_fix_of_fix_compl {W W' : Submodule (ZMod 2) S.Qt} (hW : ∀ w ∈ W, S.q w = 0)
    (hsup : W ⊔ W' = ⊤) {x : S.O} (hxW : ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ W)
    (hfix : ∀ w ∈ W', (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) :
    ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w := by
  intro w hw
  rw [← sub_eq_zero]
  refine psl_eq_zero_of_polar_compl hW hsup (W.sub_mem (hxW w hw) hw) fun w' hw' => ?_
  rw [polar_sub_left, ← psl_polar_apply_apply x w w', hfix w' hw', sub_self]

variable (S) in
structure PSLPair (g : G) (t : S.O) where
  W : Submodule (ZMod 2) S.Qt
  W' : Submodule (ZMod 2) S.Qt
  c : S.Qt
  c' : S.Qt
  inf_eq : W ⊓ W' = ⊥
  sup_eq : W ⊔ W' = ⊤
  inv : IsInv (S.actX12 g) W
  inv' : IsInv (S.actX12 g) W'
  sing : ∀ w ∈ W, S.q w = 0
  sing' : ∀ w ∈ W', S.q w = 0
  dim : finrank (ZMod 2) W = S.width
  dim' : finrank (ZMod 2) W' = S.width
  hc : c ∈ W
  hc' : c' ∈ W'
  c_ne : c ≠ 0
  c'_ne : c' ≠ 0
  tW : ∀ w ∈ W, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + polar S.q w c' • c
  tW' : ∀ w ∈ W', (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + polar S.q w c • c'
  lift : ∀ (ψ : S.Qt →ₗ[ZMod 2] ZMod 2) (u : S.Qt), u ∈ W → ψ u = 0 →
    ∃ x ∈ S.Xbar12 g, ∀ w ∈ W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + ψ w • u
  lift' : ∀ (ψ : S.Qt →ₗ[ZMod 2] ZMod 2) (u : S.Qt), u ∈ W' → ψ u = 0 →
    ∃ x ∈ S.Xbar12 g, ∀ w ∈ W', (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w + ψ w • u
  model : Nonempty (S.Xbar12 g ≃* Matrix.SpecialLinearGroup (Fin S.width) (ZMod 2))

namespace PSLPair

variable {g : G} {t : S.O} (P : S.PSLPair g t)

@[expose] def swap : S.PSLPair g t where
  W := P.W'
  W' := P.W
  c := P.c'
  c' := P.c
  inf_eq := by rw [inf_comm]; exact P.inf_eq
  sup_eq := by rw [sup_comm]; exact P.sup_eq
  inv := P.inv'
  inv' := P.inv
  sing := P.sing'
  sing' := P.sing
  dim := P.dim'
  dim' := P.dim
  hc := P.hc'
  hc' := P.hc
  c_ne := P.c'_ne
  c'_ne := P.c_ne
  tW := P.tW'
  tW' := P.tW
  lift := P.lift'
  lift' := P.lift
  model := P.model

theorem apply_mem {x : S.O} (hx : x ∈ S.Xbar12 g) {w : S.Qt} (hw : w ∈ P.W) :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ P.W :=
  P.inv ⟨x, hx⟩ w hw

theorem apply_mem' {x : S.O} (hx : x ∈ S.Xbar12 g) {w : S.Qt} (hw : w ∈ P.W') :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ P.W' :=
  P.inv' ⟨x, hx⟩ w hw

theorem mem_of_polar {v : S.Qt} (hv : ∀ w ∈ P.W, polar S.q w v = 0) : v ∈ P.W :=
  psl_mem_of_polar_eq_zero P.sing P.dim hv

theorem eq_one {x : S.O} (hx : x ∈ S.Xbar12 g)
    (hfix : ∀ w ∈ P.W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) : x = 1 :=
  psl_eq_one_of_fix P.sing P.dim P.inf_eq P.sup_eq (fun _ hw => P.apply_mem' hx hw) hfix

theorem ext {x y : S.O} (hx : x ∈ S.Xbar12 g) (hy : y ∈ S.Xbar12 g)
    (h : ∀ w ∈ P.W, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) w = (y : S.Qt ≃ₗ[ZMod 2] S.Qt) w) : x = y := by
  have h1 := P.eq_one ((S.Xbar12 g).mul_mem ((S.Xbar12 g).inv_mem hx) hy) fun w hw => by
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ← h w hw, psl_inv_apply_apply]
  rw [← mul_inv_cancel_left x y, h1, mul_one]

theorem polar_c_c' : polar S.q P.c P.c' = 0 := by
  rcases zmod2_cases (polar S.q P.c P.c') with h | h
  · exact h
  · exfalso
    have h1 := P.tW P.c P.hc
    rw [h, one_smul, self_add_self, LinearEquiv.map_eq_zero_iff] at h1
    exact P.c_ne h1

theorem exists_polar_c' : ∃ e ∈ P.W, polar S.q e P.c' = 1 := by
  by_contra hcon
  push Not at hcon
  have hmem : P.c' ∈ P.W := P.mem_of_polar fun w hw => by
    rcases zmod2_cases (polar S.q w P.c') with h | h
    · exact h
    · exact absurd h (hcon w hw)
  have h0 : P.c' ∈ P.W ⊓ P.W' := ⟨hmem, P.hc'⟩
  rw [P.inf_eq, Submodule.mem_bot] at h0
  exact P.c'_ne h0

theorem exists_apply_eq {v w : S.Qt} (hv : v ∈ P.W) (hw : w ∈ P.W) (hv0 : v ≠ 0)
    (hw0 : w ≠ 0) : ∃ x ∈ S.Xbar12 g, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = w :=
  psl_exists_apply_eq_of_lift P.lift hv hw hv0 hw0

theorem apply_c'_eq {x : S.O} (hx : x ∈ S.Xbar12 g)
    (h : ∀ w ∈ P.W, polar S.q ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) w) P.c' = polar S.q w P.c') :
    (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' = P.c' := by
  have hmem : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' - P.c' ∈ P.W := by
    refine P.mem_of_polar fun w hw => ?_
    have hxw : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ P.W :=
      P.apply_mem ((S.Xbar12 g).inv_mem hx) hw
    have h1 := psl_polar_apply_apply x (((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w) P.c'
    rw [psl_apply_inv_apply] at h1
    rw [polar_sub_right, h1, ← h _ hxw, psl_apply_inv_apply, sub_self]
  have h0 : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c' - P.c' ∈ P.W ⊓ P.W' :=
    ⟨hmem, P.W'.sub_mem (P.apply_mem' hx P.hc') P.hc'⟩
  rw [P.inf_eq, Submodule.mem_bot, sub_eq_zero] at h0
  exact h0

theorem conj_apply {x : S.O} (hx : x ∈ S.Xbar12 g) {w : S.Qt} (hw : w ∈ P.W) :
    ((x * t * x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w =
      w + polar S.q w ((x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c') • (x : S.Qt ≃ₗ[ZMod 2] S.Qt) P.c := by
  have hxw : ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ P.W :=
    P.apply_mem ((S.Xbar12 g).inv_mem hx) hw
  rw [Subgroup.coe_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    P.tW _ hxw, map_add, map_smul, psl_apply_inv_apply]
  congr 2
  rw [← psl_polar_apply_apply x, psl_apply_inv_apply]

theorem commSpace_eq :
    commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = span (ZMod 2) {P.c, P.c'} := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    have hv : v ∈ P.W ⊔ P.W' := P.sup_eq ▸ mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := mem_sup.mp hv
    change (t : S.Qt ≃ₗ[ZMod 2] S.Qt) (y + z) - (y + z) ∈ _
    rw [map_add, P.tW y hy, P.tW' z hz]
    have e : y + polar S.q y P.c' • P.c + (z + polar S.q z P.c • P.c') - (y + z) =
        polar S.q y P.c' • P.c + polar S.q z P.c • P.c' := by abel
    rw [e]
    exact add_mem (smul_mem _ _ (subset_span (by simp))) (smul_mem _ _ (subset_span (by simp)))
  · rw [span_le]
    rintro _ (rfl | rfl)
    · obtain ⟨e, he, he1⟩ := P.exists_polar_c'
      refine mem_commSpace.mpr ⟨e, ?_⟩
      rw [P.tW e he, he1, one_smul, add_sub_cancel_left]
    · obtain ⟨e, he, he1⟩ := P.swap.exists_polar_c'
      change e ∈ P.W' at he
      change polar S.q e P.c = 1 at he1
      refine mem_commSpace.mpr ⟨e, ?_⟩
      rw [P.tW' e he, he1, one_smul, add_sub_cancel_left]

theorem eq_of_mem_commSpace {v : S.Qt} (hv : v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (hv0 : v ≠ 0) : v = P.c ∨ v = P.c' ∨ v = P.c + P.c' := by
  rw [P.commSpace_eq, mem_span_pair_iff] at hv
  rcases hv with h | h | h | h
  · exact absurd h hv0
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end PSLPair

end Setting

end CFSG.LargeExtraspecial
