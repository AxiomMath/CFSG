module

public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.LinearThree

open Subgroup CFSG.Open
open CFSG.OddStandard.Seitz77 (Datum)
open CFSG.LieType.Chevalley (SL2 uSL vSL HSL WSL)
open scoped commutatorElement

namespace CaseBNotation

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}
  {K : Type} [Field K] {w : WData d Vi q} {D : LeviData A Vi K}

theorem conj_t_apply (d : Datum A) (x : G) : (MulAut.conj d.t).toMonoidHom x = d.t * x * d.t := by
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_eq_of_mul_eq_one_right d.t_mul_self]

theorem t_t_mul (d : Datum A) (x : G) : d.t * (d.t * x) = x := by
  rw [← mul_assoc, d.t_mul_self, one_mul]

theorem t_conj_t (d : Datum A) (x : G) : d.t * (d.t * x * d.t) * d.t = x := by
  simp only [mul_assoc, t_t_mul, d.t_mul_self, mul_one]

theorem comm_t_conj (w : WData d Vi q) {x : G} (hx : x ∈ w.W) :
    d.t * (d.t * x * d.t) * d.t * (d.t * x * d.t)⁻¹ = d.t * x * d.t * x⁻¹ := by
  have htx := conj_t_mem_W w hx
  rw [t_conj_t, inv_eq_self_of_mem_W w htx, inv_eq_self_of_mem_W w hx]
  exact comm_of_isElemAbelian w.elem hx htx

theorem map_conj_W (N : CaseBNotation w D) : w.W.map (MulAut.conj d.t).toMonoidHom = w.W := by
  rw [← N.W₁_sup, Subgroup.map_sup, map_conj_map_conj d.t_mul_self, sup_comm]

theorem tbar_conj_tbar (w : WData d Vi q) (x : w.Nbar) :
    (MulAut.conj w.tbar).toMonoidHom x = w.tbar * x * w.tbar := by
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, CaseBModule.tbar_inv w]

@[expose] noncomputable def swap (N : CaseBNotation w D) : CaseBNotation w D where
  W₁ := N.W₁.map (MulAut.conj d.t).toMonoidHom
  M₁ := N.M₁.map (MulAut.conj d.t).toMonoidHom
  ℓ := (MulAut.conj d.t).toMonoidHom.comp N.ℓ
  W₁_le := N.W₁t_le_W
  W₁_inf := by rw [map_conj_map_conj d.t_mul_self, inf_comm]; exact N.W₁_inf
  W₁_sup := by rw [map_conj_map_conj d.t_mul_self, sup_comm]; exact N.W₁_sup
  card_W₁ := by rw [card_map_of_injective (MulAut.conj d.t).injective]; exact N.card_W₁
  bij := fun v hv => by
    obtain ⟨x₀, ⟨hx₀, hx₀v⟩, huniq⟩ := N.bij v hv
    refine ⟨d.t * x₀ * d.t, ⟨conj_mem_map_conj d.t_mul_self hx₀, ?_⟩, ?_⟩
    · rw [comm_t_conj w (N.W₁_le hx₀), hx₀v]
    · rintro y ⟨hy, hyv⟩
      have hy' : d.t * y * d.t ∈ N.W₁ := (mem_map_conj_iff d.t_mul_self).1 hy
      have h1 := huniq _ ⟨hy', by rw [comm_t_conj w (N.W₁t_le_W hy), hyv]⟩
      rw [← h1, t_conj_t]
  ℓ_injective := (MulAut.conj d.t).injective.comp N.ℓ_injective
  ℓ_mem B := mem_map_of_mem _ (N.ℓ_mem B)
  diag B := by
    rw [MonoidHom.comp_apply, conj_t_apply, t_conj_t, ← N.comm B B, N.diag B]
  comm B B' := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, conj_t_apply, conj_t_apply, t_conj_t]
    exact (N.comm B' B).symm
  cent_W₂ B y hy := by
    rw [map_conj_map_conj d.t_mul_self] at hy
    rw [MonoidHom.comp_apply, conj_t_apply]
    exact N.cent_W₁ B y hy
  nat B x hx := by
    have hx' : d.t * x * d.t ∈ N.W₁ := (mem_map_conj_iff d.t_mul_self).1 hx
    obtain ⟨h1, h2⟩ := N.nat B _ hx'
    have e : (MonoidHom.comp (MulAut.conj d.t).toMonoidHom N.ℓ) B * x *
        ((MonoidHom.comp (MulAut.conj d.t).toMonoidHom N.ℓ) B)⁻¹ =
          d.t * (N.ℓ B * (d.t * x * d.t) * (N.ℓ B)⁻¹) * d.t := by
      rw [MonoidHom.comp_apply, conj_t_apply, mul_inv_rev, mul_inv_rev,
        inv_eq_of_mul_eq_one_right d.t_mul_self]
      simp only [mul_assoc]
    rw [e]
    refine ⟨conj_mem_map_conj d.t_mul_self h1, ?_⟩
    rw [comm_t_conj w (N.W₁_le h1), h2, comm_t_conj w (N.W₁t_le_W hx)]
  cent_W₁ B x hx := by
    rw [MonoidHom.comp_apply, conj_t_apply, t_conj_t]
    exact N.cent_W₂ B x hx
  M₁_le := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hx
    exact mul_mem (mul_mem w.t_norm (N.M₁_le hy)) (inv_mem w.t_norm)
  M₁_inf_W := by
    rw [← N.map_conj_W, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj d.t).injective, N.M₁_inf_W]
  M₁_eq := by rw [MonoidHom.range_comp, ← Subgroup.map_sup, N.M₁_eq]
  W₁_inf_ℓ := by
    rw [MonoidHom.range_comp, ← Subgroup.map_inf_eq _ _ _ (MulAut.conj d.t).injective,
      N.W₁_inf_ℓ, Subgroup.map_bot]
  M₁_inf := by rw [map_conj_map_conj d.t_mul_self, inf_comm]; exact N.M₁_inf
  M₁_comm x hx y hy := by
    rw [map_conj_map_conj d.t_mul_self] at hy
    exact (N.M₁_comm y hy x hx).symm
  σ := (MulAut.conj w.tbar).toMonoidHom.comp N.σ
  ℓ_bar B := by
    obtain ⟨h, hB⟩ := N.ℓ_bar B
    refine ⟨mul_mem (mul_mem w.t_norm h) (inv_mem w.t_norm), ?_⟩
    have e : (⟨((MulAut.conj d.t).toMonoidHom.comp N.ℓ) B,
        mul_mem (mul_mem w.t_norm h) (inv_mem w.t_norm)⟩ : w.N) = w.tN * ⟨N.ℓ B, h⟩ * w.tN⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv, hB, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
  σ_comm B B' := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, tbar_conj_tbar, tbar_conj_tbar,
      conj_tbar_tbar]
    exact (N.σ_comm B' B).symm
  σ_injective := (MulAut.conj w.tbar).injective.comp N.σ_injective
  σ_mem B := by
    have hn : (w.Ebar D.lev.range).Normal := normalClosure_normal
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hn.conj_mem _ (N.σ_mem B) _
  σ_onto x hx := by
    obtain ⟨B, B', h⟩ := N.σ_onto x hx
    refine ⟨B', B, ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, tbar_conj_tbar, tbar_conj_tbar,
      conj_tbar_tbar, ← N.σ_comm B B', h]
  σ_disj B B' h := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, tbar_conj_tbar, tbar_conj_tbar,
      conj_tbar_tbar] at h
    have hB' := N.σ_disj B' B h.symm
    subst hB'
    rw [map_one] at h
    have h' : N.σ B = 1 := by
      rw [← conj_tbar_tbar w (N.σ B), h, mul_one, CaseBModule.tbar_mul_self w]
    exact N.σ_injective (h'.trans (map_one _).symm)
  oddCore_comm := N.oddCore_comm
  M_sup := by
    rw [map_conj_map_conj d.t_mul_self, MonoidHom.range_comp,
      map_conj_map_conj (CaseBModule.tbar_mul_self w), sup_comm, sup_comm (N.σ.range.map _)]
    exact N.M_sup

end CaseBNotation

theorem WSL_conj_uSL {K : Type} [Field K] (s : K) : (WSL * uSL s * WSL⁻¹ : SL2 K) = vSL (-s) := by
  rw [CFSG.LieType.Chevalley.vSL_eq, neg_neg]

theorem WSL_mul_WSL {K : Type} [Field K] [CharP K 2] : (WSL * WSL : SL2 K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.LieType.Chevalley.coe_WSL, Matrix.mul_apply, Fin.sum_univ_two,
      CharTwo.neg_eq]

theorem eq_top_of_uSL_vSL {K : Type} [Field K] {S : Subgroup (SL2 K)}
    (hu : ∀ s, uSL s ∈ S) (hv : ∀ s, vSL s ∈ S) : S = ⊤ := by
  rw [eq_top_iff, ← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower, closure_le]
  rintro _ (⟨s, rfl⟩ | ⟨s, rfl⟩)
  · exact hu s
  · exact hv s

namespace CaseBNotation

section General

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {Vi : Subgroup G} {q : ℕ}
  {K : Type} [Field K] {w : WData d Vi q} {D : LeviData A Vi K}

theorem eq_of_mul_conj_eq (N : CaseBNotation w D) {x y : G} (hx : x ∈ N.M₁) (hy : y ∈ N.M₁)
    (h : x * (d.t * x * d.t) = y * (d.t * y * d.t)) : x = y :=
  congrArg Subtype.val (N.δ_injective (show N.δ ⟨x, hx⟩ = N.δ ⟨y, hy⟩ from h))

theorem lev_conj_eq (N : CaseBNotation w D) (B : SL2 K) {x : G} (hx : x ∈ N.M₁) :
    D.lev B * x * (D.lev B)⁻¹ = N.ℓ B * x * (N.ℓ B)⁻¹ := by
  rw [← N.diag B]
  have hc : (d.t * N.ℓ B * d.t) * x = x * (d.t * N.ℓ B * d.t) :=
    (N.M₁_comm x hx _ (conj_mem_map_conj d.t_mul_self (N.ℓ_mem B))).symm
  calc N.ℓ B * (d.t * N.ℓ B * d.t) * x * (N.ℓ B * (d.t * N.ℓ B * d.t))⁻¹
      = N.ℓ B * ((d.t * N.ℓ B * d.t) * x) * (d.t * N.ℓ B * d.t)⁻¹ * (N.ℓ B)⁻¹ := by group
    _ = N.ℓ B * x * (N.ℓ B)⁻¹ := by rw [hc]; group

theorem lev_conj_mem (N : CaseBNotation w D) (B : SL2 K) {x : G} (hx : x ∈ N.M₁) :
    D.lev B * x * (D.lev B)⁻¹ ∈ N.M₁ := by
  rw [N.lev_conj_eq B hx]
  exact mul_mem (mul_mem (N.ℓ_mem B) hx) (inv_mem (N.ℓ_mem B))

end General

open CFSG.LocalAnalysis.ComponentInitial.FieldFourCover (projRad)
open CFSG.OddStandard.Seitz77 (uelt)

section OfFrameData

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : FrameData A d.V K} {q : ℕ}
  {w₀ : WData d (F.rad 0) q} {w₁ : WData d (F.rad 1) q}
  (N₀ : CaseBNotation w₀ (F.leviData 0)) (N₁ : CaseBNotation w₁ (F.leviData 1))

omit [Finite K] [CharP K 2] in
theorem ℓ_one_mem (hA : N₀.δpre d.V ≤ N₁.M₁) (s : K) : N₁.ℓ (uSL s) ∈ N₀.δpre d.V := by
  obtain ⟨a, ha⟩ := N₀.exists_δ_eq (F.lev_uSL_mem_V 1 s)
  have haA : (a : G) ∈ N₀.δpre d.V :=
    N₀.mem_δpre.2 ⟨a.2, by rw [ha]; exact F.lev_uSL_mem_V 1 s⟩
  have h : (a : G) = N₁.ℓ (uSL s) := N₁.eq_of_mul_conj_eq (hA haA) (N₁.ℓ_mem _)
    (by rw [N₁.diag]; exact ha)
  rw [← h]
  exact haA

omit [Finite K] [CharP K 2] in
theorem δpre_eq [Finite G] (hA : N₀.δpre d.V ≤ N₁.M₁) : N₀.δpre d.V = N₁.δpre d.V := by
  have hle : N₀.δpre d.V ≤ N₁.δpre d.V := fun x hx => by
    obtain ⟨hx0, hδ⟩ := N₀.mem_δpre.1 hx
    exact N₁.mem_δpre.2 ⟨hA hx, hδ⟩
  exact eq_of_le_of_card_ge hle (by
    rw [N₀.card_δpre N₀.le_range_δ, N₁.card_δpre N₁.le_range_δ])

omit [Finite K] [CharP K 2] in
theorem ℓ_zero_mem [Finite G] (hA : N₀.δpre d.V ≤ N₁.M₁) (s : K) :
    N₀.ℓ (uSL s) ∈ N₁.δpre d.V := by
  rw [← N₀.δpre_eq N₁ hA]
  exact N₀.mem_δpre.2 ⟨N₀.ℓ_mem _, by rw [N₀.δ_ℓ]; exact F.lev_uSL_mem_V 0 s⟩

omit [Finite K] [CharP K 2] in
theorem w_conj_ℓ_one [Finite G] (hA : N₀.δpre d.V ≤ N₁.M₁) (s : K) :
    ((F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL) * N₁.ℓ (uSL s) *
      ((F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL)⁻¹ =
        N₀.ℓ (vSL (-s)) := by
  set s₀ := (F.leviData 0).lev WSL with hs₀
  set s₁ := (F.leviData 1).lev WSL with hs₁
  have hs₀t : s₀ * d.t = d.t * s₀ := d.comm_t_of_mem ((F.leviData 0).lev_mem WSL)
  have hs₁t : s₁ * d.t = d.t * s₁ := d.comm_t_of_mem ((F.leviData 1).lev_mem WSL)
  have hA₀M₀ : N₀.δpre d.V ≤ N₀.M₁ := N₀.δpre_le _
  have hx₀ := N₀.ℓ_one_mem N₁ hA s
  have hx₁M : s₀ * N₁.ℓ (uSL s) * s₀⁻¹ ∈ N₀.M₁ := N₀.lev_conj_mem WSL (hA₀M₀ hx₀)
  have hδx₁ : s₀ * N₁.ℓ (uSL s) * s₀⁻¹ * (d.t * (s₀ * N₁.ℓ (uSL s) * s₀⁻¹) * d.t) =
      F.ψ (uelt 0 0 (-s)) := by
    rw [conj_mul_conj_eq hs₀t, N₁.diag, F.lev_one_uSL, F.s_zero_conj_one]
  have hx₁A : s₀ * N₁.ℓ (uSL s) * s₀⁻¹ ∈ N₀.δpre d.V :=
    N₀.mem_δpre.2 ⟨hx₁M, by rw [show N₀.δ ⟨_, hx₁M⟩ = _ from hδx₁]; exact F.ψ_mem_V _⟩
  have hx₂ : s₁ * (s₀ * N₁.ℓ (uSL s) * s₀⁻¹) * s₁⁻¹ = N₀.ℓ (uSL s) := by
    refine N₁.eq_of_mul_conj_eq (N₁.lev_conj_mem WSL (hA hx₁A))
      (N₁.δpre_le _ (N₀.ℓ_zero_mem N₁ hA s)) ?_
    rw [conj_mul_conj_eq hs₁t, hδx₁, F.s_one_conj_three, neg_neg, N₀.diag, F.lev_zero_uSL]
  calc (s₀ * s₁ * s₀) * N₁.ℓ (uSL s) * (s₀ * s₁ * s₀)⁻¹ =
      s₀ * (s₁ * (s₀ * N₁.ℓ (uSL s) * s₀⁻¹) * s₁⁻¹) * s₀⁻¹ := by group
    _ = N₀.ℓ WSL * N₀.ℓ (uSL s) * (N₀.ℓ WSL)⁻¹ := by
        rw [hx₂, N₀.lev_conj_eq WSL (N₀.ℓ_mem _)]
    _ = N₀.ℓ (vSL (-s)) := by rw [← map_inv, ← map_mul, ← map_mul, WSL_conj_uSL]

omit [Finite K] [CharP K 2] in
theorem w_conj_ℓ_zero [Finite G] (hA : N₀.δpre d.V ≤ N₁.M₁) (s : K) :
    ((F.leviData 1).lev WSL * (F.leviData 0).lev WSL * (F.leviData 1).lev WSL) * N₀.ℓ (uSL s) *
      ((F.leviData 1).lev WSL * (F.leviData 0).lev WSL * (F.leviData 1).lev WSL)⁻¹ =
        N₁.ℓ (vSL (-s)) := by
  set s₀ := (F.leviData 0).lev WSL with hs₀
  set s₁ := (F.leviData 1).lev WSL with hs₁
  have hs₀t : s₀ * d.t = d.t * s₀ := d.comm_t_of_mem ((F.leviData 0).lev_mem WSL)
  have hs₁t : s₁ * d.t = d.t * s₁ := d.comm_t_of_mem ((F.leviData 1).lev_mem WSL)
  have hA₀M₀ : N₀.δpre d.V ≤ N₀.M₁ := N₀.δpre_le _
  have hy₀ := N₀.ℓ_zero_mem N₁ hA s
  have hy₁M : s₁ * N₀.ℓ (uSL s) * s₁⁻¹ ∈ N₁.M₁ := N₁.lev_conj_mem WSL (N₁.δpre_le _ hy₀)
  have hδy₁ : s₁ * N₀.ℓ (uSL s) * s₁⁻¹ * (d.t * (s₁ * N₀.ℓ (uSL s) * s₁⁻¹) * d.t) =
      F.ψ (uelt 0 0 s) := by
    rw [conj_mul_conj_eq hs₁t, N₀.diag, F.lev_zero_uSL, F.s_one_conj_two]
  have hy₁A : s₁ * N₀.ℓ (uSL s) * s₁⁻¹ ∈ N₀.δpre d.V := by
    rw [N₀.δpre_eq N₁ hA]
    exact N₁.mem_δpre.2 ⟨hy₁M, by rw [show N₁.δ ⟨_, hy₁M⟩ = _ from hδy₁]; exact F.ψ_mem_V _⟩
  have hy₂ : s₀ * (s₁ * N₀.ℓ (uSL s) * s₁⁻¹) * s₀⁻¹ = N₁.ℓ (uSL s) := by
    refine N₀.eq_of_mul_conj_eq (N₀.lev_conj_mem WSL (hA₀M₀ hy₁A))
      (hA₀M₀ (N₀.ℓ_one_mem N₁ hA s)) ?_
    rw [conj_mul_conj_eq hs₀t, hδy₁, F.s_zero_conj_three, N₁.diag, F.lev_one_uSL]
  calc (s₁ * s₀ * s₁) * N₀.ℓ (uSL s) * (s₁ * s₀ * s₁)⁻¹ =
      s₁ * (s₀ * (s₁ * N₀.ℓ (uSL s) * s₁⁻¹) * s₀⁻¹) * s₁⁻¹ := by group
    _ = N₁.ℓ WSL * N₁.ℓ (uSL s) * (N₁.ℓ WSL)⁻¹ := by
        rw [hy₂, N₁.lev_conj_eq WSL (N₁.ℓ_mem _)]
    _ = N₁.ℓ (vSL (-s)) := by rw [← map_inv, ← map_mul, ← map_mul, WSL_conj_uSL]

section Factor

variable [Finite G]

omit [Finite G] in
theorem commutator_ℓ_range {Vi : Subgroup G} {w : WData d Vi q} {D : LeviData A Vi K}
    (N : CaseBNotation w D) (hK : 3 ≤ Nat.card K) :
    ⁅N.ℓ.range, N.ℓ.range⁆ = N.ℓ.range := by
  obtain ⟨μ, hμ⟩ := exists_unit_ne_one (K := K) hK
  have hperf : commutator (SL2 K) = ⊤ :=
    Matrix.SL2.commutator_eq_top μ.ne_zero (sq_ne_one_of_charTwo hμ)
  rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def, hperf]

omit [Finite G] [Finite K] in
theorem lev_WSL_mul_self (F : FrameData A d.V K) (i : Fin 2) :
    (F.leviData i).lev WSL * (F.leviData i).lev WSL = 1 := by
  rw [← map_mul, WSL_mul_WSL, map_one]

omit [Finite G] [Finite K] in
theorem w_mul_self (F : FrameData A d.V K) :
    ((F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL) *
      ((F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL) = 1 := by
  have h0 := lev_WSL_mul_self F 0
  have h1 := lev_WSL_mul_self F 1
  calc _ = (F.leviData 0).lev WSL * (F.leviData 1).lev WSL *
        ((F.leviData 0).lev WSL * (F.leviData 0).lev WSL) * (F.leviData 1).lev WSL *
          (F.leviData 0).lev WSL := by group
    _ = 1 := by rw [h0, mul_one, mul_assoc ((F.leviData 0).lev WSL), h1, mul_one, h0]

variable (hA : N₀.δpre d.V ≤ N₁.M₁)
include hA

omit [Finite K] in
theorem w_conj_ℓ_one_mem (B : SL2 K) :
    ((F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL) * N₁.ℓ B *
      ((F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL)⁻¹ ∈
        N₀.ℓ.range := by
  set w := (F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL with hw
  have hww : w⁻¹ = w := inv_eq_of_mul_eq_one_right (w_mul_self F)
  have hS : (N₀.ℓ.range.comap ((MulAut.conj w).toMonoidHom.comp N₁.ℓ)) = ⊤ := by
    refine eq_top_of_uSL_vSL (fun s => ?_) (fun s => ?_)
    · exact ⟨vSL (-s), by
        rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          N₀.w_conj_ℓ_one N₁ hA s]⟩
    · refine ⟨uSL (-s), ?_⟩
      have h := N₀.w_conj_ℓ_zero N₁ hA (-s)
      rw [← F.braid, ← hw, neg_neg] at h
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← h, hww,
        show w * (w * N₀.ℓ (uSL (-s)) * w) * w = (w * w) * N₀.ℓ (uSL (-s)) * (w * w) by group,
        w_mul_self F, one_mul, mul_one]
  have hB : B ∈ N₀.ℓ.range.comap ((MulAut.conj w).toMonoidHom.comp N₁.ℓ) := hS ▸ mem_top B
  simpa only [mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    using hB

omit [Finite K] in
theorem w_conj_ℓ_zero_mem (B : SL2 K) :
    ((F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL) * N₀.ℓ B *
      ((F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL)⁻¹ ∈
        N₁.ℓ.range := by
  set w := (F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL with hw
  have hww : w⁻¹ = w := inv_eq_of_mul_eq_one_right (w_mul_self F)
  have hS : (N₁.ℓ.range.comap ((MulAut.conj w).toMonoidHom.comp N₀.ℓ)) = ⊤ := by
    refine eq_top_of_uSL_vSL (fun s => ?_) (fun s => ?_)
    · refine ⟨vSL (-s), ?_⟩
      have h := N₀.w_conj_ℓ_zero N₁ hA s
      rw [← F.braid, ← hw] at h
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, h]
    · refine ⟨uSL (-s), ?_⟩
      have h := N₀.w_conj_ℓ_one N₁ hA (-s)
      rw [← hw, neg_neg] at h
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← h, hww,
        show w * (w * N₁.ℓ (uSL (-s)) * w) * w = (w * w) * N₁.ℓ (uSL (-s)) * (w * w) by group,
        w_mul_self F, one_mul, mul_one]
  have hB : B ∈ N₁.ℓ.range.comap ((MulAut.conj w).toMonoidHom.comp N₀.ℓ) := hS ▸ mem_top B
  simpa only [mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    using hB

omit [Finite K] in
theorem ℓ_zero_comm (B B' : SL2 K) :
    N₀.ℓ B * (d.t * N₁.ℓ B' * d.t) = (d.t * N₁.ℓ B' * d.t) * N₀.ℓ B := by
  set w := (F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL with hw
  have hww : w⁻¹ = w := inv_eq_of_mul_eq_one_right (w_mul_self F)
  have hwt : w * d.t = d.t * w := d.comm_t_of_mem (mul_mem (mul_mem ((F.leviData 0).lev_mem _)
    ((F.leviData 1).lev_mem _)) ((F.leviData 0).lev_mem _))
  set y := d.t * N₁.ℓ B' * d.t with hy
  have hS : (centralizer ({y} : Set G)).comap N₀.ℓ = ⊤ := by
    refine eq_top_of_uSL_vSL (fun s => ?_) (fun s => ?_)
    · rw [mem_comap, mem_centralizer_singleton_iff]
      exact N₁.M₁_comm _ (N₁.δpre_le _ (N₀.ℓ_zero_mem N₁ hA s)) y
        (conj_mem_map_conj d.t_mul_self (N₁.ℓ_mem B'))
    · have h := N₀.w_conj_ℓ_one N₁ hA (-s)
      rw [neg_neg, ← hw] at h
      rw [mem_comap, mem_centralizer_singleton_iff, ← h]
      obtain ⟨B'', hB''⟩ := N₀.w_conj_ℓ_one_mem N₁ hA B'
      rw [← hw] at hB''
      have hy' : w⁻¹ * y * w = d.t * N₀.ℓ B'' * d.t := by
        rw [hB'', hy, hww]
        calc w * (d.t * N₁.ℓ B' * d.t) * w = (w * d.t) * N₁.ℓ B' * (d.t * w) := by group
          _ = (d.t * w) * N₁.ℓ B' * (w * d.t) := by rw [hwt]
          _ = d.t * (w * N₁.ℓ B' * w) * d.t := by group
      have hc : N₁.ℓ (uSL (-s)) * (w⁻¹ * y * w) = (w⁻¹ * y * w) * N₁.ℓ (uSL (-s)) := by
        rw [hy']
        exact N₀.M₁_comm _ (N₀.δpre_le _ (N₀.ℓ_one_mem N₁ hA (-s))) _
          (conj_mem_map_conj d.t_mul_self (N₀.ℓ_mem _))
      calc w * N₁.ℓ (uSL (-s)) * w⁻¹ * y = w * (N₁.ℓ (uSL (-s)) * (w⁻¹ * y * w)) * w⁻¹ := by
            group
        _ = w * ((w⁻¹ * y * w) * N₁.ℓ (uSL (-s))) * w⁻¹ := by rw [hc]
        _ = y * (w * N₁.ℓ (uSL (-s)) * w⁻¹) := by group
  have hB : B ∈ (centralizer ({y} : Set G)).comap N₀.ℓ := hS ▸ mem_top B
  exact mem_centralizer_singleton_iff.1 hB

omit [Finite K] in
theorem ℓ_one_comm (B B' : SL2 K) :
    N₁.ℓ B * (d.t * N₀.ℓ B' * d.t) = (d.t * N₀.ℓ B' * d.t) * N₁.ℓ B := by
  set w := (F.leviData 0).lev WSL * (F.leviData 1).lev WSL * (F.leviData 0).lev WSL with hw
  have hww : w⁻¹ = w := inv_eq_of_mul_eq_one_right (w_mul_self F)
  have hwt : w * d.t = d.t * w := d.comm_t_of_mem (mul_mem (mul_mem ((F.leviData 0).lev_mem _)
    ((F.leviData 1).lev_mem _)) ((F.leviData 0).lev_mem _))
  set y := d.t * N₀.ℓ B' * d.t with hy
  have hS : (centralizer ({y} : Set G)).comap N₁.ℓ = ⊤ := by
    refine eq_top_of_uSL_vSL (fun s => ?_) (fun s => ?_)
    · rw [mem_comap, mem_centralizer_singleton_iff]
      exact N₀.M₁_comm _ (N₀.δpre_le _ (N₀.ℓ_one_mem N₁ hA s)) y
        (conj_mem_map_conj d.t_mul_self (N₀.ℓ_mem B'))
    · have h := N₀.w_conj_ℓ_zero N₁ hA (-s)
      rw [← F.braid, ← hw, neg_neg] at h
      rw [mem_comap, mem_centralizer_singleton_iff, ← h]
      obtain ⟨B'', hB''⟩ := N₀.w_conj_ℓ_zero_mem N₁ hA B'
      rw [← hw] at hB''
      have hy' : w⁻¹ * y * w = d.t * N₁.ℓ B'' * d.t := by
        rw [hB'', hy, hww]
        calc w * (d.t * N₀.ℓ B' * d.t) * w = (w * d.t) * N₀.ℓ B' * (d.t * w) := by group
          _ = (d.t * w) * N₀.ℓ B' * (w * d.t) := by rw [hwt]
          _ = d.t * (w * N₀.ℓ B' * w) * d.t := by group
      have hc : N₀.ℓ (uSL (-s)) * (w⁻¹ * y * w) = (w⁻¹ * y * w) * N₀.ℓ (uSL (-s)) := by
        rw [hy']
        exact N₁.M₁_comm _ (N₁.δpre_le _ (N₀.ℓ_zero_mem N₁ hA (-s))) _
          (conj_mem_map_conj d.t_mul_self (N₁.ℓ_mem _))
      calc w * N₀.ℓ (uSL (-s)) * w⁻¹ * y = w * (N₀.ℓ (uSL (-s)) * (w⁻¹ * y * w)) * w⁻¹ := by
            group
        _ = w * ((w⁻¹ * y * w) * N₀.ℓ (uSL (-s))) * w⁻¹ := by rw [hc]
        _ = y * (w * N₀.ℓ (uSL (-s)) * w⁻¹) := by group
  have hB : B ∈ (centralizer ({y} : Set G)).comap N₁.ℓ := hS ▸ mem_top B
  exact mem_centralizer_singleton_iff.1 hB

omit [Finite G] [Finite K] [CharP K 2] in
open CFSG.OddStandard.Seitz77 (exists_uelt uelt_mul uelt_inj) in
theorem δpre_le_sup : N₀.δpre d.V ≤ N₀.ℓ.range ⊔ N₁.ℓ.range := by
  intro x hx
  obtain ⟨hxM, hδx⟩ := N₀.mem_δpre.1 hx
  obtain ⟨u, hu⟩ := F.mem_V_iff.1 hδx
  obtain ⟨a, b, c, rfl⟩ := exists_uelt u
  have hM : ∀ s, N₁.ℓ (uSL s) ∈ N₀.M₁ := fun s => N₀.δpre_le _ (N₀.ℓ_one_mem N₁ hA s)
  set Y : N₀.M₁ := ⟨N₁.ℓ (uSL a), hM a⟩ * ⟨N₀.ℓ (uSL b), N₀.ℓ_mem _⟩ *
    ⁅(⟨N₁.ℓ (uSL (c - a * b)), hM _⟩ : N₀.M₁), ⟨N₀.ℓ (uSL 1), N₀.ℓ_mem _⟩⁆ with hY
  have hδY : N₀.δ Y = N₀.δ ⟨x, hxM⟩ := by
    have h1 : ∀ s, N₀.δ ⟨N₁.ℓ (uSL s), hM s⟩ = F.ψ (uelt s 0 0) := fun s => by
      rw [← F.lev_one_uSL]
      exact N₁.diag _
    have h0 : ∀ s, N₀.δ ⟨N₀.ℓ (uSL s), N₀.ℓ_mem _⟩ = F.ψ (uelt 0 s 0) := fun s => by
      rw [N₀.δ_ℓ, F.lev_zero_uSL]
    rw [← hu, hY, map_mul, map_mul, map_commutatorElement, h1, h1, h0, h0,
      ← map_commutatorElement, uelt_commutator, ← map_mul, ← map_mul, uelt_mul, uelt_mul]
    congr 1
    rw [uelt_inj]
    refine ⟨by ring, by ring, by ring⟩
  have hYx : (Y : G) = x := congrArg Subtype.val (N₀.δ_injective hδY)
  rw [← hYx, hY]
  have hl1 : ∀ s, N₁.ℓ (uSL s) ∈ N₀.ℓ.range ⊔ N₁.ℓ.range := fun s => mem_sup_right ⟨_, rfl⟩
  have hl0 : ∀ s, N₀.ℓ (uSL s) ∈ N₀.ℓ.range ⊔ N₁.ℓ.range := fun s => mem_sup_left ⟨_, rfl⟩
  simp only [Subgroup.coe_mul, commutatorElement_def, Subgroup.coe_inv]
  exact mul_mem (mul_mem (hl1 a) (hl0 b)) (mul_mem (mul_mem (mul_mem (hl1 _) (hl0 1))
    (inv_mem (hl1 _))) (inv_mem (hl0 1)))

theorem M₁_le_sup : N₀.M₁ ≤ N₀.ℓ.range ⊔ N₁.ℓ.range ∧ N₁.M₁ ≤ N₀.ℓ.range ⊔ N₁.ℓ.range := by
  have hW₀ : N₀.W₁ ≤ N₀.δpre d.V := fun x hx => N₀.mem_δpre.2 ⟨N₀.W₁_le_M₁ hx, by
    rw [N₀.δ_W₁ hx]
    exact F.radicals.le₁ (w₀.comm_mem x (N₀.W₁_le hx))⟩
  have hW₁ : N₁.W₁ ≤ N₁.δpre d.V := fun x hx => N₁.mem_δpre.2 ⟨N₁.W₁_le_M₁ hx, by
    rw [N₁.δ_W₁ hx]
    exact F.radicals.le₂ (w₁.comm_mem x (N₁.W₁_le hx))⟩
  refine ⟨?_, ?_⟩
  · rw [← N₀.M₁_eq]
    exact sup_le (hW₀.trans (N₀.δpre_le_sup N₁ hA)) le_sup_left
  · rw [← N₁.M₁_eq]
    exact sup_le ((hW₁.trans (N₀.δpre_eq N₁ hA).symm.le).trans (N₀.δpre_le_sup N₁ hA))
      le_sup_right

omit [Finite K] in
theorem sup_conj_le_centralizer :
    (N₀.ℓ.range ⊔ N₁.ℓ.range).map (MulAut.conj d.t).toMonoidHom ≤
      centralizer ((N₀.ℓ.range ⊔ N₁.ℓ.range : Subgroup G) : Set G) := by
  have hct : ∀ (ℓ' : SL2 K →* G) (H : Subgroup G),
      (∀ B, ∀ x ∈ H, x * (d.t * ℓ' B * d.t) = (d.t * ℓ' B * d.t) * x) →
      ℓ'.range.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (H : Set G) := by
    rintro ℓ' H h _ ⟨_, ⟨B, rfl⟩, rfl⟩
    rw [conj_t_apply]
    exact mem_centralizer_iff.2 fun x hx => h B x hx
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← le_centralizer_iff]
      exact hct N₀.ℓ _ fun B x ⟨B'', hB''⟩ => hB'' ▸ N₀.comm B'' B
    · rw [← le_centralizer_iff]
      exact hct N₀.ℓ _ fun B x ⟨B'', hB''⟩ => hB'' ▸ N₀.ℓ_one_comm N₁ hA B'' B
  · rw [le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [← le_centralizer_iff]
      exact hct N₁.ℓ _ fun B x ⟨B'', hB''⟩ => hB'' ▸ N₀.ℓ_zero_comm N₁ hA B'' B
    · rw [← le_centralizer_iff]
      exact hct N₁.ℓ _ fun B x ⟨B'', hB''⟩ => hB'' ▸ N₁.comm B'' B

theorem swapFactors_of_le {f : ℕ} (hf : 2 ≤ f) (hKc : Nat.card K = 2 ^ f) :
    CFSG.Open.IsQuasisimple ↥(N₀.ℓ.range ⊔ N₁.ℓ.range) ∧
      (N₀.ℓ.range ⊔ N₁.ℓ.range).map (MulAut.conj d.t).toMonoidHom ≤
        centralizer ((N₀.ℓ.range ⊔ N₁.ℓ.range : Subgroup G) : Set G) ∧
      (∀ x ∈ N₀.ℓ.range ⊔ N₁.ℓ.range, x * (d.t * x * d.t) ∈ A) ∧
      (∀ y ∈ A, ∃ x ∈ N₀.ℓ.range ⊔ N₁.ℓ.range, x * (d.t * x * d.t) = y) ∧
      N₀.M₁ ≤ N₀.ℓ.range ⊔ N₁.ℓ.range ∧ N₁.M₁ ≤ N₀.ℓ.range ⊔ N₁.ℓ.range := by
  set G₁ := N₀.ℓ.range ⊔ N₁.ℓ.range with hG₁
  have hK : 3 ≤ Nat.card K := by
    rw [hKc]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h₁₂ := N₀.sup_conj_le_centralizer N₁ hA
  have hc : ∀ x ∈ G₁, ∀ y ∈ G₁.map (MulAut.conj d.t).toMonoidHom, x * y = y * x :=
    fun x hx y hy => mem_centralizer_iff.1 (h₁₂ hy) x hx
  set δ₁ : G₁ →* G := diagHom d.t_mul_self hc with hδ₁
  have hδ₀ : ∀ B, δ₁ ⟨N₀.ℓ B, mem_sup_left ⟨B, rfl⟩⟩ = (F.leviData 0).lev B := N₀.diag
  have hδ₁' : ∀ B, δ₁ ⟨N₁.ℓ B, mem_sup_right ⟨B, rfl⟩⟩ = (F.leviData 1).lev B := N₁.diag
  have hδA : ∀ x : G₁, δ₁ x ∈ A := by
    have hle : G₁ ≤ (A.comap δ₁).map G₁.subtype := sup_le
      (by
        rintro _ ⟨B, rfl⟩
        exact ⟨⟨_, mem_sup_left ⟨B, rfl⟩⟩, Subgroup.mem_comap.2 (by
          rw [hδ₀]; exact (F.leviData 0).lev_mem B), rfl⟩)
      (by
        rintro _ ⟨B, rfl⟩
        exact ⟨⟨_, mem_sup_right ⟨B, rfl⟩⟩, Subgroup.mem_comap.2 (by
          rw [hδ₁']; exact (F.leviData 1).lev_mem B), rfl⟩)
    intro x
    obtain ⟨y, hy, hyx⟩ := hle x.2
    rw [← Subtype.ext hyx]
    exact hy
  have hsurj : A ≤ δ₁.range := by
    rw [← F.sup_lev_range]
    refine sup_le ?_ ?_
    · rintro _ ⟨B, rfl⟩
      exact ⟨_, hδ₀ B⟩
    · rintro _ ⟨B, rfl⟩
      exact ⟨_, hδ₁' B⟩
  have hperf : ⁅G₁, G₁⁆ = G₁ := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (sup_le ?_ ?_)
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · rw [← N₀.commutator_ℓ_range hK]
      exact commutator_mono le_sup_left le_sup_left
    · rw [← N₁.commutator_ℓ_range hK]
      exact commutator_mono le_sup_right le_sup_right
  let δA : G₁ →* A := δ₁.codRestrict A hδA
  have hδAsurj : Function.Surjective δA := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hsurj hy
    exact ⟨x, Subtype.ext hx⟩
  have hker : δA.ker ≤ center G₁ := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : (x : G) * (d.t * x * d.t) = 1 := congrArg Subtype.val hx
    have hx' : (x : G) = d.t * (x : G)⁻¹ * d.t := by
      calc (x : G) = (d.t * x * d.t)⁻¹ := eq_inv_of_mul_eq_one_left hx1
        _ = d.t⁻¹ * (x : G)⁻¹ * d.t⁻¹ := by group
        _ = d.t * (x : G)⁻¹ * d.t := by rw [inv_eq_of_mul_eq_one_right d.t_mul_self]
    have hmem : (x : G) ∈ centralizer (G₁ : Set G) := by
      rw [hx']
      exact h₁₂ (conj_mem_map_conj d.t_mul_self (inv_mem x.2))
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((mem_centralizer_iff.1 hmem) y y.2)
  have hq : CFSG.Open.IsQuasisimple G₁ := by
    have : Group.IsPerfect G₁ := Subgroup.isPerfect_iff.2 hperf
    exact CFSG.ComponentClassification.CentralExtensions.quasisimple_of_surjective
      F.isQuasisimple δA hδAsurj hker
  obtain ⟨hM₀, hM₁⟩ := N₀.M₁_le_sup N₁ hA
  refine ⟨hq, h₁₂, fun x hx => hδA ⟨x, hx⟩, fun y hy => ?_, hM₀, hM₁⟩
  obtain ⟨x, hx⟩ := hsurj hy
  exact ⟨x, x.2, hx⟩

end Factor

include N₁ in
theorem exists_swapFactors_frameData [Finite G] (hKq : Nat.card K = q) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f) :
    ∃ N₁' : CaseBNotation w₁ (F.leviData 1),
      CFSG.Open.IsQuasisimple ↥(N₀.ℓ.range ⊔ N₁'.ℓ.range) ∧
      (N₀.ℓ.range ⊔ N₁'.ℓ.range).map (MulAut.conj d.t).toMonoidHom ≤
        centralizer ((N₀.ℓ.range ⊔ N₁'.ℓ.range : Subgroup G) : Set G) ∧
      (∀ x ∈ N₀.ℓ.range ⊔ N₁'.ℓ.range, x * (d.t * x * d.t) ∈ A) ∧
      (∀ y ∈ A, ∃ x ∈ N₀.ℓ.range ⊔ N₁'.ℓ.range, x * (d.t * x * d.t) = y) ∧
      N₀.M₁ ≤ N₀.ℓ.range ⊔ N₁'.ℓ.range ∧ N₁'.M₁ ≤ N₀.ℓ.range ⊔ N₁'.ℓ.range := by
  rcases N₀.A_le_or N₁ hKq hf hKc with h | h
  · exact ⟨N₁, N₀.swapFactors_of_le N₁ h hf hKc⟩
  · exact ⟨N₁.swap, N₀.swapFactors_of_le N₁.swap h hf hKc⟩

end OfFrameData

section OfFrame

variable {G : Type} [Group G] {A : Subgroup G} {d : Datum A} {K : Type} [Field K] [Finite K]
  [CharP K 2] {F : Frame A d.V K} {q : ℕ}
  {w₀ : WData d ((projRad K 0).map F.φ) q} {w₁ : WData d ((projRad K 1).map F.φ) q}
  (N₀ : CaseBNotation w₀ (F.leviData 0)) (N₁ : CaseBNotation w₁ (F.leviData 1))

include N₁ in
theorem exists_swapFactors [Finite G] (hKq : Nat.card K = q) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f) :
    ∃ N₁' : CaseBNotation w₁ (F.leviData 1),
      CFSG.Open.IsQuasisimple ↥(N₀.ℓ.range ⊔ N₁'.ℓ.range) ∧
      (N₀.ℓ.range ⊔ N₁'.ℓ.range).map (MulAut.conj d.t).toMonoidHom ≤
        centralizer ((N₀.ℓ.range ⊔ N₁'.ℓ.range : Subgroup G) : Set G) ∧
      (∀ x ∈ N₀.ℓ.range ⊔ N₁'.ℓ.range, x * (d.t * x * d.t) ∈ A) ∧
      (∀ y ∈ A, ∃ x ∈ N₀.ℓ.range ⊔ N₁'.ℓ.range, x * (d.t * x * d.t) = y) ∧
      N₀.M₁ ≤ N₀.ℓ.range ⊔ N₁'.ℓ.range ∧ N₁'.M₁ ≤ N₀.ℓ.range ⊔ N₁'.ℓ.range :=
  exists_swapFactors_frameData (F := F.toFrameData) N₀ N₁ hKq hf hKc

end OfFrame

end CaseBNotation

end CFSG.LocalAnalysis.EvenBN.LinearThree
