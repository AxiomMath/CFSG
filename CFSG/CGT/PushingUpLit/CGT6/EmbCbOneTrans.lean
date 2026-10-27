module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbOneStab
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbApiGrp
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbGraph
import CFSG.CGT.PushingUpLit.CGT6.EmbAltCAp
import CFSG.CGT.PushingUpLit.CGT6.EmbAltCAw
import CFSG.CGT.PushingUpLit.CGT6.EmbCbPerm

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V] {Y X : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ}

namespace CbData

variable (D : CbData Y t m X)

theorem w_mul_mem_commV (hV : ∀ v : V, v ^ 2 = 1) (hodd : Odd m) {c : MulAut V}
    (hn : ∀ x ∈ X, c * x * c⁻¹ ∈ X) {σ : Equiv.Perm (Fin (m + 2))}
    (hσ : ∀ (x : MulAut V) (hx : x ∈ X),
      (D.θ ⟨c * x * c⁻¹, hn x hx⟩ : Equiv.Perm (Fin (m + 2))) =
        σ * (D.θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) * σ⁻¹)
    (hσ2 : σ * σ = 1) (p : Fin (m + 2)) :
    D.w p * D.w (σ p) ∈ commV (Subgroup.zpowers c) := by
  obtain ⟨r, hr⟩ := cbp_exists_fixed_of_involution (hodd.add_even even_two) hσ2
  have hc : ∀ i, c (D.w i) = D.w (σ i) := fun i =>
    wfam_apply_normalizer D.θ D.hwmem D.hwact D.hwuniq hn (cbo_inv_conj_mem hn) hσ i
  have hinv : ∀ i, (D.w i)⁻¹ = D.w i := fun i => inv_eq_of_mul_eq_one_right (D.w_sq hV i)
  have h1 : c (D.w p * D.w r) * (D.w p * D.w r)⁻¹ ∈ commV (Subgroup.zpowers c) :=
    Subgroup.subset_closure ⟨c, Subgroup.mem_zpowers c, _, rfl⟩
  rw [map_mul, hc, hc, hr, mul_inv_rev, hinv, hinv] at h1
  have h2 : D.w (σ p) * D.w r * (D.w r * D.w p) = D.w p * D.w (σ p) := by
    have hrr : D.w r * D.w r = 1 := D.w_sq hV r
    calc D.w (σ p) * D.w r * (D.w r * D.w p) = D.w (σ p) * (D.w r * D.w r) * D.w p := by ac_rfl
      _ = D.w p * D.w (σ p) := by rw [hrr, mul_one, mul_comm]
  rw [h2] at h1
  exact h1

end CbData

namespace OneCfg

variable {G T : Subgroup (MulAut V)} (c : OneCfg G T Y t m X) (D : CbData Y t m X)

include c in
theorem induces_transposition {g : MulAut V} (hg : g ∈ G)
    (hn : ∀ x ∈ X, (g * t * g⁻¹) * x * (g * t * g⁻¹)⁻¹ ∈ X) :
    ∃ p q : Fin (m + 2), p ≠ q ∧ ∀ (x : MulAut V) (hx : x ∈ X),
      (D.θ ⟨(g * t * g⁻¹) * x * (g * t * g⁻¹)⁻¹, hn x hx⟩ : Equiv.Perm (Fin (m + 2))) =
        Equiv.swap p q * (D.θ ⟨x, hx⟩ : Equiv.Perm (Fin (m + 2))) * (Equiv.swap p q)⁻¹ := by
  classical
  have hm : 7 ≤ m := c.hm
  set cc : MulAut V := g * t * g⁻¹ with hcc
  have hcG : cc ∈ G := G.mul_mem (G.mul_mem hg c.htG) (G.inv_mem hg)
  have hc2 : cc ^ 2 = 1 := by rw [hcc, conj_pow, c.ht2]; group
  have hc1 : cc ≠ 1 := by
    intro h1
    apply c.ht1
    have : t = g⁻¹ * cc * g := by rw [hcc]; group
    rw [this, h1]; group
  obtain ⟨σ, hσ⟩ := exists_perm_of_normalizes (by omega : 5 ≤ m + 2) (by omega : m + 2 ≠ 6) D.θ hn
  have hσ2 : σ * σ = 1 := perm_mul_self (by omega) D.θ hn hc2 hσ
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hcent := (perm_eq_one_iff (by omega) D.θ hn hσ).mp h1
    have hcX : cc ∈ Subgroup.centralizer (X : Set (MulAut V)) := by
      rw [Subgroup.mem_centralizer_iff]
      exact fun x hx => (hcent x hx).symm
    exact hc1 (c.cfg.not_involution_centralizer c.hm c.hodd c.hY c.X_le_G c.hX.toCbAlg hcG hcX
      hc2)
  obtain ⟨p, hp⟩ : ∃ p, σ p ≠ p := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (Equiv.ext hcon)
  have hpq : p ≠ σ p := fun h' => hp h'.symm
  have hπ := D.w_mul_mem_commV c.hV c.hodd hn hσ hσ2 p
  have hfixY : ∀ y ∈ Y, (g * y * g⁻¹) (D.w p * D.w (σ p)) = D.w p * D.w (σ p) := by
    intro y hy
    have h1 : D.w p * D.w (σ p) ∈ (commV (Subgroup.zpowers t)).map g.toMonoidHom := by
      rw [← cb_commV_zpowers_conj t g]
      exact hπ
    obtain ⟨v₀, hv₀, hv⟩ := h1
    have hv₀Y : v₀ ∈ fixV Y :=
      c.cfg.commV_zpowers_le_fixV c.hV c.hm c.hodd c.hY c.htT c.ht2 hv₀
    rw [← hv]
    have h2 : (g * y * g⁻¹) (g v₀) = g (y v₀) := by simp [MulAut.mul_apply]
    show (g * y * g⁻¹) (g v₀) = g v₀
    rw [h2, mem_fixV.mp hv₀Y y hy]
  obtain ⟨τ, hτa, hτb⟩ := cbp_exists_alt_pair (by omega : 4 ≤ m + 2) D.hab hpq
  set x₁ : MulAut V := (D.θ.symm τ : MulAut V) with hx₁
  have hx₁X : x₁ ∈ X := (D.θ.symm τ).2
  have hθx₁ : (D.θ ⟨x₁, hx₁X⟩ : Equiv.Perm (Fin (m + 2))) = (τ : Equiv.Perm (Fin (m + 2))) := by
    have : (⟨x₁, hx₁X⟩ : ↥X) = D.θ.symm τ := Subtype.ext rfl
    rw [this, D.θ.apply_symm_apply]
  have hx₁u : x₁ D.u₀ = D.w p * D.w (σ p) := by
    show x₁ (D.w D.a * D.w D.b) = _
    rw [map_mul, D.hwact x₁ hx₁X, D.hwact x₁ hx₁X, hθx₁, hτa, hτb]
  set n : MulAut V := x₁⁻¹ * g with hn_def
  have hnG : n ∈ G := G.mul_mem (G.inv_mem (c.X_le_G hx₁X)) hg
  have hY₂N : ∀ y' ∈ Y.map (MulAut.conj n).toMonoidHom, y' ∈ vecStab G D.u₀ := by
    rintro _ ⟨y, hy, rfl⟩
    refine mem_vecStab.mpr ⟨?_, ?_⟩
    · show n * y * n⁻¹ ∈ G
      exact G.mul_mem (G.mul_mem hnG (c.Y_le_G hy)) (G.inv_mem hnG)
    · have h1 : x₁⁻¹ (D.w p * D.w (σ p)) = D.u₀ := by rw [← hx₁u]; simp
      have h3 : n * y * n⁻¹ = x₁⁻¹ * (g * y * g⁻¹) * x₁ := by rw [hn_def]; group
      show (n * y * n⁻¹) D.u₀ = D.u₀
      rw [h3]
      show x₁⁻¹ ((g * y * g⁻¹) (x₁ D.u₀)) = D.u₀
      rw [hx₁u, hfixY y hy, h1]
  obtain ⟨ε⟩ := c.hY
  let e₂ : ↥(Y.map (MulAut.conj n).toMonoidHom) ≃* alternatingGroup (Fin m) :=
    (MulEquiv.subgroupMap (MulAut.conj n) Y).symm.trans ε
  have hY₂G : Y.map (MulAut.conj n).toMonoidHom ≤ G := fun y hy => (mem_vecStab.mp (hY₂N y hy)).1
  have hY₂eq : Y.map (MulAut.conj n).toMonoidHom = Y := by
    refine cbo_eq_of_normalizes c.hm (Gr := G) (Y₁ := Y) c.Y_le_G hY₂G ε e₂
      (fun y hy z hz => c.vecStab_normalizes_Y D (hY₂N y hy) z hz) ?_
    intro a b haG hbG ha hb ha2 hb2 ha1 hb1 hab hcomm
    exact c.h2 V c.hV G T Y c.cfg m c.hm c.hodd ⟨ε⟩ a b haG hbG
      (Subgroup.mem_centralizer_iff.mpr fun z hz => (ha z hz).symm)
      (Subgroup.mem_centralizer_iff.mpr fun z hz => (hb z hz).symm) ha2 hb2 ha1 hb1 hab hcomm
  have hcomm : ∀ ρ : alternatingGroup (Fin (m + 2)), ρ ∈ altStabilizer (m + 2) {p, σ p} →
      σ * (ρ : Equiv.Perm (Fin (m + 2))) = (ρ : Equiv.Perm (Fin (m + 2))) * σ := by
    intro ρ hρ
    rw [mem_altStabilizer_iff] at hρ
    have hρp : (ρ : Equiv.Perm (Fin (m + 2))) p = p := hρ p (by simp)
    have hρq : (ρ : Equiv.Perm (Fin (m + 2))) (σ p) = σ p := hρ (σ p) (by simp)
    have hρ' : τ⁻¹ * ρ * τ ∈ altStabilizer (m + 2) {D.a, D.b} := by
      rw [mem_altStabilizer_iff]
      intro i hi
      have hi' : i = D.a ∨ i = D.b := by simpa using hi
      rcases hi' with rfl | rfl
      · show ((τ : Equiv.Perm (Fin (m + 2)))⁻¹ * (ρ : Equiv.Perm (Fin (m + 2))) *
          (τ : Equiv.Perm (Fin (m + 2)))) D.a = D.a
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτa, hρp]
        exact (Equiv.Perm.inv_eq_iff_eq.mpr hτa.symm)
      · show ((τ : Equiv.Perm (Fin (m + 2)))⁻¹ * (ρ : Equiv.Perm (Fin (m + 2))) *
          (τ : Equiv.Perm (Fin (m + 2)))) D.b = D.b
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτb, hρq]
        exact (Equiv.Perm.inv_eq_iff_eq.mpr hτb.symm)
    have hρ'' : τ⁻¹ * ρ * τ ∈ (Y.subgroupOf X).map D.θ.toMonoidHom := by
      rw [D.hstab]; exact hρ'
    obtain ⟨u, hu, hθu⟩ := hρ''
    have huY : (u : MulAut V) ∈ Y := hu
    have huY' : (u : MulAut V) ∈ Y.map (MulAut.conj n).toMonoidHom := by rw [hY₂eq]; exact huY
    obtain ⟨y₀, hy₀, hy₀u⟩ := huY'
    have hxg : x₁ * (u : MulAut V) * x₁⁻¹ = g * y₀ * g⁻¹ := by
      rw [← hy₀u]
      show x₁ * (n * y₀ * n⁻¹) * x₁⁻¹ = g * y₀ * g⁻¹
      rw [hn_def]; group
    have hx' : x₁ * (u : MulAut V) * x₁⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem hx₁X u.2) (X.inv_mem hx₁X)
    have hccx : cc * (x₁ * (u : MulAut V) * x₁⁻¹) * cc⁻¹ = x₁ * (u : MulAut V) * x₁⁻¹ := by
      rw [hxg, hcc]
      have ht := c.t_cent y₀ hy₀
      calc g * t * g⁻¹ * (g * y₀ * g⁻¹) * (g * t * g⁻¹)⁻¹
          = g * (t * y₀) * t⁻¹ * g⁻¹ := by group
        _ = g * (y₀ * t) * t⁻¹ * g⁻¹ := by rw [ht]
        _ = g * y₀ * g⁻¹ := by group
    have h1 := hσ _ hx'
    have hθx : D.θ ⟨x₁ * (u : MulAut V) * x₁⁻¹, hx'⟩ = ρ := by
      have h2 : (⟨x₁ * (u : MulAut V) * x₁⁻¹, hx'⟩ : ↥X) = ⟨x₁, hx₁X⟩ * u * ⟨x₁, hx₁X⟩⁻¹ := rfl
      have h3 : D.θ ⟨x₁, hx₁X⟩ = τ := by
        have : (⟨x₁, hx₁X⟩ : ↥X) = D.θ.symm τ := Subtype.ext rfl
        rw [this, D.θ.apply_symm_apply]
      rw [h2, map_mul, map_mul, map_inv, h3]
      have h4 : D.θ u = τ⁻¹ * ρ * τ := hθu
      rw [h4]
      group
    have h5 : (⟨cc * (x₁ * (u : MulAut V) * x₁⁻¹) * cc⁻¹, hn _ hx'⟩ : ↥X) =
        ⟨x₁ * (u : MulAut V) * x₁⁻¹, hx'⟩ := Subtype.ext hccx
    rw [h5, hθx] at h1
    have h6 : σ * (ρ : Equiv.Perm (Fin (m + 2))) = (ρ : Equiv.Perm (Fin (m + 2))) * σ := by
      calc σ * (ρ : Equiv.Perm (Fin (m + 2)))
          = σ * (ρ : Equiv.Perm (Fin (m + 2))) * σ⁻¹ * σ := by group
        _ = (ρ : Equiv.Perm (Fin (m + 2))) * σ := by rw [← h1]
    exact h6
  have hswap : σ = 1 ∨ σ = Equiv.swap p (σ p) :=
    cbp_eq_one_or_swap (by omega : 7 ≤ m + 2) hpq hcomm
  rcases hswap with h1 | h1
  · exact absurd h1 hσ1
  · refine ⟨p, σ p, hpq, fun x hx => ?_⟩
    rw [hσ x hx, ← h1]

end OneCfg

end CFSG.CGT.PushingUpLit.CGT6
