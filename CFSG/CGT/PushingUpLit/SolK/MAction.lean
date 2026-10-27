module

public import CFSG.CGT.PushingUpLit.SolK.QStruct

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] {M X : Subgroup G} {n : ℕ} (D : ModData G X n)

theorem ModData.exists_perm_of_normalizing (hn : 2 ≤ n) (γ : MulAut ↥(coreMod (2 * n + 1)))
    (hγ : ∀ x : ↥X, ∃ x' : ↥X, ∀ v, γ (coreAct (2 * n + 1) (D.ρ x) v) =
      coreAct (2 * n + 1) (D.ρ x') (γ v))
    (hγ' : ∀ x' : ↥X, ∃ x : ↥X, ∀ v, γ (coreAct (2 * n + 1) (D.ρ x) v) =
      coreAct (2 * n + 1) (D.ρ x') (γ v)) :
    ∃ π : Perm (Fin (2 * n + 1)), ∀ v, γ v = coreAct (2 * n + 1) π v := by
  have hd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hd5 : 5 ≤ 2 * n + 1 := by omega
  refine exists_perm_of_normalizes_alt hd hd5 γ (fun σ hσ => ?_) (fun σ' hσ' => ?_)
  · obtain ⟨x, hx⟩ := D.ρ_surj σ hσ
    obtain ⟨x', hx'⟩ := hγ x
    exact ⟨D.ρ x', D.ρ_alt x', by rw [← hx]; exact hx'⟩
  · obtain ⟨x', hx'⟩ := D.ρ_surj σ' hσ'
    obtain ⟨x, hx⟩ := hγ' x'
    exact ⟨D.ρ x, D.ρ_alt x, by rw [← hx']; exact hx⟩

namespace XNorm

variable {D} (h : XNorm M X)
include h

@[expose] noncomputable def conjW {m : G} (hm : m ∈ M) : MulAut ↥D.W where
  toFun w := ⟨m * (w : G) * m⁻¹, W_normalized h hm w.2⟩
  invFun w := ⟨m⁻¹ * (w : G) * m, by
    have := W_normalized h (M.inv_mem hm) w.2
    simpa using this⟩
  left_inv w := Subtype.ext (by simp [mul_assoc])
  right_inv w := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem exists_perm_of_mem (hn : 2 ≤ n) {m : G} (hm : m ∈ M) :
    ∃ π : Perm (Fin (2 * n + 1)), ∀ (w : ↥D.W) (hw' : m * (w : G) * m⁻¹ ∈ D.W),
      D.β ⟨m * (w : G) * m⁻¹, hw'⟩ = coreAct (2 * n + 1) π (D.β w) := by
  classical
  let γ : MulAut ↥(coreMod (2 * n + 1)) := (D.β.symm.trans (conjW h hm)).trans D.β
  have hγ : ∀ w : ↥D.W, γ (D.β w) = D.β (conjW h hm w) := fun w => by simp [γ]
  have key : ∀ {m : G} (hm : m ∈ M) (x x' : ↥X), (x' : G) = m * (x : G) * m⁻¹ →
      ∀ v, ((D.β.symm.trans (conjW h hm)).trans D.β) (coreAct (2 * n + 1) (D.ρ x) v) =
        coreAct (2 * n + 1) (D.ρ x') (((D.β.symm.trans (conjW h hm)).trans D.β) v) := by
    intro m hm x x' hx' v
    obtain ⟨w, rfl⟩ := D.β.surjective v
    have hxW : (x : G) * (w : G) * (x : G)⁻¹ ∈ D.W := W_normalized h (h.le x.2) w.2
    have hmwW : m * (w : G) * m⁻¹ ∈ D.W := W_normalized h hm w.2
    have hx'W : (x' : G) * (m * (w : G) * m⁻¹) * (x' : G)⁻¹ ∈ D.W :=
      W_normalized h (h.le x'.2) hmwW
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [← D.equivar x w hxW]
    simp only [MulEquiv.symm_apply_apply]
    show D.β (conjW h hm ⟨(x : G) * (w : G) * (x : G)⁻¹, hxW⟩) =
      coreAct (2 * n + 1) (D.ρ x') (D.β ⟨m * (w : G) * m⁻¹, hmwW⟩)
    rw [← D.equivar x' ⟨m * (w : G) * m⁻¹, hmwW⟩ hx'W]
    congr 1
    refine Subtype.ext ?_
    show m * ((x : G) * (w : G) * (x : G)⁻¹) * m⁻¹ = (x' : G) * (m * (w : G) * m⁻¹) * (x' : G)⁻¹
    rw [hx']
    group
  obtain ⟨π, hπ⟩ := D.exists_perm_of_normalizing hn γ
    (fun x => by
      refine ⟨⟨m * (x : G) * m⁻¹, h.normal m hm x x.2⟩, ?_⟩
      exact key hm x _ rfl)
    (fun x' => by
      refine ⟨⟨m⁻¹ * (x' : G) * m, by
        have := h.normal m⁻¹ (M.inv_mem hm) x' x'.2
        simpa using this⟩, ?_⟩
      exact key hm _ x' (by simp [mul_assoc]))
  refine ⟨π, fun w hw' => ?_⟩
  have h1 := hπ (D.β w)
  rw [hγ] at h1
  exact h1

end XNorm

@[expose] noncomputable def thetaFun (h : XNorm M X) (hn : 2 ≤ n) (m : ↥M) :
    Perm (Fin (2 * n + 1)) :=
  Classical.choose (XNorm.exists_perm_of_mem (D := D) h hn m.2)

theorem thetaFun_spec (h : XNorm M X) (hn : 2 ≤ n) (m : ↥M) (w : ↥D.W)
    (hw' : (m : G) * (w : G) * (m : G)⁻¹ ∈ D.W) :
    D.β ⟨(m : G) * (w : G) * (m : G)⁻¹, hw'⟩ =
      coreAct (2 * n + 1) (thetaFun D h hn m) (D.β w) :=
  Classical.choose_spec (XNorm.exists_perm_of_mem (D := D) h hn m.2) w hw'

theorem perm_unique (hn : 2 ≤ n) {m : G} {π π' : Perm (Fin (2 * n + 1))}
    (hπ : ∀ (w : ↥D.W) (hw' : m * (w : G) * m⁻¹ ∈ D.W),
      D.β ⟨m * (w : G) * m⁻¹, hw'⟩ = coreAct (2 * n + 1) π (D.β w))
    (hπ' : ∀ (w : ↥D.W) (hw' : m * (w : G) * m⁻¹ ∈ D.W),
      D.β ⟨m * (w : G) * m⁻¹, hw'⟩ = coreAct (2 * n + 1) π' (D.β w))
    (hW : ∀ w ∈ D.W, m * w * m⁻¹ ∈ D.W) : π = π' := by
  refine coreAct_injective (n := 2 * n + 1) (by omega) (MulEquiv.ext fun v => ?_)
  obtain ⟨w, rfl⟩ := D.β.surjective v
  rw [← hπ w (hW w w.2), ← hπ' w (hW w w.2)]

@[expose] noncomputable def theta (h : XNorm M X) (hn : 2 ≤ n) : ↥M →* Perm (Fin (2 * n + 1)) :=
  MonoidHom.mk' (thetaFun D h hn) (fun a b => by
    refine perm_unique D hn (m := (a : G) * (b : G)) (fun w hw' => ?_)
      (fun w hw' => ?_) (fun w hw => XNorm.W_normalized (D := D) h (M.mul_mem a.2 b.2) hw)
    · exact thetaFun_spec D h hn (a * b) w hw'
    · have hbw : (b : G) * (w : G) * (b : G)⁻¹ ∈ D.W := XNorm.W_normalized (D := D) h b.2 w.2
      have e : (a : G) * (b : G) * (w : G) * ((a : G) * (b : G))⁻¹ =
          (a : G) * ((b : G) * (w : G) * (b : G)⁻¹) * (a : G)⁻¹ := by group
      have h1 : D.β ⟨(a : G) * (b : G) * (w : G) * ((a : G) * (b : G))⁻¹, hw'⟩ =
          D.β ⟨(a : G) * ((b : G) * (w : G) * (b : G)⁻¹) * (a : G)⁻¹,
            XNorm.W_normalized (D := D) h a.2 hbw⟩ := by
        congr 1
        exact Subtype.ext e
      rw [h1, thetaFun_spec D h hn a ⟨_, hbw⟩ (XNorm.W_normalized (D := D) h a.2 hbw),
        thetaFun_spec D h hn b w hbw, map_mul]
      rfl)

theorem theta_spec (h : XNorm M X) (hn : 2 ≤ n) (m : ↥M) (w : ↥D.W)
    (hw' : (m : G) * (w : G) * (m : G)⁻¹ ∈ D.W) :
    D.β ⟨(m : G) * (w : G) * (m : G)⁻¹, hw'⟩ =
      coreAct (2 * n + 1) (theta D h hn m) (D.β w) :=
  thetaFun_spec D h hn m w hw'

theorem theta_X (h : XNorm M X) (hn : 2 ≤ n) (x : ↥X) :
    theta D h hn ⟨(x : G), h.le x.2⟩ = D.ρ x := by
  refine perm_unique D hn (m := (x : G)) (fun w hw' => ?_) (fun w hw' => D.equivar x w hw')
    (fun w hw => XNorm.W_normalized (D := D) h (h.le x.2) hw)
  exact theta_spec D h hn ⟨(x : G), h.le x.2⟩ w hw'

theorem theta_eq_one_iff (h : XNorm M X) (hn : 2 ≤ n) (m : ↥M) :
    theta D h hn m = 1 ↔ ∀ w ∈ D.W, (m : G) * w * (m : G)⁻¹ = w := by
  constructor
  · intro h1 w hw
    have h2 := theta_spec D h hn m ⟨w, hw⟩ (XNorm.W_normalized (D := D) h m.2 hw)
    rw [h1, map_one] at h2
    exact congrArg Subtype.val (D.β.injective h2)
  · intro hc
    refine coreAct_injective (n := 2 * n + 1) (by omega) (MulEquiv.ext fun v => ?_)
    obtain ⟨w, rfl⟩ := D.β.surjective v
    rw [← theta_spec D h hn m w (XNorm.W_normalized (D := D) h m.2 w.2)]
    have : (⟨(m : G) * (w : G) * (m : G)⁻¹, XNorm.W_normalized (D := D) h m.2 w.2⟩ : ↥D.W) = w :=
      Subtype.ext (hc w w.2)
    rw [this, map_one]
    rfl

end CFSG.CGT.PushingUpLit.SolK
