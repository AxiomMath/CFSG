module

public import CFSG.LocalAnalysis.OddStandard.AltStdBalLocal
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.OddStandard.AltStdBal

open Subgroup Equiv
open scoped Pointwise

section Action

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ}

@[expose] noncomputable def autEquivPerm (hn : 8 ≤ n) :
    MulAut (alternatingGroup (Fin n)) ≃* Perm (Fin n) :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega)
      (by omega))).symm

theorem conjNormal_autEquivPerm (hn : 8 ≤ n) (φ : MulAut (alternatingGroup (Fin n))) :
    MulAut.conjNormal (autEquivPerm hn φ) = φ :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega)
      (by omega))).apply_symm_apply φ

theorem conjNormal_injective' (hn : 8 ≤ n) :
    Function.Injective (MulAut.conjNormal (H := alternatingGroup (Fin n))) :=
  (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n (by omega) (by omega)).1

@[expose] def normAct (L : Subgroup G) : normalizer (L : Set G) →* MulAut L where
  toFun g :=
    { toFun := fun w => ⟨g * w * (g : G)⁻¹, (mem_normalizer_iff.mp g.2 w).mp w.2⟩
      invFun := fun w => ⟨(g : G)⁻¹ * w * g, by
        have := (mem_normalizer_iff.mp (inv_mem g.2) w).mp w.2
        simpa using this⟩
      left_inv := fun w => by ext; simp [mul_assoc]
      right_inv := fun w => by ext; simp [mul_assoc]
      map_mul' := fun w₁ w₂ => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun g₁ g₂ => by ext; simp [mul_assoc, MulAut.mul_apply]

theorem coe_normAct_apply (L : Subgroup G) (g : normalizer (L : Set G)) (w : L) :
    ((normAct L g w : L) : G) = g * w * (g : G)⁻¹ := rfl

@[expose] noncomputable def rho (e : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) :
    normalizer (L : Set G) →* Perm (Fin n) :=
  (autEquivPerm hn).toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp (normAct L))

theorem rho_conj (e : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (x : normalizer (L : Set G))
    (a : alternatingGroup (Fin n)) :
    rho e hn x * (a : Perm (Fin n)) * (rho e hn x)⁻¹ =
      ((e ⟨x * (e.symm a : G) * (x : G)⁻¹, (mem_normalizer_iff.mp x.2 _).mp (e.symm a).2⟩ :
        alternatingGroup (Fin n)) : Perm (Fin n)) := by
  have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin n)) => (φ a : Perm (Fin n)))
    (conjNormal_autEquivPerm hn (MulAut.congr e (normAct L x)))
  simp only [MulAut.conjNormal_apply, MulAut.congr_apply, MulEquiv.trans_apply] at h1
  exact h1

theorem rho_eq_one_iff (e : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)
    (x : normalizer (L : Set G)) : rho e hn x = 1 ↔ (x : G) ∈ centralizer (L : Set G) := by
  constructor
  · intro h1
    rw [mem_centralizer_iff]
    intro l hl
    have h2 := rho_conj e hn x (e ⟨l, hl⟩)
    rw [h1] at h2
    have h3 : (e ⟨l, hl⟩ : alternatingGroup (Fin n)) =
        e ⟨x * (e.symm (e ⟨l, hl⟩) : G) * (x : G)⁻¹,
          (mem_normalizer_iff.mp x.2 _).mp (e.symm (e ⟨l, hl⟩)).2⟩ := by
      apply Subtype.ext
      simpa using h2
    have h4 := e.injective h3
    have h5 := congrArg Subtype.val h4
    simp only [MulEquiv.symm_apply_apply] at h5
    have h6 : (x : G) * l * (x : G)⁻¹ = l := h5.symm
    calc l * (x : G) = ((x : G) * l * (x : G)⁻¹) * x := by rw [h6]
      _ = x * l := by group
  · intro hx
    have h1 : normAct L x = 1 := by
      ext l
      change (x : G) * l * (x : G)⁻¹ = l
      have := mem_centralizer_iff.1 hx l l.2
      calc (x : G) * l * (x : G)⁻¹ = l * x * (x : G)⁻¹ := by rw [← this]
        _ = l := by group
    show autEquivPerm hn (MulAut.congr e (normAct L x)) = 1
    rw [h1, map_one, map_one]

theorem rho_of_mem (e : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (l : L)
    (hl : (l : G) ∈ normalizer (L : Set G)) :
    rho e hn ⟨l, hl⟩ = ((e l : alternatingGroup (Fin n)) : Perm (Fin n)) := by
  have hinj := conjNormal_injective' (n := n) hn
  have : MulAut.conjNormal (H := alternatingGroup (Fin n)) (rho e hn ⟨l, hl⟩) =
      MulAut.conjNormal (H := alternatingGroup (Fin n))
        (((e l : alternatingGroup (Fin n)) : Perm (Fin n))) := by
    ext a
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply]
    have h2 := rho_conj e hn ⟨l, hl⟩ a
    rw [h2]
    have : (e ⟨(l : G) * (e.symm a : G) * (l : G)⁻¹, (mem_normalizer_iff.mp hl _).mp
        (e.symm a).2⟩ : alternatingGroup (Fin n)) = e l * a * (e l)⁻¹ := by
      have h3 : (⟨(l : G) * (e.symm a : G) * (l : G)⁻¹, (mem_normalizer_iff.mp hl _).mp
          (e.symm a).2⟩ : L) = l * e.symm a * l⁻¹ := rfl
      rw [h3, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [this]
    rfl
  exact hinj this

theorem eq_one_of_mem_of_mem_centralizer (e : L ≃* alternatingGroup (Fin n)) (hn : 4 ≤ n) {x : G}
    (hxL : x ∈ L) (hxK : x ∈ centralizer (L : Set G)) : x = 1 := by
  have hz : e ⟨x, hxL⟩ ∈ Subgroup.center ↥(alternatingGroup (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := e.surjective g
    have := mem_centralizer_iff.1 hxK l l.2
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext this
  rw [alternatingGroup.center_eq_bot (by simpa using hn)] at hz
  have h1 : (⟨x, hxL⟩ : L) = 1 := e.injective (by simpa using hz)
  simpa using congrArg Subtype.val h1

end Action

section Index

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z : G}

@[expose] noncomputable def signHom (e : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) :
    normalizer (L : Set G) →* ℤˣ :=
  Equiv.Perm.sign.comp (rho e hn)

omit [Finite G] in
theorem signHom_of_mem (e : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) (l : L)
    (hl : (l : G) ∈ normalizer (L : Set G)) : signHom e hn ⟨l, hl⟩ = 1 := by
  have h1 := rho_of_mem e hn l hl
  have h2 : ((e l : alternatingGroup (Fin n)) : Perm (Fin n)) ∈ alternatingGroup (Fin n) :=
    (e l).2
  rw [Equiv.Perm.mem_alternatingGroup] at h2
  simp only [signHom, MonoidHom.comp_apply]
  rw [h1]
  exact h2

omit [Finite G] in
theorem signHom_of_mem_centralizer (e : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n)
    (x : normalizer (L : Set G)) (hx : (x : G) ∈ centralizer (L : Set G)) :
    signHom e hn x = 1 := by
  simp [signHom, (rho_eq_one_iff e hn x).2 hx]

theorem mem_sup_of_signHom_eq_one (h : Setting G L n) (d : Cyc L Q z)
    (e : L ≃* alternatingGroup (Fin n)) (c' : normalizer (L : Set G))
    (hcC : (c' : G) ∈ centralizer ({z} : Set G)) (hsign : signHom e h.hn c' = 1) :
    (c' : G) ∈ L ⊔ Q := by
  have hmem : rho e h.hn c' ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    exact hsign
  obtain ⟨l, hlN, hrl⟩ : ∃ l : L, ∃ hlN : (l : G) ∈ normalizer (L : Set G),
      rho e h.hn ⟨l, hlN⟩ = rho e h.hn c' :=
    ⟨e.symm ⟨rho e h.hn c', hmem⟩, Subgroup.le_normalizer (e.symm _).2, by
      rw [rho_of_mem e h.hn, MulEquiv.apply_symm_apply]⟩
  let l' : normalizer (L : Set G) := ⟨l, hlN⟩
  have hker : rho e h.hn (c' * l'⁻¹) = 1 := by
    rw [map_mul, map_inv, hrl, mul_inv_cancel]
  have hK' := (rho_eq_one_iff e h.hn (c' * l'⁻¹)).1 hker
  have hK : (c' : G) * (l : G)⁻¹ ∈ centralizer (L : Set G) := hK'
  have hC : (c' : G) * (l : G)⁻¹ ∈ centralizer ({z} : Set G) :=
    mul_mem hcC (inv_mem (le_centralizer_single h d l.2))
  have hQ : (c' : G) * (l : G)⁻¹ ∈ Q := by
    rw [← cent_inf_eq h d]
    exact ⟨hK, hC⟩
  have : (c' : G) = ((c' : G) * (l : G)⁻¹) * l := by group
  rw [this]
  exact mul_mem (mem_sup_right hQ) (mem_sup_left l.2)

theorem mem_sup_iff (h : Setting G L n) (d : Cyc L Q z) (e : L ≃* alternatingGroup (Fin n))
    {c : G} (hcC : c ∈ centralizer ({z} : Set G)) :
    c ∈ L ⊔ Q ↔
      signHom e h.hn ⟨c, centralizer_le_normalizer h d hcC⟩ = 1 := by
  have hKN : centralizer (L : Set G) ≤ normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
  constructor
  · intro hc
    have hle : L ⊔ Q ≤ (signHom e h.hn).ker.map (normalizer (L : Set G)).subtype := by
      refine sup_le ?_ ?_
      · intro l hl
        exact ⟨⟨l, Subgroup.le_normalizer hl⟩, signHom_of_mem e h.hn ⟨l, hl⟩ _, rfl⟩
      · intro q hq
        exact ⟨⟨q, hKN (d.le hq)⟩, signHom_of_mem_centralizer e h.hn _ (d.le hq), rfl⟩
    obtain ⟨y, hy, hyc⟩ := hle hc
    have : y = ⟨c, centralizer_le_normalizer h d hcC⟩ := Subtype.ext hyc
    rw [← this]
    exact hy
  · intro hsign
    exact mem_sup_of_signHom_eq_one h d e ⟨c, centralizer_le_normalizer h d hcC⟩ hcC hsign

theorem signHom_eq_neg_one (h : Setting G L n) (d : Cyc L Q z)
    (e : L ≃* alternatingGroup (Fin n)) {a : G} (haC : a ∈ centralizer ({z} : Set G))
    (ha : a ∉ L ⊔ Q) : signHom e h.hn ⟨a, centralizer_le_normalizer h d haC⟩ = -1 := by
  rcases Int.units_eq_one_or (signHom e h.hn ⟨a, centralizer_le_normalizer h d haC⟩) with h1 | h1
  · exact absurd ((mem_sup_iff h d e haC).2 h1) ha
  · exact h1

theorem inf_eq_bot (h : Setting G L n) (d : Cyc L Q z) : L ⊓ Q = ⊥ := by
  obtain ⟨e⟩ := h.iso
  rw [eq_bot_iff]
  rintro x ⟨hxL, hxQ⟩
  exact (eq_one_of_mem_of_mem_centralizer e (by have := h.hn; omega) hxL (d.le hxQ) ▸
    one_mem _ : x ∈ (⊥ : Subgroup G))

theorem le_normalizer_L (d : Cyc L Q z) : Q ≤ normalizer (L : Set G) :=
  d.le.trans (Subgroup.centralizer_le_normalizer _)

theorem mem_sup_iff_mul (d : Cyc L Q z) {c : G} : c ∈ L ⊔ Q ↔ ∃ l ∈ L, ∃ q ∈ Q, l * q = c := by
  have h := Subgroup.coe_mul_of_right_le_normalizer_left L Q (le_normalizer_L d)
  have : c ∈ ((L ⊔ Q : Subgroup G) : Set G) ↔ c ∈ (L : Set G) * (Q : Set G) := by rw [h]
  simpa [Set.mem_mul] using this

end Index

end CFSG.OddStandard.AltStdBal
