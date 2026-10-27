module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbTwoPair

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V]

theorem cb_map_conj_vecStab {G : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ G) (v : V) :
    (vecStab G v).map (MulAut.conj x).toMonoidHom = vecStab G (x v) := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨hhG, hhv⟩ := mem_vecStab.mp hh
    refine mem_vecStab.mpr ⟨G.mul_mem (G.mul_mem hx hhG) (G.inv_mem hx), ?_⟩
    change (x * h * x⁻¹) (x v) = x v
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self V, hhv]
  · intro hg
    obtain ⟨hgG, hgv⟩ := mem_vecStab.mp hg
    refine ⟨x⁻¹ * g * x, mem_vecStab.mpr ⟨G.mul_mem (G.mul_mem (G.inv_mem hx) hgG) hx, ?_⟩, ?_⟩
    · rw [MulAut.mul_apply, MulAut.mul_apply, hgv, MulAut.inv_apply_self V]
    · change x * (x⁻¹ * g * x) * x⁻¹ = g
      group

theorem cb_subnormal_conj {X H : Subgroup (MulAut V)} (x : MulAut V)
    (h : (X.subgroupOf H).IsSubnormal) :
    ((X.map (MulAut.conj x).toMonoidHom).subgroupOf
      (H.map (MulAut.conj x).toMonoidHom)).IsSubnormal := by
  have hinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  let ψ := Subgroup.equivMapOfInjective H (MulAut.conj x).toMonoidHom hinj
  have hs := h.map (f := ψ.toMonoidHom) ψ.surjective
  have heq : (X.subgroupOf H).map ψ.toMonoidHom =
      (X.map (MulAut.conj x).toMonoidHom).subgroupOf (H.map (MulAut.conj x).toMonoidHom) := by
    ext ⟨g, hg⟩
    constructor
    · rintro ⟨y, hy, hyg⟩
      have hyg' : (MulAut.conj x).toMonoidHom (y : MulAut V) = g := congrArg Subtype.val hyg
      exact ⟨y, hy, hyg'⟩
    · intro hmem
      obtain ⟨x', hx', hx'g⟩ := hmem
      obtain ⟨h0, hh0, hh0g⟩ := hg
      have : h0 = x' := hinj (hh0g.trans hx'g.symm)
      subst this
      exact ⟨⟨h0, hh0⟩, hx', Subtype.ext hx'g⟩
  rwa [heq] at hs

theorem cb_conj_lifts_eq {G Y : Subgroup (MulAut V)} {m : ℕ} (hm : 7 ≤ m) {t : MulAut V}
    {X₁ X₂ : Subgroup (MulAut V)} (h₁ : IsCbLift G Y t m X₁) (h₂ : IsCbLift G Y t m X₂)
    {v₁ v₂ : V} (hv₁ : v₁ ∈ fixV X₂ ⊓ commV (Subgroup.zpowers t)) (hv₁1 : v₁ ≠ 1)
    (hv₂ : v₂ ∈ fixV X₁ ⊓ commV (Subgroup.zpowers t)) (hv₂1 : v₂ ≠ 1)
    {x₁ x₂ : MulAut V} (hx₁ : x₁ ∈ X₁) (hx₂ : x₂ ∈ X₂) (hu : x₁ v₁ = x₂ v₂)
    {Y' : Subgroup (MulAut V)} (hY' : Y' ≠ ⊥)
    (hY'₁ : Y' ≤ X₂.map (MulAut.conj x₁).toMonoidHom)
    (hY'₂ : Y' ≤ X₁.map (MulAut.conj x₂).toMonoidHom) :
    X₂.map (MulAut.conj x₁).toMonoidHom = X₁.map (MulAut.conj x₂).toMonoidHom := by
  obtain ⟨θ₁, -⟩ := h₁.alt
  obtain ⟨θ₂, -⟩ := h₂.alt
  have hinj₁ : Function.Injective (MulAut.conj x₁).toMonoidHom := (MulAut.conj x₁).injective
  have hinj₂ : Function.Injective (MulAut.conj x₂).toMonoidHom := (MulAut.conj x₂).injective
  let e₁ := Subgroup.equivMapOfInjective X₁ (MulAut.conj x₂).toMonoidHom hinj₂
  let e₂ := Subgroup.equivMapOfInjective X₂ (MulAut.conj x₁).toMonoidHom hinj₁
  have hx₁G : x₁ ∈ G := h₁.le_G hx₁
  have hx₂G : x₂ ∈ G := h₂.le_G hx₂
  have hsub₂ := cb_subnormal_conj x₁ (h₂.subnormal v₁ hv₁ hv₁1)
  have hsub₁ := cb_subnormal_conj x₂ (h₁.subnormal v₂ hv₂ hv₂1)
  rw [cb_map_conj_vecStab hx₁G] at hsub₂
  rw [cb_map_conj_vecStab hx₂G, ← hu] at hsub₁
  have hle₂ : X₂.map (MulAut.conj x₁).toMonoidHom ≤ vecStab G (x₁ v₁) := by
    rw [← cb_map_conj_vecStab hx₁G]
    refine Subgroup.map_mono fun x hx => mem_vecStab.mpr ⟨h₂.le_G hx, ?_⟩
    exact mem_fixV.mp hv₁.1 x hx
  have hle₁ : X₁.map (MulAut.conj x₂).toMonoidHom ≤ vecStab G (x₁ v₁) := by
    rw [hu, ← cb_map_conj_vecStab hx₂G]
    refine Subgroup.map_mono fun x hx => mem_vecStab.mpr ⟨h₁.le_G hx, ?_⟩
    exact mem_fixV.mp hv₂.1 x hx
  refine le_antisymm ?_ ?_
  · exact cbc_le_of_subnormal_meet hle₂ hsub₁ (by omega : 5 ≤ m + 2) (e₂.symm.trans θ₂) hY'₁
      hY'₂ hY'
  · exact cbc_le_of_subnormal_meet hle₁ hsub₂ (by omega : 5 ≤ m + 2) (e₁.symm.trans θ₁) hY'₂
      hY'₁ hY'

private theorem cbu_swap_commute {α : Type*} [DecidableEq α] (τ : Equiv.Perm α) {x y : α}
    (hx : τ x = x) (hy : τ y = y) : τ * swap x y = swap x y * τ := by
  have h := Equiv.swap_apply_apply τ x y
  rw [hx, hy] at h
  calc τ * swap x y = τ * swap x y * τ⁻¹ * τ := by group
    _ = swap x y * τ := by rw [← h]

namespace CbtLift

variable {Y : Subgroup (MulAut V)} {m : ℕ} {C : CbtY Y m} {t : MulAut V}
  {X : Subgroup (MulAut V)} (L : CbtLift C t X)

def xPerm {p q : Fin m} (_hpq : p ≠ q) : alternatingGroup (Fin (m + 2)) :=
  ⟨swap (L.j p) L.D.a * swap (L.j q) L.D.b, by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (L.hja p),
      Equiv.Perm.sign_swap (L.hjb q)]
    decide⟩

noncomputable def xElt {p q : Fin m} (hpq : p ≠ q) : ↥X := L.D.θ.symm (L.xPerm hpq)

variable {p q : Fin m} (hpq : p ≠ q)

theorem xElt_theta : L.D.θ (L.xElt hpq) = L.xPerm hpq := L.D.θ.apply_symm_apply _

theorem xElt_w (s : Fin (m + 2)) :
    (L.xElt hpq : MulAut V) (L.D.w s) =
      L.D.w ((swap (L.j p) L.D.a * swap (L.j q) L.D.b) s) := by
  have h := L.D.hwact (L.xElt hpq : MulAut V) (L.xElt hpq).2 s
  rw [h]
  have h2 : L.D.θ ⟨(L.xElt hpq : MulAut V), (L.xElt hpq).2⟩ = L.xPerm hpq := L.xElt_theta hpq
  rw [h2]
  rfl

theorem xPerm_a : (swap (L.j p) L.D.a * swap (L.j q) L.D.b) L.D.a = L.j p := by
  have h1 : L.D.a ≠ L.j q := fun h => L.hja q h.symm
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne h1 L.D.hab, swap_apply_right]

include hpq in
theorem xPerm_b : (swap (L.j p) L.D.a * swap (L.j q) L.D.b) L.D.b = L.j q := by
  have h1 : L.j q ≠ L.j p := fun h => hpq (L.hjinj h).symm
  rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne h1 (L.hja q)]

theorem xPerm_jq : (swap (L.j p) L.D.a * swap (L.j q) L.D.b) (L.j q) = L.D.b := by
  have h1 : L.D.b ≠ L.j p := fun h => L.hjb p h.symm
  rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne h1 (Ne.symm L.D.hab)]

theorem xElt_sq : (L.xElt hpq : MulAut V) * (L.xElt hpq : MulAut V) = 1 := by
  have hc : swap (L.j p) L.D.a * swap (L.j q) L.D.b =
      swap (L.j q) L.D.b * swap (L.j p) L.D.a :=
    cbtSwap_comm (fun h => hpq (L.hjinj h)) (fun h => L.hjb p h) (fun h => L.hja q h.symm)
      L.D.hab
  have h : L.xElt hpq * L.xElt hpq = 1 := by
    apply L.D.θ.injective
    rw [map_mul, L.xElt_theta hpq, map_one]
    apply Subtype.ext
    show (swap (L.j p) L.D.a * swap (L.j q) L.D.b) * (swap (L.j p) L.D.a * swap (L.j q) L.D.b) = 1
    calc (swap (L.j p) L.D.a * swap (L.j q) L.D.b) * (swap (L.j p) L.D.a * swap (L.j q) L.D.b)
        = swap (L.j p) L.D.a * (swap (L.j q) L.D.b * swap (L.j p) L.D.a) * swap (L.j q) L.D.b := by
          group
      _ = swap (L.j p) L.D.a * (swap (L.j p) L.D.a * swap (L.j q) L.D.b) * swap (L.j q) L.D.b := by
          rw [← hc]
      _ = 1 := by rw [← mul_assoc, swap_mul_self, one_mul, swap_mul_self]
  exact congrArg Subtype.val h

theorem xElt_comm {y : MulAut V} (hy : y ∈ Y) (hyp : (C.θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) p = p)
    (hyq : (C.θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) q = q) :
    (L.xElt hpq : MulAut V) * y = y * (L.xElt hpq : MulAut V) := by
  set τ : Equiv.Perm (Fin (m + 2)) := (L.D.θ ⟨y, L.hYX hy⟩ : Equiv.Perm (Fin (m + 2))) with hτ
  have hτa := (L.fix_ab y hy).1
  have hτb := (L.fix_ab y hy).2
  have hτp : τ (L.j p) = L.j p := by rw [hτ, L.hjθ y hy p, hyp]
  have hτq : τ (L.j q) = L.j q := by rw [hτ, L.hjθ y hy q, hyq]
  have h1 := cbu_swap_commute τ hτp hτa
  have h2 := cbu_swap_commute τ hτq hτb
  have h3 : (L.xPerm hpq : Equiv.Perm (Fin (m + 2))) * τ = τ * (L.xPerm hpq) := by
    show (swap (L.j p) L.D.a * swap (L.j q) L.D.b) * τ =
      τ * (swap (L.j p) L.D.a * swap (L.j q) L.D.b)
    calc (swap (L.j p) L.D.a * swap (L.j q) L.D.b) * τ
        = swap (L.j p) L.D.a * (swap (L.j q) L.D.b * τ) := by group
      _ = swap (L.j p) L.D.a * (τ * swap (L.j q) L.D.b) := by rw [h2]
      _ = (swap (L.j p) L.D.a * τ) * swap (L.j q) L.D.b := by group
      _ = (τ * swap (L.j p) L.D.a) * swap (L.j q) L.D.b := by rw [h1]
      _ = τ * (swap (L.j p) L.D.a * swap (L.j q) L.D.b) := by group
  have h4 : L.xElt hpq * (⟨y, L.hYX hy⟩ : ↥X) = (⟨y, L.hYX hy⟩ : ↥X) * L.xElt hpq := by
    apply L.D.θ.injective
    rw [map_mul, map_mul, L.xElt_theta hpq]
    apply Subtype.ext
    exact h3
  exact congrArg Subtype.val h4

private theorem cbu_vvec_sq (hV : ∀ v : V, v ^ 2 = 1) : L.vvec * L.vvec = 1 := by
  rw [← pow_two]
  exact hV _

variable [Finite V]

theorem w_j (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) (r : Fin m) :
    L.D.w (L.j r) = C.w r * L.vvec := by
  have h : L.D.w (L.j r) * L.vvec = C.w r := L.eps_eq hV hm hodd r
  calc L.D.w (L.j r) = L.D.w (L.j r) * (L.vvec * L.vvec) := by rw [L.cbu_vvec_sq hV, mul_one]
    _ = (L.D.w (L.j r) * L.vvec) * L.vvec := by rw [mul_assoc]
    _ = C.w r * L.vvec := by rw [h]

theorem xElt_vvec (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) :
    (L.xElt hpq : MulAut V) L.vvec = C.w p * C.w q := by
  have h1 : (L.xElt hpq : MulAut V) L.vvec = L.D.w (L.j p) * L.D.w (L.j q) := by
    unfold vvec
    rw [map_mul, L.xElt_w hpq, L.xElt_w hpq, L.xPerm_a, L.xPerm_b hpq]
  rw [h1, L.w_j hV hm hodd p, L.w_j hV hm hodd q]
  calc C.w p * L.vvec * (C.w q * L.vvec) = C.w p * C.w q * (L.vvec * L.vvec) := by
        ac_rfl
    _ = C.w p * C.w q := by rw [L.cbu_vvec_sq hV, mul_one]

theorem xElt_zvec (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) :
    (L.xElt hpq : MulAut V) L.zvec = C.w q * L.vvec := by
  unfold zvec
  rw [L.xElt_w hpq, L.xPerm_b hpq, L.w_j hV hm hodd q]

theorem xElt_wY (hV : ∀ v : V, v ^ 2 = 1) (hm : 7 ≤ m) (hodd : Odd m) :
    (L.xElt hpq : MulAut V) (C.w q) = L.zvec * (C.w p * C.w q) := by
  have h1 : C.w q = L.D.w (L.j q) * L.vvec := by
    rw [L.w_j hV hm hodd q, mul_assoc, L.cbu_vvec_sq hV, mul_one]
  conv_lhs => rw [h1]
  rw [map_mul, L.xElt_w hpq, L.xPerm_jq, L.xElt_vvec hpq hV hm hodd]
  rfl

omit [Finite V] in
theorem vvec_mem (hV : ∀ v : V, v ^ 2 = 1) : L.vvec ∈ commV (Subgroup.zpowers t) := by
  have h6 : t (L.D.w L.D.a) * (L.D.w L.D.a)⁻¹ ∈ commV (Subgroup.zpowers t) :=
    Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, L.D.w L.D.a, rfl⟩
  have hinv : (L.D.w L.D.a)⁻¹ = L.D.w L.D.a := inv_eq_of_mul_eq_one_right (L.D.w_sq hV _)
  rw [L.D.htw, Equiv.swap_apply_left, hinv, mul_comm] at h6
  exact h6

omit [Finite V] in
theorem vvec_ne_one (hV : ∀ v : V, v ^ 2 = 1) : L.vvec ≠ 1 := by
  intro h
  have hinv : (L.D.w L.D.b)⁻¹ = L.D.w L.D.b := inv_eq_of_mul_eq_one_right (L.D.w_sq hV _)
  have h1 : L.D.w L.D.a * L.D.w L.D.b = 1 := h
  rw [mul_eq_one_iff_eq_inv, hinv] at h1
  exact L.D.hab (L.D.hwinj h1)

end CbtLift

variable [Finite V] in
theorem cb_beta_aux {G Y : Subgroup (MulAut V)} {m : ℕ} {t : MulAut V}
    {X₁ X₂ : Subgroup (MulAut V)} {C : CbtY Y m} (hm : 7 ≤ m) (hodd : Odd m)
    (hV : ∀ v : V, v ^ 2 = 1) (h₁ : IsCbLift G Y t m X₁) (h₂ : IsCbLift G Y t m X₂)
    (L₁ : CbtLift C t X₁) (L₂ : CbtLift C t X₂) {n : ℕ} (hv₂ : L₂.vvec ∈ fixV X₁)
    (hv₁ : L₁.vvec ∈ fixV X₂) (hz₁ : L₁.zvec * L₂.vvec ^ n ∈ fixV X₂) :
    L₁.zvec * L₂.vvec ∈ fixV X₂ := by
  classical
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hV v
  let p : Fin m := ⟨0, by omega⟩
  let q : Fin m := ⟨1, by omega⟩
  have hpq : p ≠ q := fun h => by simpa [p, q] using congrArg Fin.val h
  have hx₁ : (L₁.xElt hpq : MulAut V) ∈ X₁ := (L₁.xElt hpq).2
  have hx₂ : (L₂.xElt hpq : MulAut V) ∈ X₂ := (L₂.xElt hpq).2
  have hu : (L₁.xElt hpq : MulAut V) L₁.vvec = (L₂.xElt hpq : MulAut V) L₂.vvec := by
    rw [L₁.xElt_vvec hpq hV hm hodd, L₂.xElt_vvec hpq hV hm hodd]
  let Y' : Subgroup (MulAut V) :=
    (Subgroup.comap C.θ.toMonoidHom (altStabilizer m {p, q})).map Y.subtype
  have hY'mem : ∀ y ∈ Y', ∃ hy : y ∈ Y, (C.θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) p = p ∧
      (C.θ ⟨y, hy⟩ : Equiv.Perm (Fin m)) q = q := by
    rintro y ⟨y', hy', rfl⟩
    have h1 := mem_altStabilizer_iff.mp hy'
    exact ⟨y'.2, h1 p (by simp), h1 q (by simp)⟩
  have hY'ne : Y' ≠ ⊥ := by
    let r₁ : Fin m := ⟨2, by omega⟩
    let r₂ : Fin m := ⟨3, by omega⟩
    have hr₁ : r₁ ∉ ({p, q} : Finset (Fin m)) := by
      simp [r₁, p, q, Fin.ext_iff]
    have hr₂ : r₂ ∉ ({p, q} : Finset (Fin m)) := by
      simp [r₂, p, q, Fin.ext_iff]
    obtain ⟨σ, hσF, hσ⟩ := cbtExists_alt_perm (n := m) (by omega) (F := {p, q})
      (by
        have := Finset.card_le_two (a := p) (b := q)
        omega) hr₁ hr₂
    intro hbot
    have hmem : ((C.θ.symm σ : ↥Y) : MulAut V) ∈ Y' :=
      ⟨C.θ.symm σ, mem_altStabilizer_iff.mpr (by
        intro f hf
        have := hσF f hf
        simpa using this), rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have h1 : C.θ.symm σ = 1 := Subtype.ext hmem
    have h2 : σ = 1 := by simpa using congrArg C.θ h1
    rw [h2] at hσ
    have h3 : r₂ = r₁ := hσ.symm.trans (by simp)
    simp [r₁, r₂, Fin.ext_iff] at h3
  have hY'₁ : Y' ≤ X₂.map (MulAut.conj (L₁.xElt hpq : MulAut V)).toMonoidHom := by
    intro y hy
    obtain ⟨hyY, hyp, hyq⟩ := hY'mem y hy
    refine ⟨y, L₂.hYX hyY, ?_⟩
    have hc := L₁.xElt_comm hpq hyY hyp hyq
    change (L₁.xElt hpq : MulAut V) * y * (L₁.xElt hpq : MulAut V)⁻¹ = y
    rw [hc]
    group
  have hY'₂ : Y' ≤ X₁.map (MulAut.conj (L₂.xElt hpq : MulAut V)).toMonoidHom := by
    intro y hy
    obtain ⟨hyY, hyp, hyq⟩ := hY'mem y hy
    refine ⟨y, L₁.hYX hyY, ?_⟩
    have hc := L₂.xElt_comm hpq hyY hyp hyq
    change (L₂.xElt hpq : MulAut V) * y * (L₂.xElt hpq : MulAut V)⁻¹ = y
    rw [hc]
    group
  have hXeq := cb_conj_lifts_eq hm h₁ h₂ ⟨hv₁, L₁.vvec_mem hV⟩ (L₁.vvec_ne_one hV)
    ⟨hv₂, L₂.vvec_mem hV⟩ (L₂.vvec_ne_one hV) hx₁ hx₂ hu hY'ne hY'₁ hY'₂
  set x₁ : MulAut V := (L₁.xElt hpq : MulAut V) with hx₁def
  set x₂ : MulAut V := (L₂.xElt hpq : MulAut V) with hx₂def
  have hx₂inv : x₂⁻¹ = x₂ := inv_eq_of_mul_eq_one_right (L₂.xElt_sq hpq)
  set g : MulAut V := x₂⁻¹ * x₁ with hgdef
  have hg : ∀ f ∈ fixV X₂, g f ∈ fixV X₁ := by
    intro f hf
    rw [mem_fixV]
    intro x hx
    have hx' : x₂ * x * x₂⁻¹ ∈ X₁.map (MulAut.conj x₂).toMonoidHom := ⟨x, hx, rfl⟩
    rw [← hXeq] at hx'
    obtain ⟨x', hx'X₂, hx'e⟩ := hx'
    have hx'e' : x₁ * x' * x₁⁻¹ = x₂ * x * x₂⁻¹ := hx'e
    have hxeq : x = g * x' * g⁻¹ := by
      calc x = x₂⁻¹ * (x₂ * x * x₂⁻¹) * x₂ := by group
        _ = x₂⁻¹ * (x₁ * x' * x₁⁻¹) * x₂ := by rw [hx'e']
        _ = g * x' * g⁻¹ := by rw [hgdef]; group
    have hx'f : x' f = f := mem_fixV.mp hf x' hx'X₂
    rw [hxeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self V, hx'f]
  have hgf := hg _ hz₁
  have hx₁v₂ : x₁ L₂.vvec = L₂.vvec := mem_fixV.mp hv₂ x₁ hx₁
  have hx₂v₁ : x₂ L₁.vvec = L₁.vvec := mem_fixV.mp hv₁ x₂ hx₂
  have hcomp : g (L₁.zvec * L₂.vvec ^ n) =
      L₂.zvec * (C.w p * C.w q) * L₁.vvec * (C.w p * C.w q) ^ n := by
    rw [hgdef, MulAut.mul_apply, map_mul, map_pow, hx₁v₂, L₁.xElt_zvec hpq hV hm hodd, hx₂inv,
      map_mul, map_mul, map_pow, L₂.xElt_wY hpq hV hm hodd, hx₂v₁,
      L₂.xElt_vvec hpq hV hm hodd]
  let p' : Fin m := ⟨2, by omega⟩
  have hp'q : p' ∉ ({q} : Finset (Fin m)) := by simp [p', q, Fin.ext_iff]
  have hpq' : p ∉ ({q} : Finset (Fin m)) := by simp [p, q, Fin.ext_iff]
  obtain ⟨σ, hσq, hσp⟩ := cbtExists_alt_perm (n := m) (by omega) (F := {q}) (by simp) hpq' hp'q
  let y : MulAut V := ((C.θ.symm σ : ↥Y) : MulAut V)
  have hyY : y ∈ Y := (C.θ.symm σ).2
  have hθy : C.θ ⟨y, hyY⟩ = σ := C.θ.apply_symm_apply σ
  have hyu : y (C.w p * C.w q) = C.w p' * C.w q := by
    rw [map_mul, C.hact y hyY p, C.hact y hyY q, hθy, hσp, hσq q (by simp)]
  have hyz₂ : y L₂.zvec = L₂.zvec := L₂.y_wb y hyY
  have hyv₁ : y L₁.vvec = L₁.vvec := by
    unfold CbtLift.vvec
    rw [map_mul, L₁.y_wa y hyY, L₁.y_wb y hyY]
  have hyg : y (g (L₁.zvec * L₂.vvec ^ n)) = g (L₁.zvec * L₂.vvec ^ n) :=
    mem_fixV.mp hgf y (L₁.hYX hyY)
  rw [hcomp] at hyg
  simp only [map_mul, map_pow, hyz₂, hyv₁, hyu] at hyg
  have h5 : (L₂.zvec * L₁.vvec) * (C.w p' * C.w q) ^ (n + 1) =
      (L₂.zvec * L₁.vvec) * (C.w p * C.w q) ^ (n + 1) := by
    calc (L₂.zvec * L₁.vvec) * (C.w p' * C.w q) ^ (n + 1)
        = L₂.zvec * (C.w p' * C.w q) * L₁.vvec * (C.w p' * C.w q) ^ n := by
          rw [pow_succ']
          ac_rfl
      _ = L₂.zvec * (C.w p * C.w q) * L₁.vvec * (C.w p * C.w q) ^ n := hyg
      _ = (L₂.zvec * L₁.vvec) * (C.w p * C.w q) ^ (n + 1) := by
          rw [pow_succ']
          ac_rfl
  have h6 := mul_left_cancel h5
  have hnodd : Odd n := by
    by_contra hn
    have hne : Even n := Nat.not_odd_iff_even.mp hn
    have hn1 : Odd (n + 1) := hne.add_one
    have h7 : (C.w p' * C.w q) ^ (n + 1) = C.w p' * C.w q := by
      have : (C.w p' * C.w q) * (C.w p' * C.w q) = 1 := by
        calc (C.w p' * C.w q) * (C.w p' * C.w q)
            = (C.w p' * C.w p') * (C.w q * C.w q) := by ac_rfl
          _ = 1 := by rw [hsq, hsq, mul_one]
      exact cbtPow_odd this hn1
    have h8 : (C.w p * C.w q) ^ (n + 1) = C.w p * C.w q := by
      have : (C.w p * C.w q) * (C.w p * C.w q) = 1 := by
        calc (C.w p * C.w q) * (C.w p * C.w q)
            = (C.w p * C.w p) * (C.w q * C.w q) := by ac_rfl
          _ = 1 := by rw [hsq, hsq, mul_one]
      exact cbtPow_odd this hn1
    rw [h7, h8] at h6
    have h9 : C.w p' = C.w p := mul_right_cancel h6
    have h10 : p' = p := C.hinj h9
    simp [p', p, Fin.ext_iff] at h10
  have hvn : L₂.vvec ^ n = L₂.vvec := cbtPow_odd (L₂.cbu_vvec_sq hV) hnodd
  rw [hvn] at hz₁
  exact hz₁

namespace CbtCtx

variable [Finite V] {Y : Subgroup (MulAut V)} {m : ℕ} {G T : Subgroup (MulAut V)}
  {t : MulAut V} {X₁ X₂ : Subgroup (MulAut V)} (K : CbtCtx G T Y t m X₁ X₂)

theorem beta_eq (hv₂ : K.L₂.vvec ∈ fixV X₁) (hv₁ : K.L₁.vvec ∈ fixV X₂)
    (hz₁ : ∃ n : ℕ, K.L₁.zvec * K.L₂.vvec ^ n ∈ fixV X₂)
    (hz₂ : ∃ n : ℕ, K.L₂.zvec * K.L₁.vvec ^ n ∈ fixV X₁) :
    K.L₂.zvec * K.L₁.vvec ∈ fixV X₁ ∧ K.L₁.zvec * K.L₂.vvec ∈ fixV X₂ := by
  obtain ⟨n, hn⟩ := hz₁
  obtain ⟨n', hn'⟩ := hz₂
  exact ⟨cb_beta_aux K.hm K.hodd K.hV K.h₂ K.h₁ K.L₂ K.L₁ hv₁ hv₂ hn',
    cb_beta_aux K.hm K.hodd K.hV K.h₁ K.h₂ K.L₁ K.L₂ hv₂ hv₁ hn⟩

end CbtCtx

end CFSG.CGT.PushingUpLit.CGT6
