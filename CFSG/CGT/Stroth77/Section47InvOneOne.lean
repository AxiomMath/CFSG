module

public import CFSG.CGT.Stroth77.Section47InvOneII
public import CFSG.CGT.Stroth77.Section47InvOneAction

public section

namespace CFSG.CGT.Stroth77

open Stroth42Core Stroth34T200

namespace Stroth47Inv1

variable {G : Type} [Group G] [Finite G]

theorem not_isConj_of_isConj_mul (S : Sylow 2 G) {c₁ w₀ r v : G}
    (hw : ∀ x ∈ (S : Subgroup G), x * w₀ = w₀ * x)
    (hfact : ∀ x ∈ (S : Subgroup G), IsConj c₁ x → x ≠ w₀ →
      ∃ q ∈ (S : Subgroup G), q⁻¹ * x * q = x * w₀)
    (hvw : IsConj v w₀) (hrS : r ∈ (S : Subgroup G)) (hrv : r * v = v * r) (hne : r ≠ v)
    (hrv' : ¬ IsConj (r * v) c₁) :
    ¬ IsConj r c₁ := by
  intro hrc
  have hzS : (S : Subgroup G) ≤ Subgroup.centralizer {w₀} :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hw x hx)
  have hfact' : ∀ x ∈ (S : Subgroup G), IsConj r x → x ≠ w₀ →
      ∃ q ∈ (S : Subgroup G), q⁻¹ * x * q = x * w₀ :=
    fun x hxS hrx hxw => hfact x hxS (hrc.symm.trans hrx) hxw
  exact hrv' ((Stroth76.isConj_mul_of_isConj_central_of_conj S hzS hfact' hvw hrS hrv
    hne).symm.trans hrc)

theorem cabuv_isConj_of_isConj_mul {S T Du : Subgroup G} {c₁ a₁ u x : G}
    (hT : T = S ⊓ Subgroup.centralizer {c₁})
    (hsyl : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {c₁} →
      ∃ k ∈ Subgroup.centralizer {c₁}, ∀ q ∈ Q, k⁻¹ * q * k ∈ S)
    (hS32 : ∀ A : Subgroup G, A ≤ T → (∀ y ∈ A, y * y = 1) → Nat.card A ≠ 32)
    (hDu : ∀ y ∈ Du, y * y = 1 → y ≠ 1 → IsConj y c₁ ∨ IsConj y a₁)
    (hT1 : ∀ k ∈ T, k ∉ Du → k * k = 1 → IsConj (c₁ * k) c₁ → IsConj k c₁)
    (hu : IsConj u c₁) (hux : u * x = x * u) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hxuu : IsConj (u * x) u)
    (hx32 : ∃ A : Subgroup G, A ≤ Subgroup.centralizer {x} ∧ (∀ y ∈ A, y * y = 1) ∧
      Nat.card A = 32) :
    IsConj x a₁ := by
  classical
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hcu⟩ := isConj_iff.1 hu
  set t : G := c * x * c⁻¹ with ht
  have ht2 : t * t = 1 := by
    rw [ht]
    calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have ht1 : t ≠ 1 := by
    rw [ht]
    intro h'
    apply hx1
    calc x = c⁻¹ * (c * x * c⁻¹) * c := by group
      _ = 1 := by rw [h']; group
  have htC : t * c₁ = c₁ * t := by
    rw [ht, ← hcu]
    calc c * x * c⁻¹ * (c * u * c⁻¹) = c * (x * u) * c⁻¹ := by group
      _ = c * (u * x) * c⁻¹ := by rw [hux]
      _ = c * u * c⁻¹ * (c * x * c⁻¹) := by group
  have hQp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers,
        @orderOf_eq_prime G _ t 2 hFact (by rw [pow_two]; exact ht2) ht1, pow_one])
  have hQc : Subgroup.zpowers t ≤ Subgroup.centralizer {c₁} := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.2 htC
  obtain ⟨k, hkC, hkQ⟩ := hsyl (Subgroup.zpowers t) hQp hQc
  set y : G := k⁻¹ * t * k with hy
  have hyS : y ∈ S := hkQ t (Subgroup.mem_zpowers t)
  have hkc₁ : k * c₁ = c₁ * k := Subgroup.mem_centralizer_singleton_iff.1 hkC
  have hkc₁' : k⁻¹ * c₁ * k = c₁ := by
    calc k⁻¹ * c₁ * k = k⁻¹ * (c₁ * k) := by group
      _ = k⁻¹ * (k * c₁) := by rw [← hkc₁]
      _ = c₁ := by group
  have hyC : y * c₁ = c₁ * y := by
    have hmem : y ∈ Subgroup.centralizer {c₁} := by
      rw [hy]
      exact (Subgroup.centralizer {c₁}).mul_mem
        ((Subgroup.centralizer {c₁}).mul_mem
          ((Subgroup.centralizer {c₁}).inv_mem hkC)
          (Subgroup.mem_centralizer_singleton_iff.2 htC)) hkC
    exact Subgroup.mem_centralizer_singleton_iff.1 hmem
  have hy2 : y * y = 1 := by
    rw [hy]
    calc k⁻¹ * t * k * (k⁻¹ * t * k) = k⁻¹ * (t * t) * k := by group
      _ = 1 := by rw [ht2]; group
  have hy1 : y ≠ 1 := by
    rw [hy]
    intro h'
    apply ht1
    calc t = k * (k⁻¹ * t * k) * k⁻¹ := by group
      _ = 1 := by rw [h']; group
  have hyT : y ∈ T := by
    rw [hT]
    exact Subgroup.mem_inf.2 ⟨hyS, Subgroup.mem_centralizer_singleton_iff.2 hyC⟩
  obtain ⟨A, hAx, hA2, hA32⟩ := hx32
  have hS' : ∀ B : Subgroup G, B ≤ S ⊓ Subgroup.centralizer {c₁} →
      (∀ y ∈ B, y * y = 1) → Nat.card B ≠ 32 :=
    fun B hB hB2 hBc => hS32 B (hT ▸ hB) hB2 hBc
  have hnot : ¬ IsConj x c₁ :=
    not_isConj_of_card (S := S) (z := c₁) (y := x) (n := 32) hsyl hS' hAx hA2 hA32
  set g : G := c⁻¹ * k with hg
  have hyg : y = g⁻¹ * x * g := by
    rw [hy, ht, hg]
    group
  have hc₁g : c₁ = g⁻¹ * u * g := by
    calc c₁ = k⁻¹ * c₁ * k := hkc₁'.symm
      _ = k⁻¹ * (c * u * c⁻¹) * k := by rw [hcu]
      _ = g⁻¹ * u * g := by rw [hg]; group
  have hxy : IsConj x y := isConj_iff.2 ⟨g⁻¹, by rw [hyg]; group⟩
  have huxc₁y : IsConj (u * x) (c₁ * y) := by
    refine isConj_iff.2 ⟨g⁻¹, ?_⟩
    rw [hc₁g, hyg]
    group
  by_cases hyDu : y ∈ Du
  · rcases hDu y hyDu hy2 hy1 with h' | h'
    · exact absurd (hxy.trans h') hnot
    · exact hxy.trans h'
  · have hc₁y : IsConj (c₁ * y) c₁ := huxc₁y.symm.trans (hxuu.trans hu)
    exact absurd (hxy.trans (hT1 y hyT hyDu hy2 hc₁y)) hnot

end Stroth47Inv1

namespace Stroth47Core

variable {G : Type*} [Group G] {D : Subgroup G} {m : ℕ} (dD : StrothWeakTypeData D (.t200 m))
  {e : G}

theorem mul_self_ofTorus_mul_of_action {σ : G} {φ : Torus (StrothTypeIndex.t200 m).k →+
    Torus (StrothTypeIndex.t200 m).k}
    (hσ2 : σ * σ = 1) (hconj : ∀ v, σ⁻¹ * dD.ofTorus v * σ = dD.ofTorus (φ v))
    (v : Torus (StrothTypeIndex.t200 m).k) :
    (dD.ofTorus v * σ) * (dD.ofTorus v * σ) = dD.ofTorus (v + φ v) := by
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  calc (dD.ofTorus v * σ) * (dD.ofTorus v * σ)
      = dD.ofTorus v * (σ * dD.ofTorus v * σ) := by group
    _ = dD.ofTorus v * (σ⁻¹ * dD.ofTorus v * σ) := by rw [hσinv]
    _ = dD.ofTorus v * dD.ofTorus (φ v) := by rw [hconj v]
    _ = dD.ofTorus (v + φ v) := by rw [← dD.ofTorus_add]

theorem conj_ofTorus_mul_of_action {σ : G} {φ : Torus (StrothTypeIndex.t200 m).k →+
    Torus (StrothTypeIndex.t200 m).k}
    (hσ2 : σ * σ = 1) (hconj : ∀ v, σ⁻¹ * dD.ofTorus v * σ = dD.ofTorus (φ v))
    (q v : Torus (StrothTypeIndex.t200 m).k) :
    (dD.ofTorus q)⁻¹ * (dD.ofTorus v * σ) * dD.ofTorus q =
      dD.ofTorus (v + φ q - q) * σ := by
  have hq : dD.ofTorus q * σ = σ * dD.ofTorus (φ q) := by
    calc dD.ofTorus q * σ = σ * (σ⁻¹ * dD.ofTorus q * σ) := by group
      _ = σ * dD.ofTorus (φ q) := by rw [hconj q]
  have hσq : σ * dD.ofTorus q = dD.ofTorus (φ q) * σ := by
    calc σ * dD.ofTorus q
        = σ * dD.ofTorus q * (σ * σ) := by rw [hσ2, mul_one]
      _ = σ * (dD.ofTorus q * σ) * σ := by group
      _ = σ * (σ * dD.ofTorus (φ q)) * σ := by rw [hq]
      _ = (σ * σ) * dD.ofTorus (φ q) * σ := by group
      _ = dD.ofTorus (φ q) * σ := by rw [hσ2, one_mul]
  calc (dD.ofTorus q)⁻¹ * (dD.ofTorus v * σ) * dD.ofTorus q
      = dD.ofTorus (-q) * (dD.ofTorus v * (σ * dD.ofTorus q)) := by
          rw [dD.ofTorus_neg]; group
    _ = dD.ofTorus (-q) * (dD.ofTorus v * (dD.ofTorus (φ q) * σ)) := by rw [hσq]
    _ = (dD.ofTorus (-q) * dD.ofTorus v) * (dD.ofTorus (φ q) * σ) := by group
    _ = dD.ofTorus (-q + v) * (dD.ofTorus (φ q) * σ) := by rw [dD.ofTorus_add]
    _ = (dD.ofTorus (-q + v) * dD.ofTorus (φ q)) * σ := by group
    _ = dD.ofTorus (-q + v + φ q) * σ := by
        rw [← dD.ofTorus_add]
    _ = dD.ofTorus (v + φ q - q) * σ := by
        congr 1
        abel_nf

theorem conj_mul_e_of_action {σ : G} {φ : Torus (StrothTypeIndex.t200 m).k →+
    Torus (StrothTypeIndex.t200 m).k} {w : Torus (StrothTypeIndex.t200 m).k}
    (hσ2 : σ * σ = 1) (hconj : ∀ v, σ * dD.ofTorus v * σ = dD.ofTorus (φ v))
    (he : σ * e * σ = dD.ofTorus w * e) (v : Torus (StrothTypeIndex.t200 m).k) :
    σ⁻¹ * (dD.ofTorus v * e) * σ = dD.ofTorus (φ v + w) * e := by
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσ2
  calc σ⁻¹ * (dD.ofTorus v * e) * σ
      = (σ * dD.ofTorus v * σ) * (σ * e * σ) := by
          rw [hσinv]
          rw [show (σ * dD.ofTorus v * σ) * (σ * e * σ) =
            σ * dD.ofTorus v * (σ * σ) * e * σ by group]
          rw [hσ2]
          group
    _ = dD.ofTorus (φ v) * (dD.ofTorus w * e) := by rw [hconj, he]
    _ = dD.ofTorus (φ v + w) * e := by
        rw [← mul_assoc, ← dD.ofTorus_add]

theorem t200inv1_φue {j p : ℕ} (hrel : Rel34inv dD e j 1 p) (x : Fin 3 → ℤ) :
    (dD.t200inv1EAction hrel).φe
        ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ x)) =
      Torus.ofInt _ ![-x 0, (-1 + (j : ℤ)) * x 2, (-1 + (j : ℤ)) * x 1] := by
  rw [t200_φu, StrothWeakTypeData.t200inv1_φe dD hrel]
  congr 1

theorem t200inv1_conj_Due {j p : ℕ} (hm : 1 ≤ m) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 p) :
    ∀ d ∈ D, d * (dD.u * e) * (d * (dD.u * e)) = 1 →
      ∃ q ∈ D, q⁻¹ * (d * (dD.u * e)) * q = dD.u * e ∨
        q⁻¹ * (d * (dD.u * e)) * q = (dD.c : G) * (dD.u * e) := by
  have _ := hm
  have _ := hj
  classical
  intro d hd hsq
  obtain ⟨v, rfl⟩ := dD.exists_ofTorus hd
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  let hE := dD.t200inv1EAction hrel
  set qv : Torus (StrothTypeIndex.t200 m).k := Torus.ofInt _ ![x 0 / 2, 0, x 2] with hqv
  refine ⟨dD.ofTorus qv, dD.ofTorus_mem qv, ?_⟩
  have hue2 : (dD.u * e) * (dD.u * e) = 1 := by
    have heu : e * dD.u = dD.u * e := by
      have h := hrel.u_conj
      have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hrel.e_sq
      rw [hei] at h
      calc e * dD.u = (e * dD.u * e) * e := by
            rw [show (e * dD.u * e) * e = e * dD.u * (e * e) by group,
              hrel.e_sq, mul_one]
        _ = dD.u * e := by rw [h]
    calc (dD.u * e) * (dD.u * e)
        = dD.u * (e * dD.u) * e := by group
      _ = dD.u * (dD.u * e) * e := by rw [heu]
      _ = (dD.u * dD.u) * (e * e) := by group
      _ = 1 := by rw [dD.u_sq, hrel.e_sq, one_mul]
  have hueConj : ∀ w, (dD.u * e)⁻¹ * dD.ofTorus w * (dD.u * e) =
      dD.ofTorus (hE.φe ((StrothTypeIndex.t200 m).action.φu w)) := by
    intro w
    have hui : dD.u⁻¹ = dD.u := inv_eq_of_mul_eq_one_right dD.u_sq
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hrel.e_sq
    have huw : dD.u * dD.ofTorus w * dD.u =
        dD.ofTorus ((StrothTypeIndex.t200 m).action.φu w) := by
      calc dD.u * dD.ofTorus w * dD.u
          = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu w) * dD.u * dD.u := by
              rw [dD.u_mul_ofTorus]
        _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φu w) := by
            rw [mul_assoc, dD.u_sq, mul_one]
    calc (dD.u * e)⁻¹ * dD.ofTorus w * (dD.u * e)
        = e * (dD.u * dD.ofTorus w * dD.u) * e := by rw [mul_inv_rev, hui, hei]; group
      _ = e * dD.ofTorus ((StrothTypeIndex.t200 m).action.φu w) * e := by rw [huw]
      _ = dD.ofTorus (hE.φe ((StrothTypeIndex.t200 m).action.φu w)) := by
          have h := hE.conj_ofTorus ((StrothTypeIndex.t200 m).action.φu w)
          rwa [hei] at h
  have hsq' : dD.ofTorus (Torus.ofInt _ x + hE.φe
      ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ x))) = 1 := by
    change dD.ofTorus (Torus.ofInt _ x +
      (hE.φe.comp ((StrothTypeIndex.t200 m).action.φu)) (Torus.ofInt _ x)) = 1
    rw [← mul_self_ofTorus_mul_of_action dD
      (φ := hE.φe.comp ((StrothTypeIndex.t200 m).action.φu)) hue2 hueConj]
    exact hsq
  have hxof : Torus.ofInt (StrothTypeIndex.t200 m).k x =
      Torus.ofInt (StrothTypeIndex.t200 m).k
        (![x 0, x 1, x 2] : Fin 3 → ℤ) := by
    congr 1
    funext i
    fin_cases i <;> rfl
  have hsum : Torus.ofInt _ x + hE.φe
      ((StrothTypeIndex.t200 m).action.φu (Torus.ofInt _ x)) =
      Torus.ofInt _ ![x 0 + -x 0, x 1 + (-1 + (j : ℤ)) * x 2,
        x 2 + (-1 + (j : ℤ)) * x 1] := by
    rw [hxof, t200inv1_φue dD hrel, t200_add_vec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  rw [hsum, dD.ofTorus_eq_one_iff, t200_ofInt_eq_zero_iff] at hsq'
  obtain ⟨-, hdiv, -⟩ := hsq'
  simp only [Matrix.cons_val_one] at hdiv
  have hφq : hE.φe ((StrothTypeIndex.t200 m).action.φu qv) =
      Torus.ofInt _ ![-(x 0 / 2), (-1 + (j : ℤ)) * x 2, 0] := by
    rw [hqv, t200inv1_φue dD hrel]
    congr 1
    funext i
    fin_cases i <;> simp
  have hcoe : Torus.ofInt _ x + (hE.φe.comp
      ((StrothTypeIndex.t200 m).action.φu)) qv - qv =
      Torus.ofInt _ ![x 0 % 2, 0, 0] := by
    change Torus.ofInt _ x + hE.φe
      ((StrothTypeIndex.t200 m).action.φu qv) - qv = _
    rw [hxof, hφq, hqv, t200_add_vec, t200_sub_vec, t200_ofInt_eq_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine ⟨?_, ?_, ?_⟩
    · have hx : x 0 % 2 = x 0 - 2 * (x 0 / 2) := by
        have h := Int.emod_add_mul_ediv (x 0) 2
        omega
      rw [hx]
      rw [show x 0 - 2 * (x 0 / 2) - (x 0 + -(x 0 / 2) - x 0 / 2) = 0 by ring]
      exact dvd_zero _
    · simpa using dvd_neg.mpr hdiv
    · simp
  have hconj := conj_ofTorus_mul_of_action dD
    (φ := hE.φe.comp ((StrothTypeIndex.t200 m).action.φu)) hue2 hueConj qv
    (Torus.ofInt _ x)
  rw [hcoe] at hconj
  rcases Int.emod_two_eq_zero_or_one (x 0) with hx0 | hx0
  · left
    rw [hx0] at hconj
    simpa [dD.ofTorus_ofInt] using hconj
  · right
    rw [hx0] at hconj
    have hc : dD.ofTorus (Torus.ofInt _ ![(1 : ℤ), 0, 0]) = (dD.c : G) := by
      rw [dD.ofTorus_ofInt]
      simp
    rw [hc] at hconj
    exact hconj

theorem t200inv1_t_e_t {j : ℕ} (hrel : Rel34inv dD e j 1 2) (hj : j = 0) :
    dD.t * e * dD.t = dD.ofTorus (Torus.ofInt _ ![0, 2, 0]) * e := by
  let hE := dD.t200inv1EAction hrel
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hrel.e_sq
  have h1 : e * dD.t * e = dD.ofTorus hE.wt * dD.t := by
    have h := hE.conj_t
    rwa [hei] at h
  have het : dD.t * e * dD.t = e * dD.ofTorus hE.wt := by
    calc dD.t * e * dD.t = e * (e * dD.t * e) * dD.t := by
          rw [show e * (e * dD.t * e) * dD.t =
            (e * e) * (dD.t * e * dD.t) by group, hrel.e_sq, one_mul]
      _ = e * (dD.ofTorus hE.wt * dD.t) * dD.t := by rw [h1]
      _ = e * dD.ofTorus hE.wt := by
          rw [show e * (dD.ofTorus hE.wt * dD.t) * dD.t =
            e * dD.ofTorus hE.wt * (dD.t * dD.t) by group, dD.t_sq, mul_one]
  have hwt : hE.φe hE.wt = Torus.ofInt _ ![0, 2, 0] := by
    change hE.φe (Torus.ofInt _ ![0, -(2 : ℤ), 0]) = _
    rw [StrothWeakTypeData.t200inv1_φe dD hrel]
    congr 1
    funext i
    fin_cases i <;> simp [hj]
  calc dD.t * e * dD.t = e * dD.ofTorus hE.wt := het
    _ = dD.ofTorus (hE.φe hE.wt) * e := hE.e_mul_ofTorus hE.wt
    _ = dD.ofTorus (Torus.ofInt _ ![0, 2, 0]) * e := by rw [hwt]

theorem t200inv1_uv_e_uv {j : ℕ} (hrel : Rel34inv dD e j 1 2) (hj : j = 0) :
    dD.uv * e * dD.uv = dD.ofTorus (Torus.ofInt _ ![(-2 : ℤ), -2, -2]) * e := by
  let hE := dD.t200inv1EAction hrel
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right hrel.e_sq
  have h1 : e * dD.uv * e = dD.ofTorus hE.wuv * dD.uv := by
    have h := hE.conj_uv
    rwa [hei] at h
  have heuv : dD.uv * e * dD.uv = e * dD.ofTorus hE.wuv := by
    calc dD.uv * e * dD.uv = e * (e * dD.uv * e) * dD.uv := by
          rw [show e * (e * dD.uv * e) * dD.uv =
            (e * e) * (dD.uv * e * dD.uv) by group, hrel.e_sq, one_mul]
      _ = e * (dD.ofTorus hE.wuv * dD.uv) * dD.uv := by rw [h1]
      _ = e * dD.ofTorus hE.wuv := by
          rw [show e * (dD.ofTorus hE.wuv * dD.uv) * dD.uv =
            e * dD.ofTorus hE.wuv * (dD.uv * dD.uv) by group, dD.uv_sq, mul_one]
  have hwuv : hE.φe hE.wuv = Torus.ofInt _ ![(-2 : ℤ), -2, -2] := by
    change hE.φe (Torus.ofInt _ ![2, 2, 2]) = _
    rw [StrothWeakTypeData.t200inv1_φe dD hrel]
    congr 1
    funext i
    fin_cases i <;> simp [hj]
  calc dD.uv * e * dD.uv = e * dD.ofTorus hE.wuv := heuv
    _ = dD.ofTorus (hE.φe hE.wuv) * e := hE.e_mul_ofTorus hE.wuv
    _ = dD.ofTorus (Torus.ofInt _ ![(-2 : ℤ), -2, -2]) * e := by rw [hwuv]

theorem t200inv1_t_conj_mul_e {j : ℕ} (hrel : Rel34inv dD e j 1 2) (hj : j = 0)
    (v : Torus (StrothTypeIndex.t200 m).k) :
    dD.t⁻¹ * (dD.ofTorus v * e) * dD.t =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φt v +
        Torus.ofInt _ ![0, 2, 0]) * e := by
  have ht : ∀ w, dD.t * dD.ofTorus w * dD.t =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φt w) := by
    intro w
    calc dD.t * dD.ofTorus w * dD.t
        = dD.ofTorus ((StrothTypeIndex.t200 m).action.φt w) * dD.t * dD.t := by
            rw [dD.t_mul_ofTorus]
      _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φt w) := by
          rw [mul_assoc, dD.t_sq, mul_one]
  exact conj_mul_e_of_action dD dD.t_sq ht (t200inv1_t_e_t dD hrel hj) v

theorem t200inv1_uv_conj_mul_e {j : ℕ} (hrel : Rel34inv dD e j 1 2) (hj : j = 0)
    (v : Torus (StrothTypeIndex.t200 m).k) :
    dD.uv⁻¹ * (dD.ofTorus v * e) * dD.uv =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv v +
        Torus.ofInt _ ![(-2 : ℤ), -2, -2]) * e := by
  have huv : ∀ w, dD.uv * dD.ofTorus w * dD.uv =
      dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv w) := by
    intro w
    calc dD.uv * dD.ofTorus w * dD.uv
        = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv w) * dD.uv * dD.uv := by
            rw [dD.uv_mul_ofTorus]
      _ = dD.ofTorus ((StrothTypeIndex.t200 m).action.φuv w) := by
          rw [mul_assoc, dD.uv_sq, mul_one]
  exact conj_mul_e_of_action dD dD.uv_sq huv (t200inv1_uv_e_uv dD hrel hj) v

theorem t200inv1_conj_De_one {j : ℕ} (hm : m = 1) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 2) :
    ∀ d ∈ D, d * e * (d * e) = 1 →
      (∃ q ∈ D, q⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * (d * e)) * q = e ∨
        q⁻¹ * ((dD.c : G) ^ 2 ^ (m - 1) * (d * e)) * q = (dD.c : G) ^ 2 ^ (m - 1) * e) ∨
      ∃ q ∈ D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e,
        q⁻¹ * (d * e) * q = (dD.c : G) ^ 2 ^ (m - 1) * (d * e) := by
  classical
  subst m
  intro d hd hsq
  obtain ⟨v, rfl⟩ := dD.exists_ofTorus hd
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  let hE := dD.t200inv1EAction hrel
  have heConj : ∀ w, e⁻¹ * dD.ofTorus w * e = dD.ofTorus (hE.φe w) := hE.conj_ofTorus
  have hconjD : ∀ q w, (dD.ofTorus q)⁻¹ * (dD.ofTorus w * e) * dD.ofTorus q =
      dD.ofTorus (w + hE.φe q - q) * e :=
    fun q w => conj_ofTorus_mul_of_action dD hrel.e_sq heConj q w
  have hxof : Torus.ofInt (StrothTypeIndex.t200 1).k x =
      Torus.ofInt (StrothTypeIndex.t200 1).k (![x 0, x 1, x 2] : Fin 3 → ℤ) := by
    congr 1
    funext i
    fin_cases i <;> rfl
  have hsq0 : dD.ofTorus (Torus.ofInt _ x + hE.φe (Torus.ofInt _ x)) = 1 := by
    rw [← mul_self_ofTorus_mul_of_action dD (φ := hE.φe) hrel.e_sq heConj]
    exact hsq
  have hcvec : dD.ofTorus (Torus.ofInt _ ![(1 : ℤ), 0, 0]) = (dD.c : G) := by
    rw [dD.ofTorus_ofInt]
    simp
  have hc1 : (dD.c : G) ^ 2 ^ ((1 : ℕ) - 1) = (dD.c : G) := by norm_num
  have hassoc : ∀ a b c : Torus (StrothTypeIndex.t200 1).k, a + b - c = a + (b - c) :=
    fun a b c => by abel
  rw [hc1]
  rcases hj with hj0 | hj4
  ·
    have hcy0 : (dD.c : G) * (dD.ofTorus (Torus.ofInt _ x) * e) =
        dD.ofTorus (Torus.ofInt _ ![(1 : ℤ), 0, 0] + Torus.ofInt _ x) * e := by
      calc (dD.c : G) * (dD.ofTorus (Torus.ofInt _ x) * e)
          = (dD.ofTorus (Torus.ofInt _ ![(1 : ℤ), 0, 0]) *
              dD.ofTorus (Torus.ofInt _ x)) * e := by rw [← hcvec]; group
        _ = dD.ofTorus (Torus.ofInt _ ![(1 : ℤ), 0, 0] + Torus.ofInt _ x) * e := by
            rw [← dD.ofTorus_add]
    set q0 : Torus (StrothTypeIndex.t200 1).k :=
      Torus.ofInt _ ![0, x 1 / 2, x 2 / 2] with hq0
    have hφq0 : hE.φe q0 = Torus.ofInt _ ![0, -(x 1 / 2), -(x 2 / 2)] := by
      rw [hq0, StrothWeakTypeData.t200inv1_φe dD hrel]
      congr 1
      funext i
      fin_cases i <;> simp [hj0]
    have hcoef0 : Torus.ofInt _ x + hE.φe q0 - q0 =
        Torus.ofInt _ ![x 0, x 1 % 2, x 2 % 2] := by
      rw [hxof, hq0, hφq0, t200_add_vec, t200_sub_vec, t200_ofInt_eq_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      refine ⟨?_, ?_, ?_⟩
      · rw [show x 0 - (x 0 + 0 - 0) = 0 by ring]
        exact dvd_zero _
      · have hx1mod : x 1 % 2 = x 1 - 2 * (x 1 / 2) := by
          have h := Int.emod_add_mul_ediv (x 1) 2
          omega
        rw [hx1mod]
        rw [show x 1 - 2 * (x 1 / 2) - (x 1 + -(x 1 / 2) - x 1 / 2) = 0 by ring]
        exact dvd_zero _
      · have hx2mod : x 2 % 2 = x 2 - 2 * (x 2 / 2) := by
          have h := Int.emod_add_mul_ediv (x 2) 2
          omega
        rw [hx2mod]
        rw [show x 2 - 2 * (x 2 / 2) - (x 2 + -(x 2 / 2) - x 2 / 2) = 0 by ring]
        exact dvd_zero _
    rcases Int.emod_two_eq_zero_or_one (x 2) with hε2 | hε2
    ·
      rcases Int.emod_two_eq_zero_or_one (x 1) with hε1 | hε1
      ·
        have hcoef0c : (Torus.ofInt _ ![(1 : ℤ), 0, 0] + Torus.ofInt _ x +
            hE.φe q0 - q0) = Torus.ofInt _ ![x 0 + 1, 0, 0] := by
          rw [show Torus.ofInt _ ![(1 : ℤ), 0, 0] + Torus.ofInt _ x + hE.φe q0 - q0 =
            Torus.ofInt _ ![(1 : ℤ), 0, 0] +
              (Torus.ofInt _ x + hE.φe q0 - q0) by abel]
          rw [hcoef0, show x 1 % 2 = 0 from hε1, show x 2 % 2 = 0 from hε2,
            t200_add_vec]
          congr 1
          funext i
          fin_cases i <;> simp
          ring
        refine Or.inl ⟨dD.ofTorus q0, dD.ofTorus_mem q0, ?_⟩
        rw [hcy0, hconjD q0 (Torus.ofInt _ ![(1 : ℤ), 0, 0] + Torus.ofInt _ x),
          hcoef0c]
        rcases Int.emod_two_eq_zero_or_one (x 0 + 1) with hpar | hpar
        · left
          have hzero : Torus.ofInt (StrothTypeIndex.t200 1).k
              (![x 0 + 1, 0, 0] : Fin 3 → ℤ) = 0 := by
            rw [t200_ofInt_eq_zero_iff]
            refine ⟨?_, by norm_num, by norm_num⟩
            simpa using Int.dvd_of_emod_eq_zero hpar
          rw [hzero, dD.ofTorus_zero, one_mul]
        · right
          have hc : Torus.ofInt (StrothTypeIndex.t200 1).k
              (![x 0 + 1, 0, 0] : Fin 3 → ℤ) =
              Torus.ofInt (StrothTypeIndex.t200 1).k
                (![(1 : ℤ), 0, 0] : Fin 3 → ℤ) := by
            rw [t200_ofInt_eq_iff]
            have hx0 : (2 : ℤ) ∣ x 0 := by
              have h0 : x 0 % 2 = 0 := by omega
              exact Int.dvd_of_emod_eq_zero h0
            refine ⟨?_, by norm_num, by norm_num⟩
            simpa using dvd_neg.mpr hx0
          rw [hc, hcvec]
      ·
        set quv : Torus (StrothTypeIndex.t200 1).k :=
          Torus.ofInt _ ![ -((4 * x 0 - x 1 - x 2 + 3) / 2),
            -(2 * x 0 - x 2 + 1), -(2 * x 0 - x 1 + 1)] with hquv
        have hx1eq : x 1 = 2 * (x 1 / 2) + 1 := by
          have h := Int.emod_add_mul_ediv (x 1) 2
          omega
        have hx2eq : x 2 = 2 * (x 2 / 2) := by
          have h := Int.emod_add_mul_ediv (x 2) 2
          omega
        have hmod : (4 * x 0 - x 1 - x 2 + 3) % 2 = 0 := by
          have hdvd : (2 : ℤ) ∣ 4 * x 0 - x 1 - x 2 + 3 :=
            ⟨2 * x 0 - (x 1 / 2) - (x 2 / 2) + 1, by
              linear_combination -hx1eq - hx2eq⟩
          exact Int.emod_eq_zero_of_dvd hdvd
        have hhalf : 2 * ((4 * x 0 - x 1 - x 2 + 3) / 2) =
            4 * x 0 - x 1 - x 2 + 3 := by
          have h := Int.emod_add_mul_ediv (4 * x 0 - x 1 - x 2 + 3) 2
          rw [hmod, zero_add] at h
          exact h
        have hφquv : hE.φe quv - quv = Torus.ofInt _ ![4 * x 0 - x 1 - x 2 + 3,
            4 * x 0 - 2 * x 2 + 2, 4 * x 0 - 2 * x 1 + 2] := by
          rw [hquv, StrothWeakTypeData.t200inv1_φe dD hrel, t200_sub_vec,
            t200_ofInt_eq_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons, hj0]
          refine ⟨?_, ?_, ?_⟩ <;> omega
        have hcoefuv : ((StrothTypeIndex.t200 1).action.φuv (Torus.ofInt _ x) +
            Torus.ofInt _ ![(-2 : ℤ), -2, -2]) + hE.φe quv - quv =
            Torus.ofInt _ ![(1 : ℤ), 0, 0] + Torus.ofInt _ x := by
          rw [hxof, t200_φuv, t200_add_vec, hassoc, hφquv, t200_add_vec,
            t200_add_vec, t200_ofInt_eq_iff]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.head_cons, Matrix.tail_cons]
          all_goals (rw [Int.dvd_iff_emod_eq_zero]; omega)
        refine Or.inr ⟨dD.uv * dD.ofTorus quv, ?_, ?_⟩
        · have huvS : dD.uv ∈
              D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e := by
            have hmem : dD.d8 true false false ∈
              Subgroup.closure {dD.uv, dD.t, dD.u} := dD.d8_mem true false false
            rw [dD.d8_tff] at hmem
            exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hmem)
          exact Subgroup.mul_mem _ huvS
            (Subgroup.mem_sup_left (Subgroup.mem_sup_left (dD.ofTorus_mem quv)))
        · rw [show (dD.uv * dD.ofTorus quv)⁻¹ *
              (dD.ofTorus (Torus.ofInt _ x) * e) * (dD.uv * dD.ofTorus quv) =
            (dD.ofTorus quv)⁻¹ * (dD.uv⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * e) *
              dD.uv) * dD.ofTorus quv by group]
          rw [t200inv1_uv_conj_mul_e dD hrel hj0 (Torus.ofInt _ x)]
          rw [hconjD quv ((StrothTypeIndex.t200 1).action.φuv (Torus.ofInt _ x) +
            Torus.ofInt _ ![(-2 : ℤ), -2, -2])]
          rw [hcoefuv]
          exact hcy0.symm
    ·
      set qt : Torus (StrothTypeIndex.t200 1).k :=
        Torus.ofInt _ ![ -((1 + x 2) / 2), -(x 1 - 2 * x 0 + x 2 - 1), -x 2] with hqt
      have hx2eq : x 2 = 2 * (x 2 / 2) + 1 := by
        have h := Int.emod_add_mul_ediv (x 2) 2
        omega
      have hmod : (1 + x 2) % 2 = 0 := by
        have hdvd : (2 : ℤ) ∣ 1 + x 2 := ⟨x 2 / 2 + 1, by linear_combination hx2eq⟩
        exact Int.emod_eq_zero_of_dvd hdvd
      have hhalf : 2 * ((1 + x 2) / 2) = 1 + x 2 := by
        have h := Int.emod_add_mul_ediv (1 + x 2) 2
        rw [hmod, zero_add] at h
        exact h
      have hφqt : hE.φe qt - qt = Torus.ofInt _ ![1 + x 2,
          2 * x 1 - 4 * x 0 + 2 * x 2 - 2, 2 * x 2] := by
        rw [hqt, StrothWeakTypeData.t200inv1_φe dD hrel, t200_sub_vec,
          t200_ofInt_eq_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons, hj0]
        refine ⟨?_, ?_, ?_⟩ <;> omega
      have hcoeft : ((StrothTypeIndex.t200 1).action.φt (Torus.ofInt _ x) +
          Torus.ofInt _ ![0, 2, 0]) + hE.φe qt - qt =
          Torus.ofInt _ ![(1 : ℤ), 0, 0] + Torus.ofInt _ x := by
        rw [hxof, t200_φt, t200_add_vec, hassoc, hφqt, t200_add_vec,
          t200_add_vec, t200_ofInt_eq_iff]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Matrix.head_cons, Matrix.tail_cons]
        all_goals (rw [Int.dvd_iff_emod_eq_zero]; omega)
      refine Or.inr ⟨dD.t * dD.ofTorus qt, ?_, ?_⟩
      · have htS : dD.t ∈
            D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e := by
          have hmem : dD.d8 false true false ∈
            Subgroup.closure {dD.uv, dD.t, dD.u} := dD.d8_mem false true false
          rw [dD.d8_ftf] at hmem
          exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hmem)
        exact Subgroup.mul_mem _ htS
          (Subgroup.mem_sup_left (Subgroup.mem_sup_left (dD.ofTorus_mem qt)))
      · rw [show (dD.t * dD.ofTorus qt)⁻¹ *
            (dD.ofTorus (Torus.ofInt _ x) * e) * (dD.t * dD.ofTorus qt) =
          (dD.ofTorus qt)⁻¹ * (dD.t⁻¹ * (dD.ofTorus (Torus.ofInt _ x) * e) *
            dD.t) * dD.ofTorus qt by group]
        rw [t200inv1_t_conj_mul_e dD hrel hj0 (Torus.ofInt _ x)]
        rw [hconjD qt ((StrothTypeIndex.t200 1).action.φt (Torus.ofInt _ x) +
          Torus.ofInt _ ![0, 2, 0])]
        rw [hcoeft]
        exact hcy0.symm
  · norm_num at hj4
    have hsum4 : Torus.ofInt _ x + hE.φe (Torus.ofInt _ x) =
        Torus.ofInt _ ![0, 4 * x 1, 4 * x 2] := by
      rw [hxof, StrothWeakTypeData.t200inv1_φe dD hrel, t200_add_vec]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      congr 1
      funext i
      fin_cases i <;> simp [hj4] <;> ring
    rw [hsum4, dD.ofTorus_eq_one_iff, t200_ofInt_eq_zero_iff] at hsq0
    obtain ⟨-, hdiv1, hdiv2⟩ := hsq0
    norm_num at hdiv1 hdiv2
    have hx1even : (2 : ℤ) ∣ x 1 := by
      obtain ⟨c, hc⟩ := hdiv1
      exact ⟨c, by nlinarith⟩
    have hx2even : (2 : ℤ) ∣ x 2 := by
      obtain ⟨c, hc⟩ := hdiv2
      exact ⟨c, by nlinarith⟩
    have hx1half : x 1 = 2 * (x 1 / 2) := by
      have h := Int.emod_add_mul_ediv (x 1) 2
      rw [Int.emod_eq_zero_of_dvd hx1even, zero_add] at h
      exact h.symm
    have hx2half : x 2 = 2 * (x 2 / 2) := by
      have h := Int.emod_add_mul_ediv (x 2) 2
      rw [Int.emod_eq_zero_of_dvd hx2even, zero_add] at h
      exact h.symm
    set qv : Torus (StrothTypeIndex.t200 1).k :=
      Torus.ofInt _ ![0, -(x 1 / 2), -(x 2 / 2)] with hqv
    refine Or.inl ⟨dD.ofTorus qv, dD.ofTorus_mem qv, ?_⟩
    have hφq : hE.φe qv =
        Torus.ofInt _ ![0, 3 * (-(x 1 / 2)), 3 * (-(x 2 / 2))] := by
      rw [hqv, StrothWeakTypeData.t200inv1_φe dD hrel]
      congr 1
      funext i
      fin_cases i <;> simp [hj4]
    have hcoef : Torus.ofInt _ ![(1 : ℤ), 0, 0] + Torus.ofInt _ x + hE.φe qv - qv =
        Torus.ofInt _ ![x 0 + 1, 0, 0] := by
      rw [hxof, hqv, hφq, t200_add_vec, t200_add_vec, t200_sub_vec,
        t200_ofInt_eq_iff]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      refine ⟨?_, ?_, ?_⟩
      · rw [show x 0 + 1 - (1 + x 0 + 0 - 0) = 0 by ring]
        exact dvd_zero _
      · rw [show 0 - (0 + x 1 + 3 * (-(x 1 / 2)) - (-(x 1 / 2))) = 0 by
          linear_combination -hx1half]
        exact dvd_zero _
      · rw [show 0 - (0 + x 2 + 3 * (-(x 2 / 2)) - (-(x 2 / 2))) = 0 by
          linear_combination -hx2half]
        exact dvd_zero _
    have hcy : (dD.c : G) * (dD.ofTorus (Torus.ofInt _ x) * e) =
        dD.ofTorus (Torus.ofInt _ ![(1 : ℤ), 0, 0] + Torus.ofInt _ x) * e := by
      calc (dD.c : G) * (dD.ofTorus (Torus.ofInt _ x) * e)
          = (dD.ofTorus (Torus.ofInt _ ![(1 : ℤ), 0, 0]) *
              dD.ofTorus (Torus.ofInt _ x)) * e := by rw [← hcvec]; group
        _ = dD.ofTorus (Torus.ofInt _ ![(1 : ℤ), 0, 0] + Torus.ofInt _ x) * e := by
            rw [← dD.ofTorus_add]
    rw [hcy, hconjD qv (Torus.ofInt _ ![(1 : ℤ), 0, 0] + Torus.ofInt _ x),
      hcoef]
    rcases Int.emod_two_eq_zero_or_one (x 0 + 1) with hpar | hpar
    · left
      have hzero : Torus.ofInt (StrothTypeIndex.t200 1).k
          (![x 0 + 1, 0, 0] : Fin 3 → ℤ) = 0 := by
        rw [t200_ofInt_eq_zero_iff]
        refine ⟨?_, by norm_num, by norm_num⟩
        simpa using Int.dvd_of_emod_eq_zero hpar
      rw [hzero, dD.ofTorus_zero, one_mul]
    · right
      have hc : Torus.ofInt (StrothTypeIndex.t200 1).k
            (![x 0 + 1, 0, 0] : Fin 3 → ℤ) =
          Torus.ofInt (StrothTypeIndex.t200 1).k
            (![(1 : ℤ), 0, 0] : Fin 3 → ℤ) := by
        rw [t200_ofInt_eq_iff]
        have hx0 : (2 : ℤ) ∣ x 0 := by
          have h0 : x 0 % 2 = 0 := by omega
          exact Int.dvd_of_emod_eq_zero h0
        refine ⟨?_, by norm_num, by norm_num⟩
        simpa using dvd_neg.mpr hx0
      rw [hc, hcvec]

theorem t200inv1_isConj_of_mul_one [Finite G] {j : ℕ} (hm : m = 1) (hj : j = 0 ∨ j = 2 ^ (m + 1))
    (hrel : Rel34inv dD e j 1 2)
    (hR : ∀ y : G, IsConj y ((dD.c : G) ^ 2 ^ (m - 1)) → ∀ A : Subgroup G,
      A ≤ Subgroup.centralizer {y} → (∀ x ∈ A, x * x = 1) → Nat.card A ≠ 32)
    (hU1 : (∃ A : Subgroup G, A ≤ Subgroup.centralizer {e} ∧ (∀ x ∈ A, x * x = 1) ∧
        Nat.card A = 32) ∧
      ∃ A : Subgroup G, A ≤ Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1) * e} ∧
        (∀ x ∈ A, x * x = 1) ∧ Nat.card A = 32)
    (hβ : ¬ IsConj (dD.u * e) ((dD.c : G) ^ 2 ^ (m - 1)) ∧
      ¬ IsConj ((dD.c : G) ^ 2 ^ (m - 1) * (dD.u * e)) ((dD.c : G) ^ 2 ^ (m - 1))) :
    ∀ k ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔ Subgroup.zpowers e) ⊓
        Subgroup.centralizer {(dD.c : G) ^ 2 ^ (m - 1)},
      k ∉ D ⊔ Subgroup.zpowers dD.u → k * k = 1 →
        IsConj ((dD.c : G) ^ 2 ^ (m - 1) * k) ((dD.c : G) ^ 2 ^ (m - 1)) →
          IsConj k ((dD.c : G) ^ 2 ^ (m - 1)) := by
  classical
  subst m
  simp only [Nat.sub_self, pow_zero, pow_one] at hR hU1 hβ ⊢
  intro k hk hkDu hk2 hck
  obtain ⟨hkS, hkC⟩ := Subgroup.mem_inf.mp hk
  let hE := dD.t200inv1EAction hrel
  have hf : Even j := by
    rcases hj with rfl | hj4
    · exact ⟨0, rfl⟩
    · norm_num at hj4
      exact ⟨2, by omega⟩
  have hc₁fix : hE.φe (om200 1 ![1, 0, 0]) = om200 1 ![1, 0, 0] :=
    t200inv1_φe_om dD hrel (by norm_num) hf _
  have hk' : k ∈ (D ⊔ Subgroup.closure {dD.uv, dD.t, dD.u} ⊔
      Subgroup.zpowers e) ⊓
      Subgroup.centralizer {((dD.c : G) ^ 2 ^ ((1 : ℕ) - 1))} := by
    simpa using hk
  have hkNF := t200_eAction_mem_CSc₁ dD hE hc₁fix (by norm_num) hk'
  obtain ⟨v, l, b, hk_eq⟩ := hkNF
  have hc1 : (dD.c : G) ^ 2 ^ ((1 : ℕ) - 1) = (dD.c : G) := by norm_num
  have hc2 : (dD.c : G) * (dD.c : G) = 1 := by
    rw [dD.c_eq, ← dD.ofTorus_add, ← dD.ofTorus_zero]
    congr 1
    funext i
    fin_cases i <;> simp [Torus.c, gen]
    decide
  have hmemD : dD.ofTorus v ∈ D := dD.ofTorus_mem v
  cases l with
  | false =>
    cases b with
    | false =>
      have hkD : k ∈ D ⊔ Subgroup.zpowers dD.u := by
        rw [hk_eq]
        simp only [StrothWeakTypeData.d8, Bool.false_eq_true, ↓reduceIte,
          Stroth42Core.bpow, mul_one]
        exact Subgroup.mem_sup_left hmemD
      exact absurd hkD hkDu
    | true =>
      have hk_e : k = dD.ofTorus v * e := by
        rw [hk_eq]
        simp only [StrothWeakTypeData.d8, Bool.false_eq_true, ↓reduceIte,
          Stroth42Core.bpow, mul_one]
      have hsq : (dD.ofTorus v * e) * (dD.ofTorus v * e) = 1 := by
        rw [← hk_e]; exact hk2
      have hck' : IsConj ((dD.c : G) * (dD.ofTorus v * e)) (dD.c : G) := by
        rw [← hk_e]; exact hck
      rcases t200inv1_conj_De_one dD rfl hj hrel (dD.ofTorus v) hmemD hsq with
        ⟨q, -, hq | hq⟩ | ⟨q, hqS, hq⟩
      · exfalso
        rw [hc1] at hq
        obtain ⟨Ae, hAe, hAe2, hAe32⟩ := hU1.1
        have hx_e : IsConj ((dD.c : G) * (dD.ofTorus v * e)) e :=
          isConj_iff.2 ⟨q⁻¹, by rw [inv_inv]; exact hq⟩
        have hec : IsConj e (dD.c : G) := (hx_e.symm).trans hck'
        exact absurd hAe32 (hR e hec Ae hAe hAe2)
      · exfalso
        rw [hc1] at hq
        obtain ⟨Ace, hAce, hAce2, hAce32⟩ := hU1.2
        have hx_ce : IsConj ((dD.c : G) * (dD.ofTorus v * e)) ((dD.c : G) * e) :=
          isConj_iff.2 ⟨q⁻¹, by rw [inv_inv]; exact hq⟩
        have hcec : IsConj ((dD.c : G) * e) (dD.c : G) := (hx_ce.symm).trans hck'
        exact absurd hAce32 (hR ((dD.c : G) * e) hcec Ace hAce hAce2)
      · rw [hc1] at hq
        have hq' : q⁻¹ * k * q = (dD.c : G) * k := by
          rw [hk_e]; exact hq
        exact (isConj_iff.2 ⟨q⁻¹, by rw [inv_inv]; exact hq'⟩).trans hck
  | true =>
    cases b with
    | false =>
      have hk_mem : k ∈ D ⊔ Subgroup.zpowers dD.u := by
        rw [hk_eq]
        simp only [StrothWeakTypeData.d8, Bool.false_eq_true, ↓reduceIte,
          Stroth42Core.bpow, mul_one, one_mul]
        exact Subgroup.mul_mem _
          (Subgroup.mem_sup_left hmemD)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers dD.u))
      exact absurd hk_mem hkDu
    | true =>
      have hk_ue : k = dD.ofTorus v * (dD.u * e) := by
        rw [hk_eq]
        simp only [StrothWeakTypeData.d8, Bool.false_eq_true, ↓reduceIte,
          Stroth42Core.bpow, one_mul]
        rw [mul_assoc]
      have hsq : (dD.ofTorus v * (dD.u * e)) *
          (dD.ofTorus v * (dD.u * e)) = 1 := by
        rw [← hk_ue]; exact hk2
      have hck' : IsConj ((dD.c : G) * (dD.ofTorus v * (dD.u * e))) (dD.c : G) := by
        rw [← hk_ue]; exact hck
      rcases t200inv1_conj_Due dD (m := 1) (by norm_num) hj hrel
        (dD.ofTorus v) hmemD hsq with ⟨q, hqD, hq⟩
      obtain ⟨qv, rfl⟩ := dD.exists_ofTorus hqD
      rw [← hk_ue] at hq
      have hqcomm : dD.ofTorus qv * (dD.c : G) = (dD.c : G) * dD.ofTorus qv := by
        rw [dD.c_eq, dD.ofTorus_comm]
      have hconj_c : ∀ x : G, (dD.ofTorus qv)⁻¹ * ((dD.c : G) * x) * dD.ofTorus qv =
          (dD.c : G) * ((dD.ofTorus qv)⁻¹ * x * dD.ofTorus qv) := by
        intro x
        have hqinv : (dD.ofTorus qv)⁻¹ * (dD.c : G) =
            (dD.c : G) * (dD.ofTorus qv)⁻¹ := by
          calc (dD.ofTorus qv)⁻¹ * (dD.c : G)
              = ((dD.ofTorus qv)⁻¹ * (dD.c : G) * dD.ofTorus qv) *
                (dD.ofTorus qv)⁻¹ := by group
            _ = ((dD.ofTorus qv)⁻¹ * ((dD.c : G) * dD.ofTorus qv)) *
                (dD.ofTorus qv)⁻¹ := by group
            _ = ((dD.ofTorus qv)⁻¹ * (dD.ofTorus qv * (dD.c : G))) *
                (dD.ofTorus qv)⁻¹ := by rw [hqcomm]
            _ = (dD.c : G) * (dD.ofTorus qv)⁻¹ := by group
        calc (dD.ofTorus qv)⁻¹ * ((dD.c : G) * x) * dD.ofTorus qv
            = ((dD.ofTorus qv)⁻¹ * (dD.c : G)) * x * dD.ofTorus qv := by group
          _ = ((dD.c : G) * (dD.ofTorus qv)⁻¹) * x * dD.ofTorus qv := by rw [hqinv]
          _ = (dD.c : G) * ((dD.ofTorus qv)⁻¹ * x * dD.ofTorus qv) := by group
      have hIs : IsConj ((dD.c : G) * k)
          ((dD.c : G) * ((dD.ofTorus qv)⁻¹ * k * dD.ofTorus qv)) :=
        isConj_iff.2 ⟨(dD.ofTorus qv)⁻¹, by rw [inv_inv]; exact hconj_c k⟩
      rcases hq with hq | hq
      · exfalso
        rw [hq] at hIs
        rw [hk_ue] at hIs
        exact hβ.2 ((hIs.symm).trans hck')
      · exfalso
        rw [hq] at hIs
        rw [hk_ue] at hIs
        have hcc : (dD.c : G) * ((dD.c : G) * (dD.u * e)) = dD.u * e := by
          rw [← mul_assoc, hc2, one_mul]
        rw [hcc] at hIs
        exact hβ.1 ((hIs.symm).trans hck')

end Stroth47Core

end CFSG.CGT.Stroth77
