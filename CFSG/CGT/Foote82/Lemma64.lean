module

import CFSG.Quasithin.Background.G11Basic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115CoverDihedral
import TauCeti.Algebra.CharP.LinearMaps
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

section Aux

open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private instance instFiniteGLV [Finite V] : Finite (GLV V) :=
  Finite.of_injective (fun f : GLV V => (f : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)

private theorem add_self_eq_zero' (w : V) : w + w = 0 := by
  rw [← two_smul (ZMod 2) w, show (2 : ZMod 2) = 0 from rfl, zero_smul]

private theorem neg_eq_self' (w : V) : -w = w := by
  rw [neg_eq_iff_add_eq_zero]
  exact add_self_eq_zero' w

private theorem mem_conj_iff (D : Subgroup (GLV V)) (g x : GLV V) :
    x ∈ D.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ D := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem mem_normalizer_conj_iff (D : Subgroup (GLV V)) (g z : GLV V) :
    z ∈ Subgroup.normalizer
        ((D.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup (GLV V)) : Set (GLV V)) ↔
      g * z * g⁻¹ ∈ Subgroup.normalizer (D : Set (GLV V)) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h m
    have h1 := h (g⁻¹ * m * g)
    rw [mem_conj_iff, mem_conj_iff] at h1
    have e1 : g * (g⁻¹ * m * g) * g⁻¹ = m := by group
    have e2 : g * (z * (g⁻¹ * m * g) * z⁻¹) * g⁻¹ = (g * z * g⁻¹) * m * (g * z * g⁻¹)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  · intro h n
    rw [mem_conj_iff, mem_conj_iff]
    have h1 := h (g * n * g⁻¹)
    have e2 : g * (z * n * z⁻¹) * g⁻¹ = (g * z * g⁻¹) * (g * n * g⁻¹) * (g * z * g⁻¹)⁻¹ := by
      group
    rw [e2]
    exact h1

private theorem conj_mem_centralizer {D : Subgroup (GLV V)} {n z : GLV V}
    (hn : n ∈ Subgroup.normalizer (D : Set (GLV V)))
    (hz : z ∈ Subgroup.centralizer (D : Set (GLV V))) :
    n⁻¹ * z * n ∈ Subgroup.centralizer (D : Set (GLV V)) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro d hd
  have hd' : n * d * n⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hn d).1 hd
  have h1 := hz _ hd'
  calc d * (n⁻¹ * z * n) = n⁻¹ * ((n * d * n⁻¹) * z) * n := by group
    _ = n⁻¹ * (z * (n * d * n⁻¹)) * n := by rw [h1]
    _ = n⁻¹ * z * n * d := by group

private theorem apply_mem_commSpace_conj {x g : GLV V} {w : V}
    (hw : w ∈ commSpace (Subgroup.zpowers (g⁻¹ * x * g)) ⊤) :
    g w ∈ commSpace (Subgroup.zpowers x) ⊤ := by
  have hle : commSpace (Subgroup.zpowers (g⁻¹ * x * g)) ⊤ ≤
      (commSpace (Subgroup.zpowers x) ⊤).comap (g : V →ₗ[ZMod 2] V) := by
    rw [commSpace_le_iff]
    rintro k hk u -
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have hconj : (g⁻¹ * x * g) ^ n = g⁻¹ * x ^ n * g := by
      have := conj_zpow (a := g⁻¹) (b := x) (i := n)
      simpa using this
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, map_sub, hconj, LinearEquiv.mul_apply,
      LinearEquiv.apply_symm_apply, LinearEquiv.coe_inv]
    exact sub_mem_commSpace (Subgroup.zpow_mem_zpowers x n) Submodule.mem_top
  exact hle hw

private structure Lemma64Hyp (G D : Subgroup (GLV V)) : Prop where
  le : D ≤ G
  cent : ∀ a ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V)), orderOf a = 2 →
    G ⊓ Subgroup.centralizer ({a} : Set (GLV V)) ≤ Subgroup.normalizer (D : Set (GLV V))
  conj : ∀ g ∈ G, g ∉ Subgroup.normalizer (D : Set (GLV V)) →
    ¬ ⁅D, D.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≤ D ⊓ D.map (MulAut.conj g⁻¹).toMonoidHom
  fix : ∀ x ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V)), orderOf x = 2 →
    ∀ v ∈ commSpace (Subgroup.zpowers x) ⊤, ∀ d ∈ D, d v = v
  norm : ∀ x ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V)), orderOf x = 2 →
    ∀ v ∈ commSpace (Subgroup.zpowers x) ⊤, v ≠ 0 →
      ∀ g ∈ G, g v = v → g ∈ Subgroup.normalizer (D : Set (GLV V))

private theorem Lemma64Hyp.key {G D : Subgroup (GLV V)} (H : Lemma64Hyp G D) {x y g₁ g₂ : GLV V}
    (hx : x ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V))) (hxo : orderOf x = 2)
    (hy : y ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V))) (hyo : orderOf y = 2)
    (hg₁ : g₁ ∈ G) (hg₂ : g₂ ∈ G) {v : V} (hv0 : v ≠ 0)
    (hv₁ : v ∈ commSpace (Subgroup.zpowers (g₁⁻¹ * x * g₁)) ⊤)
    (hv₂ : v ∈ commSpace (Subgroup.zpowers (g₂⁻¹ * y * g₂)) ⊤) :
    g₂ * g₁⁻¹ ∈ Subgroup.normalizer (D : Set (GLV V)) := by
  have hw₁ := apply_mem_commSpace_conj hv₁
  have hw₂ := apply_mem_commSpace_conj hv₂
  have hw₁0 : g₁ v ≠ 0 := fun h => hv0 ((g₁.map_eq_zero_iff).1 h)
  have hw₂0 : g₂ v ≠ 0 := fun h => hv0 ((g₂.map_eq_zero_iff).1 h)
  have fixes₁ : ∀ e : GLV V, g₁ * e * g₁⁻¹ ∈ D → e v = v := by
    intro e he
    have h1 := H.fix x hx hxo (g₁ v) hw₁ _ he
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h1
    exact g₁.injective h1
  have fixes₂ : ∀ e : GLV V, g₂ * e * g₂⁻¹ ∈ D → e v = v := by
    intro e he
    have h1 := H.fix y hy hyo (g₂ v) hw₂ _ he
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] at h1
    exact g₂.injective h1
  have normalizes₁ : ∀ e ∈ G, e v = v → g₁ * e * g₁⁻¹ ∈ Subgroup.normalizer (D : Set (GLV V)) := by
    intro e heG he
    refine H.norm x hx hxo (g₁ v) hw₁ hw₁0 _ (G.mul_mem (G.mul_mem hg₁ heG) (G.inv_mem hg₁)) ?_
    simp [he]
  have normalizes₂ : ∀ e ∈ G, e v = v → g₂ * e * g₂⁻¹ ∈ Subgroup.normalizer (D : Set (GLV V)) := by
    intro e heG he
    refine H.norm y hy hyo (g₂ v) hw₂ hw₂0 _ (G.mul_mem (G.mul_mem hg₂ heG) (G.inv_mem hg₂)) ?_
    simp [he]
  by_contra hn
  refine H.conj (g₂ * g₁⁻¹) (G.mul_mem hg₂ (G.inv_mem hg₁)) hn ?_
  rw [Subgroup.commutator_le]
  intro d hd e he
  have he' := (mem_conj_iff D (g₂ * g₁⁻¹) e).1 he
  have hA : e ∈ Subgroup.normalizer (D : Set (GLV V)) := by
    have h1 : g₂ * (g₁⁻¹ * e * g₁) * g₂⁻¹ ∈ D := by
      convert he' using 1
      group
    have h2 := fixes₂ _ h1
    have hG : g₁⁻¹ * e * g₁ ∈ G := by
      have heG : e ∈ G := by
        have : (g₂ * g₁⁻¹)⁻¹ * ((g₂ * g₁⁻¹) * e * (g₂ * g₁⁻¹)⁻¹) * (g₂ * g₁⁻¹) ∈ G :=
          G.mul_mem (G.mul_mem (G.inv_mem (G.mul_mem hg₂ (G.inv_mem hg₁))) (H.le he'))
            (G.mul_mem hg₂ (G.inv_mem hg₁))
        convert this using 1
        group
      exact G.mul_mem (G.mul_mem (G.inv_mem hg₁) heG) hg₁
    have h3 := normalizes₁ _ hG h2
    convert h3 using 1
    group
  have hB : d ∈ Subgroup.normalizer
      ((D.map (MulAut.conj (g₂ * g₁⁻¹)⁻¹).toMonoidHom : Subgroup (GLV V)) : Set (GLV V)) := by
    rw [mem_normalizer_conj_iff]
    have h1 : g₁ * (g₁⁻¹ * d * g₁) * g₁⁻¹ ∈ D := by
      convert hd using 1
      group
    have h2 := fixes₁ _ h1
    have hG : g₁⁻¹ * d * g₁ ∈ G :=
      G.mul_mem (G.mul_mem (G.inv_mem hg₁) (H.le hd)) hg₁
    have h3 := normalizes₂ _ hG h2
    convert h3 using 1
    group
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · have h1 : e * d⁻¹ * e⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hA d⁻¹).1 (D.inv_mem hd)
    have : ⁅d, e⁆ = d * (e * d⁻¹ * e⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [this]
    exact D.mul_mem hd h1
  · have h1 : d * e * d⁻¹ ∈ D.map (MulAut.conj (g₂ * g₁⁻¹)⁻¹).toMonoidHom :=
      (Subgroup.mem_normalizer_iff.1 hB e).1 he
    have : ⁅d, e⁆ = (d * e * d⁻¹) * e⁻¹ := by
      rw [commutatorElement_def]
    rw [this]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ he)

private theorem odd_nsmul_eq' {n : ℕ} (hn : Odd n) (v : V) : n • v = v := by
  obtain ⟨m, rfl⟩ := hn
  have h : (2 * m) • v = 0 := by
    rw [mul_comm, mul_nsmul, two_nsmul, add_self_eq_zero']
  rw [add_nsmul, one_nsmul, h, zero_add]

private theorem eq_zero_of_fixed_of_odd {x : GLV V} {n : ℕ} (hn : Odd n) (hx : x ^ n = 1)
    {w : V} (hw : x (x w - w) = x w - w) : x w - w = 0 := by
  set v := x w - w with hv
  have hxw : x w = w + v := by rw [hv]; abel
  have key : ∀ k : ℕ, (x ^ k) w = w + k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, map_add, map_nsmul, hw, hxw, add_nsmul,
        one_nsmul]
      abel
  have h := key n
  rw [hx, odd_nsmul_eq' hn] at h
  have h' : w = w + v := h
  rw [left_eq_add] at h'
  exact h'

private theorem exists_apply_ne_of_sq_ne_one {t : GLV V} {m : ℕ} (ht : t ^ 2 ^ m = 1)
    (ht2 : t ^ 2 ≠ 1) : ∃ u : V, (t ^ 2) u = u ∧ t u ≠ u := by
  by_contra hcon
  push Not at hcon
  apply ht2
  let φ : GLV V →* Module.End (ZMod 2) V := LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hf : (φ t) ^ 2 ^ m = 1 := by rw [← map_pow, ht, map_one]
  have hnil : IsNilpotent (φ t - 1) :=
    Module.End.isNilpotent_sub_one_of_pow_expChar_pow_eq_one 2 m hf
  have hN : ∀ v, (φ t - 1) v = t v - v := fun v => by simp [φ]
  have hsq : ∀ v : V, ((φ t - 1 : Module.End (ZMod 2) V) ^ 2) v = (t ^ 2) v + v := by
    intro v
    rw [pow_two, Module.End.mul_apply, hN v, hN (t v - v), map_sub]
    rw [pow_two, LinearEquiv.mul_apply]
    calc t (t v) - t v - (t v - v) = t (t v) + v - (t v + t v) := by abel
      _ = t (t v) + v := by rw [add_self_eq_zero', sub_zero]
  have hker : LinearMap.ker ((φ t - 1) ^ 2) ≤ LinearMap.ker (φ t - 1) := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hsq] at hv
    have h1 : (t ^ 2) v = v := by
      have := neg_eq_of_add_eq_zero_left hv
      rw [neg_eq_self'] at this
      exact this.symm
    rw [hN, hcon v h1, sub_self]
  have hker' : LinearMap.ker ((φ t - 1) ^ 1) = LinearMap.ker ((φ t - 1) ^ (Nat.succ 1)) := by
    refine le_antisymm ?_ ?_
    · intro v hv
      rw [LinearMap.mem_ker, pow_one] at hv
      rw [LinearMap.mem_ker, Nat.succ_eq_add_one, pow_two, Module.End.mul_apply, hv, map_zero]
    · intro v hv
      rw [pow_one]
      exact hker hv
  obtain ⟨k, hk⟩ := hnil
  have hconst := Module.End.ker_pow_constant hker' k
  have hzero : (φ t - 1) ^ (1 + k) = 0 := by rw [pow_add, hk, mul_zero]
  rw [hzero, LinearMap.ker_zero, pow_one, LinearMap.ker_eq_top] at hconst
  have ht1 : t = 1 := by
    ext v
    have := LinearMap.congr_fun hconst v
    rw [hN] at this
    exact sub_eq_zero.1 (by simpa using this)
  rw [ht1, one_pow]

section Involutions

variable {K : Type*} [Group K]

private theorem invol_conj_a {a b : K} (ha : a * a = 1) (hb : b * b = 1) :
    (a * b)⁻¹ * a * (a * b) = a * (a * b) ^ 2 := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have haa : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hbb : ∀ x, b * (b * x) = x := fun x => by rw [← mul_assoc, hb, one_mul]
  simp only [pow_two, mul_inv_rev, ha', hb', mul_assoc, haa, hbb]

private theorem invol_conj_b {a b : K} (ha : a * a = 1) (hb : b * b = 1) :
    (a * b) * b * (a * b)⁻¹ = (a * b) ^ 2 * b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have haa : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hbb : ∀ x, b * (b * x) = x := fun x => by rw [← mul_assoc, hb, one_mul]
  simp only [pow_two, mul_inv_rev, ha', hb', mul_assoc, haa, hbb, hb, mul_one]

private theorem invol_sq_b {a b : K} (ha : a * a = 1) (hb : b * b = 1) :
    (a * b) ^ 2 * b = b * ((a * b) ^ 2)⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have haa : ∀ x, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  have hbb : ∀ x, b * (b * x) = x := fun x => by rw [← mul_assoc, hb, one_mul]
  simp only [pow_two, mul_inv_rev, ha', hb', mul_assoc, haa, hbb, hb, mul_one]

end Involutions

private theorem part1 {G D : Subgroup (GLV V)} (H : Lemma64Hyp G D) {z₁ z₂ h b : GLV V}
    (hz₁ : z₁ ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V))) (hz₁o : orderOf z₁ = 2)
    (hz₂ : z₂ ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V))) (hz₂o : orderOf z₂ = 2)
    (hh : h ∈ G) (hb : b = h⁻¹ * z₂ * h) (hp : IsPGroup 2 (Subgroup.closure {z₁, b})) :
    b ∈ Subgroup.normalizer (D : Set (GLV V)) ∨
      z₁ ∈ Subgroup.normalizer ((D.map (MulAut.conj h⁻¹).toMonoidHom : Subgroup (GLV V)) :
        Set (GLV V)) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hbN, haN⟩ := hcon
  have ha2 : z₁ * z₁ = 1 := by
    have := pow_orderOf_eq_one z₁
    rwa [hz₁o, pow_two] at this
  have hz₂2 : z₂ * z₂ = 1 := by
    have := pow_orderOf_eq_one z₂
    rwa [hz₂o, pow_two] at this
  have hb2 : b * b = 1 := by
    rw [hb]
    calc h⁻¹ * z₂ * h * (h⁻¹ * z₂ * h) = h⁻¹ * (z₂ * z₂) * h := by group
      _ = 1 := by rw [hz₂2]; group
  have hbG : b ∈ G := by
    rw [hb]
    exact G.mul_mem (G.mul_mem (G.inv_mem hh) hz₂.1) hh
  obtain ⟨t, ht⟩ : ∃ t : GLV V, t = z₁ * b := ⟨_, rfl⟩
  have htG : t ∈ G := by
    rw [ht]
    exact G.mul_mem hz₁.1 hbG
  have htmem : t ∈ Subgroup.closure ({z₁, b} : Set (GLV V)) := by
    rw [ht]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, t ^ 2 ^ m = 1 := by
    obtain ⟨m, hm⟩ := hp ⟨t, htmem⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have haNorm : z₁ ∈ Subgroup.normalizer (D : Set (GLV V)) :=
    Subgroup.centralizer_le_normalizer (D : Set (GLV V)) hz₁.2
  have hz₂Norm : z₂⁻¹ ∈ Subgroup.normalizer (D : Set (GLV V)) :=
    Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer (D : Set (GLV V)) hz₂.2)
  have ht2 : t ^ 2 ≠ 1 := by
    intro h2
    apply hbN
    have hcomm : b * z₁ = z₁ * b := by
      have h3 : z₁ * b * (z₁ * b) = 1 := by rw [← pow_two, ← ht]; exact h2
      have ha' : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right ha2
      have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
      have h4 : z₁ * b = (z₁ * b)⁻¹ := (inv_eq_of_mul_eq_one_right h3).symm
      rw [mul_inv_rev, ha', hb'] at h4
      exact h4.symm
    exact H.cent z₁ hz₁ hz₁o ⟨hbG, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩
  have htN : t ∉ Subgroup.normalizer (D : Set (GLV V)) := by
    intro htN
    apply hbN
    have : b = z₁⁻¹ * t := by rw [ht, inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haNorm) htN
  obtain ⟨u, hu2, hut⟩ := exists_apply_ne_of_sq_ne_one hm ht2
  have hid_a : t⁻¹ * z₁ * t = z₁ * t ^ 2 := by
    rw [ht]; exact invol_conj_a ha2 hb2
  have hid_b : t * b * t⁻¹ = t ^ 2 * b := by
    rw [ht]; exact invol_conj_b ha2 hb2
  have hid_sq : t ^ 2 * b = b * (t ^ 2)⁻¹ := by
    rw [ht]; exact invol_sq_b ha2 hb2
  by_cases hbu : b u = u
  ·
    have hau : z₁ u ≠ u := by
      intro hau
      apply hut
      have : t u = z₁ (b u) := by rw [ht]; rfl
      rw [this, hbu, hau]
    set v := z₁ u - u with hv
    have hv0 : v ≠ 0 := sub_ne_zero.2 hau
    have hv₁ : v ∈ commSpace (Subgroup.zpowers ((1 : GLV V)⁻¹ * z₁ * 1)) ⊤ := by
      simp only [inv_one, one_mul, mul_one]
      exact sub_mem_commSpace (Subgroup.mem_zpowers z₁) Submodule.mem_top
    have hv₂ : v ∈ commSpace (Subgroup.zpowers (t⁻¹ * z₁ * t)) ⊤ := by
      have : (t⁻¹ * z₁ * t) u - u = v := by
        rw [hid_a, hv, LinearEquiv.mul_apply, hu2]
      rw [← this]
      exact sub_mem_commSpace (Subgroup.mem_zpowers _) Submodule.mem_top
    have := H.key hz₁ hz₁o hz₁ hz₁o G.one_mem htG hv0 hv₁ hv₂
    rw [inv_one, mul_one] at this
    exact htN this
  ·
    have hbfix : (t ^ 2) (b u) = b u := by
      calc (t ^ 2) (b u) = (t ^ 2 * b) u := rfl
        _ = (b * (t ^ 2)⁻¹) u := by rw [hid_sq]
        _ = b (((t ^ 2)⁻¹) u) := rfl
        _ = b u := by
          congr 1
          rw [LinearEquiv.coe_inv]
          exact (LinearEquiv.symm_apply_eq _).2 hu2.symm
    set v := b u - u with hv
    have hv0 : v ≠ 0 := sub_ne_zero.2 hbu
    have hv₁ : v ∈ commSpace (Subgroup.zpowers (h⁻¹ * z₂ * h)) ⊤ := by
      rw [← hb]
      exact sub_mem_commSpace (Subgroup.mem_zpowers b) Submodule.mem_top
    have hv₂ : v ∈ commSpace (Subgroup.zpowers ((h * t⁻¹)⁻¹ * z₂ * (h * t⁻¹))) ⊤ := by
      have e1 : (h * t⁻¹)⁻¹ * z₂ * (h * t⁻¹) = t ^ 2 * b := by
        rw [← hid_b, hb]
        group
      have : (t ^ 2 * b) u - u = v := by
        rw [LinearEquiv.mul_apply, hbfix]
      rw [e1, ← this]
      exact sub_mem_commSpace (Subgroup.mem_zpowers _) Submodule.mem_top
    have hhtG : h * t⁻¹ ∈ G := G.mul_mem hh (G.inv_mem htG)
    have h1 := H.key hz₂ hz₂o hz₂ hz₂o hh hhtG hv0 hv₁ hv₂
    apply haN
    rw [mem_normalizer_conj_iff]
    have e2 : h * z₁ * h⁻¹ = (h * t⁻¹ * h⁻¹)⁻¹ * z₂⁻¹ := by
      have : z₁ = t * b⁻¹ := by rw [ht, mul_inv_cancel_right]
      rw [this, hb]
      group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h1) hz₂Norm

private theorem exists_moved {a x t₀ : GLV V} {n : ℕ} (hn : Odd n) (hxn : x ^ n = 1)
    (hx1 : x ≠ 1) (ht₀ : t₀ * t₀ = 1) (hax : a * x * a⁻¹ = x⁻¹)
    (hxt₀ : x * t₀ = t₀ * x) : ∃ u : V, t₀ u = u ∧ a u ≠ u := by
  let fx : V →ₗ[ZMod 2] V := (x : V →ₗ[ZMod 2] V) - LinearMap.id
  have hfx : ∀ w, fx w = x w - w := fun w => rfl
  have hxt : ∀ y, x (t₀ y) = t₀ (x y) := fun y => by
    calc x (t₀ y) = (x * t₀) y := rfl
      _ = (t₀ * x) y := by rw [hxt₀]
      _ = t₀ (x y) := rfl
  have hRt₀ : ∀ w ∈ LinearMap.range fx, t₀ w ∈ LinearMap.range fx := by
    rintro _ ⟨y, rfl⟩
    refine ⟨t₀ y, ?_⟩
    rw [hfx, hfx, map_sub, hxt]
  have hRne : LinearMap.range fx ≠ ⊥ := by
    intro h
    apply hx1
    rw [LinearMap.range_eq_bot] at h
    ext w
    have := LinearMap.congr_fun h w
    rw [hfx] at this
    exact sub_eq_zero.1 this
  obtain ⟨w, hwR, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRne
  have hex : ∃ u ∈ LinearMap.range fx, u ≠ 0 ∧ t₀ u = u := by
    by_cases ht : t₀ w = w
    · exact ⟨w, hwR, hw0, ht⟩
    · refine ⟨t₀ w - w, Submodule.sub_mem _ (hRt₀ w hwR) hwR, sub_ne_zero.2 ht, ?_⟩
      have h2 : t₀ (t₀ w) = w := by
        calc t₀ (t₀ w) = (t₀ * t₀) w := rfl
          _ = w := by rw [ht₀]; rfl
      rw [map_sub, h2]
      have := neg_eq_self' (t₀ w - w)
      rw [neg_sub] at this
      exact this
  obtain ⟨u, huR, hu0, hut⟩ := hex
  by_contra hcon
  push Not at hcon
  have hxu : t₀ (x u) = x u := by rw [← hxt, hut]
  have hau := hcon u hut
  have haxu := hcon (x u) hxu
  have hax' : a * x = x⁻¹ * a := by
    have := hax
    rwa [mul_inv_eq_iff_eq_mul] at this
  have h1 : x (x u) = u := by
    have e : a (x u) = x⁻¹ u := by
      calc a (x u) = (a * x) u := rfl
        _ = (x⁻¹ * a) u := by rw [hax']
        _ = x⁻¹ (a u) := rfl
        _ = x⁻¹ u := by rw [hau]
    rw [haxu] at e
    calc x (x u) = x (x⁻¹ u) := by rw [e]
      _ = u := by simp
  have hn' := hn
  obtain ⟨j, hj⟩ := hn'
  have hpow : ∀ i : ℕ, (x ^ (2 * i)) u = u := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, pow_succ, pow_succ, LinearEquiv.mul_apply,
        LinearEquiv.mul_apply, h1, ih]
  have hxu1 : x u = u := by
    have h2 : (x ^ n) u = u := by rw [hxn]; rfl
    rw [hj, pow_succ', LinearEquiv.mul_apply, hpow j] at h2
    exact h2
  obtain ⟨y, hy⟩ := huR
  have hy' : x y - y = u := hy
  have := eq_zero_of_fixed_of_odd hn hxn (w := y) (by rw [hy']; exact hxu1)
  exact hu0 (hy'.symm.trans this)

end Aux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private theorem orderOf_mul_eq_of_dihedral {K : Type*} [Group K] [Finite K] {a b : K}
    (ha : a * a = 1) (hb : b * b = 1) {k : ℕ} (hk : 0 < k)
    (φ : Subgroup.closure ({a, b} : Set K) ≃* DihedralGroup (2 * k)) :
    orderOf (a * b) = 2 * k := by
  have hcard : Nat.card (Subgroup.closure ({a, b} : Set K)) = 2 * (2 * k) :=
    (Nat.card_congr φ.toEquiv).trans DihedralGroup.nat_card
  have hle := CFSG.QuasithinUnique.Ch1.card_closure_involutions_le ha hb
  have hmem : a * b ∈ Subgroup.closure ({a, b} : Set K) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have hdvd : orderOf (a * b) ∣ 2 * k := by
    have h1 : orderOf (φ ⟨a * b, hmem⟩) = orderOf (a * b) := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    have h2 := Monoid.order_dvd_exponent (φ ⟨a * b, hmem⟩)
    rw [h1, DihedralGroup.exponent] at h2
    exact h2.trans (Nat.lcm_dvd dvd_rfl (dvd_mul_right 2 k))
  have := Nat.le_of_dvd (by omega) hdvd
  omega

private theorem part2 {G D : Subgroup (GLV V)} (H : Lemma64Hyp G D) {z₁ z₂ h b : GLV V}
    (hz₁ : z₁ ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V))) (hz₁o : orderOf z₁ = 2)
    (hz₂ : z₂ ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V))) (hz₂o : orderOf z₂ = 2)
    (hh : h ∈ G) (hb : b = h⁻¹ * z₂ * h) {k : ℕ} (hk : Odd k) (hk1 : 1 < k)
    (φ : Subgroup.closure ({z₁, b} : Set (GLV V)) ≃* DihedralGroup (2 * k)) :
    b ∈ Subgroup.centralizer (D : Set (GLV V)) := by
  have ha2 : z₁ * z₁ = 1 := by
    have := pow_orderOf_eq_one z₁
    rwa [hz₁o, pow_two] at this
  have hz₂2 : z₂ * z₂ = 1 := by
    have := pow_orderOf_eq_one z₂
    rwa [hz₂o, pow_two] at this
  have hb2 : b * b = 1 := by
    rw [hb]
    calc h⁻¹ * z₂ * h * (h⁻¹ * z₂ * h) = h⁻¹ * (z₂ * z₂) * h := by group
      _ = 1 := by rw [hz₂2]; group
  have haG : z₁ ∈ G := hz₁.1
  have hbG : b ∈ G := by
    rw [hb]
    exact G.mul_mem (G.mul_mem (G.inv_mem hh) hz₂.1) hh
  have hamem : z₁ ∈ Subgroup.closure ({z₁, b} : Set (GLV V)) := Subgroup.subset_closure (by simp)
  have hbmem : b ∈ Subgroup.closure ({z₁, b} : Set (GLV V)) := Subgroup.subset_closure (by simp)
  have hHG : Subgroup.closure ({z₁, b} : Set (GLV V)) ≤ G := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy
    · rw [hy]; exact haG
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hbG
  obtain ⟨r, hr⟩ : ∃ r : GLV V, r = z₁ * b := ⟨_, rfl⟩
  have hrk : orderOf r = 2 * k := by
    rw [hr]; exact orderOf_mul_eq_of_dihedral ha2 hb2 (by omega) φ
  have hr2k : r ^ (2 * k) = 1 := by rw [← hrk]; exact pow_orderOf_eq_one r
  have hrmem : r ∈ Subgroup.closure ({z₁, b} : Set (GLV V)) := by
    rw [hr]; exact Subgroup.mul_mem _ hamem hbmem
  have hrG : r ∈ G := hHG hrmem
  have hcj : ∀ j : ℕ, z₁ * r ^ j * z₁ = (r ^ j)⁻¹ := by
    intro j
    have := CFSG.QuasithinUnique.Ch1.involution_conj_zpow ha2 hb2 (j : ℤ)
    rw [← hr] at this
    simpa only [zpow_natCast, zpow_neg] using this
  have hbr : b = z₁ * r := by rw [hr, ← mul_assoc, ha2, one_mul]
  obtain ⟨x, hx⟩ : ∃ x : GLV V, x = r ^ 2 := ⟨_, rfl⟩
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : GLV V, t₀ = r ^ k := ⟨_, rfl⟩
  have hxk : x ^ k = 1 := by rw [hx, ← pow_mul]; exact hr2k
  have hx1 : x ≠ 1 := by
    intro h1
    rw [hx] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hrk] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  have ht₀2 : t₀ * t₀ = 1 := by rw [ht₀, ← pow_add, ← two_mul]; exact hr2k
  have ht₀1 : t₀ ≠ 1 := by
    intro h1
    rw [ht₀] at h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hrk] at h2
    have := Nat.le_of_dvd (by omega) h2
    omega
  have ht₀o : orderOf t₀ = 2 := orderOf_eq_prime (by rwa [pow_two]) ht₀1
  have hat₀ : z₁ * t₀ = t₀ * z₁ := by
    have h1 : z₁ * t₀ * z₁ = t₀ := by
      rw [ht₀, hcj k]
      exact inv_eq_of_mul_eq_one_right (by rw [← ht₀]; exact ht₀2)
    calc z₁ * t₀ = z₁ * t₀ * z₁ * z₁ := by rw [mul_assoc (z₁ * t₀) z₁ z₁, ha2, mul_one]
      _ = t₀ * z₁ := by rw [h1]
  have hax : z₁ * x * z₁⁻¹ = x⁻¹ := by
    have h1 : z₁ * x * z₁ = x⁻¹ := by rw [hx]; exact hcj 2
    rw [inv_eq_of_mul_eq_one_right ha2]
    exact h1
  have hxt₀ : x * t₀ = t₀ * x := by
    rw [hx, ht₀]; exact (Commute.pow_pow_self r 2 k).eq
  have hrt₀ : r * t₀ = t₀ * r := by
    rw [ht₀]; exact (Commute.self_pow r k).eq
  obtain ⟨u, hut, hau⟩ := exists_moved hk hxk hx1 ht₀2 hax hxt₀
  obtain ⟨i, hi⟩ := hk
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : GLV V, x₁ = r ^ (2 * i * (i + 1)) := ⟨_, rfl⟩
  have hx₁conj : x₁⁻¹ * b * x₁ = z₁ * t₀ := by
    have hcm : (r ^ (2 * i * (i + 1)))⁻¹ * z₁ = z₁ * r ^ (2 * i * (i + 1)) := by
      calc (r ^ (2 * i * (i + 1)))⁻¹ * z₁
          = (z₁ * r ^ (2 * i * (i + 1)) * z₁) * z₁ := by rw [hcj]
        _ = z₁ * r ^ (2 * i * (i + 1)) := by rw [mul_assoc, ha2, mul_one]
    have hexp : r ^ (2 * i * (i + 1) + 1 + 2 * i * (i + 1)) = t₀ := by
      have : 2 * i * (i + 1) + 1 + 2 * i * (i + 1) = k + 2 * k * i := by
        rw [hi]; ring
      rw [this, pow_add, pow_mul, hr2k, one_pow, mul_one, ht₀]
    calc x₁⁻¹ * b * x₁
        = (r ^ (2 * i * (i + 1)))⁻¹ * z₁ * r * r ^ (2 * i * (i + 1)) := by
          rw [hx₁, hbr]; simp only [mul_assoc]
      _ = z₁ * r ^ (2 * i * (i + 1)) * r * r ^ (2 * i * (i + 1)) := by rw [hcm]
      _ = z₁ * r ^ (2 * i * (i + 1) + 1 + 2 * i * (i + 1)) := by
          rw [pow_add, pow_succ]; simp only [mul_assoc]
      _ = z₁ * t₀ := by rw [hexp]
  have hx₁mem : x₁ ∈ Subgroup.closure ({z₁, b} : Set (GLV V)) := by
    rw [hx₁]; exact Subgroup.pow_mem _ hrmem _
  have hhx₁G : h * x₁ ∈ G := G.mul_mem hh (hHG hx₁mem)
  have he1 : (h * x₁)⁻¹ * z₂ * (h * x₁) = z₁ * t₀ := by
    rw [← hx₁conj, hb]; group
  set v := z₁ u - u with hv
  have hv0 : v ≠ 0 := sub_ne_zero.2 hau
  have hv₁ : v ∈ commSpace (Subgroup.zpowers ((1 : GLV V)⁻¹ * z₁ * 1)) ⊤ := by
    simp only [inv_one, one_mul, mul_one]
    exact sub_mem_commSpace (Subgroup.mem_zpowers z₁) Submodule.mem_top
  have hv₂ : v ∈ commSpace (Subgroup.zpowers ((h * x₁)⁻¹ * z₂ * (h * x₁))) ⊤ := by
    have : (z₁ * t₀) u - u = v := by rw [LinearEquiv.mul_apply, hut]
    rw [he1, ← this]
    exact sub_mem_commSpace (Subgroup.mem_zpowers _) Submodule.mem_top
  have hkey := H.key hz₁ hz₁o hz₂ hz₂o G.one_mem hhx₁G hv0 hv₁ hv₂
  rw [inv_one, mul_one] at hkey
  have hat₀C : z₁ * t₀ ∈ Subgroup.centralizer (D : Set (GLV V)) := by
    rw [← he1]; exact conj_mem_centralizer hkey hz₂.2
  have ht₀C : t₀ ∈ Subgroup.centralizer (D : Set (GLV V)) := by
    have : t₀ = z₁⁻¹ * (z₁ * t₀) := by rw [inv_mul_cancel_left]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hz₁.2) hat₀C
  have ht₀G : t₀ ∈ G := by rw [ht₀]; exact G.pow_mem hrG k
  have hbt₀ : b * t₀ = t₀ * b := by
    rw [hbr]
    calc z₁ * r * t₀ = z₁ * (r * t₀) := by rw [mul_assoc]
      _ = z₁ * (t₀ * r) := by rw [hrt₀]
      _ = (z₁ * t₀) * r := by rw [mul_assoc]
      _ = (t₀ * z₁) * r := by rw [hat₀]
      _ = t₀ * (z₁ * r) := by rw [mul_assoc]
  have hHcent : Subgroup.closure ({z₁, b} : Set (GLV V)) ≤
      Subgroup.centralizer ({t₀} : Set (GLV V)) := by
    rw [Subgroup.closure_le]
    intro y hy
    rcases hy with hy | hy
    · rw [hy]; exact Subgroup.mem_centralizer_singleton_iff.2 hat₀
    · rw [Set.mem_singleton_iff] at hy; rw [hy]
      exact Subgroup.mem_centralizer_singleton_iff.2 hbt₀
  have hx₁N : x₁ ∈ Subgroup.normalizer (D : Set (GLV V)) :=
    H.cent t₀ ⟨ht₀G, ht₀C⟩ ht₀o ⟨hHG hx₁mem, hHcent hx₁mem⟩
  have hhN : h ∈ Subgroup.normalizer (D : Set (GLV V)) := by
    have : h = (h * x₁) * x₁⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hkey (Subgroup.inv_mem _ hx₁N)
  rw [hb]
  exact conj_mem_centralizer hhN hz₂.2

theorem lemma64 {G D : Subgroup (GLV V)} (hDG : D ≤ G)
    (hcent : ∀ a ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V)), orderOf a = 2 →
      G ⊓ Subgroup.centralizer ({a} : Set (GLV V)) ≤ Subgroup.normalizer (D : Set (GLV V)))
    (hconj : ∀ g ∈ G, g ∉ Subgroup.normalizer (D : Set (GLV V)) →
      ¬ ⁅D, D.map (MulAut.conj g⁻¹).toMonoidHom⁆ ≤ D ⊓ D.map (MulAut.conj g⁻¹).toMonoidHom)
    (hfix : ∀ x ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V)), orderOf x = 2 →
      ∀ v ∈ commSpace (Subgroup.zpowers x) ⊤, ∀ d ∈ D, d v = v)
    (hnorm : ∀ x ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V)), orderOf x = 2 →
      ∀ v ∈ commSpace (Subgroup.zpowers x) ⊤, v ≠ 0 →
        ∀ g ∈ G, g v = v → g ∈ Subgroup.normalizer (D : Set (GLV V)))
    {z₁ z₂ h : GLV V} (hz₁ : z₁ ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V)))
    (hz₁o : orderOf z₁ = 2) (hz₂ : z₂ ∈ G ⊓ Subgroup.centralizer (D : Set (GLV V)))
    (hz₂o : orderOf z₂ = 2) (hh : h ∈ G) :
    (IsPGroup 2 (Subgroup.closure {z₁, h⁻¹ * z₂ * h}) →
      h⁻¹ * z₂ * h ∈ Subgroup.normalizer (D : Set (GLV V)) ∨
        z₁ ∈ Subgroup.normalizer ((D.map (MulAut.conj h⁻¹).toMonoidHom : Subgroup (GLV V)) :
          Set (GLV V))) ∧
    (∀ k : ℕ, Odd k → 1 < k →
      Nonempty (Subgroup.closure {z₁, h⁻¹ * z₂ * h} ≃* DihedralGroup (2 * k)) →
        h⁻¹ * z₂ * h ∈ Subgroup.centralizer (D : Set (GLV V))) := by
  have H : Lemma64Hyp G D := ⟨hDG, hcent, hconj, hfix, hnorm⟩
  exact ⟨fun hp => part1 H hz₁ hz₁o hz₂ hz₂o hh rfl hp,
    fun k hk hk1 ⟨φ⟩ => part2 H hz₁ hz₁o hz₂ hz₂o hh rfl hk hk1 φ⟩

end CFSG.CGT.Foote82
