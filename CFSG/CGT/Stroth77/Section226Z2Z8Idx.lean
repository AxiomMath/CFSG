module

public import CFSG.CGT.Stroth77.Section226Z2Z8IdxFin
public import CFSG.CGT.Stroth77.StrothFrameNE

public section

namespace CFSG.CGT.Stroth77

open Sec226ZIdx

variable {G : Type} [Group G]

namespace Sec226ZIdx

variable {B : Subgroup G} {τ : StrothTypeIndex} (dB : StrothWeakTypeData B τ)

theorem exists_ofTorus_eq {d : G} (hd : d ∈ B) : ∃ v, dB.ofTorus v = d :=
  ⟨_, dB.ofTorus_e ⟨d, hd⟩⟩

theorem e_a : dB.e (Additive.ofMul dB.a) = gen τ.k 1 := by
  simp [StrothWeakTypeData.a]

theorem e_b : dB.e (Additive.ofMul dB.b) = gen τ.k 2 := by
  simp [StrothWeakTypeData.b]

theorem conj_pow_eq (g y : G) (n : ℕ) : (g⁻¹ * y * g) ^ n = g⁻¹ * y ^ n * g := by
  have h := conj_pow (a := g⁻¹) (b := y) (i := n)
  rwa [inv_inv] at h

theorem conj_ofTorus_lin (hF : IdxFacts τ) {g : G} (hg : g ∈ Subgroup.normalizer (B : Set G))
    (hc : g⁻¹ * (dB.c : G) * g = dB.c) (v : Torus τ.k) :
    g⁻¹ * dB.ofTorus v * g = dB.ofTorus (lin τ (dB.e (Additive.ofMul (conjBy hg dB.a)))
      (dB.e (Additive.ofMul (conjBy hg dB.b))) v) := by
  have hφ : ∀ y : G, MulAut.conj g⁻¹ y = g⁻¹ * y * g := fun y => by
    rw [MulAut.conj_apply, inv_inv]
  have ha : dB.ofTorus (dB.e (Additive.ofMul (conjBy hg dB.a))) = g⁻¹ * (dB.a : G) * g := by
    rw [dB.ofTorus_e]; rfl
  have hb : dB.ofTorus (dB.e (Additive.ofMul (conjBy hg dB.b))) = g⁻¹ * (dB.b : G) * g := by
    rw [dB.ofTorus_e]; rfl
  conv_lhs => rw [← hF.decomp v]
  rw [← hφ]
  simp only [lin, StrothWeakTypeData.ofTorus_add, StrothWeakTypeData.ofTorus_nsmul, map_mul,
    map_pow]
  rw [ha, hb, ← dB.c_eq, ← dB.a_eq, ← dB.b_eq, hφ, hφ, hφ, hc]

theorem conj_ofTorus_five (hF : IdxFacts τ) {g : G} (hg : g ∈ Subgroup.normalizer (B : Set G))
    (hc : g⁻¹ * (dB.c : G) * g = dB.c) (ha : g⁻¹ * (dB.a : G) * g = (dB.a : G) ^ 5)
    (hb : g⁻¹ * (dB.b : G) * g = (dB.b : G) ^ 5) (v : Torus τ.k) :
    g⁻¹ * dB.ofTorus v * g = dB.ofTorus (five τ v) := by
  have ha' : conjBy hg dB.a = dB.a ^ 5 := Subtype.ext ha
  have hb' : conjBy hg dB.b = dB.b ^ 5 := Subtype.ext hb
  rw [conj_ofTorus_lin dB hF hg hc, ha', hb', ofMul_pow, ofMul_pow, map_nsmul, map_nsmul, e_a, e_b]
  rfl

theorem conj_eq_on_omegaTwo (hF : IdxFacts τ) {g₁ g₂ : G}
    (h₀ : g₁⁻¹ * dB.ofTorus (gen τ.k 0) * g₁ = g₂⁻¹ * dB.ofTorus (gen τ.k 0) * g₂)
    (h₁ : g₁⁻¹ * dB.ofTorus (2 • gen τ.k 1) * g₁ = g₂⁻¹ * dB.ofTorus (2 • gen τ.k 1) * g₂)
    (h₂ : g₁⁻¹ * dB.ofTorus (2 • gen τ.k 2) * g₁ = g₂⁻¹ * dB.ofTorus (2 • gen τ.k 2) * g₂)
    {v : Torus τ.k} (hv : 4 • v = (0 : Torus τ.k)) :
    g₁⁻¹ * dB.ofTorus v * g₁ = g₂⁻¹ * dB.ofTorus v * g₂ := by
  have hφ : ∀ g y : G, g⁻¹ * y * g = MulAut.conj g⁻¹ y := fun g y => by
    rw [MulAut.conj_apply, inv_inv]
  rw [← hF.om2decomp v hv]
  simp only [hφ, StrothWeakTypeData.ofTorus_add, StrothWeakTypeData.ofTorus_nsmul, map_mul,
    map_pow] at h₀ h₁ h₂ ⊢
  rw [h₀, h₁, h₂]

theorem exists_conj_inv_ofTorus {g : G} (hg : g ∈ Subgroup.normalizer (B : Set G))
    {v : Torus τ.k} (hv : 4 • v = (0 : Torus τ.k)) :
    ∃ u : Torus τ.k, dB.ofTorus u = g * dB.ofTorus v * g⁻¹ ∧ 4 • u = (0 : Torus τ.k) := by
  obtain ⟨u, hu⟩ := exists_ofTorus_eq dB
    ((Subgroup.mem_normalizer_iff.mp hg (dB.ofTorus v)).mp (dB.ofTorus_mem v))
  refine ⟨u, hu, dB.ofTorus_injective ?_⟩
  rw [StrothWeakTypeData.ofTorus_nsmul, StrothWeakTypeData.ofTorus_zero, hu, conj_pow,
    ← StrothWeakTypeData.ofTorus_nsmul, hv, StrothWeakTypeData.ofTorus_zero, mul_one,
    mul_inv_cancel]

theorem conj_inv_mul_eq_of_omegaTwo {g g' : G} (hg : g ∈ Subgroup.normalizer (B : Set G))
    (hgg' : ∀ u : Torus τ.k, 4 • u = (0 : Torus τ.k) →
      g'⁻¹ * dB.ofTorus u * g' = g⁻¹ * dB.ofTorus u * g)
    {v : Torus τ.k} (hv : 4 • v = (0 : Torus τ.k)) :
    (g⁻¹ * g')⁻¹ * dB.ofTorus v * (g⁻¹ * g') = dB.ofTorus v := by
  obtain ⟨u, hu, h4u⟩ := exists_conj_inv_ofTorus dB hg hv
  calc (g⁻¹ * g')⁻¹ * dB.ofTorus v * (g⁻¹ * g') = g'⁻¹ * (g * dB.ofTorus v * g⁻¹) * g' := by
        group
    _ = g⁻¹ * (g * dB.ofTorus v * g⁻¹) * g := by rw [← hu, hgg' u h4u]
    _ = dB.ofTorus v := by group

end Sec226ZIdx

private theorem torus_t100_one_four_nsmul :
    ∀ y : Torus (StrothTypeIndex.t100 1).k, 4 • y = (0 : Torus (StrothTypeIndex.t100 1).k) := by
  decide +kernel

namespace StrothFrame.IsD

private theorem conj_eq_of_commute {x g : G} (h : g * x = x * g) : x⁻¹ * g * x = g := by
  rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]

private theorem mem_centralizer_of_conj {B : Subgroup G} {x : G}
    (hx : ∀ d ∈ B, x⁻¹ * d * x = d) : x ∈ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have := hx d hd
  calc d * x = x * (x⁻¹ * d * x) := by group
    _ = x * d := by rw [this]

variable [Finite G] {F : StrothFrame G} {D : Subgroup G} {τ : StrothTypeIndex}
  {dD : StrothWeakTypeData D τ}

private theorem pow_four_of_mem_A (F : StrothFrame G) {d : G} (hd : d ∈ F.A) : d ^ 4 = 1 := by
  obtain ⟨y, rfl⟩ := exists_ofTorus_eq F.dA hd
  rw [← StrothWeakTypeData.ofTorus_nsmul, torus_t100_one_four_nsmul,
    StrothWeakTypeData.ofTorus_zero]

private theorem exists_coords_of_mem_A (h : F.IsD D dD) {d : G} (hd : d ∈ F.A) :
    ∃ v : Torus τ.k, dD.ofTorus v = d ∧ 4 • v = (0 : Torus τ.k) := by
  obtain ⟨v, rfl⟩ := exists_ofTorus_eq dD (h.A_le hd)
  refine ⟨v, rfl, dD.ofTorus_injective ?_⟩
  rw [StrothWeakTypeData.ofTorus_nsmul, StrothWeakTypeData.ofTorus_zero, pow_four_of_mem_A F hd]

section Cases

variable (hF : IdxFacts τ)
  (hCA : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((F.A : Subgroup G) : Set G),
    (∀ d ∈ D, x⁻¹ * d * x = d) ∨
    (x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) * x = (dD.a : G) ^ 5 ∧
      x⁻¹ * (dD.b : G) * x = (dD.b : G) ^ 5))

include hF hCA in
private theorem conj_cond (h : F.IsD D dD) {x l : G} (hxS : x ∈ (F.S : Subgroup G))
    (hxN : x ∈ Subgroup.normalizer (D : Set G)) {pa pb : Torus τ.k}
    (hconj : ∀ v, x⁻¹ * dD.ofTorus v * x = dD.ofTorus (lin τ pa pb v))
    (hlS : l ∈ (F.S : Subgroup G)) (hlN : l ∈ Subgroup.normalizer (D : Set G))
    {φ : Torus τ.k →+ Torus τ.k} (hφ : ∀ v, l⁻¹ * dD.ofTorus v * l = dD.ofTorus (φ v))
    (h₀ : φ (lin τ pa pb (φ (gen τ.k 0))) = lin τ pa pb (gen τ.k 0))
    (h₁ : φ (lin τ pa pb (φ (2 • gen τ.k 1))) = lin τ pa pb (2 • gen τ.k 1))
    (h₂ : φ (lin τ pa pb (φ (2 • gen τ.k 2))) = lin τ pa pb (2 • gen τ.k 2)) :
    (∀ i, φ (lin τ pa pb (φ (gen τ.k i))) = lin τ pa pb (gen τ.k i)) ∨
      ∀ i, φ (lin τ pa pb (φ (gen τ.k i))) = five τ (lin τ pa pb (gen τ.k i)) := by
  set z := l * x * l with hzdef
  set y := x⁻¹ * z with hydef
  have hz : ∀ v, z⁻¹ * dD.ofTorus v * z = dD.ofTorus (φ (lin τ pa pb (φ v))) := fun v => by
    calc z⁻¹ * dD.ofTorus v * z = l⁻¹ * (x⁻¹ * (l⁻¹ * dD.ofTorus v * l) * x) * l := by
          rw [hzdef]; group
      _ = dD.ofTorus (φ (lin τ pa pb (φ v))) := by rw [hφ, hconj, hφ]
  have hxy : x * y = z := by rw [hydef]; group
  have hyN : y ∈ Subgroup.normalizer (D : Set G) :=
    mul_mem (inv_mem hxN) (mul_mem (mul_mem hlN hxN) hlN)
  have hyS : y ∈ (F.S : Subgroup G) := mul_mem (inv_mem hxS) (mul_mem (mul_mem hlS hxS) hlS)
  have hg : ∀ w, φ (lin τ pa pb (φ w)) = lin τ pa pb w →
      z⁻¹ * dD.ofTorus w * z = x⁻¹ * dD.ofTorus w * x := fun w hw => by rw [hz, hconj, hw]
  have hzx : ∀ u : Torus τ.k, 4 • u = (0 : Torus τ.k) →
      z⁻¹ * dD.ofTorus u * z = x⁻¹ * dD.ofTorus u * x := fun u hu =>
    conj_eq_on_omegaTwo dD hF (hg _ h₀) (hg _ h₁) (hg _ h₂) hu
  have hyA : y ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G) := by
    refine mem_centralizer_of_conj fun d hd => ?_
    obtain ⟨v, rfl, hv⟩ := exists_coords_of_mem_A h hd
    exact conj_inv_mul_eq_of_omegaTwo dD hxN hzx hv
  have hyz : ∀ w, z⁻¹ * w * z = y⁻¹ * (x⁻¹ * w * x) * y := fun w => by rw [← hxy]; group
  rcases hCA y ⟨⟨hyS, hyN⟩, hyA⟩ with hy | ⟨hyc, hya, hyb⟩
  · left
    intro i
    apply dD.ofTorus_injective
    rw [← hz, hyz, hconj, hy _ (dD.ofTorus_mem _)]
  · right
    intro i
    apply dD.ofTorus_injective
    rw [← hz, hyz, hconj, conj_ofTorus_five dD hF hyN hyc hya hyb]

include hF hCA in
private theorem sq_cond (h : F.IsD D dD) {x : G} (hxS : x ∈ (F.S : Subgroup G))
    (hxN : x ∈ Subgroup.normalizer (D : Set G)) {pa pb : Torus τ.k}
    (hconj : ∀ v, x⁻¹ * dD.ofTorus v * x = dD.ofTorus (lin τ pa pb v))
    (h₀ : lin τ pa pb (lin τ pa pb (gen τ.k 0)) = gen τ.k 0)
    (h₁ : lin τ pa pb (lin τ pa pb (2 • gen τ.k 1)) = 2 • gen τ.k 1)
    (h₂ : lin τ pa pb (lin τ pa pb (2 • gen τ.k 2)) = 2 • gen τ.k 2) :
    (∀ i, lin τ pa pb (lin τ pa pb (gen τ.k i)) = gen τ.k i) ∨
      ∀ i, lin τ pa pb (lin τ pa pb (gen τ.k i)) = five τ (gen τ.k i) := by
  have hsq : ∀ v, (x * x)⁻¹ * dD.ofTorus v * (x * x) =
      dD.ofTorus (lin τ pa pb (lin τ pa pb v)) := fun v => by
    calc (x * x)⁻¹ * dD.ofTorus v * (x * x) = x⁻¹ * (x⁻¹ * dD.ofTorus v * x) * x := by group
      _ = dD.ofTorus (lin τ pa pb (lin τ pa pb v)) := by rw [hconj, hconj]
  have hA : x * x ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G) := by
    refine mem_centralizer_of_conj fun d hd => ?_
    obtain ⟨v, rfl, hv⟩ := exists_coords_of_mem_A h hd
    have hg : ∀ w, lin τ pa pb (lin τ pa pb w) = w →
        (x * x)⁻¹ * dD.ofTorus w * (x * x) = 1⁻¹ * dD.ofTorus w * 1 := fun w hw => by
      rw [hsq, hw, inv_one, one_mul, mul_one]
    have h1 := conj_eq_on_omegaTwo dD hF (hg _ h₀) (hg _ h₁) (hg _ h₂) hv
    rwa [inv_one, one_mul, mul_one] at h1
  rcases hCA (x * x) ⟨⟨mul_mem hxS hxS, mul_mem hxN hxN⟩, hA⟩ with hy | ⟨hyc, hya, hyb⟩
  · left
    intro i
    apply dD.ofTorus_injective
    rw [← hsq, hy _ (dD.ofTorus_mem _)]
  · right
    intro i
    apply dD.ofTorus_injective
    rw [← hsq, conj_ofTorus_five dD hF (mul_mem hxN hxN) hyc hya hyb]

include hF hCA in
private theorem exists_coords (h : F.IsD D dD) {x : G}
    (hx : x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) :
    ∃ pa pb : Torus τ.k, x⁻¹ * (dD.c : G) * x = dD.c ∧
      (∀ v, x⁻¹ * dD.ofTorus v * x = dD.ofTorus (lin τ pa pb v)) ∧
      4 • pa = 4 • gen τ.k 1 ∧ 4 • pb = 4 • gen τ.k 2 ∧
      ((2 • pa = 2 • gen τ.k 1 ∧ 2 • pb = 2 • gen τ.k 2) ∨
        (2 • pa = -(2 • gen τ.k 1 : Torus τ.k) ∧ 2 • pb = -(2 • gen τ.k 2 : Torus τ.k))) := by
  obtain ⟨⟨hxS, hxN⟩, hxC⟩ := hx
  obtain ⟨hc2, ha8, hb8⟩ := hF.order
  have hfix : ∀ z ∈ omegaIn 1 D, x⁻¹ * z * x = z := fun z hz =>
    conj_eq_of_commute (Subgroup.mem_centralizer_iff.mp hxC z hz)
  have hcΩ : (dD.c : G) ∈ omegaIn 1 D := by
    refine mem_omegaIn_one_of_mul_self dD.c.2 ?_
    rw [dD.c_eq, ← StrothWeakTypeData.ofTorus_add, ← two_nsmul, hc2,
      StrothWeakTypeData.ofTorus_zero]
  have ha4 : (dD.a : G) ^ 4 ∈ omegaIn 1 D := by
    refine mem_omegaIn_one_of_mul_self (pow_mem dD.a.2 4) ?_
    rw [← pow_add, dD.a_eq, ← StrothWeakTypeData.ofTorus_nsmul, show 4 + 4 = 8 from rfl, ha8,
      StrothWeakTypeData.ofTorus_zero]
  have hb4 : (dD.b : G) ^ 4 ∈ omegaIn 1 D := by
    refine mem_omegaIn_one_of_mul_self (pow_mem dD.b.2 4) ?_
    rw [← pow_add, dD.b_eq, ← StrothWeakTypeData.ofTorus_nsmul, show 4 + 4 = 8 from rfl, hb8,
      StrothWeakTypeData.ofTorus_zero]
  have hc := hfix _ hcΩ
  set pa := dD.e (Additive.ofMul (conjBy hxN dD.a)) with hpa
  set pb := dD.e (Additive.ofMul (conjBy hxN dD.b)) with hpb
  have hconj : ∀ v, x⁻¹ * dD.ofTorus v * x = dD.ofTorus (lin τ pa pb v) :=
    conj_ofTorus_lin dD hF hxN hc
  have hpa' : dD.ofTorus pa = x⁻¹ * (dD.a : G) * x := by rw [hpa, dD.ofTorus_e]; rfl
  have hpb' : dD.ofTorus pb = x⁻¹ * (dD.b : G) * x := by rw [hpb, dD.ofTorus_e]; rfl
  have h4a : 4 • pa = 4 • gen τ.k 1 := by
    apply dD.ofTorus_injective
    rw [StrothWeakTypeData.ofTorus_nsmul, StrothWeakTypeData.ofTorus_nsmul, hpa', conj_pow_eq,
      hfix _ ha4, dD.a_eq]
  have h4b : 4 • pb = 4 • gen τ.k 2 := by
    apply dD.ofTorus_injective
    rw [StrothWeakTypeData.ofTorus_nsmul, StrothWeakTypeData.ofTorus_nsmul, hpb', conj_pow_eq,
      hfix _ hb4, dD.b_eq]
  obtain ⟨⟨a₀uv, a₀t, a₀sq⟩, ⟨a₁uv, a₁t, a₁sq⟩, ⟨a₂uv, a₂t, a₂sq⟩⟩ := hF.aux pa pb h4a h4b
  have huvS : dD.uv ∈ (F.S : Subgroup G) := h.uv_eq ▸ F.uv_mem_S
  have htS : dD.t ∈ (F.S : Subgroup G) := h.t_eq ▸ F.t_mem_S
  have huv := conj_cond hF hCA h hxS hxN hconj huvS dD.uv_mem
    (dD.conj_ofTorus dD.uv_mem dD.uv_conj) a₀uv a₁uv a₂uv
  have ht := conj_cond hF hCA h hxS hxN hconj htS dD.t_mem
    (dD.conj_ofTorus dD.t_mem dD.t_conj) a₀t a₁t a₂t
  have hsq := sq_cond hF hCA h hxS hxN hconj a₀sq a₁sq a₂sq
  exact ⟨pa, pb, hc, hconj, h4a, h4b, hF.main pa pb h4a h4b huv ht hsq⟩

include hF hCA in
private theorem exists_coords_inv (h : F.IsD D dD) {x : G}
    (hx : x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (hxA : x ∉ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    ∃ pa pb : Torus τ.k, x⁻¹ * (dD.c : G) * x = dD.c ∧
      (∀ v, x⁻¹ * dD.ofTorus v * x = dD.ofTorus (lin τ pa pb v)) ∧
      4 • pa = 4 • gen τ.k 1 ∧ 4 • pb = 4 • gen τ.k 2 ∧
      2 • pa = -(2 • gen τ.k 1 : Torus τ.k) ∧ 2 • pb = -(2 • gen τ.k 2 : Torus τ.k) := by
  obtain ⟨pa, pb, hc, hconj, h4a, h4b, ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩⟩ := exists_coords hF hCA h hx
  · refine absurd (mem_centralizer_of_conj fun d hd => ?_) hxA
    obtain ⟨v, rfl, hv⟩ := exists_coords_of_mem_A h hd
    rw [hconj, hF.triv pa pb h2a h2b v hv]
  · exact ⟨pa, pb, hc, hconj, h4a, h4b, h2a, h2b⟩

end Cases

theorem conj_omegaTwo_of_t2m1 (h : F.IsD D dD) (hτ : τ = .t200 1 ∨ τ = .t201 1)
    (hCA : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((F.A : Subgroup G) : Set G),
      (∀ d ∈ D, x⁻¹ * d * x = d) ∨
      (x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) * x = (dD.a : G) ^ 5 ∧
        x⁻¹ * (dD.b : G) * x = (dD.b : G) ^ 5))
    {x : G} (hx : x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (hxA : x ∉ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) ^ 2 * x = ((dD.a : G) ^ 2)⁻¹ ∧
      x⁻¹ * (dD.b : G) ^ 2 * x = ((dD.b : G) ^ 2)⁻¹ := by
  have hF := idxFacts_of hτ
  obtain ⟨pa, pb, hc, hconj, -, -, h2a, h2b⟩ := exists_coords_inv hF hCA h hx hxA
  obtain ⟨-, -, -, hla, hlb⟩ := hF.linf pa pb
  have ha2 : (dD.a : G) ^ 2 = dD.ofTorus (2 • gen τ.k 1) := by
    rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.a_eq]
  have hb2 : (dD.b : G) ^ 2 = dD.ofTorus (2 • gen τ.k 2) := by
    rw [StrothWeakTypeData.ofTorus_nsmul, ← dD.b_eq]
  refine ⟨hc, ?_, ?_⟩
  · rw [ha2, hconj, hla, h2a, StrothWeakTypeData.ofTorus_neg]
  · rw [hb2, hconj, hlb, h2b, StrothWeakTypeData.ofTorus_neg]

theorem inf_centralizer_le_omegaIn_of_t2m1 (h : F.IsD D dD) (hτ : τ = .t200 1 ∨ τ = .t201 1)
    (hCA : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((F.A : Subgroup G) : Set G),
      (∀ d ∈ D, x⁻¹ * d * x = d) ∨
      (x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) * x = (dD.a : G) ^ 5 ∧
        x⁻¹ * (dD.b : G) * x = (dD.b : G) ^ 5))
    {x : G} (hx : x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G))
    (hxA : x ∉ Subgroup.centralizer ((F.A : Subgroup G) : Set G)) :
    D ⊓ Subgroup.centralizer ({x} : Set G) ≤ omegaIn 1 D := by
  have hF := idxFacts_of hτ
  obtain ⟨pa, pb, -, hconj, -, -, h2a, h2b⟩ := exists_coords_inv hF hCA h hx hxA
  rintro d ⟨hdD, hdx⟩
  obtain ⟨v, rfl⟩ := exists_ofTorus_eq dD hdD
  have hfix : lin τ pa pb v = v := by
    apply dD.ofTorus_injective
    rw [← hconj, conj_eq_of_commute (Subgroup.mem_centralizer_singleton_iff.mp hdx)]
  refine mem_omegaIn_one_of_mul_self hdD ?_
  rw [← StrothWeakTypeData.ofTorus_add, ← two_nsmul,
    (hF.cent pa pb h2a h2b v).resolve_right (not_not_intro hfix), StrothWeakTypeData.ofTorus_zero]

theorem relIndex_centralizer_A_le_two_of_t2m1 (h : F.IsD D dD)
    (hτ : τ = .t200 1 ∨ τ = .t201 1)
    (hCA : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((F.A : Subgroup G) : Set G),
      (∀ d ∈ D, x⁻¹ * d * x = d) ∨
      (x⁻¹ * (dD.c : G) * x = dD.c ∧ x⁻¹ * (dD.a : G) * x = (dD.a : G) ^ 5 ∧
        x⁻¹ * (dD.b : G) * x = (dD.b : G) ^ 5)) :
    ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((F.A : Subgroup G) : Set G)).relIndex
      ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) ≤ 2 := by
  have hF := idxFacts_of hτ
  refine Nat.le_of_dvd two_pos (Subgroup.relIndex_dvd_two_iff'.mpr ?_)
  by_cases hall : ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      y ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)
  · exact ⟨1, one_mem _, fun b hb => Or.inr ⟨hb.1, hall b hb⟩⟩
  push Not at hall
  obtain ⟨x₀, hx₀, hx₀A⟩ := hall
  obtain ⟨pa, pb, -, hconj₀, -, -, h2a, h2b⟩ := exists_coords_inv hF hCA h hx₀ hx₀A
  refine ⟨x₀⁻¹, inv_mem hx₀, fun y hy => ?_⟩
  by_cases hyA : y ∈ Subgroup.centralizer ((F.A : Subgroup G) : Set G)
  · exact Or.inr ⟨hy.1, hyA⟩
  left
  obtain ⟨qa, qb, -, hconj, -, -, h2qa, h2qb⟩ := exists_coords_inv hF hCA h hy hyA
  have hx₀N : x₀ ∈ Subgroup.normalizer (D : Set G) := hx₀.1.2
  have hmem : x₀⁻¹ * y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) :=
    mul_mem (inv_mem hx₀.1) hy.1
  refine ⟨hmem, mem_centralizer_of_conj fun d hd => ?_⟩
  obtain ⟨v, rfl, hv⟩ := exists_coords_of_mem_A h hd
  refine conj_inv_mul_eq_of_omegaTwo dD hx₀N (fun u hu => ?_) hv
  rw [hconj, hconj₀, hF.inv qa qb h2qa h2qb u hu, hF.inv pa pb h2a h2b u hu]

end StrothFrame.IsD

end CFSG.CGT.Stroth77
