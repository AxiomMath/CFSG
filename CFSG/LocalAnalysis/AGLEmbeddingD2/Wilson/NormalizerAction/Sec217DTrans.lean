module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217DAction
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.Sec217DMatrix

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup

section DTrans

variable {G : Type*} [Group G] {a c : G}

theorem acts_pow {g : G} {f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3} (h : Acts a c g f) (n : ℕ) :
    Acts a c (g ^ n) (f^[n]) := by
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    rw [pow_succ, Function.iterate_succ]
    intro x
    simp only [Function.comp]
    rw [ih, h]
    group

theorem kap_nsmul (hca : c * a = a * c) (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (x : ZMod 3 × ZMod 3) (n : ℕ) : kap a c (n • x) = kap a c x ^ n := by
  induction n with
  | zero => simp [kap_zero hca ha3 hc3]
  | succ n ih => rw [succ_nsmul, kap_add hca ha3 hc3, ih, pow_succ]

theorem kap_one_zero : kap a c (1, 0) = c := by
  have h10 : (1 : ZMod 3).val = 1 := rfl
  simp [kap, h10]

theorem kap_zero_one : kap a c (0, 1) = a := by
  have h10 : (1 : ZMod 3).val = 1 := rfl
  simp [kap, h10]

variable (hca : c * a = a * c) (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1) (ha1 : a ≠ 1) (hc1 : c ≠ 1)
  (hnot : c ∉ Subgroup.zpowers a)
include hca ha3 hc3 ha1 hc1 hnot

theorem acts_fixes_iff {g : G} {f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3} (hf : Acts a c g f)
    {z : G} {y : ZMod 3 × ZMod 3} (hy : kap a c y = z) :
    f y = y ↔ g * z = z * g := by
  constructor
  · intro h
    have := hf y
    rw [h, hy] at this
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [← this]
  · intro h
    apply kap_inj hca ha3 hc3 ha1 hc1 hnot
    rw [hf, hy]
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [← h]
      _ = z := by group

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem transvection_on_D {u v x t : G} {k : ℕ} (hk : Odd k)
    (huN : u ∈ Subgroup.normalizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G))
    (hu : c * u = u * c) (hua : u ∉ Subgroup.centralizer ({a} : Set G)) (hu8 : u ^ 8 = 1)
    (hvN : v ∈ Subgroup.normalizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G))
    (hv : a * v = v * a) (hvc : v ∉ Subgroup.centralizer ({c} : Set G)) (hv8 : v ^ 8 = 1)
    (hx : ∀ δ ∈ zpowers a ⊔ zpowers c, x * δ = δ * x)
    (ht : t = u * (x * v ^ k)⁻¹)
    (hQc : ∀ n : ℕ, (n = 1 ∨ n = 2) → t ^ n * c * (t ^ n)⁻¹ ∈ zpowers c →
      ∀ δ ∈ zpowers a ⊔ zpowers c, t ^ n * δ = δ * t ^ n)
    (hQa : ∀ n : ℕ, (n = 1 ∨ n = 2) → t ^ n * a * (t ^ n)⁻¹ ∈ zpowers a →
      ∀ δ ∈ zpowers a ⊔ zpowers c, t ^ n * δ = δ * t ^ n) :
    t ∈ Subgroup.normalizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G) ∧
      ∃ d ∈ zpowers a ⊔ zpowers c, d ≠ 1 ∧ t * d * t⁻¹ = d ∧
        (∃ δ ∈ zpowers a ⊔ zpowers c, t * δ * t⁻¹ = δ * d) ∧
        ∀ δ ∈ zpowers a ⊔ zpowers c, ∃ n : ℕ, t * δ * t⁻¹ = δ * d ^ n := by
  have hxN : x ∈ Subgroup.normalizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro δ
    have key : ∀ y, y ∈ zpowers a ⊔ zpowers c → x * y * x⁻¹ = y := fun y hy => by
      rw [hx y hy]; group
    constructor
    · intro h; rw [key δ h]; exact h
    · intro h
      have := key δ
      by_contra hδ
      exact hδ (by
        have h2 : ∀ y, y ∈ zpowers a ⊔ zpowers c → x * y * x⁻¹ = y := key
        have hx' : x⁻¹ * (x * δ * x⁻¹) * x = δ := by group
        have hxi : ∀ y ∈ zpowers a ⊔ zpowers c, x⁻¹ * y * x = y := fun y hy => by
          have := hx y hy
          calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
            _ = x⁻¹ * (x * y) := by rw [this]
            _ = y := by group
        rw [← hx', hxi _ h]
        exact h)
  have hvkN : v ^ k ∈ Subgroup.normalizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G) :=
    Subgroup.pow_mem _ hvN k
  have hwN := Subgroup.mul_mem _ hxN hvkN
  have htN : t ∈ Subgroup.normalizer ((zpowers a ⊔ zpowers c : Subgroup G) : Set G) := by
    rw [ht]; exact Subgroup.mul_mem _ huN (Subgroup.inv_mem _ hwN)
  refine ⟨htN, ?_⟩
  obtain ⟨fu, hfu⟩ := acts_exists hca ha3 hc3 huN
  obtain ⟨fv, hfv⟩ := acts_exists hca ha3 hc3 hvN
  obtain ⟨ft, hft⟩ := acts_exists hca ha3 hc3 htN
  have hfx : Acts a c x id := by
    intro y
    have hy : kap a c y ∈ zpowers a ⊔ zpowers c := (mem_D_iff hca ha3 hc3).2 ⟨y, rfl⟩
    have := hx _ hy
    simp only [id]
    calc kap a c y = (kap a c y * x) * x⁻¹ := by group
      _ = x * kap a c y * x⁻¹ := by rw [← this]
  have hfw : Acts a c (x * v ^ k) (id ∘ fv^[k]) := acts_mul hca ha3 hc3 ha1 hc1 hnot hfx (acts_pow hfv k)
  have htw : t * (x * v ^ k) = u := by rw [ht]; group
  have hftw : Acts a c u (ft ∘ (id ∘ fv^[k])) := htw ▸ acts_mul hca ha3 hc3 ha1 hc1 hnot hft hfw
  have hfuw : ft ∘ (id ∘ fv^[k]) = fu := acts_unique hca ha3 hc3 ha1 hc1 hnot hftw hfu
  have hadd_u := acts_add hca ha3 hc3 ha1 hc1 hnot hfu
  have hadd_v := acts_add hca ha3 hc3 ha1 hc1 hnot hfv
  have hadd_t := acts_add hca ha3 hc3 ha1 hc1 hnot hft
  set U := matOf fu with hU
  set V := matOf fv with hV
  have hfuU : ∀ y, fu y = ap U y := eq_ap_matOf hadd_u
  have hfvV : ∀ y, fv y = ap V y := eq_ap_matOf hadd_v
  have hftT : ∀ y, ft y = ap (matOf ft) y := eq_ap_matOf hadd_t
  have hfuU' : fu = ap U := funext hfuU
  have hfvV' : fv = ap V := funext hfvV
  have hu_c : fu (1, 0) = (1, 0) :=
    (acts_fixes_iff hca ha3 hc3 ha1 hc1 hnot hfu (kap_one_zero)).2 hu.symm
  have hu_a : fu (0, 1) ≠ (0, 1) := fun h => hua (by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((acts_fixes_iff hca ha3 hc3 ha1 hc1 hnot hfu (kap_zero_one)).1 h))
  have hv_a : fv (0, 1) = (0, 1) :=
    (acts_fixes_iff hca ha3 hc3 ha1 hc1 hnot hfv (kap_zero_one)).2 hv.symm
  have hv_c : fv (1, 0) ≠ (1, 0) := fun h => hvc (by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((acts_fixes_iff hca ha3 hc3 ha1 hc1 hnot hfv (kap_one_zero)).1 h))
  have hit : ∀ {g : G} {f : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3}, Acts a c g f → g ^ 8 = 1 →
      ∀ y, f^[8] y = y := by
    intro g f hg h8 y
    have h1 := acts_pow hg 8
    rw [h8] at h1
    have h2 := acts_unique hca ha3 hc3 ha1 hc1 hnot h1 (acts_one hca ha3 hc3 ha1 hc1 hnot)
    exact congrFun h2 y
  have hu8' : ∀ y, (ap U)^[8] y = y := by rw [← hfuU']; exact hit hfu hu8
  have hv8' : ∀ y, (ap V)^[8] y = y := by rw [← hfvV']; exact hit hfv hv8
  rw [hfuU'] at hu_c hu_a
  rw [hfvV'] at hv_a hv_c
  have hVinv := involution_check V hv_a hv_c hv8'
  have hfvk : fv^[k] = fv := by
    funext y
    rw [hfvV']
    exact iterate_ap_two V hVinv k hk y
  have hft_uv : ∀ y, ft y = ap (mm U V) y := by
    intro y
    have h1 : ft (fv (fv y)) = fu (fv y) := by
      have := congrFun hfuw (fv y)
      simpa [hfvk] using this
    rw [ap_mm, ← hfuU' , ← hfvV']
    calc ft y = ft (fv (fv y)) := by rw [hfvV', hVinv]
      _ = fu (fv y) := h1
  have key : ∀ n : ℕ, (n = 1 ∨ n = 2) → ∀ M : M2, (∀ y, ap M y = ft^[n] y) →
      ((ap M (1, 0)).2 = 0 → M = m1) ∧ ((ap M (0, 1)).1 = 0 → M = m1) := by
    intro n hn M hM
    have hMf : ap M = ft^[n] := funext hM
    have hA : Acts a c (t ^ n) (ap M) := by rw [hMf]; exact acts_pow hft n
    have hid : ap M = id → M = m1 := fun h => ap_inj (fun y => by
      rw [ap_m1]; exact congrFun h y)
    constructor
    · intro h0
      have h1 := hA (1, 0)
      rw [kap_one_zero] at h1
      have hmem : t ^ n * c * (t ^ n)⁻¹ ∈ zpowers c :=
        h1 ▸ (kap_mem_zpowers_c_iff hca ha3 hc3 ha1 hc1 hnot _).2 h0
      exact hid ((acts_id_iff hca ha3 hc3 ha1 hc1 hnot hA).2 (hQc n hn hmem))
    · intro h0
      have h1 := hA (0, 1)
      rw [kap_zero_one] at h1
      have hmem : t ^ n * a * (t ^ n)⁻¹ ∈ zpowers a :=
        h1 ▸ (kap_mem_zpowers_a_iff hca ha3 hc3 ha1 hc1 hnot _).2 h0
      exact hid ((acts_id_iff hca ha3 hc3 ha1 hc1 hnot hA).2 (hQa n hn hmem))
  obtain ⟨hk1c, hk1a⟩ := key 1 (Or.inl rfl) (mm U V) (fun y => by
    rw [← hft_uv]; rfl)
  obtain ⟨hk2c, hk2a⟩ := key 2 (Or.inr rfl) (mm (mm U V) (mm U V)) (fun y => by
    rw [ap_mm, ← hft_uv, ← hft_uv]; rfl)
  obtain ⟨d, hd0, hdfix, ⟨v0, hv0⟩, hall⟩ := core_check U V hu_c hu_a hu8' hv_a hv_c hv8'
    hk1c hk1a hk2c hk2a
  have hkd : ∀ w, t * kap a c w * t⁻¹ = kap a c (ap (mm U V) w) := fun w => by
    rw [← hft_uv, hft]
  refine ⟨kap a c d, (mem_D_iff hca ha3 hc3).2 ⟨d, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hd0
    exact kap_inj hca ha3 hc3 ha1 hc1 hnot (h.trans (kap_zero hca ha3 hc3).symm)
  · rw [hkd, hdfix]
  · refine ⟨kap a c v0, (mem_D_iff hca ha3 hc3).2 ⟨v0, rfl⟩, ?_⟩
    rw [hkd, hv0, kap_add hca ha3 hc3]
  · intro δ hδ
    obtain ⟨w, rfl⟩ := (mem_D_iff hca ha3 hc3).1 hδ
    obtain ⟨κ, hκ⟩ := hall w
    refine ⟨κ.val, ?_⟩
    have hsm : ((κ * d.1, κ * d.2) : ZMod 3 × ZMod 3) = κ.val • d := by
      ext <;> simp [nsmul_eq_mul, ZMod.natCast_zmod_val]
    rw [hkd, hκ, hsm, kap_add hca ha3 hc3, kap_nsmul hca ha3 hc3]

end DTrans

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
