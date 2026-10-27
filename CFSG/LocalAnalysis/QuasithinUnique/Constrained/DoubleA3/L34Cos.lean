module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34T
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L34G2

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped MatrixGroups

section Generic

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_coset_involution (hL : L27Aut Y) (hcard : Nat.card Y = 168)
    (hcent : ∀ a : Y, a ≠ 1 → a * a = 1 → IsPGroup 2 ↥(Subgroup.centralizer ({a} : Set Y)))
    {P : Subgroup Y} (hP8 : Nat.card P = 8) (hnab : ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a)
    (α : MulAut Y) (hα : ¬ IsInner α) (hαP : ∀ y ∈ P, α y ∈ P) :
    ∃ r ∈ P, (α * MulAut.conj r⁻¹) * (α * MulAut.conj r⁻¹) = 1 ∧
      ¬ IsInner (α * MulAut.conj r⁻¹) := by
  obtain ⟨t, ht, ht2, htP⟩ := hL.exists_outer_inv P hP8
  obtain ⟨k₀, hk₀⟩ := hL.out_mul t α ht hα
  have hk₀P : k₀ ∈ P := by
    have : k₀ ∈ normalizer (P : Set Y) := by
      apply mem_normalizer_of_conj_mem
      intro a ha
      rw [← hk₀]
      exact htP _ (hαP a ha)
    exact normalizer_le_of_eight hcard hcent hP8 hnab this
  have htα : t * α = MulAut.conj k₀ := by
    ext y
    rw [hk₀]
    simp
  have hα' : α = t * MulAut.conj k₀ := by
    calc α = (t * t) * α := by rw [ht2, one_mul]
      _ = t * (t * α) := by rw [mul_assoc]
      _ = t * MulAut.conj k₀ := by rw [htα]
  have hres : α * MulAut.conj k₀⁻¹ = t := by
    rw [hα', mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  refine ⟨k₀, hk₀P, ?_, ?_⟩
  · rw [hres]; exact ht2
  · rw [hres]; exact ht

end Generic

section GenericG

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem nonab_pair_of_conj {Y R V : Subgroup G} {x : G} (hVY : V ≤ Y) (hVR : V ≤ R)
    (hxY : x ∈ normalizer (Y : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hnab : ¬ conjR V x ≤ Subgroup.centralizer (V : Set G)) :
    ∃ a ∈ (R ⊓ Y).subgroupOf Y, ∃ b ∈ (R ⊓ Y).subgroupOf Y, a * b ≠ b * a := by
  have hxRinv : ∀ y ∈ R, x⁻¹ * y * x ∈ R := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (R : Set G)).inv_mem hxR) y).mp hy
    simpa using this
  by_contra hcon
  push Not at hcon
  apply hnab
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hyx : x * y * x⁻¹ ∈ V := mem_conjR.mp hy
  have e : x⁻¹ * (x * y * x⁻¹) * x = y := by group
  have hyY : y ∈ Y := by
    have h1 := (Subgroup.mem_normalizer_iff.mp ((normalizer (Y : Set G)).inv_mem hxY)
      (x * y * x⁻¹)).mp (hVY hyx)
    have h2 : x⁻¹ * (x * y * x⁻¹) * x ∈ Y := by simpa using h1
    rwa [e] at h2
  have hyR : y ∈ R := by
    have h2 := hxRinv _ (hVR hyx)
    rwa [e] at h2
  have h1 := hcon ⟨u, hVY hu⟩ (Subgroup.mem_subgroupOf.mpr ⟨hVR hu, hVY hu⟩)
    ⟨y, hyY⟩ (Subgroup.mem_subgroupOf.mpr ⟨hyR, hyY⟩)
  exact congrArg Subtype.val h1

theorem exists_involution_coset {Y R : Subgroup G} {x : G} (hL : L27Aut ↥Y) (hd : L2pData ↥Y)
    (hcard : Nat.card Y = 168) (hRK8 : Nat.card ↥(R ⊓ Y) = 8)
    (hnab : ∃ a ∈ (R ⊓ Y).subgroupOf Y, ∃ b ∈ (R ⊓ Y).subgroupOf Y, a * b ≠ b * a)
    (hxY : x ∈ normalizer (Y : Set G)) (hxR : x ∈ normalizer (R : Set G))
    (hout : ¬ ∃ k ∈ Y, ∀ y ∈ Y, x⁻¹ * y * x = k⁻¹ * y * k) :
    ∃ r ∈ R ⊓ Y, ∃ t : MulAut ↥Y, ¬ IsInner t ∧ t * t = 1 ∧
      ∀ y : ↥Y, ((t y : ↥Y) : G) = (r * x)⁻¹ * (y : G) * (r * x) := by
  have hcent : ∀ a : ↥Y, a ≠ 1 → a * a = 1 →
      IsPGroup 2 ↥(Subgroup.centralizer ({a} : Set ↥Y)) := fun a ha1 ha2 =>
    hd.cent_two a (orderOf_eq_prime (by rwa [← pow_two] at ha2) ha1)
  obtain ⟨α, hα⟩ := exists_conjAut hxY
  have hP8 : Nat.card ((R ⊓ Y).subgroupOf Y) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ⊓ Y ≤ Y)).toEquiv]
    exact hRK8
  have hxRinv : ∀ y ∈ R, x⁻¹ * y * x ∈ R := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp ((normalizer (R : Set G)).inv_mem hxR) y).mp hy
    simpa using this
  have hαout : ¬ IsInner α := by
    rintro ⟨k, hk⟩
    apply hout
    refine ⟨((k⁻¹ : ↥Y) : G), (k⁻¹ : ↥Y).2, fun y hy => ?_⟩
    have h1 := congrArg Subtype.val (hk ⟨y, hy⟩)
    rw [hα] at h1
    simpa using h1
  have hαP : ∀ y ∈ (R ⊓ Y).subgroupOf Y, α y ∈ (R ⊓ Y).subgroupOf Y := by
    intro y hy
    have hy' : (y : G) ∈ R ⊓ Y := Subgroup.mem_subgroupOf.mp hy
    rw [Subgroup.mem_subgroupOf, hα]
    exact ⟨hxRinv _ hy'.1, by have := (α y).2; rwa [hα] at this⟩
  obtain ⟨r, hrP, hr2, hrout⟩ := exists_coset_involution hL hcard hcent hP8 hnab α hαout hαP
  refine ⟨(r : G), Subgroup.mem_subgroupOf.mp hrP, α * MulAut.conj r⁻¹, hrout, hr2, fun y => ?_⟩
  show ((α (MulAut.conj r⁻¹ y) : ↥Y) : G) = ((r : G) * x)⁻¹ * (y : G) * ((r : G) * x)
  rw [hα]
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_inv_rev]
  group

end GenericG

section Main

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

section X'

variable (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hI : Inputs2436)
  (hK : A3A3K T M H S L s x z₁ z₂ K) (hc : blockU2 L s ≤ Subgroup.centralizer (K : Set G))

section NoF

include hD h27_1 hI hK hc

theorem A3A3K.mul_self_eq_one_of_sq_inner {u : G}
    (hK1 : ∀ y ∈ K, u⁻¹ * (u⁻¹ * y * u) * u = y)
    (hK2 : ∀ y ∈ conjR K s, u⁻¹ * (u⁻¹ * y * u) * u = y) : u * u = 1 := by
  have hcomm : ∀ y : G, u⁻¹ * (u⁻¹ * y * u) * u = y → y * (u * u) = (u * u) * y := fun y h => by
    calc y * (u * u) = (u * u) * (u⁻¹ * (u⁻¹ * y * u) * u) := by group
      _ = (u * u) * y := by rw [h]
  have hcN : u * u ∈ Subgroup.centralizer ((K ⊔ conjR K s : Subgroup G) : Set G) := by
    have hle : (K ⊔ conjR K s : Subgroup G) ≤ centralizerElem (u * u) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y (hK1 y hy))
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y (hK2 y hy))
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hn)
  rw [hK.centralizer_sup_eq_bot hD h27_1 hI hc, Subgroup.mem_bot] at hcN
  exact hcN

omit hD h27_1 hI hc in
theorem A3A3K.blockU2_le_Ks : blockU2 L s ≤ conjR K s := hK.isA4s.le.trans hK.Ls_le_Ks

omit hD h27_1 hI hc in
theorem A3A3K.blockU2_le_baum : blockU2 L s ≤ baum S := by
  have hsB : s ∈ normalizer (baum S : Set G) := mem_normalizer_baum hK.s_mem
  have h1 : blockU2 L s ≤ conjR (baum S) s := Lin2.conjR_mono (blockU_le_baum hK.cs hK.a3) s
  rwa [mem_normalizer_iff_conjR_eq.mp hsB] at h1

end NoF

include hD h27_1 hI hK hc

theorem A3A3K.exists_rho
    : ∃ ρ ∈ baum S, (ρ * x) * (ρ * x) = 1 := by
  have hcs := hK.cs
  have hB := basic31 hD h27_1 hK.toA3A3
  have hxN : x ∈ normalizer (baum S : Set G) := hK.toA3A3x.x_mem_normalizer_baum hB
  have hUK : blockU L ≤ K := hK.isA4.le.trans hK.L_le_K
  have hUB : blockU L ≤ baum S := blockU_le_baum hcs hK.a3
  have hxK := hK.x_mem_normalizer_K
  have hxK' := hK.x_mem_normalizer_Ks hD h27_1 hI hc
  obtain ⟨r, hr, t, ht, ht2, htr⟩ := exists_involution_coset (Y := K) (R := baum S) (x := x)
    (hK.l27Aut_K hD h27_1 hI hc) (hK.l2pData_K hD h27_1 hI hc) (hK.card_K_eq hD h27_1 hI hc)
    (hK.card_rK hD h27_1 hI hc) (nonab_pair_of_conj hUK hUB hxK hxN hK.x_good) hxK hxN
    (hK.x_not_inner hD h27_1 hI hc)
  obtain ⟨r', hr', t', ht', ht2', htr'⟩ := exists_involution_coset (Y := conjR K s) (R := baum S)
    (x := x) (hK.l27Aut_Ks hD h27_1 hI hc) (hK.l2pData_Ks hD h27_1 hI hc)
    (hK.card_Ks_eq hD h27_1 hI hc) (hK.card_rKs hD h27_1 hI hc)
    (nonab_pair_of_conj hK.blockU2_le_Ks hK.blockU2_le_baum hxK' hxN
      hK.x_good₂) hxK' hxN (hK.x_not_inner_Ks hD h27_1 hI hc)
  have htt : ∀ y : ↥K, t (t y) = y := fun y => by
    have := congrArg (fun f : MulAut ↥K => f y) ht2
    simpa using this
  have htt' : ∀ y : ↥(conjR K s), t' (t' y) = y := fun y => by
    have := congrArg (fun f : MulAut ↥(conjR K s) => f y) ht2'
    simpa using this
  have hcomm : ∀ a ∈ K, ∀ b ∈ conjR K s, a * b = b * a := hK.comm_K_Ks hD h27_1 hI hc
  have key : ∀ (z : G) (hz : z ∈ K), (r * r' * x)⁻¹ * z * (r * r' * x) = ((t ⟨z, hz⟩ : ↥K) : G) := by
    intro z hz
    rw [htr]
    have h1 : (r⁻¹ * z * r) * r' = r' * (r⁻¹ * z * r) :=
      hcomm _ (K.mul_mem (K.mul_mem (K.inv_mem hr.2) hz) hr.2) r' hr'.2
    calc (r * r' * x)⁻¹ * z * (r * r' * x) = x⁻¹ * r'⁻¹ * (r⁻¹ * z * r) * r' * x := by group
      _ = x⁻¹ * (r' ⁻¹ * ((r⁻¹ * z * r) * r')) * x := by group
      _ = x⁻¹ * (r' ⁻¹ * (r' * (r⁻¹ * z * r))) * x := by rw [h1]
      _ = (r * x)⁻¹ * z * (r * x) := by group
  have key' : ∀ (z : G) (hz : z ∈ conjR K s),
      (r * r' * x)⁻¹ * z * (r * r' * x) = ((t' ⟨z, hz⟩ : ↥(conjR K s)) : G) := by
    intro z hz
    rw [htr']
    have h0 : r * z = z * r := hcomm r hr.2 z hz
    have h1 : r⁻¹ * z * r = z := by
      calc r⁻¹ * z * r = r⁻¹ * (z * r) := by group
        _ = r⁻¹ * (r * z) := by rw [h0]
        _ = z := by group
    calc (r * r' * x)⁻¹ * z * (r * r' * x) = x⁻¹ * r'⁻¹ * (r⁻¹ * z * r) * r' * x := by group
      _ = x⁻¹ * r'⁻¹ * z * r' * x := by rw [h1]
      _ = (r' * x)⁻¹ * z * (r' * x) := by group
  refine ⟨r * r', (baum S).mul_mem hr.1 hr'.1, ?_⟩
  apply hK.mul_self_eq_one_of_sq_inner hD h27_1 hI hc
  · intro y hy
    have h1 := key y hy
    have hty : ((t ⟨y, hy⟩ : ↥K) : G) ∈ K := (t ⟨y, hy⟩).2
    have h2 := key _ hty
    have e : (⟨((t ⟨y, hy⟩ : ↥K) : G), hty⟩ : ↥K) = t ⟨y, hy⟩ := rfl
    rw [e, htt] at h2
    rw [h1]
    simpa using h2
  · intro y hy
    have h1 := key' y hy
    have hty : ((t' ⟨y, hy⟩ : ↥(conjR K s)) : G) ∈ conjR K s := (t' ⟨y, hy⟩).2
    have h2 := key' _ hty
    have e : (⟨((t' ⟨y, hy⟩ : ↥(conjR K s)) : G), hty⟩ : ↥(conjR K s)) = t' ⟨y, hy⟩ := rfl
    rw [e, htt'] at h2
    rw [h1]
    simpa using h2

end X'

end Main

end CFSG.QuasithinUnique.DoubleA3
