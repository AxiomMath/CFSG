module

public import CFSG.GH74.Generic.BProg.B3.S3Rk4Core
public import CFSG.GH74.Generic.BProg.B3.S3Rk2Final

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup

variable {G : Type} [Group G] [Finite G]

theorem false_of_ctx_s3_rank1 {x a : G} {K A D J : Subgroup G} (h306 : Prop306aBarAt x K A)
    (hc : Ctx21 G x K A a D J) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hC : pRank 2 ↥(CxK x K) ≤ 1) : False := by
  classical
  obtain ⟨E, hEK, hAE, -, hEel, hE4, -⟩ := S3Rk1Basic.exists_E hc.circ hc.src h3
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := S3Rk1Basic.pcomp_of_circ hc.circ
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hx2' : orderOf x = 2 := S3Rk1Basic.orderOf_x_of_circ hc.circ
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2', pow_two] at this
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hsqE : ∀ e ∈ E, e * e = 1 := fun e he => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) e he
    rwa [sq] at this
  have hEc : ∀ a ∈ E, ∀ c ∈ E, a * c = c * a := S3Rk1Four.comm_of_isElementaryAbelian hEel
  obtain ⟨y, hyE, hy1⟩ : ∃ y ∈ E, y ≠ 1 := by
    have hEne : E ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hE4
      omega
    obtain ⟨y', hy'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hEne
    exact ⟨y', y'.2, fun e => hy' (Subtype.ext e)⟩
  have hyy : y * y = 1 := hsqE y hyE
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hyy) hy1
  have hyK : y ∈ K := hEK hyE
  have hset : Setup30 G x K A y :=
    ⟨hc.hyp, hc.circ, h3, hc.src, hC, Subgroup.mem_inf.2 ⟨hEA hyE, hyK⟩, hy2⟩
  obtain ⟨T, hT, -⟩ := Setup30.exists_T hset
  obtain ⟨⟨n, hn, hnx⟩, -⟩ := prop301T hset hT
  have hny : n * y = y * n := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hn).2
  have hny' : n * y * n⁻¹ = y := by rw [hny]; group
  have hxCxK : x ∈ CxK x K := S3Rk3B.x_mem_CxK (cfg_of_setup30 hset hT)
  have h316 := lemma316 h306 hc hset hT hn hnx
  obtain ⟨e, heE, he⟩ : ∃ e ∈ E, n * e * n⁻¹ ∉ K ⊔ CxK x K := by
    by_contra hcon
    push Not at hcon
    apply h316
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨e, heE, hde⟩ := S3Rk1Basic.decomp_A hKC hEK hAE hx2' hd
    show n * d * n⁻¹ ∈ K ⊔ CxK x K
    rcases hde with hde | hde
    · rw [hde]
      exact hcon e heE
    · rw [hde]
      have : n * (e * x) * n⁻¹ = (n * e * n⁻¹) * (x * y) := by rw [← hnx]; group
      rw [this]
      exact (K ⊔ CxK x K).mul_mem (hcon e heE)
        ((K ⊔ CxK x K).mul_mem (Subgroup.mem_sup_right hxCxK) (Subgroup.mem_sup_left hyK))
  have he1 : e ≠ 1 := fun e1 => he (by rw [e1]; simp)
  obtain ⟨σ, hσ, hσy⟩ := S3Rk1Four.exists_cyc h3 hEK hEel hE4 hyE heE hy1 he1
  have hσK : σ ∈ K := (Subgroup.mem_inf.1 hσ).1
  have hσE : σ ∈ normalizer (E : Set G) := (Subgroup.mem_inf.1 hσ).2
  have hσx : σ * x = x * σ := Subgroup.mem_centralizer_singleton_iff.1 (hKC hσK)
  have hzE : σ⁻¹ * y * σ ∈ E := by
    have := (Subgroup.mem_normalizer_iff.1 ((normalizer (E : Set G)).inv_mem hσE) y).1 hyE
    simpa using this
  set z : G := σ⁻¹ * y * σ with hz
  have hxz : x * z = z * x := (Subgroup.mem_centralizer_singleton_iff.1 (hKC (hEK hzE))).symm
  have hyz : y * z = z * y := hEc y hyE z hzE
  have hzz : z * z = 1 := hsqE z hzE
  have hxy : x * y = y * x := (Subgroup.mem_centralizer_singleton_iff.1 (hKC hyK)).symm
  have hee : e * e = 1 := hsqE e heE
  have hxe : x * e = e * x := (Subgroup.mem_centralizer_singleton_iff.1 (hKC (hEK heE))).symm
  have hye : y * e = e * y := hEc y hyE e heE
  have h1 : n * (x * y) * n⁻¹ = x := by
    calc n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by group
      _ = (x * y) * y := by rw [hnx, hny']
      _ = x := by rw [mul_assoc, hyy, mul_one]
  have hy'2 : (n * e * n⁻¹) * (n * e * n⁻¹) = 1 := by
    calc (n * e * n⁻¹) * (n * e * n⁻¹) = n * (e * e) * n⁻¹ := by group
      _ = 1 := by rw [hee]; group
  have hxye : (x * y) * e = e * (x * y) := by
    calc (x * y) * e = x * (y * e) := mul_assoc _ _ _
      _ = x * (e * y) := by rw [hye]
      _ = (x * e) * y := (mul_assoc _ _ _).symm
      _ = (e * x) * y := by rw [hxe]
      _ = e * (x * y) := mul_assoc _ _ _
  have hxy' : x * (n * e * n⁻¹) = (n * e * n⁻¹) * x := by
    calc x * (n * e * n⁻¹) = (n * (x * y) * n⁻¹) * (n * e * n⁻¹) := by rw [h1]
      _ = n * ((x * y) * e) * n⁻¹ := by group
      _ = n * (e * (x * y)) * n⁻¹ := by rw [hxye]
      _ = (n * e * n⁻¹) * (n * (x * y) * n⁻¹) := by group
      _ = (n * e * n⁻¹) * x := by rw [h1]
  have hx'x : (x * z) * x = x * (x * z) := by
    calc (x * z) * x = x * (z * x) := mul_assoc _ _ _
      _ = x * (x * z) := by rw [hxz]
  have hx'y : (x * z) * y = y * (x * z) := by
    calc (x * z) * y = x * (z * y) := mul_assoc _ _ _
      _ = x * (y * z) := by rw [hyz]
      _ = (x * y) * z := (mul_assoc _ _ _).symm
      _ = (y * x) * z := by rw [hxy]
      _ = y * (x * z) := mul_assoc _ _ _
  have hx'2 : (x * z) * (x * z) = 1 := by
    calc (x * z) * (x * z) = x * (z * x) * z := by group
      _ = x * (x * z) * z := by rw [← hxz]
      _ = (x * x) * (z * z) := by group
      _ = 1 := by rw [hxx, hzz, one_mul]
  have hσzσ : σ * z * σ⁻¹ = y := by rw [hz]; group
  have hσxσ : σ * x * σ⁻¹ = x := by rw [hσx]; group
  have hw1 : (n * σ) * (x * z) * (n * σ)⁻¹ = x := by
    calc (n * σ) * (x * z) * (n * σ)⁻¹ = n * ((σ * x * σ⁻¹) * (σ * z * σ⁻¹)) * n⁻¹ := by group
      _ = n * (x * y) * n⁻¹ := by
        rw [hσzσ, hσxσ]
      _ = x := h1
  have hw2 : (n * σ) * y * (n * σ)⁻¹ = n * e * n⁻¹ := by
    calc (n * σ) * y * (n * σ)⁻¹ = n * (σ * y * σ⁻¹) * n⁻¹ := by group
      _ = n * e * n⁻¹ := by rw [hσy]
  have hw3 : (n * σ) * x * (n * σ)⁻¹ = x * y := by
    calc (n * σ) * x * (n * σ)⁻¹ = n * (σ * x * σ⁻¹) * n⁻¹ := by group
      _ = n * x * n⁻¹ := by rw [hσxσ]
      _ = x * y := hnx
  exact S3Rk4Core.core hset hT (h306 y hset) hy'2 hxy' hx'x hx'y hx'2 hw1 hw2 hw3 he

end CFSG.GH74.Generic.BProg.B3
