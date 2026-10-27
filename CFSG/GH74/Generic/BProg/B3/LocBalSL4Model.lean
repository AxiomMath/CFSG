module

public import CFSG.GH74.Generic.BProg.B3.LocBalSL4Ivk
public import CFSG.GH74.Generic.BProg.B2.GenConjSU4Proved
public import CFSG.GH74.GLS.Stage2.Final.ClassicalF

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.L5U5 CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.ModelBlock CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank Subgroup

namespace LocBalSL4Model

variable {F : Type} [Field F]

structure BigModel [Finite F] (M : ModelData F) (q : ℕ) (ε : ℤ) : Prop where
  good : GoodModel M
  one : ∀ t : ↥M.K4, t * t = 1 → t ≠ 1 → t ∉ Subgroup.center ↥M.K4 → ∃ k : ↥M.K4, k * t * k⁻¹ = M.yK
  center : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔ g = 1 ∨ g = M.xK
  centerless : ∀ k : PG M, (∀ g : PG M, g * k = k * g) → k = 1
  lnEps : IsLnEps 4 (PG M) ε q
  odd : Odd q
  gt3 : 3 < q
  eps : ε = 1 ∨ ε = -1
  mod8 : ¬ ((q : ℤ) ≡ ε [ZMOD 8])
  qshape : CFSG.GH74.Generic.BProg.QShape1 ↥M.K4
  e8 : ∀ E : Subgroup ↥M.K4, CFSG.IsElementaryAbelian 2 ↥E → Nat.card ↥E = 8 → M.xK ∈ E

section Facts

variable [Finite F] {M : ModelData F}

omit [Finite F] in
theorem mkP_eq_one_iff (hM : ∀ g : ↥M.K4, g ∈ Subgroup.center ↥M.K4 ↔ g = 1 ∨ g = M.xK)
    (g : ↥M.K4) : mkP M g = 1 ↔ g ∈ Subgroup.center ↥M.K4 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact Zs_le_center M h
  · intro h
    rcases (hM g).1 h with rfl | rfl
    · exact Subgroup.one_mem _
    · exact xK_mem_Zs M

theorem involutionOddCore_eq_pPrimeCoreOf {G : Type*} [Group G] (a : G) :
    involutionOddCore a = pPrimeCoreOf 2 (Subgroup.centralizer ({a} : Set G)) := by
  unfold involutionOddCore pPrimeCoreOf
  rw [oddCore_eq_pPrimeCore]

theorem pPrimeCoreOf_comm_centralizer (hG : GoodModel M)
    (hone : ∀ t : ↥M.K4, t * t = 1 → t ≠ 1 → t ∉ Subgroup.center ↥M.K4 →
      ∃ k : ↥M.K4, k * t * k⁻¹ = M.yK)
    {t : ↥M.K4} (ht2 : t * t = 1) (ht1 : t ≠ 1) (htc : t ∉ Subgroup.center ↥M.K4)
    {γ : PG M} (hγ : γ ∈ pPrimeCoreOf 2 (Subgroup.centralizer ({mkP M t} : Set (PG M))))
    {w : PG M} (hw : w ∈ (Subgroup.centralizer ({t} : Set ↥M.K4)).map (mkP M)) :
    γ * w = w * γ := by
  obtain ⟨k, hk⟩ := hone t ht2 ht1 htc
  set κ : PG M := mkP M k with hκ
  have hκt : (MulAut.conj κ) (mkP M t) = yP M := by
    rw [MulAut.conj_apply, hκ, ← map_inv, ← map_mul, ← map_mul, hk]
  have hγ' : (MulAut.conj κ) γ ∈ pPrimeCoreOf 2 (Cg M) := by
    have h1 : γ ∈ involutionOddCore (mkP M t) := by
      rw [involutionOddCore_eq_pPrimeCoreOf]
      exact hγ
    have h2 := Subgroup.mem_map_of_mem (MulAut.conj κ).toMonoidHom h1
    rw [involutionOddCore_map (MulAut.conj κ) (mkP M t), MulEquiv.coe_toMonoidHom, hκt] at h2
    rw [involutionOddCore_eq_pPrimeCoreOf] at h2
    exact h2
  have hγBS := pPrimeCoreOf_le_BS hG hγ'
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  have hw' : (MulAut.conj κ) (mkP M w₀) ∈ C0 M := by
    refine ⟨k * w₀ * k⁻¹, ?_, ?_⟩
    · have hw₀' : w₀ * t = t * w₀ := Subgroup.mem_centralizer_singleton_iff.mp hw₀
      change k * w₀ * k⁻¹ ∈ Dsub M
      rw [mem_Dsub, ← hk]
      calc k * w₀ * k⁻¹ * (k * t * k⁻¹) = k * (w₀ * t) * k⁻¹ := by group
        _ = k * (t * w₀) * k⁻¹ := by rw [hw₀']
        _ = k * t * k⁻¹ * (k * w₀ * k⁻¹) := by group
    · rw [MulAut.conj_apply, hκ]
      simp only [map_mul, map_inv]
  have hc := Ivk413.bs_comm_C0 hG hγBS hw'
  apply (MulAut.conj κ).injective
  rw [map_mul, map_mul]
  exact hc

theorem isCentralInvolution_mkP (hG : GoodModel M)
    (hone : ∀ t : ↥M.K4, t * t = 1 → t ≠ 1 → t ∉ Subgroup.center ↥M.K4 →
      ∃ k : ↥M.K4, k * t * k⁻¹ = M.yK)
    {u : ↥M.K4} (hu2 : u * u = 1) (hu1 : u ≠ 1) (huc : u ∉ Subgroup.center ↥M.K4) :
    IsCentralInvolution (mkP M u) := by
  obtain ⟨S, hS⟩ := hG.exists_center_sylow
  have hy1 := (hS (yP M)).2 (Subgroup.mem_zpowers _)
  have hy : IsCentralInvolution (yP M) :=
    ⟨orderOf_yP M hG.two_ne_zero, S, hy1.1, hy1.2⟩
  obtain ⟨k, hk⟩ := hone u hu2 hu1 huc
  refine isCentralInvolution_of_isConj hy ?_
  rw [isConj_iff]
  refine ⟨(mkP M k)⁻¹, ?_⟩
  have h1 : yP M = mkP M k * mkP M u * (mkP M k)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hk]
  rw [h1]
  group

end Facts


section Big


variable [Finite F] {M : ModelData F} {q : ℕ} {ε : ℤ}

theorem hP_big (hM : BigModel M q ε) {u : ↥M.K4} (hu2 : u * u = 1) (hπu : mkP M u ≠ 1)
    {H : Subgroup (MulAut (PG M))} (hH : (MulAut.conj : PG M →* MulAut (PG M)).range ≤ H)
    {c : ↥H} (hc : c ∈ involutionOddCore (LocBalSL4Abs.phi hH (mkP M u)))
    {w : PG M} (hw : w ∈ (Subgroup.centralizer ({u} : Set ↥M.K4)).map (mkP M)) :
    ((c : ↥H) : MulAut (PG M)) w = w := by
  by_cases hc1 : c = 1
  · rw [hc1]
    rfl
  have hu1 : u ≠ 1 := fun h => hπu (by rw [h, map_one])
  have huc : u ∉ Subgroup.center ↥M.K4 := fun hcen => hπu ((mkP_eq_one_iff hM.center u).2 hcen)
  have hβ := isCentralInvolution_mkP hM.good hM.one hu2 hu1 huc
  obtain ⟨γ, hγ, hcγ⟩ := LocBalSL4Ivk.exists_inner_of_odd_core hM.centerless hM.odd hM.gt3 hM.eps
    hM.mod8 hM.lnEps hβ hH hc hc1
  have hcomm := pPrimeCoreOf_comm_centralizer hM.good hM.one hu2 hu1 huc hγ hw
  rw [hcγ, MulAut.conj_apply, hcomm]
  group

theorem locBal32_model_big (hM : BigModel M q ε) {Ab : Subgroup ↥M.K4}
    (hAe : CFSG.IsElementaryAbelian 2 ↥Ab) (hA8 : Nat.card ↥Ab = 8)
    (B : Subgroup (MulAut (PG M)))
    (hB : B ≤ (Ab.map (mkP M)).map (MulAut.conj : PG M →* MulAut (PG M))) :
    IsLocBal32 (PG M) B := by
  have hxA : M.xK ∈ Ab := hM.e8 Ab hAe hA8
  have hmk : ∀ b : ↥M.K4, mkP M b ≠ 1 ↔ b ∉ Subgroup.center ↥M.K4 := fun b =>
    not_congr (mkP_eq_one_iff hM.center b)
  have hx1 : M.xK ≠ 1 := by
    intro h
    have h1 := M.orderOf_xK hM.good.two_ne_zero
    rw [h, orderOf_one] at h1
    omega
  have hπx : mkP M M.xK = 1 := (mkP_eq_one_iff hM.center M.xK).2 ((hM.center _).2 (Or.inr rfl))
  refine locBal32_of_fix (mkP M) (mkP_surjective M) hM.centerless hAe hA8 hxA hx1 hπx
    ?_ ?_ B hB
  · have h := CFSG.GH74.Generic.BProg.B2.shapeGen_1_proved ↥M.K4 hM.qshape Ab hAe hA8
    simp only [hmk]
    exact h
  · intro u huA hπu H hH c hc w hw
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hu2 : u * u = 1 := by
      rw [← pow_two]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Ab) u huA
    exact hP_big hM hu2 hπu hH hc hw

end Big

end LocBalSL4Model

end CFSG.GH74.Generic.BProg.B3
