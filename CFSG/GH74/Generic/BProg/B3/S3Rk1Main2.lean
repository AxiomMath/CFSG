module

public import CFSG.GH74.Generic.BProg.B3.S3Obs32Conj
public import CFSG.GH74.Generic.BProg.B3.S3Rk1Four
public import CFSG.GH74.Generic.BProg.B3.S3Rk1Orbit
public import CFSG.GH74.Generic.BProg.B3.S3PumpFinal
public import CFSG.GH74.Generic.S3.LyRank3

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open scoped commutatorElement

@[expose] def Prop306aBarAt {G : Type} [Group G] [Finite G] (x : G) (K A : Subgroup G) : Prop :=
  ∀ y : G, Setup30 G x K A y →
    S45.barSub y (pumpUp 2 (Ly K y) y) = S45.barSub y (Ly K y)

namespace S3Rk1Main2

variable {G : Type} [Group G] [Finite G]

theorem mul_comm_of_commutator_eq_bot {X : Type} [Group X] {A B : Subgroup X} (h : ⁅A, B⁆ = ⊥) {a b : X}
    (ha : a ∈ A) (hb : b ∈ B) : a * b = b * a := by
  have := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this

theorem false_of_three_components (hG : Gen4 G) {y : G} {L₁ L₂ L₃ : Subgroup G}
    (h₁ : IsPCompIn 2 (centralizer ({y} : Set G)) L₁) (h₂ : IsPCompIn 2 (centralizer ({y} : Set G)) L₂)
    (h₃ : IsPCompIn 2 (centralizer ({y} : Set G)) L₃) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) :
    False := by
  have hY : Gen4 (barQ ↥(centralizer ({y} : Set G))) := gen4_barQ hG y
  have c12 := (FalseCtxS45Comp.pCompIn_eq_or_commute h₁ h₂).resolve_left h12
  have c13 := (FalseCtxS45Comp.pCompIn_eq_or_commute h₁ h₃).resolve_left h13
  have c23 := (FalseCtxS45Comp.pCompIn_eq_or_commute h₂ h₃).resolve_left h23
  exact S3.not_gen4_of_three_commuting_quasisimple
    (A := PumpCalc.bar y L₁) (B := PumpCalc.bar y L₂) (J := PumpCalc.bar y L₃)
    (FalseCtxS45Comp.isComponent_bar h₁).1 (FalseCtxS45Comp.isComponent_bar h₂).1
    (FalseCtxS45Comp.isComponent_bar h₃).1
    (fun a ha b hb => mul_comm_of_commutator_eq_bot c12 ha hb)
    (fun a ha b hb => mul_comm_of_commutator_eq_bot c13 ha hb)
    (fun a ha b hb => mul_comm_of_commutator_eq_bot c23 ha hb) hY

theorem prop312a_aux {x a : G} {K A D J : Subgroup G} (h306 : Prop306aBarAt x K A) (hc : Ctx21 G x K A a D J)
    (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K)) (hC : pRank 2 ↥(CxK x K) ≤ 1) :
    ∀ g ∈ normalizer (A : Set G), g * x = x * g := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4, hxK⟩ := S3Rk1Basic.exists_E hc.circ hc.src h3
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := S3Rk1Basic.pcomp_of_circ hc.circ
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hx2 : orderOf x = 2 := S3Rk1Basic.orderOf_x_of_circ hc.circ
  have hx1 : x ≠ 1 := fun h => by simp [h] at hx2
  have hxx : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx2, sq] at this
  have hxA : x ∈ A := hAE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hEx : ∀ e ∈ E, e * x = x * e := fun e he => S3Rk1Basic.comm_E_x hKC hEK he
  have hsqE : ∀ e ∈ E, e * e = 1 := fun e he => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) e he
    rwa [sq] at this
  have hax : a ≠ x := s3_a_ne_x hc h3
  have ha2 : orderOf a = 2 := hc.obs.y_ord
  have ha1 : a ≠ 1 := fun h => by simp [h] at ha2
  obtain ⟨y, hyE, hay⟩ := S3Rk1Basic.decomp_A hKC hEK hAE hx2 hc.a_mem
  have hy1 : y ≠ 1 := by
    intro h
    rcases hay with h' | h'
    · exact ha1 (by rw [h', h])
    · exact hax (by rw [h', h, one_mul])
  have hyK : y ∈ K := hEK hyE
  have hyA : y ∈ A := hEA hyE
  have hy2 : orderOf y = 2 := orderOf_eq_prime (by rw [sq]; exact hsqE y hyE) hy1
  have hset : Setup30 G x K A y :=
    ⟨hc.hyp, hc.circ, h3, hc.src, hC, Subgroup.mem_inf.2 ⟨hyA, hyK⟩, hy2⟩
  obtain ⟨T, hT, hAT⟩ := Setup30.exists_T hset
  have h301 := prop301T hset hT
  have hxy : ∀ g : G, g * x * g⁻¹ ≠ y := h301.2.1
  have htr : ∀ a₀ ∈ E, a₀ ≠ 1 → ∀ y' ∈ E, y' ≠ 1 → ∃ σ ∈ normalizer (E : Set G),
      σ * x = x * σ ∧ σ * a₀ * σ⁻¹ = y' := by
    intro a₀ ha₀ ha₀1 y' hy' hy'1
    obtain ⟨σ, hσ, hσc⟩ := S3Rk1Four.exists_cyc h3 hEK hEel hE4 ha₀ hy' ha₀1 hy'1
    exact ⟨σ, (Subgroup.mem_inf.1 hσ).2,
      Subgroup.mem_centralizer_singleton_iff.1 (hKC (Subgroup.mem_inf.1 hσ).1), hσc⟩
  obtain ⟨-, hF2, hF3⟩ := S3Rk1Orbit.exists_w hx2 hAE hEx htr hyE hy1 hxy hnot
  have hay' : a = y := by
    rcases hay with h | h
    · exact h
    · exfalso
      obtain ⟨g, hgN, hgx⟩ := hF2 y hyE hy1
      exact s3_a_ne_conj_x hc h3 hgN (h.trans hgx.symm)
  have hJ : IsPCompIn 2 (centralizer ({y} : Set G)) J := hay' ▸ hc.obs.comp
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup G, H = pumpUp 2 (Ly K y) y := ⟨_, rfl⟩
  have hH : IsPCompIn 2 (centralizer ({y} : Set G)) H := hHdef ▸ (thm9_l3_rank1 hset).1
  have hLH : Ly K y ≤ H := hHdef ▸ S3Pump305.le_pumpUp hset
  have hbar : S45.barSub y H = S45.barSub y (Ly K y) := hHdef ▸ h306 y hset
  have hLX : Ly K y ≤ K ⊓ centralizer ({y} : Set G) := (Setup30.layer hset).1.1
  have hLK : Ly K y ≤ K := hLX.trans inf_le_left
  have hxC : x ∈ centralizer ({y} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 (hEx y hyE).symm
  have hxcSecH : x ∈ centralizerSection H (pPrimeCoreOf 2 H) := by
    refine ObsPump.mem_cSec_of_bar_comm hH hxC (fun l hl => ?_)
    have hl' : l ∈ S45.barSub y (Ly K y) := hbar ▸ hl
    obtain ⟨g, hg, hgL, rfl⟩ := S45.mem_barSub.1 hl'
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hKC (hLK hgL))
    show proj y ⟨x, hxC⟩ * proj y ⟨g, hg⟩ = proj y ⟨g, hg⟩ * proj y ⟨x, hxC⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgx.symm
  obtain ⟨z, hzE, hz1, hzy⟩ : ∃ z ∈ E, z ≠ 1 ∧ z ≠ y := by
    by_contra hcon
    push Not at hcon
    have hle : E ≤ zpowers y := by
      intro e he
      by_cases h1 : e = 1
      · rw [h1]; exact one_mem _
      · rw [hcon e he h1]; exact Subgroup.mem_zpowers y
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hy2, hE4] at this
    omega
  obtain ⟨w, hwN, hwy, hwx⟩ := hF3 z hzE hz1
  have hwy' : w * y = y * w := by
    calc w * y = (w * y * w⁻¹) * w := by group
      _ = y * w := by rw [hwy]
  have hwC : w ∈ centralizer ({y} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 hwy'
  have hH' : IsPCompIn 2 (centralizer ({y} : Set G)) (H.map (MulAut.conj w).toMonoidHom) :=
    FalseCtxS45Comp.isPCompIn_conj hH hwC
  have hb₀A : z * x ∈ A := A.mul_mem (hEA hzE) hxA
  have hb₀sq : (z * x) * (z * x) = 1 := by
    calc (z * x) * (z * x) = z * (x * z) * x := by group
      _ = z * (z * x) * x := by rw [← hEx z hzE]
      _ = (z * z) * (x * x) := by group
      _ = 1 := by rw [hsqE z hzE, hxx, one_mul]
  have hbad : ¬ (z * x = 1 ∨ z * x = x ∨ z * x = y ∨ z * x = x * y) := by
    rintro (h | h | h | h)
    · exact hxE (by rw [eq_inv_of_mul_eq_one_right h]; exact E.inv_mem hzE)
    · exact hz1 (mul_eq_right.1 h)
    · apply hxE
      have : x = z⁻¹ * y := by rw [← h]; group
      rw [this]
      exact E.mul_mem (E.inv_mem hzE) hyE
    · apply hzy
      have h' : z * x = y * x := by rw [h, hEx y hyE]
      exact mul_right_cancel h'
  have hb₀cSecH' : z * x ∈ centralizerSection (H.map (MulAut.conj w).toMonoidHom)
      (pPrimeCoreOf 2 (H.map (MulAut.conj w).toMonoidHom)) := by
    have h1 := (S3Obs32Conj.mem_cSec_map_conj_iff w x H).2 hxcSecH
    rwa [hwx] at h1
  have hHH' : H ≠ H.map (MulAut.conj w).toMonoidHom := by
    intro h
    have hb₀H : z * x ∈ centralizerSection H (pPrimeCoreOf 2 H) := by
      have h1 := hb₀cSecH'
      rwa [← h] at h1
    have hzC : z ∈ centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 (S3Rk1Four.comm_of_isElementaryAbelian hEel z hzE y hyE)
    have hzN : z ∈ normalizer ((K ⊓ centralizer ({y} : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_inf.2 ⟨hEK hzE, hzC⟩)
    have hxN : x ∈ normalizer ((Ly K y : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun k hk =>
        Subgroup.mem_centralizer_singleton_iff.1 (hKC (hLK hk)))
    have hb₀N : z * x ∈ normalizer ((Ly K y : Subgroup G) : Set G) :=
      (normalizer ((Ly K y : Subgroup G) : Set G)).mul_mem (S3Pump305.mem_normalizer_pLayerOf hzN) hxN
    have hb₀L : z * x ∈ centralizerSection (Ly K y) (pPrimeCoreOf 2 (Ly K y)) := by
      refine ⟨hb₀N, TwoThin.mem_normalizer_pPrimeCoreOf hb₀N, fun l hl => ?_⟩
      have h1 : ⁅l, z * x⁆ ∈ pPrimeCoreOf 2 H := hb₀H.2.2 l (hLH hl)
      have h2 : ⁅l, z * x⁆ ∈ Ly K y := by
        have hl' : (z * x) * l⁻¹ * (z * x)⁻¹ ∈ Ly K y :=
          (Subgroup.mem_normalizer_iff.1 hb₀N l⁻¹).1 (inv_mem hl)
        have : ⁅l, z * x⁆ = l * ((z * x) * l⁻¹ * (z * x)⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [this]
        exact mul_mem hl hl'
      exact S3Pump305.inf_pPrimeCoreOf_le hLH (Subgroup.mem_inf.2 ⟨h2, h1⟩)
    exact hbad (Setup30.omega_CTL hset hT (z * x) (hAT hb₀A) hb₀L hb₀sq)
  have hHJ : H ≠ J := by
    intro h
    rw [h] at hxcSecH
    rcases hc.cA_eq x hxA hxcSecH with h1 | h1
    · exact hx1 h1
    · exact hxy 1 (by rw [hay'] at h1; simpa using h1)
  have hH'J : H.map (MulAut.conj w).toMonoidHom ≠ J := by
    intro h
    rw [h] at hb₀cSecH'
    rcases hc.cA_eq (z * x) hb₀A hb₀cSecH' with h1 | h1
    · exact hbad (Or.inl h1)
    · exact hbad (Or.inr (Or.inr (Or.inl (h1.trans hay'))))
  exact false_of_three_components hc.hyp.gen4 hH hH' hJ hHH' hHJ hH'J

end S3Rk1Main2

theorem prop312a_of_barAt {G : Type} [Group G] [Finite G] {x a : G} {K A D J : Subgroup G}
    (h306 : Prop306aBarAt x K A) (hc : Ctx21 G x K A a D J) (h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K))
    (hC : pRank 2 ↥(CxK x K) ≤ 1) : ∀ g ∈ normalizer (A : Set G), g * x = x * g :=
  S3Rk1Main2.prop312a_aux h306 hc h3 hC

end CFSG.GH74.Generic.BProg.B3
