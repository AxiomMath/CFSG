module

public import CFSG.GH74.Generic.BProg.B3.S3PumpSwap
public import CFSG.GH74.Generic.S45.LDiagCore
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3PumpKey

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.GH74.Generic.BProg.B3.S3Fusion CFSG.Blueprint CFSG.ABGLocalTools
  CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Subgroup
open scoped commutatorElement

theorem perfect_le_Kb {X : Type} [Group X] [Finite X] {Kb : Subgroup X}
    (hKc : ∀ k ∈ Kb, (∀ g ∈ Kb, g * k = k * g) → k = 1)
    (hkey : ∀ P : Subgroup X, P ≤ centralizer (Kb : Set X) → ⁅P, P⁆ = P → P = ⊥)
    {R : Subgroup X} (hR : ⁅R, R⁆ = R)
    (hRle : ∀ l ∈ R, ∃ m ∈ Kb, l * m⁻¹ ∈ centralizer (Kb : Set X)) : R ≤ Kb := by
  classical
  set Cb : Subgroup X := centralizer (Kb : Set X) with hCb
  let Ψ : ↥Kb × ↥Cb →* X := MonoidHom.noncommCoprod Kb.subtype Cb.subtype
    (fun m c => (mem_centralizer_iff.mp c.2 m m.2 : (m : X) * c = c * m))
  have hΨ : ∀ p : ↥Kb × ↥Cb, Ψ p = (p.1 : X) * p.2 := fun p => MonoidHom.noncommCoprod_apply _ _ _ p
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨m, c⟩ h1
    rw [hΨ] at h1
    have h2 : (m : X) = (c : X)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hmC : (m : X) ∈ Cb := by rw [h2]; exact Cb.inv_mem c.2
    have hm1 : (m : X) = 1 := hKc m m.2 fun g hg => mem_centralizer_iff.mp hmC g hg
    have hc1 : (c : X) = 1 := by rw [hm1, one_mul] at h1; exact h1
    exact Prod.ext (Subtype.ext hm1) (Subtype.ext hc1)
  have hR_range : R ≤ Ψ.range := by
    intro l hl
    obtain ⟨m, hm, hc⟩ := hRle l hl
    refine ⟨(⟨m, hm⟩, ⟨l * m⁻¹, hc⟩), ?_⟩
    rw [hΨ]
    show m * (l * m⁻¹) = l
    have := mem_centralizer_iff.mp hc m hm
    calc m * (l * m⁻¹) = (l * m⁻¹) * m := this
      _ = l := by group
  set R' : Subgroup (↥Kb × ↥Cb) := R.comap Ψ with hR'
  have hR'map : R'.map Ψ = R := Subgroup.map_comap_eq_self hR_range
  have hR'perf : ⁅R', R'⁆ = R' := by
    apply Subgroup.map_injective hΨinj
    rw [Subgroup.map_commutator, hR'map]
    exact hR
  set R'' : Subgroup ↥Cb := R'.map (MonoidHom.snd ↥Kb ↥Cb) with hR''
  have hR''perf : ⁅R'', R''⁆ = R'' := by
    rw [hR'', ← Subgroup.map_commutator, hR'perf]
  have hbot : R''.map Cb.subtype = ⊥ := by
    refine hkey _ (Subgroup.map_subtype_le _) ?_
    rw [← Subgroup.map_commutator, hR''perf]
  have hR''bot : R'' = ⊥ := by
    apply Subgroup.map_injective Cb.subtype_injective
    rw [hbot, Subgroup.map_bot]
  intro l hl
  rw [← hR'map] at hl
  obtain ⟨⟨m, c⟩, hp, rfl⟩ := hl
  have hc : c ∈ R'' := ⟨(m, c), hp, rfl⟩
  rw [hR''bot, Subgroup.mem_bot] at hc
  rw [hΨ]
  show (m : X) * (c : X) ∈ Kb
  rw [hc, Subgroup.coe_one, mul_one]
  exact m.2

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {x y : G} {K T : Subgroup G} (h : Cfg x y K T)

include h

theorem x_mem_Th_of_xbar {θ : G} (hθ : θ ∈ Th x y) (hpi : piC x θ = xbar x) : x ∈ Th x y := by
  classical
  have hθC : θ ∈ centralizer ({x} : Set G) := Th_le_C x y hθ
  obtain ⟨a, m, hm, hom⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos θ).ne'
  set g : ↥(centralizer ({x} : Set G)) := ⟨θ, hθC⟩ with hg
  have hθ' : ((g ^ m : ↥(centralizer ({x} : Set G))) : G) = θ ^ m := Subgroup.coe_pow _ _ _
  have hθ'Th : ((g ^ m : ↥(centralizer ({x} : Set G))) : G) ∈ Th x y := by
    rw [hθ']
    exact (Th x y).pow_mem hθ m
  have hpi' : piC x ((g ^ m : ↥(centralizer ({x} : Set G))) : G) = xbar x := by
    rw [piC_of_mem x (g ^ m).2, map_pow]
    have : proj x g = xbar x := (piC_of_mem x hθC).symm.trans hpi
    rw [this]
    obtain ⟨k, rfl⟩ := hm
    have hxb2 : xbar x * xbar x = 1 := xbar_mul_self h.hx
    calc xbar x ^ (2 * k + 1) = (xbar x * xbar x) ^ k * xbar x := by rw [pow_succ, pow_mul, sq]
      _ = xbar x := by rw [hxb2, one_pow, one_mul]
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hcomm : ((g ^ m : ↥(centralizer ({x} : Set G))) : G) * x =
      x * ((g ^ m : ↥(centralizer ({x} : Set G))) : G) :=
    mem_centralizer_singleton_iff.mp (g ^ m).2
  have hai : (((g ^ m : ↥(centralizer ({x} : Set G))) : G)) ^ (2 ^ a) = 1 := by
    rw [hθ', ← pow_mul, mul_comm, ← hom]
    exact pow_orderOf_eq_one _
  have hbj : x ^ (2 ^ 1) = 1 := by rw [pow_one, sq]; exact h.hx2
  have := eq_of_piC_eq_of_commute (g ^ m).2 hxC hcomm hai hbj (hpi'.trans (piC_x x).symm)
  rw [this] at hθ'Th
  exact hθ'Th

theorem false_of_perfect_C {n : G} (hn : n ∈ normalizer (T : Set G)) (hnx : n * x * n⁻¹ = x * y)
    (hny : n * y * n⁻¹ = y) {P : Subgroup (CentralizerBar x)} (hP : ⁅P, P⁆ = P)
    (hPC : P ≤ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x))) (hxP : xbar x ∈ P) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hybK, hyb2, hyb1⟩ := h.yb_facts
  obtain ⟨F, hF, hFin, S, -, hSD⟩ := S3PumpSData.exists_sdata_layer h.hK h.hyK h.hy h.shape
  have hyΘ : y ∈ Th x y := h.y_mem_Th
  have hPc : ∀ p ∈ P, p * piC x y = piC x y * p := fun p hp =>
    (mem_centralizer_iff.mp (hPC hp) (piC x y) hybK).symm
  have hPle : P ≤ (f0 x y).range := by
    rw [← imgBar_Th_eq_range]
    exact le_imgBar_Th h.hyC h.hy2 hP hPc
  obtain ⟨P₀, hP₀perf, hP₀map⟩ := exists_perfect_lift (f0 x y) hP hPle
  obtain ⟨θx, hθx, hfθx⟩ : ∃ θx ∈ P₀, f0 x y θx = xbar x := by
    have : xbar x ∈ P₀.map (f0 x y) := by rw [hP₀map]; exact hxP
    obtain ⟨θ, hθ, e⟩ := this
    exact ⟨θ, hθ, e⟩
  have hxΘ : x ∈ Th x y := x_mem_Th_of_xbar h θx.2 ((f0_apply x y θx).symm.trans hfθx)
  obtain ⟨α, hα⟩ := exists_alpha (Th x y) n (h.norm_Th hn).1 (h.norm_Th hn).2
  have hnxΘ : n * x * n⁻¹ ∈ Th x y := (h.norm_Th hn).1 x hxΘ
  have hnyΘ : n * y * n⁻¹ ∈ Th x y := (h.norm_Th hn).1 y hyΘ
  have hSR : S.map (S3.imgBar x K).subtype ≤ (f0 x y).range := h.SX_le_range hSD
  have hRperf : ⁅(f0 x y).range, (f0 x y).range⁆ = (f0 x y).range := by
    rw [← imgBar_Th_eq_range]
    exact imgBar_Th_perfect x y
  have hperfR : Group.IsPerfect ↥(f0 x y).range := Subgroup.isPerfect_iff.2 hRperf
  have hRle := fun l hl => h.shape.perfect_le hperfR l hl
  have hRu : ∀ l ∈ (f0 x y).range, l * piC x y = piC x y * l := by
    rintro _ ⟨θ, rfl⟩
    rw [f0_apply]
    have hθC : (θ : G) ∈ centralizer ({x} : Set G) := Th_le_C x y θ.2
    have hθy : (θ : G) * y = y * (θ : G) :=
      mem_centralizer_singleton_iff.mp (maxPerfect_le _ θ.2).2
    rw [← piC_mul x hθC h.hyC, ← piC_mul x h.hyC hθC, hθy]
  have hKc : ∀ k ∈ S3.imgBar x K, (∀ g ∈ S3.imgBar x K, g * k = k * g) → k = 1 := by
    intro k hk hkc
    have hmem : (⟨k, hk⟩ : ↥(S3.imgBar x K)) ∈ center ↥(S3.imgBar x K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hkc g g.2)
    rw [h.shape.centerless, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  refine S3PumpSwap.key_core (f0 x y) (pPrimeCore 2 ↥(Th x y)) (ker_f0_le_Q x y)
    (fun q hq => odd_of_mem_pPrimeCore hq) hSD hyb1 hyb2 hKc hSR hRperf hRle hRu α
    ⟨y, hyΘ⟩ ⟨x, hxΘ⟩ (f0_apply x y ⟨y, hyΘ⟩) ?_ ?_ P₀ hP₀perf ?_ ?_
  · have := hα ⟨y, hyΘ⟩ hnyΘ
    rw [this]
    congr 1
    exact Subtype.ext hny
  · have := hα ⟨x, hxΘ⟩ hnxΘ
    rw [this]
    congr 1
    exact Subtype.ext hnx
  · intro p hp
    exact hPC (by rw [← hP₀map]; exact ⟨p, hp, rfl⟩)
  · refine ⟨θx, hθx, ?_⟩
    apply QuotientGroup.eq.2
    apply ker_f0_le_Q x y
    rw [MonoidHom.mem_ker, map_mul, map_inv, hfθx, f0_apply]
    show (xbar x)⁻¹ * piC x x = 1
    rw [piC_x, inv_mul_cancel]

theorem perfect_C_eq_bot {n : G} (hn : n ∈ normalizer (T : Set G)) (hnx : n * x * n⁻¹ = x * y)
    (hny : n * y * n⁻¹ = y) {P : Subgroup (CentralizerBar x)} (hPC : P ≤ centralizer
      ((S3.imgBar x K : Subgroup (CentralizerBar x)) : Set (CentralizerBar x))) (hP : ⁅P, P⁆ = P) :
    P = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hodd : ¬ Odd (Nat.card ↥P) := fun ho => hne (eq_bot_of_perfect_of_odd hP ho)
  have h2 : 2 ∣ Nat.card ↥P := by
    rcases Nat.even_or_odd (Nat.card ↥P) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 h2
  have heord : orderOf (e : CentralizerBar x) = 2 := by rw [Subgroup.orderOf_coe]; exact he
  have hex : (e : CentralizerBar x) = xbar x := h.shape.only e (hPC e.2) heord
  exact false_of_perfect_C h hn hnx hny hP hPC (hex ▸ e.2)

end Cfg

end S3PumpKey

end CFSG.GH74.Generic.BProg.B3
