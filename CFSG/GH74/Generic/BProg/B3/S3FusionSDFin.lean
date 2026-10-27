module

public import CFSG.GH74.Generic.BProg.B3.S3FusionSwap
public import CFSG.GH74.Generic.S3.V1InnerUni

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Fusion

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.S3 CFSG.GH74.Generic.S45
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5
  CFSG.GH74.Generic.BProg.B1.PilotS3 Subgroup
open scoped commutatorElement

theorem odd_of_mem_pPrimeCore {Θ : Type*} [Group Θ] [Finite Θ] {q : Θ} (hq : q ∈ pPrimeCore 2 Θ) :
    Odd (orderOf q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : Nat.Coprime 2 (Nat.card (pPrimeCore 2 Θ)) := pPrimeCore_coprime_card
  have hd : orderOf q ∣ Nat.card (pPrimeCore 2 Θ) := Subgroup.orderOf_dvd_natCard _ hq
  exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right hd hc)

theorem exists_alpha {G : Type*} [Group G] (Θ : Subgroup G) [Finite Θ] (m : G)
    (h1 : ∀ θ ∈ Θ, m * θ * m⁻¹ ∈ Θ) (h2 : ∀ θ ∈ Θ, m⁻¹ * θ * m ∈ Θ) :
    ∃ α : (↥Θ ⧸ pPrimeCore 2 ↥Θ) ≃* (↥Θ ⧸ pPrimeCore 2 ↥Θ),
      ∀ (θ : ↥Θ) (hθ : m * (θ : G) * m⁻¹ ∈ Θ), α (θ : ↥Θ ⧸ pPrimeCore 2 ↥Θ) =
        ((⟨m * (θ : G) * m⁻¹, hθ⟩ : ↥Θ) : ↥Θ ⧸ pPrimeCore 2 ↥Θ) := by
  let e : ↥Θ ≃* ↥Θ :=
    { toFun := fun θ => ⟨m * θ * m⁻¹, h1 θ θ.2⟩
      invFun := fun θ => ⟨m⁻¹ * θ * m, h2 θ θ.2⟩
      left_inv := fun θ => Subtype.ext (by simp [mul_assoc])
      right_inv := fun θ => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have he : (pPrimeCore 2 ↥Θ).map e.toMonoidHom = pPrimeCore 2 ↥Θ := pPrimeCore_map_iso 2 e
  exact ⟨QuotientGroup.congr (pPrimeCore 2 ↥Θ) (pPrimeCore 2 ↥Θ) e he, fun θ hθ => rfl⟩

theorem conj_inv_mem_of_normalizer {G : Type} [Group G] {T : Subgroup G} {m : G}
    (hm : m ∈ normalizer (T : Set G)) {t : G} (ht : t ∈ T) : m⁻¹ * t * m ∈ T := by
  have hmT := mem_normalizer_iff.mp hm
  refine (hmT (m⁻¹ * t * m)).mpr ?_
  have e : m * (m⁻¹ * t * m) * m⁻¹ = t := by group
  rw [e]
  exact ht

theorem false_of_odd_mul {X : Type} [Group X] {xh : X} {Kb : Subgroup X} (hxh2 : xh * xh = 1)
    (hxhc : ∀ g : X, g * xh = xh * g) (hnot : xh ∉ Kb) {w : X} (hw : w ∈ Kb)
    (hodd : Odd (orderOf (xh * w))) : False := by
  obtain ⟨k, hk⟩ := hodd
  have hcomm : Commute xh w := (hxhc w).symm
  have h1 : (xh * w) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  rw [hcomm.mul_pow] at h1
  have hxk : xh ^ (2 * k + 1) = xh := by
    rw [pow_succ, pow_mul, sq, hxh2, one_pow, one_mul]
  rw [hxk] at h1
  apply hnot
  have : xh = (w ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [this]
  exact Kb.inv_mem (Kb.pow_mem hw _)

theorem classify_involution {X : Type} [Group X] [Finite X] {xh : X} {Kb SX : Subgroup X} {u : X}
    (hB : BarShape X xh Kb) (hS : SData X Kb u SX) (hu2 : u * u = 1) {g : X} (hg2 : g * g = 1)
    (hgu : g * u = u * g) (hgS : ∀ s ∈ SX, g * s = s * g) :
    g = 1 ∨ g = xh ∨ g = u ∨ g = u * xh := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinvC : ∀ c : X, c ∈ centralizer (Kb : Set X) → c * c = 1 → c = 1 ∨ c = xh := by
    intro c hc hc2
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    · right
      exact hB.only c hc (orderOf_eq_prime (by rw [sq]; exact hc2) hc1)
  rcases hS.aut g hg2 hgu hgS with h1 | h1
  · have hg : g ∈ centralizer (Kb : Set X) := mem_centralizer_iff.mpr fun k hk => (h1 k hk).symm
    rcases hinvC g hg hg2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
    have hc : u * g ∈ centralizer (Kb : Set X) := by
      rw [mem_centralizer_iff]
      intro k hk
      have e := h1 k hk
      rw [hu_inv] at e
      have e2 : g * k = u * k * u * g := by
        have := congrArg (· * g) e
        simpa [mul_assoc] using this
      calc k * (u * g) = (u * u) * k * (u * g) := by rw [hu2, one_mul]
        _ = u * (u * k * u * g) := by group
        _ = u * (g * k) := by rw [e2]
        _ = (u * g) * k := by group
    have hc2 : (u * g) * (u * g) = 1 := by
      calc (u * g) * (u * g) = u * (g * u) * g := by group
        _ = u * (u * g) * g := by rw [hgu]
        _ = (u * u) * (g * g) := by group
        _ = 1 := by rw [hu2, hg2, one_mul]
    have hgc : g = u * (u * g) := by rw [← mul_assoc, hu2, one_mul]
    rcases hinvC _ hc hc2 with h | h
    · right; right; left
      rw [hgc, h, mul_one]
    · right; right; right
      rw [hgc, h]

variable {G : Type} [Group G] [Finite G]

namespace Cfg

variable {x y : G} {K T : Subgroup G} (h : Cfg x y K T)

include h

theorem norm_Th {m : G} (hm : m ∈ normalizer (T : Set G)) :
    (∀ θ ∈ Th x y, m * θ * m⁻¹ ∈ Th x y) ∧ (∀ θ ∈ Th x y, m⁻¹ * θ * m ∈ Th x y) :=
  ⟨fun θ hθ => conj_mem_maxPerfect (h.conj_M hm) hθ, fun θ hθ => by
    have := conj_mem_maxPerfect (h.conj_M (inv_mem hm)) hθ
    simpa using this⟩

theorem SX_le_range {SX : Subgroup (CentralizerBar x)}
    (hS : SData (CentralizerBar x) (S3.imgBar x K) (piC x y) SX) : SX ≤ (f0 x y).range := by
  rw [← imgBar_Th_eq_range]
  exact le_imgBar_Th h.hyC h.hy2 hS.perf hS.comm

theorem swap_out {n : G} (hn : n ∈ normalizer (T : Set G)) (hnx : n * x * n⁻¹ = y)
    {SX : Subgroup (CentralizerBar x)}
    (hS : SData (CentralizerBar x) (S3.imgBar x K) (piC x y) SX) :
    ∃ α : (↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) ≃* (↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)),
      (∀ (θ : ↥(Th x y)) (hθ : n * (θ : G) * n⁻¹ ∈ Th x y),
        α (θ : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) =
          ((⟨n * (θ : G) * n⁻¹, hθ⟩ : ↥(Th x y)) : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y))) ∧
      ∀ θ : ↥(Th x y), f0 x y θ ∈ SX → ∃ θc : ↥(Th x y),
        f0 x y θc ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
          Set (CentralizerBar x)) ∧
        α (θ : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) =
          (θc : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyΘ : y ∈ Th x y := h.y_mem_Th
  obtain ⟨hybK, hyb2, hyb1⟩ := h.yb_facts
  obtain ⟨α, hα⟩ := exists_alpha (Th x y) n (h.norm_Th hn).1 (h.norm_Th hn).2
  refine ⟨α, hα, ?_⟩
  have hSR : SX ≤ (f0 x y).range := h.SX_le_range hS
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
  have hnyΘ : n * y * n⁻¹ ∈ Th x y := (h.norm_Th hn).1 y hyΘ
  have hαy : α ((⟨y, hyΘ⟩ : ↥(Th x y)) : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) =
      ((⟨n * y * n⁻¹, hnyΘ⟩ : ↥(Th x y)) : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) :=
    hα ⟨y, hyΘ⟩ hnyΘ
  obtain ⟨hzT, hzc, hz2⟩ := conj_Z hn y h.hyT h.hyc h.hy2
  have hz : n * y * n⁻¹ = x ∨ n * y * n⁻¹ = y * x := by
    rcases h.hZ _ hzT hzc hz2 with e | e | e | e
    · exfalso
      apply h.hy1
      have e1 : y = n⁻¹ * (n * y * n⁻¹) * n := by group
      rw [e1, e]
      group
    · exact Or.inl e
    · exfalso
      apply h.hxy
      have : n * x * n⁻¹ = n * y * n⁻¹ := by rw [hnx, e]
      exact mul_left_cancel (mul_right_cancel this)
    · exact Or.inr e
  have hxb2 : xbar x * xbar x = 1 := xbar_mul_self h.hx
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have hf0z : f0 x y ⟨n * y * n⁻¹, hnyΘ⟩ = xbar x ∨
      f0 x y ⟨n * y * n⁻¹, hnyΘ⟩ = piC x y * xbar x := by
    rw [f0_apply]
    show piC x (n * y * n⁻¹) = _ ∨ piC x (n * y * n⁻¹) = _
    rcases hz with hz | hz
    · left
      rw [hz, piC_x]
    · right
      rw [hz, piC_mul x h.hyC hxC, piC_x]
  have hαne : ∀ θ' : ↥(Th x y), f0 x y θ' ∈ SX →
      α ((⟨y, hyΘ⟩ : ↥(Th x y)) : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) ≠
        (θ' : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) := by
    intro θ' hθ' e
    rw [hαy] at e
    have hq : (⟨n * y * n⁻¹, hnyΘ⟩ : ↥(Th x y))⁻¹ * θ' ∈ pPrimeCore 2 ↥(Th x y) :=
      QuotientGroup.eq.1 e
    have hodd' := (odd_of_mem_pPrimeCore hq).of_dvd_nat (orderOf_map_dvd (f0 x y) _)
    rw [map_mul, map_inv] at hodd'
    have hxbinv : (xbar x)⁻¹ = xbar x := inv_eq_of_mul_eq_one_right hxb2
    have hubinv : (piC x y)⁻¹ = piC x y := inv_eq_of_mul_eq_one_right hyb2
    rcases hf0z with hf | hf
    · rw [hf, hxbinv] at hodd'
      exact false_of_odd_mul hxb2 h.shape.xh_cent h.shape.xh_notin (hS.le_Kb hθ') hodd'
    · rw [hf, mul_inv_rev, hxbinv, hubinv, mul_assoc] at hodd'
      exact false_of_odd_mul hxb2 h.shape.xh_cent h.shape.xh_notin
        (hS.le_Kb (SX.mul_mem hS.mem hθ')) hodd'
  exact swap_core (f0 x y) (pPrimeCore 2 ↥(Th x y)) (ker_f0_le_Q x y)
    (fun q hq => odd_of_mem_pPrimeCore hq) hS hyb2 hSR hRperf hRle hRu α ⟨y, hyΘ⟩
    (f0_apply x y ⟨y, hyΘ⟩) hαne

theorem comm_step {n : G} (hn : n ∈ normalizer (T : Set G))
    {SX : Subgroup (CentralizerBar x)}
    (hS : SData (CentralizerBar x) (S3.imgBar x K) (piC x y) SX)
    (α : (↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) ≃* (↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)))
    (hα1 : ∀ (θ : ↥(Th x y)) (hθ : n * (θ : G) * n⁻¹ ∈ Th x y),
      α (θ : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) =
        ((⟨n * (θ : G) * n⁻¹, hθ⟩ : ↥(Th x y)) : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)))
    (hα2 : ∀ θ : ↥(Th x y), f0 x y θ ∈ SX → ∃ θc : ↥(Th x y),
      f0 x y θc ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
        Set (CentralizerBar x)) ∧
      α (θ : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) =
        (θc : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)))
    {f₀ : G} (hf₀ : f₀ ∈ T)
    (hfc : ∀ c ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)), piC x f₀ * c = c * piC x f₀) :
    ∀ s ∈ SX, piC x (n⁻¹ * f₀ * n) * s = s * piC x (n⁻¹ * f₀ * n) := by
  classical
  intro s hs
  have hSR := h.SX_le_range hS
  obtain ⟨θ, hθ⟩ := hSR hs
  have hθs : f0 x y θ ∈ SX := by rw [hθ]; exact hs
  obtain ⟨θc, hθc, hαθ⟩ := hα2 θ hθs
  have hf₀n : f₀ ∈ normalizer (T : Set G) := Subgroup.le_normalizer hf₀
  have hf'T : n⁻¹ * f₀ * n ∈ T := conj_inv_mem_of_normalizer hn hf₀
  have hf'n : n⁻¹ * f₀ * n ∈ normalizer (T : Set G) := Subgroup.le_normalizer hf'T
  obtain ⟨αf, hαf⟩ := exists_alpha (Th x y) f₀ (h.norm_Th hf₀n).1 (h.norm_Th hf₀n).2
  obtain ⟨αg, hαg⟩ := exists_alpha (Th x y) (n⁻¹ * f₀ * n) (h.norm_Th hf'n).1 (h.norm_Th hf'n).2
  have hf₀C : f₀ ∈ centralizer ({x} : Set G) := h.hT.le hf₀
  have hgC : n⁻¹ * f₀ * n ∈ centralizer ({x} : Set G) := h.hT.le hf'T
  have hθC : (θ : G) ∈ centralizer ({x} : Set G) := Th_le_C x y θ.2
  have hθcC : (θc : G) ∈ centralizer ({x} : Set G) := Th_le_C x y θc.2
  have hfθc : f₀ * (θc : G) * f₀⁻¹ ∈ Th x y := (h.norm_Th hf₀n).1 θc θc.2
  have hfix : αf (θc : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) =
      (θc : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) := by
    rw [hαf θc hfθc]
    apply QuotientGroup.eq.2
    apply ker_f0_le_Q x y
    rw [MonoidHom.mem_ker, map_mul, map_inv, f0_apply, f0_apply]
    show (piC x (f₀ * (θc : G) * f₀⁻¹))⁻¹ * piC x (θc : G) = 1
    have hc := hfc _ hθc
    rw [f0_apply] at hc
    rw [piC_mul x (mul_mem hf₀C hθcC) (inv_mem hf₀C), piC_mul x hf₀C hθcC, piC_inv x hf₀C, hc]
    group
  have hgθ : (n⁻¹ * f₀ * n) * (θ : G) * (n⁻¹ * f₀ * n)⁻¹ ∈ Th x y := (h.norm_Th hf'n).1 θ θ.2
  have hnθ : n * (θ : G) * n⁻¹ ∈ Th x y := (h.norm_Th hn).1 θ θ.2
  have hfnθ : f₀ * (n * (θ : G) * n⁻¹) * f₀⁻¹ ∈ Th x y := (h.norm_Th hf₀n).1 _ hnθ
  have hngθ : n * ((n⁻¹ * f₀ * n) * (θ : G) * (n⁻¹ * f₀ * n)⁻¹) * n⁻¹ ∈ Th x y :=
    (h.norm_Th hn).1 _ hgθ
  have hchain : α (αg (θ : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y))) =
      αf (α (θ : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y))) := by
    rw [hαg θ hgθ, hα1 ⟨_, hgθ⟩ hngθ, hα1 θ hnθ, hαf ⟨n * (θ : G) * n⁻¹, hnθ⟩ hfnθ]
    congr 1
    apply Subtype.ext
    show n * ((n⁻¹ * f₀ * n) * (θ : G) * (n⁻¹ * f₀ * n)⁻¹) * n⁻¹ =
      f₀ * (n * (θ : G) * n⁻¹) * f₀⁻¹
    simp only [mul_inv_rev, inv_inv]
    group
  have h3 : α (αg (θ : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y))) =
      α (θ : ↥(Th x y) ⧸ pPrimeCore 2 ↥(Th x y)) := by
    rw [hchain, hαθ, hfix]
  have h4 := α.injective h3
  rw [hαg θ hgθ] at h4
  have hq : (⟨(n⁻¹ * f₀ * n) * (θ : G) * (n⁻¹ * f₀ * n)⁻¹, hgθ⟩ : ↥(Th x y))⁻¹ * θ ∈
      pPrimeCore 2 ↥(Th x y) := QuotientGroup.eq.1 h4
  have hpθ : piC x (θ : G) = s := (f0_apply x y θ).symm.trans hθ
  have hconj : piC x ((n⁻¹ * f₀ * n) * (θ : G) * (n⁻¹ * f₀ * n)⁻¹) =
      piC x (n⁻¹ * f₀ * n) * s * (piC x (n⁻¹ * f₀ * n))⁻¹ := by
    rw [piC_mul x (mul_mem hgC hθC) (inv_mem hgC), piC_mul x hgC hθC, piC_inv x hgC, hpθ]
  have hgu : piC x (n⁻¹ * f₀ * n) * piC x y = piC x y * piC x (n⁻¹ * f₀ * n) := by
    rw [← piC_mul x hgC h.hyC, ← piC_mul x h.hyC hgC, h.hyc _ hf'T]
  have hnormS := hS.norm (piC x (n⁻¹ * f₀ * n)) hgu s hs
  have ht : (piC x (n⁻¹ * f₀ * n) * s * (piC x (n⁻¹ * f₀ * n))⁻¹)⁻¹ * s ∈
      SX ⊓ (pPrimeCore 2 ↥(Th x y)).map (f0 x y) := by
    refine ⟨SX.mul_mem (SX.inv_mem hnormS) hs, _, hq, ?_⟩
    rw [map_mul, map_inv, f0_apply, f0_apply]
    show (piC x ((n⁻¹ * f₀ * n) * (θ : G) * (n⁻¹ * f₀ * n)⁻¹))⁻¹ * piC x (θ : G) = _
    rw [hconj, hpθ]
  have h5 := hS.inter_map_trivial (f0 x y) _ (fun q hq => odd_of_mem_pPrimeCore hq) hSR _ ht
  have e : piC x (n⁻¹ * f₀ * n) * s * (piC x (n⁻¹ * f₀ * n))⁻¹ = s := inv_mul_eq_one.1 h5
  calc piC x (n⁻¹ * f₀ * n) * s
      = piC x (n⁻¹ * f₀ * n) * s * (piC x (n⁻¹ * f₀ * n))⁻¹ * piC x (n⁻¹ * f₀ * n) := by group
    _ = s * piC x (n⁻¹ * f₀ * n) := by rw [e]

theorem false_of_sdata {n : G} (hn : n ∈ normalizer (T : Set G)) (hnx : n * x * n⁻¹ = y)
    {SX : Subgroup (CentralizerBar x)}
    (hS : SData (CentralizerBar x) (S3.imgBar x K) (piC x y) SX)
    {F : Subgroup G} (hFT : F ≤ T) (hFcard : Nat.card ↥F = 8) (hF2 : ∀ f ∈ F, f * f = 1)
    (hFcomm : ∀ f₁ ∈ F, ∀ f₂ ∈ F, f₁ * f₂ = f₂ * f₁)
    (hFc : ∀ f ∈ F, ∀ c ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
      Set (CentralizerBar x)), piC x f * c = c * piC x f) : False := by
  classical
  obtain ⟨α, hα1, hα2⟩ := h.swap_out hn hnx hS
  obtain ⟨-, hyb2, -⟩ := h.yb_facts
  have hconj2 : ∀ f ∈ F, (n⁻¹ * f * n) * (n⁻¹ * f * n) = 1 := fun f hf => by
    calc (n⁻¹ * f * n) * (n⁻¹ * f * n) = n⁻¹ * (f * f) * n := by group
      _ = 1 := by rw [hF2 f hf]; group
  have hgC : ∀ f ∈ F, n⁻¹ * f * n ∈ centralizer ({x} : Set G) := fun f hf =>
    h.hT.le (conj_inv_mem_of_normalizer hn (hFT hf))
  let ι : ↥F → CentralizerBar x := fun f => piC x (n⁻¹ * (f : G) * n)
  have hι_mem : ∀ f : ↥F, ι f = 1 ∨ ι f = xbar x ∨ ι f = piC x y ∨ ι f = piC x y * xbar x := by
    intro f
    have hf := f.2
    have hgu : piC x (n⁻¹ * (f : G) * n) * piC x y = piC x y * piC x (n⁻¹ * (f : G) * n) := by
      rw [← piC_mul x (hgC _ hf) h.hyC, ← piC_mul x h.hyC (hgC _ hf),
        h.hyc _ (conj_inv_mem_of_normalizer hn (hFT hf))]
    refine classify_involution h.shape hS hyb2 ?_ hgu
      (h.comm_step hn hS α hα1 hα2 (hFT hf) (hFc _ hf))
    rw [← piC_mul x (hgC _ hf) (hgC _ hf), hconj2 _ hf, piC_one]
  have hι_inj : Function.Injective ι := by
    intro f₁ f₂ e
    have ha := hgC _ f₁.2
    have hb := hgC _ f₂.2
    have hab : (n⁻¹ * (f₁ : G) * n) * (n⁻¹ * (f₂ : G) * n) =
        (n⁻¹ * (f₂ : G) * n) * (n⁻¹ * (f₁ : G) * n) := by
      calc (n⁻¹ * (f₁ : G) * n) * (n⁻¹ * (f₂ : G) * n) = n⁻¹ * ((f₁ : G) * f₂) * n := by group
        _ = n⁻¹ * ((f₂ : G) * f₁) * n := by rw [hFcomm _ f₁.2 _ f₂.2]
        _ = (n⁻¹ * (f₂ : G) * n) * (n⁻¹ * (f₁ : G) * n) := by group
    have hsq : ∀ f ∈ F, (n⁻¹ * f * n) ^ (2 ^ 1) = 1 := fun f hf => by
      rw [pow_one, sq]
      exact hconj2 f hf
    have := eq_of_piC_eq_of_commute ha hb hab (hsq _ f₁.2) (hsq _ f₂.2) e
    have h' : (f₁ : G) = f₂ := mul_left_cancel (mul_right_cancel this)
    exact Subtype.ext h'
  have : Fintype ↥F := Fintype.ofFinite ↥F
  have hcard : (Finset.univ : Finset ↥F).card ≤
      ({1, xbar x, piC x y, piC x y * xbar x} : Finset (CentralizerBar x)).card := by
    apply Finset.card_le_card_of_injOn ι
    · intro a _
      have := hι_mem a
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact this
    · intro a _ b _ hab
      exact hι_inj hab
  have h4 : ({1, xbar x, piC x y, piC x y * xbar x} : Finset (CentralizerBar x)).card ≤ 4 :=
    Finset.card_le_four
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hFcard] at hcard
  omega

theorem no_normalizer_conj {A : Subgroup G} (hsrc : IsSource2 x K A) {n : G}
    (hn : n ∈ normalizer (T : Set G)) (hnx : n * x * n⁻¹ = y) : False := by
  classical
  have hxTh := h.x_mem_Th hn hnx
  obtain ⟨hybK, hyb2, hyb1⟩ := h.yb_facts
  obtain ⟨t, p, f, ht, hp, hp2, h5, hmod⟩ := h.shape.model
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hq4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  by_cases hcase : t = .PSL ∧ p ^ f % 4 = 1
  · obtain ⟨rfl, h1⟩ := hcase
    have hK2 : RankCertified ↥(S3.imgBar x K) 2 := rankCertified_two_of_eps ⟨p, f, Or.inl ⟨hmod, h1⟩⟩
    refine h.false_of_cyclic hxTh (fun P hP2 hPle => ?_)
    have hinf : S3.imgBar x K ⊓ P = ⊥ := by
      rw [eq_bot_iff]
      rintro z ⟨hzK, hzP⟩
      have hzc : z ∈ centralizer ((S3.imgBar x K : Subgroup (CentralizerBar x)) :
          Set (CentralizerBar x)) := hPle hzP
      have hmem : (⟨z, hzK⟩ : ↥(S3.imgBar x K)) ∈ center ↥(S3.imgBar x K) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (mem_centralizer_iff.mp hzc g g.2)
      rw [h.shape.centerless, Subgroup.mem_bot] at hmem
      exact Subgroup.mem_bot.2 (congrArg Subtype.val hmem)
    exact cyclic_of_rankCertified (gen4_centralizerBar h.gen4 x) hK2
      (fun k hk p' hp' => mem_centralizer_iff.mp (hPle hp') k hk) hinf hP2
  · have hLib : LibData t p f := by
      rcases ht with rfl | rfl
      · have h3 : p ^ f % 4 = 3 := by
          rcases hq4 with h1 | h1
          · exact absurd ⟨rfl, h1⟩ hcase
          · exact h1
        exact libData_lin hp hp2 h5 h3
      · exact libData_uni hp hp2 h5
    have hX : StatedClassicalModel ↥(S3.imgBar x K) t 3 p f := by
      rcases ht with rfl | rfl
      · exact stated_of_lieModel_PSL hmod
      · exact stated_of_lieModel_PSU hmod
    obtain ⟨S, hS⟩ := (hLib ↥(S3.imgBar x K) hX).1 ⟨piC x y, hybK⟩ (Subtype.ext hyb2)
      (fun e => hyb1 (congrArg Subtype.val e))
    have hSD := SData.of_invData h.shape.normal hybK hyb2 hyb1 hS
    obtain ⟨F, hFT, hFcard, hF2, hFcomm, hFc⟩ := exists_F h.shape h.hK h.hT hsrc
    exact h.false_of_sdata hn hnx hSD hFT hFcard hF2 hFcomm hFc

end Cfg

end S3Fusion

end CFSG.GH74.Generic.BProg.B3
