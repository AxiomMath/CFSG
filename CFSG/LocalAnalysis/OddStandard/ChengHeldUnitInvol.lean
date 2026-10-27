module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitGL
public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitSylow
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Img
public import CFSG.LocalAnalysis.OddStandard.ChengHeldSec2Open
public import CFSG.LocalAnalysis.OddStandard.ChengHeldUnitBasic

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A} {α : ℕ}

omit [Finite G] in
theorem normalizerMonoidHom_eq_iff {V : Subgroup G} (n m : normalizer (V : Set G)) :
    V.normalizerMonoidHom n = V.normalizerMonoidHom m ↔
      ∀ v ∈ V, (n : G) * v * (n : G)⁻¹ = (m : G) * v * (m : G)⁻¹ := by
  constructor
  · intro h v hv
    have := congrArg (fun φ : MulAut V => ((φ ⟨v, hv⟩ : V) : G)) h
    simpa [Sec2Aux.normalizerMonoidHom_coe] using this
  · intro h
    ext v
    simpa [Sec2Aux.normalizerMonoidHom_coe] using h v v.2

omit [Finite G] in
theorem normalizerMonoidHom_eq_one_iff {V : Subgroup G} (n : normalizer (V : Set G)) :
    V.normalizerMonoidHom n = 1 ↔ ∀ v ∈ V, (n : G) * v * (n : G)⁻¹ = v := by
  have := normalizerMonoidHom_eq_iff (V := V) n 1
  rw [map_one] at this
  rw [this]
  simp

theorem Chart4.exists_involution_unitary
    (hα : α ≤ 1) (hα0 : α = 0) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) (hQ : chPropsOK = true) (hS2 : chSec2OK = true)
    (hc : Nat.card ↥(d.X ⊓ A ⊓ centralizer (A : Set G)) = 4) {g : G}
    (hg : ∀ s ∈ d.S, g⁻¹ * s * g ∈ d.S) (hact : GAct α c.t c.pi c.tau c.mu c.lam c.ze c.xi g)
    (hk : c.kinds = {Kind.unitary}) (hfus : IsConj d.q c.pi) {y : G}
    (hy : c.rep Kind.unitary = some y) : ∃ x ∈ d.Q, (y * x) * (y * x) = 1 := by
  obtain ⟨hyX, hyQS, hyact⟩ := c.rep_mem Kind.unitary y hy
  have hS := c.sFacts hα h hP hQ
  have hV2 : ∀ v : ↥c.V, v * v = 1 := fun v => Subtype.ext (hS.V_sq v v.2)
  have hXN : d.X ≤ normalizer (c.V : Set G) := fun x hx =>
    mem_normalizer_iff.2 fun v => (c.X_normalizes hα h hP hQ hS2 hc hx).2 v
  have hSN : d.S ≤ normalizer (c.V : Set G) := c.S_le_normalizer_V hα h hP hQ
  have hXsyl : CFSG.ABGLocalTools.IsSylowOf 2 d.X (normalizer (c.V : Set G)) :=
    (c.X_sylow_G_of_facts hα h hP hQ).of_le hXN le_top
  obtain ⟨Pq, hPq⟩ := hXsyl.exists_sylow_eq_subgroupOf
  have hsurj : Function.Surjective c.V.normalizerMonoidHom :=
    c.surjective_normalizerMonoidHom_of_isConj hα h hP hQ hS2 hc hg hact hfus
  let y' : normalizer (c.V : Set G) := ⟨y, hXN hyX⟩
  let μ' : normalizer (c.V : Set G) := ⟨c.mu, hSN c.mem.2.2.1⟩
  have hy'P : y' ∈ (Pq : Subgroup (normalizer (c.V : Set G))) := by
    rw [hPq]
    exact mem_subgroupOf.2 hyX
  have hmuV : ∀ v ∈ c.V, v ∈ d.S := fun v hv => c.V_le_S h hv
  have hpiV : c.pi ∈ c.V := subset_closure (by simp)
  have htauV : c.t * c.tau ∈ c.V := subset_closure (by simp)
  have hyy : c.V.normalizerMonoidHom y' * c.V.normalizerMonoidHom y' = 1 := by
    rw [← map_mul, normalizerMonoidHom_eq_one_iff]
    intro v hv
    have hyyQ : y * y ∈ d.Q := c.sq_mem_Q hα h hP hQ Kind.unitary hyX hyact
    have h1 := d.comm_Q_S hyyQ (hmuV v hv)
    show y * y * v * (y * y)⁻¹ = v
    calc y * y * v * (y * y)⁻¹ = (y * y) * v * (y * y)⁻¹ := rfl
      _ = (v * (y * y)) * (y * y)⁻¹ := by rw [h1]
      _ = v := by group
  have hy1 : c.V.normalizerMonoidHom y' ≠ 1 := by
    rw [Ne, normalizerMonoidHom_eq_one_iff]
    intro hall
    have h1 : y * (c.t * c.tau) * y⁻¹ = c.t * c.tau := hall _ htauV
    have h1' : y * (c.t * c.tau) = (c.t * c.tau) * y := by
      calc y * (c.t * c.tau) = (y * (c.t * c.tau) * y⁻¹) * y := by group
        _ = (c.t * c.tau) * y := by rw [h1]
    have h2 : cj (c.t * c.tau) y = c.t * c.tau := by
      unfold cj
      calc y⁻¹ * (c.t * c.tau) * y = y⁻¹ * ((c.t * c.tau) * y) := by group
        _ = y⁻¹ * (y * (c.t * c.tau)) := by rw [h1']
        _ = c.t * c.tau := by group
    subst hα0
    obtain ⟨ht, -, htau, -⟩ := hyact
    rw [ChartShape.cj_mul, ht, htau] at h2
    apply c.pi_ne_one
    calc c.pi = c.t * (c.t⁻¹ * (c.pi * c.tau⁻¹)) * c.tau := by group
      _ = c.t * (c.t * c.tau) * c.tau := by rw [h2]
      _ = c.t ^ 2 * c.tau ^ 2 := by simp only [pow_two, mul_assoc]
      _ = c.t ^ 2 * c.t ^ 2 := by rw [c.frame.tau_sq]
      _ = c.t ^ 4 := by rw [← pow_add]
      _ = 1 := c.frame.t4
  have hμμ : c.V.normalizerMonoidHom μ' * c.V.normalizerMonoidHom μ' = 1 := by
    have : μ' * μ' = 1 := Subtype.ext (by simpa [pow_two] using c.frame.mu2)
    rw [← map_mul, this, map_one]
  have hμ1 : c.V.normalizerMonoidHom μ' ≠ 1 := by
    rw [Ne, normalizerMonoidHom_eq_one_iff]
    intro hall
    have h1 : c.mu * c.pi * c.mu⁻¹ = c.pi := hall _ hpiV
    have h1' : c.mu * c.pi = c.pi * c.mu := by
      calc c.mu * c.pi = (c.mu * c.pi * c.mu⁻¹) * c.mu := by group
        _ = c.pi * c.mu := by rw [h1]
    have h2 : cj c.pi c.mu = c.pi := by
      unfold cj
      calc c.mu⁻¹ * c.pi * c.mu = c.mu⁻¹ * (c.pi * c.mu) := by group
        _ = c.mu⁻¹ * (c.mu * c.pi) := by rw [h1']
        _ = c.pi := by group
    rw [c.frame.pi_mu] at h2
    apply c.t_sq_ne_one
    have h3 : c.t ^ 2 * c.pi = 1 * c.pi := by rw [h2, one_mul]
    exact mul_right_cancel h3
  obtain ⟨cc, hcc⟩ := isConj_iff.1 (mulAut_involutions_conj hS.card_V hV2 hyy hμμ hy1 hμ1)
  obtain ⟨n, hn⟩ := hsurj cc
  have hι2 : n⁻¹ * μ' * n * (n⁻¹ * μ' * n) = 1 := by
    have : μ' * μ' = 1 := Subtype.ext (by simpa [pow_two] using c.frame.mu2)
    calc n⁻¹ * μ' * n * (n⁻¹ * μ' * n) = n⁻¹ * (μ' * μ') * n := by group
      _ = 1 := by rw [this]; group
  have hιρ : c.V.normalizerMonoidHom (n⁻¹ * μ' * n) = c.V.normalizerMonoidHom y' := by
    rw [map_mul, map_mul, map_inv, hn, ← hcc]
    group
  obtain ⟨ι, hιP, hι2', hιρ'⟩ := exists_involution_of_map_eq c.V.normalizerMonoidHom Pq hy'P hι2 hιρ
  have hιX : (ι : G) ∈ d.X := by
    rw [hPq] at hιP
    exact mem_subgroupOf.1 hιP
  have hι2G : (ι : G) * (ι : G) = 1 := congrArg Subtype.val hι2'
  have hwX : y⁻¹ * (ι : G) ∈ d.X := d.X.mul_mem (d.X.inv_mem hyX) hιX
  have hVc : ∀ v ∈ c.V, (y⁻¹ * (ι : G)) * v = v * (y⁻¹ * (ι : G)) := by
    intro v hv
    have h1 : (ι : G) * v * (ι : G)⁻¹ = y * v * y⁻¹ :=
      (normalizerMonoidHom_eq_iff ι y').1 hιρ' v hv
    calc y⁻¹ * (ι : G) * v = y⁻¹ * ((ι : G) * v * (ι : G)⁻¹) * (ι : G) := by group
      _ = y⁻¹ * (y * v * y⁻¹) * (ι : G) := by rw [h1]
      _ = v * (y⁻¹ * (ι : G)) := by group
  obtain ⟨-, hgraph, -⟩ := c.rep_of_kinds_unitary hk
  rcases c.centralizing_V hα h hP hQ hS2 hwX hVc with ⟨a, ha, s, hs, hw⟩ | ⟨y₂, hy₂, -⟩
  swap
  · rw [hgraph] at hy₂
    exact absurd hy₂ (by simp)
  have hιy : (ι : G) = ((y * a * y⁻¹) * (y * s * y⁻¹)) * y := by
    have : (ι : G) = y * (a * s) := by rw [← hw]; group
    rw [this]
    group
  have hu : (y * a * y⁻¹) * (y * s * y⁻¹) ∈ d.QS :=
    d.mem_QS_iff.2 ⟨y * a * y⁻¹, d.conj_mem_Q hyX ha, y * s * y⁻¹, d.conj_mem_S hyX hs.1, rfl⟩
  obtain ⟨s₂, -, x, hx, hcj⟩ := c.act_of_involution hα h hP hQ hS2 hc Kind.unitary hyX hyact hι2G
    ⟨_, hu, hιy⟩
  refine ⟨x, hx, ?_⟩
  rw [← hcj]
  unfold cj
  calc s₂⁻¹ * (ι : G) * s₂ * (s₂⁻¹ * (ι : G) * s₂) = s₂⁻¹ * ((ι : G) * (ι : G)) * s₂ := by group
    _ = 1 := by rw [hι2G]; group

end CFSG.OddStandard.ChengHeld
