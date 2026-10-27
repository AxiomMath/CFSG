module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CBBack
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CCSyl
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CCFra
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CCSpl

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem y7c_odd_false (c : Ctx7 G L) (hb : B7Std c) (r : ℕ) (z : y7cGam c.s) (hr : r.Prime)
    (hr2 : r ≠ 2) (hz : z ∈ Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s)))
    (hzc : ∀ n ∈ Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s)), z * n = n * z)
    (hzp : IsPGroup r ↥(Subgroup.zpowers z))
    (hzf : ∀ m : ↥(M3 c.s), y7cRhoC c hb z m = m → m = 1) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨g', rfl⟩ := y7cPi_surjective c.s z
  have hK : ∀ x : G, x ∈ K7 c.s ↔
      ∃ h : x ∈ y7cX c.s, y7cPi c.s ⟨x, h⟩ ∈
        Subgroup.normalClosure (y7cJC c : Set (y7cGam c.s)) := by
    intro x
    rw [y7c_K7_eq_pre c hb, mem_y7cPre]
  have hHM : c.s.H ⊓ M3 c.s = c.s.fr.F := hb.fact54.1.2.1
  have hconj : conjClass (M3 c.s) c.s.t = c.s.tCoset c.s.fr.F := hb.fact54.1.2.2.1
  have hFM : c.s.fr.F ≤ M3 c.s := by
    rw [← hHM]
    exact inf_le_right
  have hcent : ∀ m ∈ M3 c.s, c.s.t * m * c.s.t⁻¹ = m → m ∈ c.s.fr.F := by
    intro m hm hcomm
    have hmH : m ∈ c.s.H := by
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff.mp hh]
      exact mul_inv_eq_iff_eq_mul.mp hcomm
    rw [← hHM]
    exact Subgroup.mem_inf.mpr ⟨hmH, hm⟩
  have hI : ∀ m ∈ M3 c.s, c.s.t * m * c.s.t⁻¹ = m →
      ∃ u ∈ M3 c.s, m * c.s.t = u * c.s.t * u⁻¹ := by
    intro m hm hcomm
    have h3 : m * c.s.t ∈ c.s.tCoset c.s.fr.F := ⟨m, hcent m hm hcomm, rfl⟩
    rw [← hconj] at h3
    obtain ⟨u, hu, hu'⟩ := h3
    exact ⟨u, hu, hu'⟩
  have hM2 : ∀ m ∈ M3 c.s, m ^ 2 = 1 :=
    fun m hm => (y7c_M3_elem c hb.hH hb.fact57).2 m hm
  have hMK : ∀ k ∈ K7 c.s, ∀ m ∈ M3 c.s, k * m * k⁻¹ ∈ M3 c.s :=
    fun k hk m hm => (Subgroup.mem_normalizer_iff.mp (y7c_K7_le_X c hb hk) m).mp hm
  have htM : ∀ m ∈ M3 c.s, c.s.t * m * c.s.t⁻¹ ∈ M3 c.s :=
    fun m hm => (Subgroup.mem_normalizer_iff.mp (y7c_t_mem_X c hb) m).mp hm
  have htK : ∀ k ∈ K7 c.s, c.s.t * k * c.s.t⁻¹ ∈ K7 c.s :=
    y7c_K7_norm c hb c.s.t (y7c_t_mem_X c hb)
  have hg₀K : (g' : G) ∈ K7 c.s := (hK g').mpr ⟨g'.2, hz⟩
  have hg₀c : ∀ k ∈ K7 c.s, ⁅k, (g' : G)⁆ ∈ M3 c.s := by
    intro k hk
    obtain ⟨hkX, hkN⟩ := (hK k).mp hk
    have h1 : y7cPi c.s ⁅(⟨k, hkX⟩ : ↥(y7cX c.s)), g'⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (hzc _ hkN).symm
    have h2 := (y7cPi_eq_one_iff c.s _).mp h1
    simpa [commutatorElement_def] using h2
  have hg₀r : ∃ a : ℕ, (g' : G) ^ (r ^ a) ∈ M3 c.s := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hzp) ⟨y7cPi c.s g', Subgroup.mem_zpowers _⟩
    rw [Subgroup.orderOf_mk] at ha
    refine ⟨a, ?_⟩
    have h1 : (y7cPi c.s g') ^ (r ^ a) = 1 := by
      rw [← ha]
      exact pow_orderOf_eq_one _
    have h2 : y7cPi c.s (g' ^ (r ^ a)) = 1 := by
      rw [map_pow]
      exact h1
    simpa using (y7cPi_eq_one_iff c.s _).mp h2
  have hg₀f : ∀ m ∈ M3 c.s, (g' : G) * m * (g' : G)⁻¹ = m → m = 1 := by
    intro m hm hfix
    have h := hzf ⟨m, hm⟩ (Subtype.ext
      ((y7cRho_apply c.s (y7c_M3_comm c hb) g' ⟨m, hm⟩).trans hfix))
    simpa using congrArg Subtype.val h
  obtain ⟨K0, Q, -, hK0K, hK0n, hK0c, hK0Q, hSyl, hQt, hQM, hQ1⟩ :=
    y7c_odd_Q (M3 c.s) (K7 c.s) c.s.t (g' : G) r hr2 hM2 (y7c_M3_comm c hb) hMK
      (y7c_M3_le_K7 c hb) (y7c_t_sq c.s) htM htK hI hg₀K hg₀c hg₀r hg₀f
  have hQK0 : Q ≤ K0 := hSyl.1
  have hFr : ∀ k ∈ K7 c.s, ∃ m ∈ M3 c.s, ∃ n ∈ K7 c.s,
      (∀ q ∈ Q, n * q * n⁻¹ ∈ Q) ∧ k = m * n := by
    intro k hk
    obtain ⟨x, hx, n, hn, hnQ, rfl⟩ := y7c_frattini r (K7 c.s) K0 Q hK0K hK0n hSyl k hk
    obtain ⟨m, hm, q, hq, rfl⟩ := hK0Q x hx
    refine ⟨m, hm, q * n, (K7 c.s).mul_mem (hK0K (hQK0 hq)) hn, ?_, by rw [mul_assoc]⟩
    intro q' hq'
    have h1 : q * (n * q' * n⁻¹) * q⁻¹ ∈ Q :=
      Q.mul_mem (Q.mul_mem hq (hnQ q' hq')) (Q.inv_mem hq)
    have h2 : q * n * q' * (q * n)⁻¹ = q * (n * q' * n⁻¹) * q⁻¹ := by group
    rw [h2]
    exact h1
  have hsplit : SplitsOver (JF c.s) c.s.fr.F :=
    y7c_odd_splits (M3 c.s) (K7 c.s) (JF c.s) c.s.fr.F Q c.s.t hMK (y7c_M3_le_K7 c hb)
      (y7c_t_sq c.s) htM htK hFM (y7c_F_le_JF hb.hH) (y7c_JF_le_K7 c.s) (y7c_JF_comm_t c.s)
      hcent (hQK0.trans hK0K) hQ1 (fun q hq k hk => hK0c q (hQK0 hq) k hk) hQt hQM hFr
  have h5c : ¬ SplitsOver (normIn L c.s.fr.F) c.s.fr.F := hb.hH.hLF.fact18.2.2.2.2.2.1
  rw [y7c_NLF_eq_JF hb.hH] at h5c
  exact h5c hsplit

end CFSG.OddStandard.HigherRank.YamadaG23
