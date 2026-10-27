module

public import CFSG.ClassicalInvolution.Asc77.AscT7L6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.Disconnected

variable {p : ℕ} [Fact p.Prime]

namespace T7L

variable {f : ℕ} {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

omit [Finite X] in
theorem map_centralizer_le {K : Type*} [Group K] (ψ : K →* X) (s : K) :
    (Subgroup.centralizer ({s} : Set K)).map ψ ≤ Subgroup.centralizer ({ψ s} : Set X) := by
  rintro _ ⟨c, hc, rfl⟩
  have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
  exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [← map_mul, hc', map_mul])

theorem e4_gen_of_model (hgen : E4TwinGen p) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΦ : HypOmegaMod p f Φ) {tg : StatedLieTag} {k ee : ℕ} (M : Ih8Model p f Φ tg k ee)
    (hE4 : (tg = .PSp ∧ k = 2) ∨ (tg = .PSL ∧ k = 4 ∧ p ^ f % 4 = 3) ∨
      (tg = .PSU ∧ k = 4 ∧ p ^ f % 4 = 1))
    {A A' : Subgroup X} {z a₀ b₀ w : X} (T : TwinSect Φ A A' z a₀ b₀ w) :
    (⊤ : Subgroup X) = Subgroup.centralizer ({z} : Set X) ⊔
      Subgroup.centralizer ({w} : Set X) ⊔ Subgroup.centralizer ({z * w} : Set X) := by
  classical
  have hG2 : tg ≠ .G2 := by
    rintro rfl
    rcases hE4 with h | h | h <;> simp at h
  have hD4 : tg ≠ .trialityD4 := by
    rintro rfl
    rcases hE4 with h | h | h <;> simp at h
  have hnpsl : ¬ (tg = .PSL ∧ k = 2) := by
    rintro ⟨rfl, rfl⟩
    rcases hE4 with h | h | h <;> simp at h
  have hee : ee = f := M.exp_eq_f hD4
  have hq' : 5 ≤ p ^ ee := by rw [hee]; exact hq
  obtain ⟨RA, RA', a, b, x, x', hRA, hRA', hRR, hcommR, hxR, hx2, hx1, hx'R, hx'2, hx'1, hxx',
    haR, hasq, hbR, hbsq, hψa, hψb, hψx, hψx'⟩ :=
    twin_lifts hp2 hq hΦ M hG2 hD4 hnpsl T.hA T.hA' T.ne T.hzA T.hzA' T.ha₀ T.hb₀ T.ha₀sq T.hb₀sq
  have hK := hgen tg k ee M.admissible hp2 hq' (by rw [hee]; exact hE4) RA (M.cls_sub hRA) RA'
    (M.cls_sub hRA') hRR hcommR x hxR hx2 hx1 x' hx'R hx'2 hx'1 hxx' a haR hasq b hbR hbsq
  have hz2 : z * z = 1 := T.hzA.sq
  have hainv : a₀⁻¹ = z * a₀ := by
    refine inv_eq_of_mul_eq_one_right ?_
    calc a₀ * (z * a₀) = (a₀ * a₀) * (a₀ * a₀) := by rw [← T.ha₀sq]; simp only [mul_assoc]
      _ = 1 := by rw [T.ha₀sq, hz2]
  have hw₂ : a₀⁻¹ * b₀ = z * (a₀ * b₀) := by rw [hainv, mul_assoc]
  have hw₁ : a₀ * b₀ = z * (a₀⁻¹ * b₀) := by
    rw [hw₂, ← mul_assoc, ← mul_assoc, hz2, one_mul]
  have hcov : Subgroup.centralizer ({a₀ * b₀} : Set X) ⊔
      Subgroup.centralizer ({a₀⁻¹ * b₀} : Set X) ≤
      Subgroup.centralizer ({w} : Set X) ⊔ Subgroup.centralizer ({z * w} : Set X) := by
    rcases T.hw with h | h
    · subst h
      rw [← hw₂]
    · subst h
      rw [← hw₁, sup_comm]
  have hcov' : Subgroup.centralizer ({a₀ * b₀} : Set X) ⊔
      Subgroup.centralizer ({a₀⁻¹ * b₀} : Set X) ≤ Subgroup.centralizer ({z} : Set X) ⊔
        Subgroup.centralizer ({w} : Set X) ⊔ Subgroup.centralizer ({z * w} : Set X) :=
    hcov.trans (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have h0 : (Subgroup.center (modelUniv tg k p ee Fact.out).K).map M.ψ ≤
      Subgroup.centralizer ({z} : Set X) := by
    have := (Subgroup.map_mono (Subgroup.center_le_centralizer ({x} : Set _))).trans
      (map_centralizer_le M.ψ x)
    rwa [hψx] at this
  have h1 : (Subgroup.centralizer ({x} : Set (modelUniv tg k p ee Fact.out).K)).map M.ψ ≤
      Subgroup.centralizer ({z} : Set X) := by
    have := map_centralizer_le M.ψ x
    rwa [hψx] at this
  have h2 : (Subgroup.centralizer ({a * b} : Set (modelUniv tg k p ee Fact.out).K)).map M.ψ ≤
      Subgroup.centralizer ({a₀ * b₀} : Set X) := by
    have := map_centralizer_le M.ψ (a * b)
    rwa [map_mul, hψa, hψb] at this
  have h3 : (Subgroup.centralizer ({a⁻¹ * b} : Set (modelUniv tg k p ee Fact.out).K)).map M.ψ ≤
      Subgroup.centralizer ({a₀⁻¹ * b₀} : Set X) := by
    have := map_centralizer_le M.ψ (a⁻¹ * b)
    rwa [map_mul, map_inv, hψa, hψb] at this
  refine (eq_top_iff.mpr ?_).symm
  intro y _
  obtain ⟨k₀, rfl⟩ := M.surj y
  have hk : k₀ ∈ (⊤ : Subgroup (modelUniv tg k p ee Fact.out).K) := Subgroup.mem_top k₀
  rw [hK] at hk
  have hmem := Subgroup.mem_map_of_mem M.ψ hk
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup] at hmem
  have hz' : Subgroup.centralizer ({z} : Set X) ≤ Subgroup.centralizer ({z} : Set X) ⊔
      Subgroup.centralizer ({w} : Set X) ⊔ Subgroup.centralizer ({z * w} : Set X) :=
    le_sup_left.trans le_sup_left
  exact (sup_le (h0.trans hz') (sup_le (sup_le (h1.trans hz') (h2.trans (le_sup_left.trans hcov')))
    (h3.trans (le_sup_right.trans hcov')))) hmem


theorem twinSection_gen_conj (htcf : TwinCentralFact p) (hgen : E4TwinGen p) (hp : p ≠ 2)
    (hq : 5 ≤ p ^ f) {n : ℕ} (hBelow : CITBelowU p f n) (hlt : Nat.card X < n)
    (hS : GenSection p f Φ) {A A' : Subgroup X} {z a₀ b₀ w : X}
    (T : TwinSect Φ A A' z a₀ b₀ w) :
    (⊤ : Subgroup X) = Subgroup.centralizer ({z} : Set X) ⊔ Subgroup.centralizer ({w} : Set X) ⊔
      Subgroup.centralizer ({z * w} : Set X) ∧ ConjTwinInv Φ z := by
  rcases twinSection_cases htcf hp hq hBelow hlt hS T with hconn | ⟨D, hcard, i, hE4⟩
  · have hc := twinSection_central T.hzA T.hzA' hconn hS.gen
    have hCz : Subgroup.centralizer ({z} : Set X) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hc y)
    refine ⟨?_, conjTwinInv_of_conn T.hzA T.hzA' hconn⟩
    rw [hCz, top_sup_eq, top_sup_eq]
  · let M := toModelOfGen hS.hyp D hcard hS.gen i
    have hG2 : D.tag i ≠ .G2 := by
      intro h
      rcases hE4 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at h <;> simp at h
    have hD4 : D.tag i ≠ .trialityD4 := by
      intro h
      rcases hE4 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] at h <;> simp at h
    exact ⟨e4_gen_of_model hgen hp hq hS.hyp M hE4 T,
      conjTwinInv_of_model M hG2 hD4 T.hA T.hzA⟩


end T7L

end CFSG.ClassicalInvolution.Asc77

