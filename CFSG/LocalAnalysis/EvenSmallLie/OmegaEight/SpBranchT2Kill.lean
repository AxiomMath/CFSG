module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchT2Check
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Kill

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]

@[expose] def CodeIso.copy {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul)
    {N' : ℕ} {mul' : ℕ → ℕ → ℕ} (hN : N = N') (hmul : ∀ a b, mul a b = mul' a b) :
    CodeIso H N' mul' where
  f := Φ.f
  lt h := hN ▸ Φ.lt h
  inj := Φ.inj
  surj c hc := Φ.surj c (hN ▸ hc)
  map_mul x y := (Φ.map_mul x y).trans (hmul _ _)

theorem l2SurvAct_all
    {j : ℕ} (hj : j < 8) : ∃ I cents recs, l2SurvActOK j I cents recs = true := by
  interval_cases j
  · exact l2SurvAct_check_0
  · exact l2SurvAct_check_1
  · exact l2SurvAct_check_2
  · exact l2SurvAct_check_3
  · exact l2SurvAct_check_4
  · exact l2SurvAct_check_5
  · exact l2SurvAct_check_6
  · exact l2SurvAct_check_7

theorem l2K_all
    {j : ℕ} (hj : j < 8) :
    ∃ gs L, l2KOK j gs L = true := by
  interval_cases j
  · exact l2K_check_0
  · exact l2K_check_1
  · exact l2K_check_2
  · exact l2K_check_3
  · exact l2K_check_4
  · exact l2K_check_5
  · exact l2K_check_6
  · exact l2K_check_7

theorem l2TH_all (ε : Eps) :
    ∃ gs L, l2THOK (epsIdx ε) gs L = true := by
  cases ε
  · exact l2TH_check_0
  · exact l2TH_check_1

namespace Hyp

variable {ε : Eps} {t : G} {TH E₁ S : Subgroup G}

theorem false_of_canon
    [Finite G]
    (hH : Hyp ε t TH E₁ S) (hGt : ∀ K : Subgroup G, K.index = 2 → t ∈ K) {j : ℕ} (hj : j < 8)
    (e : S ≃* SModel) (hte : (e ⟨t, hH.t_mem_S⟩).code = tCode ε)
    {T₁ : Subgroup G} (hT₁p : IsPGroup 2 T₁) (hST : S ≤ T₁)
    (Φ : CodeIso T₁ 131072 (t1Mul (s2F j) (s2Z j)))
    (hΦS : ∀ (g : G) (hg : g ∈ S), Φ.f ⟨g, hST hg⟩ = (e ⟨g, hg⟩).code)
    (hG₁ : Gen (t1Mul (s2F j) (s2Z j)) t1Gens 131072)
    (hkill1 : t1Kill (s2K j) (s2M j) (s2Z j) false sMarked = true) {vec : Array ℕ}
    (hι : IotaFacts (t1Mul (s2F j) (s2Z j))
      (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j [])) vec)
    {f : ℕ × ℕ × ℕ × ℕ} (hf : f ∈ s2Canon.getD j []) {y : G}
    (hyN : y ∈ normalizer (T₁ : Set G)) (hyT : y ∉ T₁) (hy2 : y * y ∈ T₁)
    (hyS : y ∉ normalizer (S : Set G))
    (hSp : ∀ g : T₁, y⁻¹ * g * y ∈ S ↔ s2InSp vec (Φ.f g) = true)
    (hact : ∀ g : T₁, Φ.f (conjEquiv hyN g) = s2B (t1Mul (s2F j) (s2Z j))
      (s2IotaTab (t1Mul (s2F j) (s2Z j)) (s2Iota.getD j [])) (sFm f.1 f.2.1) f.2.2.1 (Φ.f g))
    (hv : Φ.f ⟨y * y, hy2⟩ = f.2.2.2 ∨
      Φ.f ⟨y * y, hy2⟩ = t1Mul (s2F j) (s2Z j) f.2.2.2 24) :
    False := by
  obtain ⟨I, cents, recs, hsa⟩ := l2SurvAct_all hj
  unfold l2SurvActOK at hsa
  rw [Bool.and_eq_true, List.all_eq_true] at hsa
  have hk2 := hsa.2 f hf
  rw [Bool.and_eq_true] at hk2
  have hk : l2ActOK j f.1 f.2.1 f.2.2.1 (Φ.f ⟨y * y, hy2⟩) recs = true := by
    rcases hv with h | h
    · rw [h]
      exact hk2.1
    · rw [h]
      exact hk2.2
  obtain ⟨h16, hB, hv0⟩ := l2Act_of hsa.1 hk
  exact hH.false_of_L2 hGt e hte hT₁p hST Φ hΦS hG₁ hkill1 hι hyN hyT hy2 hyS hSp hact
    (l2TH_all ε) hsa.1 (l2K_all hj) h16 hB hv0

end Hyp

end CFSG.EvenSmallLie.OmegaEight.SpBranch
