module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMUREnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMURPerfect
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKRStrict
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeKMCMain
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleRank

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace HeKMUR

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mul_pow_eq_inv_mul {u c : X} (huu : u * u = 1) (hcc : c * c = 1) (j : ℕ) :
    u * (u * c) ^ j = ((u * c) ^ j)⁻¹ * u := by
  have hux : u * (u * c) = (u * c)⁻¹ * u := by
    calc u * (u * c) = c := by rw [← mul_assoc, huu, one_mul]
      _ = (u * c)⁻¹ * u := by
        rw [mul_inv_rev, inv_mul_cancel_right, inv_eq_of_mul_eq_one_right hcc]
  generalize u * c = x at hux ⊢
  induction j with
  | zero => simp
  | succ j ih =>
    calc u * x ^ (j + 1) = (u * x ^ j) * x := by rw [pow_succ, mul_assoc]
      _ = (x ^ j)⁻¹ * (u * x) := by rw [ih, mul_assoc]
      _ = (x ^ j)⁻¹ * (x⁻¹ * u) := by rw [hux]
      _ = (x * x ^ j)⁻¹ * u := by rw [mul_inv_rev, mul_assoc]
      _ = (x ^ (j + 1))⁻¹ * u := by rw [pow_succ']

theorem false_of_commute
    {L N M : Subgroup X} {a u c w n₀ : X} (hset : HeldEndSetting X L) (ha : orderOf a = 2)
    (hLa : L ≤ centralizer ({a} : Set X))
    (hLc : IsPComponent 2 (L.subgroupOf (centralizer ({a} : Set X)))) (hu : HeldTwoA L u)
    (hMu : M ≤ centralizer ({u} : Set X))
    (hMp : IsPComponent 2 (M.subgroupOf (centralizer ({u} : Set X))))
    (hne : conjugate M a ≠ M) (hfix : gsFixedLayer (M ⊔ conjugate M a) a = gsFixedLayer L u)
    (hc : ∀ x ∈ (pPrimeCore 2 ↥M).map M.subtype, ∀ m ∈ M, x * m = m * x)
    (hw2 : orderOf w = 2) (hNw : N ≤ centralizer ({w} : Set X))
    (hNp : IsPComponent 2 (N.subgroupOf (centralizer ({w} : Set X)))) (hMN : M ≤ N)
    (hlt : (pPrimeCore 2 ↥M).index < (pPrimeCore 2 ↥N).index) (hsetN : HeldEndSetting X N)
    (hTA : HeldTwoA N n₀) (hKM : gsFixedLayer N n₀ = M) (hcn : c = n₀ * w)
    (hcu : c * u = u * c) : False := by
  obtain ⟨-, -, hstd, ⟨eN⟩, -⟩ := id hsetN
  have hn₀n₀ : n₀ * n₀ = 1 := by rw [← pow_two, ← hTA.2.1, pow_orderOf_eq_one]
  have hn₀M : n₀ ∈ M := hKM ▸ mem_gsFixedLayer_self ⟨eN⟩ hTA
  have hn₀u : n₀ * u = u * n₀ := mem_centralizer_singleton_iff.mp (hMu hn₀M)
  have huw : u * w = w * u := by
    have hw : w = n₀ * c := by rw [hcn, ← mul_assoc, hn₀n₀, one_mul]
    rw [hw]
    calc u * (n₀ * c) = (u * n₀) * c := by group
      _ = (n₀ * u) * c := by rw [hn₀u]
      _ = n₀ * (u * c) := by group
      _ = n₀ * (c * u) := by rw [hcu]
      _ = n₀ * c * u := by group
  have hwC : w ∈ centralizer (N : Set X) :=
    mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hNw hx)
  have hNu : conjugate N u = N := Single.conjugate_eq_of_mem_normalizer
    (HeZ.centralizer_le_normalizer hstd hwC hw2 (mem_centralizer_singleton_iff.mpr huw))
  have hMNu : M ≤ N ⊓ centralizer ({u} : Set X) := le_inf hMN hMu
  have hMNup : IsPComponent 2 (M.subgroupOf (N ⊓ centralizer ({u} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hMNu inf_le_right hMp
  obtain ⟨htype, -⟩ := HeKMC.type_and_pair hset ha hLa hLc hu hMu hMp hne hfix hc
  obtain ⟨n₁, hTA₁, hKM₁, hun⟩ := HeKR.exists_twoA_of_strict hsetN hu.2.1 hw2 huw hNw hNp hMu
    hMp hNu hMNu hMNup hlt htype
  rcases hun with hun | hun
  · exact false_of_isPComponent hsetN hTA₁ (by rw [hKM₁, ← hun]; exact hMp)
      (by rw [hKM₁]; exact hc)
  · exact false_of_conj_eq_mul (c := u) (d := 1) hset ha hLa hu hMu hMp hne hfix hc hsetN hw2
      hNw hTA₁ hKM₁ (fun m _ => by rw [one_mul, mul_one]) (by group) hun

end HeKMUR

end CFSG.ComponentClassification.GrSLit
