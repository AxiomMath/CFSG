module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralModelPairA
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTwoBSplit

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral.Model

open CFSG GorensteinWalter Subgroup CFSG.ComponentClassification.AutL2Facts

variable {F : Type} [Field F] [Finite F]

theorem right_cases {σ₀ τ : F ≃+* F} (hσ₀ : orderOf σ₀ = 2) (hτ : τ ^ 2 = 1) :
    τ = 1 ∨ τ = σ₀ := by
  by_cases h1 : τ = 1
  · exact Or.inl h1
  · right
    refine ringAut_eq_of_sq hτ (by rw [← hσ₀]; exact pow_orderOf_eq_one σ₀) h1 ?_
    intro h
    rw [h, orderOf_one] at hσ₀
    norm_num at hσ₀

omit [Finite F] in
theorem exists_pow_eq_one {P : Subgroup (PGammaL2 F)} (hP : IsPGroup 2 P) {x : PGammaL2 F}
    (hx : x ∈ P) : ∃ n : ℕ, x ^ 2 ^ n = 1 := by
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  exact ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem centralizer_cases {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PSL2 F)) {P : Subgroup (PGammaL2 F)}
    (hP : IsPGroup 2 P) {σ₀ : F ≃+* F} (hσ₀ : orderOf σ₀ = 2) {k : PGammaL2 F}
    (hkr : k.right = σ₀) (hkD : ∀ d ∈ (T : Subgroup (PSL2 F)).map (incl F), k * d = d * k)
    {c : PGammaL2 F} (hc : c ∈ P)
    (hcD : ∀ d ∈ (T : Subgroup (PSL2 F)).map (incl F), c * d = d * c) :
    c ∈ (T : Subgroup (PSL2 F)).map (incl F) ∨ c * k ∈ (T : Subgroup (PSL2 F)).map (incl F) := by
  obtain ⟨n, hn⟩ := exists_pow_eq_one hP hc
  have hσσ : σ₀ * σ₀ = 1 := by rw [← pow_two, ← hσ₀]; exact pow_orderOf_eq_one σ₀
  rcases right_cases hσ₀ (right_sq_of_commute hp hp2 hF hodd T c hn hcD) with h | h
  · exact Or.inl (mem_of_centralizes hodd T h hcD)
  · right
    refine mem_of_centralizes hodd T (by
      change c.right * k.right = 1
      rw [h, hkr, hσσ]) fun d hd => ?_
    rw [mul_assoc, hkD d hd, ← mul_assoc, hcD d hd, mul_assoc]

theorem two_model {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PSL2 F)) {P : Subgroup (PGammaL2 F)}
    (hP : IsPGroup 2 P) (hTP : (T : Subgroup (PSL2 F)).map (incl F) ≤ P) {k : PGammaL2 F}
    (hk : PairCaseTwo P ((T : Subgroup (PSL2 F)).map (incl F)) k) :
    ∃ Tbar : Subgroup (PGammaL2 F), Tbar ≤ P ∧ (T : Subgroup (PSL2 F)).map (incl F) ≤ Tbar ∧
      (∀ r ∈ P, r ^ 2 = 1 → r ∈ Tbar ∨ r * k ∈ (T : Subgroup (PSL2 F)).map (incl F)) ∧
      (∀ δ ∈ Tbar, δ ∉ (T : Subgroup (PSL2 F)).map (incl F) → δ * k ≠ k * δ) ∧
      (Nat.card ((T : Subgroup (PSL2 F)).map (incl F)) = 8 →
        ∀ r ∈ P, r ∈ Tbar ∨ r * k ∈ Tbar) ∧
      (Tbar ≠ (T : Subgroup (PSL2 F)).map (incl F) →
        ∃ m : ℕ, Nonempty (↥Tbar ≃* DihedralGroup m)) := by
  set D₀ := (T : Subgroup (PSL2 F)).map (incl F)
  obtain ⟨hkP, hkD, hkD₀, hk2, -, -⟩ := hk
  have hkk : k * k = 1 := by rw [← pow_two]; exact hk2
  have hkr : k.right ≠ 1 := fun h => hkD₀ (mem_of_centralizes hodd T h hkD)
  have hkr2 : k.right ^ 2 = 1 := by rw [← right_pow, hk2]; rfl
  have hkS : SqLeft k := sqLeft_of_involution hodd hkk hkr
  have hright : ∀ r : PGammaL2 F, r.right ^ 2 = 1 → r.right ≠ 1 → (r * k).right = 1 := by
    intro r hr2 hr1
    change r.right * k.right = 1
    rw [ringAut_eq_of_sq hr2 hkr2 hr1 hkr, ← pow_two, hkr2]
  set Tb := P ⊓ (fieldProj F).ker
  have hTb : ∀ x, x ∈ Tb ↔ x ∈ P ∧ x.right = 1 := fun _ => Iff.rfl
  have hDT : D₀ ≤ Tb := fun d hd => (hTb d).mpr ⟨hTP hd, right_of_mem_D0 T hd⟩
  refine ⟨Tb, inf_le_left, hDT, fun r hr hr2 => ?_, fun δ hδ hδD hc => ?_, fun h8 r hr => ?_,
    fun hne => tbar_dihedral hodd T (hP.to_le inf_le_left) (fun x hx => ((hTb x).mp hx).2)
      hDT hne⟩
  · by_cases hr1 : r.right = 1
    · exact Or.inl ((hTb r).mpr ⟨hr, hr1⟩)
    · right
      have hrr : r * r = 1 := by rw [← pow_two]; exact hr2
      have hr2' : r.right ^ 2 = 1 := by rw [← right_pow, hr2]; rfl
      refine (mem_D0_iff T hP hTP (mul_mem hr hkP)).mpr ⟨hright r hr2' hr1, ?_⟩
      exact (sqLeft_mul r k).mpr (iff_of_true (sqLeft_of_involution hodd hrr hr1) hkS)
  · obtain ⟨hδP, hδ1⟩ := (hTb δ).mp hδ
    have hδL := mem_pslRange_of_commute_fieldInv hp hp2 hF k hkk hkr δ.left (by
      rw [← eq_inl_of_right hδ1]; exact hc.symm)
    rw [← eq_inl_of_right hδ1] at hδL
    exact hδD ((mem_D0_iff T hP hTP hδP).mpr ((mem_pslRange_iff δ).mp hδL))
  · have hr2 : r.right ^ 2 = 1 := by
      by_contra hr2
      obtain ⟨n, hn⟩ := exists_pow_eq_one hP hr
      obtain ⟨j, hj2, hj4⟩ := exists_pow_order_four ⟨n, by rw [← right_pow, hn]; rfl⟩ hr2
      have h16 : 16 ≤ Nat.card D₀ :=
        sixteen_le_card hodd (sixteen_dvd_of_order_four hp hp2 hF hj2 hj4) T
      omega
    by_cases hr1 : r.right = 1
    · exact Or.inl ((hTb r).mpr ⟨hr, hr1⟩)
    · exact Or.inr ((hTb _).mpr ⟨mul_mem hr hkP, hright r hr2 hr1⟩)

theorem autPair_nonlinear {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PSL2 F)) {P : Subgroup (PGammaL2 F)}
    (hP : IsPGroup 2 P) (hTP : (T : Subgroup (PSL2 F)).map (incl F) ≤ P) {x₀ : PGammaL2 F}
    (hx₀ : x₀ ∈ P) (hx₀r : x₀.right ≠ 1) :
    AutPair P ((T : Subgroup (PSL2 F)).map (incl F)) := by
  set D₀ := (T : Subgroup (PSL2 F)).map (incl F)
  obtain ⟨n, hn⟩ := exists_pow_eq_one hP hx₀
  obtain ⟨j, hj2, hj1⟩ :=
    exists_pow_involution (g := x₀.right) ⟨n, by rw [← right_pow, hn]; rfl⟩ hx₀r
  set σ₀ := x₀.right ^ j
  have hσ₀ : orderOf σ₀ = 2 := orderOf_eq_prime hj2 hj1
  have hσσ : σ₀ * σ₀ = 1 := by rw [← pow_two]; exact hj2
  have hfe := even_of_orderOf_two hp hF hσ₀
  obtain ⟨k, hkr, hkk, hkS, hkD⟩ := exists_k hp hp2 hF hodd T hσ₀
  have hkD₀ : k ∉ D₀ := fun h => hj1 (by rw [← hkr]; exact right_of_mem_D0 T h)
  have hback : ∀ c ∈ P, c * k ∈ P → k ∈ P := fun c hc hck => by
    have := mul_mem (inv_mem hc) hck
    rwa [← mul_assoc, inv_mul_cancel, one_mul] at this
  have hcent : ∀ c ∈ P, (∀ d ∈ D₀, c * d = d * c) → c ∈ D₀ ∨ c * k ∈ D₀ :=
    fun c hc hcD => centralizer_cases hp hp2 hF hodd T hP hσ₀ hkr hkD hc hcD
  have hone : k ∉ P → PairCaseOne P D₀ := fun hkP c hc hcD =>
    (hcent c hc hcD).resolve_right fun h => hkP (hback c hc (hTP h))
  have hnot : PairCaseOne P D₀ → k ∉ P := fun h1 hkP => hkD₀ (h1 k hkP hkD)
  have hd : k ∉ P → ∀ y ∈ P, y.right = σ₀ → ¬ SqLeft y := by
    intro hkP y hy hyr hyS
    have hykL : y * k ∈ pGammaL2PSLRange F := (mem_pslRange_iff _).mpr ⟨by
      change y.right * k.right = 1
      rw [hyr, hkr, hσσ], (sqLeft_mul y k).mpr (iff_of_true hyS hkS)⟩
    have hyk : y * k ∈ D₀ := mem_of_normalizes hp hp2 hF hodd hfe T hykL fun d hd => by
      have h := conj_mem_of_mem T P hP hTP hy d hd
      rwa [show y * k * d * (y * k)⁻¹ = y * d * y⁻¹ by
        rw [mul_assoc y k d, hkD d hd, mul_inv_rev]; group]
    exact hkP (hback y hy (hTP hyk))
  have he : k ∉ P → ∀ y ∈ P, y.right ^ 2 = 1 := by
    intro hkP y hy
    by_contra hy2
    obtain ⟨m, hm⟩ := exists_pow_eq_one hP hy
    obtain ⟨i, hi2, hi4⟩ := exists_pow_order_four ⟨m, by rw [← right_pow, hm]; rfl⟩ hy2
    have hw : (y ^ i * y ^ i).right = σ₀ := by
      rcases right_cases hσ₀ (τ := (y.right ^ i) ^ 2)
          (by rw [← pow_mul, show 2 * 2 = 4 from rfl]; exact hi4) with h | h
      · exact absurd h hi2
      · change (y ^ i).right * (y ^ i).right = σ₀
        rw [right_pow, ← pow_two, h]
    exact hd hkP _ (mul_mem (pow_mem hy i) (pow_mem hy i)) hw ((sqLeft_mul _ _).mpr Iff.rfl)
  have hD : k ∉ P → ∀ r ∈ P, r ∈ D₀ ↔ SqLeft r := by
    intro hkP r hr
    refine (mem_D0_iff T hP hTP hr).trans ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rcases right_cases hσ₀ (he hkP r hr) with h' | h'
    · exact h'
    · exact absurd h (hd hkP r hr h')
  refine ⟨fun R' hR' => gen3_model hodd (hP.to_le hR'), ?_, fun h1 r₁ hr₁ r₂ hr₂ hn₁ hn₂ => ?_,
    fun h1 E hED hE4 hEsq c hc hcE => ?_, fun h1 σ hσ hσD hσ2 => ?_,
    fun k' hk' => two_model hp hp2 hF hodd T hP hTP hk'⟩
  · by_cases hkP : k ∈ P
    · exact Or.inr ⟨k, hkP, hkD, hkD₀, by rw [pow_two]; exact hkk,
        eight_le_card hp hp2 hF hodd hfe T, hcent⟩
    · exact Or.inl (hone hkP)
  · have hkP := hnot h1
    refine (hD hkP _ (mul_mem hr₁ (inv_mem hr₂))).mpr ?_
    rw [sqLeft_mul, sqLeft_inv]
    exact iff_of_false (fun h => hn₁ ((hD hkP r₁ hr₁).mpr h))
      (fun h => hn₂ ((hD hkP r₂ hr₂).mpr h))
  · have hkP := hnot h1
    have hE1 : ∀ e ∈ E, e.right = 1 := fun e he => right_of_mem_D0 T (hED he)
    rcases right_cases hσ₀ (he hkP c hc) with h | h
    · exact hED (klein_centralizer hodd hE1 hE4 hEsq h hcE)
    · refine absurd (hback c hc (hTP (hED (klein_centralizer hodd hE1 hE4 hEsq ?_ ?_)))) hkP
      · change c.right * k.right = 1
        rw [h, hkr, hσσ]
      · intro e he
        rw [mul_assoc, hkD e (hED he), ← mul_assoc, hcE e he, mul_assoc]
  · have hkP := hnot h1
    by_cases hσ1 : σ.right = 1
    · refine card_centralizer_le_two hodd T hσ1 (fun hL => hσD ?_) hσ2
      exact (mem_D0_iff T hP hTP hσ).mpr ((mem_pslRange_iff σ).mp hL)
    · have hσσ' : σ * σ = 1 := by rw [← pow_two]; exact hσ2
      rcases right_cases hσ₀ (τ := σ.right) (by rw [← right_pow, hσ2]; rfl) with h | h
      · exact absurd h hσ1
      · exact absurd (sqLeft_of_involution hodd hσσ' hσ1) (hd hkP σ hσ h)

theorem autPair_model {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f)
    (hodd : IsOddPrimePower (Nat.card F)) (T : Sylow 2 (PSL2 F)) {P : Subgroup (PGammaL2 F)}
    (hP : IsPGroup 2 P) (hTP : (T : Subgroup (PSL2 F)).map (incl F) ≤ P) :
    AutPair P ((T : Subgroup (PSL2 F)).map (incl F)) := by
  by_cases hlin : ∀ x ∈ P, x.right = 1
  · exact autPair_linear hodd T hP hTP hlin
  · push Not at hlin
    obtain ⟨x₀, hx₀, hx₀r⟩ := hlin
    exact autPair_nonlinear hp hp2 hF hodd T hP hTP hx₀ hx₀r

end CFSG.ComponentClassification.HSDihedral.Model
