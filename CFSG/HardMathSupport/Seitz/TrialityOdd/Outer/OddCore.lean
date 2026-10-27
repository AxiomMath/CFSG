module

public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddClose
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddDickson
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Outer.OddEntry

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.SEITZ7 CFSG.RankThree.PartOne.SEITZ8
  CFSG.RankThree.PartOne.SEITZ3 CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem

variable {K : Type} [Field K]

section Prelim


structure D4SetupO (σ δ : K →+* K) (k : Subfield K) (F0 : Subfield (fixedField σ)) (d : ℕ) :
    Prop where
  hσ3 : ∀ c, σ (σ (σ c)) = c
  hcomm : ∀ c, δ (σ c) = σ (δ c)
  hfix : ∀ c ∈ k, δ c = c
  rat : Rat3 σ k
  hF0 : ∀ c : fixedField σ, c ∈ F0 ↔ (c : K) ∈ k
  prime : d.Prime
  ne2 : d ≠ 2
  card : Nat.card (fixedField σ) = Nat.card F0 ^ d
  span : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a}
  stab : ∀ g : twistedGroup σ, ∃ g' : twistedGroup σ,
    ((g' : adjointGroup d4 K) : ModGL d4 K) =
      Units.map (entrywiseHom δ) ((g : adjointGroup d4 K) : ModGL d4 K)

theorem exists_ne_zero_one_of_three_le {L : Type*} [Field L] [Finite L] (h3 : 3 ≤ Nat.card L) :
    ∃ s : L, s ≠ 0 ∧ s ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun x : L => decide (x = 0)) := by
    intro x y hxy
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · rw [hx, hy]
      · simp [hx, hy] at hxy
    · by_cases hy : y = 0
      · simp [hx, hy] at hxy
      · rw [hcon x hx, hcon y hy]
  have := Nat.card_le_card_of_injective _ hinj
  simp at this
  omega

theorem slShort_upper_xA_odd {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (c : K) :
    ((slShort σ hσ (sl2Upper c) : twistedGroup σ) : adjointGroup d4 K) =
      xd 0 c * xd 1 (σ c) * xd 3 (σ (σ c)) := by
  rw [slShort_upper]
  simp only [xOuter, ← d4Root_dict.2.2.1, ← d4Root_dict.2.2.2.1, ← d4Root_dict.2.2.2.2.1]

theorem slShort_lower_xAm_odd {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (c : K) :
    ((slShort σ hσ (sl2Lower c) : twistedGroup σ) : adjointGroup d4 K) =
      xd 4 c * xd 6 (σ c) * xd 10 (σ (σ c)) := by
  rw [slShort_lower]
  simp only [xOuter, ← d4Root_dict.2.2.2.2.2.1, ← d4Root_dict.2.2.2.2.2.2.1,
    ← d4Root_dict.2.2.2.2.2.2.2]

theorem mem_XA_odd {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c) (g : adjointGroup d4 K) :
    g ∈ twistedRootSubgroupD4 σ (rt 1) ↔ ∃ a, g = xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a)) := by
  rw [mem_twistedRootSubgroupD4_iff_of_orbit hσ (SEITZ8.isRoot_d4 (by norm_num)) proj_dict.2.1
    rho_ne_dict.1 g]
  simp only [xOrbit_0]

end Prelim

section Rational

variable {σ δ : K →+* K} {k : Subfield K}

theorem entrywise_xd22 (δ : K →+* K) (c : K) :
    Units.map (entrywiseHom δ) ((xe 22 c : adjointGroup d4 K) : ModGL d4 K) =
      ((xe 22 (δ c) : adjointGroup d4 K) : ModGL d4 K) := by
  obtain ⟨-, εw, hεw, hW⟩ := Wt_rootMove_B (K := K)
  have h1 : (xe 22 c : adjointGroup d4 K) = Wt * xd 2 (εw * c) * Wt⁻¹ := by
    rw [hW, ← mul_assoc, hεw.sq, one_mul]
  have h2 : (xe 22 (δ c) : adjointGroup d4 K) = Wt * xd 2 (εw * δ c) * Wt⁻¹ := by
    rw [hW, ← mul_assoc, hεw.sq, one_mul]
  have hδε : δ εw = εw := by rcases hεw with rfl | rfl <;> simp
  rw [h1, h2, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul,
    Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv, entrywise_Wt,
    show xd 2 (εw * c) = xe 2 (εw * c) from rfl, show xd 2 (εw * δ c) = xe 2 (εw * δ c) from rfl,
    entrywise_xe_simple δ (nd 2) d4Root_simple_2, map_mul, hδε]

theorem psiB_upper_mem_Rg_odd {σ δ : K →+* K} {k : Subfield K} {F0 : Subfield (fixedField σ)}
    {d : ℕ} (S : D4SetupO σ δ k F0 d) {c : fixedField σ} (hc : c ∈ F0) :
    psiB σ S.hσ3 (sl2Upper c) ∈ Rg σ δ := by
  obtain ⟨ε, hε, hu⟩ := psiB_upper_odd (K := K) S.hσ3
  rw [mem_Rg, hu c]
  have hδε : δ ε = ε := by rcases hε with rfl | rfl <;> simp
  show Units.map (entrywiseHom δ) ((xe 22 (ε * (c : K)) : adjointGroup d4 K) : ModGL d4 K) = _
  rw [entrywise_xd22, map_mul, hδε, S.hfix _ ((S.hF0 c).1 hc)]

theorem spanHyp_Rδ_odd (hσ : ∀ c, σ (σ (σ c)) = c) (hcomm : ∀ c, δ (σ c) = σ (δ c))
    (hk : ∀ c ∈ k, δ c = c) (hRat : Rat3 σ k) : SpanHyp σ k (Rδ σ δ) := by
  refine ⟨hRat, fun a ha => ?_, fun a ha => ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · have := (slShort σ hσ (sl2Upper a)).2
      rw [slShort_upper_xA_odd hσ] at this
      exact this
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul,
        entrywise_xe_simple δ (nd 0) d4Root_simple_0, entrywise_xe_simple δ (nd 1) d4Root_simple_1,
        entrywise_xe_simple δ (nd 3) d4Root_simple_3, hk a ha, hcomm, hk a ha, hcomm, hcomm,
        hk a ha]
  · refine ⟨?_, ?_⟩
    · have := (slShort σ hσ (sl2Lower a)).2
      rw [slShort_lower_xAm_odd hσ] at this
      exact this
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul,
        entrywise_xe_neg δ (nd 0) d4Root_neg_0, entrywise_xe_neg δ (nd 1) d4Root_neg_1,
        entrywise_xe_neg δ (nd 3) d4Root_neg_3, hk a ha, hcomm, hk a ha, hcomm, hcomm,
        hk a ha]
  · refine ⟨xe_mem_twistedGroup hσ (by norm_num) (by decide) (map_one σ), ?_⟩
    rw [entrywise_xe_simple δ (nd 2) d4Root_simple_2, map_one]
  · refine ⟨xe_mem_twistedGroup hσ (by norm_num) (by decide) (map_one σ), ?_⟩
    rw [entrywise_xe_neg δ (nd 2) d4Root_neg_2, map_one]
  · refine ⟨?_, entrywise_weylElement δ (nd 2)⟩
    have h := (nHat σ (ng 0)).2
    rw [nHat_val, nHatE_zero] at h
    exact h
  · refine ⟨?_, ?_⟩
    · have h := (nHat σ (ng 1)).2
      rw [nHat_val, nHatE_one] at h
      exact h
    rw [show ((weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) :
      adjointGroup d4 K) : ModGL d4 K) = (weylElement d4 K (nd 0) : ModGL d4 K) *
        (weylElement d4 K (nd 1) : ModGL d4 K) * (weylElement d4 K (nd 3) : ModGL d4 K) from rfl,
      map_mul, map_mul, entrywise_weylElement, entrywise_weylElement, entrywise_weylElement]

end Rational

section Main

variable {σ δ : K →+* K}

theorem eq_top_of_long_odd (hσ : ∀ c, σ (σ (σ c)) = c) (k : Subfield K)
    {H : Subgroup (twistedGroup σ)} (hn0 : nHat σ (ng 0) ∈ H) (hn1 : nHat σ (ng 1) ∈ H)
    (hlong : ∀ c : fixedField σ, psiB σ hσ (sl2Upper c) ∈ H)
    (hA : ∀ a ∈ k, slShort σ hσ (sl2Upper a) ∈ H)
    (s : K) (hsσ : σ s = s) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hspan : ∀ x : K, x ∈ AddSubgroup.closure {y | ∃ e : K, σ e = e ∧ ∃ a ∈ k, y = e * a}) :
    H = ⊤ := by
  set Hs : Subgroup (adjointGroup d4 K) := H.map (twistedGroup σ).subtype with hHs
  have hS : ∀ y : twistedGroup σ, (y : adjointGroup d4 K) ∈ Hs ↔ y ∈ H := fun y =>
    Subgroup.mem_map_iff_mem (twistedGroup σ).subtype_injective
  have hn0' : weylElement d4 K (nd 2) ∈ Hs := by
    have := (hS _).2 hn0
    rwa [nHat_val, nHatE_zero] at this
  have hn1' : weylElement d4 K (nd 0) * weylElement d4 K (nd 1) * weylElement d4 K (nd 3) ∈ Hs := by
    have := (hS _).2 hn1
    rwa [nHat_val, nHatE_one] at this
  have hF : twistC .D4 K σ (weylElement d4 K (nd 2)) = weylElement d4 K (nd 2) := by
    have h := (mem_twistFixed ..).1 (twistedGroup_le_twistFixed σ (nHat σ (ng 0)).2)
    rwa [nHat_val, nHatE_zero] at h
  have hH : ∀ c : K, σ c = c → xd 22 c ∈ Hs := fun c hc => by
    obtain ⟨ε, hε, hu⟩ := psiB_upper_odd (K := K) hσ
    have hεc : σ (ε * c) = ε * c := pmone_mem_fixed σ hε hc
    have := (hS _).2 (hlong ⟨ε * c, hεc⟩)
    rw [hu] at this
    simpa [← mul_assoc, hε.sq] using this
  have hA' : ∀ a ∈ k, xd 0 a * xd 1 (σ a) * xd 3 (σ (σ a)) ∈ Hs := fun a ha => by
    have := (hS _).2 (hA a ha)
    rwa [slShort_upper_xA_odd hσ a] at this
  obtain ⟨hB, hAall⟩ := long_closing_odd σ hσ k Hs hn0' hn1' hF hH hA' s hsσ hs0 hs1 hspan
  apply eq_top_of_simple_tw hσ hn0 hn1
  · intro y hy
    have hy' : (y : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (rt 0) := by
      rw [rt0_single]
      exact Subgroup.mem_subgroupOf.1 hy
    obtain ⟨c, hcσ, hyc⟩ := (mem_XB hσ _).1 hy'
    rw [← hS, hyc]
    exact hB c hcσ
  · intro y hy
    have hy' : (y : adjointGroup d4 K) ∈ twistedRootSubgroupD4 σ (rt 1) := by
      rw [rt1_single]
      exact Subgroup.mem_subgroupOf.1 hy
    obtain ⟨a, hya⟩ := (mem_XA_odd hσ _).1 hy'
    rw [← hS, hya]
    exact hAall a

variable {k : Subfield K} {F0 : Subfield (fixedField σ)} {d : ℕ}

theorem eq_of_columns {a b : adjointGroup d4 K}
    (h : ∀ x : Label d4, a • (Finsupp.single x (1 : K) : RootModule d4 K) =
      b • (Finsupp.single x (1 : K) : RootModule d4 K)) : a = b := by
  have hall : ∀ v : RootModule d4 K, a • v = b • v := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [smul_add, smul_add, hx, hy]
    | single x r =>
      have h1 : (Finsupp.single x r : RootModule d4 K) = r • Finsupp.single x (1 : K) := by simp
      rw [h1, smul_smul_comm', smul_smul_comm', h x]
  refine Subtype.ext (Units.ext (LinearMap.ext fun v => ?_))
  exact hall v

theorem exists_bad_entry_odd {r : ℕ} [CharP K r] (hr3 : 3 ≤ r) (S : D4SetupO σ δ k F0 d)
    (g : twistedGroup σ) (hg : g ∉ Rg σ δ) :
    ∃ r ∈ Rδ σ δ, ∃ r' ∈ Rδ σ δ,
      coordAt (d4Root 23) ((r * (g : adjointGroup d4 K) * r') • (rv 22 : RootModule d4 K)) ∉ k := by
  have hSpan := spanHyp_Rδ_odd S.hσ3 S.hcomm S.hfix S.rat
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have : (r : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff K r 2).1 (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  by_contra hcon
  push Not at hcon
  have hrat := fun b => ratAll_of_hcon hSpan h2 (g : adjointGroup d4 K) hcon b
  obtain ⟨g', hg'⟩ := S.stab g
  have hcols : ∀ b : Label d4, (g' : adjointGroup d4 K) •
      (Finsupp.single b (1 : K) : RootModule d4 K) =
        Finsupp.mapRange δ δ.map_zero ((g : adjointGroup d4 K) •
          (Finsupp.single b (1 : K) : RootModule d4 K)) := by
    intro b
    rw [smul_eq_end, hg']
    show entrywise δ _ (Finsupp.single b 1) = _
    rw [entrywise_single]
    rfl
  have hcols' : ∀ b : Label d4, (g' : adjointGroup d4 K) •
      (Finsupp.single b (1 : K) : RootModule d4 K) =
        (g : adjointGroup d4 K) • (Finsupp.single b (1 : K) : RootModule d4 K) := by
    intro b
    rw [hcols b]
    refine Finsupp.ext fun l => ?_
    rw [Finsupp.mapRange_apply]
    exact S.hfix _ (hrat b l)
  have heq : (g' : adjointGroup d4 K) = g := eq_of_columns hcols'
  apply hg
  rw [mem_Rg, ← hg', heq]

theorem long_full_odd {r : ℕ} [Finite K] [CharP K r] (hr3 : 3 ≤ r)
    (S : D4SetupO σ δ k F0 d) (g : twistedGroup σ) (hg : g ∉ Rg σ δ) :
    ∀ c : fixedField σ, psiB σ S.hσ3 (sl2Upper c) ∈
      Subgroup.closure ((Rg σ δ : Set (twistedGroup σ)) ∪
        (((Rg σ δ).map (MulAut.conj g).toMonoidHom : Subgroup (twistedGroup σ)) :
          Set (twistedGroup σ))) := by
  obtain ⟨r₁, hr, r', hr', hbad⟩ := exists_bad_entry_odd hr3 S g hg
  set H : Subgroup (twistedGroup σ) := Subgroup.closure ((Rg σ δ : Set (twistedGroup σ)) ∪
    (((Rg σ δ).map (MulAut.conj g).toMonoidHom : Subgroup (twistedGroup σ)) :
      Set (twistedGroup σ))) with hH
  have hRH : Rg σ δ ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hRgH : (Rg σ δ).map (MulAut.conj g).toMonoidHom ≤ H := fun x hx =>
    Subgroup.subset_closure (Or.inr hx)
  set ρ : twistedGroup σ := ⟨r₁, hr.1⟩ with hρdef
  set ρ' : twistedGroup σ := ⟨r', hr'.1⟩ with hρ'def
  have hρ : ρ ∈ Rg σ δ := hr
  have hρ' : ρ' ∈ Rg σ δ := hr'
  have hcoe : ((ρ * g * ρ' : twistedGroup σ) : adjointGroup d4 K) =
      r₁ * (g : adjointGroup d4 K) * r' := rfl
  have hne0 : coordAt (d4Root 23) (((ρ * g * ρ' : twistedGroup σ) : adjointGroup d4 K) •
      (rv 22 : RootModule d4 K)) ≠ 0 := by
    rw [hcoe]
    intro h
    exact hbad (h ▸ k.zero_mem)
  obtain ⟨ψ, μ₁, μ₂, h1, h2, ⟨ε, hε, hmu⟩, hu, hl⟩ := bigCell_tw_odd S.hσ3 (ρ * g * ρ') hne0
  set lam : fixedField σ := ⟨ε * ((μ₁ * μ₂ : fixedField σ) : K), by
    show σ (ε * ((μ₁ * μ₂ : fixedField σ) : K)) = _
    rw [map_mul, pmone_sigma hε]
    exact congrArg (ε * ·) (μ₁ * μ₂).2⟩ with hlamdef
  have hlam_eq : (lam : K) = coordAt (d4Root 23)
      (((ρ * g * ρ' : twistedGroup σ) : adjointGroup d4 K) • (rv 22 : RootModule d4 K)) := by
    show ε * (((μ₁ * μ₂ : fixedField σ) : K)) = _
    rw [show (((μ₁ * μ₂ : fixedField σ) : K)) = (μ₁ : K) * (μ₂ : K) from rfl, hmu,
      ← mul_assoc, hε.sq, one_mul]
  have hlam : lam ∉ F0 := by
    intro hmem
    have h3 := (S.hF0 _).1 hmem
    rw [hlam_eq, hcoe] at h3
    exact hbad h3
  have hψ : ∀ c ∈ F0, psiB σ S.hσ3 (sl2Upper c) ∈ H := fun c hc =>
    hRH (psiB_upper_mem_Rg_odd S hc)
  have hψ2 : ∀ c ∈ F0, (ρ * g * ρ') * psiB σ S.hσ3 (sl2Upper c) * (ρ * g * ρ')⁻¹ ∈ H := by
    intro c hc
    have h5 : ρ' * psiB σ S.hσ3 (sl2Upper c) * ρ'⁻¹ ∈ Rg σ δ :=
      (Rg σ δ).mul_mem ((Rg σ δ).mul_mem hρ' (psiB_upper_mem_Rg_odd S hc)) ((Rg σ δ).inv_mem hρ')
    have h6 : g * (ρ' * psiB σ S.hσ3 (sl2Upper c) * ρ'⁻¹) * g⁻¹ ∈
        (Rg σ δ).map (MulAut.conj g).toMonoidHom := ⟨_, h5, by simp [MulAut.conj_apply]⟩
    have h7 : ρ * (g * (ρ' * psiB σ S.hσ3 (sl2Upper c) * ρ'⁻¹) * g⁻¹) * ρ⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (hRH hρ) (hRgH h6)) (H.inv_mem (hRH hρ))
    have e : (ρ * g * ρ') * psiB σ S.hσ3 (sl2Upper c) * (ρ * g * ρ')⁻¹ =
        ρ * (g * (ρ' * psiB σ S.hσ3 (sl2Upper c) * ρ'⁻¹) * g⁻¹) * ρ⁻¹ := by group
    rw [e]
    exact h7
  exact full_h_of_pair_odd hr3 S.hσ3 F0 S.prime S.ne2 S.card (ρ * g * ρ') hψ hψ2 lam hlam_eq hlam

theorem closure_eq_top_odd {r : ℕ} [Finite K] [CharP K r]
    (hr3 : 3 ≤ r) (S : D4SetupO σ δ k F0 d) (g : twistedGroup σ) (hg : g ∉ Rg σ δ) :
    Subgroup.closure ((Rg σ δ : Set (twistedGroup σ)) ∪
      (((Rg σ δ).map (MulAut.conj g).toMonoidHom : Subgroup (twistedGroup σ)) :
        Set (twistedGroup σ))) = ⊤ := by
  set H : Subgroup (twistedGroup σ) := Subgroup.closure ((Rg σ δ : Set (twistedGroup σ)) ∪
    (((Rg σ δ).map (MulAut.conj g).toMonoidHom : Subgroup (twistedGroup σ)) :
      Set (twistedGroup σ))) with hH
  have hRH : Rg σ δ ≤ H := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hSp := spanHyp_Rδ_odd S.hσ3 S.hcomm S.hfix S.rat
  have hn0 : nHat σ (ng 0) ∈ H := hRH (by
    rw [mem_Rg, nHat_val, nHatE_zero]
    exact hSp.n0.2)
  have hn1 : nHat σ (ng 1) ∈ H := hRH (by
    rw [mem_Rg, nHat_val, nHatE_one]
    exact hSp.n1.2)
  have hA : ∀ a ∈ k, slShort σ S.hσ3 (sl2Upper a) ∈ H := fun a ha => hRH (by
    rw [mem_Rg, slShort_upper_xA_odd S.hσ3 a]
    exact (hSp.A a ha).2)
  have hcard : 3 ≤ Nat.card (fixedField σ) := by
    rw [S.card]
    have h2 : 2 ≤ Nat.card F0 := by
      have : 1 < Nat.card F0 := Finite.one_lt_card
      omega
    have hd : 3 ≤ d := by
      have := S.prime.two_le
      have := S.ne2
      omega
    calc 3 ≤ 2 ^ d := by
          calc 3 ≤ 2 ^ 2 := by norm_num
            _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ Nat.card F0 ^ d := Nat.pow_le_pow_left h2 d
  have : Finite (fixedField σ) := Subtype.finite
  obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_one_of_three_le (L := fixedField σ) hcard
  exact eq_top_of_long_odd S.hσ3 k hn0 hn1 (long_full_odd hr3 S g hg) hA ((s : fixedField σ) : K)
    (s : fixedField σ).2 (fun h => hs0 (Subtype.ext h)) (fun h => hs1 (Subtype.ext h)) S.span

end Main

end CFSG.HardMathSupport.Seitz.TrialityOdd
