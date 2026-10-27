module

public import CFSG.ClassicalInvolution.Phan.PhanS26Fin
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.Sporadic.Schreier.J4SOrder

public section

namespace CFSG.ClassicalInvolution.PhanB3.S.Std.Q7

open CFSG.ClassicalInvolution.PhanB3.S.Std CFSG.ClassicalInvolution.PhanB3.S.Std.Q

theorem pair_equiv (hS : SigmaWitt) {a c a' c' : Vec GF49} {γ η : GF49}
    (hp : PairData m0 a c γ η) (hp' : PairData m0 a' c' γ η)
    (hrel : ∀ μ₁ μ₂ μ₃ μ₄ : GF49, Rel m0 a c μ₁ μ₂ μ₃ μ₄ ↔ Rel m0 a' c' μ₁ μ₂ μ₃ μ₄) :
    ∃ g : SigmaIso m0, g.toLinearEquiv a = a' ∧ g.toLinearEquiv c = c' := by
  have h1 : ∀ i j, bf m0 (![a, c] i) (![a, c] j) = bf m0 (![a', c'] i) (![a', c'] j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · simp [hp.ffa, hp'.ffa]
    · simp [hp.bac, hp'.bac]
    · simp [bf_comm m0 c a, bf_comm m0 c' a', hp.bac, hp'.bac]
    · simp [hp.ffc, hp'.ffc]
  have h2 : ∀ i j, her m0 (![a, c] i) (![a, c] j) = her m0 (![a', c'] i) (![a', c'] j) := by
    intro i j
    fin_cases i <;> fin_cases j
    · simp [hp.haa, hp'.haa]
    · simp [hp.hac, hp'.hac]
    · simp [her_conj_symm m0 a c, her_conj_symm m0 a' c', hp.hac, hp'.hac]
    · simp [hp.hcc, hp'.hcc]
  have h3 : ∀ cc dd : Fin 2 → GF49,
      ∑ i, cc i • (![a, c] i) + ∑ i, dd i • tauV m0 (![a, c] i) = 0 ↔
        ∑ i, cc i • (![a', c'] i) + ∑ i, dd i • tauV m0 (![a', c'] i) = 0 := by
    intro cc dd
    have := hrel (cc 0) (cc 1) (dd 0) (dd 1)
    unfold Rel at this
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    simpa only [add_assoc] using this
  obtain ⟨g, hg⟩ := hS ![a, c] ![a', c'] h1 h2 h3
  exact ⟨g, hg 0, hg 1⟩


theorem rep_pairData {reps : List ClassRep} (hT : TableOK reps) {r : ClassRep} (hr : r ∈ reps) :
    PairData m0 (toVec e0C) (toVec r.c) r.γ r.η := by
  obtain ⟨h3, hff, hη, hγ⟩ := hT.valid r hr
  have hffc : bfC r.c r.c = 0 := by
    simp only [isFFC, Bool.and_eq_true, beq_iff_eq] at hff
    exact hff.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [bf_toVec]; decide
  · rw [bf_toVec]; exact hffc
  · rw [bf_toVec]; simp [bfC, e0C, h3]
  · rw [her_toVec]; decide
  · rw [her_toVec]; exact hγ
  · rw [her_toVec]; exact hη

theorem rep_pairData' {reps : List ClassRep} (hT : TableOK reps) {r : ClassRep} (hr : r ∈ reps)
    {γ η : GF49} (hγr : r.γ = γ) (hηr : r.η = η) :
    PairData m0 (toVec e0C) (toVec r.c) γ η := by
  have := rep_pairData hT hr
  rwa [hγr, hηr] at this

theorem pair_to_rep_line (hS : SigmaWitt) {reps : List ClassRep} (hT : TableOK reps)
    {a c : Vec GF49} {γ η : GF49} (hγ : γ ∈ Fstar) (hη : η ∈ canonSet) (hη0 : η ≠ 0)
    (hp : PairData m0 a c γ η) :
    ∃ (g : SigmaIso m0) (r : ClassRep), r ∈ reps ∧ g.toLinearEquiv a = toVec e0C ∧
      g.toLinearEquiv c = toVec r.c := by
  have h2 : (2 : GF49) ≠ 0 := by decide
  have hη' : m0.τ η ≠ 0 := by
    rw [m0_tau]
    intro h
    exact hη0 (star_eq_zero.mp h)
  by_cases hN : Nvec m0 γ η a c = 0
  · have hΔ : pairDisc γ η (star η) = 0 := by
      have := disc_eq_zero_of_N h2 hη' hp hN
      rwa [m0_tau] at this
    obtain ⟨r, hr, hγr, hηr, hbr⟩ := hT.deg0 γ hγ η hη hη0 hΔ
    have hrp := rep_pairData' hT hr hγr hηr
    have hNr : Nvec m0 γ η (toVec e0C) (toVec r.c) = 0 := by
      have := (eqC_iff _ _).1 (hT.nvec0 r hr hbr)
      rw [hγr, hηr] at this
      rw [← toVec_NvecC, this, toVec_zeroC]
    obtain ⟨g, hg1, hg2⟩ := pair_equiv hS hp hrp
      (rel_iff_of_line h2 hη' hp hrp ⟨fun _ => hNr, fun _ => hN⟩)
    exact ⟨g, r, hr, hg1, hg2⟩
  · obtain ⟨r, hr, hγr, hηr, hbr⟩ := hT.regular γ hγ η hη (Or.inl hη0)
    have hrp := rep_pairData' hT hr hγr hηr
    have hNr : Nvec m0 γ η (toVec e0C) (toVec r.c) ≠ 0 := by
      have := (eqC_eq_false_iff _ _).1 (hT.nvec1 r hr hbr (by rw [hηr]; exact hη0))
      rw [hγr, hηr] at this
      rw [← toVec_NvecC]
      intro h
      exact this ((toVec_eq_zero_iff _).mp h)
    obtain ⟨g, hg1, hg2⟩ := pair_equiv hS hp hrp
      (rel_iff_of_line h2 hη' hp hrp ⟨fun h => absurd h hN, fun h => absurd h hNr⟩)
    exact ⟨g, r, hr, hg1, hg2⟩

theorem pair_to_rep_regular (hS : SigmaWitt) {reps : List ClassRep} (hT : TableOK reps)
    {a c : Vec GF49} {γ : GF49} (hγ : γ ∈ Fstar) (hγ1 : γ ≠ 1)
    (hp : PairData m0 a c γ 0) :
    ∃ (g : SigmaIso m0) (r : ClassRep), r ∈ reps ∧ g.toLinearEquiv a = toVec e0C ∧
      g.toLinearEquiv c = toVec r.c := by
  obtain ⟨r, hr, hγr, hηr, hbr⟩ := hT.regular γ hγ 0 (by decide) (Or.inr hγ1)
  have hrp := rep_pairData' hT hr hγr hηr
  have hΔ : pairDisc γ 0 (m0.τ 0) ≠ 0 := by
    simp only [pairDisc, map_zero, mul_zero, sub_zero, mul_zero]
    simp [sub_eq_zero, hγ1.symm]
  obtain ⟨g, hg1, hg2⟩ := pair_equiv hS hp hrp (rel_iff_of_regular hΔ hp hrp)
  exact ⟨g, r, hr, hg1, hg2⟩


theorem pvec_rot {a c : Vec GF49} {ℓ : GF49} (hℓ : ℓ * star ℓ = 1) :
    pvec m0 (ℓ • a) (ℓ⁻¹ • c) = ℓ • pvec m0 a c := by
  have hτ : m0.τ ℓ = ℓ⁻¹ := by rw [m0_tau]; exact eq_inv_of_mul_eq_one_right hℓ
  have hτ' : m0.τ ℓ⁻¹ = ℓ := by rw [map_inv₀, hτ, inv_inv]
  unfold pvec
  rw [tauV_smul, hτ', smul_sub]

theorem tauV_smul_rot {p : Vec GF49} {ℓ : GF49} (hℓ : ℓ * star ℓ = 1) :
    tauV m0 (ℓ • p) = ℓ⁻¹ • tauV m0 p := by
  have hτ : m0.τ ℓ = ℓ⁻¹ := by rw [m0_tau]; exact eq_inv_of_mul_eq_one_right hℓ
  rw [tauV_smul, hτ]

theorem special_rot_eigen {a c : Vec GF49} (hp : PairData m0 a c 1 0) (hp0 : pvec m0 a c ≠ 0)
    {ν : GF49} (hν : tauV m0 (pvec m0 a c) = ν • pvec m0 a c) :
    ∃ ℓ : GF49, ℓ * star ℓ = 1 ∧ ∃ ν₁ : GF49, (ν₁ = 1 ∨ ν₁ = zeta0) ∧
      PairData m0 (ℓ • a) (ℓ⁻¹ • c) 1 0 ∧ pvec m0 (ℓ • a) (ℓ⁻¹ • c) ≠ 0 ∧
      tauV m0 (pvec m0 (ℓ • a) (ℓ⁻¹ • c)) = ν₁ • pvec m0 (ℓ • a) (ℓ⁻¹ • c) := by
  have hνn : ν * star ν = 1 := by
    have h1 : pvec m0 a c = (star ν * ν) • pvec m0 a c := by
      calc pvec m0 a c = tauV m0 (tauV m0 (pvec m0 a c)) := (tauV_tauV m0 _).symm
        _ = tauV m0 (ν • pvec m0 a c) := by rw [hν]
        _ = star ν • tauV m0 (pvec m0 a c) := by rw [tauV_smul, m0_tau]
        _ = (star ν * ν) • pvec m0 a c := by rw [hν, smul_smul]
    have h2 : (1 - star ν * ν) • pvec m0 a c = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    have h3 : 1 - star ν * ν = 0 := (smul_eq_zero.mp h2).resolve_right hp0
    linear_combination -h3
  obtain ⟨ℓ, -, hℓ, hν₁⟩ := ratio_exists_aux ν (mem_all49 ν) hνn
  have hℓ0 : ℓ ≠ 0 := left_ne_zero_of_mul_eq_one hℓ
  have hτ : star ℓ = ℓ⁻¹ := eq_inv_of_mul_eq_one_right hℓ
  refine ⟨ℓ, hℓ, star ℓ * star ℓ * ν, hν₁, ?_, ?_, ?_⟩
  · have := hp.rot hℓ
    rwa [mul_zero] at this
  · rw [pvec_rot hℓ]
    exact smul_ne_zero hℓ0 hp0
  · rw [pvec_rot hℓ, tauV_smul_rot hℓ, hν, smul_smul, smul_smul, hτ]
    congr 1
    field_simp

theorem rep_eigen {reps : List ClassRep} (hT : TableOK reps) (ν₁ : GF49)
    (hν : ν₁ = 1 ∨ ν₁ = zeta0) :
    ∃ r ∈ reps, r.γ = 1 ∧ r.η = 0 ∧ pvec m0 (toVec e0C) (toVec r.c) ≠ 0 ∧
      tauV m0 (pvec m0 (toVec e0C) (toVec r.c)) = ν₁ • pvec m0 (toVec e0C) (toVec r.c) := by
  rcases hν with rfl | rfl
  · obtain ⟨r, hr, hγr, hηr, hbr⟩ := hT.sp 131 (by simp)
    obtain ⟨hne', hσ'⟩ := hT.p131 r hr hbr
    have hne := (eqC_eq_false_iff _ _).1 hne'
    have hσ := (eqC_iff _ _).1 hσ'
    refine ⟨r, hr, hγr, hηr, ?_, ?_⟩
    · rw [← toVec_pvecC]
      intro h
      exact hne ((toVec_eq_zero_iff _).mp h)
    · rw [← toVec_pvecC, ← toVec_tauC, hσ, toVec_smulC]
  · obtain ⟨r, hr, hγr, hηr, hbr⟩ := hT.sp 146 (by simp)
    obtain ⟨hne', hσ'⟩ := hT.p146 r hr hbr
    have hne := (eqC_eq_false_iff _ _).1 hne'
    have hσ := (eqC_iff _ _).1 hσ'
    refine ⟨r, hr, hγr, hηr, ?_, ?_⟩
    · rw [← toVec_pvecC]
      intro h
      exact hne ((toVec_eq_zero_iff _).mp h)
    · rw [← toVec_pvecC, ← toVec_tauC, hσ, toVec_smulC]


theorem rep_indep {reps : List ClassRep} (hT : TableOK reps) :
    ∃ r ∈ reps, r.γ = 1 ∧ r.η = 0 ∧ ∀ s t : GF49,
      s • pvec m0 (toVec e0C) (toVec r.c) -
        t • tauV m0 (pvec m0 (toVec e0C) (toVec r.c)) = 0 → s = 0 ∧ t = 0 := by
  obtain ⟨r, hr, hγr, hηr, hbr⟩ := hT.sp 104 (by simp)
  refine ⟨r, hr, hγr, hηr, fun s t h => ?_⟩
  refine hT.p104 r hr hbr s (mem_all49 s) t (mem_all49 t) ?_
  rw [eqC_iff, ← toVec_eq_zero_iff, toVec_subC, toVec_smulC, toVec_smulC, toVec_tauC,
    toVec_pvecC]
  exact h

theorem special_indep_of_not_eigen {p : Vec GF49} (hp0 : p ≠ 0)
    (hne : ¬ ∃ ν : GF49, tauV m0 p = ν • p) :
    ∀ s t : GF49, s • p - t • tauV m0 p = 0 → s = 0 ∧ t = 0 := by
  intro s t h
  by_cases ht : t = 0
  · subst ht
    simp at h
    exact ⟨h.resolve_right hp0, rfl⟩
  · exfalso
    apply hne
    refine ⟨t⁻¹ * s, ?_⟩
    have h1 : t • tauV m0 p = s • p := by
      rw [sub_eq_zero] at h
      exact h.symm
    calc tauV m0 p = t⁻¹ • (t • tauV m0 p) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      _ = (t⁻¹ * s) • p := by rw [h1, smul_smul]

theorem scale_back (g : SigmaIso m0) {a e : Vec GF49} {u s : GF49} (hu : u ≠ 0)
    (h : g.toLinearEquiv (u • a) = s • e) : g.toLinearEquiv a = (u⁻¹ * s) • e := by
  rw [map_smul] at h
  calc g.toLinearEquiv a = u⁻¹ • (u • g.toLinearEquiv a) := by
        rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
    _ = (u⁻¹ * s) • e := by rw [h, smul_smul]

theorem pair_to_rep_special (hS : SigmaWitt) {reps : List ClassRep} (hT : TableOK reps)
    {a c : Vec GF49} (hp : PairData m0 a c 1 0) :
    ∃ (g : SigmaIso m0) (r : ClassRep) (s t : GF49), r ∈ reps ∧ s ≠ 0 ∧ t ≠ 0 ∧
      g.toLinearEquiv a = s • toVec e0C ∧ g.toLinearEquiv c = t • toVec r.c := by
  by_cases hp0 : pvec m0 a c = 0
  · obtain ⟨r, hr, hγr, hηr, hbr⟩ := hT.sp 102 (by simp)
    have hrp := rep_pairData' hT hr hγr hηr
    have hpr : pvec m0 (toVec e0C) (toVec r.c) = 0 := by
      rw [← toVec_pvecC, (eqC_iff _ _).1 (hT.p102 r hr hbr), toVec_zeroC]
    obtain ⟨g, hg1, hg2⟩ := pair_equiv hS hp hrp
      (rel_iff_special hp hrp (special_h_zero hp0 hpr))
    exact ⟨g, r, 1, 1, hr, one_ne_zero, one_ne_zero, by simpa using hg1, by simpa using hg2⟩
  · by_cases hex : ∃ ν : GF49, tauV m0 (pvec m0 a c) = ν • pvec m0 a c
    · obtain ⟨ν, hν⟩ := hex
      obtain ⟨ℓ, hℓ, ν₁, hν₁, hp', hp0', hσ'⟩ := special_rot_eigen hp hp0 hν
      obtain ⟨r, hr, hγr, hηr, hrne, hrσ⟩ := rep_eigen hT ν₁ hν₁
      have hrp := rep_pairData' hT hr hγr hηr
      obtain ⟨g, hg1, hg2⟩ := pair_equiv hS hp' hrp
        (rel_iff_special hp' hrp (special_h_eigen hp0' hσ' hrne hrσ))
      have hℓ0 : ℓ ≠ 0 := left_ne_zero_of_mul_eq_one hℓ
      refine ⟨g, r, ℓ⁻¹, ℓ, hr, inv_ne_zero hℓ0, hℓ0, ?_, ?_⟩
      · have := scale_back g hℓ0 (s := 1) (e := toVec e0C) (a := a) (by simpa using hg1)
        simpa using this
      · have h3 : g.toLinearEquiv (ℓ⁻¹ • c) = toVec r.c := hg2
        have h4 := scale_back g (inv_ne_zero hℓ0) (s := 1) (e := toVec r.c) (a := c)
          (by simpa using h3)
        simpa using h4
    · obtain ⟨r, hr, hγr, hηr, hind⟩ := rep_indep hT
      have hrp := rep_pairData' hT hr hγr hηr
      obtain ⟨g, hg1, hg2⟩ := pair_equiv hS hp hrp (rel_iff_special hp hrp
        (special_h_indep (special_indep_of_not_eigen hp0 hex) hind))
      exact ⟨g, r, 1, 1, hr, one_ne_zero, one_ne_zero, by simpa using hg1, by simpa using hg2⟩

theorem pair_to_rep (hS : SigmaWitt) {reps : List ClassRep} (hT : TableOK reps)
    {a c : Vec GF49} {γ η : GF49} (hγ : γ ∈ Fstar) (hη : η ∈ canonSet)
    (hp : PairData m0 a c γ η) :
    ∃ (g : SigmaIso m0) (r : ClassRep) (s t : GF49), r ∈ reps ∧ s ≠ 0 ∧ t ≠ 0 ∧
      g.toLinearEquiv a = s • toVec e0C ∧ g.toLinearEquiv c = t • toVec r.c := by
  by_cases hη0 : η = 0
  · subst hη0
    by_cases hγ1 : γ = 1
    · subst hγ1
      exact pair_to_rep_special hS hT hp
    · obtain ⟨g, r, hr, h1, h2⟩ := pair_to_rep_regular hS hT hγ hγ1 hp
      exact ⟨g, r, 1, 1, hr, one_ne_zero, one_ne_zero, by simpa using h1, by simpa using h2⟩
  · obtain ⟨g, r, hr, h1, h2⟩ := pair_to_rep_line hS hT hγ hη hη0 hp
    exact ⟨g, r, 1, 1, hr, one_ne_zero, one_ne_zero, by simpa using h1, by simpa using h2⟩

theorem exists_sigmaIso_to_rep (hS : SigmaWitt) {reps : List ClassRep} (hT : TableOK reps)
    {a c : Vec GF49} (ha : IsFF m0 a) (hc : IsFF m0 c) (hac : bf m0 a c ≠ 0) :
    ∃ (g : SigmaIso m0) (r : ClassRep) (s t : GF49), r ∈ reps ∧ s ≠ 0 ∧ t ≠ 0 ∧
      g.toLinearEquiv a = s • toVec e0C ∧ g.toLinearEquiv c = t • toVec r.c := by
  have hfix : star (her m0 a a) = her m0 a a := by
    have := tau_her_self m0 a
    rwa [m0_tau] at this
  obtain ⟨s₀, -, hs₀⟩ := norm_surj_aux (her m0 a a) (fixed_mem_Fstar _ hfix ha.2)
  obtain ⟨s', t', hs', ht', hp⟩ := PairData.of_ff (M := m0) ha.1 hc.1 hac
    (s := s₀) (by rw [m0_tau]; exact hs₀)
  have hγ0 : her m0 (t' • c) (t' • c) ≠ 0 := by
    rw [her_smul_left, her_smul_right]
    exact mul_ne_zero ht' (mul_ne_zero (tau_ne_zero m0 ht') hc.2)
  have hγf : star (her m0 (t' • c) (t' • c)) = her m0 (t' • c) (t' • c) := by
    have := tau_her_self m0 (t' • c)
    rwa [m0_tau] at this
  have hγ := fixed_mem_Fstar _ hγf hγ0
  obtain ⟨ℓ, -, hℓ, hη⟩ := rot_exists_aux (her m0 (s' • a) (t' • c)) (mem_all49 _)
  have hℓ0 : ℓ ≠ 0 := left_ne_zero_of_mul_eq_one hℓ
  have hp' := hp.rot (M := m0) (ℓ := ℓ) (by rw [m0_tau]; exact hℓ)
  obtain ⟨g, r, s, t, hr, hs, ht, h1, h2⟩ := pair_to_rep hS hT hγ hη hp'
  rw [smul_smul] at h1 h2
  refine ⟨g, r, (ℓ * s')⁻¹ * s, (ℓ⁻¹ * t')⁻¹ * t, hr, ?_, ?_, ?_, ?_⟩
  · exact mul_ne_zero (inv_ne_zero (mul_ne_zero hℓ0 hs')) hs
  · exact mul_ne_zero (inv_ne_zero (mul_ne_zero (inv_ne_zero hℓ0) ht')) ht
  · exact scale_back g (mul_ne_zero hℓ0 hs') h1
  · exact scale_back g (mul_ne_zero (inv_ne_zero hℓ0) ht') h2


@[expose] def RepConn (c : V7) : Prop :=
  ∀ A C : FFPt m0, (∃ s : GF49, s ≠ 0 ∧ A.1.rep = s • toVec e0C) →
    (∃ t : GF49, t ≠ 0 ∧ C.1.rep = t • toVec c) → MuConnectedAt m0 A C

theorem muConnected_m0 (hS : SigmaWitt) {reps : List ClassRep} (hT : TableOK reps)
    (hr : ∀ r ∈ reps, RepConn r.c) : MuConnected m0 := by
  intro A C hbf B D hAB hCB hAD hCD
  have key : MuConnectedAt m0 A C := by
    obtain ⟨g, r, s, t, hrm, hs, ht, h1, h2⟩ := exists_sigmaIso_to_rep hS hT A.2 C.2 hbf
    apply g.toSimil.muConnectedAt_of_simil
    apply hr r hrm
    · obtain ⟨c₁, hc₁, hA⟩ := g.toSimil.ptMap_rep A
      refine ⟨c₁ * s, mul_ne_zero hc₁ hs, ?_⟩
      rw [hA, g.toSimil_T, h1, smul_smul]
    · obtain ⟨c₁, hc₁, hC⟩ := g.toSimil.ptMap_rep C
      refine ⟨c₁ * t, mul_ne_zero hc₁ ht, ?_⟩
      rw [hC, g.toSimil_T, h2, smul_smul]
  exact key B D hAB hCB hAD hCD

end CFSG.ClassicalInvolution.PhanB3.S.Std.Q7
