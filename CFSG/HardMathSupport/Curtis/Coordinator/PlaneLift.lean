module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralReduceRank
public import CFSG.HardMathSupport.Curtis.Coordinator.PlaneDiag

public section

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.AGLEmbedding

namespace CFSG.HardMathSupport.Curtis.Coordinator.Plane

variable {K : Type*} [Field K]

theorem exists_lift_eq [Finite K] {p k : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {Eb : Subgroup (projectiveSL 3 K)} (hc : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x)
    (hexp : ∀ x ∈ Eb, x ^ p = 1) (hcard : Nat.card Eb = p ^ k) :
    ∃ P : Subgroup (SpecialLinearGroup (Fin 3) K), Nat.card P = p ^ k ∧
      (∀ a ∈ P, ∀ b ∈ P, Commute a b) ∧ (∀ g ∈ P, g ^ p = 1) ∧ P.map (proj 3 K) = Eb := by
  have : Fact p.Prime := ⟨hp⟩
  set H : Subgroup (SpecialLinearGroup (Fin 3) K) := Eb.comap (proj 3 K)
  let ψ : ↥H →* ↥Eb := ((proj 3 K).comp H.subtype).codRestrict Eb fun h => h.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := proj_surjective 3 K y
    exact ⟨⟨s, hy⟩, rfl⟩
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime p
    (hcard ▸ ((Subgroup.card_dvd_of_surjective hψ) : Nat.card Eb ∣ Nat.card H))
  have hker : ∀ g ∈ P₀.map H.subtype, proj 3 K g = 1 → g = 1 := by
    intro g hg hg1
    obtain ⟨g', hg', rfl⟩ := hg
    have h3 : (g' : SpecialLinearGroup (Fin 3) K) ^ 3 = 1 :=
      ToralReduce.pow_three_eq_one_of_mem_scalars (proj_eq_one_iff.mp hg1)
    have hpk : (g' : SpecialLinearGroup (Fin 3) K) ^ p ^ k = 1 := by
      have := pow_card_eq_one' (G := ↥P₀) (x := ⟨g', hg'⟩)
      rw [hP₀] at this
      simpa using congrArg (fun x : ↥P₀ => ((x : ↥H) : SpecialLinearGroup (Fin 3) K)) this
    have hcop : Nat.Coprime 3 (p ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
    have := pow_gcd_eq_one.mpr ⟨h3, hpk⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hmemE : ∀ g ∈ P₀.map H.subtype, proj 3 K g ∈ Eb := by
    rintro _ ⟨g', -, rfl⟩
    exact g'.2
  have hinj : Function.Injective ((proj 3 K).comp (P₀.map H.subtype).subtype) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact Subtype.ext (hker g.1 g.2 hg)
  have hle : (P₀.map H.subtype).map (proj 3 K) ≤ Eb := by
    rintro _ ⟨g, hg, rfl⟩
    exact hmemE g hg
  have hcardP : Nat.card (P₀.map H.subtype) = p ^ k := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hP₀]
  refine ⟨P₀.map H.subtype, hcardP, fun a ha b hb => ?_, fun g hg => ?_, ?_⟩
  · have h1 : a * b * (b * a)⁻¹ = 1 := hker _ ((P₀.map H.subtype).mul_mem
        ((P₀.map H.subtype).mul_mem ha hb) ((P₀.map H.subtype).inv_mem
          ((P₀.map H.subtype).mul_mem hb ha))) (by
      rw [map_mul, map_inv, map_mul, map_mul, hc _ (hmemE a ha) _ (hmemE b hb), mul_inv_cancel])
    exact mul_inv_eq_one.mp h1
  · refine hker _ ((P₀.map H.subtype).pow_mem hg p) ?_
    rw [map_pow, hexp _ (hmemE g hg)]
  · have hfin : Finite Eb := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have h2 : Nat.card ((P₀.map H.subtype).map (proj 3 K)) = Nat.card (P₀.map H.subtype) := by
      have hr : ((proj 3 K).comp (P₀.map H.subtype).subtype).range =
          (P₀.map H.subtype).map (proj 3 K) := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [← hr]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    rw [h2, hcardP, hcard]

theorem exists_diag_conj {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : (p : K) ≠ 0)
    (P : Subgroup (SpecialLinearGroup (Fin 3) K)) (hc : ∀ a ∈ P, ∀ b ∈ P, Commute a b)
    (hexp : ∀ g ∈ P, g ^ p = 1) (hcard : Nat.card P = p ^ 2) :
    ∃ B : SpecialLinearGroup (Fin 3) K,
      (∀ g ∈ P, ∃ d : Fin 3 → K, (∀ i, d i ^ p = 1) ∧
        ((B⁻¹ * g * B : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          diagonal d) ∧
      (∀ (d : Fin 3 → K) (h : d 0 * d 1 * d 2 = 1), (∀ i, d i ^ p = 1) →
        ∃ g ∈ P, B⁻¹ * g * B = diagElt d h) := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp2' : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hfin : Finite P :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨a, haP, ha1⟩ : ∃ a ∈ P, a ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : P = ⊥ := (Subgroup.eq_bot_iff_forall P).mpr h
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hoa : orderOf a = p := orderOf_eq_prime (hexp a haP) ha1
  obtain ⟨b, hbP, hba⟩ : ∃ b ∈ P, b ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have hza : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hoa]
    have : Finite (Subgroup.zpowers a) :=
      Nat.finite_of_card_ne_zero (by rw [hza]; exact hp.ne_zero)
    have hle : Nat.card P ≤ Nat.card (Subgroup.zpowers a) := Subgroup.card_le_of_le h
    omega
  obtain ⟨g, hgP, hg1, v, hv0, hgv⟩ : ∃ g ∈ P, g ≠ 1 ∧ ∃ v : Fin 3 → K, v ≠ 0 ∧
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
    rcases ToralReduce.exists_fixed_of_commute hpK (hc a haP b hbP) (hexp a haP) (hexp b hbP)
      with ⟨k, hk, hkp, v, hv0, hv⟩ | ⟨i, hi, v, hv0, hv⟩
    · refine ⟨a ^ k, P.pow_mem haP k, ?_, v, hv0, hv⟩
      exact pow_ne_one_of_lt_orderOf hk.ne' (hoa ▸ hkp)
    · refine ⟨a ^ i * b, P.mul_mem (P.pow_mem haP i) hbP, fun h => hba ?_, v, hv0, hv⟩
      have : b = (a ^ i)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [this]
      exact (Subgroup.zpowers a).inv_mem (Subgroup.npow_mem_zpowers a i)
  have hfl : LinearThreeKit.IsFixedLine p g v :=
    ToralReduce.isFixedLine_of_fixed (hp.odd_of_ne_two hp2) hpK (hexp g hgP) hg1 hv0 hgv
  have hPC : P ≤ Subgroup.centralizer ({g} : Set (SpecialLinearGroup (Fin 3) K)) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff.mp hk]
    exact (hc g hgP h hh).eq
  have hPeq : P = hfl.omega := hfl.eq_omega_of_card_eq hPC hexp hcard
  obtain ⟨r, hr⟩ : ∃ r : K, (LinearThreeKit.centPoly g).IsRoot r := by
    by_contra hs
    push Not at hs
    have h1 := hfl.omega_eq_zpowers_of_nonsplit (fun r hr => hs r hr) hp
    rw [← hPeq] at h1
    have h2 : Nat.card P = p := by
      rw [h1, Nat.card_zpowers, orderOf_eq_prime (hexp g hgP) hg1]
    omega
  obtain ⟨b₁, b₂, hli, hU₁, hU₂, hr1, hrr, hrp, hC⟩ := hfl.exists_splitTorus hr
  set w : Fin 3 → Fin 3 → K := ![v, b₁, b₂] with hw
  have hdet0 : (Matrix.of w).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).mp (LinearThreeKit.isUnit_transpose_of hli)
    rw [Matrix.det_transpose] at this
    exact this.ne_zero
  set c : K := ((Matrix.of w).det)⁻¹ with hc
  have hc0 : c ≠ 0 := inv_ne_zero hdet0
  set w' : Fin 3 → Fin 3 → K := ![c • v, b₁, b₂] with hw'
  have hdet' : (Matrix.of w').det = 1 := by
    have : Matrix.of w' = Matrix.updateRow (Matrix.of w) 0 (c • (Matrix.of w) 0) := by
      ext i j
      fin_cases i <;> simp [Matrix.updateRow_apply, hw, hw']
    rw [this, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, hc, inv_mul_cancel₀ hdet0]
  obtain ⟨B, hB⟩ : ∃ B : SpecialLinearGroup (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) = (Matrix.of w')ᵀ :=
    ⟨⟨(Matrix.of w')ᵀ, by rw [Matrix.det_transpose, hdet']⟩, rfl⟩
  have hBinv : ((B⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (B : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hw'0 : ∀ j, w' j ≠ 0 := by
    intro j
    fin_cases j
    · exact smul_ne_zero hc0 hv0
    · exact hli.ne_zero 1
    · exact hli.ne_zero 2
  have hcol : ∀ (A : Matrix (Fin 3) (Fin 3) K) (lam : Fin 3 → K),
      A * (B : Matrix (Fin 3) (Fin 3) K) = (B : Matrix (Fin 3) (Fin 3) K) * diagonal lam ↔
        ∀ j, A *ᵥ w' j = lam j • w' j := by
    intro A lam
    rw [hB, LinearThreeKit.mul_transpose_of_iff]
    refine forall_congr' fun j => ?_
    simp [diagonal_apply]
  refine ⟨B, fun g' hg' => ?_, fun d h hd => ?_⟩
  ·
    have hg'C : g' ∈ Subgroup.centralizer ({g} : Set (SpecialLinearGroup (Fin 3) K)) := hPC hg'
    obtain ⟨h0, h1, h2⟩ := (hC g').mp hg'C
    obtain ⟨l₀, hl₀⟩ := Submodule.mem_span_singleton.mp h0
    obtain ⟨l₁, hl₁⟩ := Submodule.mem_span_singleton.mp h1
    obtain ⟨l₂, hl₂⟩ := Submodule.mem_span_singleton.mp h2
    set lam : Fin 3 → K := ![l₀, l₁, l₂] with hlam
    have hev : ∀ j, (g' : Matrix (Fin 3) (Fin 3) K) *ᵥ w' j = lam j • w' j := by
      intro j
      fin_cases j
      · show (g' : Matrix (Fin 3) (Fin 3) K) *ᵥ (c • v) = l₀ • (c • v)
        rw [Matrix.mulVec_smul, ← hl₀, smul_comm]
      · exact hl₁.symm
      · exact hl₂.symm
    refine ⟨lam, fun j => ?_, ?_⟩
    · have hp1 : (g' : Matrix (Fin 3) (Fin 3) K) ^ p = 1 :=
        LinearThreeKit.coe_pow_eq_one (hexp g' hg')
      have e := LinearThreeKit.pow_mulVec_of_mulVec_eq_smul (hev j) p
      rw [hp1, Matrix.one_mulVec] at e
      exact smul_left_injective K (hw'0 j) (by simpa using e.symm)
    · have h1 := (hcol g' lam).mpr hev
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, h1,
        ← Matrix.mul_assoc, hBinv, Matrix.one_mul]
  ·
    obtain ⟨g', hg'⟩ : ∃ g' : SpecialLinearGroup (Fin 3) K, g' = B * diagElt d h * B⁻¹ :=
      ⟨_, rfl⟩
    have hgB : (g' : Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) =
        (B : Matrix (Fin 3) (Fin 3) K) * diagonal d := by
      rw [hg', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
        Matrix.mul_assoc, hBinv, Matrix.mul_one, coe_diagElt]
    have hev := (hcol g' d).mp hgB
    have hmem : g' ∈ Subgroup.centralizer ({g} : Set (SpecialLinearGroup (Fin 3) K)) := by
      refine (hC g').mpr ⟨?_, ?_, ?_⟩
      · have h0 : (g' : Matrix (Fin 3) (Fin 3) K) *ᵥ (c • v) = d 0 • (c • v) := hev 0
        rw [Matrix.mulVec_smul] at h0
        have h' : (g' : Matrix (Fin 3) (Fin 3) K) *ᵥ v = d 0 • v := by
          refine smul_right_injective _ hc0 ?_
          show c • ((g' : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = c • (d 0 • v)
          rw [h0, smul_comm]
        exact Submodule.mem_span_singleton.mpr ⟨d 0, h'.symm⟩
      · have h1 : (g' : Matrix (Fin 3) (Fin 3) K) *ᵥ b₁ = d 1 • b₁ := hev 1
        exact Submodule.mem_span_singleton.mpr ⟨d 1, h1.symm⟩
      · have h2 : (g' : Matrix (Fin 3) (Fin 3) K) *ᵥ b₂ = d 2 • b₂ := hev 2
        exact Submodule.mem_span_singleton.mpr ⟨d 2, h2.symm⟩
    have hDp : diagElt d h ^ p = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, coe_diagElt, diagonal_pow, Matrix.SpecialLinearGroup.coe_one]
      have : d ^ p = fun _ => 1 := funext fun i => by simpa using hd i
      rw [this, diagonal_one]
    have hgp : g' ^ p = 1 := by
      rw [hg', conj_pow, hDp, mul_one, mul_inv_cancel]
    refine ⟨g', hPeq ▸ (hfl.mem_omega.mpr ⟨hmem, hgp⟩), ?_⟩
    rw [hg']
    group

theorem plane_automizer [Finite K] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : (p : K) ≠ 0)
    {Eb : Subgroup (projectiveSL 3 K)} (hc : ∀ x ∈ Eb, ∀ y ∈ Eb, x * y = y * x)
    (hexp : ∀ x ∈ Eb, x ^ p = 1) (hcard : Nat.card Eb = p ^ 2)
    (α : MulAut (projectiveSL 3 K)) {k : ℕ} (hα : α ^ p ^ k = 1) (hαE : ∀ e ∈ Eb, α e ∈ Eb) :
    ∀ e ∈ Eb, α e = e := by
  obtain ⟨P, hPcard, hPc, hPexp, hPE⟩ := exists_lift_eq hp (by omega) hc hexp hcard
  obtain ⟨B, hBd, hBf⟩ := exists_diag_conj hp hp5 hpK P hPc hPexp hPcard
  set Q : Subgroup (SpecialLinearGroup (Fin 3) K) :=
    P.map (MulAut.conj B⁻¹).toMonoidHom with hQ
  have hQmem : ∀ g' : SpecialLinearGroup (Fin 3) K, g' ∈ Q ↔ ∃ g ∈ P, B⁻¹ * g * B = g' := by
    intro g'
    rw [hQ, Subgroup.mem_map]
    refine exists_congr fun g => and_congr_right fun _ => ?_
    simp
  set c : MulAut (projectiveSL 3 K) := MulAut.conj (proj 3 K B) with hcdef
  have hmemQ : ∀ e, e ∈ Q.map (proj 3 K) ↔ c e ∈ Eb := by
    intro e
    constructor
    · rintro ⟨g', hg', rfl⟩
      obtain ⟨g, hg, rfl⟩ := (hQmem g').mp hg'
      rw [← hPE]
      refine ⟨g, hg, ?_⟩
      simp only [hcdef, MulAut.conj_apply, map_mul, map_inv]
      group
    · intro he
      rw [← hPE] at he
      obtain ⟨g, hg, hge⟩ := he
      refine ⟨B⁻¹ * g * B, (hQmem _).mpr ⟨g, hg, rfl⟩, ?_⟩
      have : e = c⁻¹ (c e) := by simp
      rw [this, ← hge]
      simp only [hcdef, MulAut.conj_inv_apply, map_mul, map_inv]
  have hQd : ∀ g ∈ Q, ∃ d : Fin 3 → K, (∀ i, d i ^ p = 1) ∧
      (g : Matrix (Fin 3) (Fin 3) K) = diagonal d := fun g' hg' => by
    obtain ⟨g, hg, rfl⟩ := (hQmem g').mp hg'
    exact hBd g hg
  have hQf : ∀ d : Fin 3 → K, (∀ i, d i ^ p = 1) → d 0 * d 1 * d 2 = 1 →
      ∃ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) = diagonal d := fun d hd h => by
    obtain ⟨g, hg, hgd⟩ := hBf d h hd
    exact ⟨B⁻¹ * g * B, (hQmem _).mpr ⟨g, hg, rfl⟩, by rw [hgd, coe_diagElt]⟩
  have hEQ : Q.map (proj 3 K) = Eb.comap (c : projectiveSL 3 K →* projectiveSL 3 K) := by
    ext e
    exact hmemQ e
  have hQcard : Nat.card (Q.map (proj 3 K)) = p ^ 2 := by
    rw [hEQ, Subgroup.comap_equiv_eq_map_symm, Subgroup.card_map_of_injective c.symm.injective]
    exact hcard
  set α' : MulAut (projectiveSL 3 K) := c⁻¹ * α * c⁻¹⁻¹ with hα'
  have hα'p : α' ^ p ^ k = 1 := by
    rw [hα', conj_pow, hα, mul_one, mul_inv_cancel]
  have hα'e : ∀ e, α' e = c⁻¹ (α (c e)) := fun e => by
    simp [hα']
  have hαQ : ∀ e ∈ Q.map (proj 3 K), α' e ∈ Q.map (proj 3 K) := by
    intro e he
    rw [hmemQ] at he ⊢
    rw [hα'e]
    simpa using hαE _ he
  have hfix := plane_diag_aut hp hp5 Q hQd hQf hQcard α' hα'p hαQ
  intro e₀ he₀
  have he : c⁻¹ e₀ ∈ Q.map (proj 3 K) := by
    rw [hmemQ]
    simpa using he₀
  have h1 := hfix _ he
  rw [hα'e] at h1
  simp only [MulAut.apply_inv_self] at h1
  have h2 := congrArg c h1
  simpa using h2

end CFSG.HardMathSupport.Curtis.Coordinator.Plane
