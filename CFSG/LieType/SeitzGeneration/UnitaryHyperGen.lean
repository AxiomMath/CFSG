module

public import CFSG.LieType.SeitzGeneration.UnitaryHyperOpp
public import CFSG.LieType.SeitzGeneration.UnitaryHyperCenters
public import CFSG.RankThree.PartOne.KE8F.HyperGen

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.CTP
  CFSG.Open

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem eq_one_of_scalar_pow_char {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hn : 1 ≤ n)
    {g : SUid σ n} (hg : ∃ c : K, matU g = c • 1) (hgl : g ^ ℓ = 1) : g = 1 := by
  obtain ⟨c, hc⟩ := hg
  have hv : (Pi.single ⟨0, hn⟩ 1 : Fin n → K) ∈
      Module.End.eigenspace (Matrix.mulVecLin (matU g)) c := by
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, hc, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have hv0 : (Pi.single ⟨0, hn⟩ 1 : Fin n → K) ≠ 0 := fun h => by
    have := congrFun h ⟨0, hn⟩
    simp at this
  have hcl : c ^ ℓ = 1 := pow_eq_one_of_mem_eigU hgl hv hv0
  have hc1 : c = 1 := by
    refine frobenius_inj K ℓ ?_
    rw [frobenius_def, map_one, hcl]
  refine ext_smul σ fun v => ?_
  have hc' : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1 := hc
  rw [smul_def, hc', hc1, one_smul, Matrix.one_mulVec, one_smul]

theorem natCast_card_comap_ne_zero [Finite K] (hn : 1 ≤ n) {P : Type*} [Group P]
    (π : SUid σ n →* P) (hker : ∀ g ∈ π.ker, ∃ c : K, matU g = c • 1) {p : ℕ} (hp : p.Prime)
    (hpK : (p : K) ≠ 0) {E : Subgroup P} (hE : ∀ x ∈ E, x ^ p = 1) :
    ((Nat.card (E.comap π) : ℕ) : K) ≠ 0 := by
  intro h0
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  have hℓp : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hdvd : ℓ ∣ Nat.card (E.comap π) := (CharP.cast_eq_zero_iff K ℓ _).1 h0
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hgℓ : (g : SUid σ n) ^ ℓ = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  have hcop : Nat.Coprime ℓ p := by
    refine (Nat.coprime_primes hℓp hp).2 fun h => hpK ?_
    rw [← h]
    exact CharP.cast_eq_zero K ℓ
  have h1 : π g.1 = 1 := by
    have h2 : (π g.1) ^ ℓ = 1 := by rw [← map_pow, hgℓ, map_one]
    have h3 : (π g.1) ^ p = 1 := hE _ g.2
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h2)
      (orderOf_dvd_of_pow_eq_one h3))
  have h4 : (g : SUid σ n) = 1 := eq_one_of_scalar_pow_char hn (hker g.1 h1) hgℓ
  have h5 : g = 1 := Subtype.ext h4
  rw [h5, orderOf_one] at hg
  exact hℓp.one_lt.ne hg

theorem le_hyperClosure_of_normalized {P : Type} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    {E : Subgroup P} (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 3) {Q : Subgroup P}
    (hnorm : ∀ e ∈ E, ∀ v ∈ Q, e * v * e⁻¹ ∈ Q) (hQp : ¬ p ∣ Nat.card Q) :
    Q ≤ Subgroup.closure {k : P | k ∈ (⊤ : Subgroup P) ∧ ∃ F₀ : Subgroup P, F₀ ≤ E ∧
      F₀.relIndex E = p ∧ ∀ f ∈ F₀, f * k = k * f} := by
  classical
  have hfp : Fact p.Prime := ⟨hp⟩
  have hEel : CFSG.IsElementaryAbelian p E :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one]) }
  have hnt : Nontrivial E :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hcard]; exact Nat.one_lt_pow (by norm_num) hp.one_lt)
  have hAV : E ≤ Subgroup.normalizer (Q : Set P) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro v
    refine ⟨fun hv => hnorm e he v hv, fun hv => ?_⟩
    have := hnorm e⁻¹ (E.inv_mem he) _ hv
    simpa [mul_assoc] using this
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := p) (A := E)
    (V := Q) hAV hQp
  refine hgen.trans (iSup₂_le fun B hB => ?_)
  intro k hk
  rw [Subgroup.mem_inf] at hk
  refine Subgroup.subset_closure ⟨Subgroup.mem_top _, B.map E.subtype,
    Subgroup.map_subtype_le B, ?_, fun f hf => Subgroup.mem_centralizer_iff.1 hk.2 f hf⟩
  have hsub : (B.map E.subtype).subgroupOf E = B :=
    Subgroup.comap_map_eq_self_of_injective E.subtype_injective B
  rw [Subgroup.relIndex, hsub]
  exact hB

theorem hyperGen_top_of_isotropic_unitary [Finite K] (hσ : IsUnitaryInvolution σ) (hn : 2 ≤ n)
    (h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) {P : Type} [Group P] (π : SUid σ n →* P)
    (hπ : Function.Surjective π) (hker : ∀ g ∈ π.ker, ∃ c : K, matU g = c • 1) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0) {E : Subgroup P} (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 3) {W : Submodule K (Fin n → K)} (hW0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0)
    (hstab : ∀ g : SUid σ n, π g ∈ E → ∀ w ∈ W, g • w ∈ W) :
    (⊤ : Subgroup P) ≤ Subgroup.closure {k : P | k ∈ (⊤ : Subgroup P) ∧
      ∃ F₀ : Subgroup P, F₀ ≤ E ∧ F₀.relIndex E = p ∧ ∀ f ∈ F₀, f * k = k * f} := by
  classical
  have hfin : Finite P := Finite.of_surjective π hπ
  set Et : Subgroup (SUid σ n) := E.comap π with hEt
  have hEtcard : ((Nat.card Et : ℕ) : K) ≠ 0 :=
    natCast_card_comap_ne_zero (by omega) π hker hp hpK hE.2
  have hWs : ∀ g ∈ Et, ∀ w ∈ W, g • w ∈ W := fun g hg w hw => hstab g hg w hw
  obtain ⟨W', hW', hcompl, hW's⟩ := exists_opposite hσ hEtcard hW hWs
  set Kset : Subgroup P := Subgroup.closure {k : P | k ∈ (⊤ : Subgroup P) ∧
    ∃ F₀ : Subgroup P, F₀ ≤ E ∧ F₀.relIndex E = p ∧ ∀ f ∈ F₀, f * k = k * f} with hKset
  set H : Subgroup (SUid σ n) := Kset.comap π with hH
  have hrad : ∀ {X : Submodule K (Fin n → K)} (hX : ∀ x ∈ X, ∀ y ∈ X, herm σ x y = 0),
      (∀ g ∈ Et, ∀ w ∈ X, g • w ∈ X) → uRad σ X hX ≤ H := by
    intro X hX hXs q hq
    have hnorm : ∀ e ∈ E, ∀ v ∈ (uRad σ X hX).map π, e * v * e⁻¹ ∈ (uRad σ X hX).map π := by
      intro e he v hv
      obtain ⟨a, rfl⟩ := hπ e
      obtain ⟨q', hq', rfl⟩ := hv
      have haEt : a ∈ Et := he
      exact ⟨a * q' * a⁻¹, uRad_conj_mem (fun w hw => hXs a haEt w hw)
        (fun w hw => hXs a⁻¹ (Et.inv_mem haEt) w hw) hq', by simp⟩
    have hQp : ¬ p ∣ Nat.card ((uRad σ X hX).map π) := fun hd =>
      not_dvd_card_uRad hp hp2 hpK (hd.trans (Subgroup.card_map_dvd _ π))
    exact le_hyperClosure_of_normalized hp hE hcard hnorm hQp (Subgroup.mem_map_of_mem _ hq)
  have htop : H = ⊤ :=
    eq_top_of_uRad_of_opposite hσ hn h3 hW0 hW hW' hcompl (hrad hW hWs) (hrad hW' hW's)
  intro k _
  obtain ⟨g, rfl⟩ := hπ k
  have hg : g ∈ H := htop ▸ Subgroup.mem_top g
  exact hg

end CFSG.LieType.SeitzGeneration
