module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Descent
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Statements
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Cocycle

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.HardMathSupport.Seitz.Proving

section Sylow

variable {G : Type*} [Group G] [Finite G]

theorem exists_conj_mem_of_forall_card_le {p : ℕ} [Fact p.Prime] {C P : Subgroup G}
    (hPC : P ≤ C) (hP : IsPGroup p P)
    (hmax : ∀ R : Subgroup G, IsPGroup p R → R ≤ C → Nat.card R ≤ Nat.card P) {x : G}
    (hxC : x ∈ C) (hx : x ^ p = 1) : ∃ c ∈ C, c⁻¹ * x * c ∈ P := by
  classical
  have hPsyl : Nat.card (P.subgroupOf C) = p ^ (Nat.card C).factorization p := by
    rw [card_subgroupOf_of_le hPC]
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p C))
    have hS := Sylow.card_eq_multiplicity S
    refine le_antisymm ?_ ?_
    · have hPp' : IsPGroup p (P.subgroupOf C) := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
        exact IsPGroup.of_card (n := n) (by rw [card_subgroupOf_of_le hPC, hn])
      obtain ⟨S', hS'⟩ := hPp'.exists_le_sylow
      have h1 := Subgroup.card_le_of_le hS'
      rw [card_subgroupOf_of_le hPC, Sylow.card_eq_multiplicity] at h1
      exact h1
    · have hR : IsPGroup p ((S : Subgroup C).map C.subtype) := S.isPGroup'.map _
      have h2 := hmax _ hR (Subgroup.map_subtype_le _)
      rw [← hS]
      calc Nat.card (S : Subgroup C) = Nat.card ((S : Subgroup C).map C.subtype) :=
            (Nat.card_congr (Subgroup.equivMapOfInjective _ _ C.subtype_injective).toEquiv)
        _ ≤ Nat.card P := h2
  have hxp : IsPGroup p (Subgroup.zpowers (⟨x, hxC⟩ : C)) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hx))
  obtain ⟨S, hS⟩ := hxp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq C (Sylow.ofCard _ hPsyl) S
  have hxS : (⟨x, hxC⟩ : C) ∈ (S : Subgroup C) := hS (Subgroup.mem_zpowers _)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Sylow.coe_ofCard, Subgroup.mem_subgroupOf] at hxS
  simp only [MulAut.smul_def, map_inv, MulAut.conj_inv_apply] at hxS
  refine ⟨c, c.2, ?_⟩
  simpa [mul_assoc] using hxS

end Sylow

section Field

variable {K K₂ : Type} [Field K] [Finite K] [Field K₂] [Finite K₂]

theorem sq_mod_three (hq : Nat.card K % 3 = 2) : Nat.card K ^ 2 % 3 = 1 := by
  rw [Nat.pow_mod, hq]

theorem frob_frob (hcard : Nat.card K₂ = Nat.card K ^ 2) {σ : K₂ →+* K₂}
    (hσ : ∀ x, σ x = x ^ Nat.card K) (x : K₂) : σ (σ x) = x := by
  have := Fintype.ofFinite K₂
  rw [hσ, hσ, ← pow_mul, ← sq, ← hcard, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem units_frob {q : ℕ} {σ : K₂ →+* K₂} (hσ : ∀ x, σ x = x ^ q) (u : K₂ˣ) :
    Units.map σ.toMonoidHom u = u ^ q :=
  Units.ext (by simp [hσ])

theorem exists_twist_data (hq : Nat.card K % 3 = 2) (hcard : Nat.card K₂ = Nat.card K ^ 2)
    {σ : K₂ →+* K₂} (hσ : ∀ x, σ x = x ^ Nat.card K) :
    ∃ (Q : SL2 K₂) (ω c : K₂ˣ), Q⁻¹ * orderThreeSL K₂ * Q = HSL ω ∧ orderOf ω = 3 ∧
      Units.map σ.toMonoidHom ω = ω⁻¹ ∧ Matrix.SpecialLinearGroup.map σ Q = Q * nSL c ∧
      Units.map σ.toMonoidHom c = -c := by
  have hK₂ : Nat.card K₂ % 3 = 1 := by rw [hcard]; exact sq_mod_three hq
  have h3 : 3 ∣ Nat.card K₂ - 1 := by have := Nat.card_pos (α := K₂); omega
  obtain ⟨P, t, hP⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.exists_conj_HSL_of_three h3
    (orderThreeSL K₂) ⟨1, by rw [pow_one]; exact orderThreeSL_pow_three K₂⟩
  have ht3 : t ^ 3 = 1 := by
    have h : HSL t ^ 3 = 1 := by rw [← hP, conj_pow, orderThreeSL_pow_three]; group
    apply CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.HSLHom_injective
    rw [map_pow, map_one]
    exact h
  have ht1 : t ≠ 1 := by
    intro h1
    apply orderThreeSL_ne_one K₂
    have h : HSL t = 1 := by
      rw [h1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [HSL]
    have := congrArg (fun A => P⁻¹ * A * P) (hP.trans h)
    simpa [mul_assoc] using this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ht : orderOf t = 3 := orderOf_eq_prime ht3 ht1
  have hσt : Units.map σ.toMonoidHom t = t⁻¹ := by
    rw [units_frob hσ]
    have hq' : Nat.card K = 3 * (Nat.card K / 3) + 2 := by omega
    rw [hq', pow_add, pow_mul, ht3, one_pow, one_mul, eq_inv_iff_mul_eq_one, ← pow_succ, ht3]
  have hQ : (P⁻¹)⁻¹ * orderThreeSL K₂ * P⁻¹ = HSL t := by rw [inv_inv]; exact hP
  set Q := P⁻¹ with hQdef
  have hσQ : (Matrix.SpecialLinearGroup.map σ Q)⁻¹ * orderThreeSL K₂ *
      Matrix.SpecialLinearGroup.map σ Q = HSL t⁻¹ := by
    have := congrArg (Matrix.SpecialLinearGroup.map σ) hQ
    rwa [map_mul, map_mul, map_inv, mapSL_orderThreeSL, mapSL_HSL, hσt] at this
  have hn_inv : HSL t * (Q⁻¹ * Matrix.SpecialLinearGroup.map σ Q) =
      (Q⁻¹ * Matrix.SpecialLinearGroup.map σ Q) * HSL t⁻¹ := by
    rw [← hQ, ← hσQ]
    group
  have ht2 : (t : K₂) ^ 2 ≠ 1 := by
    intro h2
    apply ht1
    have h2' : t ^ 2 = 1 := Units.ext (by simpa using h2)
    calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
      _ = 1 := by rw [ht3, h2', inv_one, one_mul]
  obtain ⟨c, hc⟩ := exists_eq_nSL ht2 hn_inv
  have hσQ' : Matrix.SpecialLinearGroup.map σ Q = Q * nSL c := by
    rw [← hc, mul_inv_cancel_left]
  have hσσ : Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map σ Q) = Q := by
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, frob_frob hcard hσ]
  have hc' : nSL (Units.map σ.toMonoidHom c) = (nSL c)⁻¹ := by
    have h := hσσ
    rw [hσQ', map_mul, hσQ', mapSL_nSL, mul_assoc] at h
    have h1 : nSL c * nSL (Units.map σ.toMonoidHom c) = 1 :=
      mul_left_cancel (h.trans (mul_one Q).symm)
    exact eq_inv_of_mul_eq_one_right h1
  have hcσ : Units.map σ.toMonoidHom c = -c := by
    rw [nSL_inv] at hc'
    have h01 := congrArg (fun A : SL2 K₂ => (A : Matrix (Fin 2) (Fin 2) K₂) 0 1) hc'
    simp only [nSL] at h01
    exact Units.ext (by simpa using h01)
  exact ⟨Q, t, c, hQ, ht, hσt, hσQ', hcσ⟩

end Field


theorem rootDiagUnit_pow_D4 {L : Type} [Field L] (a : Fin Tag.D4.rank → Lˣ) (n : ℕ) :
    rootDiagUnit Tag.D4 (a ^ n) = rootDiagUnit Tag.D4 a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, rootDiagUnit_one]
  | succ n ih => rw [pow_succ, pow_succ, rootDiagUnit_mul, ih]

theorem exists_cocyc_eq_mul_bcAd {L : Type} [Field L] [Finite L] {q : ℕ}
    (hcard : Nat.card L = q ^ 2) (hq1 : 1 ≤ q) (σ : L →+* L) (hσ : ∀ x, σ x = x ^ q) {c : Lˣ}
    (hc : Units.map σ.toMonoidHom c = -c) :
    ∃ (r : ↥(adjointGroup Tag.D4 L)) (x z : Lˣ),
      (r : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 (tupXZ x z) ∧ cocyc c = r * bcAd σ r := by
  obtain ⟨a, b, hab⟩ := exists_cocyc_tupXZ c
  have hσab : tupXZ (Units.map σ.toMonoidHom a) (Units.map σ.toMonoidHom b) = tupXZ a b := by
    have e := congrArg Subtype.val (bcAd_cocyc σ hc)
    rw [coe_bcAd_of_eq_rootDiagUnit σ hab, hab, map_tupXZ] at e
    exact rootDiagUnit_injective_D4 e
  have ha : a ^ q = a := by
    have h0 := congrFun hσab ⟨0, by decide⟩
    rwa [tupXZ_zero, tupXZ_zero, units_frob hσ] at h0
  have hb : b ^ q = b := by
    have h2 := congrFun hσab ⟨2, by decide⟩
    rwa [tupXZ_two, tupXZ_two, units_frob hσ] at h2
  obtain ⟨x, hx⟩ := exists_pow_succ_eq hcard hq1 ha
  obtain ⟨z, hz⟩ := exists_pow_succ_eq hcard hq1 hb
  refine ⟨cochar vChi x * cochar vTheta z, x, z, cochar_tupXZ x z, ?_⟩
  apply Subtype.ext
  rw [hab, Subgroup.coe_mul, cochar_tupXZ, coe_bcAd_of_eq_rootDiagUnit σ (cochar_tupXZ x z),
    map_tupXZ, ← rootDiagUnit_mul, tupXZ_mul, units_frob hσ, units_frob hσ, ← pow_succ',
    ← pow_succ', hx, hz]

theorem sylowCentral_of_ext {K : Type} [Field K] [Finite K] (hq : Nat.card K % 3 = 2)
    (hK4 : 4 ≤ Nat.card K) {K₂ : Type} [Field K₂] [Finite K₂] [Algebra K K₂]
    (hcard : Nat.card K₂ = Nat.card K ^ 2) (σ : K₂ →+* K₂) (hσ : ∀ x, σ x = x ^ Nat.card K)
    {x : ↥(adjointGroup Tag.D4 K)} (hαx : gammaP K (orderThreeSL K) x = x) (hx3 : x ^ 3 = 1) :
    ∃ c : ↥(adjointGroup Tag.D4 K), gammaP K (orderThreeSL K) c = c ∧
      Commute (c⁻¹ * x * c) (frameD K (orderThreeSL K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, ω, c₀, hQ, hω, hσω, hQc, hc₀⟩ := exists_twist_data hq hcard hσ
  have hω3 : ω ^ 3 = 1 := hω ▸ pow_orderOf_eq_one ω
  have hK₂ : Nat.card K₂ % 3 = 1 := by rw [hcard]; exact sq_mod_three hq
  have hK₂4 : 4 ≤ Nat.card K₂ := by rw [hcard]; nlinarith
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq_three_pow (K := K₂)
  set e := (Nat.card K₂ - 1).factorization 3 with he
  set μ := Subgroup.zpowers ζ with hμ
  have hμsq : ∀ u ∈ μ, ∃ b : K₂ˣ, u = b ^ 2 := mu_sq (Odd.pow (by decide : Odd 3)) hζ
  have hcardμ : Nat.card μ = 3 ^ e := by rw [hμ, Nat.card_zpowers, hζ]
  have hζq : ζ ^ (Nat.card K + 1) = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hζ]
    have hdvd : 3 ^ e ∣ (Nat.card K - 1) * (Nat.card K + 1) := by
      have h1 : 3 ^ e ∣ Nat.card K₂ - 1 := Nat.ordProj_dvd _ _
      have h2 : Nat.card K₂ - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
        rw [hcard]
        obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by
          have := Nat.card_pos (α := K); omega⟩
        rw [hm, Nat.add_sub_cancel]
        have : (m + 1) ^ 2 = m * (m + 1 + 1) + 1 := by ring
        omega
      rwa [h2] at h1
    have hcop : Nat.Coprime (3 ^ e) (Nat.card K - 1) := by
      apply Nat.Coprime.pow_left
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      omega
    exact hcop.dvd_of_dvd_mul_left hdvd
  have hμq : ∀ u ∈ μ, u ^ (Nat.card K + 1) = 1 := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζq, one_zpow]
  have hμσ : ∀ u ∈ μ, Units.map σ.toMonoidHom u = u⁻¹ := by
    intro u hu
    rw [units_frob hσ]
    exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hμq u hu)
  have hζe : ζ ^ 3 ^ e = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hμ3 : ∀ u ∈ μ, u ^ 3 ^ e = 1 := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζe, one_zpow]
  have hT3ι : T3fix (ω := ω) (K := K₂) μ ≤ (ιTw K Q).range := by
    rintro t ⟨⟨a, ha, hta⟩, -⟩
    have hσt : bcAd σ t = t⁻¹ := by
      apply Subtype.ext
      rw [coe_bcAd_of_eq_rootDiagUnit σ hta, Subgroup.coe_inv, hta, rootDiagUnit_inv]
      congr 1
      funext j
      rw [Pi.inv_apply, hμσ _ (ha j)]
    have htinv : ((t⁻¹ : ↥(adjointGroup Tag.D4 K₂)) : ModGL Tag.D4 K₂) =
        rootDiagUnit Tag.D4 a⁻¹ := by
      rw [Subgroup.coe_inv, hta, rootDiagUnit_inv]
    refine mem_range_ιTw_of_fixed σ hσ hQc (k := e) ?_ ?_
    · rw [hσt, gTw_nSL_conj_diag c₀ htinv, inv_inv]
    · apply Subtype.ext
      rw [Subgroup.coe_pow, hta, ← rootDiagUnit_pow_D4, Subgroup.coe_one, ← rootDiagUnit_one]
      congr 1
      funext j
      rw [Pi.pow_apply, Pi.one_apply, hμ3 _ (ha j)]
  obtain ⟨r, a₁, a₂, hr, hcr⟩ := exists_cocyc_eq_mul_bcAd hcard Nat.card_pos σ hσ hc₀
  have hπ3 : (r * yP hω3) ^ 3 = 1 := mul_yP_pow_three hω3 hr
  have hπnd : r * yP hω3 ∉ T3fix (ω := ω) (K := K₂) μ := by
    rintro ⟨⟨b, -, hb⟩, -⟩
    exact mul_yP_not_diag hω3 hω hr hb
  have hπ1 : r * yP hω3 ≠ 1 := by
    intro h1
    apply hπnd
    rw [h1]
    exact Subgroup.one_mem _
  have hπord : orderOf (r * yP hω3) = 3 := orderOf_eq_prime hπ3 hπ1
  have hπι : r * yP hω3 ∈ (ιTw K Q).range :=
    mem_range_ιTw_of_fixed σ hσ hQc (fixed_mul_yP hω3 hσω hr hcr) (k := 1)
      (by rw [pow_one]; exact hπ3)
  set P' := T3fix (ω := ω) (K := K₂) μ ⊔ Subgroup.zpowers (r * yP hω3) with hP'
  have hcardP' : Nat.card P' = Nat.card (T3fix (ω := ω) (K := K₂) μ) * 3 := by
    rw [hP', card_sup_of_le_normalizer
      ((Subgroup.zpowers_le).2 (mul_yP_mem_normalizer_T3fix hω3 μ hr))
      (inf_zpowers_eq_bot_of_pow_three hπ3 hπnd), Nat.card_zpowers, hπord]
  have hP'ge : 3 * Nat.card μ ^ 2 ≤ Nat.card P' := by
    rw [hcardP', mul_comm 3]
    exact Nat.mul_le_mul_right 3 (card_T3fix_ge (ω := ω) μ hμsq)
  have hP'p : IsPGroup 3 P' := by
    have hdvdT : Nat.card (T3fix (ω := ω) (K := K₂) μ) ∣ 3 ^ (4 * e) := by
      have h := Subgroup.card_dvd_of_le
        (inf_le_left : T3fix (ω := ω) (K := K₂) μ ≤ torusSub μ)
      rwa [card_torusSub μ hμsq, hcardμ, ← pow_mul, mul_comm e 4] at h
    refine IsPGroup.of_card_dvd_pow (n := 4 * e + 1) ?_
    rw [hcardP', pow_succ]
    exact Nat.mul_dvd_mul_right hdvdT 3
  have hP'ι : P' ≤ (ιTw K Q).range := sup_le hT3ι ((Subgroup.zpowers_le).2 hπι)
  have hP'α : P' ≤ fixedSubgroup (gammaP K₂ (HSL ω)) :=
    sup_le inf_le_right ((Subgroup.zpowers_le).2 (gammaP_HSL_mul_yP hω3 hr))
  have hP'd : P' ≤ Subgroup.centralizer
      ({torusElement Tag.D4 K₂ ⟨0, by decide⟩ ω * torusElement Tag.D4 K₂ ⟨1, by decide⟩ ω⁻¹} :
        Set ↥(adjointGroup Tag.D4 K₂)) := by
    refine sup_le ?_ ((Subgroup.zpowers_le).2 ?_)
    · rintro y ⟨⟨a, -, hya⟩, -⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commute_of_diag hya (coe_dTorus ω)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact mul_yP_commute_dTorus hω3 hr ω
  set P := P'.comap (ιTw K Q) with hP
  have hιinj : Function.Injective (ιTw K Q) := ιTw_injective Q
  have hcardP : Nat.card P = Nat.card P' := by
    rw [← Subgroup.card_map_of_injective hιinj, hP, Subgroup.map_comap_eq_self hP'ι]
  have hPp : IsPGroup 3 P := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP'p
    exact IsPGroup.of_card (n := n) (by rw [hcardP, hn])
  have hPC : P ≤ fixedSubgroup (gammaP K (orderThreeSL K)) := by
    intro y hy
    show gammaP K (orderThreeSL K) y = y
    apply hιinj
    rw [ιTw_gammaP hQ y]
    exact hP'α hy
  have hPd : ∀ y ∈ P, Commute y (frameD K (orderThreeSL K)) := by
    intro y hy
    show y * frameD K (orderThreeSL K) = frameD K (orderThreeSL K) * y
    apply hιinj
    rw [map_mul, map_mul, ιTw_frameD hQ]
    exact Subgroup.mem_centralizer_singleton_iff.1 (hP'd hy)
  have hmax : ∀ R : Subgroup ↥(adjointGroup Tag.D4 K), IsPGroup 3 R →
      R ≤ fixedSubgroup (gammaP K (orderThreeSL K)) → Nat.card R ≤ Nat.card P := by
    intro R hR hRC
    have h := card_le_of_isPGroup_fixed_gammaP hK₂ hK₂4 hω3 hω hζ (hR.map (ιTw K Q)) ?_
    · rw [Subgroup.card_map_of_injective hιinj] at h
      rw [hcardP]
      exact h.trans hP'ge
    · rintro y ⟨z, hz, rfl⟩
      rw [← ιTw_gammaP hQ z, show gammaP K (orderThreeSL K) z = z from hRC hz]
  obtain ⟨c, hcC, hcP⟩ := exists_conj_mem_of_forall_card_le hPC hPp hmax
    (show x ∈ fixedSubgroup (gammaP K (orderThreeSL K)) from hαx) hx3
  exact ⟨c, hcC, hPd _ hcP⟩

theorem nonsplitSylowCentral_holds : NonsplitSylowCentral := by
  intro K _ _ hq hK4 x hαx hx3
  have := Fintype.ofFinite K
  obtain ⟨n, hp, -⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  exact sylowCentral_of_ext hq hK4 (FiniteField.natCard_extension K (ringChar K) 2)
    (FiniteField.Extension.frob K (ringChar K) 2).toRingEquiv.toRingHom
    (fun y => FiniteField.Extension.frob_apply K (ringChar K) 2) hαx hx3

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
