module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcE6OneModel
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcHRConcB
import CFSG.CGT.T75P.SylowSplit
import CFSG.GH74.Uniqueness.SU.SU7Gen3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcE6OneVad
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenActPSimple

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.E6One

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction CFSG.SeitzReduction.EPilot
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.NoOffE6Three CFSG.StandardType.TableBExc.E6Three
open scoped Pointwise

section Quot


variable {K : Type} [Field K]

theorem quot_transport {Ω : Type} [Group Ω] {S : Subgroup Ω} (hS : S.Normal) {X : Type}
    [Group X] {π : ↥S →* X} {Γ : Ω →* MulAut X}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 b⟩) (ψ : MulAut X)
    (b : Ω) (g : ↥S) :
    ((MulAut.conj ψ).toMonoidHom.comp Γ) b ((ψ.toMonoidHom.comp π) g) =
      (ψ.toMonoidHom.comp π) ⟨b * g * b⁻¹, hS.conj_mem _ g.2 b⟩ := by
  change ψ (Γ b (ψ.symm (ψ (π g)))) = ψ (π _)
  rw [MulEquiv.symm_apply_apply, hΓ]

theorem ker_comp_mulEquiv {S X Y : Type*} [Group S] [Group X] [Group Y] (π : S →* X)
    (ψ : X ≃* Y) : (ψ.toMonoidHom.comp π).ker = π.ker := by
  ext g
  simp [MonoidHom.mem_ker]

theorem concA_of_actData_quot {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [Finite K]
    (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hB : IsElemAbelian 3 B) (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3)
    {π : ↥S →* ↥(adjointGroup .E6 K)} (hπ : Function.Surjective π)
    (hπZ : π.ker ≤ Subgroup.center ↥S) {Γ : Ω →* MulAut ↥(adjointGroup .E6 K)}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 b⟩)
    (hW : ModelGen.ActData 3 B (fun x => Γ x)) : S267ConcA 3 S B := by
  haveI : Finite ↥(adjointGroup .E6 K) := generated_group_finite .E6 K
  exact ModelGen.concA_of_actData_central Nat.prime_three (by norm_num) hS hperf hcore hB hBC π
    hπ hπZ (fun x => Γ x) (fun x g => (hΓ x g).symm) hW

theorem hypLift {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [Finite K]
    (hK2 : ringChar K ≠ 2) (h3 : 3 ∣ Nat.card K - 1) (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hB : IsElemAbelian 3 B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) {π : ↥S →* ↥(adjointGroup .E6 K)}
    (hπ : Function.Surjective π) (hπZ : π.ker ≤ Subgroup.center ↥S)
    {Γ : Ω →* MulAut ↥(adjointGroup .E6 K)}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 b⟩)
    (hΓker : Γ.ker = centModSubgroup 3 S) {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {σ : K ≃+* K} (hσζ : σ (ζ : K) = ζ) {b : Ω} (hbB : b ∈ B)
    (hb : Γ b = entrywiseAdjointAut .E6 σ) : HypLift Γ ζ hζ b := by
  by_cases hπi : Function.Injective π
  · exact hypLift_of_injective hK2 hS hcore hB hBC hπ hπi hΓ hΓker hζo hζ hσζ hbB hb
  · exact hypLift_of_not_injective hK2 h3 hS hperf hcore hπ hπZ hπi hΓ hζo hζ hσζ hb

theorem concA_of_lift {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [Finite K]
    (hK2 : ringChar K ≠ 2) (hS : S.Normal) (hperf : ⁅S, S⁆ = S) (hcore : GLAPPrimeCore 3 ↥S = ⊥)
    (hB : IsElemAbelian 3 B) {π : ↥S →* ↥(adjointGroup .E6 K)} (hπ : Function.Surjective π)
    (hπZ : π.ker ≤ Subgroup.center ↥S) {Γ : Ω →* MulAut ↥(adjointGroup .E6 K)}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 b⟩)
    (hΓker : Γ.ker = centModSubgroup 3 S) {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {σ : K ≃+* K} (hσζ : σ (ζ : K) = ζ) (hσ3 : σ ^ 3 = 1) {b : Ω} (hbB : b ∈ B)
    (hb : Γ b = entrywiseAdjointAut .E6 σ)
    (hbout : ∀ k : ℕ, entrywiseAdjointAut .E6 σ ^ k ∈ (hatAut .E6 K).range → b ^ k = 1)
    (hBle : Nat.card B ≤ 3 ^ 6 * Nat.card (Subgroup.zpowers (entrywiseAdjointAut .E6 σ)))
    (hL : HypLift Γ ζ hζ b) : S267ConcA 3 S B := by
  classical
  haveI : Finite ↥(adjointGroup .E6 K) := generated_group_finite .E6 K
  haveI : Finite (MulAut ↥(adjointGroup .E6 K)) :=
    Finite.of_injective (fun f : MulAut ↥(adjointGroup .E6 K) =>
      (f : ↥(adjointGroup .E6 K) → ↥(adjointGroup .E6 K))) DFunLike.coe_injective
  obtain ⟨M, t, hMel, hMc, hMΓ, hbM, ht1, ht2, htM, htb⟩ := hL
  set s := entrywiseAdjointAut .E6 σ with hs
  set Z := Subgroup.zpowers b with hZ
  set B' := M ⊔ Z with hB'
  have hb3 : b ^ 3 = 1 := hB.2 b hbB
  have hs3 : s ^ 3 = 1 := by
    rw [hs, ← entrywiseAdjointAut_pow, hσ3]
    exact map_one (entrywiseAdjointAutHom (τ := .E6) (K := K))
  have hZel : IsElemAbelian 3 Z := hB.mono ((Subgroup.zpowers_le).2 hbB)
  have hMZ : ∀ m ∈ M, ∀ y ∈ Z, m * y = y * m := by
    intro m hm y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact Commute.zpow_right (hbM m hm).symm n
  have hB'el : IsElemAbelian 3 B' := hMel.sup_of_commute hZel hMZ
  have hΓB' : B'.map Γ = vHyp ζ hζ ⊔ Subgroup.zpowers s := by
    rw [hB', Subgroup.map_sup, hMΓ, hZ, MonoidHom.map_zpowers, hb]
  have hcl : vHyp ζ hζ ⊔ Subgroup.zpowers s ≤
      Subgroup.closure (Set.range (diag3 ζ hζ) ∪ {s}) := by
    refine sup_le ?_ ((Subgroup.zpowers_le).2 (Subgroup.subset_closure (Or.inr rfl)))
    rintro _ ⟨x, rfl⟩
    exact Subgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  have hBV : ∀ x ∈ B', ∃ z, ∃ k : ℕ, Γ x = diag3 ζ hζ z * s ^ k := fun x hx =>
    exists_eq_of_mem_closure_diag3 hζ hσζ hσ3 (hcl (hΓB' ▸ ⟨x, hx, rfl⟩))
  have hinf : vHyp ζ hζ ⊓ Subgroup.zpowers s = ⊥ := by
    rw [eq_bot_iff]
    rintro f ⟨hf1, hf2⟩
    obtain ⟨k, -, rfl⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.exists_pow_lt_of_pow_eq_one (by norm_num) hs3
        hf2
    have hin : s ^ k ∈ (hatAut .E6 K).range := vAd_le_hatAut_range ζ hζ (vHyp_le_vAd ζ hζ hf1)
    rw [Subgroup.mem_bot, ← hb, ← map_pow, hbout k hin, map_one]
  have hcommV : ∀ f ∈ vHyp ζ hζ, ∀ g ∈ Subgroup.zpowers s, f * g = g * f := by
    intro f hf g hg
    obtain ⟨x, rfl⟩ := hf
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact (Commute.zpow_left (entrywiseAdjointAut_mul_diag3 hζ hσζ (hypIncl x)) n).symm
  have hcardV : Nat.card (B'.map Γ) = 3 ^ 5 * Nat.card (Subgroup.zpowers s) := by
    rw [hΓB', CFSG.CGT.T75P.card_sup_of_commute hcommV hinf, card_vHyp hζo hζ]
  have hZker : Z ⊓ Γ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨k, -, rfl⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.exists_pow_lt_of_pow_eq_one (by norm_num) hb3
        hy1
    have hsk : s ^ k = 1 := by rw [← hb, ← map_pow]; exact hy2
    rw [Subgroup.mem_bot]
    exact hbout k (by rw [hsk]; exact one_mem _)
  have hZc : Nat.card Z = Nat.card (Subgroup.zpowers s) := by
    have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Γ Z
    rw [hZker, Subgroup.card_bot, mul_one, hZ, MonoidHom.map_zpowers, hb] at h
    exact h.symm
  have hMker : Nat.card ↥(M ⊓ Γ.ker) = 3 := by
    have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Γ M
    rw [hMΓ, card_vHyp hζo hζ, hMc] at h
    have h' : 3 ^ 5 * Nat.card ↥(M ⊓ Γ.ker) = 3 ^ 5 * 3 := by rw [h]; norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'
  have hB'up : Nat.card B' ≤ 3 ^ 6 * Nat.card (Subgroup.zpowers s) := by
    have h := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute M Z hMZ).1
    rw [hMc, hZc] at h
    rw [← h]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hB'ker : Nat.card ↥(B' ⊓ Γ.ker) = 3 := by
    have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Γ B'
    rw [hcardV] at h
    have hle : Nat.card ↥(B' ⊓ Γ.ker) ≤ 3 := by
      have h2 : 3 ^ 5 * Nat.card (Subgroup.zpowers s) * Nat.card ↥(B' ⊓ Γ.ker) ≤
          3 ^ 5 * Nat.card (Subgroup.zpowers s) * 3 := by
        rw [h]
        calc Nat.card B' ≤ 3 ^ 6 * Nat.card (Subgroup.zpowers s) := hB'up
          _ = 3 ^ 5 * Nat.card (Subgroup.zpowers s) * 3 := by ring
      exact Nat.le_of_mul_le_mul_left h2 (Nat.mul_pos (by norm_num) Nat.card_pos)
    have hge : 3 ≤ Nat.card ↥(B' ⊓ Γ.ker) := by
      rw [← hMker]
      exact Subgroup.card_le_of_le (inf_le_inf_right _ le_sup_left)
    omega
  have hB'c : 3 ^ 6 * Nat.card (Subgroup.zpowers s) ≤ Nat.card B' := by
    have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker Γ B'
    rw [hcardV, hB'ker] at h
    rw [← h]
    ring_nf
    exact le_refl _
  have he₁hyp : (Pi.single (highNode .E6) 1 : Fin Tag.E6.rank → ZMod 3) ∈
      CFSG.StandardType.NoOffRest.hypE6 :=
    CFSG.StandardType.NoOffRest.mem_hypE6.2 (by decide)
  have hVB' : vHyp ζ hζ ≤ B'.map Γ := hΓB' ▸ le_sup_left
  have hd₁ : diag3 ζ hζ (Multiplicative.ofAdd (Pi.single (highNode .E6) 1)) ∈ B'.map Γ :=
    hVB' ⟨Multiplicative.ofAdd ⟨_, he₁hyp⟩, rfl⟩
  have hdy : diag3 ζ hζ (Multiplicative.ofAdd yHyp) ∈ B'.map Γ :=
    hVB' ⟨Multiplicative.ofAdd ⟨_, yHyp_mem_hypE6⟩, rfl⟩
  have hB'4 : 3 ^ 4 ≤ Nat.card B' := by
    refine le_trans ?_ hB'c
    calc 3 ^ 4 ≤ 3 ^ 6 := by norm_num
      _ ≤ 3 ^ 6 * Nat.card (Subgroup.zpowers s) := Nat.le_mul_of_pos_right _ Nat.card_pos
  have hW := actData_of_diagAct_yHyp hK2 hζo hζ σ Γ hB'ker hB'4 hBV hd₁ hdy
  have hconc := concA_of_actData_quot hS hperf hcore hB'el (by rw [← hΓker]; exact hB'ker) hπ
    hπZ hΓ hW
  have hle : B' ≤ Subgroup.centralizer ({t} : Set Ω) := by
    refine sup_le (fun m hm => Subgroup.mem_centralizer_singleton_iff.2 (htM m hm))
      ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2 htb))
  have hB'T : B' ≤ Subgroup.normalizer (Subgroup.zpowers t : Set Ω) := by
    intro g hg
    refine CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.mem_normalizer_of_forall_comm
      fun k hk => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    exact Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hle hg)) n
  exact concA_of_concA_of_card_le hconc (hBle.trans hB'c)
    (CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.zpowers_ne_bot_of_ne_one ht1)
    (CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.isPGroup_two_zpowers_of_sq ht2) hB'T

theorem concA_of_vAd_image_quot {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [Finite K]
    (hK2 : ringChar K ≠ 2) (h3 : 3 ∣ Nat.card K - 1) (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hB : IsElemAbelian 3 B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) (hB4 : 3 ^ 4 ≤ Nat.card B)
    {π : ↥S →* ↥(adjointGroup .E6 K)} (hπ : Function.Surjective π)
    (hπZ : π.ker ≤ Subgroup.center ↥S) {Γ : Ω →* MulAut ↥(adjointGroup .E6 K)}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 b⟩)
    (hΓker : Γ.ker = centModSubgroup 3 S) {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    (hI : B.map Γ ≤ (hatAut .E6 K).range) (h6 : 3 ^ 6 ≤ Nat.card (B.map Γ)) :
    S267ConcA 3 S B := by
  obtain ⟨γ, -, hγ⟩ :=
    exists_conj_eq_vAd h3 hζo hζ (CFSG.SectionRank.isElemAbelian_map hB Γ) hI h6
  set Γ' := (MulAut.conj γ).toMonoidHom.comp Γ with hΓ'def
  have hBV' : B.map Γ' = vAd ζ hζ := by rw [hΓ'def, ← Subgroup.map_map, hγ]
  have hker' : Γ'.ker = centModSubgroup 3 S := by rw [hΓ'def, ker_conj_comp, hΓker]
  have hBV : ∀ x ∈ B, ∃ z, ∃ k : ℕ,
      Γ' x = diag3 ζ hζ z * entrywiseAdjointAut .E6 (RingEquiv.refl K) ^ k := by
    intro x hx
    have hmem : Γ' x ∈ vAd ζ hζ := hBV' ▸ ⟨x, hx, rfl⟩
    obtain ⟨z, hz⟩ := hmem
    exact ⟨z, 0, by rw [pow_zero, mul_one, hz]⟩
  have hW := actData_of_diagAct_yHyp hK2 hζo hζ (RingEquiv.refl K) Γ'
    (by rw [hker']; exact hBC) hB4 hBV (by rw [hBV']; exact ⟨_, rfl⟩) (by rw [hBV']; exact ⟨_, rfl⟩)
  exact concA_of_actData_quot hS hperf hcore hB hBC (π := γ.toMonoidHom.comp π)
    (γ.surjective.comp hπ) (by rw [ker_comp_mulEquiv]; exact hπZ) (quot_transport hS hΓ γ) hW

theorem concA_of_outer_elt_quot {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [Finite K]
    (hK2 : ringChar K ≠ 2) (h3 : 3 ∣ Nat.card K - 1) (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hB : IsElemAbelian 3 B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) (hB4 : 3 ^ 4 ≤ Nat.card B)
    {π : ↥S →* ↥(adjointGroup .E6 K)} (hπ : Function.Surjective π)
    (hπZ : π.ker ≤ Subgroup.center ↥S) {Γ : Ω →* MulAut ↥(adjointGroup .E6 K)}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 b⟩)
    (hΓker : Γ.ker = centModSubgroup 3 S) {b : Ω} (hbB : b ∈ B)
    (hbI : Γ b ∉ (hatAut .E6 K).range) : S267ConcA 3 S B := by
  classical
  haveI : Finite ↥(adjointGroup .E6 K) := generated_group_finite .E6 K
  haveI : Finite (MulAut ↥(adjointGroup .E6 K)) :=
    Finite.of_injective (fun f : MulAut ↥(adjointGroup .E6 K) =>
      (f : ↥(adjointGroup .E6 K) → ↥(adjointGroup .E6 K))) DFunLike.coe_injective
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hb3 : Γ b ^ 3 = 1 := by rw [← map_pow, hB.2 b hbB, map_one]
  have hbI' : Γ b ∉ CFSG.HardMathSupport.Timmesfeld.CrossChar.e6Inndiag K := by
    intro h
    apply hbI
    rw [hatAut_range_eq_sup]
    exact h
  obtain ⟨σ, hσ, -, ψ, hψ⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_conj_entrywise_of_not_mem_e6Inndiag hℓ n.pos
      K hK Nat.prime_three (by norm_num) hb3 hbI'
  set π₁ := ψ.toMonoidHom.comp π with hπ₁def
  set Γ₁ := (MulAut.conj ψ).toMonoidHom.comp Γ with hΓ₁def
  have hπ₁ : Function.Surjective π₁ := ψ.surjective.comp hπ
  have hπ₁Z : π₁.ker ≤ Subgroup.center ↥S := by rw [hπ₁def, ker_comp_mulEquiv]; exact hπZ
  have hΓ₁ := quot_transport hS hΓ ψ
  set s := entrywiseAdjointAut .E6 σ with hs
  have hΓ₁b : Γ₁ b = s := hψ
  have hker₁ : Γ₁.ker = centModSubgroup 3 S := by rw [hΓ₁def, ker_conj_comp, hΓker]
  have hIn := hatAut_range_normal K
  have hsI : s ∉ (hatAut .E6 K).range := by
    intro h
    apply hbI
    have e : Γ b = ψ⁻¹ * s * ψ⁻¹⁻¹ := by rw [← hψ]; group
    rw [e]
    exact hIn.conj_mem s h ψ⁻¹
  have hσ3 : σ ^ 3 = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hs3 : s ^ 3 = 1 := by
    rw [hs, ← entrywiseAdjointAut_pow, hσ3]
    exact map_one (entrywiseAdjointAutHom (τ := .E6) (K := K))
  obtain ⟨ζ, hζo, hσζ⟩ := exists_orderOf_eq_fixSubfield Nat.prime_three hσ h3
  have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hbout : ∀ k : ℕ, s ^ k ∈ (hatAut .E6 K).range → b ^ k = 1 := by
    intro k hk
    obtain ⟨m, rfl⟩ := three_dvd_of_pow_mem hs3 hsI hk
    rw [pow_mul, hB.2 b hbB, one_pow]
  have hscard : Nat.card (Subgroup.zpowers s) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hs3 (fun h => hsI (h ▸ one_mem _))
  have hĀel : IsElemAbelian 3 (B.map Γ₁) := CFSG.SectionRank.isElemAbelian_map hB Γ₁
  have hBΓ₁ := card_eq_card_map_mul_three (B := B) hker₁ hBC
  have hĀle := card_le_three_mul_card_inf_hatAut hĀel
  by_cases h6 : 3 ^ 6 ≤ Nat.card ↥(B.map Γ₁ ⊓ (hatAut .E6 K).range)
  ·
    set Ā₁ := B.map Γ₁ ⊓ (hatAut .E6 K).range with hĀ₁
    have hĀ₁el : IsElemAbelian 3 Ā₁ := hĀel.mono inf_le_left
    have hĀ₁6 : Nat.card Ā₁ = 3 ^ 6 :=
      le_antisymm (card_le_of_le_hatAut h3 hĀ₁el inf_le_right) h6
    set N := (hatAut .E6 K).range ⊓
      Subgroup.centralizer ({s} : Set (MulAut ↥(adjointGroup .E6 K))) with hN
    have hVN : vAd ζ hζ ≤ N := by
      intro f hf
      refine ⟨vAd_le_hatAut_range ζ hζ hf, ?_⟩
      obtain ⟨z, rfl⟩ := hf
      exact Subgroup.mem_centralizer_singleton_iff.2 (entrywiseAdjointAut_mul_diag3 hζ hσζ z).symm
    have hA₁N : Ā₁ ≤ N := by
      rintro f ⟨⟨x, hx, rfl⟩, hfI⟩
      refine ⟨hfI, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      rw [← hΓ₁b, ← map_mul, ← map_mul, hB.comm hx hbB]
    have hV3 : IsPGroup 3 ((vAd ζ hζ).subgroupOf N) := fun f => ⟨1, by
      apply Subtype.ext
      apply Subtype.ext
      simpa using (isElemAbelian_vAd ζ hζ).2 _ (Subgroup.mem_subgroupOf.1 f.2)⟩
    have hA3 : IsPGroup 3 (Ā₁.subgroupOf N) := fun f => ⟨1, by
      apply Subtype.ext
      apply Subtype.ext
      simpa using hĀ₁el.2 _ (Subgroup.mem_subgroupOf.1 f.2)⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨P₁, hP₁⟩ := hV3.exists_le_sylow
    obtain ⟨P₂, hP₂⟩ := hA3.exists_le_sylow
    haveI : Finite (Sylow 3 ↥N) := Sylow.finite_of_finiteIndex P₁
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥N) P₂ P₁
    have hgI : (g : MulAut ↥(adjointGroup .E6 K)) ∈ (hatAut .E6 K).range :=
      (Subgroup.mem_inf.1 g.2).1
    have hgC : (g : MulAut ↥(adjointGroup .E6 K)) ∈
        Subgroup.centralizer ({s} : Set (MulAut ↥(adjointGroup .E6 K))) :=
      (Subgroup.mem_inf.1 g.2).2
    set P := (P₁ : Subgroup ↥N).map N.subtype with hP
    have hP3 : IsPGroup 3 P := P₁.isPGroup'.map _
    have hVP : vAd ζ hζ ≤ P := fun f hf =>
      ⟨⟨f, hVN hf⟩, hP₁ (Subgroup.mem_subgroupOf.2 hf), rfl⟩
    set X := Ā₁.map (MulAut.conj (g : MulAut ↥(adjointGroup .E6 K))).toMonoidHom with hX
    have hXP : X ≤ P := by
      rintro _ ⟨f, hf, rfl⟩
      have hfP₂ : (⟨f, hA₁N hf⟩ : ↥N) ∈ (P₂ : Subgroup ↥N) := hP₂ (Subgroup.mem_subgroupOf.2 hf)
      have hgf : g * ⟨f, hA₁N hf⟩ * g⁻¹ ∈ (P₁ : Subgroup ↥N) := by
        rw [← hg, Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hfP₂
      exact ⟨_, hgf, rfl⟩
    have hXI : X ≤ (hatAut .E6 K).range := by
      rintro _ ⟨f, hf, rfl⟩
      exact mul_mem (mul_mem hgI (Subgroup.mem_inf.1 hf).2) (inv_mem hgI)
    have hXel : IsElemAbelian 3 X := CFSG.SectionRank.isElemAbelian_map hĀ₁el _
    have hXc : Nat.card X = 3 ^ 6 := by
      rw [hX, Subgroup.card_map_of_injective (MulAut.conj _).injective, hĀ₁6]
    have hXV : X = vAd ζ hζ := eq_of_le_of_isPGroup h3 hP3 hXI (vAd_le_hatAut_range ζ hζ) hXP
      hVP hXel (isElemAbelian_vAd ζ hζ) hXc (card_vAd hζo hζ)
    set Γ₂ := (MulAut.conj (g : MulAut ↥(adjointGroup .E6 K))).toMonoidHom.comp Γ₁ with hΓ₂def
    have hΓ₂ := quot_transport hS hΓ₁ (g : MulAut ↥(adjointGroup .E6 K))
    have hker₂ : Γ₂.ker = centModSubgroup 3 S := by rw [hΓ₂def, ker_conj_comp, hker₁]
    have hΓ₂x : ∀ x, Γ₂ x = (g : MulAut _) * Γ₁ x * (g : MulAut _)⁻¹ := fun x => rfl
    have hΓ₂b : Γ₂ b = s := by
      rw [hΓ₂x, hΓ₁b, Subgroup.mem_centralizer_singleton_iff.1 hgC, mul_inv_cancel_right]
    have hĀ₂I : B.map Γ₂ ⊓ (hatAut .E6 K).range = vAd ζ hζ := by
      rw [← hXV]
      apply le_antisymm
      · rintro _ ⟨⟨x, hx, rfl⟩, hxI⟩
        refine ⟨Γ₁ x, ⟨⟨x, hx, rfl⟩, ?_⟩, (hΓ₂x x).symm⟩
        have e : Γ₁ x = (g : MulAut _)⁻¹ * Γ₂ x * (g : MulAut _) := by rw [hΓ₂x]; group
        show Γ₁ x ∈ (hatAut .E6 K).range
        rw [e]
        exact mul_mem (mul_mem (inv_mem hgI) (hxI : Γ₂ x ∈ (hatAut .E6 K).range)) hgI
      · rintro _ ⟨f, ⟨⟨x, hx, rfl⟩, hfI⟩, rfl⟩
        refine ⟨⟨x, hx, hΓ₂x x⟩, ?_⟩
        show (g : MulAut _) * Γ₁ x * (g : MulAut _)⁻¹ ∈ (hatAut .E6 K).range
        exact mul_mem (mul_mem hgI (hfI : Γ₁ x ∈ (hatAut .E6 K).range)) (inv_mem hgI)
    have hVB : vAd ζ hζ ≤ B.map Γ₂ := hĀ₂I ▸ inf_le_left
    have hcomm : ∀ f ∈ vAd ζ hζ, ∀ h ∈ Subgroup.zpowers s, f * h = h * f := by
      intro f hf h hh
      obtain ⟨z, rfl⟩ := hf
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      exact (Commute.zpow_left (entrywiseAdjointAut_mul_diag3 hζ hσζ z) m).symm
    have hinf : vAd ζ hζ ⊓ Subgroup.zpowers s = ⊥ := by
      rw [eq_bot_iff]
      rintro f ⟨hf1, hf2⟩
      obtain ⟨k, -, rfl⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen.exists_pow_lt_of_pow_eq_one (by norm_num) hs3
          hf2
      have hk := three_dvd_of_pow_mem hs3 hsI (vAd_le_hatAut_range ζ hζ hf1)
      obtain ⟨m, rfl⟩ := hk
      rw [Subgroup.mem_bot, pow_mul, hs3, one_pow]
    have hsub : vAd ζ hζ ⊔ Subgroup.zpowers s ≤ B.map Γ₂ :=
      sup_le hVB ((Subgroup.zpowers_le).2 ⟨b, hbB, hΓ₂b⟩)
    have hcard : Nat.card (B.map Γ₂) ≤ Nat.card ↥(vAd ζ hζ ⊔ Subgroup.zpowers s) := by
      have h := card_le_three_mul_card_inf_hatAut (CFSG.SectionRank.isElemAbelian_map hB Γ₂)
      rw [hĀ₂I, card_vAd hζo hζ] at h
      rw [CFSG.CGT.T75P.card_sup_of_commute hcomm hinf, card_vAd hζo hζ, hscard]
      linarith
    have heq := Subgroup.eq_of_le_of_card_ge hsub hcard
    have hĀ₂ : B.map Γ₂ ≤ Subgroup.closure (Set.range (diag3 ζ hζ) ∪ {s}) := by
      rw [← heq]
      refine sup_le ?_ ?_
      · rintro _ ⟨z, rfl⟩
        exact Subgroup.subset_closure (Or.inl ⟨z, rfl⟩)
      · exact (Subgroup.zpowers_le).2 (Subgroup.subset_closure (Or.inr rfl))
    have hBV : ∀ x ∈ B, ∃ z, ∃ k : ℕ, Γ₂ x = diag3 ζ hζ z * s ^ k := fun x hx =>
      exists_eq_of_mem_closure_diag3 hζ hσζ hσ3 (hĀ₂ ⟨x, hx, rfl⟩)
    have hW := actData_of_diagAct_yHyp hK2 hζo hζ σ Γ₂ (by rw [hker₂]; exact hBC) hB4 hBV
      (hVB ⟨_, rfl⟩) (hVB ⟨_, rfl⟩)
    exact concA_of_actData_quot hS hperf hcore hB hBC
      (π := (g : MulAut ↥(adjointGroup .E6 K)).toMonoidHom.comp π₁)
      ((g : MulAut ↥(adjointGroup .E6 K)).surjective.comp hπ₁)
      (by rw [ker_comp_mulEquiv]; exact hπ₁Z) hΓ₂ hW
  ·
    have hĀ₁ := card_le_pow_five_of_not_le (hĀel.mono inf_le_left) h6
    refine concA_of_lift hK2 hS hperf hcore hB hπ₁ hπ₁Z hΓ₁ hker₁ hζo hζ hσζ hσ3 hbB hΓ₁b hbout ?_
      (hypLift hK2 h3 hS hperf hcore hB hBC hπ₁ hπ₁Z hΓ₁ hker₁ hζo hζ hσζ hbB hΓ₁b)
    rw [hscard, hBΓ₁]
    calc Nat.card (B.map Γ₁) * 3 ≤ 3 * Nat.card ↥(B.map Γ₁ ⊓ (hatAut .E6 K).range) * 3 :=
          Nat.mul_le_mul_right _ hĀle
      _ ≤ 3 * 3 ^ 5 * 3 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hĀ₁)
      _ = 3 ^ 6 * 3 := by norm_num

theorem concA_E6_three_of_quot {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω} [Finite K]
    (hK2 : ringChar K ≠ 2) (h3 : 3 ∣ Nat.card K - 1) (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore 3 ↥S = ⊥) (hB : IsElemAbelian 3 B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) (hB4 : 3 ^ 4 ≤ Nat.card B)
    {π : ↥S →* ↥(adjointGroup .E6 K)} (hπ : Function.Surjective π)
    (hπZ : π.ker ≤ Subgroup.center ↥S) {Γ : Ω →* MulAut ↥(adjointGroup .E6 K)}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 b⟩)
    (hΓker : Γ.ker = centModSubgroup 3 S) : S267ConcA 3 S B := by
  by_cases hout : ∃ b ∈ B, Γ b ∉ (hatAut .E6 K).range
  · obtain ⟨b, hbB, hbI⟩ := hout
    exact concA_of_outer_elt_quot hK2 h3 hS hperf hcore hB hBC hB4 hπ hπZ hΓ hΓker hbB hbI
  · push Not at hout
    have hI : B.map Γ ≤ (hatAut .E6 K).range := by
      rintro _ ⟨b, hb, rfl⟩
      exact hout b hb
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨ζ, hζo⟩ : ∃ ζ : Kˣ, orderOf ζ = 3 :=
      exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact h3)
    have hζ : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
    by_cases h6 : 3 ^ 6 ≤ Nat.card (B.map Γ)
    · exact concA_of_vAd_image_quot hK2 h3 hS hperf hcore hB hBC hB4 hπ hπZ hΓ hΓker hζo hζ hI h6
    · have hĀ := card_le_pow_five_of_not_le (CFSG.SectionRank.isElemAbelian_map hB Γ) h6
      have hBΓ := card_eq_card_map_mul_three (B := B) hΓker hBC
      have h1 : entrywiseAdjointAut .E6 (RingEquiv.refl K) = 1 :=
        map_one (entrywiseAdjointAutHom (τ := .E6) (K := K))
      have hΓ1 : Γ 1 = entrywiseAdjointAut .E6 (RingEquiv.refl K) := by rw [map_one, h1]
      refine concA_of_lift hK2 hS hperf hcore hB hπ hπZ hΓ hΓker hζo hζ (σ := RingEquiv.refl K)
        rfl (one_pow 3) (one_mem B) hΓ1 (fun k _ => one_pow k) ?_
        (hypLift hK2 h3 hS hperf hcore hB hBC hπ hπZ hΓ hΓker hζo hζ rfl (one_mem B) hΓ1)
      rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot, mul_one, hBΓ]
      calc Nat.card (B.map Γ) * 3 ≤ 3 ^ 5 * 3 := Nat.mul_le_mul_right _ hĀ
        _ = 3 ^ 6 := by norm_num

end Quot

section Head


theorem chevQuotHom_ker_le_center {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {p : ℕ}
    (hcore : GLAPPrimeCore p ↥S = ⊥) : (chevQuotHom p S).ker ≤ Subgroup.center ↥S := by
  intro x hx
  refine Subgroup.mem_center_iff.2 fun s => ?_
  have hx' : pQuotHom p S x ∈ Subgroup.center (PQuot p S) := by
    rw [MonoidHom.mem_ker] at hx
    exact (QuotientGroup.eq_one_iff _).1 hx
  have hinj : Function.Injective (pQuotHom p S) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_pQuotHom, hcore]
  apply hinj
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.1 hx' (pQuotHom p S s)

end Head

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.E6One

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem concA_badExcCore_E6_three_of_mod_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqp : q ≠ p) {Ω : Type} [Group Ω] [Finite Ω]
    (hK : CFSG.Open.IsKGroup Ω) {S B : Subgroup Ω} (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hcore : GLAPPrimeCore p ↥S = ⊥) (hB : IsElemAbelian p B) (hSB : S ⊔ B = ⊤)
    (hrank : p ^ GLATwoLocalRank p Ω ≤ Nat.card B) (hB4 : p ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hp3B : ¬ (p = 3 ∧ Nat.card B = 3 ^ 4))
    {Q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.E6 Q).Valid)
    (hchar : (TauCeti.LieTypeIndex.E6 Q).characteristic = q)
    (e : PSimple p S ≃* (TauCeti.CFSGIndex.lie ⟨.E6 Q, hv⟩).Group) (hd : p ∣ Q.card ^ 2 - 1)
    (hp3 : p = 3) (h1 : p ∣ Q.card - 1)
    (hHq : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
      Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧ GLATwoLocalRank q K' ≤ CFSG.Open.pRank p B) :
    S267ConcA p S B ∨ S267ConcBCDE p q S B := by
  subst hp3
  rw [TauCeti.LieTypeIndex.characteristic_E6] at hchar
  subst hchar
  obtain ⟨K, _, _, hKc, hKchar, ⟨eC⟩⟩ := CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 Q hv
  haveI := hKchar
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K Q.p]; exact hq2
  have h3 : 3 ∣ Nat.card K - 1 := by rwa [hKc]
  set e₀ := e.trans eC with he₀
  obtain ⟨Γ, hΓ, hΓker⟩ := ModelGen.exists_actHom_pSimple hS hperf e₀
  refine Or.inl (E6One.concA_E6_three_of_quot hK2 h3 hS hperf hcore hB hBC hB4
    (π := e₀.toMonoidHom.comp (chevQuotHom 3 S)) (e₀.surjective.comp (chevQuotHom_surjective 3 S))
    ?_ hΓ hΓker)
  rw [E6One.ker_comp_mulEquiv]
  exact E6One.chevQuotHom_ker_le_center hcore

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
