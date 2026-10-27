module

public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Defs
public import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
public import CFSG.RankThree.PartTwo.KFacts.L34NormalizerMax
public import CFSG.GH74.KGroups.L34Aut
public import Certificates.Certificate13510
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Triple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I28_8

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Sporadic.Schreier
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem l34_seven_spec
    {a : Equiv.Perm (Fin 42)} (ha : a ∈ QA.originalSubgroup)
    (ha2 : a * a = 1) (haP : a ∉ QP.originalSubgroup) :
    ∃ q ∈ QP.originalSubgroup, orderOf q = 7 ∧ (a * q = q * a ∨ a * q * a⁻¹ = q⁻¹) := by
  have h := Certificates.certificate13510
  unfold l34SevenCheck at h
  have h1 := List.all_eq_true.1 h a ((mem_elemsT QA QA_ok a).2 ha)
  have hsift : QP.sift a 0 = false := by
    by_contra hne
    exact haP ((mem_iff_sift QP QP_ok a).2 (by simpa using hne))
  simp only [ha2, ne_eq, not_true_eq_false, decide_false, hsift, Bool.false_or, List.any_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, List.mem_filter] at h1
  obtain ⟨q, ⟨hq, hq7⟩, hc⟩ := h1
  exact ⟨q, (mem_elemsT QP QP_ok q).1 hq, (orderIs_iff _ (by norm_num)).1 hq7, hc⟩


theorem mem_normalizer_map' {A B : Type*} [Group A] [Group B] (ψ : A ≃* B) {S : Subgroup A} {e : A}
    (he : e ∈ Subgroup.normalizer (S : Set A)) :
    ψ e ∈ Subgroup.normalizer ((S.map ψ.toMonoidHom : Subgroup B) : Set B) := by
  rw [Subgroup.mem_normalizer_iff] at he ⊢
  intro h
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  have := he (ψ.symm h)
  simpa [map_mul, map_inv] using this

theorem exists_equiv_projectiveSL' {Y : Type} [Group Y] (h : IsLThreeFour Y) :
    ∃ (k : Type) (_ : Field k), Nat.card k = 4 ∧ Nonempty (Y ≃* projectiveSL 3 k) := by
  obtain ⟨F, hF, _, hcard, ⟨e⟩⟩ := h
  exact ⟨F, hF, hcard, ⟨(e.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 F)⟩⟩

theorem exists_equiv_P21 {Y : Type} [Group Y] (h : IsLThreeFour Y) :
    Nonempty (Y ≃* QP21.originalSubgroup) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  obtain ⟨e4⟩ := equiv_psl_P21
  let f : F ≃+* GF4 :=
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField F 2 2 (by norm_num) (by rw [hcard]; norm_num)).trans
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField GF4 2 2 (by norm_num) card_F).symm
  exact ⟨(e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).trans
    ((CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv f (Fin 3)).trans e4)⟩

open CFSG.RankThree.PartTwo.KFacts.L34 CFSG.RankThree.PartTwo.KFacts in
theorem exists_tau {G0 : Type} [Group G0] (h : IsLThreeFour G0) {D : Subgroup G0}
    (hD : Nat.card D = 9) {X : Subgroup (MulAut G0)} (hX : ¬ 3 ∣ Nat.card X)
    (hDX : ∀ d ∈ D, MulAut.conj d ∈ Subgroup.normalizer (X : Set (MulAut G0))) :
    X = ⊥ ∨ ∃ τ : MulAut G0, X = Subgroup.zpowers τ ∧ τ * τ = 1 ∧
      (¬ ∃ g : G0, τ = MulAut.conj g) ∧
      ∀ x : G0, τ x = x ↔ x ∈ Subgroup.normalizer (D : Set G0) := by
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := exists_equiv_projectiveSL' h
  have hfin : Finite k := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hk
  set ψ : MulAut G0 ≃* MulAut (projectiveSL 3 k) := MulAut.congr φ with hψ
  set E : Subgroup (projectiveSL 3 k) := D.map φ.toMonoidHom with hE
  have hE9 : Nat.card E = 9 := by
    rw [hE, Subgroup.card_map_of_injective φ.injective, hD]
  have hX' : ¬ 3 ∣ Nat.card (X.map ψ.toMonoidHom) := by
    rw [Subgroup.card_map_of_injective ψ.injective]; exact hX
  have hEX : ∀ e ∈ E, MulAut.conj e ∈
      Subgroup.normalizer ((X.map ψ.toMonoidHom : Subgroup _) : Set (MulAut (projectiveSL 3 k))) := by
    rintro _ ⟨d, hd, rfl⟩
    have h1 : ψ (MulAut.conj d) = MulAut.conj (φ d) := by
      rw [hψ]; exact CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj φ d
    have h2 := mem_normalizer_map' ψ (hDX d hd)
    rw [h1] at h2
    exact h2
  rcases eq_bot_or_eq_zpowers_graphField hk hE9 hX' hEX with hbot | ⟨τ, hXτ, hτ1, hτ2, hgf, hfix⟩
  · left
    exact Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective (by rw [hbot, Subgroup.map_bot])
  · right
    have hτinv : ψ.symm τ * ψ.symm τ = 1 := by
      apply ψ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hτ2, map_one]
    refine ⟨ψ.symm τ, ?_, hτinv, ?_, ?_⟩
    · apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
      rw [hXτ, MonoidHom.map_zpowers]
      simp
    · rintro ⟨g, hg⟩
      refine not_isInnerAut_of_isGraphField hk hgf ⟨φ g, ?_⟩
      have h1 : ψ (MulAut.conj g) = MulAut.conj (φ g) := by
        rw [hψ]; exact CFSG.RankThree.PartTwo.KFacts.congr_mulAutConj φ g
      rw [← h1, ← hg, MulEquiv.apply_symm_apply]
    · intro x
      have hnorm := autFixed_eq_normalizer_of_isGraphField hk hgf hE9 hfix
      have h1 : ψ.symm τ x = φ.symm (τ (φ x)) := by
        rw [hψ]; simp
      have h2 : ψ.symm τ x = x ↔ φ x ∈ Subgroup.normalizer (E : Set _) := by
        rw [h1, φ.symm_apply_eq, ← hnorm]
        exact (CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModel.mem_autFixed).symm
      rw [h2, hE, ← Subgroup.map_equiv_normalizer_eq D φ]
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [← φ.injective hyx]
      · intro hx
        exact ⟨x, hx, rfl⟩

theorem exists_seven
    {G0 : Type} [Group G0] (e : G0 ≃* QP.originalSubgroup)
    {τ : MulAut G0} (hτ : τ * τ = 1) (hout : ¬ ∃ g : G0, τ = MulAut.conj g) :
    ∃ x : G0, orderOf x = 7 ∧ (τ x = x ∨ τ x = x⁻¹) := by
  obtain ⟨M, hP, hA⟩ := autModel e
  have ha : (M.Φ τ : Equiv.Perm (Fin 42)) ∈ QA.originalSubgroup := hA ▸ (M.Φ τ).2
  have ha2 : (M.Φ τ : Equiv.Perm (Fin 42)) * (M.Φ τ : Equiv.Perm (Fin 42)) = 1 := by
    rw [← M.Φ_mul, hτ, M.Φ_one]
  have haP : (M.Φ τ : Equiv.Perm (Fin 42)) ∉ QP.originalSubgroup := by
    intro hmem
    obtain ⟨g, hg⟩ := M.inner_of_mem τ (hP ▸ hmem)
    exact hout ⟨g, MulEquiv.ext fun x => by rw [hg x]; simp⟩
  obtain ⟨q, hq, hq7, hc⟩ := l34_seven_spec ha ha2 haP
  have hqM : q ∈ M.P := hP ▸ hq
  refine ⟨M.e.symm ⟨q, hqM⟩, ?_, ?_⟩
  · exact (MulEquiv.orderOf_eq M.e.symm _).trans ((Subgroup.orderOf_coe (⟨q, hqM⟩ : M.P)).symm.trans hq7)
  · have hspec := M.spec τ (M.e.symm ⟨q, hqM⟩)
    rw [MulEquiv.apply_symm_apply] at hspec
    rcases hc with hc | hc
    · left
      apply M.e.injective
      apply Subtype.ext
      rw [hspec, MulEquiv.apply_symm_apply]
      simp only
      rw [hc, mul_inv_cancel_right]
    · right
      apply M.e.injective
      apply Subtype.ext
      rw [hspec, map_inv, MulEquiv.apply_symm_apply]
      simp only [Subgroup.coe_inv]
      rw [hc]

theorem rho_mem_normalizer {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal] {T : Subgroup Y} {g : Y}
    (hg : g ∈ Subgroup.normalizer (T : Set Y)) :
    (MulAut.conjNormal (H := K) g) ∈
      Subgroup.normalizer ((T.map (MulAut.conjNormal (H := K)) : Subgroup (MulAut ↥K)) : Set (MulAut ↥K)) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨g * t * g⁻¹, (hg t).1 ht, ?_⟩
    simp
  · rintro ⟨t, ht, hth⟩
    refine ⟨g⁻¹ * t * g, (hg (g⁻¹ * t * g)).2 (by simpa [mul_assoc] using ht), ?_⟩
    have : h = (MulAut.conjNormal (H := K) g)⁻¹ * (MulAut.conjNormal (H := K) g * h *
        (MulAut.conjNormal (H := K) g)⁻¹) * MulAut.conjNormal (H := K) g := by group
    rw [this, ← hth]
    simp [mul_assoc]

theorem zpowers_involution_cases {M : Type*} [Group M] {τ : M} (h : τ * τ = 1) {m : M}
    (hm : m ∈ Subgroup.zpowers τ) : m = 1 ∨ m = τ := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
  have h2 : τ ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact h
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left; rw [zpow_mul, h2, one_zpow]
  · right; rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem l34Facts_holds :
    L34Facts := by
  intro Y _ _ K T B hKn hL hT hBT h9
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ : Y →* MulAut ↥K := MulAut.conjNormal (H := K) with hρ
  have hρ1 : ∀ (g : Y) (x : ↥K), ((ρ g x : ↥K) : Y) = g * x * g⁻¹ := fun g x =>
    MulAut.conjNormal_apply g x
  set D : Subgroup ↥K := (B ⊓ K).subgroupOf K with hDdef
  have hD : Nat.card D = 9 := by
    rw [← h9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hX : ¬ 3 ∣ Nat.card (T.map ρ) := by
    intro h3
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hT
    have h4 : Nat.card (T.map ρ) ∣ 2 ^ n := hn ▸ Subgroup.card_map_dvd (H := T) ρ
    exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3.trans h4))) (by norm_num)
  have hDX : ∀ d ∈ D, MulAut.conj d ∈
      Subgroup.normalizer ((T.map ρ : Subgroup (MulAut ↥K)) : Set (MulAut ↥K)) := by
    intro d hd
    have hdB : (d : Y) ∈ B := (Subgroup.mem_subgroupOf.1 hd).1
    have h1 : MulAut.conj d = ρ (d : Y) := by
      ext x
      rw [hρ1]
      simp
    rw [h1]
    exact rho_mem_normalizer (hBT hdB)
  rcases exists_tau hL hD hX hDX with hbot | ⟨τ, hXτ, hτ2, hout, hfix⟩
  · left
    intro k hk t ht
    have h1 : ρ t = 1 := by
      have : ρ t ∈ T.map ρ := ⟨t, ht, rfl⟩
      rw [hbot] at this
      exact this
    have h2 := congrArg (fun m : MulAut ↥K => ((m ⟨k, hk⟩ : ↥K) : Y)) h1
    simp only [hρ1, MulAut.one_apply] at h2
    show t * k = k * t
    rw [show t * k = (t * k * t⁻¹) * t by group, h2]
  · obtain ⟨ψ⟩ := exists_equiv_P21 hL
    obtain ⟨π⟩ := equiv_P21_P
    obtain ⟨x, hx7, hxτ⟩ := exists_seven (ψ.trans π) hτ2 hout
    have hxne : τ x ≠ x := by
      intro hx
      have hxN : x ∈ Subgroup.normalizer (D : Set ↥K) := (hfix x).1 hx
      have h72 := CFSG.RankThree.PartTwo.KFacts.L34Max.card_normalizer_of_mulEquiv ψ hD
      have h1 := orderOf_dvd_natCard (⟨x, hxN⟩ : Subgroup.normalizer (D : Set ↥K))
      rw [h72] at h1
      have h2 : orderOf x ∣ 72 := by
        rw [← (Subgroup.orderOf_coe (⟨x, hxN⟩ : Subgroup.normalizer (D : Set ↥K)))] at h1
        exact h1
      rw [hx7] at h2
      omega
    have hτx : τ x = x⁻¹ := hxτ.resolve_left hxne
    set x' : Y := (x : Y) with hx'
    set Q : Subgroup Y := Subgroup.zpowers x' with hQ
    have hQK : Q ≤ K := (Subgroup.zpowers_le).2 x.2
    have hQcard : Nat.card Q = 7 := by
      rw [hQ, Nat.card_zpowers, hx', Subgroup.orderOf_coe, hx7]
    have hρT : ∀ t ∈ T, ρ t = 1 ∨ ρ t = τ := fun t ht =>
      zpowers_involution_cases hτ2 (hXτ ▸ (⟨t, ht, rfl⟩ : ρ t ∈ T.map ρ))
    have hact : ∀ t ∈ T, t * x' * t⁻¹ = x' ∨ t * x' * t⁻¹ = x'⁻¹ := by
      intro t ht
      have h1 := hρ1 t x
      rcases hρT t ht with h | h
      · left; rw [h] at h1; simpa using h1.symm
      · right; rw [h, hτx] at h1; simpa using h1.symm
    have hconjQ : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := by
      intro t ht q hq
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      have : t * x' ^ m * t⁻¹ = (t * x' * t⁻¹) ^ m := by
        simp
      rw [this]
      rcases hact t ht with h | h <;> rw [h]
      · exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
      · exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) _
    have hTQ : T ≤ Subgroup.normalizer (Q : Set Y) := fun t ht =>
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.mem_normalizer_of_conj_mem
        (hconjQ t ht) (fun q hq => by simpa using hconjQ t⁻¹ (inv_mem ht) q hq)
    obtain ⟨t0, ht0, hρt0⟩ : ∃ t0 ∈ T, ρ t0 = τ := by
      have : τ ∈ T.map ρ := hXτ ▸ Subgroup.mem_zpowers τ
      exact this
    have hinv : ∀ q ∈ Q, t0 * q * t0⁻¹ = q⁻¹ := by
      intro q hq
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
      have h1 : t0 * x' * t0⁻¹ = x'⁻¹ := by
        have := hρ1 t0 x
        rw [hρt0, hτx] at this
        simpa using this.symm
      have : t0 * x' ^ m * t0⁻¹ = (t0 * x' * t0⁻¹) ^ m := by
        simp
      rw [this, h1, inv_zpow', zpow_neg]
    right
    refine ⟨Q, hQK, hQcard, hTQ, ⟨t0, ht0, hinv⟩, ?_⟩
    apply le_antisymm (sup_le inf_le_right hQK)
    set W : Subgroup Y := (Subgroup.centralizer (T : Set Y) ⊓ K) ⊔ Q with hW
    have hfixcent : ∀ k : ↥K, τ k = k → (k : Y) ∈ Subgroup.centralizer (T : Set Y) := by
      intro k hk t ht
      have h1 := hρ1 t k
      have h2 : t * k * t⁻¹ = k := by
        rcases hρT t ht with h | h
        · rw [h] at h1; simpa using h1.symm
        · rw [h, hk] at h1; exact h1.symm
      show t * k = k * t
      rw [show t * k = (t * k * t⁻¹) * t by group, h2]
    have hWk : W.subgroupOf K = ⊤ := by
      by_contra hne
      have hEY : Subgroup.normalizer (D : Set ↥K) ≤ W.subgroupOf K := by
        intro k hk
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_sup_left ⟨hfixcent k ((hfix k).2 hk), k.2⟩
      have heq := CFSG.RankThree.PartTwo.KFacts.L34Max.eq_normalizer_of_mulEquiv ψ hD hEY hne
      have hxW : x ∈ W.subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      rw [heq] at hxW
      exact hxne ((hfix x).2 hxW)
    intro k hk
    have : (⟨k, hk⟩ : ↥K) ∈ W.subgroupOf K := hWk ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this

end CFSG.HardMathSupport.Solomon.Coordinator.I28_8
