module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410Inner
public import CFSG.LocalAnalysis.ComponentClassification.Foote47Gen

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools GSThmB
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem footeAct_mem_range_of_mem_sup {M : Subgroup G}
    (ε : M ⧸ pPrimeCore 2 M ≃* L ⧸ Open.fusionZStar L) {x : ↥(normalizer (M : Set G))}
    (hx : (x : G) ∈ M ⊔ coreActionKernel M) :
    footeAct ε x ∈ (MulAut.conj : (L ⧸ Open.fusionZStar L) →* _).range := by
  obtain ⟨m, hm, c, hc, hmc⟩ : ∃ m ∈ M, ∃ c ∈ coreActionKernel M, m * c = (x : G) := by
    have h1 : (x : G) ∈ ((M : Set G) * (coreActionKernel M : Set G)) := by
      rw [← coe_mul_of_left_le_normalizer_right M (coreActionKernel M)
        (le_normalizer.trans (normalizer_le_normalizer_coreActionKernel M))]
      exact hx
    obtain ⟨m, hm, c, hc, hmc⟩ := Set.mem_mul.mp h1
    exact ⟨m, hm, c, hc, hmc⟩
  have hmN : m ∈ normalizer (M : Set G) := le_normalizer hm
  have hcN : c ∈ normalizer (M : Set G) := (mem_coreActionKernel.mp hc).1
  have h1 : x = ⟨m, hmN⟩ * ⟨c, hcN⟩ := Subtype.ext hmc.symm
  rw [h1, map_mul, footeAct_eq_one_of_mem_coreActionKernel ε (x := ⟨c, hcN⟩) hc, mul_one]
  refine ⟨ε ((⟨m, hm⟩ : ↥M) : M ⧸ pPrimeCore 2 M), ?_⟩
  rw [footeAct, MonoidHom.comp_apply, oddBarConj_eq_conj' (⟨m, hm⟩ : ↥M) hmN]
  show MulAut.conj (ε ((⟨m, hm⟩ : ↥M) : M ⧸ pPrimeCore 2 M)) =
    MulAut.congr ε (MulAut.conj ((⟨m, hm⟩ : ↥M) : M ⧸ pPrimeCore 2 M))
  rw [MulAut.congr_conj]

theorem perm7_card_le_eight_of_comm {T : Subgroup (Equiv.Perm (Fin 7))} (hTp : IsPGroup 2 T)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : Nat.card T ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hTp
  have hcard : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hdvd : 2 ^ k ∣ 5040 := by
    rw [← hk, ← hcard]
    exact T.card_subgroup_dvd_card
  have hk4 : k ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ∣ 5040 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  by_contra hlt
  have hk4' : k = 4 := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hidx : ¬ 2 ∣ T.index := by
    have h1 := T.card_mul_index
    rw [hk, hk4', hcard] at h1
    omega
  set P := hTp.toSylow hidx
  obtain ⟨H, hH2, x, hx, y, hy, hxy⟩ := AutL2Facts.exists_noncomm_two_subgroup_a7
  set H' := H.map (alternatingGroup (Fin 7)).subtype
  have hH'2 : IsPGroup 2 H' := hH2.map _
  obtain ⟨Q, hQ⟩ := hH'2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 7)) Q P
  have hmem : ∀ z ∈ H, g * (z : Equiv.Perm (Fin 7)) * g⁻¹ ∈ T := by
    intro z hz
    have h1 : g * (z : Equiv.Perm (Fin 7)) * g⁻¹ ∈ (P : Subgroup (Equiv.Perm (Fin 7))) := by
      rw [← hg, AutL2Facts.mem_smul_sylow_iff_conj,
        show g⁻¹ * (g * (z : Equiv.Perm (Fin 7)) * g⁻¹) * g = (z : Equiv.Perm (Fin 7)) by group]
      exact hQ ⟨z, hz, rfl⟩
    exact h1
  have key : ∀ a b c : Equiv.Perm (Fin 7),
      c * a * c⁻¹ * (c * b * c⁻¹) = c * b * c⁻¹ * (c * a * c⁻¹) → a * b = b * a := by
    intro a b c h
    calc a * b = c⁻¹ * (c * a * c⁻¹ * (c * b * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * b * c⁻¹ * (c * a * c⁻¹)) * c := by rw [h]
      _ = b * a := by group
  apply hxy
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact key _ _ g (hT _ (hmem x hx) _ (hmem y hy))

theorem card_le_eight_of_isMulCommutative
    (h : FooteSec4 G L) (hFI : FooteFourgroupInner)
    (htype : Nonempty (L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ^ f = 9 ∧ Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 2 p f)
    {M : Subgroup G} (hM : IsFooteM L M) {T : Subgroup G}
    (hTN : T ≤ normalizer (M : Set G)) (hTp : IsPGroup 2 T)
    (hTC : ∀ x ∈ T, x ∈ coreActionKernel M → x = 1)
    (hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) {E : Subgroup G} (hET : E ≤ T)
    (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8) : Nat.card T ≤ 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨ε⟩⟩ := hM.quotient h
  set N := normalizer (M : Set G) with hN
  set Φ := footeAct ε with hΦ
  have hinj : Function.Injective (Φ.comp (T.subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    exact hTC _ x.2 (mem_coreActionKernel_of_footeAct_eq_one ε hx)
  have himage : ∀ {A : Type} [Group A] (ψ : MulAut (L ⧸ Open.fusionZStar L) →* A),
      Function.Injective ψ → Nat.card ((T.subgroupOf N).map (ψ.comp Φ)) = Nat.card T := by
    intro A _ ψ hψ
    have hinj' : Function.Injective ((ψ.comp Φ).comp (T.subgroupOf N).subtype) :=
      hψ.comp hinj
    have hr : ((ψ.comp Φ).comp (T.subgroupOf N).subtype).range =
        (T.subgroupOf N).map (ψ.comp Φ) := by rw [MonoidHom.range_comp, range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe hTN).toEquiv
  have hcommute : ∀ {A : Type} [Group A] (ψ : MulAut (L ⧸ Open.fusionZStar L) →* A),
      ∀ a ∈ (T.subgroupOf N).map (ψ.comp Φ), ∀ b ∈ (T.subgroupOf N).map (ψ.comp Φ),
        a * b = b * a := by
    intro A _ ψ
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hTab _ hx _ hy)
  rcases htype with ⟨⟨e⟩⟩ | ⟨p, f, hp, hpf, hlie⟩
  ·
    set Ψ : MulAut (L ⧸ Open.fusionZStar L) ≃* Equiv.Perm (Fin 7) :=
      (MulAut.congr e).trans AutL2Facts.a7AutEquiv.symm with hΨ
    rw [← himage Ψ.toMonoidHom Ψ.injective]
    obtain ⟨k, hk⟩ := hTp.exists_card_eq
    refine perm7_card_le_eight_of_comm (IsPGroup.of_card (n := k) ?_) (hcommute Ψ.toMonoidHom)
    rw [himage Ψ.toMonoidHom Ψ.injective, hk]
  ·
    obtain ⟨-, hf, -, -, F, _, _, hF, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data hlie
    have hF9 : Nat.card F = 3 ^ 2 := by rw [hF, hpf]; norm_num
    have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      ⟨3, 2, Nat.prime_three, by decide, by norm_num, hF9⟩
    have hAut : Nat.card (F ≃+* F) = 2 := AutL2Facts.card_ringAut F Nat.prime_three hF9
    set ψ := (AutL2Facts.autEquiv e).toMonoidHom with hψ
    have hcard := himage ψ (AutL2Facts.autEquiv e).injective
    obtain ⟨E₀, hE₀, hE₀E, hE₀MC⟩ := exists_isKleinFour_le_inf_sup h hFI hM
      (hET.trans hTN) hE2 hE8 fun x hxE hxC => hTC x (hET hxE) hxC
    set U := (E₀.subgroupOf N).map (ψ.comp Φ) with hU
    have hE₀N : E₀ ≤ N := hE₀E.trans (hET.trans hTN)
    have hUinj : Function.Injective ((ψ.comp Φ).comp (E₀.subgroupOf N).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hx' : Φ ((E₀.subgroupOf N).subtype x) = 1 := by
        have h1 : ψ (Φ ((E₀.subgroupOf N).subtype x)) = 1 := hx
        rwa [hψ, MulEquiv.coe_toMonoidHom,
          map_eq_one_iff _ (AutL2Facts.autEquiv e).injective] at h1
      apply Subtype.ext
      apply Subtype.ext
      exact hTC _ (hET (hE₀E x.2)) (mem_coreActionKernel_of_footeAct_eq_one ε hx')
    have hU4 : Nat.card U = 4 := by
      have hr : ((ψ.comp Φ).comp (E₀.subgroupOf N).subtype).range = U := by
        rw [MonoidHom.range_comp, range_subtype]
      rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hUinj).toEquiv, ← hE₀.card_four]
      exact Nat.card_congr (subgroupOfEquivOfLe hE₀N).toEquiv
    have hU2 : ∀ u ∈ U, u * u = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      have hx2 : x * x = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, OneMemClass.coe_one, ← sq]
        exact sq_eq_one_of_isKleinFour hE₀ hx)
      rw [← map_mul, hx2, map_one]
    have hUr : ∀ u ∈ U, u.right = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨s, hs⟩ := footeAct_mem_range_of_mem_sup ε (x := x) (hE₀MC hx)
      change (ψ (Φ x)).right = 1
      rw [← hs, hψ, MulEquiv.coe_toMonoidHom, AutL2Facts.autEquiv_conj, AutL2Facts.incl_apply,
        SemidirectProduct.right_inl]
    have hCU := Foote47.Nine.card_centralizer_four_le hodd hU4 hU2 hUr
    rw [hAut] at hCU
    have hle : (T.subgroupOf N).map (ψ.comp Φ) ≤ centralizer (U : Set _) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_centralizer_iff]
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hTab _ (hET (hE₀E hy)) _ hx)
    rw [← hcard]
    exact (card_le_of_le hle).trans hCU

theorem le_normalizer_conjugate_or_eq
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    (hFI : FooteFourgroupInner)
    (htype : Nonempty (L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin 7)) ∨
      ∃ p f : ℕ, p.Prime ∧ p ^ f = 9 ∧ Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 2 p f)
    {M : Subgroup G} (hM : IsFooteM L M) {g : G} {P : Subgroup G}
    (hPC' : P ≤ coreActionKernel (conjugate M g)) (hPN : P ≤ normalizer (M : Set G))
    (hPp : IsPGroup 2 P) (hPC : ∀ x ∈ P, x ∈ coreActionKernel M → x = 1) {E : Subgroup G}
    (hEP : E ≤ P) (hE2 : ∀ x ∈ E, x ^ 2 = 1) (hE8 : Nat.card E = 8) :
    M ≤ normalizer (conjugate M g : Set G) ∨ P = E := by
  by_cases hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a
  · right
    have h8 := card_le_eight_of_isMulCommutative h hFI htype hM hPN hPp hPC hab hEP hE2 hE8
    exact (eq_of_le_of_card_ge hEP (by rw [hE8]; exact h8)).symm
  · left
    push Not at hab
    obtain ⟨a, ha, b, hb, hab⟩ := hab
    have hM' := isFooteM_conjugate h hM g
    refine Foote47.le_of_forall_fourgroup_le h Foote47.foote47FourgroupGeneration hM hPN hPp hPC
      hEP hE2 hE8 ⟨a, ha, b, hb, hab⟩ fun W F hW hWF hFP _ _ => ?_
    refine inf_le_right.trans ((centralizer_le_normalizer _).trans ?_)
    exact foote_cor_4_8_iv h h47 hST hM' (hWF.trans (hFP.trans hPC')) hW le_rfl

end CFSG.ComponentClassification.FooteLit
