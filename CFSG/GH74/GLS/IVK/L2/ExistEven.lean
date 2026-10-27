module

public import CFSG.GH74.GLS.IVK.L2.ExistEvenAux

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

theorem exists_notation_of_even (hF : L2Field F) (hev : Even (Nat.card (fieldAutSub e))) :
    Nonempty (L2Notation e) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := innDiagSub_normal e
  obtain ⟨g₀, a, m, hg₀F, hFpow, ha, hm, hord⟩ := exists_even_data e hev
  have hm0 : 0 < m := hm.pos
  have h2a : 0 < 2 ^ a := by positivity
  have hKpos : 0 < Nat.card K := Nat.card_pos
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulAut K, ψ = g₀ ^ m := ⟨_, rfl⟩
  obtain ⟨z₁, hz₁⟩ : ∃ z₁ : MulAut K, z₁ = g₀ ^ (2 ^ (a - 1)) := ⟨_, rfl⟩
  obtain ⟨ω, hω⟩ : ∃ ω : MulAut K, ω = g₀ ^ (2 ^ a) := ⟨_, rfl⟩
  have hψF : ψ ∈ fieldAutSub e := hψ ▸ Subgroup.pow_mem _ hg₀F m
  have hz₁F : z₁ ∈ fieldAutSub e := hz₁ ▸ Subgroup.pow_mem _ hg₀F _
  have hωF : ω ∈ fieldAutSub e := hω ▸ Subgroup.pow_mem _ hg₀F _
  have hψo : orderOf ψ = 2 ^ a := hψ ▸ orderOf_pow_odd_part g₀ hm0 hord
  have hz₁o : orderOf z₁ = 2 * m := hz₁ ▸ orderOf_pow_half g₀ ha hord
  have hωo : orderOf ω = m := hω ▸ orderOf_pow_two_part g₀ hord
  have hexp : 2 ^ (a - 1) * 2 = 2 ^ a := by
    rw [← pow_succ]
    congr 1
    omega
  have hωz : ω = z₁ ^ 2 := by rw [hω, hz₁, ← pow_mul, hexp]
  have hψz : ψ * z₁ = z₁ * ψ := by
    rw [hψ, hz₁]; exact ((Commute.refl g₀).pow_pow _ _).eq
  have hψω : ψ * ω = ω * ψ := by
    rw [hψ, hω]; exact ((Commute.refl g₀).pow_pow _ _).eq
  obtain ⟨σz, hσz⟩ : ∃ σ : F ≃+* F, fieldAutHom e σ = z₁ := id hz₁F
  obtain ⟨σω, hσω⟩ : ∃ σ : F ≃+* F, fieldAutHom e σ = ω := id hωF
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ : F ≃+* F, fieldAutHom e σ = g₀ := id hg₀F
  have hσzo : orderOf σz = 2 * m := by
    have := orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) σz
    rw [hσz, hz₁o] at this
    exact this.symm
  have hσωo : orderOf σω = m := by
    have := orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) σω
    rw [hσω, hωo] at this
    exact this.symm
  have hFcard : Nat.card ↥(fieldAutSub e) = 2 ^ a * m := by
    have hFeq : fieldAutSub e = zpowers g₀ := by
      apply le_antisymm
      · intro φ hφ
        obtain ⟨k, rfl⟩ := hFpow φ hφ
        exact Subgroup.zpow_mem_zpowers g₀ k
      · exact zpowers_le.mpr hg₀F
    rw [hFeq, Nat.card_zpowers, hord]
  obtain ⟨A, hA⟩ : ∃ A : Subgroup (MulAut K),
      A = centralizer ({fieldAutHom e σz} : Set (MulAut K)) ⊓ innDiagSub e := ⟨_, rfl⟩
  obtain ⟨A', hA'⟩ : ∃ A' : Subgroup (MulAut K),
      A' = centralizer ({fieldAutHom e σω} : Set (MulAut K)) ⊓ innDiagSub e := ⟨_, rfl⟩
  have hAcomm : ∀ x ∈ A, x * z₁ = z₁ * x := by
    intro x hx
    rw [hA] at hx
    have := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    rwa [hσz] at this
  have hA'comm : ∀ x ∈ A', x * ω = ω * x := by
    intro x hx
    rw [hA'] at hx
    have := Subgroup.mem_centralizer_singleton_iff.mp hx.1
    rwa [hσω] at this
  have hAD : A ≤ innDiagSub e := hA ▸ inf_le_right
  have hA'D : A' ≤ innDiagSub e := hA' ▸ inf_le_right
  have hAA' : A ≤ A' := by
    intro x hx
    rw [hA']
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hAD hx⟩
    rw [hσω, hωz]
    exact (Commute.pow_right (show Commute x z₁ from hAcomm x hx) 2).eq
  have hAK : A ≤ innAut K := by
    rw [hA]
    exact centralizer_fieldAut_le_innAut e σz ⟨m, by rw [hσzo]; ring⟩
  have hAfac : (Nat.card A).factorization 2 = (Nat.card K).factorization 2 := by
    rw [hA]; exact factorization_card_centralizer_even e hF σz hm hσzo
  have hA'fac : (Nat.card A').factorization 2 = (Nat.card ↥(innDiagSub e)).factorization 2 := by
    rw [hA']; exact factorization_card_centralizer_odd e hF σω (by rw [hσωo]; exact hm)
  obtain ⟨U, hU4, hUle⟩ := exists_fourSubgroup_centralizer e hF σ₀
  rw [hσ₀] at hUle
  have hUg : ∀ u ∈ U, u * g₀ = g₀ * u := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mp (hUle hu).1
  have hUD : U ≤ innDiagSub e := fun u hu => (hUle hu).2
  have hUz : ∀ u ∈ U, u * z₁ = z₁ * u := fun u hu => by
    rw [hz₁]; exact (Commute.pow_right (show Commute u g₀ from hUg u hu) _).eq
  have hUA : U ≤ A := fun u hu => by
    rw [hA]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (by rw [hσz]; exact hUz u hu), hUD hu⟩
  have hUK : U ≤ innAut K := hUA.trans hAK
  have hU2 : IsPGroup 2 ↥U := IsPGroup.of_card (n := 2) (by rw [hU4.2]; norm_num)
  have hψ2 : IsPGroup 2 ↥(zpowers ψ) := IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hψo])
  have hUψ : ∀ u ∈ U, ∀ k ∈ zpowers ψ, u * k = k * u := by
    intro u hu k hk
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hk
    have : Commute u ψ := by
      rw [hψ]; exact Commute.pow_right (show Commute u g₀ from hUg u hu) m
    exact (this.zpow_right j).eq
  have hZ2 : IsPGroup 2 ↥(U ⊔ zpowers ψ) := isPGroup_sup_of_commute hU2 hψ2 hUψ
  have hψA : ψ ∈ normalizer (A : Set (MulAut K)) := by
    rw [hA]
    exact mem_normalizer_centralizer_inf (innDiagSub e) (fieldAutHom e σz) ψ (by rw [hσz]; exact hψz)
  have hψA' : ψ ∈ normalizer (A' : Set (MulAut K)) := by
    rw [hA']
    exact mem_normalizer_centralizer_inf (innDiagSub e) (fieldAutHom e σω) ψ
      (by rw [hσω]; exact hψω)
  have hMle : A ⊔ zpowers ψ ≤ normalizer (A : Set (MulAut K)) :=
    sup_le Subgroup.le_normalizer (zpowers_le.mpr hψA)
  have hnormM : ∀ x ∈ A ⊔ zpowers ψ, ∀ a ∈ A, x * a * x⁻¹ ∈ A :=
    fun x hx a ha => (Subgroup.mem_normalizer_iff.mp (hMle hx) a).mp ha
  have hZM : U ⊔ zpowers ψ ≤ A ⊔ zpowers ψ := sup_le_sup hUA le_rfl
  obtain ⟨Q, hQM, hZQ, hQ2, hQcard⟩ :=
    exists_pGroup_inf_sylow 2 (A ⊔ zpowers ψ) A (U ⊔ zpowers ψ) le_sup_left hZM hnormM hZ2
  have hMM' : A ⊔ zpowers ψ ≤ A' ⊔ zpowers ψ := sup_le_sup hAA' le_rfl
  have hQ2' : IsPGroup 2 ↥(Q.subgroupOf (A' ⊔ zpowers ψ)) :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe (hQM.trans hMM')).symm
  obtain ⟨Q'', hQ''⟩ := hQ2'.exists_le_sylow
  have hdisj : Disjoint A' (zpowers ψ) :=
    (disjoint_iff.mpr (innDiagSub_inf_fieldAutSub e)).mono hA'D (zpowers_le.mpr hψF)
  have hM'card : Nat.card ↥(A' ⊔ zpowers ψ) = Nat.card A' * 2 ^ a := by
    rw [card_sup_of_le_normalizer A' (zpowers ψ) (zpowers_le.mpr hψA') hdisj, Nat.card_zpowers,
      hψo]
  obtain ⟨T₀, hT₀⟩ : ∃ T₀ : Subgroup (MulAut K),
      T₀ = (Q'' : Subgroup ↥(A' ⊔ zpowers ψ)).map (A' ⊔ zpowers ψ).subtype := ⟨_, rfl⟩
  have hT₀M' : T₀ ≤ A' ⊔ zpowers ψ := hT₀ ▸ Subgroup.map_subtype_le _
  have hT₀card : Nat.card T₀ = 2 ^ (Nat.card (MulAut K)).factorization 2 := by
    rw [hT₀, Subgroup.card_map_of_injective (A' ⊔ zpowers ψ).subtype_injective,
      Sylow.card_eq_multiplicity Q'', hM'card, card_mulAut_eq e, hFcard]
    congr 1
    have h1 := hA'fac
    rw [Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two] at h1
    rw [Nat.factorization_def _ Nat.prime_two, Nat.factorization_def _ Nat.prime_two,
      padicValNat.mul Nat.card_pos.ne' h2a.ne', padicValNat.prime_pow,
      padicValNat.mul Nat.card_pos.ne' (Nat.mul_ne_zero h2a.ne' hm0.ne'),
      padicValNat.mul h2a.ne' hm0.ne', padicValNat.prime_pow, padicValNat_two_of_odd hm]
    omega
  obtain ⟨T, hT⟩ : ∃ T : Sylow 2 (MulAut K), (T : Subgroup (MulAut K)) = T₀ :=
    ⟨Sylow.ofCard T₀ hT₀card, rfl⟩
  subst hT
  have hQT : Q ≤ (T : Subgroup (MulAut K)) := by
    intro x hx
    have hxM' : x ∈ A' ⊔ zpowers ψ := hMM' (hQM hx)
    rw [hT₀]
    exact ⟨⟨x, hxM'⟩, hQ'' hx, rfl⟩
  have hψT : ψ ∈ (T : Subgroup (MulAut K)) := hQT (hZQ (Subgroup.mem_sup_right (mem_zpowers ψ)))
  have hUT : U ≤ (T : Subgroup (MulAut K)) := fun u hu => hQT (hZQ (Subgroup.mem_sup_left hu))
  have hM'c : A' ⊔ zpowers ψ ≤ centralizer ({ω} : Set (MulAut K)) := by
    refine sup_le ?_ ?_
    · intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hA'comm x hx)
    · exact zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hψω)
  have hTω : ∀ x ∈ (T : Subgroup (MulAut K)), x * ω = ω * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hM'c (hT₀M' hx))
  have hcop : Nat.Coprime m (2 ^ a) := Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hm)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hbez : g₀ = ψ ^ u * ω ^ v := by
    have h1 : g₀ ^ ((m : ℤ) * u + ((2 ^ a : ℕ) : ℤ) * v) = g₀ := by
      have : (m : ℤ) * u + ((2 ^ a : ℕ) : ℤ) * v = 1 := by linarith
      rw [this, zpow_one]
    conv_lhs => rw [← h1]
    rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hψ, hω]
  have hg₀N : g₀ ∈ normalizer (((T : Subgroup (MulAut K)) : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rw [hbez]
    refine Subgroup.mul_mem _ ?_ ?_
    · exact Subgroup.le_normalizer (Subgroup.zpow_mem _ hψT u)
    · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr ?_)
      intro x hx
      exact (Commute.zpow_right (show Commute x ω from hTω x hx) v).eq
  have hPA : (T : Subgroup (MulAut K)) ⊓ innAut K ≤ A := by
    have hT2 : IsPGroup 2 ↥((T : Subgroup (MulAut K)) ⊓ innAut K) := T.isPGroup'.to_inf_left
    have hle : Q ⊓ A ≤ (T : Subgroup (MulAut K)) ⊓ innAut K := inf_le_inf hQT hAK
    have hcard1 : Nat.card ↥((T : Subgroup (MulAut K)) ⊓ innAut K) ≤
        2 ^ (Nat.card K).factorization 2 := by
      have := card_le_pow_factorization 2 hT2
        (inf_le_right : (T : Subgroup (MulAut K)) ⊓ innAut K ≤ innAut K)
      rwa [card_innAut e] at this
    have hcard2 : Nat.card ↥(Q ⊓ A) = 2 ^ (Nat.card K).factorization 2 := by
      rw [hQcard, hAfac]
    have heq : Q ⊓ A = (T : Subgroup (MulAut K)) ⊓ innAut K :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard2]; exact hcard1)
    rw [← heq]
    exact inf_le_right
  have hDfac : (Nat.card ↥(innDiagSub e)).factorization 2 = (Nat.card K).factorization 2 + 1 := by
    rw [card_innDiagSub e hF, Nat.factorization_mul (by norm_num) hKpos.ne']
    simp only [Finsupp.add_apply]
    have h3 : (2 : ℕ).factorization 2 = 1 := by
      rw [Nat.factorization_def _ Nat.prime_two]; exact padicValNat_self
    rw [h3]
    ring
  obtain ⟨m', hm', ⟨φ⟩⟩ := dihedral_of_sylow_inf_innDiag e hF T
  have hTDcard : Nat.card ↥((T : Subgroup (MulAut K)) ⊓ innDiagSub e) =
      2 ^ (Nat.card ↥(innDiagSub e)).factorization 2 := card_sylow_inf_normal 2 T (innDiagSub e)
  have hTD_not : ¬ ((T : Subgroup (MulAut K)) ⊓ innDiagSub e ≤ innAut K) := by
    intro hle
    have hle' : (T : Subgroup (MulAut K)) ⊓ innDiagSub e ≤ (T : Subgroup (MulAut K)) ⊓ innAut K :=
      le_inf inf_le_left hle
    have h1 := Subgroup.card_le_of_le hle'
    have hT2 : IsPGroup 2 ↥((T : Subgroup (MulAut K)) ⊓ innAut K) := T.isPGroup'.to_inf_left
    have h2 := card_le_pow_factorization 2 hT2
      (inf_le_right : (T : Subgroup (MulAut K)) ⊓ innAut K ≤ innAut K)
    rw [card_innAut e] at h2
    rw [hDfac, pow_succ] at hTDcard
    have hpos : 0 < 2 ^ (Nat.card K).factorization 2 := by positivity
    omega
  obtain ⟨t, htTD, ht2, htI⟩ : ∃ t ∈ (T : Subgroup (MulAut K)) ⊓ innDiagSub e,
      orderOf t = 2 ∧ t ∉ innAut K := by
    by_contra hcon
    push Not at hcon
    exact hTD_not (DihedralAux.le_of_involutions_le _ (innAut K) φ hcon)
  refine ⟨{
    T := T
    t := t
    t_mem := htTD.1
    t_order := ht2
    t_mem_diag := htTD.2
    t_not_mem_inn := htI
    T_inv := ?_
    R_cent := ?_
    F_odd_cent := ?_
    four_cent := ?_ }⟩
  · intro φ' hφ'
    obtain ⟨k, rfl⟩ := hFpow φ' hφ'
    exact Subgroup.zpow_mem _ hg₀N k
  · intro f hf hf2 x hx
    obtain ⟨hfT, hfF⟩ := hf
    obtain ⟨k, rfl⟩ := hFpow f hfF
    have hf2' : (g₀ ^ k) ^ (2 * m) = 1 := by
      rw [pow_mul]
      have h2 : (g₀ ^ k) ^ 2 = 1 := by
        have := pow_orderOf_eq_one (g₀ ^ k)
        rwa [hf2] at this
      rw [h2, one_pow]
    have h3 : 2 ^ a * m = 2 * m * 2 ^ (a - 1) := by
      have : 2 ^ a = 2 * 2 ^ (a - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]; ring
    obtain ⟨k', hk'⟩ := exists_zpow_of_pow_eq_one g₀ (d := 2 * m) (n := 2 ^ a * m) hord
      ⟨2 ^ (a - 1), h3⟩ (by omega) k hf2'
    have h4 : 2 ^ a * m / (2 * m) = 2 ^ (a - 1) := by
      rw [h3, Nat.mul_div_cancel_left _ (by omega)]
    rw [h4, ← hz₁] at hk'
    have hxA : x ∈ A := hPA hx
    rw [hk']
    exact (Commute.zpow_right (show Commute x z₁ from hAcomm x hxA) k').eq
  · intro f hf hodd x hx
    obtain ⟨k, rfl⟩ := hFpow f hf
    have hfn : (g₀ ^ k) ^ (2 ^ a * m) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hord,
        pow_orderOf_eq_one, one_zpow]
    have hdvd : orderOf (g₀ ^ k) ∣ 2 ^ a * m := orderOf_dvd_of_pow_eq_one hfn
    have hcop' : Nat.Coprime (orderOf (g₀ ^ k)) (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hodd)
    have hdvd' : orderOf (g₀ ^ k) ∣ m := hcop'.dvd_of_dvd_mul_left hdvd
    have hfm : (g₀ ^ k) ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp hdvd'
    obtain ⟨k', hk'⟩ := exists_zpow_of_pow_eq_one g₀ (d := m) (n := 2 ^ a * m) hord
      ⟨2 ^ a, by ring⟩ hm0 k hfm
    have h4 : 2 ^ a * m / m = 2 ^ a := Nat.mul_div_cancel _ hm0
    rw [h4, ← hω] at hk'
    rw [hk']
    exact (Commute.zpow_right (show Commute x ω from hTω x hx) k').eq
  · refine ⟨U, le_inf hUT hUK, hU4, ?_⟩
    intro φ' hφ' u hu
    obtain ⟨k, rfl⟩ := hFpow φ' hφ'
    exact (Commute.zpow_right (show Commute u g₀ from hUg u hu) k).eq.symm

end CFSG.GH74.GLS.IVK
