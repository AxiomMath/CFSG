module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFCC
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigCoverConj

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem two_dvd_card_support_of_pow_two_pow {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} {k : ℕ} (hσ : σ ^ 2 ^ k = 1) : 2 ∣ σ.support.card := by
  rw [← Perm.sum_cycleType]
  apply Multiset.dvd_sum
  intro m hm
  have h1 : m ∣ 2 ^ k := (Perm.dvd_of_mem_cycleType hm).trans (orderOf_dvd_of_pow_eq_one hσ)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have h2 := Perm.two_le_of_mem_cycleType hm
  rcases j with _ | j
  · rw [pow_zero] at h2
    omega
  · exact dvd_pow_self 2 (Nat.succ_ne_zero j)

theorem inf_kernel_eq_of_sylow [Finite X] {E M : Subgroup X} {Q Sc : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2)
    (hQS : Q ≤ Sc) (hS2 : IsPGroup 2 Sc) :
    Sc ⊓ (normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K : Subgroup X := normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
    UnbalancedLayer.coreActionKernel M with hKdef
  have hQP : Q ≤ Sc ⊓ K := le_inf hQS hQK
  have hP2 : IsPGroup 2 (Sc ⊓ K : Subgroup X) := hS2.to_le inf_le_left
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hPdvd : Nat.card (Sc ⊓ K : Subgroup X) ∣ Nat.card K := card_dvd_of_le inf_le_right
  have hkle : k ≤ (Nat.card K).factorization 2 := by
    rw [hk] at hPdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hPdvd
  have hcard : Nat.card (Sc ⊓ K : Subgroup X) ≤ Nat.card Q := by
    rw [hk, hQcard]
    exact Nat.pow_le_pow_right (by norm_num) hkle
  exact (Subgroup.eq_of_le_of_card_ge hQP hcard).symm

theorem exists_orderOf_eq_two_of_ne_bot [Finite X] {P : Subgroup X} (hP : IsPGroup 2 P)
    (hP1 : P ≠ ⊥) : ∃ w ∈ P, orderOf w = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP1
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hk
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (show 2 ∣ Nat.card P by
    rw [hk]; exact dvd_pow_self 2 hk0)
  exact ⟨w, w.2, by rw [Subgroup.orderOf_coe, hw]⟩

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}

theorem inf_conj_eq_bot_of_mem (S : Sig36 X t J n e E D) (h33 : Sol78.BalanceLemmaInput)
    (h35 : SignalizerLemma35) (hT13 : Sol76T13.SolomonThm13Simple)
    (hML : Sol78.MaximalityLemmaInput) (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin n)) (hsup : J ⊔ FooteLit.oddCoreIn M = M)
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin n)} (hρ : IsPermAction θ ρ) {Q Sc : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2) (htQ : t ∈ Q) (hQS : Q ≤ Sc)
    (hSH : Sc ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hS2 : IsPGroup 2 Sc)
    (hCQ : ∀ y ∈ Q, orderOf y = 2 →
      centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {x y : X} (hyS : y ∈ Sc) (hyQ : y ∉ Q) (hyx : y ∈ Q.map (MulAut.conj x).toMonoidHom) :
    Q ⊓ Q.map (MulAut.conj x).toMonoidHom = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hyH : y ∈ H := hSH hyS
  have hy1 : ρ ⟨y, hHN hyH⟩ ≠ 1 := by
    intro h
    apply hyQ
    have h1 : y ∈ Sc ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) :=
      mem_inf.mpr ⟨hyS, mem_inf.mpr ⟨hyH, hρ.mem_coreActionKernel _ h⟩⟩
    rwa [inf_kernel_eq_of_sylow hQK hQcard hQS hS2] at h1
  by_contra hne
  obtain ⟨w, hw, hwo⟩ := exists_orderOf_eq_two_of_ne_bot (hQ2.to_le inf_le_left) hne
  have hCw := hCQ w (mem_inf.mp hw).1 hwo
  exact S.false_of_conj_of_centralizer_le h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ hρ
    (hQK.trans inf_le_left) (hQK.trans inf_le_right) hQ2 htQ (mem_inf.mp hw).2 hCw hyx hyH hy1

end Sig36

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 9)} {E : Subgroup X} {D : Finset (Fin 9)}

theorem six_le_card_support_of_commute (S : Sig36 X t J 9 e E D)
    (h33 : Sol78.BalanceLemmaInput) (h35 : SignalizerLemma35)
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput)
    {M : Subgroup X} (hMH : M ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (normalizer (Sol78.signalizerCompletion E E : Set X))))
    (hJM : J ≤ M)
    (hHN : normalizer (Sol78.signalizerCompletion E E : Set X) ≤ normalizer (M : Set X))
    (hsup : J ⊔ FooteLit.oddCoreIn M = M) (θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} (hρ : IsPermAction θ ρ) {Q Sc : Subgroup X}
    (hQK : Q ≤ normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M) (hQ2 : IsPGroup 2 Q)
    (hQcard : Nat.card Q = 2 ^ (Nat.card ↥(normalizer (Sol78.signalizerCompletion E E : Set X) ⊓
      UnbalancedLayer.coreActionKernel M)).factorization 2) (htQ : t ∈ Q) (hQS : Q ≤ Sc)
    (hSH : Sc ≤ normalizer (Sol78.signalizerCompletion E E : Set X)) (hS2 : IsPGroup 2 Sc)
    (hCQ : ∀ y ∈ Q, orderOf y = 2 →
      centralizer ({y} : Set X) ≤ normalizer (Sol78.signalizerCompletion E E : Set X))
    {s a g : X} (hsS : s ∈ Sc) (hsQ : s ∉ Q) (ha : a ∈ Q) (hgs : g⁻¹ * a * g = s)
    (hs2 : s * s = 1) {y : X} (hyQ : y ∈ Q) (hys : y * s = s * y) (hy1 : y ≠ 1)
    (hyN : g * y * g⁻¹ ∈ normalizer (M : Set X)) :
    6 ≤ (ρ ⟨g * y * g⁻¹, hyN⟩).support.card := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hsH : s ∈ H := hSH hsS
  have hs1 : ρ ⟨s, hHN hsH⟩ ≠ 1 := by
    intro h
    apply hsQ
    have h1 : s ∈ Sc ⊓ (H ⊓ UnbalancedLayer.coreActionKernel M) :=
      mem_inf.mpr ⟨hsS, mem_inf.mpr ⟨hsH, hρ.mem_coreActionKernel _ h⟩⟩
    rwa [inf_kernel_eq_of_sylow hQK hQcard hQS hS2] at h1
  have hags : a = g * s * g⁻¹ := by rw [← hgs]; group
  have ha2 : a * a = 1 := by
    rw [hags]
    calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hs2]; group
  have ha1 : a ≠ 1 := by
    rintro rfl
    apply hsQ
    rw [← hgs, show g⁻¹ * 1 * g = 1 by group]
    exact one_mem Q
  have hao : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact ha2) ha1
  have hCa := hCQ a ha hao
  have haH : a ∈ H := (hQK ha).1
  have haK : a ∈ UnbalancedLayer.coreActionKernel M := (hQK ha).2
  set x := g * y * g⁻¹ with hxdef
  have hxa : x * a = a * x := by
    rw [hxdef, hags]
    calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
      _ = g * (s * y) * g⁻¹ := by rw [hys]
      _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group
  have hxH : x ∈ H := hCa (mem_centralizer_singleton_iff.mpr hxa)
  have hx1 : ρ ⟨x, hyN⟩ ≠ 1 := by
    intro hρx
    have hxK : x ∈ UnbalancedLayer.coreActionKernel M := hρ.mem_coreActionKernel _ hρx
    have hy2 : IsPGroup 2 (zpowers y) := hQ2.to_le (zpowers_le.mpr hyQ)
    obtain ⟨y₀, hy₀, hy₀o⟩ := exists_orderOf_eq_two_of_ne_bot hy2
      (fun h => hy1 (zpowers_eq_bot.mp h))
    have hy₀Q : y₀ ∈ Q := zpowers_le.mpr hyQ hy₀
    have hCy₀ := hCQ y₀ hy₀Q hy₀o
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hy₀
    set x₀ := g * y₀ * g⁻¹ with hx₀def
    have hx₀ : x₀ = x ^ m := by
      rw [hx₀def, hxdef, ← hm]
      have h1 : g * y * g⁻¹ = MulAut.conj g y := by simp
      rw [h1, ← map_zpow]
      simp
    have hx₀K : x₀ ∈ UnbalancedLayer.coreActionKernel M := by rw [hx₀]; exact zpow_mem hxK m
    have hx₀H : x₀ ∈ H := by rw [hx₀]; exact zpow_mem hxH m
    have hx₀a : x₀ * a = a * x₀ := by
      rw [hx₀]
      exact (Commute.zpow_left (show Commute x a from hxa) m).eq
    have hx₀2 : x₀ * x₀ = 1 := by
      rw [hx₀def]
      have h1 : y₀ * y₀ = 1 := by rw [← sq, ← hy₀o, pow_orderOf_eq_one]
      calc g * y₀ * g⁻¹ * (g * y₀ * g⁻¹) = g * (y₀ * y₀) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    set T : Subgroup X := zpowers a ⊔ zpowers x₀ with hTdef
    have hT2 : IsPGroup 2 T :=
      (isPGroup_zpowers_of_mul_self ha2).to_sup_of_normal_right'
        (isPGroup_zpowers_of_mul_self hx₀2)
        (zpowers_le.mpr (mem_normalizer_zpowers_of_commute hx₀a))
    have hTK : T ≤ UnbalancedLayer.coreActionKernel M :=
      sup_le (zpowers_le.mpr haK) (zpowers_le.mpr hx₀K)
    set L := GSLit.fixedLayer M T with hLdef
    have hLC : L ≤ centralizer (T : Set X) := (GSLit.fixedLayer_le_inf M T).trans inf_le_right
    set Y := L.map (MulAut.conj g⁻¹).toMonoidHom with hYdef
    have hLx₀ : L ≤ centralizer ({x₀} : Set X) := fun l hl =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (hLC hl) x₀
        (mem_sup_right (mem_zpowers x₀))).symm)
    have hYy₀ : Y ≤ centralizer ({y₀} : Set X) := by
      have h1 := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hLx₀
      rwa [map_conj_centralizer_singleton, show g⁻¹ * x₀ * g⁻¹⁻¹ = y₀ by rw [hx₀def]; group]
        at h1
    have hsa : (MulAut.conj g⁻¹).toMonoidHom a = s := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hgs]
    have hy₀x : (MulAut.conj g⁻¹).toMonoidHom x₀ = y₀ := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hx₀def]
      group
    have hTx : T.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
      rw [map_le_iff_le_comap]
      refine sup_le (zpowers_le.mpr (mem_comap.mpr ?_)) (zpowers_le.mpr (mem_comap.mpr ?_))
      · rw [hsa]
        exact hsH
      · rw [hy₀x]
        exact (hQK hy₀Q).1
    have hsT : s ∈ T.map (MulAut.conj g⁻¹).toMonoidHom := ⟨a, mem_sup_left (mem_zpowers a), hsa⟩
    have hT1 : T ≠ ⊥ := fun h => ha1 (by
      have h1 : a ∈ T := mem_sup_left (mem_zpowers a)
      rwa [h, mem_bot] at h1)
    exact S.false_of_cover_of_conj_fixedLayer h33 h35 hT13 hML hSch hMH hMpc hHN hsup θ hρ
      (sup_le (zpowers_le.mpr haH) (zpowers_le.mpr hx₀H)) hTK hT2 hT1 hTx hsT hs1 le_rfl
      (hYy₀.trans hCy₀) (sup_eq_left.mpr (map_subtype_le _))
  have h5 : 5 ≤ (ρ ⟨x, hyN⟩).support.card := by
    by_contra h4
    push Not at h4
    exact S.false_of_support_le_four_of_commute h33 h35 hT13 hML hSch hMH hMpc hJM hHN
      hsup θ hρ (hQK.trans inf_le_left) (hQK.trans inf_le_right) hQ2 htQ hxH hyQ
      (show g⁻¹⁻¹ * y * g⁻¹ = x by rw [inv_inv]) haH hao haK hxa.symm hCa hx1 (by omega)
  have hx2 : IsPGroup 2 (zpowers x) := by
    have h1 : IsPGroup 2 ((zpowers y).map (MulAut.conj g).toMonoidHom) :=
      (hQ2.to_le (zpowers_le.mpr hyQ)).map _
    rwa [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  obtain ⟨k, hk⟩ := hx2 ⟨x, mem_zpowers x⟩
  have hxk : (⟨x, hyN⟩ : ↥(normalizer (M : Set X))) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    have h1 := congrArg Subtype.val hk
    simpa using h1
  have hρk : ρ ⟨x, hyN⟩ ^ 2 ^ k = 1 := by rw [← map_pow, hxk, map_one]
  have hev := two_dvd_card_support_of_pow_two_pow hρk
  have h6 : 6 ≤ (ρ ⟨x, hyN⟩).support.card := by omega
  exact h6

end Sig36

end CFSG.ComponentClassification.SolMax
