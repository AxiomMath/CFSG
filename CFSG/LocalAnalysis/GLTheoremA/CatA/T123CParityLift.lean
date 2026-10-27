module

public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma88
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneSmallBasic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T123C

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom)

theorem le_normalizer_of_conj_mem {G : Type*} [Group G] {S H : Subgroup G}
    (h : ∀ g ∈ S, ∀ x ∈ H, g * x * g⁻¹ ∈ H) : S ≤ Subgroup.normalizer (H : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (S.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem exists_two_le_of_center_quot {Q : Type*} [Group Q] [Finite Q] (Φ : Set (MulAut Q))
    {U : Subgroup (Q ⧸ Subgroup.center Q)} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hΦ : ∀ φ ∈ Φ, ∀ u ∈ U, centerQuotientHom Q φ u ∈ U) :
    ∃ P : Subgroup Q, P ≠ ⊥ ∧ IsPGroup 2 P ∧ ∀ φ ∈ Φ, ∀ x ∈ P, φ x ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ψ := QuotientGroup.mk' (Subgroup.center Q)
  set H : Subgroup Q := U.comap ψ
  let f : H →* U := (ψ.comp H.subtype).codRestrict U (fun h => h.2)
  have hf : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) r
    exact ⟨⟨l, hr⟩, rfl⟩
  have hker : f.ker ≤ Subgroup.center H := by
    intro h hh
    have h1 : ψ h = 1 := congrArg Subtype.val hh
    have h2 : (h : Q) ∈ Subgroup.center Q := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro k
    exact Subtype.ext (h2 k)
  have : Group.IsNilpotent U := hU2.isNilpotent
  have : Group.IsNilpotent H := Subgroup.isNilpotent_of_ker_le_center f hker
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 H))
  have hPn : (P : Subgroup H).Normal := inferInstance
  have htop : (⊤ : Subgroup U) = (P : Subgroup H).map f := by
    have h := (P.mapSurjective hf).is_maximal' (Q := ⊤)
      (hU2.of_equiv Subgroup.topEquiv.symm) le_top
    rwa [Sylow.coe_mapSurjective] at h
  have hmemP : ∀ h : H, ∀ k : ℕ, h ^ 2 ^ k = 1 → h ∈ (P : Subgroup H) := by
    intro h k hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    have hZ : IsPGroup 2 (Subgroup.zpowers h) :=
      IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    obtain ⟨R, hR⟩ := hZ.exists_le_sylow
    have := Sylow.unique_of_normal P hPn
    have hRP : R = P := Subsingleton.elim R P
    rw [← hRP]
    exact hR (Subgroup.mem_zpowers h)
  refine ⟨(P : Subgroup H).map H.subtype, ?_, P.isPGroup'.map _, ?_⟩
  · intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at hbot
    rw [hbot, Subgroup.map_bot] at htop
    apply hU
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hu⟩ : U) ∈ (⊥ : Subgroup U) := htop ▸ Subgroup.mem_top _
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  · rintro φ hφ _ ⟨q, hq, rfl⟩
    have hφH : φ (q : Q) ∈ H := by
      show ψ (φ (q : Q)) ∈ U
      have e1 : ψ (φ (q : Q)) = centerQuotientHom Q φ (ψ (q : Q)) :=
        (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk φ _).symm
      rw [e1]
      exact hΦ φ hφ _ q.2
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨q, hq⟩
    have hqk : (q : Q) ^ 2 ^ k = 1 := by
      have := congrArg (fun z : (P : Subgroup H) => ((z : H) : Q)) hk
      simpa using this
    have hφP : (⟨φ (q : Q), hφH⟩ : H) ∈ (P : Subgroup H) := by
      refine hmemP _ k (Subtype.ext ?_)
      show φ (q : Q) ^ 2 ^ k = 1
      rw [← map_pow, hqk, map_one]
    exact ⟨⟨φ (q : Q), hφH⟩, hφP, rfl⟩

theorem not_dvd_card_comap_of_isPGroup_two {A B : Type*} [Group A] [Group B] [Finite A]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (f : A →* B) (hker : Nat.Coprime p (Nat.card f.ker))
    {S : Subgroup B} (hS : IsPGroup 2 S) : ¬ p ∣ Nat.card (S.comap f) := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro hdvd
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := S.comap f) p hdvd
  have hwS : f (w : A) ∈ S := w.2
  obtain ⟨k, hk⟩ := hS ⟨_, hwS⟩
  have hk' : f (w : A) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hord : orderOf (f (w : A)) ∣ p := by
    have := orderOf_map_dvd f (w : A)
    rwa [Subgroup.orderOf_coe, hw] at this
  have hc : Nat.Coprime p (2 ^ k) := ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right k
  have h1 : orderOf (f (w : A)) = 1 :=
    (Nat.Coprime.coprime_dvd_left hord hc).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one hk')
  rw [orderOf_eq_one_iff] at h1
  have hdvd' : p ∣ Nat.card f.ker := by
    have := orderOf_dvd_natCard (⟨(w : A), (MonoidHom.mem_ker).2 h1⟩ : f.ker)
    rwa [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hw] at this
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hker hdvd')

variable {G : Type} [Group G] [Finite G]

theorem exists_twoSubgroup_le_of_chevAut {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K E : Subgroup G} (hE : IsElemAbelian p E) (hEK : E ≤ Subgroup.normalizer (K : Set G))
    {U : Subgroup (PSimple p K)} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hEU : ∀ (e : G) (he : e ∈ E), ∀ u ∈ U, chevAut p K ⟨e, hEK he⟩ u ∈ U) :
    ∃ T : Subgroup G, T ≤ K ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      E ≤ Subgroup.normalizer (T : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Φ : Set (MulAut (PQuot p K)) :=
    {φ | ∃ (e : G) (he : e ∈ E), φ = barAut p K ⟨e, hEK he⟩}
  obtain ⟨P, hP1, hP2, hPinv⟩ := exists_two_le_of_center_quot Φ hU hU2 (by
    rintro φ ⟨e, he, rfl⟩ u hu
    exact hEU e he u hu)
  set W₀ : Subgroup ↥K := P.comap (pQuotHom p K)
  set W : Subgroup G := W₀.map K.subtype
  have hWK : W ≤ K := Subgroup.map_subtype_le _
  have hEW : E ≤ Subgroup.normalizer (W : Set G) := by
    refine le_normalizer_of_conj_mem fun e he w hw => ?_
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hw
    refine Subgroup.mem_map.2 ⟨K.normalizerMonoidHom ⟨e, hEK he⟩ k, ?_, rfl⟩
    show pQuotHom p K (K.normalizerMonoidHom ⟨e, hEK he⟩ k) ∈ P
    rw [← barAut_pQuotHom]
    exact hPinv _ ⟨e, he, rfl⟩ _ hk
  have hcop : Nat.Coprime p (Nat.card (GLAPPrimeCore p ↥K)) := by
    unfold GLAPPrimeCore
    exact CFSG.pPrimeCore_coprime_card
  have hcard : Nat.card W = Nat.card W₀ := Subgroup.card_map_of_injective K.subtype_injective
  have hWp : ¬ p ∣ Nat.card W := by
    rw [hcard]
    exact not_dvd_card_comap_of_isPGroup_two hp hp2 (pQuotHom p K)
      (by rw [ker_pQuotHom]; exact hcop) hP2
  have hW2 : 2 ∣ Nat.card W := by
    rw [hcard]
    obtain ⟨x, hx⟩ :=
      exists_prime_orderOf_dvd_card' (G := P) 2 (S8.L89.two_dvd_card_of_two hP2 hP1)
    obtain ⟨k, hk⟩ := pQuotHom_surjective p K (x : PQuot p K)
    have hkW : k ∈ W₀ := by
      show pQuotHom p K k ∈ P
      rw [hk]
      exact x.2
    have h1 : orderOf (pQuotHom p K k) ∣ orderOf (⟨k, hkW⟩ : W₀) := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_map_dvd _ k
    rw [hk, Subgroup.orderOf_coe, hx] at h1
    exact h1.trans (orderOf_dvd_natCard _)
  obtain ⟨T, hTW, hT1, hT2, hET⟩ :=
    CFSG.StandardType.ggExists_invariant_two_subgroup hE hEW hWp hW2
  exact ⟨T, hTW.trans hWK, hT1, hT2, hET⟩

end CFSG.LocalAnalysis.GLTheoremA.T123C

end
