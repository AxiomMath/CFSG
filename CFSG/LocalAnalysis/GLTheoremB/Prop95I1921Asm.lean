module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Norm
public import CFSG.LocalAnalysis.GLTheoremB.Prop95I1921Comb
public import CFSG.HardMathSupport.Cooperstein.Coordinator.NaturalBridgeLS
public import CFSG.Alternating.Multipliers.Main

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Parts
open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open Equiv Equiv.Perm
open scoped commutatorElement

theorem center_no_two_elements {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Group K]
    [Finite K] (hO : GLAPPrimeCore p K = ⊥) :
    ∀ z ∈ Subgroup.center K, ∀ n : ℕ, z ^ (2 ^ n) = 1 → z = 1 := by
  intro z hz n hn
  let N : Subgroup K := Subgroup.zpowers z
  have hle : N ≤ Subgroup.center K := Subgroup.zpowers_le.2 hz
  haveI : N.Normal := ⟨fun m hm g => by
    have := Subgroup.mem_center_iff.1 (hle hm) g
    rw [this]; simpa using hm⟩
  have hcop2 : Nat.Coprime p (2 ^ n) :=
    Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hcop : Nat.Coprime p (Nat.card N) := by
    rw [Nat.card_zpowers]
    exact Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hn) hcop2
  have hNle : N ≤ CFSG.pPrimeCore p K := le_sSup ⟨inferInstance, hcop⟩
  have hO' : CFSG.pPrimeCore p K = ⊥ := hO
  rw [hO'] at hNle
  exact Subgroup.mem_bot.1 (hNle (Subgroup.mem_zpowers z))

theorem odd_card_center_of_no_two {K : Type} [Group K] [Finite K]
    (hodd : ∀ z ∈ Subgroup.center K, ∀ n : ℕ, z ^ (2 ^ n) = 1 → z = 1) :
    ¬ 2 ∣ Nat.card (Subgroup.center K) := by
  intro hdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hz1 : (z : K) ^ (2 ^ 1) = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    simpa using congrArg Subtype.val this
  have := hodd z z.2 1 hz1
  have : z = 1 := Subtype.ext this
  rw [this, orderOf_one] at hz
  omega

theorem center_cases_seven {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K)
    (hodd : ∀ z ∈ Subgroup.center K, ∀ n : ℕ, z ^ (2 ^ n) = 1 → z = 1)
    (e : (K ⧸ Subgroup.center K) ≃* ↥(alternatingGroup (Fin 7))) :
    Subgroup.center K = ⊥ ∨ Nat.card (Subgroup.center K) = 3 := by
  have h6 : Nat.card (Subgroup.center K) ∣ 6 :=
    CFSG.HardMathSupport.Cooperstein.Coordinator.card_center_dvd_six_of_alt7 hK e
  have h2 : ¬ 2 ∣ Nat.card (Subgroup.center K) := odd_card_center_of_no_two hodd
  have hcases : Nat.card (Subgroup.center K) ∈ ({1, 2, 3, 6} : Finset ℕ) := by
    have hmem : Nat.card (Subgroup.center K) ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨h6, by norm_num⟩
    have : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [this] at hmem; exact hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hcases
  rcases hcases with h | h | h | h
  · left; exact Subgroup.card_eq_one.1 h
  · exact absurd (by rw [h]) h2
  · right; exact h
  · exact absurd (by rw [h]; norm_num) h2

theorem card_center_dvd_two_of_alt {K : Type} [Group K]
    (hperf : commutator K = ⊤) {n : ℕ} (hn5 : 5 ≤ n) (hn6 : n ≠ 6) (hn7 : n ≠ 7)
    (e : (K ⧸ Subgroup.center K) ≃* ↥(alternatingGroup (Fin n))) :
    Nat.card (Subgroup.center K) ∣ 2 := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.2 hperf
  have h := CFSG.HardMathSupport.Cooperstein.Coordinator.card_ker_dvd_card_hopfMultiplier
    (e.toMonoidHom.comp (QuotientGroup.mk' _)) (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (CFSG.HardMathSupport.Cooperstein.Coordinator.ker_comp_mk'_center e).le
  rw [CFSG.HardMathSupport.Cooperstein.Coordinator.ker_comp_mk'_center] at h
  rcases (by omega : n = 5 ∨ 8 ≤ n) with rfl | hn8
  · rwa [(CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_five).2] at h
  · rwa [CFSG.Alternating.Multipliers.card_hopfMultiplier_alternatingGroup hn8] at h

theorem center_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Group K] [Finite K] (hK : CFSG.IsQuasisimple K) (hO : GLAPPrimeCore p K = ⊥)
    {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : (K ⧸ Subgroup.center K) ≃* ↥(alternatingGroup (Fin n))) :
    Subgroup.center K = ⊥ ∨ (n = 7 ∧ Nat.card (Subgroup.center K) = 3 ∧ p = 3) := by
  have hodd := center_no_two_elements hp hp2 hO
  have h2 := odd_card_center_of_no_two hodd
  by_cases h7 : n = 7
  · subst h7
    rcases center_cases_seven hK hodd e with h | h
    · exact Or.inl h
    · refine Or.inr ⟨rfl, h, ?_⟩
      by_contra hp3
      have hcop : Nat.Coprime p (Nat.card (Subgroup.center K)) := by
        rw [h]
        exact (Nat.coprime_primes hp Nat.prime_three).2 hp3
      have hle : Subgroup.center K ≤ CFSG.pPrimeCore p K := le_sSup ⟨inferInstance, hcop⟩
      have hO' : CFSG.pPrimeCore p K = ⊥ := hO
      rw [hO'] at hle
      have hbot : Subgroup.center K = ⊥ := le_bot_iff.1 hle
      rw [hbot, Subgroup.card_bot] at h
      omega
  · left
    have hperf : commutator K = ⊤ := Group.isPerfect_def.1 hK.1
    have hdvd := card_center_dvd_two_of_alt hperf hn hn6 h7 e
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact Subgroup.card_eq_one.1 h
    · exact absurd (by rw [h]) h2

theorem glaPPrimeCore_three_of_alt7 {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hO : GLAPPrimeCore p K = ⊥)
    (e : (K ⧸ Subgroup.center K) ≃* ↥(alternatingGroup (Fin 7))) : GLAPPrimeCore 3 K = ⊥ := by
  have hodd := center_no_two_elements hp hp2 hO
  have hZ := center_cases_seven hK hodd e
  have hZ3 : Nat.card (Subgroup.center K) = 1 ∨ Nat.card (Subgroup.center K) = 3 := by
    rcases hZ with h | h
    · left; rw [h]; simp
    · right; exact h
  have h3K : 3 ∣ Nat.card K := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center K)
    rw [this, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    exact Dvd.dvd.mul_right (by decide) _
  haveI : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.2.1
  have hperf : commutator K = ⊤ := Group.isPerfect_def.1 hK.1
  show CFSG.pPrimeCore 3 K = ⊥
  unfold CFSG.pPrimeCore
  rw [eq_bot_iff]
  refine sSup_le fun N hN => ?_
  obtain ⟨hNn, hNcop⟩ := hN
  have hNb : N = ⊥ := by
    by_cases hNZ : N ≤ Subgroup.center K
    · have hd1 : Nat.card N ∣ Nat.card (Subgroup.center K) := Subgroup.card_dvd_of_le hNZ
      have hd : Nat.card N ∣ 3 := by
        rcases hZ3 with h | h
        · rw [h] at hd1; exact hd1.trans (one_dvd _)
        · rw [h] at hd1; exact hd1
      have : Nat.card N = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
        · exact h
        · exfalso
          rw [h] at hNcop
          simp at hNcop
      exact Subgroup.card_eq_one.1 this
    · exfalso
      let Nb : Subgroup (K ⧸ Subgroup.center K) := N.map (QuotientGroup.mk' (Subgroup.center K))
      haveI : Nb.Normal := hNn.map _ (QuotientGroup.mk'_surjective _)
      have hNb1 : Nb ≠ ⊥ := by
        intro h
        apply hNZ
        intro n hn
        have : (QuotientGroup.mk' (Subgroup.center K)) n ∈ Nb := Subgroup.mem_map_of_mem _ hn
        rw [h, Subgroup.mem_bot] at this
        exact (QuotientGroup.eq_one_iff _).1 this
      have hNbt : Nb = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal Nb).resolve_left hNb1
      have hdecomp : ∀ k : K, ∃ n ∈ N, ∃ z ∈ Subgroup.center K, k = n * z := by
        intro k
        have hk : (QuotientGroup.mk k : K ⧸ Subgroup.center K) ∈ Nb := by rw [hNbt]; trivial
        obtain ⟨n, hn, hnk⟩ := Subgroup.mem_map.1 hk
        have hnk' : (QuotientGroup.mk n : K ⧸ Subgroup.center K) = QuotientGroup.mk k := hnk
        refine ⟨n, hn, n⁻¹ * k, ?_, by group⟩
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hnk']
        simp
      have hcomm : ∀ a b : K, ⁅a, b⁆ ∈ N := by
        intro a b
        obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := hdecomp a
        obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := hdecomp b
        have hmk : ∀ (n : K), n ∈ N → ∀ z : K,
            (QuotientGroup.mk' N) (n * z) = (QuotientGroup.mk' N) z := by
          intro n hn z
          have h0 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
          rw [map_mul, h0, one_mul]
        rw [← QuotientGroup.eq_one_iff]
        show (QuotientGroup.mk' N) ⁅n₁ * z₁, n₂ * z₂⁆ = 1
        rw [map_commutatorElement, hmk n₁ hn₁, hmk n₂ hn₂, commutatorElement_eq_one_iff_mul_comm,
          ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz₂ z₁]
      have hNtop : N = ⊤ := by
        rw [eq_top_iff]
        intro k _
        have hk : k ∈ commutator K := by rw [hperf]; exact Subgroup.mem_top k
        exact (commutator_def K ▸ Subgroup.commutator_le.2 (fun a _ b _ => hcomm a b)) hk
      rw [hNtop] at hNcop
      simp only [Subgroup.card_top] at hNcop
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hNcop h3K
  rw [hNb]

section V4

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem fin4_card_V4 :
    Fintype.card {s : Perm (Fin 4) // s = 1 ∨ IsDT (Finset.univ : Finset (Fin 4)) s} = 4 := by
  decide +kernel

theorem V4_sign {F : Finset Ω} (hF : F.card = 4) {s : Perm Ω} (hs : s ∈ V4 F hF) : sign s = 1 := by
  rcases (mem_V4 hF).1 hs with h | h
  · rw [h]; simp
  · exact sign_isDT hF h

theorem card_V4 {F : Finset Ω} (hF : F.card = 4) : Nat.card (V4 F hF) = 4 := by
  have hcard : Fintype.card ↥F = 4 := by rw [Fintype.card_coe]; exact hF
  let e : ↥F ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
  let f : {r : Perm ↥F // r = 1 ∨ IsDT (Finset.univ : Finset ↥F) r} → V4 F hF := fun r =>
    ⟨Perm.ofSubtype r.1, by
      rcases r.2 with h | h
      · exact (mem_V4 hF).2 (Or.inl (by rw [h, map_one]))
      · exact (mem_V4 hF).2 (Or.inr (isDT_of_ofSubtype h))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro r r' h
      exact Subtype.ext (Perm.ofSubtype_injective (congrArg Subtype.val h))
    · rintro ⟨s, hs⟩
      rcases (mem_V4 hF).1 hs with h | h
      · exact ⟨⟨1, Or.inl rfl⟩, Subtype.ext (by simp [f, h])⟩
      · obtain ⟨r, hr, hrd⟩ := exists_restrictDT h
        exact ⟨⟨r, Or.inr hrd⟩, Subtype.ext hr⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  have hcongr : Nat.card {r : Perm ↥F // r = 1 ∨ IsDT (Finset.univ : Finset ↥F) r} =
      Nat.card {s : Perm (Fin 4) // s = 1 ∨ IsDT (Finset.univ : Finset (Fin 4)) s} := by
    refine Nat.card_congr (e.permCongr.subtypeEquiv (fun r => ?_))
    have h1 : (e.permCongr r = 1) ↔ (r = 1) := by
      constructor
      · intro h
        apply e.permCongrHom.injective
        rw [map_one, Equiv.permCongrHom_coe e]; exact h
      · intro h; rw [h]; exact (map_one e.permCongrHom : _)
    rw [h1, isDT_univ_permCongr]
  rw [hcongr, Nat.card_eq_fintype_card, fin4_card_V4]

theorem moved_V4 {F : Finset Ω} (hF : F.card = 4) :
    {i : Ω | ¬ ∀ v ∈ V4 F hF, v i = i} = (F : Set Ω) := by
  ext i
  simp only [Set.mem_setOf_eq, Finset.mem_coe]
  constructor
  · intro h
    by_contra hiF
    apply h
    intro v hv
    rcases (mem_V4 hF).1 hv with h1 | h1
    · rw [h1]; rfl
    · exact h1.1 i hiF
  · intro hiF hall
    have hc := card_V4 hF
    obtain ⟨v, hv1⟩ : ∃ v : V4 F hF, v ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Subsingleton (V4 F hF) := ⟨fun a b => (hcon a).trans (hcon b).symm⟩
      have := Finite.card_le_one_iff_subsingleton.2 this
      omega
    have hvne : (v : Perm Ω) ≠ 1 := fun h => hv1 (Subtype.ext h)
    rcases (mem_V4 hF).1 v.2 with h | h
    · exact hvne h
    · exact h.2.2 i hiF (hall v v.2)

end V4

theorem isRootFour_of_V4 {n : ℕ} {F : Finset (Fin n)} (hF : F.card = 4)
    (V : Subgroup (alternatingGroup (Fin n)))
    (hV : ∀ g : alternatingGroup (Fin n), g ∈ V ↔ (g : Perm (Fin n)) ∈ V4 F hF) :
    IsRootFour V := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← card_V4 hF]
    exact Nat.card_congr
      { toFun := fun v => ⟨(v : Perm (Fin n)), (hV v).1 v.2⟩
        invFun := fun w => ⟨⟨(w : Perm (Fin n)),
          Perm.mem_alternatingGroup.2 (V4_sign hF w.2)⟩, (hV _).2 w.2⟩
        left_inv := fun v => rfl
        right_inv := fun w => rfl }
  · intro v hv
    rcases (mem_V4 hF).1 ((hV v).1 hv) with h | h
    · apply Subtype.ext
      simp [h]
    · apply Subtype.ext
      simpa [sq] using h.2.1
  · have hset : {i : Fin n | ¬ ∀ v ∈ V, (v : Perm (Fin n)) i = i} = (F : Set (Fin n)) := by
      rw [← moved_V4 hF]
      ext i
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h hall
        apply h
        intro v hv
        exact hall v ((hV v).1 hv)
      · intro h hall
        apply h
        intro w hw
        have hw' : w ∈ alternatingGroup (Fin n) := Perm.mem_alternatingGroup.2 (V4_sign hF hw)
        exact hall ⟨w, hw'⟩ ((hV ⟨w, hw'⟩).2 hw)
    have : Nat.card {i : Fin n // ¬ ∀ v ∈ V, (v : Perm (Fin n)) i = i} = 4 := by
      have h1 : Nat.card {i : Fin n // ¬ ∀ v ∈ V, (v : Perm (Fin n)) i = i} =
          Set.ncard {i : Fin n | ¬ ∀ v ∈ V, (v : Perm (Fin n)) i = i} :=
        (Nat.card_coe_set_eq _)
      rw [h1, hset, Set.ncard_coe_finset, hF]
    exact this

theorem isQuasisimple_of_comp {X : Type} [Group X] {K : Subgroup X} (hK : IsComponentOf K ⊤) :
    CFSG.IsQuasisimple ↥K := by
  have h : CFSG.Open.IsQuasisimple ↥K := hK.2.2
  refine ⟨Group.isPerfect_def.2 h.1, h.2, ?_⟩
  by_contra hcon
  push Not at hcon
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := h.2
  have h1 : ∀ k : ↥K, (QuotientGroup.mk k : ↥K ⧸ Subgroup.center ↥K) = 1 := by
    intro k
    have hk : k ∈ commutator ↥K := by rw [h.1]; exact Subgroup.mem_top k
    have hle : commutator ↥K ≤ (QuotientGroup.mk' (Subgroup.center ↥K)).ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcon _ _
    exact MonoidHom.mem_ker.1 (hle hk)
  have : Subsingleton (↥K ⧸ Subgroup.center ↥K) := by
    constructor
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rw [h1, h1]
  exact not_subsingleton (↥K ⧸ Subgroup.center ↥K) this

theorem pow_four_of_two_power_seven (g : Perm (Fin 7)) (hg : ∃ n : ℕ, g ^ (2 ^ n) = 1) :
    g ^ 4 = 1 := by
  obtain ⟨n, hn⟩ := hg
  have hord : orderOf g ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  rw [← orderOf_dvd_iff_pow_eq_one, ← lcm_cycleType, Multiset.lcm_dvd]
  intro k hk
  have hk1 : k ∣ 2 ^ n := (dvd_of_mem_cycleType hk).trans hord
  have hk2 : 2 ≤ k := two_le_of_mem_cycleType hk
  have hk7 : k ≤ 7 := (le_card_support_of_mem_cycleType hk).trans (by simpa using g.support.card_le_univ)
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk1
  have hj : j ≤ 2 := by
    by_contra h
    push Not at h
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h
    omega
  have := Nat.pow_dvd_pow 2 hj
  simpa using this

section APDsec

structure APD {X : Type} [Group X] (K : Subgroup X) {n : ℕ}
    (e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin n))) where
  θ : MulAut ↥K →* Perm (Fin n)
  inj : Function.Injective θ
  ind : ∀ φ : MulAut ↥K,
    InducesOn e φ (MulAut.conjNormal (H := alternatingGroup (Fin n)) (θ φ))
  inner : ∀ k : ↥K, θ (MulAut.conj k) =
    ((e (QuotientGroup.mk k) : ↥(alternatingGroup (Fin n))) : Perm (Fin n))

variable {X : Type} [Group X] {K : Subgroup X} {n : ℕ}
  {e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin n))}

theorem APD.exists_inner (D : APD K e) {c : Perm (Fin n)} (hc : sign c = 1) :
    ∃ k : ↥K, D.θ (MulAut.conj k) = c := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective
    (e.symm ⟨c, Perm.mem_alternatingGroup.2 hc⟩)
  refine ⟨k, ?_⟩
  rw [D.inner]
  have : e (QuotientGroup.mk k) = ⟨c, Perm.mem_alternatingGroup.2 hc⟩ := by
    rw [hk]; simp
  rw [this]

theorem rho_conj (k : ↥K) :
    K.normalizerMonoidHom ⟨(k : X), Subgroup.le_normalizer k.2⟩ = MulAut.conj k := by
  ext y
  rfl

theorem conj_comm_aux (hZ : Subgroup.center ↥K = ⊥) {w : X}
    (hw : w ∈ Subgroup.normalizer (K : Set X)) {k : ↥K}
    (h1 : MulAut.conj k * K.normalizerMonoidHom ⟨w, hw⟩ =
      K.normalizerMonoidHom ⟨w, hw⟩ * MulAut.conj k) :
    w * (k : X) * w⁻¹ = k := by
  have hpt : ∀ y : ↥K, (k : X) * (w * (y : X) * w⁻¹) * (k : X)⁻¹ =
      w * ((k : X) * (y : X) * (k : X)⁻¹) * w⁻¹ := by
    intro y
    have := congrArg (fun f : MulAut ↥K => ((f y : ↥K) : X)) h1
    exact this
  have hwkK : w * (k : X) * w⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hw k).1 k.2
  have hw' : w⁻¹ ∈ Subgroup.normalizer (K : Set X) := Subgroup.inv_mem _ hw
  let a : ↥K := k⁻¹ * ⟨w * (k : X) * w⁻¹, hwkK⟩
  have ha : a ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro u
    have huK : w⁻¹ * (u : X) * w ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 hw' u).1 u.2
      simpa using this
    have H := hpt ⟨w⁻¹ * (u : X) * w, huK⟩
    simp only [Subgroup.coe_mk] at H
    have e1 : w * (w⁻¹ * (u : X) * w) * w⁻¹ = u := by group
    rw [e1] at H
    have e2 : w * ((k : X) * (w⁻¹ * (u : X) * w) * (k : X)⁻¹) * w⁻¹ =
        (w * k * w⁻¹) * u * (w * k * w⁻¹)⁻¹ := by group
    rw [e2] at H
    apply Subtype.ext
    show (u : X) * ((k : X)⁻¹ * (w * k * w⁻¹)) = ((k : X)⁻¹ * (w * k * w⁻¹)) * u
    calc (u : X) * ((k : X)⁻¹ * (w * k * w⁻¹))
        = (k : X)⁻¹ * ((k : X) * u * (k : X)⁻¹) * (w * k * w⁻¹) := by group
      _ = (k : X)⁻¹ * ((w * k * w⁻¹) * u * (w * k * w⁻¹)⁻¹) * (w * k * w⁻¹) := by rw [H]
      _ = ((k : X)⁻¹ * (w * k * w⁻¹)) * u := by group
  rw [hZ, Subgroup.mem_bot] at ha
  have := congrArg Subtype.val ha
  simp only [a, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
  calc w * (k : X) * w⁻¹ = (k : X) * ((k : X)⁻¹ * (w * k * w⁻¹)) := by group
    _ = k := by rw [this]; simp

theorem APD.comm_aux (D : APD K e) (hZ : Subgroup.center ↥K = ⊥) {w : X}
    (hw : w ∈ Subgroup.normalizer (K : Set X)) {k : ↥K}
    (h : D.θ (MulAut.conj k) * D.θ (K.normalizerMonoidHom ⟨w, hw⟩) =
      D.θ (K.normalizerMonoidHom ⟨w, hw⟩) * D.θ (MulAut.conj k)) :
    w * (k : X) * w⁻¹ = k :=
  conj_comm_aux hZ hw (D.inj (by rw [map_mul, map_mul]; exact h))

end APDsec

theorem even_of_fixes_center (hH : HatSevenOddInverts) {Y : Type} [Group Y] (hY : IsHatSeven Y)
    (e : (Y ⧸ Subgroup.center Y) ≃* ↥(alternatingGroup (Fin 7))) (φ : MulAut Y)
    (hφ : ∀ z ∈ Subgroup.center Y, φ z = z) (σ : Perm (Fin 7))
    (hσ : InducesOn e φ (MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ)) :
    sign σ = 1 := by
  by_contra hodd
  have hodd' : sign σ = -1 := by
    rcases Int.units_eq_one_or (sign σ) with h | h
    · exact absurd h hodd
    · exact h
  have hinv := hH Y hY e φ σ hodd' hσ
  have hc3 : Nat.card (Subgroup.center Y) = 3 := hY.2.1
  obtain ⟨z, hz⟩ : ∃ z : Subgroup.center Y, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton (Subgroup.center Y) := ⟨fun a b => (hcon a).trans (hcon b).symm⟩
    have := Finite.card_le_one_iff_subsingleton.2 this
    omega
  have h1 : φ z = z := hφ z z.2
  have h2 : φ z = (z : Y)⁻¹ := hinv z z.2
  have h3 : (z : Y) * z = 1 := by
    rw [h1] at h2
    exact mul_eq_one_iff_eq_inv.2 h2
  have hord2 : orderOf z ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [sq] using h3
  have hord3 : orderOf z ∣ 3 := by
    rw [← hc3]; exact orderOf_dvd_natCard z
  have : orderOf z ∣ Nat.gcd 2 3 := Nat.dvd_gcd hord2 hord3
  have h1' : orderOf z = 1 := by simpa using this
  exact hz (orderOf_eq_one_iff.1 h1')

section PermData

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}

theorem mem_sig_iff {n : ℕ} (θ : MulAut ↥K →* Perm (Fin n)) (T : Subgroup X) {s : Perm (Fin n)} :
    s ∈ (inducedAutGroup T K).map θ ↔ ∃ (t : X) (ht : t ∈ Subgroup.normalizer (K : Set X)),
      t ∈ T ∧ θ (K.normalizerMonoidHom ⟨t, ht⟩) = s := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    obtain ⟨w, hw, hwT, rfl⟩ := mem_inducedAutGroup.1 hφ
    exact ⟨w, hw, hwT, rfl⟩
  · rintro ⟨t, ht, htT, rfl⟩
    exact ⟨_, mem_inducedAutGroup.2 ⟨t, ht, htT, rfl⟩, rfl⟩

theorem sd_fixes_center {x : X} (hxz : ∀ z ∈ Subgroup.center ↥K, x * (z : X) * x⁻¹ = z)
    (hodd : ∀ z ∈ Subgroup.center ↥K, ∀ m : ℕ, z ^ (2 ^ m) = 1 → z = 1) {Sd : Subgroup X}
    (hSd2 : ∀ t ∈ Sd, ∃ m : ℕ, t ^ (2 ^ m) = 1)
    (hSdinv : ∀ c ∈ Subgroup.centralizer ({x} : Set X), c ∈ Subgroup.normalizer (Sd : Set X))
    {t : X} (htT : t ∈ Sd) (ht : t ∈ Subgroup.normalizer (K : Set X)) :
    ∀ z ∈ Subgroup.center ↥K, K.normalizerMonoidHom ⟨t, ht⟩ z = z := by
  intro z hz
  have hzC : (z : X) ∈ Subgroup.centralizer ({x} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (z : X) * x = (x * z * x⁻¹) * x := by rw [hxz z hz]
      _ = x * z := by group
  have hzn := hSdinv _ hzC
  have hzt : (z : X) * t * (z : X)⁻¹ ∈ Sd := (Subgroup.mem_normalizer_iff.1 hzn t).1 htT
  have hu : (z : X) * t * (z : X)⁻¹ * t⁻¹ ∈ Sd := Sd.mul_mem hzt (Sd.inv_mem htT)
  have hρz : K.normalizerMonoidHom ⟨t, ht⟩ z⁻¹ ∈ Subgroup.center ↥K := by
    have := Subgroup.map_center_eq (K.normalizerMonoidHom ⟨t, ht⟩)
    rw [← this]
    exact Subgroup.mem_map_of_mem _ (Subgroup.inv_mem _ hz)
  have hucen : z * K.normalizerMonoidHom ⟨t, ht⟩ z⁻¹ ∈ Subgroup.center ↥K :=
    Subgroup.mul_mem _ hz hρz
  have hucoe : ((z * K.normalizerMonoidHom ⟨t, ht⟩ z⁻¹ : ↥K) : X) =
      (z : X) * t * (z : X)⁻¹ * t⁻¹ := by
    show (z : X) * (t * (z : X)⁻¹ * t⁻¹) = (z : X) * t * (z : X)⁻¹ * t⁻¹
    group
  obtain ⟨m, hm⟩ := hSd2 _ hu
  have hn' : (z * K.normalizerMonoidHom ⟨t, ht⟩ z⁻¹) ^ (2 ^ m) = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, hucoe]; exact hm)
  have h1 := hodd _ hucen m hn'
  have h2 : K.normalizerMonoidHom ⟨t, ht⟩ z⁻¹ = z⁻¹ := by
    have := mul_eq_one_iff_eq_inv.1 h1
    exact inv_eq_iff_eq_inv.1 this.symm
  have h3 := congrArg (fun w => w⁻¹) h2
  simpa using h3

theorem perm_data_triv {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ}
    {e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin n))} (D : APD K e)
    (hZ : Subgroup.center ↥K = ⊥) {x : X} (hxp : x ^ p = 1)
    (hxN : x ∈ Subgroup.normalizer (K : Set X)) {Sd : Subgroup X}
    (hSdC : Sd ≤ Subgroup.centralizer ({x} : Set X)) (hSd2 : ∀ t ∈ Sd, ∃ m : ℕ, t ^ (2 ^ m) = 1)
    (hSdN : Sd ≤ Subgroup.normalizer (K : Set X))
    (hSdinv : ∀ c ∈ Subgroup.centralizer ({x} : Set X), c ∈ Subgroup.normalizer (Sd : Set X)) :
    ∀ s ∈ (inducedAutGroup Sd K).map D.θ,
      (∀ y, D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) y ≠ y → s y = y) ∧
      (s = 1 ∨ (fixF (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩))).card = 2 ∨
        ((fixF (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩))).card = 4 ∧
          IsDT (fixF (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩))) s)) := by
  set σ := D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) with hσdef
  have hσp : σ ^ p = 1 := by
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p = 1 := Subtype.ext hxp
    rw [hσdef, ← map_pow, ← map_pow, h1, map_one, map_one]
  let Sig : Subgroup (Perm (Fin n)) := (inducedAutGroup Sd K).map D.θ
  have hexp : ∀ s ∈ Sig, ∃ m : ℕ, s ^ (2 ^ m) = 1 := by
    intro s hs
    obtain ⟨t, ht, htT, rfl⟩ := (mem_sig_iff D.θ Sd).1 hs
    obtain ⟨m, hm⟩ := hSd2 t htT
    refine ⟨m, ?_⟩
    have h1 : (⟨t, ht⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ (2 ^ m) = 1 := Subtype.ext hm
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  have hC : ∀ s ∈ Sig, Commute s σ := by
    intro s hs
    obtain ⟨t, ht, htT, rfl⟩ := (mem_sig_iff D.θ Sd).1 hs
    have h1 : t * x = x * t := Subgroup.mem_centralizer_singleton_iff.1 (hSdC htT)
    have h2 : (⟨t, ht⟩ : ↥(Subgroup.normalizer (K : Set X))) * ⟨x, hxN⟩ =
        ⟨x, hxN⟩ * ⟨t, ht⟩ := Subtype.ext h1
    show D.θ (K.normalizerMonoidHom ⟨t, ht⟩) * σ = σ * D.θ (K.normalizerMonoidHom ⟨t, ht⟩)
    rw [hσdef, ← map_mul, ← map_mul, ← map_mul, ← map_mul, h2]
  have hN : ∀ c : Perm (Fin n), Commute c σ → sign c = 1 → ∀ s ∈ Sig, c * s * c⁻¹ ∈ Sig := by
    intro c hc hsg s hs
    obtain ⟨k, hk⟩ := D.exists_inner hsg
    have hkcomm : D.θ (MulAut.conj k) * D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) =
        D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) * D.θ (MulAut.conj k) := by
      rw [hk]; exact hc.eq
    have hkx := D.comm_aux hZ hxN hkcomm
    have hkC : (k : X) ∈ Subgroup.centralizer ({x} : Set X) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (k : X) * x = (x * k * x⁻¹) * x := by rw [hkx]
        _ = x * k := by group
    have hkn := hSdinv _ hkC
    obtain ⟨t, ht, htT, rfl⟩ := (mem_sig_iff D.θ Sd).1 hs
    have hkt : (k : X) * t * (k : X)⁻¹ ∈ Sd := (Subgroup.mem_normalizer_iff.1 hkn t).1 htT
    have hktN : (k : X) * t * (k : X)⁻¹ ∈ Subgroup.normalizer (K : Set X) := hSdN hkt
    have hconj : MulAut.conj k * K.normalizerMonoidHom ⟨t, ht⟩ =
        K.normalizerMonoidHom ⟨(k : X) * t * (k : X)⁻¹, hktN⟩ * MulAut.conj k := by
      ext y
      show (k : X) * (t * (y : X) * t⁻¹) * (k : X)⁻¹ =
        ((k : X) * t * (k : X)⁻¹) * ((k : X) * (y : X) * (k : X)⁻¹) * ((k : X) * t * (k : X)⁻¹)⁻¹
      group
    have h2 : c * D.θ (K.normalizerMonoidHom ⟨t, ht⟩) =
        D.θ (K.normalizerMonoidHom ⟨(k : X) * t * (k : X)⁻¹, hktN⟩) * c := by
      rw [← hk, ← map_mul, ← map_mul, hconj]
    have h3 : c * D.θ (K.normalizerMonoidHom ⟨t, ht⟩) * c⁻¹ =
        D.θ (K.normalizerMonoidHom ⟨(k : X) * t * (k : X)⁻¹, hktN⟩) := by
      rw [h2]; group
    rw [h3]
    exact (mem_sig_iff D.θ Sd).2 ⟨_, hktN, hkt, rfl⟩
  exact (locA hp hp2 hσp (Sg := Sig) hexp hC hN).1

theorem perm_data_hat (hH : HatSevenOddInverts)
    (hK : IsComponentOf K ⊤)
    (hodd : ∀ z ∈ Subgroup.center ↥K, ∀ m : ℕ, z ^ (2 ^ m) = 1 → z = 1)
    {e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))} (D : APD K e)
    (hZ : Nat.card (Subgroup.center ↥K) = 3) {x : X} (hx3 : x ^ 3 = 1)
    (hxN : x ∈ Subgroup.normalizer (K : Set X))
    (hσ1 : D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) ≠ 1) {Sd : Subgroup X}
    (hSdC : Sd ≤ Subgroup.centralizer ({x} : Set X)) (hSd2 : ∀ t ∈ Sd, ∃ m : ℕ, t ^ (2 ^ m) = 1)
    (hSdN : Sd ≤ Subgroup.normalizer (K : Set X))
    (hSdinv : ∀ c ∈ Subgroup.centralizer ({x} : Set X), c ∈ Subgroup.normalizer (Sd : Set X)) :
    ∀ s ∈ (inducedAutGroup Sd K).map D.θ,
      (∀ y, D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) y ≠ y → s y = y) ∧
      (s = 1 ∨ ((fixF (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩))).card = 4 ∧
        IsDT (fixF (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩))) s)) := by
  set σ := D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) with hσdef
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 := Subtype.ext hx3
    rw [hσdef, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσev : sign σ = 1 := by
    rcases Int.units_eq_one_or (sign σ) with h | h
    · exact h
    · have h1 : (-1 : ℤˣ) ^ 3 = 1 := by simpa [map_pow, h] using congrArg sign hσ3
      exact absurd h1 (by decide)
  let Sig : Subgroup (Perm (Fin 7)) := (inducedAutGroup Sd K).map D.θ
  have hexp : ∀ s ∈ Sig, ∃ m : ℕ, s ^ (2 ^ m) = 1 := by
    intro s hs
    obtain ⟨t, ht, htT, rfl⟩ := (mem_sig_iff D.θ Sd).1 hs
    obtain ⟨m, hm⟩ := hSd2 t htT
    refine ⟨m, ?_⟩
    have h1 : (⟨t, ht⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ (2 ^ m) = 1 := Subtype.ext hm
    rw [← map_pow, ← map_pow, h1, map_one, map_one]
  have hC : ∀ s ∈ Sig, Commute s σ := by
    intro s hs
    obtain ⟨t, ht, htT, rfl⟩ := (mem_sig_iff D.θ Sd).1 hs
    have h1 : t * x = x * t := Subgroup.mem_centralizer_singleton_iff.1 (hSdC htT)
    have h2 : (⟨t, ht⟩ : ↥(Subgroup.normalizer (K : Set X))) * ⟨x, hxN⟩ =
        ⟨x, hxN⟩ * ⟨t, ht⟩ := Subtype.ext h1
    show D.θ (K.normalizerMonoidHom ⟨t, ht⟩) * σ = σ * D.θ (K.normalizerMonoidHom ⟨t, ht⟩)
    rw [hσdef, ← map_mul, ← map_mul, ← map_mul, ← map_mul, h2]
  have hY : IsHatSeven ↥K := ⟨hK.2.2.1, hZ, ⟨e⟩⟩
  obtain ⟨k₀, hk₀⟩ := D.exists_inner hσev
  have hρx : K.normalizerMonoidHom ⟨x, hxN⟩ = MulAut.conj k₀ := D.inj (by rw [hk₀])
  have hxz : ∀ z ∈ Subgroup.center ↥K, x * (z : X) * x⁻¹ = z := by
    intro z hz
    have h1 : ((K.normalizerMonoidHom ⟨x, hxN⟩ z : ↥K) : X) =
        ((MulAut.conj k₀ z : ↥K) : X) := by rw [hρx]
    have h2 : x * (z : X) * x⁻¹ = (k₀ : X) * z * (k₀ : X)⁻¹ := h1
    rw [h2]
    have hz' : k₀ * z = z * k₀ := Subgroup.mem_center_iff.1 hz k₀
    calc (k₀ : X) * z * (k₀ : X)⁻¹ = ((k₀ * z : ↥K) : X) * (k₀ : X)⁻¹ := rfl
      _ = ((z * k₀ : ↥K) : X) * (k₀ : X)⁻¹ := by rw [hz']
      _ = z := by simp
  have hev : ∀ s ∈ Sig, sign s = 1 := by
    intro s hs
    obtain ⟨t, ht, htT, rfl⟩ := (mem_sig_iff D.θ Sd).1 hs
    exact even_of_fixes_center hH hY e (K.normalizerMonoidHom ⟨t, ht⟩)
      (sd_fixes_center hxz hodd hSd2 hSdinv htT ht) _ (D.ind _)
  intro s hs
  exact locB7 hσ3 hσ1 (hC s hs).eq (hev s hs) (pow_four_of_two_power_seven s (hexp s hs))

theorem perm_data (hH : HatSevenOddInverts) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : IsComponentOf K ⊤)
    (hodd : ∀ z ∈ Subgroup.center ↥K, ∀ m : ℕ, z ^ (2 ^ m) = 1 → z = 1) {n : ℕ}
    {e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin n))} (D : APD K e)
    (hZ : Subgroup.center ↥K = ⊥ ∨ (n = 7 ∧ Nat.card (Subgroup.center ↥K) = 3 ∧ p = 3))
    {x : X} (hxp : x ^ p = 1) (hxN : x ∈ Subgroup.normalizer (K : Set X))
    (hσ1 : D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) ≠ 1) {Sd : Subgroup X}
    (hSdC : Sd ≤ Subgroup.centralizer ({x} : Set X)) (hSd2 : ∀ t ∈ Sd, ∃ m : ℕ, t ^ (2 ^ m) = 1)
    (hSdN : Sd ≤ Subgroup.normalizer (K : Set X))
    (hSdinv : ∀ c ∈ Subgroup.centralizer ({x} : Set X), c ∈ Subgroup.normalizer (Sd : Set X)) :
    ∀ s ∈ (inducedAutGroup Sd K).map D.θ,
      (∀ y, D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) y ≠ y → s y = y) ∧
      (s = 1 ∨ (fixF (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩))).card = 2 ∨
        ((fixF (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩))).card = 4 ∧
          IsDT (fixF (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩))) s)) := by
  rcases hZ with hZ | ⟨rfl, hZ3, rfl⟩
  · exact perm_data_triv hp hp2 D hZ hxp hxN hSdC hSd2 hSdN hSdinv
  · intro s hs
    obtain ⟨h1, h2⟩ := perm_data_hat hH hK hodd D hZ3 hxp hxN hσ1 hSdC hSd2 hSdN hSdinv s hs
    exact ⟨h1, h2.elim Or.inl fun h => Or.inr (Or.inr h)⟩

theorem perm_data_seven (hH : HatSevenOddInverts)
    (hK : IsComponentOf K ⊤) (hO3 : GLAPPrimeCore 3 ↥K = ⊥)
    {e : (↥K ⧸ Subgroup.center ↥K) ≃* ↥(alternatingGroup (Fin 7))} (D : APD K e)
    {x : X} (hx3 : x ^ 3 = 1) (hxN : x ∈ Subgroup.normalizer (K : Set X))
    (hσ1 : D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) ≠ 1) :
    ∀ s ∈ (inducedAutGroup (pCoreOf 2 (Subgroup.centralizer ({x} : Set X))) K).map D.θ,
      (∀ y, D.θ (K.normalizerMonoidHom ⟨x, hxN⟩) y ≠ y → s y = y) ∧
      (s = 1 ∨ ((fixF (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩))).card = 4 ∧
        IsDT (fixF (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩))) s)) := by
  have hT₀N : pCoreOf 2 (Subgroup.centralizer ({x} : Set X)) ≤ Subgroup.normalizer (K : Set X) :=
    pCoreOf_centralizer_singleton_le_normalizer Nat.prime_three (by norm_num) hK hO3 hx3
  have hKq := isQuasisimple_of_comp hK
  have hodd := center_no_two_elements Nat.prime_three (by norm_num) hO3
  have hZ : Subgroup.center ↥K = ⊥ ∨ (7 = 7 ∧ Nat.card (Subgroup.center ↥K) = 3 ∧ 3 = 3) := by
    rcases center_cases_seven hKq hodd e with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h, rfl⟩
  have hdata := perm_data hH Nat.prime_three (by norm_num) hK hodd D hZ hx3 hxN hσ1
    (Sd := pCoreOf 2 (Subgroup.centralizer ({x} : Set X)))
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (fun t ht => by
      obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2
        (Subgroup.centralizer ({x} : Set X))) ⟨t, ht⟩
      exact ⟨m, congrArg Subtype.val hm⟩)
    hT₀N (fun c hc => le_normalizer_pCoreOf 2 _ hc)
  intro s hs
  refine ⟨(hdata s hs).1, ?_⟩
  have hcard2 : (fixF (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩))).card ≠ 2 := by
    intro h
    have hσ3 : (D.θ (K.normalizerMonoidHom ⟨x, hxN⟩)) ^ 3 = 1 := by
      have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 := Subtype.ext hx3
      rw [← map_pow, ← map_pow, h1, map_one, map_one]
    have := card_modEq_fixF Nat.prime_three hσ3
    rw [h, Fintype.card_fin] at this
    exact absurd this (by decide)
  rcases (hdata s hs).2 with h | h | h
  · exact Or.inl h
  · exact absurd h hcard2
  · exact Or.inr h

end PermData

section V4fix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem commute_preserves_fixF {σ g : Perm Ω} (hg : g * σ = σ * g) (y : Ω) :
    y ∈ fixF σ ↔ g y ∈ fixF σ := by
  have hcx : g (σ y) = σ (g y) := congrArg (fun f : Perm Ω => f y) hg
  simp only [mem_fixF]
  constructor
  · intro hy; rw [← hcx, hy]
  · intro hy; apply g.injective; rw [hcx, hy]

theorem V4_commute {σ s : Perm Ω} (hF : (fixF σ).card = 4) (hs : s ∈ V4 (fixF σ) hF) :
    s * σ = σ * s := by
  rcases (mem_V4 hF).1 hs with h | h
  · rw [h]; simp
  · ext y
    simp only [Perm.mul_apply]
    by_cases hy : y ∈ fixF σ
    · have hσy : σ y = y := mem_fixF.1 hy
      have hsy : s y ∈ fixF σ := (isDT_preserves h y).1 hy
      rw [hσy, mem_fixF.1 hsy]
    · have hσy : σ y ∉ fixF σ := fun hh => hy (mem_fixF.2 (σ.injective (mem_fixF.1 hh)))
      rw [h.1 y hy, h.1 (σ y) hσy]

theorem V4_conj {σ s g : Perm Ω} (hF : (fixF σ).card = 4) (hs : s ∈ V4 (fixF σ) hF)
    (hg : g * σ = σ * g) : g * s * g⁻¹ ∈ V4 (fixF σ) hF := by
  rcases (mem_V4 hF).1 hs with h | h
  · rw [h]; left; simp
  · refine (mem_V4 hF).2 (Or.inr ⟨fun y hy => ?_, ?_, fun y hy => ?_⟩)
    · have hy' : g⁻¹ y ∉ fixF σ := fun hh => hy (by
        have := (commute_preserves_fixF hg _).1 hh
        simpa using this)
      simp only [Perm.mul_apply]
      rw [h.1 _ hy']; simp
    · have h2 := h.2.1
      calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
        _ = 1 := by rw [h2]; group
    · intro hgy
      simp only [Perm.mul_apply] at hgy
      have hy' : g⁻¹ y ∈ fixF σ := by
        have := (commute_preserves_fixF hg (g⁻¹ y)).1
        by_contra hh
        have hh' : g (g⁻¹ y) ∈ fixF σ := by rw [pai]; exact hy
        exact hh ((commute_preserves_fixF hg (g⁻¹ y)).2 hh')
      apply h.2.2 _ hy'
      apply g.injective
      simpa using hgy

end V4fix

