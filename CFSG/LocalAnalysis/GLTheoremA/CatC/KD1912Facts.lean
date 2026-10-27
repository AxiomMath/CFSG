module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD1912Core
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm35Aux2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.YS03Lie

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD1912

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55Ns
open scoped commutatorElement

variable {p : ℕ}

theorem odd_card_commutator_of_odd_core {S : Type} [Group S] [Finite S] (hp : p.Prime)
    {M A H : Subgroup (MulAut S)} (hM : M.Normal)
    (hMo : Odd ((innerAut S).relIndex M)) (hAM : A ≤ M) {x : MulAut S}
    (hAc : A ≤ Subgroup.centralizer ({x} : Set (MulAut S))) (hIH : innerAut S ≤ H)
    (hAH : A ≤ Subgroup.normalizer (H : Set (MulAut S)))
    (hcore : Odd (Nat.card (GLAPPrimeCoreOf p
      (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S)))))) :
    Odd (Nat.card (⁅GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))), A⁆ :
      Subgroup (MulAut S))) := by
  classical
  set X : Subgroup (MulAut S) :=
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) with hX
  have hInorm : (innerAut S).Normal := ys03_innerAut_normal S
  have hAX : A ≤ Subgroup.normalizer (X : Set (MulAut S)) := by
    intro a ha
    refine mem_normalizer_gLAPPrimeCoreOf p ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hN1 := Subgroup.mem_normalizer_iff.mp (hAH ha) y
    have hN2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hAc ha)) y
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr hN1 hN2
  have hYle : ⁅X, A⁆ ≤ X ⊓ M := by
    rw [Subgroup.commutator_le]
    intro g hg a ha
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have h1 : a * g⁻¹ * a⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hAX ha) g⁻¹).1 (X.inv_mem hg)
      have := X.mul_mem hg h1
      simpa [commutatorElement_def, mul_assoc] using this
    · rw [commutatorElement_def]
      exact M.mul_mem (hM.conj_mem a (hAM ha) g) (M.inv_mem (hAM ha))
  rw [Nat.odd_iff]
  by_contra h
  have h2 : 2 ∣ Nat.card (⁅X, A⁆ : Subgroup (MulAut S)) := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(⁅X, A⁆ : Subgroup (MulAut S))) 2 h2
  have hyXM := hYle y.2
  have hyord : orderOf (y : MulAut S) = 2 := by rw [Subgroup.orderOf_coe]; exact hy
  have hyI : (y : MulAut S) ∈ innerAut S := by
    haveI := hInorm
    set q := (QuotientGroup.mk' ((innerAut S).subgroupOf M) : M →* M ⧸ (innerAut S).subgroupOf M)
    set ym : M := ⟨y, hyXM.2⟩
    have hdvd1 : orderOf (q ym) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [← map_pow]
      have hy2 : ym ^ 2 = 1 := by
        apply Subtype.ext
        have h := pow_orderOf_eq_one (y : MulAut S)
        rw [hyord] at h
        simpa [ym] using h
      rw [hy2, map_one]
    have hdvd2 : orderOf (q ym) ∣ (innerAut S).relIndex M := by
      rw [Subgroup.relIndex]
      exact orderOf_dvd_natCard _
    have hone : orderOf (q ym) = 1 := by
      have hgcd := Nat.dvd_gcd hdvd1 hdvd2
      have hge : Nat.gcd 2 ((innerAut S).relIndex M) = 1 := by
        rcases hMo with ⟨k, hk⟩
        rw [hk]
        simp [Nat.gcd_comm]
      rw [hge, Nat.dvd_one] at hgcd
      exact hgcd
    rw [orderOf_eq_one_iff] at hone
    have hmem : ym ∈ (innerAut S).subgroupOf M := (QuotientGroup.eq_one_iff ym).mp hone
    exact (Subgroup.mem_subgroupOf.1 hmem)
  have hXle : X ≤ H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)) :=
    gLAPPrimeCoreOf_le p _
  have hyC : (y : MulAut S) ∈ Subgroup.centralizer ({x} : Set (MulAut S)) :=
    (Subgroup.mem_inf.1 (hXle hyXM.1)).2
  have hsub : innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S)) ≤
      H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)) := inf_le_inf_right _ hIH
  have hyO : (y : MulAut S) ∈ GLAPPrimeCoreOf p
      (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) :=
    inf_gLAPPrimeCoreOf_le hp hsub
      (Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨hyI, hyC⟩, hyXM.1⟩)
  have hdvd : orderOf (⟨y, hyO⟩ : ↥(GLAPPrimeCoreOf p
      (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S))))) ∣ Nat.card _ :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hyord] at hdvd
  rcases hcore with ⟨k, hk⟩
  omega


theorem odd_card_commutator_of_isCyclic_core {S : Type} [Group S] [Finite S] (hp : p.Prime)
    {A H : Subgroup (MulAut S)}
    (hOut : ⁅(⊤ : Subgroup (MulAut S)), ⊤⁆ ≤ innerAut S) (hA : IsPGroup p A) {x : MulAut S}
    (hAc : A ≤ Subgroup.centralizer ({x} : Set (MulAut S))) (hIH : innerAut S ≤ H)
    (hAH : A ≤ Subgroup.normalizer (H : Set (MulAut S)))
    (hcore : IsCyclic (GLAPPrimeCoreOf p
      (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S))))) :
    Odd (Nat.card (⁅GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))), A⁆ :
      Subgroup (MulAut S))) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set X : Subgroup (MulAut S) :=
    GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) with hX
  set Y : Subgroup (MulAut S) := ⁅X, A⁆ with hY
  have hXle : X ≤ H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)) :=
    Lemma512Ns.gLAPPrimeCoreOf_le p _
  have hAX : A ≤ Subgroup.normalizer (X : Set (MulAut S)) := by
    intro a ha
    refine Lemma512Ns.mem_normalizer_gLAPPrimeCoreOf p ?_
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hN1 := Subgroup.mem_normalizer_iff.mp (hAH ha) y
    have hN2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hAc ha)) y
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr hN1 hN2
  have hYX : Y ≤ X := by
    rw [hY]
    rw [Subgroup.commutator_le]
    intro g hg a ha
    have h1 : a * g⁻¹ * a⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hAX ha) g⁻¹).1 (X.inv_mem hg)
    have := X.mul_mem hg h1
    simpa [commutatorElement_def, mul_assoc] using this
  have hYI : Y ≤ innerAut S := by
    rw [hY]
    exact (Subgroup.commutator_mono (le_top : X ≤ ⊤) (le_top : A ≤ ⊤)).trans hOut
  have hXI : X ⊓ innerAut S ≤ GLAPPrimeCoreOf p
      (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) := by
    have hsub : innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S)) ≤
        H ⊓ Subgroup.centralizer ({x} : Set (MulAut S)) := inf_le_inf_right _ hIH
    refine (le_inf (le_inf inf_le_right (inf_le_left.trans (hXle.trans inf_le_right)))
      inf_le_left).trans ?_
    exact inf_gLAPPrimeCoreOf_le hp hsub
  have hYZ : Y ≤ GLAPPrimeCoreOf p
      (innerAut S ⊓ Subgroup.centralizer ({x} : Set (MulAut S))) :=
    (le_inf hYX hYI).trans hXI
  haveI hYcyc : IsCyclic ↥Y :=
    isCyclic_of_injective (Subgroup.inclusion hYZ) (Subgroup.inclusion_injective hYZ)
  have hhA : A ≤ Subgroup.normalizer (Y : Set (MulAut S)) := by
    rw [hY]
    exact Subgroup.normalizer_commutator_ge_right (H₁ := X) (H₂ := A)
  have hcopX : Nat.Coprime p (Nat.card ↥X) := by
    rw [hX]
    unfold GLAPPrimeCoreOf
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    exact coprime_card_pPrimeCore p _
  have hcopY : Nat.Coprime p (Nat.card ↥Y) :=
    hcopX.coprime_dvd_right (Subgroup.card_dvd_of_le hYX)
  have hYY : ⁅Y, A⁆ = Y := by
    rw [hY]
    exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25Ns.commutator_commutator_eq hA hAX hcopX
  have hdisj : ⁅Y, A⁆ ⊓ Subgroup.centralizer (A : Set (MulAut S)) = ⊥ :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Thm35.commutator_inf_centralizer_eq_bot hp hA hhA hcopY
  rw [hYY] at hdisj
  have hYodd : Odd (Nat.card ↥Y) := by
    rw [Nat.odd_iff]
    by_contra hne
    have h2dvd : 2 ∣ Nat.card ↥Y := by
      by_contra hnd
      exact hne (by omega)
    haveI : Fintype ↥Y := Fintype.ofFinite _
    have huniq : ∀ y₁ y₂ : ↥Y, orderOf y₁ = 2 → orderOf y₂ = 2 → y₁ = y₂ := by
      intro y₁ y₂ h₁ h₂
      have hd : 2 ∣ Fintype.card ↥Y := by
        simpa [Nat.card_eq_fintype_card] using h2dvd
      have hcard : (Finset.univ.filter (fun y : ↥Y => orderOf y = 2)).card = 1 := by
        have h := IsCyclic.card_orderOf_eq_totient (α := ↥Y) (d := 2) hd
        simpa using h
      exact Finset.card_le_one.mp (le_of_eq hcard) y₁ (by simp [h₁]) y₂ (by simp [h₂])
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 2 h2dvd
    have ht' : orderOf (t : MulAut S) = 2 := (Subgroup.orderOf_coe t).trans ht
    have htC : (t : MulAut S) ∈ Subgroup.centralizer (A : Set (MulAut S)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hmem : a * (t : MulAut S) * a⁻¹ ∈ Y :=
        (Subgroup.mem_normalizer_iff.mp (hhA ha) (t : MulAut S)).1 t.2
      have heq : (⟨a * (t : MulAut S) * a⁻¹, hmem⟩ : ↥Y) = t := by
        refine huniq _ _ ?_ ht
        rw [← Subgroup.orderOf_coe]
        calc orderOf (a * (t : MulAut S) * a⁻¹)
            = orderOf (MulAut.conj a (t : MulAut S)) := by rw [MulAut.conj_apply]
          _ = orderOf (t : MulAut S) := MulEquiv.orderOf_eq (MulAut.conj a) _
          _ = 2 := ht'
      have h1 : a * (t : MulAut S) * a⁻¹ = (t : MulAut S) := congrArg Subtype.val heq
      calc a * (t : MulAut S) = (a * (t : MulAut S) * a⁻¹) * a := by group
        _ = (t : MulAut S) * a := by rw [h1]
    have hmem : (t : MulAut S) ∈ (⊥ : Subgroup (MulAut S)) :=
      hdisj ▸ Subgroup.mem_inf.2 ⟨t.2, htC⟩
    rw [Subgroup.mem_bot] at hmem
    have ht1 : t = 1 := Subtype.ext hmem
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  rw [hY]
  exact hYodd

theorem kd1912TwoLieAt_of_facts {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : TauCeti.LieTypeIndex → Prop}
    (h : ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
      ∀ d : TauCeti.ValidLieTypeIndex, k2Lie p d.1 → P d.1 →
        Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
          OddCoreFact p S ∨ CyclicCoreFact p S) :
    KD1912TwoLieAt p P := by
  intro S _ _ hS hnc d hd hP e A hA D hD H hH hAH
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hpA : IsPGroup p A := hA.isPGroup
  have hcardD : Nat.card D = p := by simpa using hD.2.2
  have hDne : D ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcardD
    exact hp.ne_one hcardD.symm
  obtain ⟨⟨x, hxD⟩, hx1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hDne
  have hx1 : x ≠ 1 := fun hh => hx1' (Subtype.ext hh)
  have hxA : x ∈ A := hD.1 hxD
  have hxord : orderOf x = p := orderOf_eq_prime (hA.2 x hxA) hx1
  have hxAc : A ≤ Subgroup.centralizer ({x} : Set (MulAut S)) := by
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hA ha hxA)
  have hmono : ⁅localDeltaIn p H D, A⁆ ≤
      ⁅GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut S))), A⁆ :=
    Subgroup.commutator_mono (ys03_localDelta_le H D hxD hx1) le_rfl
  rcases h S hS hnc d hd hP e with hOdd | hCyc
  · obtain ⟨M, hMn, hIM, hMo, hpow⟩ := hOdd.1
    have hAM : A ≤ M := by
      intro a ha
      obtain ⟨k2, hk2⟩ := hpow a
      obtain ⟨k1, hk1⟩ := hpA ⟨a, ha⟩
      have hk1' : a ^ p ^ k1 = 1 := by simpa using hk1
      set q : MulAut S →* MulAut S ⧸ M := QuotientGroup.mk' M with hq
      have hdvd1 : orderOf a ∣ p ^ k1 := orderOf_dvd_of_pow_eq_one hk1'
      have hdvd2 : orderOf (q a) ∣ p ^ k1 := (orderOf_map_dvd q a).trans hdvd1
      have hdvd3 : orderOf (q a) ∣ 2 ^ k2 := by
        refine orderOf_dvd_of_pow_eq_one ?_
        rw [← map_pow,
          show q (a ^ 2 ^ k2) = 1 from (QuotientGroup.eq_one_iff (a ^ 2 ^ k2)).2 hk2]
      have hcop : Nat.Coprime (2 ^ k2) (p ^ k1) :=
        ((Nat.coprime_primes Nat.prime_two hp).2 hp2.symm).pow k2 k1
      have hone : orderOf (q a) = 1 := by
        have hdvd : orderOf (q a) ∣ 1 := by
          rw [← hcop.gcd_eq_one]
          exact Nat.dvd_gcd hdvd3 hdvd2
        rwa [Nat.dvd_one] at hdvd
      rw [orderOf_eq_one_iff] at hone
      exact (QuotientGroup.eq_one_iff a).1 hone
    haveI := hMn
    exact (odd_card_commutator_of_odd_core hp hMn hMo hAM hxAc hH hAH
      (hOdd.2 x hxord)).of_dvd_nat (Subgroup.card_dvd_of_le hmono)
  · exact (odd_card_commutator_of_isCyclic_core hp hCyc.1 hpA hxAc hH hAH
      (hCyc.2 x hxord)).of_dvd_nat (Subgroup.card_dvd_of_le hmono)

end CFSG.LocalAnalysis.GLTheoremA.KD1912
