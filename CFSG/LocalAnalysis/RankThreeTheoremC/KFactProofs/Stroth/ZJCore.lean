module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJNormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ

open CFSG Subgroup
open scoped commutatorElement

section Coprime

variable {X : Type*} [Group X]

theorem zj_mem_of_pow_coprime {H : Subgroup X} {x : X} {m n : ℕ} (hmn : Nat.Coprime m n)
    (hm : x ^ m ∈ H) (hn : x ^ n ∈ H) : x ∈ H := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hmn
  have h : x = (x ^ m) ^ a * (x ^ n) ^ b := by
    calc x = x ^ (1 : ℤ) := (zpow_one x).symm
      _ = x ^ (a * (m : ℤ) + b * (n : ℤ)) := by rw [hab]
      _ = (x ^ m) ^ a * (x ^ n) ^ b := by
        rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
  rw [h]
  exact H.mul_mem (H.zpow_mem hm a) (H.zpow_mem hn b)

end Coprime

section TwoClosed

variable {X : Type*} [Group X] [Finite X]

theorem zj_exists_pow_mem_pPrimeCore {p : ℕ} [Fact p.Prime] {g : X}
    (hg : g ∈ CFSG.GH74.GLS.pPrimePCore p X) : ∃ j : ℕ, g ^ (p ^ j) ∈ CFSG.pPrimeCore p X := by
  have hg' : QuotientGroup.mk' (CFSG.pPrimeCore p X) g ∈
      CFSG.pCore p (X ⧸ CFSG.pPrimeCore p X) := hg
  obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (p := p) ⟨_, hg'⟩
  refine ⟨j, ?_⟩
  have h1 : (QuotientGroup.mk' (CFSG.pPrimeCore p X) g) ^ (p ^ j) = 1 := by
    have := congrArg Subtype.val hj
    simpa using this
  rw [← map_pow] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem zj_exists_normal_two_subgroup {p : ℕ} [Fact p.Prime]
    (h2cl : ∀ T₂ : Sylow 2 (CFSG.pPrimeCore p X), (T₂ : Subgroup (CFSG.pPrimeCore p X)).Normal) :
    ∃ P : Subgroup X, P.Normal ∧ IsPGroup 2 P ∧
      (∀ o ∈ CFSG.pPrimeCore p X, (∃ k : ℕ, o ^ (2 ^ k) = 1) → o ∈ P) ∧
      (∀ o ∈ CFSG.pPrimeCore p X, ∃ m : ℕ, Odd m ∧ o ^ m ∈ P) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥(CFSG.pPrimeCore p X)) := inferInstance
  have hPn := h2cl P
  haveI : (CFSG.pPrimeCore p X).Characteristic := CFSG.pPrimeCore_characteristic
  haveI hPch : (P : Subgroup ↥(CFSG.pPrimeCore p X)).Characteristic :=
    Sylow.characteristic_of_normal P hPn
  haveI hch : ((P : Subgroup ↥(CFSG.pPrimeCore p X)).map
      (CFSG.pPrimeCore p X).subtype).Characteristic :=
    Subgroup.characteristic_of_characteristic_of_characteristic
  refine ⟨(P : Subgroup ↥(CFSG.pPrimeCore p X)).map (CFSG.pPrimeCore p X).subtype,
    Subgroup.normal_of_characteristic _, P.isPGroup'.map _, ?_, ?_⟩
  · intro o ho ⟨k, hk⟩
    have hx : (⟨o, ho⟩ : ↥(CFSG.pPrimeCore p X)) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    have hzp : IsPGroup 2 (Subgroup.zpowers (⟨o, ho⟩ : ↥(CFSG.pPrimeCore p X))) := by
      obtain ⟨m, hm, hmk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx)
      rw [IsPGroup.iff_card, Nat.card_zpowers]
      exact ⟨m, hmk⟩
    obtain ⟨Q, hQ⟩ := hzp.exists_le_sylow
    haveI := Sylow.unique_of_normal P hPn
    have hQP : Q = P := Subsingleton.elim _ _
    subst hQP
    exact ⟨⟨o, ho⟩, hQ (Subgroup.mem_zpowers _), rfl⟩
  · intro o ho
    refine ⟨(P : Subgroup ↥(CFSG.pPrimeCore p X)).index, ?_, ?_⟩
    · have h := P.not_dvd_index
      rw [Nat.odd_iff]
      by_contra h2
      exact h (by omega)
    · refine ⟨⟨o, ho⟩ ^ (P : Subgroup ↥(CFSG.pPrimeCore p X)).index, ?_, rfl⟩
      haveI : (P : Subgroup ↥(CFSG.pPrimeCore p X)).Normal := hPn
      have h1 := pow_card_eq_one' (x := (QuotientGroup.mk (⟨o, ho⟩ : ↥(CFSG.pPrimeCore p X)) :
        ↥(CFSG.pPrimeCore p X) ⧸ (P : Subgroup ↥(CFSG.pPrimeCore p X))))
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
      exact h1

theorem zj_two_power_mem_pPrimeCore {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {g : X}
    (hg : g ∈ CFSG.GH74.GLS.pPrimePCore p X) {k : ℕ} (hk : g ^ (2 ^ k) = 1) :
    g ∈ CFSG.pPrimeCore p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj⟩ := zj_exists_pow_mem_pPrimeCore hg
  exact zj_mem_of_pow_coprime (m := p ^ j) (n := 2 ^ k)
    (Nat.Coprime.pow j k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)) hj
    (by rw [hk]; exact one_mem _)

theorem zj_two_power_mem_pCore {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h2cl : ∀ T₂ : Sylow 2 (CFSG.pPrimeCore p X), (T₂ : Subgroup (CFSG.pPrimeCore p X)).Normal)
    {g : X} (hg : g ∈ CFSG.GH74.GLS.pPrimePCore p X) {k : ℕ} (hk : g ^ (2 ^ k) = 1) :
    g ∈ CFSG.pCore 2 X := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPn, hP2, hPmem, -⟩ := zj_exists_normal_two_subgroup h2cl
  exact le_sSup (show P ∈ {K : Subgroup X | K.Normal ∧ IsPGroup 2 K} from ⟨hPn, hP2⟩)
    (hPmem g (zj_two_power_mem_pPrimeCore hp hp2 hg hk) ⟨k, hk⟩)

theorem zj_odd_pow_mem_pCore {p : ℕ} [Fact p.Prime]
    (h2cl : ∀ T₂ : Sylow 2 (CFSG.pPrimeCore p X), (T₂ : Subgroup (CFSG.pPrimeCore p X)).Normal)
    {o : X} (ho : o ∈ CFSG.pPrimeCore p X) : ∃ m : ℕ, Odd m ∧ o ^ m ∈ CFSG.pCore 2 X := by
  obtain ⟨P, hPn, hP2, -, hodd⟩ := zj_exists_normal_two_subgroup h2cl
  obtain ⟨m, hm, hmP⟩ := hodd o ho
  exact ⟨m, hm, le_sSup (show P ∈ {K : Subgroup X | K.Normal ∧ IsPGroup 2 K} from ⟨hPn, hP2⟩) hmP⟩

theorem zj_perfect_le_two_group {K W : Subgroup X} (hK : ⁅K, K⁆ = K) (hW : IsPGroup 2 W)
    (hKW : K ≤ W) : K = ⊥ := by
  by_contra hne
  haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hne
  haveI : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK
  haveI : Group.IsNilpotent K := (hW.to_le hKW).isNilpotent
  exact Group.IsPerfect.not_isNilpotent K inferInstance

end TwoClosed

section PComponent

variable {X : Type} [Group X] [Finite X]

theorem zj_quasisimple_nontrivial {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    Nontrivial Q := by
  haveI := h.2.1.toNontrivial
  exact (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial

theorem zj_pComponent_perfect {p : ℕ} {K : Subgroup X} [K.Normal] (hK : CFSG.IsPComponent p K) :
    ⁅K, K⁆ = K := by
  obtain ⟨K₀, hK₀, -, hmap, hmin⟩ := hK
  by_contra hne
  have hlt : ⁅K, K⁆ < K := lt_of_le_of_ne (Subgroup.commutator_le_left K K) hne
  refine hmin ⁅K, K⁆ hlt (Subgroup.Normal.isSubnormal inferInstance) ?_
  rw [Subgroup.map_commutator, hmap]
  exact Subgroup.isPerfect_iff.mp hK₀.1.1

theorem zj_nontrivial_of_pComponent {p : ℕ} {K : Subgroup X} (hK : CFSG.IsPComponent p K) :
    Nontrivial X := by
  obtain ⟨K₀, hK₀, -⟩ := hK
  haveI := zj_quasisimple_nontrivial hK₀.1
  haveI : Nontrivial (X ⧸ CFSG.pPrimeCore p X) :=
    Function.Injective.nontrivial (f := fun x : ↥K₀ => (x : X ⧸ CFSG.pPrimeCore p X))
      Subtype.val_injective
  exact (QuotientGroup.mk'_surjective (CFSG.pPrimeCore p X)).nontrivial

theorem zj_pCore_quotient_eq_bot {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K C : Subgroup X}
    [K.Normal] [C.Normal] (hK : CFSG.IsPComponent p K) (T : Sylow 2 X)
    (hKT : K ⊔ (T : Subgroup X) = ⊤)
    (h2cl : ∀ T₂ : Sylow 2 (CFSG.pPrimeCore p X), (T₂ : Subgroup (CFSG.pPrimeCore p X)).Normal)
    (hCc : CFSG.pCore 2 X ≤ C) (hKC : ¬ K ≤ C) : CFSG.pCore 2 (X ⧸ C) = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsup : CFSG.pCore 2 (X ⧸ C) =
      sSup {W : Subgroup (X ⧸ C) | W.Normal ∧ IsPGroup 2 W} := rfl
  rw [hsup, sSup_eq_bot]
  rintro W ⟨hWn, hW2⟩
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective C w
  haveI hNn : (W.comap (QuotientGroup.mk' C)).Normal := hWn.comap _
  have hKN : ¬ K ≤ W.comap (QuotientGroup.mk' C) := by
    intro hKN
    apply hKC
    have hle : K.map (QuotientGroup.mk' C) ≤ W := by
      rintro _ ⟨k, hk, rfl⟩
      exact hKN hk
    have hperf : ⁅K.map (QuotientGroup.mk' C), K.map (QuotientGroup.mk' C)⁆ =
        K.map (QuotientGroup.mk' C) := by
      rw [← Subgroup.map_commutator, zj_pComponent_perfect hK]
    have hbot := zj_perfect_le_two_group hperf hW2 hle
    intro k hk
    have hmem : QuotientGroup.mk' C k ∈ K.map (QuotientGroup.mk' C) := ⟨k, hk, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff k).mp hmem
  have hNM := zj_normal_le_pPrimeP hp hp2 hK T hKT hKN
  have hn : n ∈ W.comap (QuotientGroup.mk' C) := hw
  obtain ⟨j, hj⟩ := zj_exists_pow_mem_pPrimeCore (hNM hn)
  obtain ⟨m, hm, hmC⟩ := zj_odd_pow_mem_pCore h2cl hj
  obtain ⟨k, hk⟩ := hW2 ⟨QuotientGroup.mk' C n, hw⟩
  have hk' : n ^ (2 ^ k) ∈ C := by
    have h1 : (QuotientGroup.mk' C n) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    rw [← map_pow] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hnC : n ∈ C := by
    refine zj_mem_of_pow_coprime (m := p ^ j * m) (n := 2 ^ k) ?_ ?_ hk'
    · exact Nat.Coprime.mul_left
        (Nat.Coprime.pow j k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2))
        (Nat.Coprime.pow_right k hm.coprime_two_right)
    · rw [pow_mul]
      exact hCc hmC
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff n).mpr hnC

theorem zj_odd_card_map_le_pPrimeCore {p : ℕ} [Fact p.Prime]
    (h2cl : ∀ T₂ : Sylow 2 (CFSG.pPrimeCore p X), (T₂ : Subgroup (CFSG.pPrimeCore p X)).Normal)
    {C : Subgroup X} [C.Normal] (hCc : CFSG.pCore 2 X ≤ C) {O : Subgroup X}
    (hO : O ≤ CFSG.pPrimeCore p X) : Odd (Nat.card ↥(O.map (QuotientGroup.mk' C))) := by
  by_contra hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card ↥(O.map (QuotientGroup.mk' C)) := by
    rw [Nat.odd_iff] at hodd
    omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(O.map (QuotientGroup.mk' C))) 2 h2
  obtain ⟨o, hoO, hox⟩ := x.2
  obtain ⟨m, hm, hmC⟩ := zj_odd_pow_mem_pCore h2cl (hO hoO)
  have h1 : (x : X ⧸ C) ^ m = 1 := by
    rw [← hox, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (hCc hmC)
  have h3 : orderOf x ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using h1)
  rw [hx] at h3
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h3)

end PComponent

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ
