module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2Z
public import CFSG.LocalAnalysis.OddStandard.ThmCO2KL
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.OddStandard.ThmC.O2

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
def dcE (D : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ D ∧ x * x = 1 ∧ ∀ y ∈ D, x * y = y * x}
  one_mem' := ⟨D.one_mem, mul_one 1, fun y _ => by rw [one_mul, mul_one]⟩
  mul_mem' := by
    rintro x x' ⟨hxD, hx2, hxc⟩ ⟨hx'D, hx'2, hx'c⟩
    refine ⟨D.mul_mem hxD hx'D, ?_, fun y hy => ?_⟩
    · have h1 : x * x' = x' * x := hxc x' hx'D
      calc x * x' * (x * x') = x * (x' * x) * x' := by simp only [mul_assoc]
        _ = x * (x * x') * x' := by rw [h1]
        _ = (x * x) * (x' * x') := by simp only [mul_assoc]
        _ = 1 := by rw [hx2, hx'2, one_mul]
    · calc x * x' * y = x * (x' * y) := mul_assoc _ _ _
        _ = x * (y * x') := by rw [hx'c y hy]
        _ = (x * y) * x' := (mul_assoc _ _ _).symm
        _ = (y * x) * x' := by rw [hxc y hy]
        _ = y * (x * x') := mul_assoc _ _ _
  inv_mem' := by
    rintro x ⟨hxD, hx2, hxc⟩
    refine ⟨D.inv_mem hxD, ?_, fun y hy => ?_⟩
    · rw [← mul_inv_rev, hx2, inv_one]
    · exact (Commute.inv_left (show Commute x y from hxc y hy)).eq

omit [Finite G] in
theorem mem_dcE {D : Subgroup G} {x : G} :
    x ∈ dcE D ↔ x ∈ D ∧ x * x = 1 ∧ ∀ y ∈ D, x * y = y * x := Iff.rfl

omit [Finite G] in
theorem dcE_normal {D : Subgroup G} (hD : D.Normal) : (dcE D).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨hxD, hx2, hxc⟩ := mem_dcE.1 hx
  refine mem_dcE.2 ⟨hD.conj_mem x hxD g, ?_, fun y hy => ?_⟩
  · calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  · have hy' : g⁻¹ * y * g ∈ D := by simpa using hD.conj_mem y hy g⁻¹
    have h := hxc _ hy'
    calc g * x * g⁻¹ * y = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * x) * g⁻¹ := by rw [h]
      _ = y * (g * x * g⁻¹) := by group

theorem dcE_ne_bot {D : Subgroup G} (hD2 : IsPGroup 2 D) (hD : D ≠ ⊥) : dcE D ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).2 hD
  have := hD2.center_nontrivial
  have hc2 : IsPGroup 2 (center D) := hD2.to_subgroup _
  have h2 : 2 ∣ Nat.card (center D) := by
    obtain ⟨n, hn0, hn⟩ := hc2.nontrivial_iff_card.1 inferInstance
    exact hn ▸ dvd_pow_self 2 (Nat.pos_iff_ne_zero.1 hn0)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center D) 2 h2
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    exact absurd hc (by norm_num)
  have hcc : c * c = 1 := by
    have := pow_orderOf_eq_one c
    rwa [hc, pow_two] at this
  have hx : ((c : D) : G) ∈ dcE D := by
    refine mem_dcE.2 ⟨(c : D).2, ?_, fun y hy => ?_⟩
    · have := congrArg (fun z : center D => ((z : D) : G)) hcc
      simpa using this
    · have := Subgroup.mem_center_iff.1 c.2 ⟨y, hy⟩
      exact (congrArg (fun z : D => (z : G)) this).symm
  intro hE
  rw [hE, Subgroup.mem_bot] at hx
  apply hc1
  apply Subtype.ext
  apply Subtype.ext
  exact hx

theorem card_eq_two_of_pPrimeCore_eq_bot {H : Type} [Group H] [Finite H]
    (hH : pPrimeCore 2 H = ⊥) {i : ℕ} (hi : ¬ 2 ∣ i) (hcard : Nat.card H = 2 * i) : i = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 H))
  have hi0 : i ≠ 0 := fun h => hi (h ▸ dvd_zero 2)
  have hfac : (2 * i).factorization 2 = 1 := by
    rw [Nat.factorization_mul (by norm_num) hi0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hi]
  have hQ : Nat.card Q = 2 := by
    rw [Sylow.card_eq_multiplicity, hcard, hfac, pow_one]
  have hcyc : IsCyclic Q := isCyclic_of_prime_card hQ
  have h := (CFSG.cyclic_sylow_normal_odd_complement Q hcyc).1
  rw [hH, Subgroup.card_bot, hcard, hQ] at h
  simpa using h.symm

theorem dClass_aux8 (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G) (td : TData (S : Subgroup G))
    {D : Subgroup G} (hDn : D.Normal) (hD2 : IsPGroup 2 D)
    (hDmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ D)
    (hDA : D ≤ td.A) (hD8 : Nat.card D = 8) {a : G} (haD : a ∈ D) (haA : a ∈ td.A)
    (haZ : a ∉ td.Z) : False := by
  set R : Subgroup G := Subgroup.centralizer (D : Set G) with hR
  have hRn : R.Normal := Subgroup.normal_centralizer
  have hDR : D ≤ R := fun d hd => Subgroup.mem_centralizer_iff.2 fun y hy =>
    td.A_abel y (hDA hy) d (hDA hd)
  have hAR : td.A ≤ R := fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
    td.A_abel y (hDA hy) x hx
  have hSR : (S : Subgroup G) ⊓ R = td.A := by
    refine le_antisymm (fun x hx => ?_) (le_inf td.A_le_S hAR)
    exact td.cent_A a haA haZ x hx.1 (Subgroup.mem_centralizer_iff.1 hx.2 a haD).symm
  have hD'c : D.subgroupOf R ≤ center R := by
    intro d hd
    rw [Subgroup.mem_center_iff]
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 x.2 d hd).symm
  have hD'n : (D.subgroupOf R).Normal := normal_of_le_center hD'c
  have hD'2 : IsPGroup 2 (D.subgroupOf R) := hD2.of_equiv (Subgroup.subgroupOfEquivOfLe hDR).symm
  have hQ := pPrimeCore_quot_central hO R (D.subgroupOf R) hD'c hD'2
  have hcardD' : Nat.card (D.subgroupOf R) = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDR).toEquiv).trans hD8
  have hRcard : Nat.card (R ⧸ D.subgroupOf R) * Nat.card (D.subgroupOf R) = Nat.card R :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup (D.subgroupOf R)).symm
  rw [hcardD'] at hRcard
  have hodd := sylow_inf_normal_relIndex_odd S R
  rw [hSR] at hodd
  have hAcard : Nat.card td.A = 16 := td.card_A
  have hrel := Subgroup.relIndex_mul_card (H := td.A) (K := R)
  rw [inf_eq_left.2 hAR, hAcard] at hrel
  have hi := card_eq_two_of_pPrimeCore_eq_bot hQ hodd
    (i := td.A.relIndex R) (by omega)
  have hRcard16 : Nat.card R = 16 := by omega
  have hAeq : td.A = R := Subgroup.eq_of_le_of_card_ge hAR (by omega)
  have hAn : td.A.Normal := hAeq ▸ hRn
  have hA2 : IsPGroup 2 td.A := IsPGroup.of_card (n := 4) (by rw [hAcard]; norm_num)
  have := Subgroup.card_le_of_le (hDmax td.A hAn hA2)
  omega

theorem Z_normal_of_E (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G) (td : TData (S : Subgroup G))
    {E : Subgroup G} (hEn : E.Normal) (hEsq : ∀ x ∈ E, x * x = 1) (hEne : E ≠ ⊥)
    (hEZ : E ≤ td.Z) : td.Z.Normal := by
  have hdvd : Nat.card E ∣ 4 := td.card_Z ▸ Subgroup.card_dvd_of_le hEZ
  have hne1 : Nat.card E ≠ 1 := fun h => hEne (Subgroup.card_eq_one.1 h)
  have h24 : Nat.card E = 2 ∨ Nat.card E = 4 := by
    have hle : Nat.card E ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card E := Nat.card_pos
    revert hdvd hne1 hle hpos
    generalize Nat.card E = n
    intro hdvd hne1 hle hpos
    interval_cases n <;> omega
  rcases h24 with h2 | h4
  · obtain ⟨⟨z, hzE⟩, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
    have hz1 : z ≠ 1 := fun h => hz (Subtype.ext h)
    obtain ⟨y, -, hyu⟩ := (Nat.card_eq_two_iff' (1 : E)).1 h2
    have hcent : ∀ g : G, g * z * g⁻¹ = z := by
      intro g
      have h1 : (⟨z, hzE⟩ : E) = y := hyu _ (fun h => hz1 (congrArg Subtype.val h))
      have h2 : (⟨g * z * g⁻¹, hEn.conj_mem z hzE g⟩ : E) = y := hyu _ (fun h => hz1 (by
        have h3 := congrArg Subtype.val h
        simpa using h3))
      exact congrArg Subtype.val (h2.trans h1.symm)
    have hzc : z ∈ center G :=
      Subgroup.mem_center_iff.2 fun g => (mul_inv_eq_iff_eq_mul.1 (hcent g))
    exact Z_normal_of_central_involution hO S td hzc hz1 (hEsq z hzE)
  · exact (Subgroup.eq_of_le_of_card_ge hEZ (by rw [h4, td.card_Z])) ▸ hEn

theorem dClass_aux (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G) (td : TData (S : Subgroup G))
    {D : Subgroup G} (hDn : D.Normal) (hD2 : IsPGroup 2 D) (hDS : D ≤ (S : Subgroup G))
    (hDmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ D)
    {E : Subgroup G} (hE : ∀ x ∈ E, x ∈ D ∧ x * x = 1 ∧ ∀ y ∈ D, x * y = y * x)
    (hEmax : ∀ x ∈ D, x * x = 1 → (∀ y ∈ D, x * y = y * x) → x ∈ E)
    (hZE : td.Z ≤ E) (hEZ : ¬ E ≤ td.Z) (hEA : E ≤ td.A) : D = td.A := by
  obtain ⟨a, haE, haZ⟩ := IsConcreteLE.not_le_iff_exists.1 hEZ
  have haA : a ∈ td.A := hEA haE
  have hDA : D ≤ td.A := fun d hd =>
    td.cent_A a haA haZ d (hDS hd) ((hE a haE).2.2 d hd).symm
  have hDE : D ≤ E := fun d hd =>
    hEmax d hd (td.A_sq d (hDA hd)) (fun y hy => td.A_abel d (hDA hd) y (hDA hy))
  have hDEeq : D = E := le_antisymm hDE fun x hx => (hE x hx).1
  have hZcard : Nat.card td.Z = 4 := td.card_Z
  have hAcard : Nat.card td.A = 16 := td.card_A
  have h4E : 4 ∣ Nat.card E := hZcard ▸ Subgroup.card_dvd_of_le hZE
  have hE16 : Nat.card E ∣ 16 := hAcard ▸ Subgroup.card_dvd_of_le hEA
  have hE4 : Nat.card E ≠ 4 := fun h =>
    hEZ (Subgroup.eq_of_le_of_card_ge hZE (by rw [h, hZcard])).ge
  have hE816 : Nat.card E = 8 ∨ Nat.card E = 16 := by
    have hle : Nat.card E ≤ 16 := Nat.le_of_dvd (by norm_num) hE16
    have hpos : 0 < Nat.card E := Nat.card_pos
    revert h4E hE16 hE4 hle hpos
    generalize Nat.card E = n
    intro h4E hE16 hE4 hle hpos
    interval_cases n <;> omega
  rcases hE816 with h8 | h16
  · exact (dClass_aux8 hO S td hDn hD2 hDmax hDA (by rw [hDEeq]; exact h8) (hE a haE).1 haA
      haZ).elim
  · rw [hDEeq]
    exact Subgroup.eq_of_le_of_card_ge hEA (by rw [h16, hAcard])

theorem dClass (hGor : Gor42) (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (td : TData (S : Subgroup G)) (hD : pCore 2 G ≠ ⊥) (hSn : ¬ (S : Subgroup G).Normal) :
    pCore 2 G = td.A ∨ pCore 2 G = td.B := by
  have hDn : (pCore 2 G).Normal := pCore_normal
  have hD2 : IsPGroup 2 (pCore 2 G) := pCore_isPGroup
  have hDS : pCore 2 G ≤ (S : Subgroup G) := hD2.le_sylow_of_normal S
  have hDmax : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N ≤ pCore 2 G :=
    fun N hN hN2 => le_sSup ⟨hN, hN2⟩
  have hEn : (dcE (pCore 2 G)).Normal := dcE_normal hDn
  have hEne : dcE (pCore 2 G) ≠ ⊥ := dcE_ne_bot hD2 hD
  have hEsq : ∀ x ∈ dcE (pCore 2 G), x * x = 1 := fun x hx => (mem_dcE.1 hx).2.1
  by_cases hEZ : dcE (pCore 2 G) ≤ td.Z
  · exact (hSn (kl hGor hO S td (Z_normal_of_E hO S td hEn hEsq hEne hEZ))).elim
  · have hES : dcE (pCore 2 G) ≤ (S : Subgroup G) := fun x hx => hDS (mem_dcE.1 hx).1
    have hZE : td.Z ≤ dcE (pCore 2 G) :=
      (td.normal_dich _ hES fun s _ n hn => hEn.conj_mem n hn s).resolve_left hEZ
    have hEcomm : ∀ x ∈ dcE (pCore 2 G), ∀ y ∈ dcE (pCore 2 G), x * y = y * x :=
      fun x hx y hy => (mem_dcE.1 hx).2.2 y (mem_dcE.1 hy).1
    rcases td.elemAb_le _ hES hEsq hEcomm with hA | hB
    · exact Or.inl (dClass_aux hO S td hDn hD2 hDS hDmax (fun x hx => mem_dcE.1 hx)
        (fun x hx h1 h2 => mem_dcE.2 ⟨hx, h1, h2⟩) hZE hEZ hA)
    · exact Or.inr (dClass_aux hO S td.swap hDn hD2 hDS hDmax (fun x hx => mem_dcE.1 hx)
        (fun x hx h1 h2 => mem_dcE.2 ⟨hx, h1, h2⟩) hZE hEZ hB)

end CFSG.OddStandard.ThmC.O2
