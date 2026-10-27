module

public import CFSG.GroupTheory.UniqueElemSylow
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.Quasithin.Background.A1cRank
import CFSG.HardMathSupport.Solomon.Coordinator.C25Group

public section

namespace CFSG.GroupTheory.ExtraspecialThreeFive

open scoped commutatorElement

variable {R : Type*} [Group R] [Finite R]

theorem commutator_eq_center (hcard : Nat.card R = 3 ^ 5)
    (hZ : Nat.card (Subgroup.center R) = 3)
    (hcomm : commutator R ≤ Subgroup.center R) :
    commutator R = Subgroup.center R := by
  have hne : commutator R ≠ ⊥ := by
    intro hbot
    have hab : IsMulCommutative R := (commutator_eq_bot_iff (G := R)).mp hbot
    have htop : Subgroup.center R = ⊤ := Subgroup.center_eq_top_iff.mpr hab
    rw [htop, Subgroup.card_top, hcard] at hZ
    norm_num at hZ
  have hdvd : Nat.card (commutator R) ∣ 3 := by
    rw [← hZ]
    exact Subgroup.card_dvd_of_le hcomm
  have hne1 : Nat.card (commutator R) ≠ 1 := by
    intro h1
    exact hne (Subgroup.eq_bot_of_card_eq _ h1)
  have hc3 : Nat.card (commutator R) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hcomm (by rw [hc3, hZ])

theorem center_le_of_index_le_three (hcard : Nat.card R = 3 ^ 5)
    (hZ : Nat.card (Subgroup.center R) = 3)
    (hcomm : commutator R ≤ Subgroup.center R) {H : Subgroup R} (hH : H.index ≤ 3) :
    Subgroup.center R ≤ H := by
  have hmin : (Nat.card R).minFac = 3 := by
    rw [hcard]
    norm_num
  have hidx_dvd : H.index ∣ 3 ^ 5 := by
    rw [← hcard]
    exact Subgroup.index_dvd_card H
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hidx_dvd
  have hi_le : i ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ i := by omega
    have h3 : 3 ^ 2 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) h2
    have hle : 3 ^ i ≤ 3 := by
      rw [← hi]
      exact hH
    norm_num at h3
    omega
  have hidx : H.index = 1 ∨ H.index = 3 := by
    interval_cases i
    · left
      rw [hi]
      norm_num
    · right
      rw [hi]
      norm_num
  rcases hidx with hidx | hidx
  · have htop : H = ⊤ := Subgroup.index_eq_one.mp hidx
    rw [htop]
    exact le_top
  · have hHn : H.Normal :=
      Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hmin])
    haveI := hHn
    have hqcard : Nat.card (R ⧸ H) = 3 := by
      rw [← Subgroup.index_eq_card, hidx]
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hcommq : IsMulCommutative (R ⧸ H) :=
      (isCyclic_of_prime_card (p := 3) hqcard).isMulCommutative
    have hR'le : commutator R ≤ H :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommq
    rw [← commutator_eq_center hcard hZ hcomm]
    exact hR'le

private theorem card_inf_centralizer_ge_27 (hcard : Nat.card R = 3 ^ 5)
    (hZ : Nat.card (Subgroup.center R) = 3)
    (hcomm : commutator R ≤ Subgroup.center R) {H : Subgroup R} (hH : H.index ≤ 3) (a : R) :
    27 ≤ Nat.card (H ⊓ Subgroup.centralizer ({a} : Set R) : Subgroup R) := by
  have hcommPt : ∀ x y : R, ⁅x, y⁆ ∈ Subgroup.center R := fun x y =>
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  have hCindex : (Subgroup.centralizer ({a} : Set R)).index ≤ 3 :=
    CFSG.HardMathSupport.Solomon.Coordinator.c25_index_centralizer_le hZ hcommPt a
  have hidx : (H ⊓ Subgroup.centralizer ({a} : Set R) : Subgroup R).index ≤ 9 := by
    calc (H ⊓ Subgroup.centralizer ({a} : Set R) : Subgroup R).index
        ≤ H.index * (Subgroup.centralizer ({a} : Set R)).index := Subgroup.index_inf_le
      _ ≤ 3 * 3 := Nat.mul_le_mul hH hCindex
      _ = 9 := by norm_num
  have hmul := Subgroup.card_mul_index
    (H ⊓ Subgroup.centralizer ({a} : Set R) : Subgroup R)
  have hRcard : Nat.card R = 243 := by
    rw [hcard]
    norm_num
  have h243 : 243 ≤
      Nat.card (H ⊓ Subgroup.centralizer ({a} : Set R) : Subgroup R) * 9 := by
    calc 243 = Nat.card R := hRcard.symm
      _ = Nat.card (H ⊓ Subgroup.centralizer ({a} : Set R) : Subgroup R) *
            (H ⊓ Subgroup.centralizer ({a} : Set R) : Subgroup R).index := hmul.symm
      _ ≤ Nat.card (H ⊓ Subgroup.centralizer ({a} : Set R) : Subgroup R) * 9 :=
            Nat.mul_le_mul_left _ hidx
  have hle : 27 * 9 ≤
      Nat.card (H ⊓ Subgroup.centralizer ({a} : Set R) : Subgroup R) * 9 := by
    rwa [show 27 * 9 = 243 by norm_num]
  exact Nat.le_of_mul_le_mul_right hle (by norm_num)

theorem exists_elemAbelian_27_of_index_le_three (hcard : Nat.card R = 3 ^ 5)
    (hexp : ∀ x : R, x ^ 3 = 1) (hZ : Nat.card (Subgroup.center R) = 3)
    (hcomm : commutator R ≤ Subgroup.center R) {H : Subgroup R} (hH : H.index ≤ 3) {a : R}
    (haH : a ∈ H) (haZ : a ∉ Subgroup.center R) :
    ∃ E : Subgroup R, E ≤ H ∧ a ∈ E ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZleH : Subgroup.center R ≤ H :=
    center_le_of_index_le_three hcard hZ hcomm hH
  have hinfcard := card_inf_centralizer_ge_27 hcard hZ hcomm hH a
  set Z9 : Subgroup R := Subgroup.center R ⊔ Subgroup.zpowers a with hZ9def
  have hZea : CFSG.Open.IsElemAbelian 3 (Subgroup.center R) :=
    ⟨Subgroup.center.isMulCommutative (G := R), fun x _ => hexp x⟩
  have ha1 : a ≠ 1 := by
    intro h
    apply haZ
    rw [h]
    exact (Subgroup.center R).one_mem
  have haord : orderOf a = 3 := orderOf_eq_prime (hexp a) ha1
  have hcommZa : ∀ e ∈ Subgroup.center R, Commute e a :=
    fun e he => (Subgroup.mem_center_iff.1 he a).symm
  obtain ⟨hZ9ea', hZ9card'⟩ :=
    CFSG.Quasithin.exists_elemAbelian_sup_zpowers (p := 3) hZea haord hcommZa haZ
  have hZ9ea : CFSG.Open.IsElemAbelian 3 Z9 := by
    rw [hZ9def]
    exact hZ9ea'
  have hZ9card : Nat.card Z9 = 9 := by
    rw [hZ9def, hZ9card', hZ]
  have hnotle : ¬ H ⊓ Subgroup.centralizer ({a} : Set R) ≤ Z9 := by
    intro hle
    have hcardle : Nat.card (H ⊓ Subgroup.centralizer ({a} : Set R) : Subgroup R) ≤
        Nat.card Z9 := Subgroup.card_le_of_le hle
    rw [hZ9card] at hcardle
    omega
  obtain ⟨b, hbHC, hbZ9⟩ := Set.not_subset.mp hnotle
  have hb1 : b ≠ 1 := by
    intro h
    apply hbZ9
    rw [h]
    exact Z9.one_mem
  have hbord : orderOf b = 3 := orderOf_eq_prime (hexp b) hb1
  have hbcomm : ∀ e ∈ Z9, Commute e b := by
    intro e he
    have hZ9cent : Z9 ≤ Subgroup.centralizer ({b} : Set R) := by
      rw [hZ9def]
      apply sup_le
      · intro z hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.1 hz b).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_singleton_iff.1 hbHC.2).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hZ9cent he)
  obtain ⟨hEea, hEcard'⟩ :=
    CFSG.Quasithin.exists_elemAbelian_sup_zpowers (p := 3) hZ9ea hbord hbcomm hbZ9
  refine ⟨Z9 ⊔ Subgroup.zpowers b, ?_, ?_, hEea, ?_⟩
  · rw [hZ9def]
    exact sup_le (sup_le hZleH (Subgroup.zpowers_le.mpr haH)) (Subgroup.zpowers_le.mpr hbHC.1)
  · exact Subgroup.mem_sup_left (by
      rw [hZ9def]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
  · rw [hEcard', hZ9card]

theorem exists_two_elemAbelian_27 (hcard : Nat.card R = 3 ^ 5)
    (hexp : ∀ x : R, x ^ 3 = 1) (hZ : Nat.card (Subgroup.center R) = 3)
    (hcomm : commutator R ≤ Subgroup.center R) :
    ∃ E₁ E₂ : Subgroup R, E₁ ≠ E₂ ∧
      CFSG.Open.IsElemAbelian 3 E₁ ∧ Nat.card E₁ = 27 ∧
      CFSG.Open.IsElemAbelian 3 E₂ ∧ Nat.card E₂ = 27 := by
  classical
  have hZne : Subgroup.center R ≠ ⊥ := by
    intro hbot
    rw [hbot] at hZ
    simpa using hZ
  have hcommNe : commutator R ≠ ⊥ := by
    intro hbot
    apply hZne
    rw [← commutator_eq_center hcard hZ hcomm, hbot]
  have hnotcomm : ¬ IsMulCommutative R := by
    intro hR
    exact hcommNe (commutator_eq_bot (G := R))
  have hpairs : ∃ a b : R, a * b ≠ b * a := by
    by_contra h
    apply hnotcomm
    refine ⟨⟨fun a b => ?_⟩⟩
    by_contra hab
    exact h ⟨a, b, hab⟩
  obtain ⟨a, b, hab⟩ := hpairs
  have haZ : a ∉ Subgroup.center R := by
    intro ha
    apply hab
    exact (Subgroup.mem_center_iff.1 ha b).symm
  have hbZ : b ∉ Subgroup.center R := by
    intro hb
    apply hab
    exact Subgroup.mem_center_iff.1 hb a
  obtain ⟨E₁, -, haE₁, hE₁ea, hE₁card⟩ :=
    exists_elemAbelian_27_of_index_le_three hcard hexp hZ hcomm (H := ⊤) (by simp)
      (Subgroup.mem_top a) haZ
  obtain ⟨E₂, -, hbE₂, hE₂ea, hE₂card⟩ :=
    exists_elemAbelian_27_of_index_le_three hcard hexp hZ hcomm (H := ⊤) (by simp)
      (Subgroup.mem_top b) hbZ
  refine ⟨E₁, E₂, ?_, hE₁ea, hE₁card, hE₂ea, hE₂card⟩
  intro hEq
  apply hab
  rw [hEq] at haE₁
  exact (hE₂ea.comm hbE₂ haE₁).symm

variable {G : Type*} [Group G] [Finite G]

theorem exists_elemAbelian_27_le_inf {R N : Subgroup G}
    (hcard : Nat.card ↥R = 3 ^ 5) (hexp : ∀ x : ↥R, x ^ 3 = 1)
    (hZ : Nat.card (Subgroup.center ↥R) = 3)
    (hcomm : commutator ↥R ≤ Subgroup.center ↥R)
    (hle : Nat.card R ≤ 3 * Nat.card (R ⊓ N : Subgroup G)) :
    ∃ E : Subgroup G, E ≤ R ⊓ N ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  classical
  let K : Subgroup ↥R := (R ⊓ N).subgroupOf R
  have hKcard : Nat.card K = Nat.card (R ⊓ N : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hRcard : Nat.card R = 243 := by
    rw [show Nat.card R = Nat.card ↥R from rfl, hcard]
    norm_num
  have hKbig : 81 ≤ Nat.card K := by
    rw [hKcard]
    have h : 3 * 81 ≤ 3 * Nat.card (R ⊓ N : Subgroup G) := by
      rw [show 3 * 81 = 243 by norm_num, ← hRcard]
      exact hle
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have hKindex : K.index ≤ 3 := by
    have hmul := Subgroup.card_mul_index K
    have hcard' : Nat.card K * K.index = Nat.card R := hmul
    have h : Nat.card K * K.index ≤ Nat.card K * 3 := by
      calc Nat.card K * K.index = Nat.card R := hcard'
        _ ≤ 3 * Nat.card (R ⊓ N : Subgroup G) := hle
        _ = Nat.card K * 3 := by rw [hKcard]; ring
    exact Nat.le_of_mul_le_mul_left h (by positivity)
  have hnotle : ¬ K ≤ Subgroup.center ↥R := by
    intro hleZ
    have hcardle : Nat.card K ≤ Nat.card (Subgroup.center ↥R) :=
      Subgroup.card_le_of_le hleZ
    rw [hZ] at hcardle
    omega
  obtain ⟨a, haK, haZ⟩ := Set.not_subset.mp hnotle
  obtain ⟨E, hEK, haE, hEea, hEcard⟩ :=
    exists_elemAbelian_27_of_index_le_three (R := ↥R) hcard hexp hZ hcomm
      (H := K) hKindex haK haZ
  refine ⟨E.map R.subtype, ?_, hEea.map R.subtype, ?_⟩
  · calc E.map R.subtype ≤ K.map R.subtype := Subgroup.map_mono hEK
      _ = R ⊓ N := Subgroup.map_subgroupOf_eq_of_le inf_le_left
  · rw [Subgroup.card_subtype, hEcard]

theorem false_of_uniqueElemSylow (h : CFSG.GroupTheory.UniqueElemSylow 3 3 G) {R : Subgroup G}
    (hcard : Nat.card ↥R = 3 ^ 5) (hexp : ∀ x : ↥R, x ^ 3 = 1)
    (hZ : Nat.card (Subgroup.center ↥R) = 3)
    (hcomm : commutator ↥R ≤ Subgroup.center ↥R) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₁, E₂, hne, hE₁ea, hE₁card, hE₂ea, hE₂card⟩ :=
    exists_two_elemAbelian_27 hcard hexp hZ hcomm
  have hR3 : IsPGroup 3 ↥R := IsPGroup.of_card (p := 3) (n := 5) hcard
  obtain ⟨P, hRP⟩ := hR3.exists_le_sylow
  let A₁ : Subgroup G := E₁.map R.subtype
  let A₂ : Subgroup G := E₂.map R.subtype
  have hA₁ea : CFSG.Open.IsElemAbelian 3 A₁ := hE₁ea.map R.subtype
  have hA₂ea : CFSG.Open.IsElemAbelian 3 A₂ := hE₂ea.map R.subtype
  have hA₁card : Nat.card A₁ = 3 ^ 3 := by
    change Nat.card (E₁.map R.subtype) = 3 ^ 3
    rw [Subgroup.card_subtype, hE₁card]
    norm_num
  have hA₂card : Nat.card A₂ = 3 ^ 3 := by
    change Nat.card (E₂.map R.subtype) = 3 ^ 3
    rw [Subgroup.card_subtype, hE₂card]
    norm_num
  have hA₁P : A₁ ≤ P := (Subgroup.map_subtype_le E₁).trans hRP
  have hA₂P : A₂ ≤ P := (Subgroup.map_subtype_le E₂).trans hRP
  obtain ⟨A, -, huniqA⟩ := h P
  have hA₁eq : A₁ = A := huniqA A₁ ⟨hA₁P, hA₁ea, hA₁card⟩
  have hA₂eq : A₂ = A := huniqA A₂ ⟨hA₂P, hA₂ea, hA₂card⟩
  have hmap : E₁.map R.subtype = E₂.map R.subtype := by
    change A₁ = A₂
    rw [hA₁eq, hA₂eq]
  exact hne (Subgroup.map_injective (Subgroup.subtype_injective R) hmap)

theorem card_le_three_mul_card_inf_of_pow_three {B N C : Subgroup G}
    (hB : ∀ b ∈ B, b ^ 3 = 1) (hC : IsCyclic C)
    (hCN : C ≤ Subgroup.normalizer (N : Set G))
    (hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c) :
    Nat.card B ≤ 3 * Nat.card (B ⊓ N : Subgroup G) := by
  set P := Subgroup.normalizer (N : Set G)
  have hNP : N ≤ P := Subgroup.le_normalizer
  have hBP : B ≤ P := by
    intro b hb
    obtain ⟨n, hn, c, hc, rfl⟩ := hBNC b hb
    exact P.mul_mem (hNP hn) (hCN hc)
  have : (N.subgroupOf P).Normal := Subgroup.normal_in_normalizer
  set π := QuotientGroup.mk' (N.subgroupOf P)
  set ψ : B →* P ⧸ N.subgroupOf P := π.comp (Subgroup.inclusion hBP)
  set Cbar : Subgroup (P ⧸ N.subgroupOf P) := (C.subgroupOf P).map π
  have hCbar : IsCyclic Cbar := by
    have : IsCyclic (C.subgroupOf P) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hCN).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hCN).symm.surjective
    have h := isCyclic_of_surjective (π.comp (C.subgroupOf P).subtype).rangeRestrict
      (π.comp (C.subgroupOf P).subtype).rangeRestrict_surjective
    have e : (π.comp (C.subgroupOf P).subtype).range = Cbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [e] at h
    exact h
  have hrange : ψ.range ≤ Cbar := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨n, hn, c, hc, hbnc⟩ := hBNC b b.2
    refine ⟨⟨c, hCN hc⟩, Subgroup.mem_subgroupOf.mpr hc, ?_⟩
    change π ⟨c, hCN hc⟩ = π (Subgroup.inclusion hBP b)
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have : ((⟨c, hCN hc⟩ : P)⁻¹ * Subgroup.inclusion hBP b : P) = c⁻¹ * n * c := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, hbnc]
      group
    rw [this]
    have hcN : c⁻¹ ∈ P := P.inv_mem (hCN hc)
    have h := (Subgroup.mem_normalizer_iff.mp hcN n).mp hn
    rwa [inv_inv] at h
  have hcard3 : Nat.card ψ.range ≤ 3 := by
    have : IsCyclic (ψ.range.subgroupOf Cbar) := Subgroup.isCyclic _
    have e := Subgroup.subgroupOfEquivOfLe hrange
    have hcyc : IsCyclic ψ.range := isCyclic_of_surjective e.toMonoidHom e.surjective
    have hexp : Monoid.exponent ψ.range ∣ 3 := Monoid.exponent_dvd_of_forall_pow_eq_one
      fun y => by
        obtain ⟨b, hb⟩ := y.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, ← hb, ← map_pow, Subgroup.coe_one]
        have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa using hB b b.2)
        rw [hb3, map_one]
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) hexp
  have hker : Nat.card ψ.ker = Nat.card (B ⊓ N : Subgroup G) := by
    have hk : ψ.ker = N.subgroupOf B := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      change π (Subgroup.inclusion hBP b) = 1 ↔ _
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    rw [hk, inf_comm]
    exact ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).symm.trans
      (by rw [Subgroup.inf_subgroupOf_right])).symm
  have hfirst : Nat.card B = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hfirst, hker]
  exact Nat.mul_le_mul_right _ hcard3

end CFSG.GroupTheory.ExtraspecialThreeFive
