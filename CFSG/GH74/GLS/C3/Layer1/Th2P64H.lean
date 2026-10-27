module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GH74.GLS.C3.Layer1.Th2P61A7
public import CFSG.GH74.GLS.C3.Layer1.Th2P64Cop

public section

open Equiv Equiv.Perm Subgroup CFSG
open CFSG.GH74.GLS CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs CFSG.ABGLocalTools
open scoped commutatorElement

namespace CFSG.GH74.GLS.Th2.Obs

theorem card_center_of_card_eight {P : Type*} [Group P] [Finite P] (h8 : Nat.card P = 8) :
    Nat.card (center P) = 2 ∨ ∀ a b : P, a * b = b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [h8]; norm_num)
  have : Nontrivial P := by
    rw [← Finite.one_lt_card_iff_nontrivial, h8]; norm_num
  have hZ : Nontrivial (center P) := hp.center_nontrivial
  have hdvd : Nat.card (center P) ∣ 8 := h8 ▸ Subgroup.card_subgroup_dvd_card (center P)
  have hgt : 1 < Nat.card (center P) := Finite.one_lt_card
  have hn : Nat.card (center P) = 2 ∨ Nat.card (center P) = 4 ∨ Nat.card (center P) = 8 := by
    have hle : Nat.card (center P) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hc : Nat.card (center P) <;> simp_all
  rcases hn with h2 | h4 | h8'
  · exact Or.inl h2
  · right
    have hidx : (center P).index = 2 := by
      have := Subgroup.card_mul_index (center P)
      rw [h4, h8] at this
      omega
    have hq : Nat.card (P ⧸ center P) = 2 := by rw [← Subgroup.index, hidx]
    have : IsCyclic (P ⧸ center P) := isCyclic_of_prime_card hq
    have hcomm := (QuotientGroup.mk' (center P)).isMulCommutative_of_isCyclic_of_ker_le_center
      (by rw [QuotientGroup.ker_mk'])
    intro a b
    exact hcomm.is_comm.comm a b
  · right
    have : center P = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h8', h8])
    intro a b
    have hb : b ∈ center P := by rw [this]; trivial
    exact ((Subgroup.mem_center_iff.1 hb) a)

theorem card_center_eq_two_of_card_eight {P : Type*} [Group P] [Finite P] (h8 : Nat.card P = 8)
    {a b : P} (hab : a * b ≠ b * a) : Nat.card (center P) = 2 := by
  rcases card_center_of_card_eight h8 with h | h
  · exact h
  · exact absurd (h a b) hab

theorem commutator_mem_center_of_card_eight {P : Type*} [Group P] [Finite P]
    (h8 : Nat.card P = 8) (a b : P) : ⁅a, b⁆ ∈ center P := by
  classical
  rcases card_center_of_card_eight h8 with h | h
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hidx : (center P).index = 4 := by
      have := Subgroup.card_mul_index (center P)
      rw [h, h8] at this
      omega
    have hq : Nat.card (P ⧸ center P) = 2 ^ 2 := by rw [← Subgroup.index, hidx]; norm_num
    have hcomm : IsMulCommutative (P ⧸ center P) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) hq
    have h1 : QuotientGroup.mk' (center P) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.is_comm.comm _ _
    exact (QuotientGroup.eq_one_iff _).1 h1
  · rw [commutatorElement_eq_one_iff_mul_comm.2 (h a b)]
    exact one_mem _


theorem swap_eq_of_mem_rootFour_sup {F : Subgroup (Perm (Fin 7))} (hF : IsRootFour F)
    {t : Perm (Fin 7)} (ht : t.IsSwap) (hdis : ∀ i, (∃ f ∈ F, f i ≠ i) → t i = i)
    {g : Perm (Fin 7)} (hg : g ∈ F ⊔ Subgroup.zpowers t) (hgs : g.IsSwap) : g = t := by
  classical
  obtain ⟨-, hcard, hF2, S, hS, hsupp⟩ := hF
  have ht1 : t ≠ 1 := ht.isCycle.ne_one
  have ht2 : orderOf t = 2 := by
    obtain ⟨a, b, hab, rfl⟩ := ht
    exact orderOf_eq_prime (by rw [sq]; exact Equiv.swap_mul_self a b) ht1
  have htcard : t.support.card = 2 := Equiv.Perm.card_support_eq_two.2 ht
  have hdisj : ∀ f ∈ F, f.Disjoint t := fun f hf i => by
    by_cases h : f i = i
    · exact Or.inl h
    · exact Or.inr (hdis i ⟨f, hf, h⟩)
  have hcomm : ∀ f ∈ F, ∀ q ∈ Subgroup.zpowers t, f * q = q * f := by
    intro f hf q hq
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    exact (Commute.zpow_right ((hdisj f hf).commute) m).eq
  obtain ⟨f, hf, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hg
  have hgcard : (f * q).support.card = 2 := Equiv.Perm.card_support_eq_two.2 hgs
  rcases mem_zpowers_two ht2 hq with rfl | rfl
  · exfalso
    rw [mul_one] at hgcard
    by_cases hf1 : f = 1
    · rw [hf1] at hgcard; simp at hgcard
    · rw [hsupp f hf hf1, hS] at hgcard; omega
  · by_cases hf1 : f = 1
    · rw [hf1, one_mul]
    · exfalso
      have h1 : (f * q).support = f.support ∪ q.support := (hdisj f hf).support_mul
      have h2 : Disjoint f.support q.support := Equiv.Perm.disjoint_iff_disjoint_support.1 (hdisj f hf)
      rw [h1, Finset.card_union_of_disjoint h2, hsupp f hf hf1, hS, htcard] at hgcard
      omega

theorem forall_comm_swap_of_card {F : Subgroup (Perm (Fin 7))} (hF : IsRootFour F) {t : Perm (Fin 7)}
    (ht : t.IsSwap) (hdis : ∀ i, (∃ f ∈ F, f i ≠ i) → t i = i) {Y : Subgroup (Perm (Fin 7))}
    (hM : F ⊔ Subgroup.zpowers t ≤ Y) (hcard : Nat.card Y = 2 * Nat.card ↥(F ⊔ Subgroup.zpowers t)) :
    ∀ y ∈ Y, y * t = t * y := by
  classical
  set M : Subgroup (Perm (Fin 7)) := F ⊔ Subgroup.zpowers t with hMdef
  have hidx : (M.subgroupOf Y).index = 2 := by
    have h1 := Subgroup.card_mul_index (M.subgroupOf Y)
    have h2 : Nat.card ↥(M.subgroupOf Y) = Nat.card ↥M :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv
    rw [h2, hcard] at h1
    have hpos : 0 < Nat.card ↥M := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1]; ring)
  have hnorm : (M.subgroupOf Y).Normal := Subgroup.normal_of_index_eq_two hidx
  intro y hy
  have htM : t ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have h1 : (⟨y, hy⟩ : ↥Y) * ⟨t, hM htM⟩ * (⟨y, hy⟩ : ↥Y)⁻¹ ∈ M.subgroupOf Y :=
    hnorm.conj_mem ⟨t, hM htM⟩ (Subgroup.mem_subgroupOf.2 htM) ⟨y, hy⟩
  have h2 : y * t * y⁻¹ ∈ M := h1
  have h3 : (y * t * y⁻¹).IsSwap := by
    obtain ⟨a, b, hab, rfl⟩ := ht
    refine ⟨y a, y b, fun h => hab (y.injective h), ?_⟩
    rw [Equiv.swap_apply_apply]
  have h4 : y * t * y⁻¹ = t := swap_eq_of_mem_rootFour_sup hF ht hdis h2 h3
  calc y * t = y * t * y⁻¹ * y := by group
    _ = t * y := by rw [h4]


section Lift

variable {G : Type} [Group G] [Finite G]

theorem exists_J_lift {J : Subgroup G} (e : kBar J ≃* alternatingGroup (Fin 7)) {x : G}
    (hxN : x ∈ normalizer (J : Set G)) (hx2 : x * x = 1) (hx1 : x ≠ 1) {y₀ : Perm (Fin 7)}
    (hy₀A : y₀ ∈ alternatingGroup (Fin 7))
    (hy₀s : y₀ * a7Act J e ⟨x, hxN⟩ = a7Act J e ⟨x, hxN⟩ * y₀) :
    ∃ (y' : G) (hy'J : y' ∈ J), x * y' = y' * x ∧
      a7Act J e ⟨y', Subgroup.le_normalizer hy'J⟩ = y₀ := by
  obtain ⟨kb, hkb⟩ := e.surjective ⟨y₀, hy₀A⟩
  induction kb using QuotientGroup.induction_on with | H j => ?_
  have hjJ : (j : G) ∈ J := j.2
  have hJj : a7Act J e ⟨(j : G), Subgroup.le_normalizer hjJ⟩ = y₀ :=
    (a7Act_of_mem e hjJ).trans (congrArg Subtype.val hkb)
  have hcJ : x⁻¹ * ((j : G) * x * (j : G)⁻¹) ∈ J := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hxN) (j : G)).1 hjJ
    have : x⁻¹ * ((j : G) * x * (j : G)⁻¹) = (x⁻¹ * (j : G) * x⁻¹⁻¹) * (j : G)⁻¹ := by group
    rw [this]
    exact J.mul_mem h1 (J.inv_mem hjJ)
  have hcact : a7Act J e ⟨x⁻¹ * ((j : G) * x * (j : G)⁻¹), Subgroup.le_normalizer hcJ⟩ = 1 := by
    have : (⟨x⁻¹ * ((j : G) * x * (j : G)⁻¹), Subgroup.le_normalizer hcJ⟩ :
        ↥(normalizer (J : Set G))) =
        (⟨x, hxN⟩ : ↥(normalizer (J : Set G)))⁻¹ *
          (⟨(j : G), Subgroup.le_normalizer hjJ⟩ * ⟨x, hxN⟩ *
            ⟨(j : G), Subgroup.le_normalizer hjJ⟩⁻¹) := rfl
    rw [this, map_mul, map_inv, map_mul, map_mul, map_inv, hJj]
    set s := a7Act J e ⟨x, hxN⟩ with hs
    have h2 : y₀ * s * y₀⁻¹ = s := by
      calc y₀ * s * y₀⁻¹ = (s * y₀) * y₀⁻¹ := by rw [hy₀s]
        _ = s := by group
    rw [h2]; group
  have hcO : x⁻¹ * ((j : G) * x * (j : G)⁻¹) ∈ pPrimeCoreOf 2 J := by
    rw [a7Act_of_mem e hcJ] at hcact
    have h1 : e (QuotientGroup.mk (⟨x⁻¹ * ((j : G) * x * (j : G)⁻¹), hcJ⟩ : ↥J)) = 1 :=
      Subtype.ext hcact
    have h2 : QuotientGroup.mk (⟨x⁻¹ * ((j : G) * x * (j : G)⁻¹), hcJ⟩ : ↥J) = (1 : kBar J) :=
      e.injective (by rw [h1, map_one])
    exact ⟨_, (QuotientGroup.eq_one_iff _).1 h2, rfl⟩
  obtain ⟨y', hy'J, hy'x, hy'O⟩ := exists_centralizer_lift hxN hx2 hx1 hjJ hcO
  have hmk : (QuotientGroup.mk (⟨y', hy'J⟩ : ↥J) : kBar J) = QuotientGroup.mk j := by
    rw [QuotientGroup.eq]
    obtain ⟨o, ho, hoeq⟩ := hy'O
    have hO2 : y'⁻¹ * ((j : G) * y'⁻¹) * y' ∈ pPrimeCoreOf 2 J := by
      have := TwoThin.mem_normalizer_pPrimeCoreOf (Subgroup.le_normalizer (J.inv_mem hy'J))
      have h5 := (Subgroup.mem_normalizer_iff.1 this ((j : G) * y'⁻¹)).1 ⟨o, ho, hoeq⟩
      simpa using h5
    obtain ⟨o2, ho2, hoeq2⟩ := hO2
    have : (⟨y', hy'J⟩ : ↥J)⁻¹ * j = o2 := by
      apply Subtype.ext
      have : ((⟨y', hy'J⟩ : ↥J)⁻¹ * j : ↥J).1 = y'⁻¹ * (j : G) := rfl
      rw [this]
      have h6 : (o2 : G) = y'⁻¹ * ((j : G) * y'⁻¹) * y' := hoeq2
      rw [h6]; group
    rw [this]; exact ho2
  refine ⟨y', hy'J, hy'x, ?_⟩
  rw [a7Act_of_mem e hy'J, hmk, ← a7Act_of_mem e hjJ]
  exact hJj

end Lift


section Solv

theorem alternatingGroup_le_derivedSeries (n : ℕ) :
    alternatingGroup (Fin 5) ≤ derivedSeries (Perm (Fin 5)) n := by
  induction n with
  | zero => simp [derivedSeries_zero]
  | succ n ih =>
    rw [derivedSeries_succ]
    calc alternatingGroup (Fin 5) = ⁅alternatingGroup (Fin 5), alternatingGroup (Fin 5)⁆ :=
          (commutator_alternatingGroup_eq_self (by simp)).symm
      _ ≤ ⁅derivedSeries (Perm (Fin 5)) n, derivedSeries (Perm (Fin 5)) n⁆ :=
          Subgroup.commutator_mono ih ih

theorem exists_mem_ker_of_solvable_range {S H₀ : Type*} [Group S] [Group H₀]
    (φ : S →* Perm (Fin 5)) (hφ : Function.Surjective φ) (ρ : S →* H₀)
    (hs : Group.IsSolvable ρ.range) {v : Perm (Fin 5)} (hv : v ∈ alternatingGroup (Fin 5)) :
    ∃ s ∈ ρ.ker, φ s = v := by
  obtain ⟨n, hn⟩ := hs.solvable
  have h1 : derivedSeries S n ≤ ρ.ker := by
    intro s hs'
    have h0 : ρ.rangeRestrict s ∈ derivedSeries ρ.range n := by
      have := map_derivedSeries_le_derivedSeries ρ.rangeRestrict n
      exact this ⟨s, hs', rfl⟩
    rw [hn, Subgroup.mem_bot] at h0
    have h2 : ρ s = 1 := by
      have := congrArg Subtype.val h0
      simpa using this
    exact h2
  have h2 : alternatingGroup (Fin 5) ≤ derivedSeries (Perm (Fin 5)) n :=
    alternatingGroup_le_derivedSeries n
  rw [← map_derivedSeries_eq hφ n] at h2
  obtain ⟨s, hs', hsv⟩ := h2 hv
  exact ⟨s, h1 hs', hsv⟩

end Solv

section Klein

theorem exists_exp_two_lift {X Y : Type*} [Group X] [Finite X] [Group Y] (φ : X →* Y)
    (hker : Odd (Nat.card φ.ker)) {A : Subgroup Y} (hA : A ≤ φ.range)
    (hsq : ∀ a ∈ A, a * a = 1) (h4 : 4 ∣ Nat.card A) :
    ∃ E : Subgroup X, (∀ e ∈ E, e * e = 1) ∧ 4 ∣ Nat.card E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X₄ : Subgroup X := A.comap φ with hX₄
  have hdvd : Nat.card A ∣ Nat.card X₄ := by
    let φ₄ : ↥X₄ →* ↥A := φ.subgroupComap A
    have hs : Function.Surjective φ₄ := by
      intro a
      obtain ⟨x, hx⟩ := hA a.2
      exact ⟨⟨x, by rw [hX₄, Subgroup.mem_comap, hx]; exact a.2⟩, Subtype.ext hx⟩
    exact Subgroup.card_dvd_of_surjective hs
  obtain ⟨E, hE⟩ := exists_isSylowOf 2 X₄
  have hEle : E ≤ X₄ := hE.le
  have hEp : IsPGroup 2 E := hE.isPGroup
  have hEcard := hE.card_eq
  refine ⟨E, fun e he => ?_, ?_⟩
  · have hee : e * e ∈ E := E.mul_mem he he
    have h1 : φ (e * e) = 1 := by
      rw [map_mul]; exact hsq _ (hEle he)
    have h2 : orderOf (e * e) ∣ Nat.card φ.ker :=
      Subgroup.orderOf_dvd_natCard φ.ker (MonoidHom.mem_ker.2 h1)
    obtain ⟨k, hk2⟩ := hEp ⟨e * e, hee⟩
    have h3 : orderOf (e * e) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hk2
      simpa using this
    obtain ⟨j, hj, hj2⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h3
    have hodd : Odd (orderOf (e * e)) := Odd.of_dvd_nat hker h2
    have hj0 : j = 0 := by
      by_contra hne
      rw [hj2] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow).2 ⟨even_two, hne⟩)
    rw [hj0, pow_zero] at hj2
    exact orderOf_eq_one_iff.1 hj2
  · rw [hEcard]
    have h4' : 2 ^ 2 ∣ Nat.card X₄ := (by norm_num : 2 ^ 2 ∣ 4).trans (h4.trans hdvd)
    have hv : 2 ≤ (Nat.card X₄).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 h4'
    exact (by norm_num : 4 = 2 ^ 2) ▸ pow_dvd_pow 2 hv

end Klein

theorem klein_exp_alt5 : ∀ g : Perm (Fin 5), Equiv.Perm.sign g = 1 → g ^ 4 = 1 → g * g = 1 := by
  decide +kernel

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem exists_klein_alt5 : ∃ A : Subgroup (Perm (Fin 5)), A ≤ alternatingGroup (Fin 5) ∧
    (∀ a ∈ A, a * a = 1) ∧ 4 ∣ Nat.card A := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 (alternatingGroup (Fin 5))))
  have hQ : Nat.card Q = 4 := by
    rw [Sylow.card_eq_multiplicity, card_alt5]
    norm_num [Nat.factorization]
  set A : Subgroup (Perm (Fin 5)) := (Q : Subgroup (alternatingGroup (Fin 5))).map
    (alternatingGroup (Fin 5)).subtype with hA
  have hAcard : Nat.card A = 4 := by
    rw [hA, Subgroup.card_map_of_injective (alternatingGroup (Fin 5)).subtype_injective]
    exact hQ
  have hAle : A ≤ alternatingGroup (Fin 5) := Subgroup.map_subtype_le _
  refine ⟨A, hAle, fun a ha => ?_, by rw [hAcard]⟩
  have h4 : a ^ 4 = 1 := by
    have hd : orderOf a ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A ha
    rw [hAcard] at hd
    exact orderOf_dvd_iff_pow_eq_one.1 hd
  exact klein_exp_alt5 a (Equiv.Perm.mem_alternatingGroup.1 (hAle ha)) h4

end CFSG.GH74.GLS.Th2.Obs
