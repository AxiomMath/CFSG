module

public import CFSG.GH74.GLS.C3.Layer1.EvenSelLeaves
public import CFSG.GH74.GLS.C3.Layer1.BkIvk73PU4

public section

namespace CFSG.GH74.GLS

namespace EvenFive

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS.C3.Layer1
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]

theorem card_eq_sixty {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 5)) : Nat.card K = 60 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  norm_num [Nat.factorial]

omit [Finite G] in
theorem sq_eq_one_of_le {K P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 2 ↥P)
    (e : ↥K ≃* alternatingGroup (Fin 5)) : ∀ p ∈ P, p * p = 1 := by
  intro p hp
  obtain ⟨m, hm⟩ := hP ⟨p, hp⟩
  have hpm : p ^ 2 ^ m = 1 := congrArg Subtype.val hm
  have h1 : (e ⟨p, hPK hp⟩) ^ 2 ^ m = 1 := by
    rw [← map_pow, show (⟨p, hPK hp⟩ : ↥K) ^ 2 ^ m = 1 from Subtype.ext hpm, map_one]
  have h2 := Bk.PU4.a5_sq_eq_one_of_two_power h1
  have h3 : (⟨p, hPK hp⟩ : ↥K) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, h2, map_one]
  have := congrArg Subtype.val h3
  simpa [pow_two] using this

theorem card_le_four_of_le {K P : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 2 ↥P)
    (hK : Nat.card ↥K = 60) : Nat.card ↥P ≤ 4 := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hd : 2 ^ k ∣ 60 := hK ▸ hk ▸ Subgroup.card_dvd_of_le hPK
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h8 : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 (by omega)
    have := h8.trans hd
    omega
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 4 := by norm_num

omit [Finite G] in
theorem exists_mem_normalizer_not_mem {S T : Subgroup G} [Finite S] (hS : IsPGroup 2 ↥S) (hTS : T < S) :
    ∃ a ∈ S, a ∈ normalizer (T : Set G) ∧ a ∉ T := by
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  obtain ⟨s, hsS, hsT⟩ := IsConcreteLE.exists_of_lt hTS
  have hlt : T.subgroupOf S < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hsT ?_
    have : (⟨s, hsS⟩ : ↥S) ∈ T.subgroupOf S := h ▸ Subgroup.mem_top _
    exact this
  have hnc : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent
  have hlt' := hnc _ hlt
  obtain ⟨a, haN, haT⟩ := IsConcreteLE.exists_of_lt hlt'
  refine ⟨a, a.2, ?_, fun h => haT h⟩
  have hsub : a ∈ (normalizer (T : Set G)).subgroupOf S := by
    rw [Subgroup.subgroupOf_normalizer_eq hTS.le]
    exact haN
  exact Subgroup.mem_subgroupOf.mp hsub

theorem isSylowOf_top_of_isCentralInvolution {x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hx : IsCentralInvolution x) :
    IsSylowOf 2 T ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, S', -, hS'c⟩ := hx
  have hS'C : (S' : Subgroup G) ≤ centralizer ({x} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.2 (hS'c s hs)
  have h1 : Nat.card ↥(S' : Subgroup G) = 2 ^ (Nat.card G).factorization 2 :=
    Sylow.card_eq_multiplicity S'
  have h2 : Nat.card ↥T = 2 ^ (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 :=
    hT.card_eq
  have hdvd : Nat.card ↥(S' : Subgroup G) ∣ Nat.card ↥(centralizer ({x} : Set G)) :=
    Subgroup.card_dvd_of_le hS'C
  have h3 : (Nat.card G).factorization 2 ≤ (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 (h1 ▸ hdvd)
  have h4 : (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 ≤ (Nat.card G).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1
      ((Nat.ordProj_dvd _ 2).trans (Subgroup.card_subgroup_dvd_card _))
  refine isSylowOf_of_card le_top ?_
  rw [Subgroup.card_top, h2, le_antisymm h4 h3]

omit [Finite G] in
theorem exists_elementaryAbelian_four_le {H : Type} [Group H] [Finite H] (hrank : 2 ≤ CFSG.pRank 2 H) :
    ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ 4 ≤ Nat.card A := by
  set S := {r : ℕ | ∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ r} with hS
  have hpos : 0 < sSup S := by
    change 0 < CFSG.pRank 2 H
    omega
  have hne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.1 h, csSup_empty] at hpos
    exact absurd hpos (lt_irrefl 0)
  have hbdd : BddAbove S := by
    by_contra h
    rw [Nat.sSup_of_not_bddAbove h] at hpos
    exact absurd hpos (lt_irrefl 0)
  obtain ⟨A, hA, hcard⟩ := Nat.sSup_mem hne hbdd
  refine ⟨A, hA, ?_⟩
  rw [hcard]
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ sSup S := Nat.pow_le_pow_right (by norm_num) (by change 2 ≤ CFSG.pRank 2 H; exact hrank)

theorem pf_eq_five {K : Type} [Group K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hL : LieModel K .PSL 2 p f) (hcard : Nat.card K = 60) : p ^ f = 5 := by
  have hodd : Odd (p ^ f) := Odd.pow (hp.odd_of_ne_two hp2)
  have h := card_of_lieModel_PSL (by norm_num : (2 : ℕ) ≠ 0) hL
  rw [hcard, show (2 : ℕ) - 1 = 1 from rfl] at h
  obtain ⟨k, hk⟩ := hodd
  rw [hk, C3.Layer1.PumpClass.ordA_one_odd] at h
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have : 2 * 3 * (3 + 1) * (2 * 3 + 1) ≤ 2 * k * (k + 1) * (2 * k + 1) := by gcongr <;> omega
    omega
  interval_cases k <;> omega

end Basic

end EvenFive

open Subgroup CFSG CFSG.ABGLocalTools Blueprint CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.EvenFive
open scoped commutatorElement

theorem b_even_five_of_PU4 (hPU4 : B_cor_PU4) : B_even_five := by
  intro G _ _ hG _ _ x K T Q hs _ ⟨e⟩ hTR hTS p f hp hp2 hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : HasL2Model ↥K Odd :=
    C3.Layer1.Back.hasL2Model_mono (fun q hq => C3.Layer1.Back.isFM9_odd hq) hs.isL2
  have hstd : IsStandardSubgroup K :=
    hPU4 G hG.kproper x K hs.terminal.1 hs.twoTerminal.1.2.2
      (two_le_pRank_of_hasL2Model_odd hodd) hs.terminal
  have hK60 : Nat.card ↥K = 60 := card_eq_sixty e
  have hpf : p ^ f = 5 := pf_eq_five hp hp2 hL hK60
  have hT2 : IsPGroup 2 ↥T := hs.sylowT.isPGroup
  have hTC : T ≤ centralizer ({x} : Set G) := hs.sylowT.le
  have hTN : T ≤ normalizer (K : Set G) := hs.sylowTM.le
  have hQ2 : IsPGroup 2 ↥Q := hs.sylowQ.isPGroup
  have hQC : Q ≤ centralizer (K : Set G) := hs.sylowQ.le
  have hQT : Q ≤ T := by rw [hs.hQ]; exact inf_le_left
  have hPK : T ⊓ K ≤ K := inf_le_right
  have hPT : T ⊓ K ≤ T := inf_le_left
  have hP2 : IsPGroup 2 ↥(T ⊓ K) := hT2.to_le hPT
  have hPcard : Nat.card ↥(T ⊓ K) ≤ 4 := card_le_four_of_le hPK hP2 hK60
  have hcomm : ∀ u ∈ T ⊓ K, ∀ q ∈ Q, u * q = q * u := fun u hu q hq =>
    Subgroup.mem_centralizer_iff.1 (hQC hq) u (hPK hu)
  have hTle : Nat.card ↥T ≤ Nat.card ↥(T ⊓ K) * Nat.card ↥Q := by
    have := Bk.card_sup_le_of_commute hcomm
    rwa [← hTR] at this
  obtain ⟨A, hA, hA4⟩ := exists_elementaryAbelian_four_le hs.rankQ
  have hQ4 : 4 ≤ Nat.card ↥Q := hA4.trans (Subgroup.card_le_card_group A)
  obtain ⟨S, hS, hTS'⟩ := Bk.exists_isSylowOf_ge_two hT2 (le_top : T ≤ ⊤)
  have hTlt : T < S := lt_of_le_of_ne hTS' fun h => hTS (h ▸ hS)
  obtain ⟨a, haS, haN, haT⟩ := exists_mem_normalizer_not_mem hS.isPGroup hTlt
  have haK : a ∉ normalizer (K : Set G) := by
    intro haK
    have hpa : IsPGroup 2 ↥(zpowers a) := hS.isPGroup.to_le (zpowers_le.2 haS)
    have hsup : IsPGroup 2 ↥(T ⊔ zpowers a) := hT2.to_sup_of_normal_left' hpa (zpowers_le.2 haN)
    have hle : T ⊔ zpowers a ≤ normalizer (K : Set G) := sup_le hTN (zpowers_le.2 haK)
    have heq := hs.sylowTM.eq_of_le le_sup_left hle hsup
    exact haT (heq ▸ mem_sup_right (mem_zpowers a))
  have hanot : a⁻¹ ∉ normalizer ((centralizer (K : Set G) : Subgroup G) : Set G) := by
    rw [hstd.2.2.2.1]
    intro h
    exact haK (by simpa using (normalizer (K : Set G)).inv_mem h)
  have hoddC := hstd.2.2.1 a⁻¹ hanot
  set Q₂ : Subgroup G := Q.map (MulAut.conj a).toMonoidHom with hQ₂
  have hQ₂C : Q₂ ≤ conjugate (centralizer (K : Set G)) a⁻¹ := by
    show Q₂ ≤ (centralizer (K : Set G)).map (MulAut.conj a⁻¹⁻¹).toMonoidHom
    rw [inv_inv]
    exact Subgroup.map_mono hQC
  have hbot : Q ⊓ Q₂ = ⊥ := by
    have hle : Q ⊓ Q₂ ≤ centralizer (K : Set G) ⊓ conjugate (centralizer (K : Set G)) a⁻¹ :=
      inf_le_inf hQC hQ₂C
    have hodd' : Odd (Nat.card ↥(Q ⊓ Q₂)) :=
      Odd.of_dvd_nat hoddC (Subgroup.card_dvd_of_le hle)
    obtain ⟨k, hk⟩ := (hQ2.to_le (inf_le_left : Q ⊓ Q₂ ≤ Q)).exists_card_eq
    have h1 : Nat.card ↥(Q ⊓ Q₂) = 1 := by
      rcases k with _ | k
      · simpa using hk
      · exfalso
        rw [hk, pow_succ] at hodd'
        exact (Nat.not_even_iff_odd.2 hodd') (even_two.mul_left _)
    exact Subgroup.card_eq_one.1 h1
  have hQ₂T : Q₂ ≤ T := by
    calc Q₂ ≤ T.map (MulAut.conj a).toMonoidHom := Subgroup.map_mono hQT
      _ = T := Bk.PU4.map_conj_eq_of_mem_normalizer haN
  have hcard₂ : Nat.card ↥Q₂ = Nat.card ↥Q :=
    Subgroup.card_map_of_injective (MulAut.conj a).injective
  have hinj : Function.Injective (fun u : ↥Q × ↥Q₂ =>
      (⟨(u.1 : G) * (u.2 : G), T.mul_mem (hQT u.1.2) (hQ₂T u.2.2)⟩ : ↥T)) := by
    rintro ⟨q₁, r₁⟩ ⟨q₂, r₂⟩ h
    have h1 : (q₁ : G) * r₁ = q₂ * r₂ := congrArg Subtype.val h
    have h2 : (q₂ : G)⁻¹ * q₁ = r₂ * (r₁ : G)⁻¹ := by
      calc (q₂ : G)⁻¹ * q₁ = (q₂ : G)⁻¹ * (q₁ * r₁) * (r₁ : G)⁻¹ := by group
        _ = (q₂ : G)⁻¹ * (q₂ * r₂) * (r₁ : G)⁻¹ := by rw [h1]
        _ = r₂ * (r₁ : G)⁻¹ := by group
    have hmem : (q₂ : G)⁻¹ * q₁ ∈ Q ⊓ Q₂ :=
      ⟨Q.mul_mem (Q.inv_mem q₂.2) q₁.2, by rw [h2]; exact Q₂.mul_mem r₂.2 (Q₂.inv_mem r₁.2)⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    have hq : q₁ = q₂ := Subtype.ext hmem.symm
    have hr : (r₁ : G) = r₂ := by
      have : (q₁ : G) * r₁ = q₁ * r₂ := by rw [h1, hmem]
      exact mul_left_cancel this
    rw [hq, Subtype.ext hr]
  have hQQ : Nat.card ↥Q * Nat.card ↥Q ≤ Nat.card ↥T := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod, hcard₂] at this
  have hQP : Nat.card ↥Q ≤ Nat.card ↥(T ⊓ K) :=
    Nat.le_of_mul_le_mul_right (hQQ.trans hTle) (by omega)
  have hQcard : Nat.card ↥Q = 4 := le_antisymm (hQP.trans hPcard) hQ4
  have hPcard4 : Nat.card ↥(T ⊓ K) = 4 := le_antisymm hPcard (hQcard ▸ hQP)
  have hTcard : Nat.card ↥T = 2 ^ 4 := by
    have h1 : Nat.card ↥T ≤ 16 := by
      calc Nat.card ↥T ≤ Nat.card ↥(T ⊓ K) * Nat.card ↥Q := hTle
        _ = 16 := by rw [hPcard4, hQcard]
    have h2 : 16 ≤ Nat.card ↥T := by
      calc 16 = Nat.card ↥Q * Nat.card ↥Q := by rw [hQcard]
        _ ≤ Nat.card ↥T := hQQ
    norm_num
    omega
  have hQel : IsElementaryAbelian 2 ↥Q := by
    have := hA
    have hA' : IsElementaryAbelian 2 ↥(A.map Q.subtype) := IsElementaryAbelian.map_subtype
    have hcardA' : 4 ≤ Nat.card ↥(A.map Q.subtype) := by
      rw [Subgroup.card_map_of_injective Q.subtype_injective]
      exact hA4
    have heq : A.map Q.subtype = Q :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.map_subtype_le A) (by rw [hQcard]; exact hcardA')
    rw [← heq]
    exact hA'
  have hPsq := sq_eq_one_of_le hPK hP2 e
  have hPcomm : ∀ u ∈ T ⊓ K, ∀ v ∈ T ⊓ K, u * v = v * u := by
    intro u hu v hv
    have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hPsq u hu)
    have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hPsq v hv)
    have hwi : (u * v)⁻¹ = u * v :=
      inv_eq_of_mul_eq_one_right (hPsq (u * v) ((T ⊓ K).mul_mem hu hv))
    rw [mul_inv_rev, hui, hvi] at hwi
    exact hwi.symm
  have hPel : IsElementaryAbelian 2 ↥(T ⊓ K) :=
    C3.Layer1.Back.isElementaryAbelian_of_forall hPcomm hPsq
  have hTel : IsElementaryAbelian 2 ↥T := by
    have := Bk.isElementaryAbelian_sup_of_commute hPel hQel hcomm
    rwa [← hTR] at this
  refine ⟨?_, fun hc => hTS (isSylowOf_top_of_isCentralInvolution hs.sylowT hc), Or.inl ⟨hpf, ?_⟩⟩
  ·
    have hE : IsElementaryAbelian 2 ↥(T.subgroupOf (centralizer ({x} : Set G))) :=
      IsElementaryAbelian.subgroupOf hTC
    have hcardE : Nat.card ↥(T.subgroupOf (centralizer ({x} : Set G))) = 2 ^ 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv, hTcard]
    exact CFSG.RankThree.Coprime.le_pRank_of_isElementaryAbelian one_lt_two hE hcardE
  ·
    obtain ⟨R, hR⟩ := hs.sylowTM.exists_sylow_eq_subgroupOf
    refine ⟨R, ?_, ?_⟩
    · rw [hR]
      exact IsElementaryAbelian.subgroupOf hTN
    · rw [hR, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, hTcard]

end CFSG.GH74.GLS
