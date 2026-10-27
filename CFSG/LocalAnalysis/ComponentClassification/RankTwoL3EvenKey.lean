module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenAction
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34Basic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3EvenAut

public noncomputable section

namespace CFSG.ComponentClassification.RankTwoL3Even

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial LinearFlag
  FieldFourCover
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open scoped commutatorElement

section Tight

variable {G : Type} [Group G]

theorem mem_normalizer_of_commute_of_mem [Finite G] {Q : Subgroup G} (hQ : TightlyEmbedded Q)
    {x : G} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (hx2 : x * x = 1) {y : G} (hyx : y * x = x * y) :
    y ∈ normalizer (Q : Set G) := by
  by_contra hy
  have hodd := hQ.2 y hy
  have hxmem : x ∈ Q ⊓ rightConjugate Q y := by
    refine ⟨hxQ, (mem_rightConjugate_iff Q y x).2 ?_⟩
    rw [hyx, mul_inv_cancel_right]
    exact hxQ
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
  have h2 := hodd.of_dvd_nat (hxo ▸ Subgroup.orderOf_dvd_natCard _ hxmem)
  exact (Nat.not_odd_iff_even.2 even_two) h2

theorem normalizer_rightConjugate_centralizer {A : Subgroup G} (hA : standardComponentIsStandard A)
    (c : G) :
    normalizer (rightConjugate (centralizer (A : Set G)) c : Set G) =
      normalizer (rightConjugate A c : Set G) := by
  ext y
  rw [AS76b.mem_normalizer_rightConjugate_iff, AS76b.mem_normalizer_rightConjugate_iff,
    AS76b.normalizer_centralizer_eq hA]

theorem centralizer_rightConjugate_eq (A : Subgroup G) (c : G) :
    centralizer (rightConjugate A c : Set G) = rightConjugate (centralizer (A : Set G)) c := by
  ext y
  rw [mem_centralizer_rightConjugate_iff, mem_rightConjugate_iff]

theorem sq_eq_one_of_mem_rightConjugate [Finite G] {K : Subgroup G}
    (hR : ∀ S : Subgroup G, IsSylowOf 2 S K → IsElemAbelian 2 S) (c : G) {k : G}
    (hk : k ∈ rightConjugate K c) {n : ℕ} (hkn : k ^ 2 ^ n = 1) : k ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hkS⟩ := AS76b.exists_isSylowOf_le ((zpowers_le).2 hk)
    (isPGroup_zpowers_of_pow_two hkn)
  have hS' : IsSylowOf 2 (rightConjugate S c⁻¹) K := by
    have := AschbacherTheorem3.isSylowOf_rightConjugate hS c⁻¹
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
  have hE := AS76b.isElemAbelian_rightConjugate (hR _ hS') c
  rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at hE
  exact hE.2 k (hkS (mem_zpowers k))

end Tight

section Key

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] [CharP F 2]
  {A : Subgroup G} {ψ : normalizer (A : Set G) →* MulAut (projectiveSL 3 F)}

omit [Finite F] [CharP F 2] in
theorem conj_mul_conj_mem_inner (γ : MulAut (projectiveSL 3 F)) (p : projectiveSL 3 F) :
    γ * MulAut.conj p * γ⁻¹ ∈
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range :=
  ⟨γ p, conj_map_eq γ p⟩

theorem commutatorElement_conj {M : Type*} [Group M] (γ a b : M) :
    ⁅γ * a * γ⁻¹, γ * b * γ⁻¹⁆ = γ * ⁅a, b⁆ * γ⁻¹ := by
  simp only [commutatorElement_def]
  group

theorem commutatorElement_mem' {M : Type*} [Group M] {H : Subgroup M} {a b : M} (ha : a ∈ H)
    (hb : b ∈ H) : ⁅a, b⁆ ∈ H := by
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

omit [Finite G] in
theorem exists_commutator_sq_psi_eq (hψ : IsActionHom A
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G))) (h8 : 8 ≤ Nat.card F)
    {x : G} (hxA : x ∈ A) (hx2 : x * x = 1) (hxC : x ∉ centralizer (A : Set G)) :
    ∃ d u : G, ∃ hd : d ∈ A, ∃ hu : u ∈ A, d * x = x * d ∧ u * x = x * u ∧
      ⁅ψ ⟨d, le_normalizer hd⟩, ψ ⟨u, le_normalizer hu⟩⁆ ^ 2 = ψ ⟨x, le_normalizer hxA⟩ := by
  set τ := ψ ⟨x, le_normalizer hxA⟩ with hτ
  have hτX : τ ∈ (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range :=
    hψ.map_mem x hxA
  have hτ2 : τ * τ = 1 := by
    rw [hτ, ← psi_mul (le_normalizer hxA) (le_normalizer hxA)]
    have h1 : (⟨x * x, mul_mem (le_normalizer hxA) (le_normalizer hxA)⟩ :
        normalizer (A : Set G)) = 1 := Subtype.ext hx2
    rw [h1, map_one]
  have hτ1 : τ ≠ 1 := fun h => hxC ((hψ.eq_one_iff _).1 h)
  obtain ⟨γ, hγ⟩ := exists_eq_conj_x0 hτX hτ2 hτ1
  obtain ⟨l, hl⟩ := LinearCover.exists_units_pow_three_ne_one (K := F) h8
  have hl' : (l : F) ^ 3 ≠ 1 := fun h => hl (Units.ext (by rw [Units.val_pow_eq_pow_val, h,
    Units.val_one]))
  obtain ⟨v, hv, hvsq⟩ := exists_commutator_sq_eq_x0 hl'
  obtain ⟨d, hd, hdψ⟩ := hψ.exists_eq _ (conj_mul_conj_mem_inner γ (projTorus F l))
  obtain ⟨u, hu, huψ⟩ := hψ.exists_eq _ (conj_mul_conj_mem_inner γ v)
  have hxN : x ∈ normalizer (A : Set G) := le_normalizer hxA
  have hxZ : ∀ z ∈ A ⊓ centralizer (A : Set G), x * z = z * x := fun z hz =>
    mem_centralizer_iff.1 hz.2 x hxA
  have hcd : MulAut.conj (projTorus F l) * MulAut.conj (x0 F) =
      MulAut.conj (x0 F) * MulAut.conj (projTorus F l) := by
    rw [← map_mul, ← map_mul, projTorus_mul_comm_of_mem_projCenterW l x0_mem_projCenterW]
  have hcu : MulAut.conj v * MulAut.conj (x0 F) = MulAut.conj (x0 F) * MulAut.conj v := by
    rw [← map_mul, ← map_mul, x0_mul_comm hv]
  refine ⟨d, u, hd, hu, commute_of_psi_commute hψ hZ hxN hx2 hxZ hd ?_,
    commute_of_psi_commute hψ hZ hxN hx2 hxZ hu ?_, ?_⟩
  · rw [hdψ, show ψ ⟨x, hxN⟩ = τ from rfl, hγ]
    calc γ * MulAut.conj (projTorus F l) * γ⁻¹ * (γ * MulAut.conj (x0 F) * γ⁻¹)
        = γ * (MulAut.conj (projTorus F l) * MulAut.conj (x0 F)) * γ⁻¹ := by group
      _ = γ * (MulAut.conj (x0 F) * MulAut.conj (projTorus F l)) * γ⁻¹ := by rw [hcd]
      _ = γ * MulAut.conj (x0 F) * γ⁻¹ * (γ * MulAut.conj (projTorus F l) * γ⁻¹) := by group
  · rw [huψ, show ψ ⟨x, hxN⟩ = τ from rfl, hγ]
    calc γ * MulAut.conj v * γ⁻¹ * (γ * MulAut.conj (x0 F) * γ⁻¹)
        = γ * (MulAut.conj v * MulAut.conj (x0 F)) * γ⁻¹ := by group
      _ = γ * (MulAut.conj (x0 F) * MulAut.conj v) * γ⁻¹ := by rw [hcu]
      _ = γ * MulAut.conj (x0 F) * γ⁻¹ * (γ * MulAut.conj v * γ⁻¹) := by group
  · rw [hdψ, huψ, hγ, commutatorElement_conj, ← map_commutatorElement, conj_pow, ← map_pow,
      sq, hvsq]

theorem odd_card_inf_rightConjugate_centralizer (hA : standardComponentIsStandard A)
    (hψ : IsActionHom A (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range ψ)
    (hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)))
    (hR : ∀ S : Subgroup G, IsSylowOf 2 S (centralizer (A : Set G)) → IsElemAbelian 2 S)
    {m : ℕ} (hm : 3 ≤ m) (hF : Nat.card F = 2 ^ m) (c : G) :
    Odd (Nat.card (A ⊓ rightConjugate (centralizer (A : Set G)) c : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : 8 ≤ Nat.card F := by
    rw [hF]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  by_contra hodd
  obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(A ⊓ rightConjugate (centralizer (A : Set G)) c)) 2
    (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd))
  rw [Subgroup.orderOf_mk] at hxo
  obtain ⟨hxA, hxK⟩ := mem_inf.1 hx
  have hx2 : x * x = 1 := by rw [← sq, ← hxo, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxo
    norm_num at hxo
  have hxsq : x ^ 2 ^ 1 = 1 := by rw [pow_one, sq, hx2]
  have hxC : x ∉ centralizer (A : Set G) := fun h =>
    hx1 (eq_one_of_odd_of_pow_two (odd_orderOf_of_mem hZ ⟨hxA, h⟩) hxsq)
  obtain ⟨d, u, hd, hu, hdx, hux, hsq⟩ := exists_commutator_sq_psi_eq hψ hZ h8 hxA hx2 hxC
  have htight := AS76b.tightlyEmbedded_rightConjugate (AS76b.tightlyEmbedded_centralizer hA) c
  have hdN : d ∈ normalizer (rightConjugate A c : Set G) := by
    rw [← normalizer_rightConjugate_centralizer hA c]
    exact mem_normalizer_of_commute_of_mem htight hxK hx1 hx2 hdx
  have huN : u ∈ normalizer (rightConjugate A c : Set G) := by
    rw [← normalizer_rightConjugate_centralizer hA c]
    exact mem_normalizer_of_commute_of_mem htight hxK hx1 hx2 hux
  obtain ⟨e, -, he2, he3, he4⟩ := exists_twoPartExp G
  set q := ⁅d, u⁆ with hq
  have hqA : q ∈ A := commutatorElement_mem' hd hu
  have hψq : ψ ⟨q * q, le_normalizer (mul_mem hqA hqA)⟩ = ψ ⟨x, le_normalizer hxA⟩ := by
    rw [psi_mul (le_normalizer hqA) (le_normalizer hqA), ← sq, ← hsq]
    congr 1
    exact psi_commutatorElement (le_normalizer hd) (le_normalizer hu)
  have hz := inv_mul_mem_of_psi_eq hψ (mul_mem hqA hqA) hxA hψq
  set z := (q * q)⁻¹ * x with hzdef
  set p := q ^ e with hp
  have hpp : p * p = x := by
    have hqq : q * q = x * z⁻¹ := by rw [hzdef, mul_inv_rev, inv_inv, mul_inv_cancel_left]
    have hcomm : Commute x z⁻¹ := mem_centralizer_iff.1 (inv_mem hz.2) x hxA
    calc p * p = (q * q) ^ e := by rw [hp, (Commute.refl q).mul_pow]
      _ = (x * z⁻¹) ^ e := by rw [hqq]
      _ = x ^ e * z⁻¹ ^ e := hcomm.mul_pow e
      _ = x := by rw [he3 x 1 hxsq, he4 z⁻¹ (odd_orderOf_of_mem hZ (inv_mem hz)), mul_one]
  have hψc := isActionHom_conjAct hψ c
  have hqN : q ∈ normalizer (rightConjugate A c : Set G) := commutatorElement_mem' hdN huN
  have hpN : p ∈ normalizer (rightConjugate A c : Set G) := pow_mem hqN e
  have hD : conjAct ψ c ⟨p, hpN⟩ ∈ linearAutGroup 3 F := by
    rw [psi_pow hqN]
    refine pow_mem ?_ e
    rw [psi_commutatorElement hdN huN]
    exact commutatorElement_mem_linearAutGroup (by omega : 1 ≤ m) hF _ _
  have hp4 : p ^ 2 ^ 2 = 1 := by
    rw [show (2 : ℕ) ^ 2 = 2 * 2 by norm_num, pow_mul, sq p, hpp, sq, hx2]
  have hX : conjAct ψ c ⟨p, hpN⟩ ∈
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)).range := by
    refine mem_inner_of_mem_linearAutGroup hD (k := 2) ?_
    rw [← psi_pow hpN]
    have h1 : (⟨p ^ 2 ^ 2, pow_mem hpN _⟩ : normalizer (rightConjugate A c : Set G)) = 1 :=
      Subtype.ext hp4
    rw [h1, map_one]
  obtain ⟨a, haAc, ha⟩ := hψc.exists_eq _ hX
  have hk : p * a⁻¹ ∈ centralizer (rightConjugate A c : Set G) := by
    refine (hψc.eq_one_iff ⟨p * a⁻¹, mul_mem hpN (inv_mem (le_normalizer haAc))⟩).1 ?_
    rw [psi_mul hpN (inv_mem (le_normalizer haAc)), psi_inv (le_normalizer haAc), ha,
      mul_inv_cancel]
  have hcomm2 : Commute (p * a⁻¹) a := (mem_centralizer_iff.1 hk a haAc).symm
  have hpeq : p = (p * a⁻¹) ^ e * a ^ e := by
    calc p = p ^ e := (he3 p 2 hp4).symm
      _ = (p * a⁻¹ * a) ^ e := by rw [inv_mul_cancel_right]
      _ = (p * a⁻¹) ^ e * a ^ e := hcomm2.mul_pow e
  have hkK : (p * a⁻¹) ^ e ∈ rightConjugate (centralizer (A : Set G)) c := by
    rw [← centralizer_rightConjugate_eq]
    exact pow_mem hk e
  have hk2 : ((p * a⁻¹) ^ e) ^ 2 = 1 := sq_eq_one_of_mem_rightConjugate hR c hkK (he2 _)
  have hcomm3 : Commute ((p * a⁻¹) ^ e) (a ^ e) := hcomm2.pow_pow e e
  have hxAc : x ∈ rightConjugate A c := by
    have hxa : x = a ^ e * a ^ e := by
      calc x = p * p := hpp.symm
        _ = (p * a⁻¹) ^ e * a ^ e * ((p * a⁻¹) ^ e * a ^ e) := by rw [← hpeq]
        _ = (p * a⁻¹) ^ e * (a ^ e * (p * a⁻¹) ^ e) * a ^ e := by group
        _ = (p * a⁻¹) ^ e * ((p * a⁻¹) ^ e * a ^ e) * a ^ e := by rw [hcomm3.eq]
        _ = ((p * a⁻¹) ^ e) ^ 2 * (a ^ e * a ^ e) := by group
        _ = a ^ e * a ^ e := by rw [hk2, one_mul]
    rw [hxa]
    exact mul_mem (pow_mem haAc e) (pow_mem haAc e)
  have hxZc : x ∈ rightConjugate A c ⊓ centralizer (rightConjugate A c : Set G) :=
    ⟨hxAc, by rw [centralizer_rightConjugate_eq]; exact hxK⟩
  have hZc : Odd (Nat.card (rightConjugate A c ⊓ centralizer (rightConjugate A c : Set G) :
      Subgroup G)) := by
    rw [card_inf_centralizer_rightConjugate]
    exact hZ
  exact hx1 (eq_one_of_odd_of_pow_two (odd_orderOf_of_mem hZc hxZc) hxsq)

omit [Finite F] [CharP F 2] in
theorem inf_eq_bot_of_le_rightConjugate {c : G}
    (hKey : Odd (Nat.card (A ⊓ rightConjugate (centralizer (A : Set G)) c : Subgroup G)))
    {T : Subgroup G} (hT : IsPGroup 2 T) (hTK : T ≤ rightConjugate (centralizer (A : Set G)) c) :
    T ⊓ A = ⊥ :=
  two_subgroup_of_odd_eq_bot _ _ hT.to_inf_left hKey
    (le_inf inf_le_right (inf_le_left.trans hTK))

omit [Finite F] [CharP F 2] in
theorem not_conj_le_of_le
    (hKey : ∀ c : G, Odd (Nat.card (A ⊓ rightConjugate (centralizer (A : Set G)) c :
      Subgroup G)))
    {U : Subgroup G} (hU : IsPGroup 2 U) (hUK : U ≤ centralizer (A : Set G)) (hU1 : U ≠ ⊥)
    (g : G) : ¬ AS76b.Lemma34.conj U g ≤ A := by
  intro hle
  have hle' : AS76b.Lemma34.conj U g ≤ rightConjugate (centralizer (A : Set G)) g⁻¹ := by
    intro y hy
    rw [mem_rightConjugate_iff, inv_inv]
    obtain ⟨u, hu, rfl⟩ := hy
    have : g⁻¹ * ((MulAut.conj g).toMonoidHom u) * g = u := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact hUK hu
  have hbot := two_subgroup_of_odd_eq_bot _ _ (hU.map _) (hKey g⁻¹) (le_inf hle hle')
  exact hU1 ((map_eq_bot_iff_of_injective U (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective).1 hbot)

end Key

end CFSG.ComponentClassification.RankTwoL3Even
