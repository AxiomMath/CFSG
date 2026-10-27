module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup
import CFSG.FeitThompson.Local.OddFrobeniusComplementPrimeSubgroupsNormal
import CFSG.FeitThompson.Local.OddFrobeniusComplementCyclicSylows
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.PSubgroupCentralizersLiftQuotient
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Foundations.SylowExistencePrimePower
import CFSG.FeitThompson.OddOrder.TypeIIntersectionInSupportingKernel
import CFSG.FeitThompson.OddOrder.FrobeniusKernelContainsRoots
import CFSG.FeitThompson.OddOrder.InvariantHallComplement
import CFSG.FeitThompson.Representations.ConjugationTransportsDadeSignalizers

open Pointwise

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] {p q a : ℕ}

theorem coe_mul_coe_eq_coe_of_isComplement'_subgroupOf {H E L : Subgroup G} (hHL : H ≤ L)
    (hEL : E ≤ L) (h : (H.subgroupOf L).IsComplement' (E.subgroupOf L)) :
    (H : Set G) * (E : Set G) = (L : Set G) := by
  refine Set.Subset.antisymm ?_ fun x hx => ?_
  · rintro x ⟨u, hu, v, hv, rfl⟩
    exact L.mul_mem (hHL hu) (hEL hv)
  · obtain ⟨⟨u, v⟩, huv⟩ := h.2 (⟨x, hx⟩ : ↥L)
    exact ⟨(u : G), u.2, (v : G), v.2, congrArg Subtype.val huv⟩

theorem inf_eq_bot_of_isComplement'_subgroupOf {H E L : Subgroup G} (hEL : E ≤ L)
    (h : (H.subgroupOf L).IsComplement' (E.subgroupOf L)) : H ⊓ E = ⊥ := by
  have h1 : (H ⊓ E).subgroupOf L = ⊥ := by
    rw [Subgroup.subgroupOf, Subgroup.comap_inf]
    exact disjoint_iff.1 h.disjoint
  have h2 : H ⊓ E ⊓ L = ⊥ := disjoint_iff.1 (subgroupOf_eq_bot.1 h1)
  rwa [inf_eq_left.2 (le_trans inf_le_right hEL)] at h2

theorem conj_smul_subgroupOf {L E : Subgroup G} (hEL : E ≤ L) (g : ↥L) :
    (MulAut.conj (g : G) • E).subgroupOf L = MulAut.conj g • E.subgroupOf L := by
  have h1 : Subgroup.map L.subtype (MulAut.conj g • E.subgroupOf L)
      = MulAut.conj (g : G) • E := by
    rw [map_conj_smul, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hEL]; rfl
  rw [Subgroup.subgroupOf, ← h1, Subgroup.comap_map_eq_self_of_injective L.subtype_injective]

theorem conj_smul_le_of_mem {L E : Subgroup G} (hEL : E ≤ L) {l : G} (hl : l ∈ L) :
    MulAut.conj l • E ≤ L := by
  intro x hx
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
  simp only [MulAut.smul_def, MulAut.conj_inv_apply] at hx
  have h : l * (l⁻¹ * x * l) * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hl (hEL hx)) (L.inv_mem hl)
  simpa [mul_assoc] using h

theorem isComplement'_conj_smul {A K : Subgroup G} [A.Normal] (h : A.IsComplement' K) (g : G) :
    A.IsComplement' (MulAut.conj g • K) := by
  have hsup : A ⊔ MulAut.conj g • K = ⊤ := by
    have h1 : MulAut.conj g • (A ⊔ K) = MulAut.conj g • A ⊔ MulAut.conj g • K :=
      Subgroup.smul_sup _ _ _
    rw [h.sup_eq_top] at h1
    simpa using h1.symm
  have hinf : A ⊓ MulAut.conj g • K = ⊥ := by
    have h1 : MulAut.conj g • (A ⊓ K) = MulAut.conj g • A ⊓ MulAut.conj g • K :=
      Subgroup.smul_inf _ _ _
    rw [disjoint_iff.1 h.disjoint] at h1
    simpa using h1.symm
  exact (isComplement'_of_sup_eq_top_of_inf_eq_bot hsup hinf).symm

theorem le_normalizer_of_subgroupOf_le_normalizer {L B E : Subgroup G} (hBL : B ≤ L) (hEL : E ≤ L)
    (h : E.subgroupOf L ≤ normalizer ((B.subgroupOf L : Subgroup ↥L) : Set ↥L)) :
    E ≤ normalizer (B : Set G) := by
  refine Subgroup.le_normalizer_iff.2 fun e he b hb => ?_
  have he' : (⟨e, hEL he⟩ : ↥L) ∈ E.subgroupOf L := he
  have hb' : (⟨b, hBL hb⟩ : ↥L) ∈ B.subgroupOf L := hb
  simpa [Subgroup.mem_subgroupOf] using (Subgroup.le_normalizer_iff.1 h) _ he' _ hb'

theorem free_subgroupOf {L H E : Subgroup G} (hHL : H ≤ L)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer {e} = ⊥) :
    ∀ e ∈ E.subgroupOf L, e ≠ 1 → H.subgroupOf L ⊓ centralizer {e} = ⊥ := by
  intro e he he1
  rw [inf_centralizer_singleton_subgroupOf_eq_bot_iff hHL]
  exact hfree _ he fun h => he1 (Subtype.ext h)

theorem free_conj_smul {H E : Subgroup G} {l : G} (hl : l ∈ normalizer (H : Set G))
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer {e} = ⊥) :
    ∀ e ∈ MulAut.conj l • E, e ≠ 1 → H ⊓ centralizer {e} = ⊥ := by
  intro e he he1
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at he
  simp only [MulAut.smul_def, MulAut.conj_inv_apply] at he
  have hcancel : l * (l⁻¹ * e * l) * l⁻¹ = e := by group
  have he0 : l⁻¹ * e * l ≠ 1 := by
    intro h
    refine he1 ?_
    rw [h, mul_one, mul_inv_cancel] at hcancel
    exact hcancel.symm
  have hbot := hfree _ he he0
  have hHconj : MulAut.conj l • H = H := conj_smul_eq_self_of_mem_normalizer hl
  have hc : MulAut.conj l • centralizer ({l⁻¹ * e * l} : Set G) = centralizer ({e} : Set G) := by
    rw [smul_centralizer_singleton, hcancel]
  have key : MulAut.conj l • (H ⊓ centralizer ({l⁻¹ * e * l} : Set G)) = ⊥ := by
    rw [hbot]; simp
  rwa [Subgroup.smul_inf, hHconj, hc] at key

theorem natCard_dvd_of_isCyclic_of_pow_eq_one {K : Type*} [Group K] [Finite K] [IsCyclic K]
    (h : ∀ x : K, x ^ q = 1) : Nat.card K ∣ q := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  exact hx ▸ orderOf_dvd_of_pow_eq_one (h x)

theorem natCard_eq_mul_of_coe_mul_coe {Q C N : Subgroup G}
    (hNmul : (Q : Set G) * (C : Set G) = (N : Set G)) (hQC : Q ⊓ C = ⊥) :
    Nat.card ↥N = Nat.card ↥Q * Nat.card ↥C := by
  have h := natCard_mul_mul_natCard_inf Q C
  rw [hQC, hNmul] at h
  simpa using h

theorem exists_mem_le_conj_smul_of_natCard_eq_prime [Finite G] (hq : q.Prime)
    {L H E₀ B : Subgroup G} [Group.IsSolvable ↥L] (hHL : H ≤ L) (hE₀L : E₀ ≤ L)
    (hHnorm : (H.subgroupOf L).Normal)
    (hmul : (H : Set G) * (E₀ : Set G) = (L : Set G)) (hdisj : H ⊓ E₀ = ⊥)
    (hHall : (Nat.card ↥H).Coprime (H.relIndex L))
    (hBL : B ≤ L) (hB : Nat.card ↥B = q) (hHq : (Nat.card ↥H).Coprime q) :
    ∃ l ∈ L, B ≤ MulAut.conj l • E₀ := by
  have _i := hHnorm
  set π : Set ℕ := ((Nat.card ↥E₀).primeFactors : Set ℕ) with hπ
  have hcompl : (H.subgroupOf L).IsComplement' (E₀.subgroupOf L) :=
    isComplement'_subgroupOf_of_coe_mul_coe_eq hmul hdisj
  have hcardH : Nat.card ↥(H.subgroupOf L) = Nat.card ↥H := natCard_subgroupOf_of_le' hHL
  have hcardE₀ : Nat.card ↥(E₀.subgroupOf L) = Nat.card ↥E₀ := natCard_subgroupOf_of_le' hE₀L
  have hidx : (E₀.subgroupOf L).index = Nat.card ↥H := by rw [hcompl.index_eq_card, hcardH]
  have hidxH : (H.subgroupOf L).index = Nat.card ↥E₀ := by
    rw [hcompl.symm.index_eq_card, hcardE₀]
  have hcop : (Nat.card ↥H).Coprime (Nat.card ↥E₀) := by
    have h : H.relIndex L = Nat.card ↥E₀ := hidxH
    rwa [h] at hHall
  have hHallE₀ : IsHallSubgroup π (E₀.subgroupOf L) := by
    refine isHallSubgroup_iff.2 ⟨isPiNumber_iff.2 fun r hr => ?_, ?_⟩
    · rw [hcardE₀] at hr; exact hr
    · rw [hidx]
      refine isPiNumber_iff.2 fun r hr => ?_
      simp only [hπ, Set.mem_compl_iff, Finset.mem_coe]
      intro hmem
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      exact hrp.one_lt.ne' (Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd
        (Nat.dvd_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hmem)))
  have hcardB : Nat.card ↥(B.subgroupOf L) = q := by rw [natCard_subgroupOf_of_le' hBL, hB]
  have hqE₀ : q ∣ Nat.card ↥E₀ := by
    have hqL : q ∣ Nat.card ↥L := hB ▸ Subgroup.card_dvd_of_le hBL
    have hLcard : Nat.card ↥H * Nat.card ↥E₀ = Nat.card ↥L := by
      rw [← hcardH, ← hcardE₀, hcompl.card_mul_card]
    rcases (Nat.Prime.dvd_mul hq).1 (hLcard ▸ hqL) with h | h
    · exact absurd h ((Nat.Prime.coprime_iff_not_dvd hq).1 hHq.symm)
    · exact h
  have hBpi : IsPiNumber π (Nat.card ↥(B.subgroupOf L)) := by
    rw [hcardB]
    refine isPiNumber_iff.2 fun r hr => ?_
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq (Nat.prime_of_mem_primeFactors hr) hq).1
      (Nat.dvd_of_mem_primeFactors hr)
    simp [hπ, Nat.mem_primeFactors, hrq, hq, hqE₀, Nat.card_pos.ne']
  obtain ⟨F, hF, hBF⟩ := exists_isHallSubgroup_ge (G := ↥L) (π := π) hBpi
  obtain ⟨g, hg⟩ := exists_conj_smul_eq_of_isHallSubgroup hHallE₀ hF
  refine ⟨(g : G), g.2, le_of_subgroupOf_le hBL ?_⟩
  rw [conj_smul_subgroupOf hE₀L g]
  exact hg ▸ hBF

theorem free_complement_conj_smul {L H E₀ : Subgroup G} (hHL : H ≤ L) (hE₀L : E₀ ≤ L)
    (hHnorm : (H.subgroupOf L).Normal)
    (hmul : (H : Set G) * (E₀ : Set G) = (L : Set G)) (hdisj : H ⊓ E₀ = ⊥)
    (hfree : ∀ e ∈ E₀, e ≠ 1 → H ⊓ centralizer {e} = ⊥) {l : G} (hl : l ∈ L) :
    MulAut.conj l • E₀ ≤ L ∧
      (H : Set G) * ((MulAut.conj l • E₀ : Subgroup G) : Set G) = (L : Set G) ∧
      H ⊓ MulAut.conj l • E₀ = ⊥ ∧
      ∀ e ∈ MulAut.conj l • E₀, e ≠ 1 → H ⊓ centralizer {e} = ⊥ := by
  have _i := hHnorm
  have hEL : MulAut.conj l • E₀ ≤ L := conj_smul_le_of_mem hE₀L hl
  have hcompl : (H.subgroupOf L).IsComplement' (E₀.subgroupOf L) :=
    isComplement'_subgroupOf_of_coe_mul_coe_eq hmul hdisj
  have hcompl' : (H.subgroupOf L).IsComplement'
      ((MulAut.conj l • E₀ : Subgroup G).subgroupOf L) := by
    rw [conj_smul_subgroupOf hE₀L (⟨l, hl⟩ : ↥L)]
    exact isComplement'_conj_smul hcompl _
  refine ⟨hEL, coe_mul_coe_eq_coe_of_isComplement'_subgroupOf hHL hEL hcompl',
    inf_eq_bot_of_isComplement'_subgroupOf hEL hcompl',
    free_conj_smul (le_normalizer_of_normal_subgroupOf hHL hHnorm hl) hfree⟩

theorem eq_inf_of_le_normalizer_of_isElementaryAbelian [Finite G] (hq : q.Prime)
    {Q C L H E B : Subgroup G} (hQea : IsElementaryAbelian q Q)
    (hCcard : Nat.card ↥C = p) (hLodd : Odd (Nat.card ↥L)) [Group.IsSolvable ↥L]
    (hH : H ≠ ⊥) (hHL : H ≤ L) (hEL : E ≤ L) (hHnorm : (H.subgroupOf L).Normal)
    (hHnil : Group.IsNilpotent ↥H)
    (hfree : ∀ e ∈ E, e ≠ 1 → H ⊓ centralizer {e} = ⊥)
    (hNmul : (Q : Set G) * (C : Set G) = (normalizer (B : Set G) : Set G)) (hQC : Q ⊓ C = ⊥)
    (hQnorm : (Q.subgroupOf (normalizer (B : Set G))).Normal)
    (hBQ : B ≤ Q) (hBE : B ≤ E) (hEN : E ≤ normalizer (B : Set G))
    (hBcard : Nat.card ↥B = q) :
    Q ⊓ E = B ∧ Q.relIndex E ∣ p := by
  have _i := hHnorm
  have _j := hQnorm
  have := Fact.mk hq
  set N : Subgroup G := normalizer (B : Set G) with hNdef
  have hQN : Q ≤ N := fun x hx => by
    have h : x ∈ (Q : Set G) * (C : Set G) := ⟨x, hx, 1, C.one_mem, mul_one x⟩
    rw [hNmul] at h; exact h
  obtain ⟨d, hQd⟩ := hQea.exists_natCard_eq_pow hq
  have hNcard : Nat.card ↥N = p * q ^ d := by
    rw [natCard_eq_mul_of_coe_mul_coe hNmul hQC, hQd, hCcard, mul_comm]
  have hQindex : (Q.subgroupOf N).index = p := by
    have h := Subgroup.card_mul_index (Q.subgroupOf N)
    rw [natCard_subgroupOf_of_le' hQN, hQd, hNcard] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos d) (by rw [h, mul_comm])
  have hrel : Q.relIndex E ∣ p := by
    have h1 : (Q.subgroupOf N).relIndex (E.subgroupOf N) ∣ (Q.subgroupOf N).index :=
      Subgroup.relIndex_dvd_index_of_normal _ _
    rwa [Subgroup.relIndex_subgroupOf hEN, hQindex] at h1
  have hHbot : H.subgroupOf L ≠ ⊥ := fun h => hH <| by
    have h1 : H ⊓ L = ⊥ := disjoint_iff.1 (subgroupOf_eq_bot.1 h)
    rwa [inf_eq_left.2 hHL] at h1
  have hHnil' : Group.IsNilpotent ↥(H.subgroupOf L) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hHL)).2 hHnil
  have _k : Group.IsSolvable ↥(H.subgroupOf L) := by have := hHnil'; infer_instance
  have hzE₀ : IsZGroup ↥(E.subgroupOf L) :=
    isZGroup_of_free_complement hLodd hHbot (free_subgroupOf (E := E) hHL hfree)
  have _hzE : IsZGroup ↥E :=
    IsZGroup.of_injective
      (f := ((Subgroup.subgroupOfEquivOfLe hEL).symm : ↥E →* ↥(E.subgroupOf L)))
      (MulEquiv.injective _)
  have hQEE : Q ⊓ E ≤ E := inf_le_right
  have hpg : IsPGroup q ↥((Q ⊓ E).subgroupOf E) :=
    ((hQea.mono inf_le_left).isPGroup).of_equiv (Subgroup.subgroupOfEquivOfLe hQEE).symm
  have _hcyc : IsCyclic ↥(Q ⊓ E) :=
    haveI : IsCyclic ↥((Q ⊓ E).subgroupOf E) := hpg.isCyclic_of_isZGroup
    isCyclic_of_surjective ((Subgroup.subgroupOfEquivOfLe hQEE) : ↥((Q ⊓ E).subgroupOf E) →* _)
      (MulEquiv.surjective _)
  have hpow : ∀ x : ↥(Q ⊓ E), x ^ q = 1 := fun x =>
    Subtype.ext (by simpa using hQea.pow_eq_one (Subgroup.mem_inf.1 x.2).1)
  have hdvd : Nat.card ↥(Q ⊓ E) ∣ q := natCard_dvd_of_isCyclic_of_pow_eq_one hpow
  refine ⟨(Subgroup.eq_of_le_of_card_ge (le_inf hBQ hBE) ?_).symm, hrel⟩
  rw [hBcard]
  exact Nat.le_of_dvd hq.pos hdvd

theorem exists_mem_conj_smul_eq_of_natCard_eq_prime [Finite G] (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {N C D : Subgroup G} (hNcard : Nat.card ↥N = p * q ^ a)
    (hCN : C ≤ N) (hDN : D ≤ N) (hC : Nat.card ↥C = p) (hD : Nat.card ↥D = p) :
    ∃ n ∈ N, MulAut.conj n • C = D := by
  have := Fact.mk hp
  have hpq' : ¬ p ∣ q ^ a := (Nat.Prime.coprime_iff_not_dvd hp).1
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp hq).2 hpq))
  have hfac : (Nat.card ↥N).factorization p = 1 :=
    factorization_eq_of_eq_pow_mul hp hpq' (by rw [hNcard, pow_one])
  have hC' : Nat.card ↥(C.subgroupOf N) = p ^ (Nat.card ↥N).factorization p := by
    rw [natCard_subgroupOf_of_le' hCN, hC, hfac, pow_one]
  have hD' : Nat.card ↥(D.subgroupOf N) = p ^ (Nat.card ↥N).factorization p := by
    rw [natCard_subgroupOf_of_le' hDN, hD, hfac, pow_one]
  obtain ⟨g, hg⟩ := exists_conj_smul_eq hC' hD'
  refine ⟨(g : G), g.2, ?_⟩
  have h := congrArg (Subgroup.map N.subtype) hg
  rwa [map_conj_smul, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hCN, inf_eq_left.2 hDN] at h

theorem eq_or_exists_eq_sup_conj_smul [Finite G] (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {Q C N E B : Subgroup G} (hQa : Nat.card ↥Q = q ^ a) (hCcard : Nat.card ↥C = p)
    (hNmul : (Q : Set G) * (C : Set G) = (N : Set G)) (hQC : Q ⊓ C = ⊥)
    (hBcard : Nat.card ↥B = q) (hBE : B ≤ E) (hEN : E ≤ N)
    (hinf : Q ⊓ E = B) (hrel : Q.relIndex E ∣ p) :
    E = B ∨ ∃ y ∈ Q, E = B ⊔ MulAut.conj y⁻¹ • C := by
  have hCN : C ≤ N := fun x hx => by
    have h : x ∈ (Q : Set G) * (C : Set G) := ⟨1, Q.one_mem, x, hx, one_mul x⟩
    rw [hNmul] at h; exact h
  have hNcard : Nat.card ↥N = p * q ^ a := by
    rw [natCard_eq_mul_of_coe_mul_coe hNmul hQC, hQa, hCcard, mul_comm]
  have hidxeq : (B.subgroupOf E).index = Q.relIndex E := by
    rw [← hinf, Subgroup.inf_subgroupOf_right]; rfl
  have hEcard : Nat.card ↥E = q * (B.subgroupOf E).index := by
    have h := Subgroup.card_mul_index (B.subgroupOf E)
    rw [natCard_subgroupOf_of_le' hBE, hBcard] at h
    exact h.symm
  rcases hp.eq_one_or_self_of_dvd _ (hidxeq ▸ hrel) with h1 | hp1
  ·
    left
    refine (Subgroup.eq_of_le_of_card_ge hBE ?_).symm
    rw [hEcard, h1, mul_one, hBcard]
  ·
    right
    have hEcard' : Nat.card ↥E = q * p := by rw [hEcard, hp1]
    have := Fact.mk hp
    have hpE : p ∣ Nat.card ↥E := hEcard' ▸ Dvd.intro_left q rfl
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) p hpE
    set D : Subgroup G := (Subgroup.zpowers x).map E.subtype with hDdef
    have hDE : D ≤ E := Subgroup.map_subtype_le _
    have hDcard : Nat.card ↥D = p := by
      rw [hDdef, Subgroup.card_map_of_injective E.subtype_injective, Nat.card_zpowers, hx]
    have hBD : B ⊔ D = E := by
      have hcompl : (B.subgroupOf E).IsComplement' (D.subgroupOf E) := by
        refine Subgroup.isComplement'_of_coprime ?_ ?_
        · rw [natCard_subgroupOf_of_le' hBE, natCard_subgroupOf_of_le' hDE, hBcard, hDcard,
            hEcard']
        · rw [natCard_subgroupOf_of_le' hBE, natCard_subgroupOf_of_le' hDE, hBcard, hDcard]
          exact (Nat.coprime_primes hq hp).2 (Ne.symm hpq)
      have h := hcompl.sup_eq_top
      rw [← Subgroup.subgroupOf_sup hBE hDE] at h
      exact le_antisymm (sup_le hBE hDE) (Subgroup.subgroupOf_eq_top.1 h)
    obtain ⟨n, hn, hnCD⟩ := exists_mem_conj_smul_eq_of_natCard_eq_prime hp hq hpq hNcard hCN
      (le_trans hDE hEN) hCcard hDcard
    have hn' : n ∈ (Q : Set G) * (C : Set G) := by rw [hNmul]; exact hn
    obtain ⟨y, hy, c, hc, rfl⟩ := hn'
    refine ⟨y⁻¹, Q.inv_mem hy, ?_⟩
    have hyC : MulAut.conj y • C = D := by
      rw [← hnCD, map_mul, mul_smul,
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hc)]
    rw [inv_inv, hyC, hBD]

theorem supporting_frobenius_complement_shape [Finite G] (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {Q C L H E₀ B : Subgroup G} (hQea : IsElementaryAbelian q Q)
    (hCcard : Nat.card ↥C = p) (hLodd : Odd (Nat.card ↥L)) [Group.IsSolvable ↥L]
    (hH : H ≠ ⊥) (_hE₀ : E₀ ≠ ⊥) (hHL : H ≤ L) (hE₀L : E₀ ≤ L)
    (hHnorm : (H.subgroupOf L).Normal)
    (hmul : (H : Set G) * (E₀ : Set G) = (L : Set G)) (hdisj : H ⊓ E₀ = ⊥)
    (hHnil : Group.IsNilpotent ↥H) (hHall : (Nat.card ↥H).Coprime (H.relIndex L))
    (hfree : ∀ e ∈ E₀, e ≠ 1 → H ⊓ centralizer {e} = ⊥)
    (hBLQ : B ≤ L ⊓ Q) (hBcard : Nat.card ↥B = q) (hHq : (Nat.card ↥H).Coprime q)
    (hNmul : (Q : Set G) * (C : Set G) = (normalizer (B : Set G) : Set G)) (hQC : Q ⊓ C = ⊥)
    (hQnorm : (Q.subgroupOf (normalizer (B : Set G))).Normal) :
    ((H : Set G) * (B : Set G) = (L : Set G) ∧ H ⊓ B = ⊥) ∨
      ∃ y ∈ Q, (H : Set G) * ((B ⊔ MulAut.conj y⁻¹ • C : Subgroup G) : Set G) = (L : Set G) ∧
        H ⊓ (B ⊔ MulAut.conj y⁻¹ • C) = ⊥ := by
  have _i := hHnorm
  have hBL : B ≤ L := le_trans hBLQ inf_le_left
  have hBQ : B ≤ Q := le_trans hBLQ inf_le_right
  obtain ⟨l, hl, hBE⟩ := exists_mem_le_conj_smul_of_natCard_eq_prime hq hHL hE₀L hHnorm hmul hdisj
    hHall hBL hBcard hHq
  set E : Subgroup G := MulAut.conj l • E₀ with hEdef
  obtain ⟨hEL, hEmul, hEdisj, hEfree⟩ :=
    free_complement_conj_smul hHL hE₀L hHnorm hmul hdisj hfree hl
  have hHbot : H.subgroupOf L ≠ ⊥ := fun h => hH <| by
    have h1 : H ⊓ L = ⊥ := disjoint_iff.1 (subgroupOf_eq_bot.1 h)
    rwa [inf_eq_left.2 hHL] at h1
  have hHnil' : Group.IsNilpotent ↥(H.subgroupOf L) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hHL)).2 hHnil
  have hBcard' : Nat.card ↥(B.subgroupOf L) = q := by rw [natCard_subgroupOf_of_le' hBL, hBcard]
  have hEN : E ≤ normalizer (B : Set G) :=
    le_normalizer_of_subgroupOf_le_normalizer hBL hEL
      (le_normalizer_of_natCard_eq_prime (L := ↥L) (H := H.subgroupOf L) (E := E.subgroupOf L)
        hLodd hHbot hHnil' (free_subgroupOf (E := E) hHL hEfree) hq
        (P := B.subgroupOf L) (fun x hx => hBE hx) hBcard')
  obtain ⟨hQEB, hrel⟩ := eq_inf_of_le_normalizer_of_isElementaryAbelian hq hQea hCcard hLodd hH
    hHL hEL hHnorm hHnil hEfree hNmul hQC hQnorm hBQ hBE hEN hBcard
  obtain ⟨d, hQd⟩ := hQea.exists_natCard_eq_pow hq
  rcases eq_or_exists_eq_sup_conj_smul hp hq hpq hQd hCcard hNmul hQC hBcard hBE hEN hQEB hrel
    with hEB | ⟨y, hy, hEy⟩
  · exact Or.inl ⟨hEB ▸ hEmul, hEB ▸ hEdisj⟩
  · exact Or.inr ⟨y, hy, hEy ▸ hEmul, hEy ▸ hEdisj⟩

end CFSG.FeitThompson

end
