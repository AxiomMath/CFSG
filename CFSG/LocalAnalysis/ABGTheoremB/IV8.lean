module

public import CFSG.LocalAnalysis.ABGTheoremB.Statements
import CFSG.LocalAnalysis.ABGTheoremB.IV1
import CFSG.LinearAlgebra.LinearGroups.Perfect
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ThompsonPQ
import CFSG.GroupTheory.ABGLocalTools.Criteria
import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizers
import CFSG.GroupTheory.Gorenstein.MaxCardThompson
public import CFSG.LocalAnalysis.ABGTheoremB.Facts

public section

namespace CFSG.ABGTheoremB

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

universe u

section General

variable {G : Type u} [Group G]

private theorem commutator_mem_left {M K : Subgroup G}
    (hKM : K ≤ Subgroup.normalizer (M : Set G)) {x y : G} (hx : x ∈ M) (hy : y ∈ K) :
    x * y * x⁻¹ * y⁻¹ ∈ M := by
  have h : y * x⁻¹ * y⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp (hKM hy) x⁻¹).mp (M.inv_mem hx)
  have := M.mul_mem hx h
  simpa [mul_assoc] using this

private theorem commutator_mem_right {M K : Subgroup G}
    (hKM : K ≤ Subgroup.normalizer (M : Set G)) {x y : G} (hx : x ∈ K) (hy : y ∈ M) :
    x * y * x⁻¹ * y⁻¹ ∈ M :=
  M.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKM hx) y).mp hy) (M.inv_mem hy)

private theorem mem_normalizer_of_conj_mem [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : H.map (MulAut.conj g : G →* G) ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem inf_eq_bot_of_coprime {A B : Subgroup G}
    (h : Nat.Coprime (Nat.card A) (Nat.card B)) : A ⊓ B = ⊥ :=
  (Subgroup.disjoint_of_coprime_natCard h).eq_bot

private theorem inf_eq_bot_of_isPGroup [Finite G] {r : ℕ} [Fact r.Prime] {A B : Subgroup G}
    (hA : IsPGroup r A)
    (hB : Nat.Coprime r (Nat.card B)) : A ⊓ B = ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  exact inf_eq_bot_of_coprime (by rw [hk]; exact Nat.Coprime.pow_left k hB)

private theorem coprime_two_of_odd {B : Subgroup G} (hB : Odd (Nat.card B)) :
    Nat.Coprime 2 (Nat.card B) :=
  Nat.coprime_two_left.mpr hB

private theorem normalizer_le_normalizer_of_characteristic [Finite G] {P Q : Subgroup G}
    (hQP : Q ≤ P) (hQ : (Q.subgroupOf P).Characteristic) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  intro g hg
  apply mem_normalizer_of_conj_mem
  intro q hq
  let φ : P ≃* P := Subgroup.normalizerMonoidHom P ⟨g, hg⟩
  have hfix := hQ.fixed φ
  have hmem : (⟨q, hQP hq⟩ : P) ∈ Subgroup.comap φ.toMonoidHom (Q.subgroupOf P) := by
    rw [hfix]
    exact hq
  exact hmem

private theorem eq_one_of_mem_of_coprime {r : ℕ} [Fact r.Prime] {A : Subgroup G}
    (hA : IsPGroup r A) {g : G} (hg : g ∈ A) (hcop : Nat.Coprime r (orderOf g)) : g = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hA) ⟨g, hg⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at hcop
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · have h := Nat.Coprime.coprime_dvd_right (dvd_pow_self r (Nat.succ_ne_zero k)) hcop
    rw [Nat.coprime_self] at h
    exact absurd h (Fact.out : r.Prime).one_lt.ne'

private theorem eq_one_of_mem_of_mem_odd' {A K : Subgroup G} (hA : IsPGroup 2 A)
    (hK : Odd (Nat.card K)) {g : G} (hgA : g ∈ A) (hgK : g ∈ K) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply eq_one_of_mem_of_coprime hA hgA
  exact Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard K hgK)
    (coprime_two_of_odd hK)

private theorem odd_card_of_isPGroup' [Finite G] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {X : Subgroup G} (hX : IsPGroup r X) : Odd (Nat.card X) := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rw [hk]
  exact (hr.eq_two_or_odd'.resolve_left hr2).pow

private theorem card_sup_of_coprime' [Finite G] {r : ℕ} [Fact r.Prime] {M Q : Subgroup G}
    (hQM : Q ≤ Subgroup.normalizer (M : Set G)) (hM : Nat.Coprime r (Nat.card M))
    (hQ : IsPGroup r Q) : Nat.card (M ⊔ Q : Subgroup G) = Nat.card M * Nat.card Q := by
  have h := card_sup_mul_card_inf_of_le_normalizer hQM
  rw [inf_comm, inf_eq_bot_of_isPGroup hQ hM, Subgroup.card_bot, mul_one] at h
  exact h

private theorem isSylowOf_sup_of_coprime' [Finite G] {r : ℕ} [Fact r.Prime] {M Q : Subgroup G}
    (hQM : Q ≤ Subgroup.normalizer (M : Set G)) (hM : Nat.Coprime r (Nat.card M))
    (hQ : IsPGroup r Q) : IsSylowOf r Q (M ⊔ Q) := by
  apply isSylowOf_of_card le_sup_right
  rw [card_sup_of_coprime' hQM hM hQ]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
  have hp : r.Prime := Fact.out
  have hMp : ¬ r ∣ Nat.card M := (Nat.Prime.coprime_iff_not_dvd hp).mp hM
  rw [hk, mul_comm, Nat.factorization_mul (pow_ne_zero k hp.ne_zero) Nat.card_pos.ne',
    Finsupp.add_apply, Nat.Prime.factorization_pow hp, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hMp, add_zero]

private theorem isSolvable_solvRadIn [Finite G] (H : Subgroup G) :
    Group.IsSolvable (solvRadIn H) := by
  have : Group.IsSolvable (CFSG.solvableRadical H) := solvableRadical_isSolvable
  exact Group.isSolvable_of_surjective
    (f := ((CFSG.solvableRadical H).equivMapOfInjective H.subtype
      H.subtype_injective).toMonoidHom)
    ((CFSG.solvableRadical H).equivMapOfInjective H.subtype H.subtype_injective).surjective

private theorem le_solvRadIn {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hK : Group.IsSolvable K) :
    K ≤ solvRadIn H := by
  have hnormal : (K.subgroupOf H).Normal := by
    constructor
    intro a ha h
    exact (Subgroup.mem_normalizer_iff.mp (hnorm h.property) a).mp ha
  have hsolv : Group.IsSolvable (K.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKH).injective
  have hle : K.subgroupOf H ≤ CFSG.solvableRadical H := le_sSup ⟨hnormal, hsolv⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

private theorem isSolvable_of_le {A B : Subgroup G} (hAB : A ≤ B) (hB : Group.IsSolvable B) :
    Group.IsSolvable A :=
  Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hAB)
    (Subgroup.inclusion_injective hAB)

private theorem isSolvable_sup_of_le_normalizer' {A B : Subgroup G}
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) (hA : Group.IsSolvable A)
    (hB : Group.IsSolvable B) : Group.IsSolvable (A ⊔ B : Subgroup G) := by
  set M : Subgroup G := A ⊔ B with hM
  have hMA : M ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hBA
  have hAM : A ≤ M := le_sup_left
  have : (A.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAM).mpr hMA
  have : Group.IsSolvable (A.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hAM).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAM).injective
  let f : B →* M ⧸ A.subgroupOf M :=
    (QuotientGroup.mk' (A.subgroupOf M)).comp (Subgroup.inclusion (le_sup_right : B ≤ M))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf M) y
    have hm' : m ∈ ((B ⊔ A : Subgroup G) : Set G) := by rw [sup_comm]; exact hm
    rw [Subgroup.coe_mul_of_left_le_normalizer_right B A hBA] at hm'
    obtain ⟨b, hb, a, ha, rfl⟩ := hm'
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using ha
  have : Group.IsSolvable (M ⧸ A.subgroupOf M) := Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient (A.subgroupOf M)

private theorem exists_mem_mul_normalizer_of_isSylowOf [Finite G] {r : ℕ} [Fact r.Prime]
    {K P : Subgroup G} (hP : IsSylowOf r P K) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, k⁻¹ * g ∈ Subgroup.normalizer (P : Set G) := by
  have hgK : K.map (MulAut.conj g : G →* G) = K := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have hP' : IsSylowOf r (P.map (MulAut.conj g : G →* G)) K := by
    apply isSylowOf_of_card
    · rw [← hgK]
      exact Subgroup.map_mono hP.le
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hP.card_eq
  obtain ⟨k, hk, hconj⟩ := hP.exists_mem_conj hP'
  refine ⟨k, hk, mem_normalizer_of_conj_mem fun x hx => ?_⟩
  have hx' : g * x * g⁻¹ ∈ P.map (MulAut.conj g : G →* G) := ⟨x, hx, rfl⟩
  have := (hconj _).mp hx'
  simpa [mul_assoc] using this

private theorem mem_centralizer_subgroupOf_iff' {T X : Subgroup G} (hTX : T ≤ X) {g : X} :
    g ∈ Subgroup.centralizer ((T.subgroupOf X : Subgroup X) : Set X) ↔
      (g : G) ∈ Subgroup.centralizer (T : Set G) := by
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe, Subgroup.mem_subgroupOf]
  constructor
  · intro h t ht
    exact congrArg Subtype.val (h ⟨t, hTX ht⟩ ht)
  · intro h t ht
    exact Subtype.ext (h _ ht)

private theorem automizerIndex_subgroupOf_eq {T X : Subgroup G} (hTX : T ≤ X) :
    automizerIndex (T.subgroupOf X) =
      (Subgroup.centralizer (T : Set G)).relIndex (Subgroup.normalizer (T : Set G) ⊓ X) := by
  have hC : Subgroup.centralizer ((T.subgroupOf X : Subgroup X) : Set X) =
      (Subgroup.centralizer (T : Set G)).subgroupOf X := by
    ext g
    rw [mem_centralizer_subgroupOf_iff' hTX, Subgroup.mem_subgroupOf]
  rw [automizerIndex, hC, ← Subgroup.subgroupOf_normalizer_eq hTX,
    ← Subgroup.inf_subgroupOf_right (Subgroup.normalizer (T : Set G)) X,
    Subgroup.relIndex_subgroupOf inf_le_right]

private theorem thompsonCenter_map_conj [Finite G] (P : Subgroup G) (g : G) :
    (CFSG.thompsonCenter P).map (MulAut.conj g).toMonoidHom =
      CFSG.thompsonCenter (P.map (MulAut.conj g).toMonoidHom) :=
  CFSG.map_thompsonCenter_of_injective _ P ((MulAut.conj g).injective.comp P.subtype_injective)

private theorem mem_of_mem_sup_of_odd_orderOf {O Z : Subgroup G}
    (hZO : Z ≤ Subgroup.normalizer (O : Set G)) (hZ : IsPGroup 2 Z) (hO : Odd (Nat.card O))
    {y : G} (hy : y ∈ O ⊔ Z) (hyo : Odd (orderOf y)) : y ∈ O := by
  have hy' : y ∈ ((Z ⊔ O : Subgroup G) : Set G) := by rw [sup_comm]; exact hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Z O hZO] at hy'
  obtain ⟨z, hz, o, ho, rfl⟩ := hy'
  have key : ∀ n : ℕ, ∃ o' ∈ O, (z * o) ^ n = z ^ n * o' := by
    intro n
    induction n with
    | zero => exact ⟨1, O.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨o', ho', h⟩ := ih
      have hconj : z⁻¹ * o' * z⁻¹⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp (hZO (Z.inv_mem hz)) o').mp ho'
      refine ⟨z⁻¹ * o' * z⁻¹⁻¹ * o, O.mul_mem hconj ho, ?_⟩
      rw [pow_succ, h, pow_succ]
      group
  obtain ⟨o', ho', h⟩ := key (orderOf (z * o))
  rw [pow_orderOf_eq_one] at h
  have hzn : z ^ orderOf (z * o) = 1 := by
    have e : z ^ orderOf (z * o) = o'⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    exact eq_one_of_mem_of_mem_odd' hZ hO (Z.pow_mem hz _) (e ▸ O.inv_mem ho')
  have hz1 : z = 1 := by
    have hdvd := orderOf_dvd_of_pow_eq_one hzn
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZ) ⟨z, hz⟩
    rw [Subgroup.orderOf_mk] at hk
    rw [hk] at hdvd
    have hodd := hyo.of_dvd_nat hdvd
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact orderOf_eq_one_iff.mp hk
    · exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩))
  rw [hz1]
  simpa using ho

private theorem normalizer_le_normalizer_centralizer' (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  simp only [Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hc y hy
    have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (X : Set G)).inv_mem hg) y).mp hy
    have := hc _ hy'
    calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * y * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
      _ = g * c * g⁻¹ * y := by group
  · intro hc y hy
    have hy' : g * y * g⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hg y).mp hy
    have := hc _ hy'
    calc y * c = g⁻¹ * ((g * y * g⁻¹) * (g * c * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * c * g⁻¹) * (g * y * g⁻¹)) * g := by rw [this]
      _ = c * y := by group

private theorem solvRadIn_le_solvRadIn [Finite G] {A H : Subgroup G} (hAH : A ≤ H)
    (hHA : H ≤ Subgroup.normalizer (A : Set G)) : solvRadIn A ≤ solvRadIn H := by
  set S := solvRadIn A with hS
  have hSA : S ≤ A := solvRadIn_le A
  have : (CFSG.solvableRadical A).Normal := solvableRadical_normal
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := le_normalizer_map_subtype A _
  have hSsolv : Group.IsSolvable S := isSolvable_solvRadIn A
  have hconj : ∀ g ∈ H, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro g hg
    set W := S.map (MulAut.conj g).toMonoidHom with hW
    have hWA : W ≤ A := by
      rintro _ ⟨s, hs, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hHA hg) s).mp (hSA hs)
    have hAW : A ≤ Subgroup.normalizer (W : Set G) := by
      apply CFSG.subgroup_le_normalizer_of_conj_mem
      rintro ⟨a, ha⟩ _ ⟨s, hs, rfl⟩
      have ha' : g⁻¹ * a * g ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (hHA (H.inv_mem hg)) a).mp ha
        simpa using this
      have hs' := (Subgroup.mem_normalizer_iff.mp (hAS ha') s).mp hs
      refine ⟨_, hs', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hWsolv : Group.IsSolvable W :=
      Group.isSolvable_of_surjective
        (f := (S.equivMapOfInjective _ (MulAut.conj g).injective).toMonoidHom)
        (S.equivMapOfInjective _ (MulAut.conj g).injective).surjective
    have hle := le_solvRadIn hWA hAW hWsolv
    intro s hs
    exact hle ⟨s, hs, rfl⟩
  exact le_solvRadIn (hSA.trans hAH) (fun g hg => mem_normalizer_of_conj_mem (hconj g hg))
    hSsolv

private theorem le_pPrimePCoreIn_of_thompson [Finite G] {r : ℕ} [Fact r.Prime]
    {Ns Rs Q X M : Subgroup G} (hcon : IsPConstrained r Ns)
    (hRs : IsSylowOf r Rs (pPrimePCoreIn r Ns)) (hQ : IsPGroup r Q) (hQNs : Q ≤ Ns)
    (hQRs : Q ≤ Subgroup.normalizer (Rs : Set G)) (hXNs : X ≤ Ns)
    (hXr : Nat.Coprime r (Nat.card X)) (hXQ : X ≤ Subgroup.centralizer (Q : Set G))
    (hM : Nat.Coprime r (Nat.card M))
    (hXRQ : ∀ x ∈ X, ∀ y ∈ Rs ⊓ Subgroup.centralizer (Q : Set G), x * y * x⁻¹ * y⁻¹ ∈ M) :
    X ≤ pPrimePCoreIn r Ns := by
  set Mp : Subgroup Ns := CFSG.pPrimeCore r Ns with hMp
  set π : Ns →* Ns ⧸ Mp := QuotientGroup.mk' Mp with hπ
  set R' : Subgroup Ns := Rs.subgroupOf Ns with hR'def
  set Q' : Subgroup Ns := Q.subgroupOf Ns with hQ'def
  set X' : Subgroup Ns := X.subgroupOf Ns with hX'def
  have hRsNs : Rs ≤ Ns := hRs.le.trans (pPrimePCoreIn_le r Ns)
  have hR' : IsSylowOf r R' (Op_p'p r Ns) := by
    rw [← isSylowOf_map_subtype_iff Ns, hR'def, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hRsNs]
    exact hRs
  have hR'p : IsPGroup r R' := hR'.isPGroup
  have hsup : Mp ⊔ R' = Op_p'p r Ns := (sup_eq_Op_p'p_iff_isSylowOf hR'p).mpr hR'
  have hRbar : R'.map π = pCore r (Ns ⧸ Mp) := by
    calc R'.map π = (Mp ⊔ R').map π := by
          rw [Subgroup.map_sup, hπ, QuotientGroup.map_mk'_self, bot_sup_eq]
      _ = (Op_p'p r Ns).map π := by rw [hsup]
      _ = pCore r (Ns ⧸ Mp) :=
          Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hRbarp : IsPGroup r (R'.map π) := hR'p.map π
  have hRbar_norm : ∀ K : Subgroup (Ns ⧸ Mp), K ≤ Subgroup.normalizer (R'.map π : Set _) := by
    intro K
    rw [hRbar]
    exact Subgroup.le_normalizer_of_normal
  have hR'Op : R' ≤ Op_p'p r Ns := hR'.le
  have hPQ : ⁅R'.map π, X'.map π⁆ = ⊥ := by
    apply CFSG.GorensteinWalter.ThompsonPQ.thompson_p_times_q (p := r) (Q'.map π) (X'.map π)
      (R'.map π)
    · exact (hQ.comap_subtype (K := Ns)).map π
    · exact hRbarp
    · apply Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd X' π)
      rw [hX'def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXNs).toEquiv]
      exact hXr
    · exact hRbar_norm _
    · exact hRbar_norm _
    · rw [← Subgroup.map_commutator]
      have : ⁅Q', X'⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        apply Subtype.ext
        exact ((Subgroup.mem_centralizer_iff.mp (hXQ hx)) q hq).symm
      rw [this, Subgroup.map_bot]
    · rintro _ ⟨⟨y', hy', rfl⟩, hyC⟩
      have hyR : (y' : G) ∈ Rs := hy'
      have hyQ : (y' : G) ∈ Subgroup.centralizer (Q : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        set q' : Ns := ⟨q, hQNs hq⟩
        have hq' : q' ∈ Q' := hq
        have hcomm := Subgroup.mem_centralizer_iff.mp hyC (π q') ⟨q', hq', rfl⟩
        have hc1 : q' * y' * q'⁻¹ * y'⁻¹ ∈ Mp := by
          rw [← QuotientGroup.eq_one_iff (N := Mp)]
          change π (q' * y' * q'⁻¹ * y'⁻¹) = 1
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
          group
        have hc2 : q' * y' * q'⁻¹ * y'⁻¹ ∈ R' := by
          change ((q' * y' * q'⁻¹ * y'⁻¹ : Ns) : G) ∈ Rs
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          exact commutator_mem_right hQRs hq hyR
        have hbot : R' ⊓ Mp = ⊥ := inf_eq_bot_of_isPGroup hR'p pPrimeCore_coprime_card
        have hc : q' * y' * q'⁻¹ * y'⁻¹ = 1 := by
          have : q' * y' * q'⁻¹ * y'⁻¹ ∈ R' ⊓ Mp := ⟨hc2, hc1⟩
          rwa [hbot, Subgroup.mem_bot] at this
        have hc' : q' * y' = y' * q' := by
          rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def]
          exact hc
        exact congrArg Subtype.val hc'
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x', hx', rfl⟩
      have hxX : (x' : G) ∈ X := hx'
      set c : Ns := x' * y' * x'⁻¹ * y'⁻¹ with hc
      have hcO : c ∈ Op_p'p r Ns :=
        commutator_mem_right (fun _ _ => Subgroup.le_normalizer_of_normal (Subgroup.mem_top _))
          (Subgroup.mem_top x') (hR'Op hy')
      have hcM : (c : G) ∈ M := by
        rw [hc]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hXRQ _ hxX _ ⟨hyR, hyQ⟩
      have hπc : π c ∈ pCore r (Ns ⧸ Mp) := hcO
      have hπc1 : π c = 1 := by
        apply eq_one_of_mem_of_coprime (pCore_isPGroup (G := Ns ⧸ Mp) (p := r)) hπc
        apply Nat.Coprime.coprime_dvd_right (orderOf_map_dvd π c)
        rw [← Subgroup.orderOf_coe]
        exact Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard M hcM) hM
      rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv] at hπc1
      rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def]
      exact hπc1
  have hXbar : X'.map π ≤ Subgroup.centralizer (R'.map π : Set (Ns ⧸ Mp)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hPQ
  have hX' : X' ≤ Subgroup.centralizer (R' : Set Ns) ⊔ Mp := by
    rw [centralizer_sup_eq_comap pPrimeCore_coprime_card hR'p]
    intro x hx
    exact hXbar ⟨x, hx, rfl⟩
  have hX'' : X' ≤ Op_p'p r Ns := hX'.trans (sup_le (hcon R' hR') pPrimeCore_le_Op_p'p)
  intro x hx
  exact ⟨⟨x, hXNs hx⟩, hX'' hx, rfl⟩

private theorem automizerIndex_subgroupOf_eq_of_forall {T X : Subgroup G} (hTX : T ≤ X)
    (h : ∀ m ∈ Subgroup.normalizer (T : Set G),
      ∃ c ∈ Subgroup.centralizer (T : Set G), c⁻¹ * m ∈ X) :
    automizerIndex (T.subgroupOf X) = automizerIndex T := by
  set C := Subgroup.centralizer (T : Set G) with hC
  set M := Subgroup.normalizer (T : Set G) with hM
  have hCM : C ≤ M := Subgroup.centralizer_le_normalizer _
  have hMC : M ≤ Subgroup.normalizer (C : Set G) := normalizer_le_normalizer_centralizer' T
  have hsup : (M ⊓ X) ⊔ C = M := by
    refine le_antisymm (sup_le inf_le_left hCM) fun m hm => ?_
    obtain ⟨c, hc, hcm⟩ := h m hm
    have hcm' : c⁻¹ * m ∈ M ⊓ X := ⟨M.mul_mem (M.inv_mem (hCM hc)) hm, hcm⟩
    have : m = c * (c⁻¹ * m) := by group
    rw [this]
    exact Subgroup.mul_mem _ (le_sup_right (a := M ⊓ X) hc) (le_sup_left (b := C) hcm')
  rw [automizerIndex_subgroupOf_eq hTX, automizerIndex, ← hC, ← hM,
    ← relIndex_sup_right_of_le_normalizer (inf_le_left.trans hMC), hsup]

private theorem relIndex_ne_zero' [Finite G] (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h
  have := Subgroup.relIndex_mul_card H K
  rw [h, zero_mul] at this
  exact Nat.card_pos.ne' this.symm

private theorem mem_normalizer_subgroupOf_iff' {T X : Subgroup G} (hTX : T ≤ X) {g : X} :
    g ∈ Subgroup.normalizer ((T.subgroupOf X : Subgroup X) : Set X) ↔
      (g : G) ∈ Subgroup.normalizer (T : Set G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq hTX, Subgroup.mem_subgroupOf]

private theorem exists_of_three_dvd_automizerIndex' [Finite G] {T X : Subgroup G} (hTX : T ≤ X)
    (h : 3 ∣ automizerIndex (T.subgroupOf X)) :
    ∃ g ∈ X, g ∈ Subgroup.normalizer (T : Set G) ∧ g ^ 3 ∈ Subgroup.centralizer (T : Set G) ∧
      g ∉ Subgroup.centralizer (T : Set G) := by
  set T' : Subgroup X := T.subgroupOf X
  set Nt := Subgroup.normalizer (T' : Set X)
  set Ct := Subgroup.centralizer (T' : Set X)
  have hCN : Ct ≤ Nt := Subgroup.centralizer_le_normalizer _
  have : (Ct.subgroupOf Nt).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr
      (normalizer_le_normalizer_centralizer' T')
  have h3 : 3 ∣ Nat.card (Nt ⧸ Ct.subgroupOf Nt) := by
    rw [← Subgroup.index_eq_card]
    exact h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 3 h3
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨((g : X) : G), (g : X).2, (mem_normalizer_subgroupOf_iff' hTX).mp g.2, ?_, ?_⟩
  · have hg3 : ((g ^ 3 : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := by
      rw [QuotientGroup.mk_pow, ← hq, pow_orderOf_eq_one]
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hg3
    have := (mem_centralizer_subgroupOf_iff' hTX).mp hg3
    simpa using this
  · intro hg
    have hg' : ((g : Nt) : Nt ⧸ Ct.subgroupOf Nt) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact (mem_centralizer_subgroupOf_iff' hTX).mpr hg
    rw [hg', orderOf_one] at hq
    exact absurd hq (by norm_num)

private theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  rw [MulEquiv.toMonoidHom_eq_coe]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

private theorem exists_mem_mul_mem_normalizer [Finite G] {r : ℕ} [Fact r.Prime]
    {H O R₁ Q T : Subgroup G} (hOH : O ≤ H) (hHO : H ≤ Subgroup.normalizer (O : Set G))
    (hO2 : Odd (Nat.card O)) (hOr : Nat.Coprime r (Nat.card O)) (hR₁ : IsPGroup r R₁)
    (hR₁H : R₁ ≤ H) (hHR : H ≤ Subgroup.normalizer ((O ⊔ R₁ : Subgroup G) : Set G))
    (hQ : IsPGroup r Q) (hQH : Q ≤ H) (hQR : Q ≤ Subgroup.normalizer (R₁ : Set G))
    (hT : IsPGroup 2 T) (hTH : T ≤ H) (hTR : T ≤ Subgroup.normalizer (R₁ : Set G))
    (hTQ : T ≤ Subgroup.normalizer (Q : Set G)) {u : G} (huH : u ∈ H)
    (huQ : u ∈ Subgroup.normalizer (Q : Set G)) (huT : u ∈ Subgroup.centralizer (T : Set G)) :
    ∃ z ∈ O, z ∈ Subgroup.centralizer (Q : Set G) ∧ z ∈ Subgroup.centralizer (T : Set G) ∧
      z * u ∈ Subgroup.normalizer (R₁ : Set G) := by
  set A : Subgroup G := Q ⊔ R₁ with hA
  have hAp : IsPGroup r A := IsPGroup.to_sup_of_normal_right' hQ hR₁ hQR
  have hTA : T ≤ Subgroup.normalizer (A : Set G) :=
    (le_inf hTQ hTR).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  set B : Subgroup G := A ⊔ T with hB
  have hBH : B ≤ H := sup_le (sup_le hQH hR₁H) hTH
  have hcopB : Nat.Coprime (Nat.card O) (Nat.card B) := by
    have hdvd : Nat.card B ∣ Nat.card A * Nat.card T :=
      Dvd.intro _ (card_sup_mul_card_inf_of_le_normalizer hTA)
    apply Nat.Coprime.coprime_dvd_right hdvd
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hAp
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hT
    rw [ha, hb]
    exact Nat.Coprime.mul_right (Nat.Coprime.pow_right a hOr.symm)
      (Nat.Coprime.pow_right b (coprime_two_of_odd hO2).symm)
  have hOB : O ⊓ B = ⊥ := inf_eq_bot_of_coprime hcopB
  have hBO : B ≤ Subgroup.normalizer (O : Set G) := hBH.trans hHO
  set φ : G →* G := (MulAut.conj u).toMonoidHom with hφ
  set B' : Subgroup G := B.map φ with hB'
  have huN : u ∈ Subgroup.normalizer (T : Set G) := Subgroup.centralizer_le_normalizer _ huT
  set W : Subgroup G := O ⊔ B with hW
  have hB'W : B' ≤ W := by
    rw [hB', hB, hA, Subgroup.map_sup, Subgroup.map_sup, map_conj_eq_of_mem_normalizer huQ,
      map_conj_eq_of_mem_normalizer huN]
    refine sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_right)) ?_)
      (le_sup_right.trans le_sup_right)
    calc R₁.map φ ≤ (O ⊔ R₁).map φ := Subgroup.map_mono le_sup_right
      _ = O ⊔ R₁ := map_conj_eq_of_mem_normalizer (hHR huH)
      _ ≤ W := sup_le le_sup_left ((le_sup_right.trans le_sup_left).trans le_sup_right)
  have hcardB' : Nat.card B' = Nat.card B :=
    Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hOW : O ≤ W := le_sup_left
  have hBW : B ≤ W := le_sup_right
  have hWO : W ≤ Subgroup.normalizer (O : Set G) := sup_le Subgroup.le_normalizer hBO
  have hcardW : Nat.card W = Nat.card O * Nat.card B := by
    have h := card_sup_mul_card_inf_of_le_normalizer hBO
    rw [hOB, Subgroup.card_bot, mul_one] at h
    exact h
  set N' : Subgroup W := O.subgroupOf W with hN'
  set H' : Subgroup W := B.subgroupOf W with hH'
  set K' : Subgroup W := B'.subgroupOf W with hK'
  have hN'n : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOW).mpr hWO
  have hcN' : Nat.card N' = Nat.card O := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOW).toEquiv
  have hcH' : Nat.card H' = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBW).toEquiv
  have hcK' : Nat.card K' = Nat.card B := by
    rw [← hcardB']
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB'W).toEquiv
  have hcW : Nat.card W = Nat.card N' * Nat.card H' := by rw [hcN', hcH', hcardW]
  have hcompH : N'.IsComplement' H' :=
    Subgroup.isComplement'_of_coprime hcW.symm (by rw [hcN', hcH']; exact hcopB)
  have hcompK : N'.IsComplement' K' :=
    Subgroup.isComplement'_of_coprime (by rw [hcN', hcK', ← hcardW])
      (by rw [hcN', hcK']; exact hcopB)
  have hindex : N'.index = Nat.card B := by
    have h := Subgroup.card_mul_index N'
    rw [hcN', hcardW] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h
  obtain ⟨n, hn⟩ := CFSG.GorensteinWalter.SchurZassenhaus.exists_mem_normal_conjugator_of_coprime
    N' H' K' hN'n hcompH hcompK (by rw [hcN', hindex]; exact hcopB)
  set n₀ : G := ((n : W) : G) with hn₀
  have hn₀O : n₀ ∈ O := n.2
  have key : ∀ k ∈ B', n₀⁻¹ * k * n₀ ∈ B := by
    intro k hk
    have hk' : (⟨k, hB'W hk⟩ : W) ∈ K' := hk
    rw [hn] at hk'
    obtain ⟨h, hh, hhk⟩ := hk'
    have hhk' : n₀ * (h : G) * n₀⁻¹ = k := congrArg Subtype.val hhk
    have : n₀⁻¹ * k * n₀ = (h : G) := by rw [← hhk']; group
    rw [this]
    exact hh
  have hfix : ∀ a ∈ B, a ∈ B' → a * n₀⁻¹ = n₀⁻¹ * a := by
    intro a haB haB'
    have h1 : n₀⁻¹ * a * n₀ * a⁻¹ ∈ B := B.mul_mem (key a haB') (B.inv_mem haB)
    have h2 : n₀⁻¹ * a * n₀ * a⁻¹ ∈ O := by
      have : a * n₀ * a⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hBO haB) n₀).mp hn₀O
      have := O.mul_mem (O.inv_mem hn₀O) this
      simpa [mul_assoc] using this
    have h3 : n₀⁻¹ * a * n₀ * a⁻¹ ∈ O ⊓ B := ⟨h2, h1⟩
    rw [hOB, Subgroup.mem_bot] at h3
    calc a * n₀⁻¹ = (n₀⁻¹ * a * n₀ * a⁻¹)⁻¹ * (n₀⁻¹ * a) := by group
      _ = n₀⁻¹ * a := by rw [h3, inv_one, one_mul]
  refine ⟨n₀⁻¹, O.inv_mem hn₀O, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_,
    Subgroup.mem_centralizer_iff.mpr fun a ha => ?_, mem_normalizer_of_conj_mem fun y hy => ?_⟩
  · apply hfix a ((le_sup_left.trans le_sup_left : Q ≤ B) ha)
    have ha' : u⁻¹ * a * u⁻¹⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q : Set G)).inv_mem huQ) a).mp ha
    refine ⟨u⁻¹ * a * u⁻¹⁻¹, (le_sup_left.trans le_sup_left : Q ≤ B) ha', ?_⟩
    simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · apply hfix a ((le_sup_right : T ≤ B) ha)
    refine ⟨a, (le_sup_right : T ≤ B) ha, ?_⟩
    simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(Subgroup.mem_centralizer_iff.mp huT a ha).symm]
    group
  ·
    have hyB : y ∈ B := (le_sup_right.trans le_sup_left : R₁ ≤ B) hy
    have h1 : n₀⁻¹ * u * y * (n₀⁻¹ * u)⁻¹ ∈ B := by
      have := key (u * y * u⁻¹) ⟨y, hyB, by simp [hφ, MulAut.conj_apply]⟩
      convert this using 1
      group
    have h2 : n₀⁻¹ * u * y * (n₀⁻¹ * u)⁻¹ ∈ O ⊔ R₁ :=
      (Subgroup.mem_normalizer_iff.mp (hHR (H.mul_mem (H.inv_mem (hOH hn₀O)) huH)) y).mp
        ((le_sup_right : R₁ ≤ O ⊔ R₁) hy)
    rw [← SetLike.mem_coe, sup_comm,
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hR₁H.trans hHO)] at h2
    obtain ⟨y₁, hy₁, o, ho, hyo⟩ := h2
    dsimp only at hyo
    have ho1 : o = 1 := by
      have hoB : o = y₁⁻¹ * (n₀⁻¹ * u * y * (n₀⁻¹ * u)⁻¹) := by rw [← hyo]; group
      have : o ∈ O ⊓ B := ⟨ho, hoB ▸ B.mul_mem (B.inv_mem
        ((le_sup_right.trans le_sup_left : R₁ ≤ B) hy₁)) h1⟩
      rwa [hOB, Subgroup.mem_bot] at this
    rw [ho1, mul_one] at hyo
    rw [← hyo]
    exact hy₁

private theorem mem_map_conj_iff {P : Subgroup G} {g x : G} :
    x ∈ P.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rw [e]
    exact hy
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

private theorem isSylowOf_map_conj [Finite G] {r : ℕ} [Fact r.Prime] {P H : Subgroup G}
    (hP : IsSylowOf r P H) {g : G} (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    IsSylowOf r (P.map (MulAut.conj g).toMonoidHom) H := by
  apply isSylowOf_of_card
  · rw [← map_conj_eq_of_mem_normalizer hg]
    exact Subgroup.map_mono hP.le
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hP.card_eq

end General

namespace Setting

variable {G : Type u} [Group G] [Finite G] (σ : Setting G)

omit [Finite G] in
private theorem L₀_le_L' : σ.L₀ ≤ σ.L := le_sup_left

omit [Finite G] in
private theorem S_le_L' : (σ.S : Subgroup G) ≤ σ.L := le_sup_right

private theorem L_le_N' (hσ : σ.IsValid) : σ.L ≤ σ.N := sup_le hσ.L₀_le_N (σ.S_le_N hσ)

private theorem ON_le_solvRadIn_N (hII : σ.NStructure) : σ.ON ≤ solvRadIn σ.N := by
  rw [hII.N_solvRad]
  exact le_sup_left

private theorem solvRadIn_N_le_L (hσ : σ.IsValid) (hII : σ.NStructure) :
    solvRadIn σ.N ≤ σ.L := by
  rw [hII.N_solvRad]
  exact sup_le (hσ.ON_le_L₀.trans (σ.L₀_le_L')) (inf_le_left.trans (σ.S_le_L'))

private theorem not_commutator_L₀_le (hσ : σ.IsValid) :
    ¬ ⁅σ.L₀, σ.L₀⁆ ≤ solvRadIn σ.N := by
  intro h
  obtain ⟨F, hF, hFfin, hcard, ψ, hψ, -⟩ := hσ.L₀_quotient
  have : Fintype F := Fintype.ofFinite F
  have h4 : ∃ s : Finset F, s.card = 4 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]; have := hσ.five_lt_q; omega)
    exact ⟨t, ht⟩
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  have hnt : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F) := by
    refine ⟨⟨⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩, 1, fun he => ?_⟩⟩
    have := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (A : Matrix (Fin 2) (Fin 2) F) 0 1) he
    simp at this
  set W : Subgroup σ.L₀ := (solvRadIn σ.N).subgroupOf σ.L₀ with hW
  have hWsolv : Group.IsSolvable W := by
    have : Group.IsSolvable (solvRadIn σ.N) := isSolvable_solvRadIn σ.N
    let f : W →* solvRadIn σ.N :=
      (σ.L₀.subtype.comp W.subtype).codRestrict (solvRadIn σ.N) (fun w => w.2)
    have hf : Function.Injective f := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
    exact Group.isSolvable_of_isSolvable_injective hf
  have hcomm : commutator σ.L₀ ≤ W := by
    intro c hc
    have hmap : (c : G) ∈ (commutator σ.L₀).map σ.L₀.subtype := ⟨c, hc, rfl⟩
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at hmap
    exact h hmap
  have hsurj : Function.Surjective (ψ.comp W.subtype) := by
    intro m
    have htop : (commutator σ.L₀).map ψ = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr hψ, ← commutator_def, hperf.commutator_eq_top]
    have hm : m ∈ (commutator σ.L₀).map ψ := by rw [htop]; exact Subgroup.mem_top m
    obtain ⟨c, hc, rfl⟩ := hm
    exact ⟨⟨c, hcomm hc⟩, rfl⟩
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) :=
    Group.isSolvable_of_surjective hsurj
  exact Group.IsPerfect.not_isSolvable _ this

private theorem le_solvRadIn_N_of_cover (hσ : σ.IsValid) (hII : σ.NStructure)
    {Y K : Subgroup G} (hYN : Y ≤ σ.N) (hY : Group.IsSolvable Y) (hKN : K ≤ σ.N)
    (hKY : K ≤ Subgroup.normalizer (Y : Set G))
    (hcov : (σ.L₀ : Set G) ⊆ (K : Set G) * (σ.ON : Set G)) : Y ≤ solvRadIn σ.N := by
  set SN := solvRadIn σ.N with hSN
  set A : Subgroup G := σ.L₀ ⊔ SN with hA
  set B : Subgroup G := Y ⊔ SN with hB
  have hSNN : SN ≤ σ.N := solvRadIn_le σ.N
  have : (CFSG.solvableRadical σ.N).Normal := solvableRadical_normal
  have hNSN : σ.N ≤ Subgroup.normalizer (SN : Set G) := le_normalizer_map_subtype σ.N _
  have hSNsolv : Group.IsSolvable SN := isSolvable_solvRadIn σ.N
  have hAN : A ≤ σ.N := sup_le hσ.L₀_le_N hSNN
  have hNA : σ.N ≤ Subgroup.normalizer (A : Set G) :=
    (le_inf hσ.N_le_normalizer_L₀ hNSN).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hBsolv : Group.IsSolvable B := by
    rw [hB, sup_comm]
    exact isSolvable_sup_of_le_normalizer' (hYN.trans hNSN) hSNsolv hY
  have hONSN : σ.ON ≤ SN := σ.ON_le_solvRadIn_N hII
  have hL₀B : σ.L₀ ≤ Subgroup.normalizer (B : Set G) := by
    intro l hl
    obtain ⟨k, hk, o, ho, rfl⟩ := hcov hl
    exact Subgroup.mul_mem _
      (normalizer_inf_normalizer_le_normalizer_sup Y SN ⟨hKY hk, hNSN (hKN hk)⟩)
      (Subgroup.le_normalizer (le_sup_right (a := Y) (hONSN ho)))
  have hAB : A ≤ Subgroup.normalizer (B : Set G) :=
    sup_le hL₀B ((le_sup_right : SN ≤ B).trans Subgroup.le_normalizer)
  have hW : A ⊓ B ≤ SN := by
    have h1 : A ⊓ B ≤ solvRadIn A :=
      le_solvRadIn inf_le_left
        ((le_inf Subgroup.le_normalizer hAB).trans Subgroup.inf_normalizer_le_normalizer_inf)
        (isSolvable_of_le inf_le_right hBsolv)
    exact h1.trans (solvRadIn_le_solvRadIn hAN hNA)
  have hcomm : ∀ y ∈ Y, ∀ l ∈ σ.L₀, y * l * y⁻¹ * l⁻¹ ∈ SN := by
    intro y hy l hl
    apply hW
    refine ⟨commutator_mem_right hNA (hYN hy) (le_sup_left (b := SN) hl), ?_⟩
    have := commutator_mem_left hL₀B (le_sup_left (b := SN) hy) hl
    exact this
  let C₀ : Subgroup G :=
    { carrier := {n | n ∈ σ.N ∧ ∀ l ∈ σ.L₀, n * l * n⁻¹ * l⁻¹ ∈ SN}
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨σ.N.mul_mem haN hbN, fun l hl => ?_⟩
        have h1 : a * (b * l * b⁻¹ * l⁻¹) * a⁻¹ ∈ SN :=
          (Subgroup.mem_normalizer_iff.mp (hNSN haN) _).mp (hb l hl)
        have := SN.mul_mem h1 (ha l hl)
        convert this using 1
        group
      one_mem' := ⟨σ.N.one_mem, fun l _ => by simp⟩
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨σ.N.inv_mem haN, fun l hl => ?_⟩
        have h1 : a⁻¹ * (a * l * a⁻¹ * l⁻¹)⁻¹ * a⁻¹⁻¹ ∈ SN :=
          (Subgroup.mem_normalizer_iff.mp (hNSN (σ.N.inv_mem haN)) _).mp (SN.inv_mem (ha l hl))
        convert h1 using 1
        group }
  have hC₀N : C₀ ≤ σ.N := fun n hn => hn.1
  have hNC₀ : σ.N ≤ Subgroup.normalizer (C₀ : Set G) := by
    apply CFSG.subgroup_le_normalizer_of_conj_mem
    rintro ⟨m, hm⟩ n ⟨hnN, hn⟩
    refine ⟨σ.N.mul_mem (σ.N.mul_mem hm hnN) (σ.N.inv_mem hm), fun l hl => ?_⟩
    have hl' : m⁻¹ * l * m⁻¹⁻¹ ∈ σ.L₀ :=
      (Subgroup.mem_normalizer_iff.mp (hσ.N_le_normalizer_L₀ (σ.N.inv_mem hm)) l).mp hl
    have h1 : m * (n * (m⁻¹ * l * m⁻¹⁻¹) * n⁻¹ * (m⁻¹ * l * m⁻¹⁻¹)⁻¹) * m⁻¹ ∈ SN :=
      (Subgroup.mem_normalizer_iff.mp (hNSN hm) _).mp (hn _ hl')
    convert h1 using 1
    group
  have hSNC₀ : SN ≤ C₀ := fun s hs =>
    ⟨hSNN hs, fun l hl => commutator_mem_left hNSN hs (hσ.L₀_le_N hl)⟩
  have hC₀ : C₀ ≤ SN := by
    by_contra hC
    have hL := hII.N_minimalNormal C₀ hC₀N hNC₀ hC
    rw [sup_eq_left.mpr hSNC₀] at hL
    apply σ.not_commutator_L₀_le hσ
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (hL ha).2 b hb
  exact fun y hy => hC₀ ⟨hYN hy, hcomm y hy⟩

private theorem solvRadIn_L_eq (hσ : σ.IsValid) (hII : σ.NStructure) :
    solvRadIn σ.L = solvRadIn σ.N := by
  have : (CFSG.solvableRadical σ.L).Normal := solvableRadical_normal
  apply le_antisymm
  · exact σ.le_solvRadIn_N_of_cover hσ hII ((solvRadIn_le σ.L).trans (σ.L_le_N' hσ))
      (isSolvable_solvRadIn σ.L) (σ.L_le_N' hσ) (le_normalizer_map_subtype σ.L _)
      (fun l hl => ⟨l, σ.L₀_le_L' hl, 1, σ.ON.one_mem, mul_one l⟩)
  · have : (CFSG.solvableRadical σ.N).Normal := solvableRadical_normal
    exact le_solvRadIn (σ.solvRadIn_N_le_L hσ hII)
      ((σ.L_le_N' hσ).trans (le_normalizer_map_subtype σ.N _)) (isSolvable_solvRadIn σ.N)

private theorem x_mul_x' (hσ : σ.IsValid) : σ.x * σ.x = 1 := by
  rw [← pow_two, ← hσ.x_order]
  exact pow_orderOf_eq_one _

private theorem x₂_mul_x₂' (hσ : σ.IsValid) : σ.x₂ * σ.x₂ = 1 := by
  rw [← pow_two, ← hσ.x₂_order]
  exact pow_orderOf_eq_one _

private theorem x_ne_one' (hσ : σ.IsValid) : σ.x ≠ 1 := by
  intro h
  have h2 := hσ.x_order
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

private theorem x₂_ne_one' (hσ : σ.IsValid) : σ.x₂ ≠ 1 := by
  intro h
  have h2 := hσ.x₂_order
  rw [h, orderOf_one] at h2
  exact absurd h2 (by norm_num)

omit [Finite G] in
private theorem mem_centralizer_T_iff' {g : G} :
    g ∈ Subgroup.centralizer (σ.T : Set G) ↔ σ.x * g = g * σ.x ∧ σ.x₂ * g = g * σ.x₂ := by
  rw [T, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  simp

private theorem mem_T_cases' (hσ : σ.IsValid) {t : G} (ht : t ∈ σ.T) :
    t = 1 ∨ t = σ.x ∨ t = σ.x₂ ∨ t = σ.x * σ.x₂ := by
  have hc : Commute σ.x σ.x₂ := hσ.commute
  have hxi : σ.x⁻¹ = σ.x := inv_eq_of_mul_eq_one_right (σ.x_mul_x' hσ)
  have hx₂i : σ.x₂⁻¹ = σ.x₂ := inv_eq_of_mul_eq_one_right (σ.x₂_mul_x₂' hσ)
  have key : ∃ a b : ℕ, t = σ.x ^ a * σ.x₂ ^ b := by
    refine Subgroup.closure_induction (p := fun t _ => ∃ a b : ℕ, t = σ.x ^ a * σ.x₂ ^ b)
      ?_ ?_ ?_ ?_ ht
    · rintro g (rfl | rfl)
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
    · exact ⟨0, 0, by simp⟩
    · rintro g h _ _ ⟨a, b, rfl⟩ ⟨c, d, rfl⟩
      refine ⟨a + c, b + d, ?_⟩
      have hbc : σ.x₂ ^ b * σ.x ^ c = σ.x ^ c * σ.x₂ ^ b := (hc.symm.pow_pow b c).eq
      rw [pow_add, pow_add]
      calc σ.x ^ a * σ.x₂ ^ b * (σ.x ^ c * σ.x₂ ^ d)
          = σ.x ^ a * (σ.x₂ ^ b * σ.x ^ c) * σ.x₂ ^ d := by simp only [mul_assoc]
        _ = σ.x ^ a * (σ.x ^ c * σ.x₂ ^ b) * σ.x₂ ^ d := by rw [hbc]
        _ = σ.x ^ a * σ.x ^ c * (σ.x₂ ^ b * σ.x₂ ^ d) := by simp only [mul_assoc]
    · rintro g _ ⟨a, b, rfl⟩
      refine ⟨a, b, ?_⟩
      rw [mul_inv_rev, ← inv_pow, ← inv_pow, hxi, hx₂i]
      exact (hc.symm.pow_pow b a).eq
  obtain ⟨a, b, rfl⟩ := key
  rw [← pow_mod_orderOf σ.x a, hσ.x_order, ← pow_mod_orderOf σ.x₂ b, hσ.x₂_order]
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [ha, hb]

private theorem conj_x_eq_x₂_of_automizer (hσ : σ.IsValid) {g : G}
    (hg : g ∈ Subgroup.normalizer (σ.T : Set G))
    (h3 : g ^ 3 ∈ Subgroup.centralizer (σ.T : Set G))
    (h1 : g ∉ Subgroup.centralizer (σ.T : Set G)) :
    g * σ.x * g⁻¹ = σ.x₂ ∨ g ^ 2 * σ.x * (g ^ 2)⁻¹ = σ.x₂ := by
  have hxx := σ.x_mul_x' hσ
  have hx₂x₂ := σ.x₂_mul_x₂' hσ
  have hcomm : σ.x * σ.x₂ = σ.x₂ * σ.x := hσ.commute
  have hx1 := σ.x_ne_one' hσ
  have hx₂1 := σ.x₂_ne_one' hσ
  have hne := hσ.x_ne_x₂
  have hinj : ∀ a b : G, g * a * g⁻¹ = g * b * g⁻¹ → a = b := fun a b h => by simpa using h
  have hmul : ∀ a b : G, g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := fun a b => by group
  have hxT : g * σ.x * g⁻¹ ∈ σ.T := (Subgroup.mem_normalizer_iff.mp hg σ.x).mp σ.x_mem_T
  have hx₂T : g * σ.x₂ * g⁻¹ ∈ σ.T := (Subgroup.mem_normalizer_iff.mp hg σ.x₂).mp σ.x₂_mem_T
  have hcube : ∀ t ∈ σ.T, g * (g * (g * t * g⁻¹) * g⁻¹) * g⁻¹ = t := by
    intro t ht
    have := (Subgroup.mem_centralizer_iff.mp h3) t ht
    rw [pow_three] at this
    calc g * (g * (g * t * g⁻¹) * g⁻¹) * g⁻¹ = g * (g * g) * t * (g * (g * g))⁻¹ := by group
      _ = t := by rw [← this]; group
  have hone : ∀ a : G, g * a * g⁻¹ = 1 → a = 1 := fun a h => hinj a 1 (by rw [h]; group)
  rcases σ.mem_T_cases' hσ hxT with ha | ha | ha | ha
  · exact absurd (hone _ ha) hx1
  ·
    exfalso
    rcases σ.mem_T_cases' hσ hx₂T with hb | hb | hb | hb
    · exact hx₂1 (hone _ hb)
    · exact hne (hinj _ _ (by rw [ha, hb])).symm
    · apply h1
      rw [mem_centralizer_T_iff']
      constructor
      · calc σ.x * g = g * σ.x * g⁻¹ * g := by rw [ha]
          _ = g * σ.x := by group
      · calc σ.x₂ * g = g * σ.x₂ * g⁻¹ * g := by rw [hb]
          _ = g * σ.x₂ := by group
    · have e : g * (σ.x * σ.x₂) * g⁻¹ = σ.x₂ := by
        rw [hmul, ha, hb, ← mul_assoc, hxx, one_mul]
      have := hcube σ.x₂ σ.x₂_mem_T
      rw [hb, e, hb] at this
      apply hx1
      calc σ.x = σ.x * σ.x₂ * σ.x₂⁻¹ := by group
        _ = 1 := by rw [this, mul_inv_cancel]
  · exact Or.inl ha
  · rcases σ.mem_T_cases' hσ hx₂T with hb | hb | hb | hb
    · exact absurd (hone _ hb) hx₂1
    · right
      calc g ^ 2 * σ.x * (g ^ 2)⁻¹ = g * (g * σ.x * g⁻¹) * g⁻¹ := by rw [pow_two]; group
        _ = σ.x₂ := by
          rw [ha, hmul, ha, hb, mul_assoc, ← hcomm, ← mul_assoc, hxx, one_mul]
    · exfalso
      have e : g * (σ.x * σ.x₂) * g⁻¹ = σ.x := by
        rw [hmul, ha, hb, mul_assoc, hx₂x₂, mul_one]
      have := hcube σ.x σ.x_mem_T
      rw [ha, e, ha] at this
      apply hx₂1
      calc σ.x₂ = σ.x⁻¹ * (σ.x * σ.x₂) := by group
        _ = 1 := by rw [this, inv_mul_cancel]
    · exact absurd (hinj _ _ (by rw [ha, hb])) hne

variable {σ}

private theorem IV7Data.isPGroup_Q {r : ℕ} (d : σ.IV7Data r) : IsPGroup r d.Q :=
  d.P_sylow.isPGroup.to_le d.Q_le

private theorem IV7Data.D_le_normalizer_Q {r : ℕ} (d : σ.IV7Data r) :
    σ.D ≤ Subgroup.normalizer (d.Q : Set G) :=
  d.P_D.trans (normalizer_le_normalizer_of_characteristic d.Q_le d.Q_characteristic)

private theorem IV7Data.Cstar_le_C {r : ℕ} (d : σ.IV7Data r) : d.Cstar ≤ σ.C :=
  inf_le_left.trans inf_le_left

private theorem IV7Data.Cstar_le_Nstar {r : ℕ} (d : σ.IV7Data r) : d.Cstar ≤ d.Nstar :=
  inf_le_left.trans inf_le_right

private theorem IV7Data.Cstar_le_normalizer_Q {r : ℕ} (d : σ.IV7Data r) :
    d.Cstar ≤ Subgroup.normalizer (d.Q : Set G) :=
  inf_le_right

private theorem IV7Data.Q_le_Qstar {r : ℕ} (d : σ.IV7Data r) : d.Q ≤ d.Qstar :=
  le_sup_left

private theorem IV7Data.Qstar_le_normalizer_Q {r : ℕ} (d : σ.IV7Data r) :
    d.Qstar ≤ Subgroup.normalizer (d.Q : Set G) :=
  sup_le Subgroup.le_normalizer (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))

private theorem IV7Data.isPGroup_Qstar {r : ℕ} (d : σ.IV7Data r) : IsPGroup r d.Qstar := by
  apply IsPGroup.to_sup_of_normal_right' d.isPGroup_Q
    (d.Rstar_sylow.isPGroup.to_le inf_le_left)
  exact (le_inf d.Rstar_Q (Subgroup.le_normalizer.trans
    (normalizer_le_normalizer_centralizer' d.Q))).trans Subgroup.inf_normalizer_le_normalizer_inf

private theorem IV7Data.D_le_normalizer_Qstar {r : ℕ} (d : σ.IV7Data r) :
    σ.D ≤ Subgroup.normalizer (d.Qstar : Set G) :=
  (le_inf d.D_le_normalizer_Q ((le_inf d.Rstar_D (d.D_le_normalizer_Q.trans
    (normalizer_le_normalizer_centralizer' d.Q))).trans
      Subgroup.inf_normalizer_le_normalizer_inf)).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

private theorem IV7Data.T_le_Cstar (hσ : σ.IsValid) {r : ℕ} (d : σ.IV7Data r) :
    σ.T ≤ d.Cstar :=
  le_inf (le_inf (σ.T_le_C hσ) ((σ.T_le_D hσ).trans d.D_le_Nstar))
    ((σ.T_le_D hσ).trans d.D_le_normalizer_Q)

private theorem IV7Data.Cstar_inf_pPrimeCore_le_pPrimePCoreIn {r : ℕ} (hr : r.Prime)
    (d : σ.IV7Data r) {K : Subgroup G} (hK : d.Qstar ≤ K) :
    d.Cstar ⊓ pPrimeCoreIn r K ≤ pPrimePCoreIn r d.Nstar := by
  have : Fact r.Prime := ⟨hr⟩
  set O := pPrimeCoreIn r K with hO
  have hOcop : Nat.Coprime r (Nat.card O) := by
    rw [hO, pPrimeCoreIn, Subgroup.card_map_of_injective K.subtype_injective]
    exact pPrimeCore_coprime_card
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_map_subtype K _
  set X := d.Cstar ⊓ O with hX
  apply le_pPrimePCoreIn_of_thompson (Q := d.Q) (M := O)
    d.Nstar_constrained.2 d.Rstar_sylow d.isPGroup_Q
    d.Q_le_Nstar d.Rstar_Q (inf_le_left.trans d.Cstar_le_Nstar)
    (hOcop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right))
  ·
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 : x * q * x⁻¹ * q⁻¹ ∈ O := commutator_mem_left hKO hx.2 (hK (d.Q_le_Qstar hq))
    have h2 : x * q * x⁻¹ * q⁻¹ ∈ d.Q := commutator_mem_right d.Cstar_le_normalizer_Q hx.1 hq
    have h3 : x * q * x⁻¹ * q⁻¹ ∈ d.Q ⊓ O := ⟨h2, h1⟩
    rw [inf_eq_bot_of_isPGroup d.isPGroup_Q hOcop, Subgroup.mem_bot] at h3
    calc q * x = x * q * x⁻¹ * q⁻¹ * (q * x) := by rw [h3, one_mul]
      _ = x * q := by group
  · exact hOcop
  · intro x hx y hy
    exact commutator_mem_left hKO hx.2 (hK (le_sup_right (a := d.Q) hy))

variable (σ) in
theorem IV7Data.Cstar_inf_pPrimeCore_le (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) (d : σ.IV7Data r) {K : Subgroup G} (hK : d.Qstar ≤ K) :
    d.Cstar ⊓ pPrimeCoreIn r K ≤ solvRadIn σ.L := by
  have h1 := d.Cstar_inf_pPrimeCore_le_pPrimePCoreIn hr.prime hK
  have h2 : pPrimePCoreIn r d.Nstar ≤ solvRadIn d.Nstar :=
    Subgroup.map_mono d.Nstar_constrained.1
  have : (CFSG.solvableRadical d.Nstar).Normal := solvableRadical_normal
  have h3 : σ.N ⊓ solvRadIn d.Nstar ≤ solvRadIn σ.N := by
    refine σ.le_solvRadIn_N_of_cover hσ hII.toNStructure (K := d.Nstar ⊓ σ.N) inf_le_left
      (isSolvable_of_le inf_le_right (isSolvable_solvRadIn _)) inf_le_right ?_ ?_
    · rw [inf_comm]
      exact (inf_le_inf Subgroup.le_normalizer (le_normalizer_map_subtype d.Nstar _)).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    · exact fun l hl => subset_inf_mul_of_subset_mul (σ.L_le_N' hσ) σ.ON_le_N d.Nstar_covers
        (σ.L₀_le_L' hl)
  rw [σ.solvRadIn_L_eq hσ hII.toNStructure]
  intro x hx
  exact h3 ⟨σ.C_le_N (d.Cstar_le_C hx.1), h2 (h1 hx)⟩

private theorem IV7Data.automizerIndex_normalizer_Q (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : r.Prime) (d : σ.IV7Data r) :
    automizerIndex (σ.T.subgroupOf (Subgroup.normalizer (d.Q : Set G))) = 6 := by
  have : Fact r.Prime := ⟨hr⟩
  rw [← hII.automizer_T]
  apply automizerIndex_subgroupOf_eq_of_forall ((σ.T_le_D hσ).trans d.D_le_normalizer_Q)
  intro m hm
  obtain ⟨c, hc, hcm⟩ := exists_mem_mul_normalizer_of_isSylowOf d.P_sylow
    (normalizer_le_normalizer_centralizer' σ.T hm)
  exact ⟨c, hc, normalizer_le_normalizer_of_characteristic d.Q_le d.Q_characteristic hcm⟩

variable (σ) in
theorem lemmaIV81 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) : σ.LemmaIV81 := by
  intro r hr d
  refine ⟨⟨d.Q, d.Q_ne_bot, d.isPGroup_Q, rfl⟩, d.D_le_normalizer_Q, d.Qstar_le_normalizer_Q,
    d.automizerIndex_normalizer_Q hσ hII hr.prime, ?_,
    IV7Data.Cstar_inf_pPrimeCore_le σ hσ hII hr d d.Qstar_le_normalizer_Q⟩
  intro u hu
  exact ⟨u, ⟨hu.1, d.Cstar_le_normalizer_Q hu.1⟩, 1, Subgroup.one_mem _, mul_one u⟩

private theorem centerOf_D_le_C (hσ : σ.IsValid) : centerOf σ.D ≤ σ.C :=
  inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (σ.T_le_D hσ)))

private theorem centerOf_S_le_normalizer_ON (hσ : σ.IsValid) :
    centerOf (σ.S : Subgroup G) ≤ Subgroup.normalizer (σ.ON : Set G) :=
  (inf_le_left.trans (σ.S_le_N hσ)).trans σ.N_le_normalizer_ON

private theorem mem_centerOf_S_of_mem_solvRadIn_N (hσ : σ.IsValid) (hII : σ.NStructure)
    {t : G} (htS : t ∈ (σ.S : Subgroup G)) (ht : t ∈ solvRadIn σ.N) :
    t ∈ centerOf (σ.S : Subgroup G) := by
  rw [hII.N_solvRad, sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (σ.centerOf_S_le_normalizer_ON hσ)] at ht
  obtain ⟨z, hz, o, ho, hzo⟩ := ht
  dsimp only at hzo
  have ho1 : o = 1 := by
    have : o = z⁻¹ * t := by rw [← hzo]; group
    exact eq_one_of_mem_of_mem_odd' σ.S.isPGroup' σ.odd_card_ON
      (this ▸ (σ.S : Subgroup G).mul_mem ((σ.S : Subgroup G).inv_mem hz.1) htS) ho
  rw [ho1, mul_one] at hzo
  exact hzo ▸ hz

private theorem eq_x_of_mem_T_of_mem_solvRadIn_N (hσ : σ.IsValid) (hII : σ.NStructure)
    {t : G} (htT : t ∈ σ.T) (ht : t ∈ solvRadIn σ.N) (ht1 : t ≠ 1) : t = σ.x := by
  have ht2 : t ^ 2 = 1 := by
    rw [pow_two]
    rcases σ.mem_T_cases' hσ htT with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact σ.x_mul_x' hσ
    · exact σ.x₂_mul_x₂' hσ
    · calc σ.x * σ.x₂ * (σ.x * σ.x₂) = σ.x * (σ.x₂ * σ.x) * σ.x₂ := by simp only [mul_assoc]
        _ = σ.x * (σ.x * σ.x₂) * σ.x₂ := by rw [hσ.commute]
        _ = 1 := by rw [← mul_assoc, σ.x_mul_x' hσ, one_mul, σ.x₂_mul_x₂' hσ]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hσ.center_involution t
    (σ.mem_centerOf_S_of_mem_solvRadIn_N hσ hII ((σ.T_le_S hσ) htT) ht)
    (orderOf_eq_prime ht2 ht1)

private theorem x₂_not_mem_solvRadIn_N (hσ : σ.IsValid) (hII : σ.NStructure) :
    σ.x₂ ∉ solvRadIn σ.N := fun h =>
  hσ.x_ne_x₂ (σ.eq_x_of_mem_T_of_mem_solvRadIn_N hσ hII σ.x₂_mem_T h (σ.x₂_ne_one' hσ)).symm

private theorem mem_T_of_mem_centerOf (hσ : σ.IsValid) (hII : σ.NStructure)
    {S₁ : Subgroup G} (hS₁ : IsPGroup 2 S₁) (hDS₁ : σ.D ≤ S₁) {w : G}
    (hw : w ∈ centerOf S₁) (hw2 : w ^ 2 = 1) : w ∈ σ.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx₂S₁ : σ.x₂ ∈ S₁ := hDS₁ ((σ.T_le_D hσ) σ.x₂_mem_T)
  rcases hσ.sylow with ⟨-, n, hn, hiso⟩ | hW
  · obtain ⟨S₂, hS₁₂⟩ := hS₁.exists_le_sylow
    obtain ⟨f⟩ := hiso S₂
    set z' : S₂ := f (CFSG.Semidihedral.r n) ^ (2 ^ (n - 1) / 2) with hz'
    have hz'c : z' ∈ Subgroup.center S₂ := CFSG.Semidihedral.Local.image_z_mem_center hn f
    have hz'o : orderOf z' = 2 := CFSG.Semidihedral.Local.image_z_orderOf (by omega) f
    obtain ⟨-, hcent⟩ := hII.center_involution_of_sylow S₂ (hDS₁.trans hS₁₂)
    have hcenter : ∀ y : S₂, y ∈ Subgroup.center S₂ → (y : G) ∈ centerOf (S₂ : Subgroup G) := by
      intro y hy
      refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)
    have hz'x : ((z' : S₂) : G) = σ.x := by
      apply hcent _ (hcenter z' hz'c)
      rw [Subgroup.orderOf_coe]
      exact hz'o
    set x₂' : S₂ := ⟨σ.x₂, hS₁₂ hx₂S₁⟩
    have hx₂'o : orderOf x₂' = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hσ.x₂_order
    have hx₂'z : x₂' ∉ Subgroup.zpowers z' := by
      intro hmem
      have hc : x₂' ∈ Subgroup.center S₂ := (Subgroup.zpowers_le.mpr hz'c) hmem
      exact hσ.x_ne_x₂ (hcent σ.x₂ (hcenter x₂' hc) hσ.x₂_order).symm
    obtain ⟨hC, -⟩ := CFSG.Semidihedral.Local.centralizer_eq_closure hn f x₂' hx₂'o hx₂'z
    set w' : S₂ := ⟨w, hS₁₂ hw.1⟩
    have hw'C : w' ∈ Subgroup.centralizer {x₂'} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hw.2) σ.x₂ hx₂S₁).symm
    rw [hC] at hw'C
    have hle : Subgroup.closure {z', x₂'} ≤ σ.T.comap (S₂ : Subgroup G).subtype := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · change ((z' : S₂) : G) ∈ σ.T
        rw [hz'x]
        exact σ.x_mem_T
      · exact σ.x₂_mem_T
    exact hle hw'C
  · have hh : σ.height ≠ 1 := by
      have := hW.1
      omega
    have hDS : σ.D = σ.S := le_antisymm σ.D_le_S (le_inf le_rfl (hσ.T_normal hh))
    have hS₁S : S₁ = σ.S := σ.S.is_maximal' hS₁ (hDS ▸ hDS₁)
    by_cases hw1 : w = 1
    · rw [hw1]
      exact σ.T.one_mem
    rw [hσ.center_involution w (hS₁S ▸ hw) (orderOf_eq_prime hw2 hw1)]
    exact σ.x_mem_T

private theorem IV7Data.C_inf_L_subset_of_mem_familyM (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (d : σ.IV7Data r) {H : Subgroup G} (hH : H ∈ d.familyM) :
    ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆ (H : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G) := by
  obtain ⟨-, hDH, -, -, hcov, -⟩ := hH
  intro u hu
  obtain ⟨c, hc, s, hs, hcsu⟩ := d.Cstar_covers hu
  dsimp only at hcsu
  have hcL : c ∈ σ.L := by
    have : c = u * s⁻¹ := by rw [← hcsu]; group
    rw [this]
    exact σ.L.mul_mem hu.2 (σ.L.inv_mem (solvRadIn_le σ.L hs.2))
  obtain ⟨h, hh, s', hs', hcs⟩ := hcov ⟨hc, hcL⟩
  dsimp only at hcs
  have hss : s' * s ∈ solvRadIn σ.L := (solvRadIn σ.L).mul_mem hs'.2 hs.2
  rw [σ.solvRadIn_L_eq hσ hII.toNStructure, hII.N_solvRad, sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ (σ.centerOf_S_le_normalizer_ON hσ)] at hss
  obtain ⟨z, hz, o, ho, hzo⟩ := hss
  dsimp only at hzo
  rw [hII.center_S_eq_center_D] at hz
  refine ⟨h * z, H.mul_mem hh.2 (hDH hz.1), o, ⟨?_, ho⟩, ?_⟩
  · have : o = z⁻¹ * (s' * s) := by rw [← hzo]; group
    rw [this]
    exact σ.C.mul_mem (σ.C.inv_mem (σ.centerOf_D_le_C hσ hz))
      (σ.C.mul_mem (d.Cstar_le_C hs'.1) hs.1)
  · change h * z * o = u
    rw [← hcsu, ← hcs, mul_assoc h z o, hzo, mul_assoc]

private theorem IV7Data.isDGroupWrt_of_mem_familyM (hσ : σ.IsValid) (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r) {H : Subgroup G} (hH : H ∈ d.familyM) :
    IsDGroupWrt (σ.T.subgroupOf H) := by
  have hcov := d.C_inf_L_subset_of_mem_familyM hσ hII hH
  obtain ⟨hloc, hDH, -, haut, -, -⟩ := hH
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hDH
  have hO : oddCoreIn H ≠ ⊥ := oddCoreIn_ne_bot_of_isPLocal hr.prime
    (σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON) hloc
  rcases hII.qd_or_d_of_three H hTH (Or.inl hDH) (by rw [haut]; norm_num) with h | h
  · exact absurd h (hII.not_qd_of_cover H hTH hO hcov)
  · exact h

private theorem IV7Data.odd_card_pPrimeCoreIn_of_mem_familyM (hσ : σ.IsValid)
    (hII : σ.ChapterIIFacts)
    {r : ℕ} (hr : σ.HypIV7 r) (d : σ.IV7Data r) {H : Subgroup G} (hH : H ∈ d.familyM) :
    Odd (Nat.card (pPrimeCoreIn r H)) := by
  have : Fact r.Prime := ⟨hr.prime⟩
  obtain ⟨-, hDH, -, haut, -, hdH⟩ := hH
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hDH
  have hcard : Nat.card (pPrimeCoreIn r H) = Nat.card (CFSG.pPrimeCore r H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  rw [hcard, Nat.odd_iff]
  by_contra hodd
  have heven : 2 ∣ Nat.card (CFSG.pPrimeCore r H) := Nat.dvd_of_mod_eq_zero (by omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD2 : IsPGroup 2 (σ.D.subgroupOf H) :=
    (σ.S.isPGroup'.to_le σ.D_le_S).comap_subtype
  obtain ⟨S₁, hS₁⟩ := hD2.exists_le_sylow
  obtain ⟨w, hwZ, hw1, hw2, hwO⟩ := exists_central_involution_of_even (S := S₁)
    (L := CFSG.pPrimeCore r H) heven
  have hwZ' : ((w : H) : G) ∈ centerOf ((S₁ : Subgroup H).map H.subtype) := by
    refine ⟨⟨(w : H), w.2, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have h1 := Subgroup.mem_center_iff.mp hwZ ⟨y, hy⟩
    have h2 := congrArg (fun a : (S₁ : Subgroup H) => ((a : H) : G)) h1
    simpa using h2
  have hwT : ((w : H) : G) ∈ σ.T := by
    refine σ.mem_T_of_mem_centerOf hσ hII.toNStructure (S₁.isPGroup'.map H.subtype)
      (fun y hy => ⟨⟨y, hDH hy⟩, hS₁ hy, rfl⟩) hwZ' ?_
    have h2 := congrArg (fun a : (S₁ : Subgroup H) => ((a : H) : G)) hw2
    simpa using h2
  have hw'x : ((w : H) : G) = σ.x := by
    have hmem := hdH ⟨d.T_le_Cstar hσ hwT, ⟨(w : H), hwO, rfl⟩⟩
    rw [σ.solvRadIn_L_eq hσ hII.toNStructure] at hmem
    refine σ.eq_x_of_mem_T_of_mem_solvRadIn_N hσ hII.toNStructure hwT hmem fun h1 => hw1 ?_
    apply Subtype.ext
    apply Subtype.ext
    simpa using h1
  set O := pPrimeCoreIn r H with hO
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := le_normalizer_map_subtype H _
  have hxO : σ.x ∈ O := ⟨(w : H), hwO, hw'x⟩
  obtain ⟨g, hgH, hgN, hg3, hg1⟩ :=
    exists_of_three_dvd_automizerIndex' hTH (by rw [haut]; norm_num)
  have hx₂O : σ.x₂ ∈ O := by
    rcases σ.conj_x_eq_x₂_of_automizer hσ hgN hg3 hg1 with h | h
    · rw [← h]
      exact (Subgroup.mem_normalizer_iff.mp (hHO hgH) σ.x).mp hxO
    · rw [← h]
      exact (Subgroup.mem_normalizer_iff.mp (hHO (H.pow_mem hgH 2)) σ.x).mp hxO
  have hmem := hdH ⟨d.T_le_Cstar hσ σ.x₂_mem_T, hx₂O⟩
  rw [σ.solvRadIn_L_eq hσ hII.toNStructure] at hmem
  exact σ.x₂_not_mem_solvRadIn_N hσ hII.toNStructure hmem

variable (σ) in
theorem lemmaIV83 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) : σ.LemmaIV83 := by
  intro r hr d H hH
  have hodd := d.odd_card_pPrimeCoreIn_of_mem_familyM hσ hII hr hH
  refine ⟨d.isDGroupWrt_of_mem_familyM hσ hII hr hH, hodd, fun y hy => ?_⟩
  have hyS := hH.2.2.2.2.2 hy
  rw [σ.solvRadIn_L_eq hσ hII.toNStructure, hII.N_solvRad] at hyS
  exact mem_of_mem_sup_of_odd_orderOf (σ.centerOf_S_le_normalizer_ON hσ)
    (σ.S.isPGroup'.to_le inf_le_left) σ.odd_card_ON hyS
    (hodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hy.2))

variable (σ) in
theorem familyM_subset_familyMstar (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {r : ℕ}
    (hr : σ.HypIV7 r) (d : σ.IV7Data r) : d.familyM ⊆ σ.familyMstar r := by
  intro K hK
  exact ⟨hK.1, hK.2.1, d.isDGroupWrt_of_mem_familyM hσ hII hr hK,
    d.odd_card_pPrimeCoreIn_of_mem_familyM hσ hII hr hK⟩

private theorem IV7Data.R_le_Rstar {r : ℕ} (hr : r.Prime) (d : σ.IV7Data r)
    (hN : d.Nstar = Subgroup.normalizer (d.R : Set G)) : d.R ≤ d.Rstar := by
  have : Fact r.Prime := ⟨hr⟩
  have hRp : IsPGroup r d.R := d.R_sylow.isPGroup
  have hRN : d.R ≤ d.Nstar := hN ▸ Subgroup.le_normalizer
  have hRE : d.R ≤ pPrimePCoreIn r d.Nstar := by
    have hnormal : (d.R.subgroupOf d.Nstar).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hRN).mpr ?_
      rw [hN]
    have hle : d.R.subgroupOf d.Nstar ≤ Op_p'p r d.Nstar := by
      apply le_Op_p'p_of_normal hnormal
      intro x hx
      obtain ⟨k, hk⟩ := (hRp.comap_subtype (K := d.Nstar)) ⟨x, hx⟩
      refine ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [this]
      exact Subgroup.one_mem _
    intro y hy
    exact ⟨⟨y, hRN hy⟩, hle hy, rfl⟩
  have hRsR : d.Rstar ≤ Subgroup.normalizer (d.R : Set G) :=
    hN ▸ (d.Rstar_sylow.le.trans (pPrimePCoreIn_le r d.Nstar))
  have hsup : d.Rstar ⊔ d.R = d.Rstar :=
    d.Rstar_sylow.eq_of_le le_sup_left (sup_le d.Rstar_sylow.le hRE)
      (IsPGroup.to_sup_of_normal_right' d.Rstar_sylow.isPGroup hRp hRsR)
  exact le_sup_right.trans hsup.le

private theorem IV7Data.exists_Qtilde {r : ℕ} (hr : r.Prime) (d : σ.IV7Data r) :
    ∃ Qt : Subgroup G, IsPGroup r Qt ∧ Qt ≤ d.Qstar ∧
      d.Cstar ≤ Subgroup.normalizer (Qt : Set G) ∧ σ.D ≤ Subgroup.normalizer (Qt : Set G) ∧
      ∀ z ∈ σ.C, z ∈ Subgroup.centralizer (Qt : Set G) → z ∈ d.Cstar := by
  rcases d.cases with h1 | ⟨-, hN, hQR⟩
  · refine ⟨d.Q, d.isPGroup_Q, d.Q_le_Qstar, d.Cstar_le_normalizer_Q, d.D_le_normalizer_Q,
      fun z hz hzQ => ?_⟩
    change z ∈ σ.C ⊓ d.Nstar ⊓ Subgroup.normalizer (d.Q : Set G)
    rw [h1]
    exact ⟨hz, Subgroup.centralizer_le_normalizer _ hzQ⟩
  · have hRp : IsPGroup r d.R := d.R_sylow.isPGroup
    have hRQ : d.R ≤ Subgroup.centralizer (d.Q : Set G) := Subgroup.le_centralizer_iff.mp hQR
    refine ⟨d.Q ⊔ d.R, IsPGroup.to_sup_of_normal_right' d.isPGroup_Q hRp
      (hQR.trans (Subgroup.centralizer_le_normalizer _)), ?_, ?_, ?_, fun z hz hzQR => ?_⟩
    · exact sup_le d.Q_le_Qstar (le_sup_of_le_right (le_inf (d.R_le_Rstar hr hN) hRQ))
    · exact (le_inf d.Cstar_le_normalizer_Q (hN ▸ d.Cstar_le_Nstar)).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact (le_inf d.D_le_normalizer_Q d.R_D).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · have hzQ : z ∈ Subgroup.centralizer (d.Q : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hzQR
      have hzR : z ∈ Subgroup.centralizer (d.R : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right) hzQR
      refine ⟨⟨hz, ?_⟩, Subgroup.centralizer_le_normalizer _ hzQ⟩
      rw [hN]
      exact Subgroup.centralizer_le_normalizer _ hzR

private theorem exists_mem_of_automizerIndex_eq {T H : Subgroup G} (hTH : T ≤ H)
    (h : automizerIndex (T.subgroupOf H) = automizerIndex T) :
    ∀ m ∈ Subgroup.normalizer (T : Set G), ∃ k ∈ Subgroup.normalizer (T : Set G) ⊓ H,
      k⁻¹ * m ∈ Subgroup.centralizer (T : Set G) := by
  set C := Subgroup.centralizer (T : Set G) with hC
  set M := Subgroup.normalizer (T : Set G) with hM
  have hCM : C ≤ M := Subgroup.centralizer_le_normalizer _
  have hMC : M ≤ Subgroup.normalizer (C : Set G) := normalizer_le_normalizer_centralizer' T
  set A : Subgroup G := (M ⊓ H) ⊔ C with hA
  have hCA : C ≤ A := le_sup_right
  have hAM : A ≤ M := sup_le inf_le_left hCM
  have h1 : C.relIndex A = C.relIndex M := by
    rw [hA, relIndex_sup_right_of_le_normalizer (inf_le_left.trans hMC)]
    rw [automizerIndex_subgroupOf_eq hTH, automizerIndex] at h
    exact h
  have h2 : A.relIndex M = 1 := by
    have := Subgroup.relIndex_mul_relIndex C A M hCA hAM
    rw [h1] at this
    exact (Nat.mul_eq_left (relIndex_ne_zero' C M)).mp this
  intro m hm
  have hmA : m ∈ (A : Set G) := Subgroup.relIndex_eq_one.mp h2 hm
  rw [hA, Subgroup.coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans hMC)] at hmA
  obtain ⟨k, hk, c, hc, rfl⟩ := hmA
  refine ⟨k, hk, ?_⟩
  simpa using hc

variable (σ) in
theorem propIV81 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) :
    ∀ r : ℕ, σ.HypIV7 r → ∀ d : σ.IV7Data r, ∀ H ∈ d.familyM, ∀ R₁ : Subgroup G, R₁ ≠ ⊥ →
      IsPGroup r R₁ → R₁ ≤ H → σ.D ≤ Subgroup.normalizer (R₁ : Set G) →
      d.Qstar ≤ Subgroup.normalizer (R₁ : Set G) →
      H ≤ Subgroup.normalizer ((pPrimeCoreIn r H ⊔ R₁ : Subgroup G) : Set G) →
        Subgroup.normalizer (R₁ : Set G) ∈ d.familyM := by
  intro r hr d H hH R₁ hR₁ hR₁p hR₁H hDR hQR hHR
  have : Fact r.Prime := ⟨hr.prime⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  have hodd := d.odd_card_pPrimeCoreIn_of_mem_familyM hσ hII hr hH
  obtain ⟨-, hDH, hQH, haut, hcov, hdH⟩ := hH
  set O := pPrimeCoreIn r H with hO
  have hOH : O ≤ H := pPrimeCoreIn_le r H
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := le_normalizer_map_subtype H _
  have hOr : Nat.Coprime r (Nat.card O) := by
    rw [hO, pPrimeCoreIn, Subgroup.card_map_of_injective H.subtype_injective]
    exact pPrimeCore_coprime_card
  have hTH : σ.T ≤ H := (σ.T_le_D hσ).trans hDH
  have hT2 : IsPGroup 2 σ.T := σ.S.isPGroup'.to_le (σ.T_le_S hσ)
  have hTR : σ.T ≤ Subgroup.normalizer (R₁ : Set G) := (σ.T_le_D hσ).trans hDR
  refine ⟨⟨R₁, hR₁, hR₁p, rfl⟩, hDR, hQR, ?_, ?_, IV7Data.Cstar_inf_pPrimeCore_le σ hσ hII hr d hQR⟩
  ·
    rw [← hII.automizer_T]
    apply automizerIndex_subgroupOf_eq_of_forall hTR
    have hK : Odd (Nat.card (O ⊔ R₁ : Subgroup G)) :=
      odd_card_sup_of_le_normalizer_of_odd (hR₁H.trans hHO) hodd
        (odd_card_of_isPGroup' hr.prime hr2 hR₁p)
    have hR₁K : IsSylowOf r R₁ (O ⊔ R₁) := isSylowOf_sup_of_coprime' (hR₁H.trans hHO) hOr hR₁p
    have step : ∀ h ∈ Subgroup.normalizer (σ.T : Set G) ⊓ H,
        ∃ c ∈ Subgroup.centralizer (σ.T : Set G), c⁻¹ * h ∈ Subgroup.normalizer (R₁ : Set G) := by
      rintro h ⟨hhT, hhH⟩
      have hR₂ : IsSylowOf r (R₁.map (MulAut.conj h).toMonoidHom) (O ⊔ R₁) := by
        apply isSylowOf_of_card
        · rw [← map_conj_eq_of_mem_normalizer (hHR hhH)]
          exact Subgroup.map_mono hR₁K.le
        · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]
          exact hR₁K.card_eq
      have hTR₂ : σ.T ≤ Subgroup.normalizer
          ((R₁.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) := by
        intro t ht
        apply mem_normalizer_of_conj_mem
        rintro _ ⟨y, hy, rfl⟩
        have ht' : h⁻¹ * t * h ∈ σ.T := by
          have := (Subgroup.mem_normalizer_iff.mp
            ((Subgroup.normalizer (σ.T : Set G)).inv_mem hhT) t).mp ht
          simpa using this
        have hy' := (Subgroup.mem_normalizer_iff.mp (hTR ht') y).mp hy
        refine ⟨_, hy', ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      obtain ⟨c, ⟨-, hcT⟩, hc⟩ := exists_conj_eq_of_isSylowOf_normalized_of_odd hr.prime hT2
        (hTH.trans hHR) hK hR₁K hR₂ hTR hTR₂
      refine ⟨c, hcT, mem_normalizer_of_conj_mem fun y hy => ?_⟩
      have hy' : h * y * h⁻¹ ∈ R₁.map (MulAut.conj c).toMonoidHom := by
        rw [hc]
        exact ⟨y, hy, rfl⟩
      obtain ⟨y', hy'R, hy'e⟩ := hy'
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hy'e
      have : c⁻¹ * h * y * (c⁻¹ * h)⁻¹ = y' := by
        calc c⁻¹ * h * y * (c⁻¹ * h)⁻¹ = c⁻¹ * (h * y * h⁻¹) * c := by group
          _ = y' := by rw [← hy'e]; group
      rw [this]
      exact hy'R
    intro m hm
    obtain ⟨k, hk, hkm⟩ := exists_mem_of_automizerIndex_eq hTH
      (by rw [haut, hII.automizer_T]) m hm
    obtain ⟨c, hc, hck⟩ := step k hk
    have hc' : c⁻¹ * k ∈ Subgroup.normalizer (σ.T : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hc)) hk.1
    have hconj : (c⁻¹ * k) * (k⁻¹ * m) * (c⁻¹ * k)⁻¹ ∈ Subgroup.centralizer (σ.T : Set G) :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer' σ.T hc') _).mp hkm
    refine ⟨c * ((c⁻¹ * k) * (k⁻¹ * m) * (c⁻¹ * k)⁻¹), Subgroup.mul_mem _ hc hconj, ?_⟩
    have : (c * ((c⁻¹ * k) * (k⁻¹ * m) * (c⁻¹ * k)⁻¹))⁻¹ * m = c⁻¹ * k := by group
    rw [this]
    exact hck
  ·
    obtain ⟨Qt, hQtp, hQtQ, hCQt, hDQt, hCstar⟩ := d.exists_Qtilde hr.prime
    intro u hu
    obtain ⟨h, hh, s, hs, rfl⟩ := hcov hu
    obtain ⟨z, hzO, hzQ, hzT, hzh⟩ := exists_mem_mul_mem_normalizer hOH hHO hodd hOr hR₁p hR₁H
      hHR hQtp (hQtQ.trans hQH) (hQtQ.trans hQR) hT2 hTH hTR ((σ.T_le_D hσ).trans hDQt)
      hh.2 (hCQt hh.1) (d.Cstar_le_C hh.1)
    have hzC : z ∈ d.Cstar := hCstar z hzT hzQ
    set k := z * h with hk
    have hkC : k ∈ d.Cstar := d.Cstar.mul_mem hzC hh.1
    have hkH : k ∈ H := H.mul_mem (hOH hzO) hh.2
    have hs' : k⁻¹ * z⁻¹ * k ∈ d.Cstar ⊓ O :=
      ⟨d.Cstar.mul_mem (d.Cstar.mul_mem (d.Cstar.inv_mem hkC) (d.Cstar.inv_mem hzC)) hkC, by
        have := (Subgroup.mem_normalizer_iff.mp (hHO (H.inv_mem hkH)) z⁻¹).mp (O.inv_mem hzO)
        simpa using this⟩
    refine ⟨k, ⟨hkC, hzh⟩, (k⁻¹ * z⁻¹ * k) * s,
      ⟨d.Cstar.mul_mem hs'.1 hs.1, (solvRadIn σ.L).mul_mem (hdH hs') hs.2⟩, ?_⟩
    simp only [hk]
    group

variable (σ) in
theorem corIV81 (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) : σ.CorIV81 := by
  intro r hr d H hH P₁ hP₁ hHZ
  have : Fact r.Prime := ⟨hr.prime⟩
  have hr2 : r ≠ 2 := σ.prime_ne_two_of_dvd_ON hr.prime hr.dvd_ON
  have hodd := d.odd_card_pPrimeCoreIn_of_mem_familyM hσ hII hr hH
  have hDH : σ.D ≤ H := hH.2.1
  have hQH : d.Qstar ≤ H := hH.2.2.1
  set O := pPrimeCoreIn r H with hO
  have hOH : O ≤ H := pPrimeCoreIn_le r H
  have hHO : H ≤ Subgroup.normalizer (O : Set G) := le_normalizer_map_subtype H _
  have hOr : Nat.Coprime r (Nat.card O) := by
    rw [hO, pPrimeCoreIn, Subgroup.card_map_of_injective H.subtype_injective]
    exact pPrimeCore_coprime_card
  set Z := CFSG.thompsonCenter P₁ with hZ
  have hP₁H : P₁ ≤ H := hP₁.le
  have hZP₁ : Z ≤ P₁ := thompsonCenter_le_self P₁
  have hZp : IsPGroup r Z := hP₁.isPGroup.to_le hZP₁
  set E := O ⊔ Z with hE
  have hZO : Z ≤ Subgroup.normalizer (O : Set G) := (hZP₁.trans hP₁H).trans hHO
  have hEsyl : IsSylowOf r Z E := isSylowOf_sup_of_coprime' hZO hOr hZp
  obtain ⟨S', hS'⟩ := (d.isPGroup_Qstar.comap_subtype (K := H)).exists_le_sylow
  have hP' : IsSylowOf r ((S' : Subgroup H).map H.subtype) H := ⟨S', rfl⟩
  obtain ⟨h, hhH, hconj⟩ := hP₁.exists_mem_conj hP'
  have hP'eq : (S' : Subgroup H).map H.subtype = P₁.map (MulAut.conj h).toMonoidHom := by
    ext y
    rw [hconj, mem_map_conj_iff]
  have hQP' : d.Qstar ≤ P₁.map (MulAut.conj h).toMonoidHom := by
    rw [← hP'eq]
    intro y hy
    exact ⟨⟨y, hQH hy⟩, hS' hy, rfl⟩
  set Z' := Z.map (MulAut.conj h).toMonoidHom with hZ'
  have hZ'eq : CFSG.thompsonCenter (P₁.map (MulAut.conj h).toMonoidHom) = Z' :=
    (thompsonCenter_map_conj P₁ h).symm
  have hQZ' : d.Qstar ≤ Subgroup.normalizer (Z' : Set G) := by
    rw [← hZ'eq]
    exact (hQP'.trans Subgroup.le_normalizer).trans
      (CFSG.normalizer_le_normalizer_thompsonCenter _)
  have hZ'p : IsPGroup r Z' := hZp.map _
  have hZ'H : Z' ≤ H := by
    rw [hZ', ← map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hhH)]
    exact Subgroup.map_mono (hZP₁.trans hP₁H)
  have hEm : ∀ g ∈ H, E.map (MulAut.conj g).toMonoidHom = E := fun g hg =>
    map_conj_eq_of_mem_normalizer (hHZ hg)
  have hZ'E : Z' ≤ E := by
    rw [← hEm h hhH]
    exact Subgroup.map_mono le_sup_right
  set V := d.Qstar ⊔ Z' with hV
  have hVp : IsPGroup r V := IsPGroup.to_sup_of_normal_right' d.isPGroup_Qstar hZ'p hQZ'
  have hVH : V ≤ H := sup_le hQH hZ'H
  have hVO : V ≤ Subgroup.normalizer (O : Set G) := hVH.trans hHO
  set K := O ⊔ V with hK
  have hKsyl : IsSylowOf r V K := isSylowOf_sup_of_coprime' hVO hOr hVp
  have hKodd : Odd (Nat.card K) :=
    odd_card_sup_of_le_normalizer_of_odd hVO hodd (odd_card_of_isPGroup' hr.prime hr2 hVp)
  have hcardE : ∀ Y : Subgroup G, Y ≤ E → Y ≤ Subgroup.normalizer (O : Set G) →
      Nat.card Y = Nat.card Z → O ⊔ Y = E := by
    intro Y hYE hYO hYZ
    have hYp : IsPGroup r Y := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZp
      exact IsPGroup.of_card (hYZ.trans hn)
    apply Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hYE)
    rw [card_sup_of_coprime' hYO hOr hYp, card_sup_of_coprime' hZO hOr hZp, hYZ]
  have hcardZ' : Nat.card Z' = Nat.card Z :=
    Subgroup.card_map_of_injective (MulAut.conj h).injective
  have hOZ' : O ⊔ Z' = E := hcardE Z' hZ'E (hZ'H.trans hHO) hcardZ'
  have hKeq : K = E ⊔ d.Qstar := by
    rw [hK, hV, ← hOZ', sup_comm d.Qstar Z', sup_assoc]
  have hDK : σ.D ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact (le_inf (hDH.trans hHZ) d.D_le_normalizer_Qstar).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  obtain ⟨R₂, hR₂, hQR₂, hDR₂⟩ := exists_isSylowOf_normalized_ge_of_odd hr.prime
    (σ.S.isPGroup'.to_le σ.D_le_S) hDK hKodd ((le_sup_left : d.Qstar ≤ V).trans le_sup_right)
    d.isPGroup_Qstar d.D_le_normalizer_Qstar
  obtain ⟨k, hkK, hkconj⟩ := hKsyl.exists_mem_conj hR₂
  set g := k * h with hg
  have hgH : g ∈ H := H.mul_mem (sup_le hOH hVH hkK) hhH
  set P₂ := P₁.map (MulAut.conj g).toMonoidHom with hP₂
  have hP₂syl : IsSylowOf r P₂ H := isSylowOf_map_conj hP₁ (Subgroup.le_normalizer hgH)
  set R₃ := CFSG.thompsonCenter P₂ with hR₃
  have hR₃eq : R₃ = Z.map (MulAut.conj g).toMonoidHom := (thompsonCenter_map_conj P₁ g).symm
  have hR₃E : R₃ ≤ E := by
    rw [hR₃eq, ← hEm g hgH]
    exact Subgroup.map_mono le_sup_right
  have hR₃R₂ : R₃ ≤ R₂ := by
    intro y hy
    rw [hR₃eq, mem_map_conj_iff] at hy
    rw [hkconj]
    apply (le_sup_right : Z' ≤ V)
    rw [hZ', mem_map_conj_iff]
    convert hy using 1
    rw [hg]
    group
  have hcardR₃ : Nat.card R₃ = Nat.card Z := by
    rw [hR₃eq]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hR₃syl : IsSylowOf r R₃ E := isSylowOf_of_card hR₃E (hcardR₃.trans hEsyl.card_eq)
  have hR₃int : E ⊓ R₂ = R₃ :=
    hR₃syl.eq_of_le (le_inf hR₃E hR₃R₂) inf_le_left (hR₂.isPGroup.to_le inf_le_right)
  have hR₃H : R₃ ≤ H := (thompsonCenter_le_self P₂).trans hP₂syl.le
  have hP₂ne : P₂ ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card P₂ = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hP₂, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      ← Subgroup.card_map_of_injective (f := (MulAut.conj h).toMonoidHom)
        (MulAut.conj h).injective, Subgroup.card_eq_one] at h1
    apply d.Q_ne_bot
    rw [eq_bot_iff, ← h1]
    exact d.Q_le_Qstar.trans hQP'
  refine ⟨P₂, hP₂syl, propIV81 σ hσ hII r hr d H hH R₃
    (CFSG.section8_centerIn_thompsonSubgroup_ne_bot_of_ne_bot hP₂syl.isPGroup hP₂ne)
    (hP₂syl.isPGroup.to_le (thompsonCenter_le_self P₂)) hR₃H ?_ ?_ ?_⟩
  · rw [← hR₃int]
    exact (le_inf (hDH.trans hHZ) hDR₂).trans Subgroup.inf_normalizer_le_normalizer_inf
  · rw [← hR₃int]
    exact (le_inf (hQH.trans hHZ) (hQR₂.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  · rw [hcardE R₃ hR₃E (hR₃H.trans hHO) hcardR₃]
    exact hHZ

end Setting

end CFSG.ABGTheoremB
