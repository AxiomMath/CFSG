module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Mult
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocIdx2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocBSStd
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1Slim
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSylow

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem vPairs_nonempty_of_idx2Cover_of_mem {L K : Subgroup H} {u : H} (hu2 : orderOf u = 2)
    (huL : u ∈ L) (hKL : K ≤ L) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcov : IsIdx2Cover ↥(L ⊓ centralizer ({u} : Set H))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set H))))
    (hlt : twoAdic (L ⊓ centralizer ({u} : Set H)) < twoAdic L)
    (hZS : ∀ S : Subgroup H, S ≤ L ⊓ centralizer ({u} : Set H) → IsPGroup 2 S →
      (∀ S' : Subgroup H, S' ≤ L ⊓ centralizer ({u} : Set H) → IsPGroup 2 S' → S ≤ S' →
        S' = S) → ∀ z ∈ S, (∀ s ∈ S, z * s = s * z) → z ∈ K) :
    (vPairs L K u).Nonempty := by
  set Cu : Subgroup H := L ⊓ centralizer ({u} : Set H) with hCu
  have hKC : K ≤ Cu := fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  set E : Subgroup ↥Cu := K.subgroupOf Cu with hE
  have hKE : E.map Cu.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKC
  have : E.Normal := hcov.normal
  obtain ⟨huK, hC⟩ := central_eq_of_idx2Cover huL hu2 hcov
  let u' : ↥Cu := ⟨u, huL, mem_centralizer_singleton_iff.2 rfl⟩
  have hu'2 : u' * u' = 1 := by
    have : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
    exact Subtype.ext (by simpa [pow_two] using this)
  obtain ⟨P, hP⟩ := (isPGroup_two_zpowers hu'2).exists_le_sylow
  have huP : u' ∈ (P : Subgroup ↥Cu) := hP (mem_zpowers u')
  set S : Subgroup H := (P : Subgroup ↥Cu).map Cu.subtype with hS
  have hSCu : S ≤ Cu := Subgroup.map_subtype_le _
  have hSp : IsPGroup 2 S := P.isPGroup'.map Cu.subtype
  have hScard : Nat.card S = 2 ^ twoAdic Cu := by
    rw [hS, Subgroup.card_map_of_injective Cu.subtype_injective, P.card_eq_multiplicity]
    rfl
  have hlt' : Nat.card S < 2 ^ (Nat.card L).factorization 2 := by
    rw [hScard]
    exact Nat.pow_lt_pow_right (by norm_num) hlt
  obtain ⟨T, hTL, hTp, hST⟩ := exists_lt_of_card_lt (hSCu.trans inf_le_left) hSp hlt'
  have hSmax : ∀ S' : Subgroup H, S' ≤ Cu → IsPGroup 2 S' → S ≤ S' → S' = S := by
    intro S' hS'Cu hS'p hSS'
    have hS'' : IsPGroup 2 (S'.subgroupOf Cu) := hS'p.comap_subtype
    have hPle : (P : Subgroup ↥Cu) ≤ S'.subgroupOf Cu := fun x hx =>
      mem_subgroupOf.2 (hSS' ⟨x, hx, rfl⟩)
    have hPeq : S'.subgroupOf Cu = (P : Subgroup ↥Cu) := P.is_maximal' hS'' hPle
    rw [← Subgroup.map_subgroupOf_eq_of_le hS'Cu, hPeq]
  refine vPairs_nonempty_of_sylow (L := L) (K := K) (S := S) (T := T) hu2 ⟨u', huP, rfl⟩ hSCu
    hSmax hTL hTp hST (fun z hz hzc => (le_sup_left : K ≤ K ⊔ zpowers u)
      (hZS S hSCu hSp hSmax z hz hzc)) ?_ ?_
  · intro z hz _
    obtain ⟨hzK, hzc⟩ := mem_center_map_iff.1 hz
    have hzC : z ∈ Cu := hKC hzK
    have hzE : (⟨z, hzC⟩ : ↥Cu) ∈ E := mem_subgroupOf.2 hzK
    have hcen : (⟨⟨z, hzC⟩, hzE⟩ : ↥E) ∈ center ↥E := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subtype.ext (hzc (y : ↥Cu) (mem_subgroupOf.1 y.2)).symm)
    have hu'E : u' ∈ E := mem_subgroupOf.2 huK
    have hcenU : (⟨u', hu'E⟩ : ↥E) ∈ center ↥E :=
      Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subtype.ext
        (mem_centralizer_singleton_iff.1 (y : ↥Cu).2.2))
    have hx1 : (⟨⟨u', hu'E⟩, hcenU⟩ : ↥(center ↥E)) ≠ 1 := fun h => by
      have h1 : u = 1 := congrArg (fun w : ↥(center ↥E) => (((w : ↥E) : ↥Cu) : H)) h
      rw [h1, orderOf_one] at hu2
      exact absurd hu2 (by decide)
    rcases eq_one_or_eq_of_card_eq_two hcov.card_center hx1 ⟨⟨⟨z, hzC⟩, hzE⟩, hcen⟩ with h | h
    · left
      exact congrArg (fun w : ↥(center ↥E) => (((w : ↥E) : ↥Cu) : H)) h
    · right
      exact congrArg (fun w : ↥(center ↥E) => (((w : ↥E) : ↥Cu) : H)) h
  · have hcardK : Nat.card ↥K = Nat.card ↥E := by
      rw [← hKE, Subgroup.card_map_of_injective Cu.subtype_injective]
    have hCuK : Nat.card ↥Cu = 2 * Nat.card ↥K := by
      have := Subgroup.card_mul_index E
      rw [hcov.index_eq, ← hcardK] at this
      omega
    have hpos : 0 < Nat.card ↥K := Nat.card_pos
    have h2 : twoAdic Cu = twoAdic K + 1 := by
      unfold twoAdic
      rw [hCuK, Nat.factorization_mul (by norm_num) hpos.ne', Finsupp.add_apply,
        Nat.Prime.factorization Nat.prime_two, Finsupp.single_eq_same]
      omega
    have hSK : S ⊓ K = ((P : Subgroup ↥Cu) ⊓ E).map Cu.subtype := by
      rw [Subgroup.map_inf _ _ _ Cu.subtype_injective, hKE]
    have hle := card_le_two_mul_card_inf E (P : Subgroup ↥Cu) hcov.index_eq
    have hPcard : Nat.card (P : Subgroup ↥Cu) = 2 ^ twoAdic Cu := P.card_eq_multiplicity
    have hSKp : IsPGroup 2 ↥(S ⊓ K) := hSp.to_le inf_le_left
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hSKp
    have hcardSK : Nat.card ↥(S ⊓ K) = Nat.card ↥((P : Subgroup ↥Cu) ⊓ E) := by
      rw [hSK, Subgroup.card_map_of_injective Cu.subtype_injective]
    rw [hPcard, ← hcardSK, hm, h2, pow_succ] at hle
    have hmm : twoAdic K ≤ m := by
      have : 2 ^ twoAdic K ≤ 2 ^ m := by omega
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    unfold twoAdic
    rw [hm, Nat.Prime.factorization_pow Nat.prime_two]
    simpa [twoAdic] using hmm

theorem sol78Local39Q_of_idx2Cover {N L K : Subgroup H} {t u : H}
    (hset : SolomonSettingQ H N L K t u) (huL : u ∈ L)
    (hcov : IsIdx2Cover ↥(L ⊓ centralizer ({u} : Set H))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set H))))
    (hlt : twoAdic (L ⊓ centralizer ({u} : Set H)) < twoAdic L)
    (hZS : ∀ S : Subgroup H, S ≤ L ⊓ centralizer ({u} : Set H) → IsPGroup 2 S →
      (∀ S' : Subgroup H, S' ≤ L ⊓ centralizer ({u} : Set H) → IsPGroup 2 S' → S ≤ S' →
        S' = S) → ∀ z ∈ S, (∀ s ∈ S, z * s = s * z) → z ∈ K)
    (hinn : ∀ α : MulAut ↥K, ∃ c ∈ L ⊓ centralizer ({u} : Set H),
      ∀ k : K, ((α k : K) : H) = c * (k : H) * c⁻¹)
    (hov : ∀ X : Subgroup H, K ≤ X → X ≤ L → X ≤ L ⊓ centralizer ({u} : Set H) ∨ X = L) :
    (vPairs L K u).Nonempty ∧ Sol78Fusion39 L K u ∧ Sol78Generate L K u := by
  have hKu : ∀ k ∈ K, k * u = u * k := fun k hk =>
    mem_centralizer_iff.1 hset.u_mem_centralizer_K k hk
  obtain ⟨-, hC⟩ := central_eq_of_idx2Cover huL hset.u_order hcov
  refine ⟨vPairs_nonempty_of_idx2Cover_of_mem hset.u_order huL hset.K_le hKu hcov hlt hZS, ?_,
    sol78Generate_of_overgroups hset.u_order hC hset.K_le huL hov⟩
  refine sol78Fusion39_of_induced hKu ?_ (inducedByCentralizer_of_forall_aut hinn)
  intro g hg
  obtain ⟨-, hKg⟩ := map_conj_eq_of_hyp35 hset.hyp35 hg
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => conj_mem_of_map_eq hKg hh, fun hh => ?_⟩
  have := conj_inv_mem_of_map_eq hKg hh
  simpa [mul_assoc] using this

theorem card_centralizer_le_two_of_central_eq {L K : Subgroup H} {u : H} (huL : u ∈ L)
    (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hC : ∀ c ∈ L, (∀ k ∈ K, c * k = k * c) → c = 1 ∨ c = u) :
    Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) ≤ 2 := by
  let u' : ↥L := ⟨u, huL⟩
  have hz2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hxk : ∀ x : ↥L, (∀ k ∈ (K.subgroupOf L : Subgroup ↥L), k * x = x * k) → x ∈ zpowers u' := by
    intro x hx
    have h1 : ∀ k ∈ K, (x : H) * k = k * (x : H) := fun k hk =>
      (congrArg Subtype.val (hx ⟨k, hKL hk⟩ (mem_subgroupOf.2 hk))).symm
    rcases hC (x : H) x.2 h1 with h | h
    · rw [show x = 1 from Subtype.ext h]
      exact one_mem _
    · rw [show x = u' from Subtype.ext h]
      exact mem_zpowers u'
  calc Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L))
      ≤ Nat.card ↥(zpowers u') := Subgroup.card_le_of_le fun x hx =>
        hxk x fun k hk => (mem_centralizer_iff.1 hx k hk)
    _ = 2 := by rw [Nat.card_zpowers, hz2]

theorem card_centralizer_le_two_of_idx2Cover {L K : Subgroup H} {u : H} (huL : u ∈ L)
    (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hcov : IsIdx2Cover ↥(L ⊓ centralizer ({u} : Set H))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set H)))) :
    Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) ≤ 2 :=
  card_centralizer_le_two_of_central_eq huL hu2 hKL (central_eq_of_idx2Cover huL hu2 hcov).2

theorem solomonLocalQ_of_normal_quasisimple {s : TauCeti.SporadicName} {L K : Subgroup H} {u : H}
    (hL : OddCover s L) (hout : OutTwo ↥L) (huL : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k)
    (hC : ∀ c ∈ L, (∀ k ∈ K, c * k = k * c) → c = 1 ∨ c = u)
    (hn : (K.subgroupOf (L ⊓ centralizer ({u} : Set H))).Normal)
    (hqE : CFSG.Open.IsQuasisimple ↥(K.subgroupOf (L ⊓ centralizer ({u} : Set H)))) :
    SolomonLocalQ L K u := by
  set Cu : Subgroup H := L ⊓ centralizer ({u} : Set H) with hCu
  have hKC : K ≤ Cu := fun k hk => ⟨hKL hk, mem_centralizer_singleton_iff.2 (hKu k hk)⟩
  let u' : ↥L := ⟨u, huL⟩
  have hz2 : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu2
  have hxk : ∀ x : ↥L, (∀ k ∈ (K.subgroupOf L : Subgroup ↥L), k * x = x * k) → x ∈ zpowers u' := by
    intro x hx
    have h1 : ∀ k ∈ K, (x : H) * k = k * (x : H) := fun k hk =>
      (congrArg Subtype.val (hx ⟨k, hKL hk⟩ (mem_subgroupOf.2 hk))).symm
    rcases hC (x : H) x.2 h1 with h | h
    · rw [show x = 1 from Subtype.ext h]
      exact one_mem _
    · rw [show x = u' from Subtype.ext h]
      exact mem_zpowers u'
  have hq : CFSG.Open.IsQuasisimple ↥(K.subgroupOf L) :=
    isQuasisimple_of_mulEquiv'
      ((Subgroup.subgroupOfEquivOfLe hKL).trans (Subgroup.subgroupOfEquivOfLe hKC).symm).symm hqE
  have hcentC := card_centralizer_le_two_of_central_eq huL hu2 hKL hC
  have hKz : K.subgroupOf L ≤ centralizer ({u'} : Set ↥L) := fun k hk =>
    mem_centralizer_singleton_iff.2 (Subtype.ext (hKu k (mem_subgroupOf.1 hk)))
  have hHn : ((K.subgroupOf L).subgroupOf (centralizer ({u'} : Set ↥L))).Normal := by
    refine ⟨fun n hn' g => ?_⟩
    have hn'' : ((n : ↥L) : H) ∈ K := mem_subgroupOf.1 (mem_subgroupOf.1 hn')
    have hgC : (((g : ↥L) : H)) ∈ Cu := ⟨(g : ↥L).2, mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (mem_centralizer_singleton_iff.1 g.2))⟩
    have hnC : (((n : ↥L) : H)) ∈ Cu := hKC hn''
    have h1 := hn.conj_mem ⟨((n : ↥L) : H), hnC⟩ (mem_subgroupOf.2 hn'')
      ⟨((g : ↥L) : H), hgC⟩
    exact mem_subgroupOf.2 (mem_subgroupOf.2 (mem_subgroupOf.1 h1))
  have hsyl : ∀ U : Subgroup ↥L, IsPGroup 2 U →
      U ≤ centralizer ({u'} : Set ↥L) ⊓ centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L) →
        Nat.card U ≤ 2 := by
    intro U _ hU
    calc Nat.card U ≤ Nat.card ↥(zpowers u') := Subgroup.card_le_of_le fun x hx =>
          hxk x fun k hk => (mem_centralizer_iff.1 (hU hx).2 k hk)
      _ = 2 := by rw [Nat.card_zpowers, hz2]
  have hstd : CFSG.Open.standardComponentIsStandard (K.subgroupOf L) :=
    (M24Std.standardComponentIsStandard_of_normal hz2 hq hKz hHn hsyl).1
  exact
  { u_order := hu2
    u_mem := Subgroup.le_normalizer huL
    u_not_central := hL.not_mem_centralizer_of_orderOf_two huL hu2
    K_le := hKL
    u_mem_centralizer_K := mem_centralizer_iff.2 hKu
    standard_in_L := solStd_of_standardComponentIsStandard hstd
    autCentralizer_two := twoAdic_autCentralizer_le hout hcentC }

theorem solomonLocalQ_of_idx2Cover {s : TauCeti.SporadicName} {L K : Subgroup H} {u : H}
    (hL : OddCover s L) (hout : OutTwo ↥L) (huL : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k)
    (hcov : IsIdx2Cover ↥(L ⊓ centralizer ({u} : Set H))
      (K.subgroupOf (L ⊓ centralizer ({u} : Set H)))) : SolomonLocalQ L K u :=
  solomonLocalQ_of_normal_quasisimple hL hout huL hu2 hKL hKu
    (central_eq_of_idx2Cover huL hu2 hcov).2 hcov.normal hcov.quasisimple

theorem eq_commutator_of_perfect_of_index_two {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hn : E.Normal) (hp : _root_.commutator ↥E = ⊤) (hi : E.index = 2) :
    E = _root_.commutator X := by
  apply le_antisymm
  · intro x hx
    have hx' : (⟨x, hx⟩ : ↥E) ∈ _root_.commutator ↥E := by
      rw [hp]
      exact mem_top _
    have h1 := Subgroup.mem_map_of_mem E.subtype hx'
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h1
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mono le_top le_top h1
  · have hsq : ∀ x : X ⧸ E, x * x = 1 := by
      intro x
      have h2 := pow_card_eq_one' (G := X ⧸ E) (x := x)
      rwa [← Subgroup.index_eq_card, hi, pow_two] at h2
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have hmk : (QuotientGroup.mk' E) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_def,
        inv_eq_of_mul_eq_one_right (hsq _), inv_eq_of_mul_eq_one_right (hsq _)]
      calc QuotientGroup.mk' E a * QuotientGroup.mk' E b * QuotientGroup.mk' E a *
          QuotientGroup.mk' E b = (QuotientGroup.mk' E a * QuotientGroup.mk' E b) *
          (QuotientGroup.mk' E a * QuotientGroup.mk' E b) := by group
        _ = 1 := hsq _
    exact (QuotientGroup.eq_one_iff _).1 hmk

theorem _root_.CFSG.EvenSporadicStandard.Solomon78.IsIdx2Cover.eq_commutator {X : Type} [Group X]
    [Finite X] {E : Subgroup X} (h : IsIdx2Cover X E) : E = _root_.commutator X :=
  eq_commutator_of_perfect_of_index_two h.normal h.quasisimple.1 h.index_eq

theorem twoAdic_autCentralizer_le_one_of_allInner {L K : Subgroup H} (hinn : AllInner ↥L)
    (hC : Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) ≤ 2) :
    twoAdic (autCentralizer L K) ≤ 1 := by
  have h1 := twoAdic_autCentralizer_le_of_allInner (L := L) (K := K) (fun α => by
    obtain ⟨g, hg⟩ := hinn α
    exact ⟨g, fun x => by rw [hg]; rfl⟩)
  refine h1.trans ?_
  unfold twoAdic
  have h2 : Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) ∣ 2 := by
    have hpos : 0 < Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) :=
      Nat.card_pos
    have : Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) = 1 ∨
        Nat.card ↥(centralizer ((K.subgroupOf L : Subgroup ↥L) : Set ↥L)) = 2 := by omega
    rcases this with h | h
    · rw [h]; exact one_dvd _
    · rw [h]
  have h3 := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' (by norm_num)).2 h2 2
  simpa [Nat.Prime.factorization Nat.prime_two] using h3

end CFSG.EvenSporadicStandard.Induction
