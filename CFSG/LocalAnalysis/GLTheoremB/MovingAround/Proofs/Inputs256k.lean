module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Abs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeTwE6TwoCriterion
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQThreeFactsTwoE

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T (vecProd vecProdHom vecProdHom_apply)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T (listVec exists_normVec_ker_mem)
open Timmesfeld.Co1Leaf (normVecs kerBasis)

section Center

variable {H : Type*} [Group H]

theorem eq_one_of_mul_mem_center (hperf : commutator H = ⊤) (φ : MulAut H)
    (h : ∀ x : H, x⁻¹ * φ x ∈ Subgroup.center H) : φ = 1 := by
  let f : H →* Subgroup.center H :=
    { toFun := fun x => ⟨x⁻¹ * φ x, h x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => by
        apply Subtype.ext
        have hc : (y⁻¹ * φ y) * x⁻¹ = x⁻¹ * (y⁻¹ * φ y) :=
          ((Subgroup.mem_center_iff.1 (h y)) x⁻¹).symm
        simp only [Subgroup.coe_mul, mul_inv_rev, map_mul]
        calc y⁻¹ * x⁻¹ * (φ x * φ y) = y⁻¹ * (x⁻¹ * φ x) * φ y := by group
          _ = (x⁻¹ * φ x) * (y⁻¹ * φ y) := by
            have hx : (x⁻¹ * φ x) * y⁻¹ = y⁻¹ * (x⁻¹ * φ x) :=
              ((Subgroup.mem_center_iff.1 (h x)) y⁻¹).symm
            calc y⁻¹ * (x⁻¹ * φ x) * φ y = (x⁻¹ * φ x) * y⁻¹ * φ y := by rw [hx]
              _ = (x⁻¹ * φ x) * (y⁻¹ * φ y) := by group }
  have hker : commutator H ≤ f.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact Subtype.ext (Subgroup.mem_center_iff.1 (f b).2 (f a))
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ f.ker := hker (hperf ▸ Subgroup.mem_top x)
  rw [MonoidHom.mem_ker] at hx
  have h1 : x⁻¹ * φ x = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  calc φ x = x * (x⁻¹ * φ x) := by group
    _ = x := by rw [h1, mul_one]

variable (H) in
@[expose] noncomputable def autQuotCenter : MulAut H →* MulAut (H ⧸ Subgroup.center H) where
  toFun φ := QuotientGroup.congr (Subgroup.center H) (Subgroup.center H) φ
    ((Subgroup.characteristic_iff_map_eq.1 inferInstance) φ)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' φ ψ := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x => rfl

theorem autQuotCenter_mk (φ : MulAut H) (x : H) :
    autQuotCenter H φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := rfl

theorem eq_one_of_autQuotCenter_eq_one (hperf : commutator H = ⊤) {φ : MulAut H}
    (h : autQuotCenter H φ = 1) : φ = 1 := by
  refine eq_one_of_mul_mem_center hperf φ fun x => ?_
  have h1 := congrArg (fun ψ : MulAut (H ⧸ Subgroup.center H) => ψ (QuotientGroup.mk x)) h
  simp only [autQuotCenter_mk, MulAut.one_apply] at h1
  exact (QuotientGroup.eq.1 h1.symm)

end Center

section Conj

variable {X : Type*} [Group X]

@[expose] noncomputable def conjAutOfNormalizes (R A : Subgroup X)
    (hA : ∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R) : ↥A →* MulAut ↥R where
  toFun a :=
    { toFun := fun r => ⟨a * r * a⁻¹, hA a a.2 r r.2⟩
      invFun := fun r => ⟨a⁻¹ * r * a, by
        have := hA a⁻¹ (inv_mem a.2) r r.2
        rwa [inv_inv] at this⟩
      left_inv := fun r => Subtype.ext (by simp [mul_assoc])
      right_inv := fun r => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun r s => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext r
    simp
  map_mul' a b := by
    ext r
    simp [mul_assoc]

theorem conjAutOfNormalizes_apply (R A : Subgroup X) (hA : ∀ a ∈ A, ∀ r ∈ R, a * r * a⁻¹ ∈ R)
    (a : A) (r : R) : ((conjAutOfNormalizes R A hA a r : R) : X) = a * r * a⁻¹ := rfl

end Conj

theorem card_mulAut_alternatingGroup_five_k :
    Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
  rw [← Nat.card_congr (Equiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num))), Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem card_alternatingGroup_five_k : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem dvd_three_of_dvd_pow_of_dvd_120 {d m : ℕ} (h1 : d ∣ 3 ^ m) (h2 : d ∣ 120) : d ∣ 3 := by
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h1
  rcases j with _ | _ | j
  · norm_num
  · norm_num
  · exfalso
    have : 3 ^ 2 ∣ 120 := (pow_dvd_pow 3 (by omega)).trans h2
    norm_num at this

section Exponent

variable {X : Type*} [Group X]

theorem exists_orderOf_five_alternatingGroup_five :
    ∃ g : alternatingGroup (Fin 5), orderOf g = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact exists_prime_orderOf_dvd_card' 5 (by rw [card_alternatingGroup_five_k]; norm_num)

theorem false_of_pow_eighteen {K : Type*} [Group K]
    (hA5 : Nonempty ((K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin 5))) (f : K →* X)
    (hker : f.ker ≤ Subgroup.center K) (h18 : ∀ k, f k ^ 18 = 1) : False := by
  obtain ⟨e⟩ := hA5
  obtain ⟨g, hg⟩ := exists_orderOf_five_alternatingGroup_five
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (e.symm g)
  have h1 : k ^ 18 ∈ Subgroup.center K := hker (by rw [MonoidHom.mem_ker, map_pow]; exact h18 k)
  have h2 : ((k : K ⧸ Subgroup.center K)) ^ 18 = 1 := by
    rw [← QuotientGroup.mk_pow]
    exact (QuotientGroup.eq_one_iff _).2 h1
  rw [hk] at h2
  have h3 : g ^ 18 = 1 := by
    have := congrArg e h2
    rwa [map_pow, MulEquiv.apply_symm_apply, map_one] at this
  have h4 := orderOf_dvd_of_pow_eq_one h3
  rw [hg] at h4
  norm_num at h4

end Exponent

section Centralizer

variable {X : Type*} [Group X]

theorem relIndex_centralizer_dvd_three {A' R : Subgroup X} [Finite A'] {m : ℕ}
    (hA' : Nat.card A' ∣ 3 ^ m) (hnorm : ∀ a ∈ A', ∀ r ∈ R, a * r * a⁻¹ ∈ R)
    (hperf : commutator R = ⊤)
    (hA5 : Nonempty ((↥R ⧸ Subgroup.center ↥R) ≃* alternatingGroup (Fin 5))) :
    (A' ⊓ Subgroup.centralizer (R : Set X)).relIndex A' ∣ 3 := by
  obtain ⟨e⟩ := hA5
  let ψ : ↥A' →* MulAut (alternatingGroup (Fin 5)) :=
    (MulAut.congr e).toMonoidHom.comp ((autQuotCenter ↥R).comp (conjAutOfNormalizes R A' hnorm))
  have hrange : Nat.card ψ.range ∣ 3 := by
    refine dvd_three_of_dvd_pow_of_dvd_120 (m := m) ((Subgroup.card_range_dvd ψ).trans hA') ?_
    rw [← card_mulAut_alternatingGroup_five_k]
    exact Subgroup.card_subgroup_dvd_card _
  have hker : (A' ⊓ Subgroup.centralizer (R : Set X)).subgroupOf A' = ψ.ker := by
    ext a
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, MonoidHom.mem_ker]
    constructor
    · rintro ⟨-, hc⟩
      have h1 : conjAutOfNormalizes R A' hnorm a = 1 := by
        refine MulEquiv.ext fun r => Subtype.ext ?_
        rw [conjAutOfNormalizes_apply, MulAut.one_apply]
        have := (Subgroup.mem_centralizer_iff.1 hc) r r.2
        calc (a : X) * r * (a : X)⁻¹ = r * a * (a : X)⁻¹ := by rw [this]
          _ = r := by group
      show (MulAut.congr e) (autQuotCenter ↥R (conjAutOfNormalizes R A' hnorm a)) = 1
      rw [h1, map_one, map_one]
    · intro ha
      refine ⟨a.2, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
      have h1 : autQuotCenter ↥R (conjAutOfNormalizes R A' hnorm a) = 1 := by
        apply (MulAut.congr e).injective
        rw [map_one]
        exact ha
      have h3 := eq_one_of_autQuotCenter_eq_one hperf h1
      have h4 : (a : X) * r * (a : X)⁻¹ = r :=
        congrArg (fun σ : MulAut ↥R => ((σ ⟨r, hr⟩ : R) : X)) h3
      calc r * a = (a : X) * r * (a : X)⁻¹ * a := by rw [h4]
        _ = a * r := by group
  rw [Subgroup.relIndex, hker, Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  exact hrange

end Centralizer

section Conjugates

variable {X : Type*} [Group X]

theorem mem_map_conj_iff_k {K : Subgroup X} {g x : X} :
    x ∈ K.map (MulAut.conj g : X →* X) ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have e : g⁻¹ * (MulAut.conj g : X →* X) k * g = k := by
      change g⁻¹ * (g * k * g⁻¹) * g = k
      group
    rw [e]
    exact hk
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem map_conj_eq_self_of_mem_k {C : Subgroup X} {c : X} (hc : c ∈ C) :
    C.map (MulAut.conj c : X →* X) = C := by
  ext x
  rw [mem_map_conj_iff_k]
  constructor
  · intro h
    have e : x = c * (c⁻¹ * x * c) * c⁻¹ := by group
    rw [e]
    exact C.mul_mem (C.mul_mem hc h) (C.inv_mem hc)
  · intro h
    exact C.mul_mem (C.mul_mem (C.inv_mem hc) h) hc

theorem isComponentOf_map_conj_of_mem_k {K C : Subgroup X} (hK : CFSG.Open.IsComponentOf K C)
    {c : X} (hc : c ∈ C) : CFSG.Open.IsComponentOf (K.map (MulAut.conj c : X →* X)) C := by
  have h := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (MulAut.conj c) hK
  rwa [map_conj_eq_self_of_mem_k hc] at h

theorem mem_normalizer_of_map_conj_eq_k {K : Subgroup X} {g h : X}
    (e : K.map (MulAut.conj g : X →* X) = K.map (MulAut.conj h : X →* X)) :
    g⁻¹ * h ∈ Subgroup.normalizer (K : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have h1 : h * n * h⁻¹ ∈ K.map (MulAut.conj h : X →* X) := by
      rw [mem_map_conj_iff_k]
      have e2 : h⁻¹ * (h * n * h⁻¹) * h = n := by group
      rw [e2]
      exact hn
    rw [← e, mem_map_conj_iff_k] at h1
    have e3 : g⁻¹ * (h * n * h⁻¹) * g = g⁻¹ * h * n * (g⁻¹ * h)⁻¹ := by group
    rwa [e3] at h1
  · intro hn
    have h1 : g * (g⁻¹ * h * n * (g⁻¹ * h)⁻¹) * g⁻¹ ∈ K.map (MulAut.conj g : X →* X) := by
      rw [mem_map_conj_iff_k]
      have e2 : g⁻¹ * (g * (g⁻¹ * h * n * (g⁻¹ * h)⁻¹) * g⁻¹) * g = g⁻¹ * h * n * (g⁻¹ * h)⁻¹ := by
        group
      rw [e2]
      exact hn
    rw [e, mem_map_conj_iff_k] at h1
    have e3 : h⁻¹ * (g * (g⁻¹ * h * n * (g⁻¹ * h)⁻¹) * g⁻¹) * h = n := by group
    rwa [e3] at h1

theorem mem_normalizer_of_map_conj_eq_self_k {K : Subgroup X} {g : X}
    (e : K.map (MulAut.conj g : X →* X) = K) : g ∈ Subgroup.normalizer (K : Set X) := by
  have e' : K.map (MulAut.conj (1 : X) : X →* X) = K.map (MulAut.conj g : X →* X) := by
    rw [e]
    ext x
    rw [mem_map_conj_iff_k]
    simp
  simpa using mem_normalizer_of_map_conj_eq_k e'

theorem mem_normalizer_of_forall_commute {N : Subgroup X} {a : X}
    (h : ∀ n ∈ N, a * n = n * a) : a ∈ Subgroup.normalizer (N : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    have e : a * n * a⁻¹ = n := by rw [h n hn]; group
    rw [e]
    exact hn
  · intro hn
    have h1 : a * (a * n * a⁻¹) = (a * n * a⁻¹) * a := h _ hn
    have e : a * n * a⁻¹ = n := by
      calc a * n * a⁻¹ = a⁻¹ * (a * (a * n * a⁻¹)) := by group
        _ = a⁻¹ * ((a * n * a⁻¹) * a) := by rw [h1]
        _ = n := by group
    rw [← e]
    exact hn

theorem relIndex_sup_zpowers_eq_three {N : Subgroup X} {a : X} (ha3 : a ^ 3 = 1) (haN : a ∉ N)
    (hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (N : Set X)) :
    N.relIndex (Subgroup.zpowers a ⊔ N) = 3 := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient (Subgroup.zpowers a) N hnorm
  have h1 : N.relIndex (Subgroup.zpowers a ⊔ N) = N.relIndex (Subgroup.zpowers a) := by
    rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact (Nat.card_congr e.toEquiv).symm
  rw [h1]
  have ha1 : a ≠ 1 := fun h => haN (h ▸ N.one_mem)
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hcard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  haveI : Finite (Subgroup.zpowers a) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hbot : N.subgroupOf (Subgroup.zpowers a) = ⊥ := by
    have hd : Nat.card (N.subgroupOf (Subgroup.zpowers a)) ∣ 3 :=
      hcard ▸ Subgroup.card_subgroup_dvd_card _
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h | h
    · exact Subgroup.eq_bot_of_card_eq _ h
    · exfalso
      have htop : N.subgroupOf (Subgroup.zpowers a) = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (h.trans hcard.symm)
      have : (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) ∈
          N.subgroupOf (Subgroup.zpowers a) := htop ▸ Subgroup.mem_top _
      exact haN (Subgroup.mem_subgroupOf.1 this)
  rw [Subgroup.relIndex, hbot, Subgroup.index_bot, hcard]

end Conjugates

section Family

variable {X : Type*} [Group X]

theorem card_eq_sixty_mul_card_center {H : Type*} [Group H]
    (hA5 : Nonempty ((H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 5))) :
    Nat.card H = 60 * Nat.card (Subgroup.center H) := by
  obtain ⟨e⟩ := hA5
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H),
    Nat.card_congr e.toEquiv, card_alternatingGroup_five_k]

theorem sixty_pow_dvd_of_pairwise_commute {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → Subgroup X) [∀ i, Finite (H i)]
    (hcomm : Pairwise fun i j => ∀ x y : X, x ∈ H i → y ∈ H j → Commute x y)
    {C : Subgroup X} [Finite C] (hHC : ∀ i, H i ≤ C)
    (hA5 : ∀ i, Nonempty ((↥(H i) ⧸ Subgroup.center ↥(H i)) ≃* alternatingGroup (Fin 5))) :
    60 ^ Fintype.card ι ∣ Nat.card C := by
  classical
  set ψ := Subgroup.noncommPiCoprod hcomm with hψ
  have hrange : Nat.card ψ.range ∣ Nat.card C := by
    apply Subgroup.card_dvd_of_le
    rw [hψ, Subgroup.noncommPiCoprod_range]
    exact iSup_le hHC
  set Z : Subgroup (∀ i, H i) := Subgroup.pi Set.univ fun i => Subgroup.center (H i) with hZ
  have hkerZ : ψ.ker ≤ Z := by
    intro u hu
    rw [Subgroup.mem_pi]
    intro i _
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ i) (fun j => (u j : X))
      (fun j _ k _ h => hcomm h _ _ (u j).2 (u k).2)
    have hu' : ψ u = 1 := hu
    rw [hψ, Subgroup.noncommPiCoprod_apply] at hu'
    rw [hu'] at h1
    set P := (Finset.univ.erase i).noncommProd (fun j => (u j : X))
      (fun j hj k hk h => hcomm h _ _ (u j).2 (u k).2) with hP
    have hPc : Commute (y : X) P := by
      apply Finset.noncommProd_commute
      intro j hj
      exact hcomm (Finset.ne_of_mem_erase hj).symm _ _ y.2 (u j).2
    have hui : (u i : X) = P⁻¹ := eq_inv_of_mul_eq_one_left h1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hui]
    exact hPc.inv_right.eq
  have hZcard : Nat.card Z = ∏ i, Nat.card (Subgroup.center (H i)) := by
    rw [← Nat.card_pi]
    refine Nat.card_congr ((Equiv.subtypeEquivRight fun x => ?_).trans
      (Equiv.subtypePiEquivPi (p := fun i (y : H i) => y ∈ Subgroup.center (H i))))
    rw [Subgroup.mem_pi]
    simp
  have hdom : Nat.card (∀ i, H i) = 60 ^ Fintype.card ι * Nat.card Z := by
    rw [Nat.card_pi, hZcard, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => card_eq_sixty_mul_card_center (hA5 i)
  have hker : Nat.card ψ.range * Nat.card ψ.ker = Nat.card (∀ i, H i) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
  obtain ⟨q, hq⟩ := Subgroup.card_dvd_of_le hkerZ
  have hk0 : 0 < Nat.card ψ.ker := Nat.card_pos
  have h60 : Nat.card ψ.range = 60 ^ Fintype.card ι * q := by
    rw [hdom, hq] at hker
    have : Nat.card ψ.range * Nat.card ψ.ker = (60 ^ Fintype.card ι * q) * Nat.card ψ.ker := by
      rw [hker]
      ring
    exact Nat.eq_of_mul_eq_mul_right hk0 this
  exact (Dvd.intro q h60.symm).trans hrange

end Family

section Torus

variable {X : Type*} [Group X] {m : ℕ} {d : Fin m → X}

theorem vecProdHom_range_comm (hcomm : ∀ i j, Commute (d i) (d j)) (hpow : ∀ i, d i ^ 3 = 1)
    {x y : X}
    (hx : x ∈ (vecProdHom d hcomm hpow).range) (hy : y ∈ (vecProdHom d hcomm hpow).range) :
    x * y = y * x := by
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm]

theorem vecProdHom_range_pow_three (hcomm : ∀ i j, Commute (d i) (d j)) (hpow : ∀ i, d i ^ 3 = 1)
    {x : X}
    (hx : x ∈ (vecProdHom d hcomm hpow).range) : x ^ 3 = 1 := by
  obtain ⟨u, rfl⟩ := hx
  rw [← map_pow]
  have : u ^ 3 = 1 := by
    rw [← ofAdd_toAdd u, ← ofAdd_nsmul]
    have h3 : 3 • Multiplicative.toAdd u = 0 := by
      funext j
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
      have : (3 : ZMod 3) = 0 := rfl
      rw [Nat.cast_ofNat, this, zero_mul]
    rw [h3, ofAdd_zero]
  rw [this, map_one]

theorem card_vecProdHom_range (hcomm : ∀ i j, Commute (d i) (d j)) (hpow : ∀ i, d i ^ 3 = 1)
    (hinj : Function.Injective (vecProdHom d hcomm hpow)) :
    Nat.card (vecProdHom d hcomm hpow).range = 3 ^ m := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
    Nat.card_eq_fintype_card]
  simp [Fintype.card_multiplicative, Fintype.card_pi, ZMod.card]

theorem pow_eighteen_of_relIndex (hcomm : ∀ i j, Commute (d i) (d j)) (hpow : ∀ i, d i ^ 3 = 1)
    (hinj : Function.Injective (vecProdHom d hcomm hpow)) {C : Subgroup X}
    (hstd : ∀ x ∈ C, (∀ a ∈ (vecProdHom d hcomm hpow).range, a * x = x * a) → x ^ 18 = 1)
    (hhyp : ∀ fl ∈ normVecs 3 m, ∀ x ∈ C,
      (∀ b ∈ kerBasis 3 fl, vecProd d (listVec m b) * x = x * vecProd d (listVec m b)) →
        x ^ 18 = 1)
    {B : Subgroup X} (hBA : B ≤ (vecProdHom d hcomm hpow).range)
    (hidx : B.relIndex (vecProdHom d hcomm hpow).range ∣ 3) {x : X} (hx : x ∈ C)
    (hxB : ∀ b ∈ B, b * x = x * b) : x ^ 18 = 1 := by
  rcases (Nat.dvd_prime Nat.prime_three).1 hidx with h1 | h3
  · have hAB : (vecProdHom d hcomm hpow).range ≤ B := Subgroup.relIndex_eq_one.1 h1
    exact hstd x hx fun a ha => hxB a (hAB ha)
  · obtain ⟨fl, hfl, hmem⟩ := exists_normVec_ker_mem hcomm hpow hinj hBA h3
    exact hhyp fl hfl x hx fun b hb => hxB _ (hmem b hb)

end Torus

section Arith

variable {X : Type*} [Group X]

theorem pow_mod_three_of_pow_three_k {x : X} (hx : x ^ 3 = 1) (u : ℕ) : x ^ u = x ^ (u % 3) := by
  conv_lhs => rw [← Nat.div_add_mod u 3, pow_add, pow_mul, hx, one_pow, one_mul]

theorem eq_sq_sq_of_pow_three_k {x : X} (hx : x ^ 3 = 1) : x = (x ^ 2) ^ 2 := by
  rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, hx, one_mul]

theorem mod_three_eq_zero_of_mem {A₀ : Subgroup X} {a b : X} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (haA : a ∉ A₀) (hbA : b ∉ A₀ ⊔ Subgroup.zpowers a) {u w : ℕ}
    (h : a ^ u * b ^ w ∈ A₀) : u % 3 = 0 ∧ w % 3 = 0 := by
  rw [pow_mod_three_of_pow_three_k ha3 u, pow_mod_three_of_pow_three_k hb3 w] at h
  have hu3 : u % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hw3 : w % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hzp : ∀ k : ℕ, (a ^ k)⁻¹ ∈ A₀ ⊔ Subgroup.zpowers a := fun k =>
    Subgroup.mem_sup_right (inv_mem (pow_mem (Subgroup.mem_zpowers a) k))
  have hbw : b ^ (w % 3) ∈ A₀ ⊔ Subgroup.zpowers a := by
    have e : b ^ (w % 3) = (a ^ (u % 3))⁻¹ * (a ^ (u % 3) * b ^ (w % 3)) := by group
    rw [e]
    exact mul_mem (hzp _) (Subgroup.mem_sup_left h)
  interval_cases hw : w % 3
  · simp only [pow_zero, mul_one] at h
    interval_cases hu : u % 3
    · exact ⟨rfl, rfl⟩
    · exact absurd (by simpa using h) haA
    · exact absurd (by rw [eq_sq_sq_of_pow_three_k ha3]; exact pow_mem h 2) haA
  · exact absurd (by simpa using hbw) hbA
  · exact absurd (by rw [eq_sq_sq_of_pow_three_k hb3]; exact pow_mem hbw 2) hbA

theorem inv_mul_eq_pow_mul_pow {a b : X} (hab : Commute a b) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (i j i' j' : ℕ) :
    (a ^ i * b ^ j)⁻¹ * (a ^ i' * b ^ j') = a ^ (i' + 2 * i) * b ^ (j' + 2 * j) := by
  have hai : (a ^ i)⁻¹ = a ^ (2 * i) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, ha3, one_pow]
  have hbj : (b ^ j)⁻¹ = b ^ (2 * j) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hb3, one_pow]
  have hc : Commute (b ^ (2 * j)) (a ^ (2 * i + i')) := (hab.pow_pow _ _).symm
  rw [mul_inv_rev, hai, hbj]
  calc b ^ (2 * j) * a ^ (2 * i) * (a ^ i' * b ^ j')
      = b ^ (2 * j) * a ^ (2 * i + i') * b ^ j' := by rw [pow_add]; group
    _ = a ^ (2 * i + i') * b ^ (2 * j) * b ^ j' := by rw [hc.eq]
    _ = a ^ (i' + 2 * i) * b ^ (j' + 2 * j) := by
      rw [mul_assoc, ← pow_add, add_comm (2 * i), add_comm (2 * j)]

end Arith

section Main

variable {X : Type*} [Group X] {m : ℕ} {d : Fin m → X}

section Rearrange


theorem six_mul_rearrange_k (x y x₁ y₁ x₂ y₂ : X) (c1 : y * x₁ = x₁ * y)
    (c2 : y₁ * x₂ = x₂ * y₁) (c3 : y * x₂ = x₂ * y) :
    x * y * (x₁ * y₁) * (x₂ * y₂) = x * x₁ * x₂ * (y * y₁ * y₂) := by
  calc x * y * (x₁ * y₁) * (x₂ * y₂) = x * (y * x₁) * y₁ * x₂ * y₂ := by group
    _ = x * (x₁ * y) * y₁ * x₂ * y₂ := by rw [c1]
    _ = x * x₁ * y * (y₁ * x₂) * y₂ := by group
    _ = x * x₁ * y * (x₂ * y₁) * y₂ := by rw [c2]
    _ = x * x₁ * (y * x₂) * y₁ * y₂ := by group
    _ = x * x₁ * (x₂ * y) * y₁ * y₂ := by rw [c3]
    _ = x * x₁ * x₂ * (y * y₁ * y₂) := by group

end Rearrange

variable [Finite X]

theorem false_of_torus_comp (hcomm : ∀ i j, Commute (d i) (d j)) (hpow : ∀ i, d i ^ 3 = 1)
    (hinj : Function.Injective (vecProdHom d hcomm hpow)) {C K : Subgroup X}
    (hAC : (vecProdHom d hcomm hpow).range ≤ C) (hK : CFSG.Open.IsComponentOf K C)
    (hA5 : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5)))
    (hstd : ∀ x ∈ C, (∀ a ∈ (vecProdHom d hcomm hpow).range, a * x = x * a) → x ^ 18 = 1)
    (hhyp : ∀ fl ∈ normVecs 3 m, ∀ x ∈ C,
      (∀ b ∈ kerBasis 3 fl, vecProd d (listVec m b) * x = x * vecProd d (listVec m b)) →
        x ^ 18 = 1)
    (h5 : ¬ 5 ^ 9 ∣ Nat.card C) : False := by
  classical
  set A := (vecProdHom d hcomm hpow).range with hAdef
  have hAcard : Nat.card A = 3 ^ m := card_vecProdHom_range hcomm hpow hinj
  haveI : Finite A := Nat.finite_of_card_ne_zero (by rw [hAcard]; positivity)
  have hKC : K ≤ C := hK.1
  haveI : Finite K := Finite.of_injective (Subgroup.inclusion hKC) (Subgroup.inclusion_injective _)
  have hperf : commutator K = ⊤ := hK.2.2.1
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    vecProdHom_range_comm hcomm hpow hx hy
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := fun x hx => vecProdHom_range_pow_three hcomm hpow hx
  set A₀ := A ⊓ Subgroup.normalizer (K : Set X) with hA₀def
  haveI : Finite A₀ := Finite.of_injective (Subgroup.inclusion (inf_le_left : A₀ ≤ A))
    (Subgroup.inclusion_injective _)
  have hA₀card : Nat.card A₀ ∣ 3 ^ m := hAcard ▸ Subgroup.card_dvd_of_le inf_le_left
  have hnorm₀ : ∀ a ∈ A₀, ∀ r ∈ K, a * r * a⁻¹ ∈ K := fun a ha r hr =>
    (Subgroup.mem_normalizer_iff.1 ha.2 r).1 hr
  set B₀ := A₀ ⊓ Subgroup.centralizer (K : Set X) with hB₀def
  have hB₀ : B₀.relIndex A₀ ∣ 3 := relIndex_centralizer_dvd_three hA₀card hnorm₀ hperf hA5
  have hB₀A₀ : B₀ ≤ A₀ := inf_le_left
  have hA₀A : A₀ ≤ A := inf_le_left
  have hB₀K : ∀ b ∈ B₀, ∀ k ∈ K, b * k = k * b := fun b hb k hk =>
    ((Subgroup.mem_centralizer_iff.1 hb.2) k hk).symm
  obtain ⟨e⟩ := hA5
  by_cases hAN : A ≤ Subgroup.normalizer (K : Set X)
  ·
    have hA₀eq : A₀ = A := inf_eq_left.2 hAN
    have hidx : B₀.relIndex A ∣ 3 := by
      have h := hB₀
      rwa [hA₀eq] at h
    refine false_of_pow_eighteen ⟨e⟩ K.subtype (by
      rw [Subgroup.ker_subtype]
      exact bot_le) fun k => ?_
    exact pow_eighteen_of_relIndex hcomm hpow hinj hstd hhyp (hB₀A₀.trans hA₀A) hidx (hKC k.2)
      fun b hb => hB₀K b hb k k.2
  obtain ⟨a, haA, haN⟩ := Set.not_subset.1 hAN
  have ha3 : a ^ 3 = 1 := hA3 a haA
  have haC : a ∈ C := hAC haA
  have haA₀ : a ∉ A₀ := fun h => haN h.2
  have hsq : a = (a ^ 2) ^ 2 := eq_sq_sq_of_pow_three_k ha3
  by_cases hA1 : A ≤ A₀ ⊔ Subgroup.zpowers a
  ·
    set K₁ := K.map (MulAut.conj a : X →* X) with hK₁def
    set K₂ := K.map (MulAut.conj (a ^ 2) : X →* X) with hK₂def
    have hK₁ : CFSG.Open.IsComponentOf K₁ C := isComponentOf_map_conj_of_mem_k hK haC
    have hK₂ : CFSG.Open.IsComponentOf K₂ C := isComponentOf_map_conj_of_mem_k hK (pow_mem haC 2)
    have hne01 : K ≠ K₁ := fun h => haN (mem_normalizer_of_map_conj_eq_self_k h.symm)
    have hne02 : K ≠ K₂ := fun h => haN (by
      have h2 := mem_normalizer_of_map_conj_eq_self_k h.symm
      rw [hsq]
      exact pow_mem h2 2)
    have hne12 : K₁ ≠ K₂ := fun h => haN (by
      have h2 := mem_normalizer_of_map_conj_eq_k h
      have e2 : a⁻¹ * a ^ 2 = a := by group
      rwa [e2] at h2)
    have hc01 := CFSG.LocalAnalysis.GLTheoremA.I142.components_commute_of_ne hK hK₁ hne01
    have hc02 := CFSG.LocalAnalysis.GLTheoremA.I142.components_commute_of_ne hK hK₂ hne02
    have hc12 := CFSG.LocalAnalysis.GLTheoremA.I142.components_commute_of_ne hK₁ hK₂ hne12
    have hm1 : ∀ k ∈ K, a * k * a⁻¹ ∈ K₁ := fun k hk => ⟨k, hk, rfl⟩
    have hm2 : ∀ k ∈ K, a ^ 2 * k * (a ^ 2)⁻¹ ∈ K₂ := fun k hk => ⟨k, hk, rfl⟩
    let Δ : ↥K →* X :=
      { toFun := fun k => (k : X) * (a * k * a⁻¹) * (a ^ 2 * k * (a ^ 2)⁻¹)
        map_one' := by simp
        map_mul' := fun k l => by
          simp only [Subgroup.coe_mul]
          have e1 : a * ((k : X) * l) * a⁻¹ = (a * k * a⁻¹) * (a * l * a⁻¹) := by group
          have e2 : a ^ 2 * ((k : X) * l) * (a ^ 2)⁻¹ =
              (a ^ 2 * k * (a ^ 2)⁻¹) * (a ^ 2 * l * (a ^ 2)⁻¹) := by group
          rw [e1, e2]
          exact six_mul_rearrange_k _ _ _ _ _ _ (hc01 l l.2 _ (hm1 k k.2))
            (hc12 _ (hm1 l l.2) _ (hm2 k k.2)) (hc02 l l.2 _ (hm2 k k.2)) }
    have hΔ : ∀ k : K, Δ k = (k : X) * (a * k * a⁻¹) * (a ^ 2 * k * (a ^ 2)⁻¹) := fun k => rfl
    have hker : Δ.ker ≤ Subgroup.center ↥K := by
      intro k hk
      rw [MonoidHom.mem_ker, hΔ] at hk
      rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      have hx : (k : X) = (a ^ 2 * k * (a ^ 2)⁻¹)⁻¹ * (a * k * a⁻¹)⁻¹ := by
        calc (k : X) = ((k : X) * (a * k * a⁻¹) * (a ^ 2 * k * (a ^ 2)⁻¹)) *
              (a ^ 2 * k * (a ^ 2)⁻¹)⁻¹ * (a * k * a⁻¹)⁻¹ := by group
          _ = _ := by rw [hk, one_mul]
      have cz1 : Commute (z : X) (a * k * a⁻¹) := hc01 z z.2 _ (hm1 k k.2)
      have cz2 : Commute (z : X) (a ^ 2 * k * (a ^ 2)⁻¹) := hc02 z z.2 _ (hm2 k k.2)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hx]
      exact (cz2.inv_right.mul_right cz1.inv_right).eq
    have hΔC : ∀ k : K, Δ k ∈ C := fun k => by
      rw [hΔ]
      exact C.mul_mem (C.mul_mem (hKC k.2) (C.mul_mem (C.mul_mem haC (hKC k.2)) (C.inv_mem haC)))
        (C.mul_mem (C.mul_mem (pow_mem haC 2) (hKC k.2)) (C.inv_mem (pow_mem haC 2)))
    have hΔa : ∀ k : K, a * Δ k = Δ k * a := by
      intro k
      have c1 : (k : X) * (a * k * a⁻¹) = (a * k * a⁻¹) * k := hc01 k k.2 _ (hm1 k k.2)
      have c2 : (k : X) * (a ^ 2 * k * (a ^ 2)⁻¹) = (a ^ 2 * k * (a ^ 2)⁻¹) * k :=
        hc02 k k.2 _ (hm2 k k.2)
      have ha3' : a * a ^ 2 = 1 := by rw [← pow_succ', ha3]
      rw [hΔ]
      calc a * ((k : X) * (a * k * a⁻¹) * (a ^ 2 * k * (a ^ 2)⁻¹))
          = (a * k * a⁻¹) * (a ^ 2 * k * (a ^ 2)⁻¹) * ((a * a ^ 2) * k * (a * a ^ 2)⁻¹) * a := by
            group
        _ = (a * k * a⁻¹) * ((a ^ 2 * k * (a ^ 2)⁻¹) * k) * a := by rw [ha3']; group
        _ = (a * k * a⁻¹) * ((k : X) * (a ^ 2 * k * (a ^ 2)⁻¹)) * a := by rw [c2]
        _ = ((a * k * a⁻¹) * k) * (a ^ 2 * k * (a ^ 2)⁻¹) * a := by group
        _ = ((k : X) * (a * k * a⁻¹)) * (a ^ 2 * k * (a ^ 2)⁻¹) * a := by rw [c1]
    have hΔB : ∀ k : K, ∀ b ∈ B₀, b * Δ k = Δ k * b := by
      intro k b hb
      have hba : Commute b a := hAcomm b (hA₀A (hB₀A₀ hb)) a haA
      have hbk : Commute b (k : X) := hB₀K b hb k k.2
      have h1 : Commute b (a * k * a⁻¹) := (hba.mul_right hbk).mul_right hba.inv_right
      have hba2 : Commute b (a ^ 2) := hba.pow_right 2
      have h2 : Commute b (a ^ 2 * k * (a ^ 2)⁻¹) := (hba2.mul_right hbk).mul_right hba2.inv_right
      rw [hΔ]
      exact ((hbk.mul_right h1).mul_right h2).eq
    set H₁ := B₀ ⊔ Subgroup.zpowers a with hH₁def
    have hH₁A : H₁ ≤ A := sup_le (hB₀A₀.trans hA₀A) (Subgroup.zpowers_le.2 haA)
    have hAeq : Subgroup.zpowers a ⊔ A₀ = A := by
      rw [sup_comm]
      exact le_antisymm (sup_le hA₀A (Subgroup.zpowers_le.2 haA)) hA1
    have hnA₀ : Subgroup.zpowers a ≤ Subgroup.normalizer (A₀ : Set X) := Subgroup.zpowers_le.2
      (mem_normalizer_of_forall_commute fun n hn => hAcomm a haA n (hA₀A hn))
    have hnB₀ : Subgroup.zpowers a ≤ Subgroup.normalizer (B₀ : Set X) := Subgroup.zpowers_le.2
      (mem_normalizer_of_forall_commute fun n hn => hAcomm a haA n (hA₀A (hB₀A₀ hn)))
    have h3A : A₀.relIndex A = 3 := by
      rw [← hAeq]
      exact relIndex_sup_zpowers_eq_three ha3 haA₀ hnA₀
    have h3H : B₀.relIndex H₁ = 3 := by
      rw [hH₁def, sup_comm]
      exact relIndex_sup_zpowers_eq_three ha3 (fun h => haA₀ (hB₀A₀ h)) hnB₀
    have hidx : H₁.relIndex A ∣ 3 := by
      have t1 := Subgroup.relIndex_mul_relIndex B₀ A₀ A hB₀A₀ hA₀A
      have t2 := Subgroup.relIndex_mul_relIndex B₀ H₁ A le_sup_left hH₁A
      rw [h3A] at t1
      rw [h3H] at t2
      have : H₁.relIndex A = B₀.relIndex A₀ := by omega
      rw [this]
      exact hB₀
    refine false_of_pow_eighteen ⟨e⟩ Δ hker fun k => ?_
    refine pow_eighteen_of_relIndex hcomm hpow hinj hstd hhyp hH₁A hidx (hΔC k) fun h hh => ?_
    have hle : H₁ ≤ Subgroup.centralizer {Δ k} := by
      refine sup_le (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (hΔB k b hb)) ?_
      exact Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hΔa k))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hh)
  ·
    obtain ⟨b, hbA, hbN⟩ := Set.not_subset.1 hA1
    have hb3 : b ^ 3 = 1 := hA3 b hbA
    have hab : Commute a b := hAcomm a haA b hbA
    let c : Fin 3 × Fin 3 → X := fun p => a ^ p.1.val * b ^ p.2.val
    have hcA : ∀ p, c p ∈ A := fun p => mul_mem (pow_mem haA _) (pow_mem hbA _)
    let H : Fin 3 × Fin 3 → Subgroup X := fun p => K.map (MulAut.conj (c p) : X →* X)
    have hH : ∀ p, CFSG.Open.IsComponentOf (H p) C := fun p =>
      isComponentOf_map_conj_of_mem_k hK (hAC (hcA p))
    haveI : ∀ p, Finite (H p) := fun p =>
      Finite.of_injective (Subgroup.inclusion (hH p).1) (Subgroup.inclusion_injective _)
    have hdist : ∀ p q, H p = H q → p = q := by
      intro p q hpq
      have hn := mem_normalizer_of_map_conj_eq_k hpq
      have hnA₀ : (c p)⁻¹ * c q ∈ A₀ :=
        Subgroup.mem_inf.2 ⟨A.mul_mem (A.inv_mem (hcA p)) (hcA q), hn⟩
      have e1 : (c p)⁻¹ * c q = a ^ (q.1.val + 2 * p.1.val) * b ^ (q.2.val + 2 * p.2.val) :=
        inv_mul_eq_pow_mul_pow hab ha3 hb3 _ _ _ _
      rw [e1] at hnA₀
      obtain ⟨h1, h2⟩ := mod_three_eq_zero_of_mem ha3 hb3 haA₀ hbN hnA₀
      have hp1 := p.1.isLt
      have hp2 := p.2.isLt
      have hq1 := q.1.isLt
      have hq2 := q.2.isLt
      ext <;> omega
    have hcomm' : Pairwise fun p q => ∀ x y : X, x ∈ H p → y ∈ H q → Commute x y := by
      intro p q hpq x y hx hy
      exact CFSG.LocalAnalysis.GLTheoremA.I142.components_commute_of_ne (hH p) (hH q)
        (fun h => hpq (hdist p q h)) x hx y hy
    have hA5' : ∀ p, Nonempty ((↥(H p) ⧸ Subgroup.center ↥(H p)) ≃* alternatingGroup (Fin 5)) :=
      fun p => ⟨(QuotientGroup.congr _ _ (K.equivMapOfInjective _ (MulAut.conj (c p)).injective)
        (Subgroup.map_center_eq _)).symm.trans e⟩
    have h60 := sixty_pow_dvd_of_pairwise_commute H hcomm' (fun p => (hH p).1) hA5'
    rw [show Fintype.card (Fin 3 × Fin 3) = 9 by rfl] at h60
    exact h5 ((pow_dvd_pow_of_dvd (by norm_num : 5 ∣ 60) 9).trans h60)

end Main

section Leaf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3


variable {τ : Tag} {k : Type} [Field k]

theorem pow_eighteen_of_mem_familyCentralizer {G : Subgroup (ModGL τ k)} {ω : kˣ}
    {kb : List (List ℕ)} (hX3 : ∀ g ∈ G, g ∈ torusGroup τ k → g ^ 3 = 1)
    (hcase : (familyKernel (famV (τ := τ) ω kb) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1) ∨
      ∃ α, IsRoot τ α ∧ familyKernel (famV (τ := τ) ω kb) = {α, -α} ∧
        (∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1 ∨ w = rootReflection α) ∧
        (∀ g ∈ G, g ∈ torusGroup τ k ⊔ rootSpan τ k {α, -α} → g ^ 3 ∈ rootSpan τ k {α, -α}) ∧
        ∀ g ∈ G, g ∈ rootSpan τ k {α, -α} → g ^ 6 = 1)
    {g : ModGL τ k} (hgG : g ∈ G) (hgC : g ∈ familyCentralizer τ k (famV (τ := τ) ω kb)) :
    g ^ 18 = 1 := by
  obtain ⟨w, hw, m, hm, he⟩ := familyCentralizer_le_mul τ k (famV (τ := τ) ω kb) hgC
  rcases hcase with ⟨hK, hW⟩ | ⟨α, hα, hK, hW, hX4, hX6⟩
  · rw [hW w hw, canonicalRep_one, mul_one] at he
    have hmT : m ∈ torusGroup τ k := by
      have hm' : m ∈ torusGroup τ k ⊔ rootSpan τ k (familyKernel (famV (τ := τ) ω kb)) := hm
      rw [hK] at hm'
      have hbot : rootSpan τ k (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
      rwa [hbot, sup_bot_eq] at hm'
    have h3 := hX3 g hgG (he ▸ hmT)
    rw [show (18 : ℕ) = 3 * 6 by norm_num, pow_mul, h3, one_pow]
  · have hmM : m ∈ torusGroup τ k ⊔ rootSpan τ k {α, -α} := by
      have hm' : m ∈ torusGroup τ k ⊔ rootSpan τ k (familyKernel (famV (τ := τ) ω kb)) := hm
      rwa [hK] at hm'
    have hgM : g ∈ torusGroup τ k ⊔ rootSpan τ k {α, -α} := by
      rw [he]
      rcases hW w hw with rfl | rfl
      · rwa [canonicalRep_one, mul_one]
      · exact mul_mem hmM (canonicalRep_rootReflection_mem hα)
    have h6 := hX6 (g ^ 3) (pow_mem hgG 3) (hX4 g hgG hgM)
    rw [show (18 : ℕ) = 3 * 6 by norm_num, pow_mul, h6]

theorem sq_eq_one_of_antidiag_charTwo {L : Type} [Field L] [CharP L 2]
    {A : Matrix.SpecialLinearGroup (Fin 2) L}
    (h0 : (A : Matrix (Fin 2) (Fin 2) L) 0 0 = 0) (h1 : (A : Matrix (Fin 2) (Fin 2) L) 1 1 = 0) :
    A ^ 2 = 1 := by
  obtain ⟨b, c, hAm⟩ : ∃ b c : L, (A : Matrix (Fin 2) (Fin 2) L) = !![0, b; c, 0] :=
    ⟨(A : Matrix (Fin 2) (Fin 2) L) 0 1, (A : Matrix (Fin 2) (Fin 2) L) 1 0, by
      conv_lhs => rw [Matrix.eta_fin_two (A : Matrix (Fin 2) (Fin 2) L)]
      rw [h0, h1]⟩
  have hdet : -(b * c) = 1 := by
    have := A.2
    rw [hAm, Matrix.det_fin_two_of] at this
    linear_combination this
  have hbc : b * c = 1 := by
    rw [← hdet, CharTwo.neg_eq]
  have hcb : c * b = 1 := by rw [mul_comm]; exact hbc
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hAm, sq, Matrix.SpecialLinearGroup.coe_one,
    Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hbc, hcb]

variable {L : Type} [Field L] [CharP L 2]

theorem pow_six_eq_one_of_twFix (F : ModGL τ L →* ModGL τ L) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) {μ : Lˣ}
    (hμ : ∀ A : Matrix.SpecialLinearGroup (Fin 2) L, F (rootSL2 τ L α A) = rootSL2 τ L α
      (conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A)))
    {g : ModGL τ L} (hgF : F g = g) (hgL : g ∈ rootSpan τ L {α, -α}) : g ^ 6 = 1 := by
  have hspan : rootSpan τ L {α, -α} = (rootSL2 τ L α).range := by
    rw [range_rootSL2_of_isRoot hα, rootSpan, iSup_insert, iSup_singleton]
  obtain ⟨A, rfl⟩ : g ∈ (rootSL2 τ L α).range := hspan ▸ hgL
  have hAfix : conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
      (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A) = A :=
    rootSL2_injective_of_field (τ := τ) (K := L) α ((hμ A).symm.trans hgF)
  have hA6 : A ^ 6 = 1 := by
    rcases twFix_cases hAfix with h3 | ⟨h0, h1⟩
    · rw [show (6 : ℕ) = 3 * 2 by norm_num, pow_mul, h3, one_pow]
    · rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, sq_eq_one_of_antidiag_charTwo h0 h1, one_pow]
  rw [← map_pow, hA6, map_one]

end Leaf

section TwModel

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3


variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem mem_familyCentralizer_of_commute {ω : Lˣ} {kb : List (List ℕ)} {g : ModGL τ L}
    (hgC : g ∈ adjointGroup τ L)
    (h : ∀ b ∈ kb, dV ω (listVec τ.rank b) * g = g * dV ω (listVec τ.rank b)) :
    g ∈ familyCentralizer τ L (famV (τ := τ) ω kb) := by
  rw [mem_familyCentralizer]
  refine ⟨hgC, fun j => ?_⟩
  change dV ω (listVec τ.rank (kb.get j)) * g * (dV ω (listVec τ.rank (kb.get j)))⁻¹ = g
  rw [h _ (List.get_mem kb j), mul_assoc, mul_inv_cancel, mul_one]

variable {w₀ : WeylGroup τ}

theorem false_of_comp_twModel (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (htorL : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    {G : Subgroup (ModGL τ L)} [Finite G]
    (hGW : G ≤ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1))
    {ω : Lˣ} (hω : orderOf ω = 3) (hG : ∀ x, dV (τ := τ) ω x ∈ G)
    (hcert : Native.hypOK τ = true) (h5 : ¬ 5 ^ 9 ∣ Nat.card G) {t : ModGL τ L}
    (ht : ∀ x, dV (τ := τ) ω x * t = t * dV ω x) {K : Subgroup G}
    (hK : CFSG.Open.IsComponentOf K ((Subgroup.centralizer ({t} : Set (ModGL τ L))).subgroupOf G))
    (hA5 : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))) : False := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  set d : Fin τ.rank → G := genG hG with hd
  have hcomm := genG_comm hω3 hG
  have hpow := genG_pow hω3 hG
  set φ := vecProdHom (genG hG) hcomm hpow with hφdef
  have hφ : ∀ a, φ (Multiplicative.ofAdd a) = dG hG a := fun a => vecProd_genG hω3 hG a
  have hinj : Function.Injective φ := by
    intro a b h
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, hφ, hφ] at h
    have := dV_injective (τ := τ) hω (congrArg Subtype.val h)
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, this]
  have hGC : G ≤ adjointGroup τ L := hGW.trans inf_le_left
  have hX3 : ∀ g ∈ G, g ∈ torusGroup τ L → g ^ 3 = 1 := fun g hg hgT =>
    pow_three_of_mem_twModel htorL hw₀ (hGW hg) hgT
  have hleaf : ∀ kb : List (List ℕ), (∀ b ∈ kb, b.length = τ.rank) → (∀ b ∈ kb, ∀ x ∈ b, x < 3) →
      ((familyKernel (famV (τ := τ) ω kb) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1) ∨
      ∃ α, IsRoot τ α ∧ familyKernel (famV (τ := τ) ω kb) = {α, -α} ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω kb), w = 1 ∨ w = rootReflection α) →
      ∀ x : G, (∀ b ∈ kb, dV ω (listVec τ.rank b) * x = x * dV ω (listVec τ.rank b)) →
        x ^ 18 = 1 := by
    intro kb _ _ hdata x hx
    have hxC := mem_familyCentralizer_of_commute (hGC x.2) hx
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine pow_eighteen_of_mem_familyCentralizer hX3 ?_ x.2 hxC
    rcases hdata with h | ⟨α, hα, hker, hW⟩
    · exact Or.inl h
    · obtain ⟨μ, hμ⟩ := exists_twFrob_rootSL2 (L := L) hw₀ hα
      refine Or.inr ⟨α, hα, hker, hW, fun g hg hgTL => pow_three_mem_rootSpan_two hw₀ hα
        (hGW hg) hgTL, fun g hg hgL => ?_⟩
      exact pow_six_eq_one_of_twFix
        ((MulAut.conj (canonicalRep (coxeterSystem τ) L w₀)).toMonoidHom.comp
          (Units.map (entrywiseHom (iterateFrobenius L 2 1)))) hα hμ (hGW hg).2 hgL
  set C : Subgroup G := (Subgroup.centralizer ({t} : Set (ModGL τ L))).subgroupOf G with hCdef
  have hAC : φ.range ≤ C := by
    rintro _ ⟨a, rfl⟩
    rw [← ofAdd_toAdd a, hφ, hCdef, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    exact ht _
  refine false_of_torus_comp hcomm hpow hinj hAC hK hA5 ?_ ?_ ?_
  ·
    intro x _ hx
    refine hleaf (Native.stdBasis τ.rank) length_of_mem_stdBasis lt_of_mem_stdBasis
      (Or.inl (famData0_of_famOK0 hω length_of_mem_stdBasis lt_of_mem_stdBasis
        (famOK_std_of_hypOK hcert))) x fun b _ => ?_
    have h1 := hx (dG hG (listVec τ.rank b)) ⟨Multiplicative.ofAdd _, hφ _⟩
    exact congrArg Subtype.val h1
  ·
    intro fl hfl x _ hx
    refine hleaf (kerBasis 3 fl) (length_of_mem_kerBasis hfl) lt_of_mem_kerBasis
      (famData_of_famOK hω (length_of_mem_kerBasis hfl) lt_of_mem_kerBasis
        (famOK_of_hypOK hcert hfl)) x fun b hb => ?_
    have h1 := hx b hb
    rw [vecProd_genG hω3 hG] at h1
    exact congrArg Subtype.val h1
  · intro h
    exact h5 (h.trans (Subgroup.card_subgroup_dvd_card C))

end TwModel

section SubTorus

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3


variable {τ : Tag} {L : Type} [Field L] [CharP L 2]

theorem false_of_comp_sub (F : ModGL τ L →* ModGL τ L)
    (hFT : ∀ a : Fin τ.rank → Lˣ, F (rootDiagUnit τ a) = (rootDiagUnit τ a)⁻¹ ^ 2)
    (hFα : ∀ α : Fin τ.rank → ℤ, IsRoot τ α → ∃ μ : Lˣ, ∀ A : Matrix.SpecialLinearGroup (Fin 2) L,
      F (rootSL2 τ L α A) = rootSL2 τ L α (conjSL (RankThree.Classical.swapGL * diagUnitOne μ)
        (Matrix.SpecialLinearGroup.map (iterateFrobenius L 2 1) A)))
    {G : Subgroup (ModGL τ L)} [Finite G] (hGF : G ≤ fixModel F)
    {ω : Lˣ} (hω : orderOf ω = 3) {m : ℕ} {e : Fin m → Fin τ.rank → ZMod 3}
    (he : ∀ i, dV (τ := τ) ω (e i) ∈ G) (heinj : Function.Injective (subLin (τ := τ) e))
    (hdata : ∀ fl ∈ normVecs 3 m,
      (familyKernel (famV (τ := τ) ω ((kerBasis 3 fl).map (liftL e))) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω ((kerBasis 3 fl).map (liftL e))), w = 1) ∨
      ∃ α, IsRoot τ α ∧ familyKernel (famV (τ := τ) ω ((kerBasis 3 fl).map (liftL e))) = {α, -α} ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω ((kerBasis 3 fl).map (liftL e))),
          w = 1 ∨ w = rootReflection α)
    (hdata0 : familyKernel (famV (τ := τ) ω ((Native.stdBasis m).map (liftL e))) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω ((Native.stdBasis m).map (liftL e))), w = 1)
    (h5 : ¬ 5 ^ 9 ∣ Nat.card G) {t : ModGL τ L}
    (ht : ∀ y, dV (τ := τ) ω (subLin e y) * t = t * dV ω (subLin e y)) {K : Subgroup G}
    (hK : CFSG.Open.IsComponentOf K ((Subgroup.centralizer ({t} : Set (ModGL τ L))).subgroupOf G))
    (hA5 : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 5))) : False := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hcomm := genS_comm hω3 he
  have hpow := genS_pow hω3 he
  set φ := vecProdHom (genS he) hcomm hpow with hφdef
  have hφ : ∀ a, φ (Multiplicative.ofAdd a) = dS hω3 he a := fun a => vecProd_genS hω3 he a
  have hinj : Function.Injective φ := by
    intro a b h
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, hφ, hφ] at h
    have := heinj (dV_injective (τ := τ) hω (congrArg Subtype.val h))
    rw [← ofAdd_toAdd a, ← ofAdd_toAdd b, this]
  have hGC : G ≤ adjointGroup τ L := hGF.trans inf_le_left
  have hX3 : ∀ g ∈ G, g ∈ torusGroup τ L → g ^ 3 = 1 := by
    intro g hg hgT
    obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom hgT
    have hF : F (rootDiagUnit τ a) = rootDiagUnit τ a := (hGF hg).2
    rw [hFT, inv_pow] at hF
    change rootDiagUnit τ a ^ 3 = 1
    rw [pow_succ]
    exact inv_eq_iff_mul_eq_one.1 hF
  have hleaf : ∀ kb : List (List ℕ),
      ((familyKernel (famV (τ := τ) ω (kb.map (liftL e))) = ∅ ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω (kb.map (liftL e))), w = 1) ∨
      ∃ α, IsRoot τ α ∧ familyKernel (famV (τ := τ) ω (kb.map (liftL e))) = {α, -α} ∧
        ∀ w ∈ familyStabilizer (famV (τ := τ) ω (kb.map (liftL e))), w = 1 ∨
          w = rootReflection α) →
      ∀ x : G, (∀ b ∈ kb, dS hω3 he (listVec m b) * x = x * dS hω3 he (listVec m b)) →
        x ^ 18 = 1 := by
    intro kb hdat x hx
    have hxC : (x : ModGL τ L) ∈ familyCentralizer τ L (famV (τ := τ) ω (kb.map (liftL e))) := by
      refine mem_familyCentralizer_of_commute (hGC x.2) fun b hb => ?_
      obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
      rw [listVec_liftL]
      exact congrArg Subtype.val (hx b' hb')
    refine Subtype.ext ?_
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine pow_eighteen_of_mem_familyCentralizer hX3 ?_ x.2 hxC
    rcases hdat with h | ⟨α, hα, hker, hW⟩
    · exact Or.inl h
    · obtain ⟨μ, hμ⟩ := hFα α hα
      refine Or.inr ⟨α, hα, hker, hW, fun g hg hgTL => ?_, fun g hg hgL =>
        pow_six_eq_one_of_twFix F hα hμ (hGF hg).2 hgL⟩
      exact pow_three_mem_rootSpan_tw F hFT hα hμ (hGF hg) hgTL
  set C : Subgroup G := (Subgroup.centralizer ({t} : Set (ModGL τ L))).subgroupOf G with hCdef
  have hAC : φ.range ≤ C := by
    rintro _ ⟨a, rfl⟩
    rw [← ofAdd_toAdd a, hφ, hCdef, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ht _
  refine false_of_torus_comp hcomm hpow hinj hAC hK hA5 ?_ ?_ ?_
  · intro x _ hx
    exact hleaf (Native.stdBasis m) (Or.inl hdata0) x fun b _ =>
      hx (dS hω3 he (listVec m b)) ⟨Multiplicative.ofAdd _, hφ _⟩
  · intro fl hfl x _ hx
    refine hleaf (kerBasis 3 fl) (hdata fl hfl) x fun b hb => ?_
    have h1 := hx b hb
    rwa [vecProd_genS hω3 he] at h1
  · intro h
    exact h5 (h.trans (Subgroup.card_subgroup_dvd_card C))

end SubTorus

section Transport

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem fixSubgroup_congr_k {S T : Type*} [Group S] [Group T] (e : S ≃* T) (β : MulAut S) :
    fixSubgroup (MulAut.congr e β) = (fixSubgroup β).map (e : S →* T) := by
  ext x
  rw [mem_fixSubgroup]
  refine Iff.trans ?_ (Subgroup.mem_map_equiv (f := e)).symm
  rw [mem_fixSubgroup]
  show e (β (e.symm x)) = x ↔ β (e.symm x) = e.symm x
  exact e.eq_symm_apply.symm

theorem congr_conj_k {S T : Type*} [Group S] [Group T] (e : S ≃* T) (t : S) :
    MulAut.congr e (MulAut.conj t) = MulAut.conj (e t) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem fixSubgroup_conj_eq_subgroupOf {G : Type*} [Group G] {M : Subgroup G} (y : M) :
    fixSubgroup (MulAut.conj y) = (Subgroup.centralizer ({(y : G)} : Set G)).subgroupOf M := by
  ext z
  rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    MulAut.conj_apply]
  constructor
  · intro h
    have h1 : ((y * z * y⁻¹ : M) : G) = z := congrArg Subtype.val h
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h1
    calc (z : G) * y = y * z * (y : G)⁻¹ * y := by rw [h1]
      _ = y * z := by group
  · intro h
    apply Subtype.ext
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [← h]
    group

theorem nonempty_a5_map {S T : Type*} [Group S] [Group T] (e : S ≃* T) {J : Subgroup S}
    (hA5 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5))) :
    Nonempty ((↥(J.map (e : S →* T)) ⧸ Subgroup.center ↥(J.map (e : S →* T))) ≃*
      alternatingGroup (Fin 5)) := by
  obtain ⟨f⟩ := hA5
  exact ⟨(QuotientGroup.congr _ _ (J.equivMapOfInjective (e : S →* T) e.injective)
    (Subgroup.map_center_eq _)).symm.trans f⟩

end Transport

section InnerTwModel

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)


variable {τ : Tag} {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {w₀ : WeylGroup τ}

theorem false_of_inner_twModel (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (htorL : ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ torusGroup τ L)
    {M : Subgroup (ModGL τ L)} [Finite M]
    (hMW : M ≤ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1))
    (hnorm : ∀ u ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1),
      ∀ m ∈ M, u * m * u⁻¹ ∈ M)
    (h3 : ∀ g ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1),
      g ^ 3 = 1 → g ∈ M)
    {ω : Lˣ} (hω : orderOf ω = 3)
    (hfus : ∀ s ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1),
      s ^ 3 = 1 → ∃ u ∈ twModel (canonicalRep (coxeterSystem τ) L w₀) (iterateFrobenius L 2 1),
        ∃ x : Fin τ.rank → ZMod 3, u * s * u⁻¹ = dV ω x)
    (hcert : Native.hypOK τ = true) (h5 : ¬ 5 ^ 9 ∣ Nat.card M)
    {X : Type*} [Group X] (e : X ≃* M) {t₀ : X} (ht₀ : t₀ ^ 3 = 1) {J : Subgroup X}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj t₀)))
    (hA5 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5))) : False := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hs3 : ((e t₀ : M) : ModGL τ L) ^ 3 = 1 := by
    have h1 : (e t₀) ^ 3 = 1 := by rw [← map_pow, ht₀, map_one]
    have := congrArg (fun m : M => (m : ModGL τ L)) h1
    simpa using this
  obtain ⟨u, huW, x, hux⟩ := hfus _ (hMW (e t₀).2) hs3
  have hmem : ∀ m : M, u⁻¹ * m * u ∈ M := fun m => by
    have := hnorm u⁻¹ (inv_mem huW) m m.2
    rwa [inv_inv] at this
  let ψ : M ≃* M :=
    { toFun := fun m => ⟨u * m * u⁻¹, hnorm u huW m m.2⟩
      invFun := fun m => ⟨u⁻¹ * m * u, hmem m⟩
      left_inv := fun m => Subtype.ext (by simp [mul_assoc])
      right_inv := fun m => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun m m' => Subtype.ext (by simp [mul_assoc]) }
  set θ : X ≃* M := e.trans ψ with hθ
  have hθt : ((θ t₀ : M) : ModGL τ L) = dV ω x := hux
  have hG : ∀ y, dV (τ := τ) ω y ∈ M := fun y =>
    h3 _ (dV_mem_twModel htorL hw₀ hω3 y) (dV_pow_three hω3 y)
  have hJ' := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map θ hJ
  rw [← fixSubgroup_congr_k, congr_conj_k, fixSubgroup_conj_eq_subgroupOf, hθt] at hJ'
  refine false_of_comp_twModel hw₀ htorL hMW hω hG hcert h5 (t := dV ω x) (fun y => ?_) hJ'
    (nonempty_a5_map θ hA5)
  rw [← dV_add hω3, ← dV_add hω3, add_comm]

end InnerTwModel

section Groups

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)


variable {K : Type} [Field K] [Finite K]

theorem not_dvd_ordF4_two : ¬ 5 ^ 9 ∣ CFSG.Open.ordF4 2 := by
  unfold CFSG.Open.ordF4
  norm_num

theorem not_dvd_ordE7_two : ¬ 5 ^ 9 ∣ CFSG.Open.ordE7 2 := by
  unfold CFSG.Open.ordE7
  norm_num

theorem not_dvd_ordE8_two : ¬ 5 ^ 9 ∣ CFSG.Open.ordE8 2 := by
  unfold CFSG.Open.ordE8
  norm_num

theorem noA5Comp_inner_F4_two
    (hK : Nat.card K = 2) {t₀ : adjointGroup Tag.F4 K} (ht₀ : t₀ ^ 3 = 1)
    {J : Subgroup (adjointGroup Tag.F4 K)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj t₀))) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  intro hA5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_two hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ :=
    exists_lang_data Tag.F4 K CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 1 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_two_one]
  subst hFr2
  set W := twModel (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K)
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg)
    (iterateFrobenius (AlgebraicClosure K) 2 1) with hW
  have : Finite W := finite_twModel hg0C hg0
  set e := twModelEquivF4 K (AlgebraicClosure K) hFr hg0C hg0 with he
  have htorL : ∀ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ,
      rootDiagUnit Tag.F4 a ∈ torusGroup Tag.F4 (AlgebraicClosure K) :=
    rootDiagUnit_mem_torusGroup_of_unimodular
      CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_mul_cartan_F4.choose_spec
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one K (L := AlgebraicClosure K) (N := 3)
    (by rw [hK])
  have hLang : ∀ a : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.F4 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.F4 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.F4
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K)
            CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg) z = c := fun a ha3 c hc =>
    toral_centralizer_Lang_F4_three 2 (AlgebraicClosure K) (by norm_num) a ha3 1 le_rfl
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul ha3)
        c hc
  have hcard : Nat.card W = CFSG.Open.ordF4 2 := by
    rw [← Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hK]
  exact false_of_inner_twModel CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul htorL
    (M := W) le_rfl
    (fun u hu m hm => mul_mem (mul_mem hu hm) (inv_mem hu)) (fun g hg _ => hg) hω
    (fun s hs hs3 => exists_conj_dV_twModel (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
      (monomialToralAt_three_of_block a2BlockToral_F4)
      CFSG.HardMathSupport.Timmesfeld.CrossChar.f4Neg_smul hLang hω hs hs3)
    Certificates.certificate13666.1 (by rw [hcard]; exact not_dvd_ordF4_two) e ht₀ hJ hA5

theorem noA5Comp_inner_E8_two
    (hK : Nat.card K = 2) {t₀ : adjointGroup Tag.E8 K} (ht₀ : t₀ ^ 3 = 1)
    {J : Subgroup (adjointGroup Tag.E8 K)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj t₀))) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  intro hA5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_two hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.E8 K e8Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 1 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_two_one]
  subst hFr2
  have hMW := langModel_le_twModel Tag.E8 K (AlgebraicClosure K) hFr hg0C hg0
  have : Finite (twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
      (iterateFrobenius (AlgebraicClosure K) 2 1)) := finite_twModel hg0C hg0
  have hWM := le_langModel_E8_of_le_twModel K (AlgebraicClosure K) hFr hg0C hg0 (P :=
    twModel (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K) e8Neg)
      (iterateFrobenius (AlgebraicClosure K) 2 1)) le_rfl
  have : Finite (langModel Tag.E8 K (AlgebraicClosure K) g0) :=
    finite_langModel Tag.E8 K (AlgebraicClosure K) g0
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one K (L := AlgebraicClosure K) (N := 3)
    (by rw [hK])
  have hLang : ∀ a : Fin Tag.E8.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.E8 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.E8 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.E8
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.E8) (AlgebraicClosure K)
            e8Neg) z = c := fun a ha3 c hc =>
    toral_centralizer_Lang_E8_three 2 (AlgebraicClosure K) (by norm_num) a ha3 1 le_rfl
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq e8Neg_smul ha3) c hc
  have hcard : Nat.card (langModel Tag.E8 K (AlgebraicClosure K) g0) = CFSG.Open.ordE8 2 := by
    rw [← Nat.card_congr (langModelEquiv Tag.E8 K (AlgebraicClosure K) g0).toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E8, hK]
  exact false_of_inner_twModel e8Neg_smul rootDiagUnit_mem_torusGroup_E8 hMW
    (fun u hu m hm => hWM (mul_mem (mul_mem hu (hMW hm)) (inv_mem hu))) (fun g hg _ => hWM hg) hω
    (fun s hs hs3 => exists_conj_dV_twModel (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
      (monomialToralAt_three_of_block a2BlockToral_E8) e8Neg_smul hLang hω hs hs3)
    Certificates.certificate13666.2.2.1 (by rw [hcard]; exact not_dvd_ordE8_two)
    (langModelEquiv Tag.E8 K (AlgebraicClosure K) g0) ht₀ hJ hA5

theorem noA5Comp_inner_E7_two
    (hK : Nat.card K = 2) {t₀ : adjointGroup Tag.E7 K} (ht₀ : t₀ ^ 3 = 1)
    {J : Subgroup (adjointGroup Tag.E7 K)}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup (MulAut.conj t₀))) :
    ¬ Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5)) := by
  intro hA5
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_two hK
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, g0, hg0C, hg0⟩ := exists_lang_data Tag.E7 K e7Neg
  have hFr2 : Fr = iterateFrobenius (AlgebraicClosure K) 2 1 :=
    RingHom.ext fun c => by rw [hFr, hK, iterateFrobenius_two_one]
  subst hFr2
  set W := twModel (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K) e7Neg)
    (iterateFrobenius (AlgebraicClosure K) 2 1) with hW
  set M := e7Model K (AlgebraicClosure K) g0 with hM
  have hMW : M ≤ W := e7Model_le_twModel K (AlgebraicClosure K) hFr hg0C hg0
  have : Finite W := finite_twModel hg0C hg0
  have : Finite M := finite_e7Model K (AlgebraicClosure K) g0
  have hd : M.relIndex W ∣ 2 := by
    set X := W.map (MulAut.conj g0).toMonoidHom with hX
    have : Finite X := Finite.of_surjective ((MulAut.conj g0).toMonoidHom.subgroupMap W)
      ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective W)
    have hXF := map_conj_twModel hg0C hg0
    have hdesc := (finite_fixed_subgroup_rational_perfect 2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
      (iterateFrobenius (AlgebraicClosure K) 2 1) hFr X (fun x hx => by
        rw [hX, hXF] at hx
        exact hx.1) (fun x hx => by
        rw [hX, hXF] at hx
        exact hx.2)).1
    have hcomp : (MulAut.conj g0).toMonoidHom.comp (MulAut.conj g0⁻¹).toMonoidHom =
        MonoidHom.id _ := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    have hMX : M.map (MulAut.conj g0).toMonoidHom =
        (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
      rw [hM, e7Model, Subgroup.map_map, hcomp, Subgroup.map_id]
    rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g0).toMonoidHom) _ _
      (MulAut.conj g0).injective, hMX]
    exact hdesc
  obtain ⟨hnorm, h3⟩ := normal_of_relIndex_dvd_two hMW hd
  obtain ⟨ω, hω, -⟩ := exists_orderOf_eq_of_dvd_add_one K (L := AlgebraicClosure K) (N := 3)
    (by rw [hK])
  have hLang : ∀ a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ, (∀ i, a i ^ 3 = 1) →
      ∀ c ∈ toralCentralizer Tag.E7 (AlgebraicClosure K) a,
        ∃ z ∈ toralCentralizer Tag.E7 (AlgebraicClosure K) a, z⁻¹ * frobTwistGL Tag.E7
          (AlgebraicClosure K) 2 1 (canonicalRep (coxeterSystem Tag.E7) (AlgebraicClosure K)
            e7Neg) z = c := fun a ha3 c hc =>
    toral_centralizer_Lang_E7_three 2 (AlgebraicClosure K) (by norm_num) a ha3 1 le_rfl
      (canonicalRep_mem_adjointGroup _ _ _) (s := 2) (by norm_num)
      (canonicalRep_conj_rootDiagUnit_sq e7Neg_smul ha3) c hc
  have hcard : Nat.card M = CFSG.Open.ordE7 2 := by
    rw [← Nat.card_congr (e7ModelEquiv K (AlgebraicClosure K) g0).toEquiv,
      CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hK]
  exact false_of_inner_twModel e7Neg_smul rootDiagUnit_mem_torusGroup_E7 hMW hnorm h3 hω
    (fun s hs hs3 => exists_conj_dV_twModel (isAlgebraic_zmod_algebraicClosure_of_finite K 2)
      (monomialToralAt_three_of_block a2BlockToral_E7) e7Neg_smul hLang hω hs hs3)
    Certificates.certificate13666.2.1 (by rw [hcard]; exact not_dvd_ordE7_two)
    (e7ModelEquiv K (AlgebraicClosure K) g0) ht₀ hJ hA5

end Groups

section TwE6Model

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ3

@[expose] noncomputable def conjOfNormalizes {X : Type*} [Group X] (Γ : Subgroup X) (m : X)
    (h1 : ∀ x ∈ Γ, m * x * m⁻¹ ∈ Γ) (h2 : ∀ x ∈ Γ, m⁻¹ * x * m ∈ Γ) : Γ ≃* Γ where
  toFun x := ⟨m * x * m⁻¹, h1 x x.2⟩
  invFun x := ⟨m⁻¹ * x * m, h2 x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem map_conjOfNormalizes_centralizer {X : Type*} [Group X] (Γ : Subgroup X) (m : X)
    (h1 : ∀ x ∈ Γ, m * x * m⁻¹ ∈ Γ) (h2 : ∀ x ∈ Γ, m⁻¹ * x * m ∈ Γ) (u : X) :
    ((Subgroup.centralizer ({u} : Set X)).subgroupOf Γ).map
        (conjOfNormalizes Γ m h1 h2 : Γ →* Γ) =
      (Subgroup.centralizer ({m * u * m⁻¹} : Set X)).subgroupOf Γ := by
  ext z
  refine Iff.trans (Subgroup.mem_map_equiv (f := conjOfNormalizes Γ m h1 h2)) ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  change m⁻¹ * (z : X) * m * u = u * (m⁻¹ * z * m) ↔ (z : X) * (m * u * m⁻¹) = m * u * m⁻¹ * z
  constructor
  · intro h
    calc (z : X) * (m * u * m⁻¹) = m * ((m⁻¹ * z * m) * u) * m⁻¹ := by group
      _ = m * (u * (m⁻¹ * z * m)) * m⁻¹ := by rw [h]
      _ = m * u * m⁻¹ * z := by group
  · intro h
    calc m⁻¹ * (z : X) * m * u = m⁻¹ * ((z : X) * (m * u * m⁻¹)) * m := by group
      _ = m⁻¹ * (m * u * m⁻¹ * z) * m := by rw [h]
      _ = u * (m⁻¹ * z * m) := by group


variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L]

theorem false_of_comp_twE6Two
    [Finite (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))]
    {ω : Lˣ} (hω : orderOf ω = 3)
    (h5 : ¬ 5 ^ 9 ∣ Nat.card (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L)))
    {u m' : ModGL Tag.E6 L} (hm' : m' ∈ twE6TwoModel L) {x : Fin Tag.E6.rank → ZMod 3}
    (hux : m' * u * m'⁻¹ = dV ω x)
    {J : Subgroup ↥(⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))}
    (hJ : CFSG.Open.IsComponentOf J ((Subgroup.centralizer ({u} : Set (ModGL Tag.E6 L))).subgroupOf
      (⁅twE6TwoModel L, twE6TwoModel L⁆ : Subgroup (ModGL Tag.E6 L))))
    (hA5 : Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* alternatingGroup (Fin 5))) : False := by
  have hω3 : ω ^ 3 = 1 := pow_three_of_orderOf hω
  set Γ : Subgroup (ModGL Tag.E6 L) := ⁅twE6TwoModel L, twE6TwoModel L⁆ with hΓ
  have h1 : ∀ y ∈ Γ, m' * y * m'⁻¹ ∈ Γ := fun y hy => twE6Two_conj_mem_commutator hm' hy
  have h2 : ∀ y ∈ Γ, m'⁻¹ * y * m' ∈ Γ := fun y hy => by
    have := twE6Two_conj_mem_commutator (inv_mem hm') hy
    rwa [inv_inv] at this
  set ψ := conjOfNormalizes Γ m' h1 h2 with hψ
  have hJ' := CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map ψ hJ
  rw [map_conjOfNormalizes_centralizer, hux] at hJ'
  have hcert := Certificates.certificate13614
  unfold Native.e6FourCoreCheck at hcert
  simp only [Bool.and_eq_true, List.all_eq_true] at hcert
  obtain ⟨⟨hhyp, hstd0⟩, -⟩ := hcert
  have hlenL : ∀ (l : List (List ℕ)), ∀ b ∈ l.map (liftL (τ := .E6) e6InnerVec),
      b.length = Tag.E6.rank := by
    intro l b hb
    obtain ⟨b', -, rfl⟩ := List.mem_map.1 hb
    exact length_liftL _ _
  have hltL : ∀ (l : List (List ℕ)), ∀ b ∈ l.map (liftL (τ := .E6) e6InnerVec), ∀ x ∈ b,
      x < 3 := by
    intro l b hb
    obtain ⟨b', -, rfl⟩ := List.mem_map.1 hb
    exact lt_of_mem_liftL _ _
  exact false_of_comp_sub (twE6TwoF L) twE6TwoF_rootDiagUnit
    (fun α hα => exists_twE6TwoF_rootSL2 hα) twE6Two_commutator_le_model hω
    (twE6Two_dV_e6InnerVec_mem_commutator hω3) subLin_e6InnerVec_injective
    (fun fl hfl => famData_of_famOKW hω (hlenL _) (hltL _) (hhyp fl hfl))
    (famData0_of_famOK0W hω (hlenL _) (hltL _) hstd0) h5
    (fun y => by rw [← dV_add hω3, ← dV_add hω3, add_comm]) hJ' (nonempty_a5_map ψ hA5)

end TwE6Model

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256k

end
