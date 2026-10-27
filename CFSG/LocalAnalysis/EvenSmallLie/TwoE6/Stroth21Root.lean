module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Stroth21
public import CFSG.Monster.B.TwoA.Sp8.Par1Center
public import CFSG.Monster.B.TwoA.Unitary.Twenty
public import CFSG.Monster.B.TwoA.Amalgam.CentralExt
public import CFSG.Monster.B.GSide.HSylowCenter
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate110
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate6023
public import Certificates.Certificate6024
public import Certificates.Certificate3023
public import Certificates.Certificate3043
public import Certificates.Certificate3130
public import Certificates.Certificate3131
public import Certificates.Certificate3132
public import Certificates.Certificate3133
public import Certificates.Certificate3134
public import Certificates.Certificate3135
public import Certificates.Certificate3136
public import Certificates.Certificate3137
public import Certificates.Certificate3178
public import Certificates.Certificate3179
public import Certificates.Certificate8046
public import Certificates.Certificate8048
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate10032
public import Certificates.Certificate10033
public import Certificates.Certificate10034
public import Certificates.Certificate10035
public import Certificates.Certificate10069
public import Certificates.Certificate10070
public import Certificates.Certificate16005
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup

section Generic

variable {H : Type*} [Group H]

theorem closure_odd_normal (N : Subgroup H) [N.Normal] :
    (closure {h : H | h ∈ N ∧ Odd (orderOf h)}).Normal := by
  refine ⟨fun n hn g => ?_⟩
  induction hn using closure_induction with
  | mem a ha =>
    refine subset_closure ⟨‹N.Normal›.conj_mem a ha.1 g, ?_⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ha.2
  | one => simp
  | mul a b _ _ iha ihb =>
    rw [show g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) by group]
    exact mul_mem iha ihb
  | inv a _ iha =>
    rw [show g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ by group]
    exact inv_mem iha

theorem closure_odd_eq {N : Subgroup H} [N.Normal] (hN : IsSimpleGroup N) {n : H} (hnN : n ∈ N)
    (hn1 : n ≠ 1) (hno : Odd (orderOf n)) :
    closure {h : H | h ∈ N ∧ Odd (orderOf h)} = N := by
  set S := closure {h : H | h ∈ N ∧ Odd (orderOf h)} with hS
  have hSN : S ≤ N := (closure_le N).2 fun h hh => hh.1
  have hSn : (S.subgroupOf N).Normal := (closure_odd_normal N).subgroupOf N
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hN _ hSn with h | h
  · exfalso
    apply hn1
    have hmem : (⟨n, hnN⟩ : N) ∈ S.subgroupOf N := mem_subgroupOf.2 (subset_closure ⟨hnN, hno⟩)
    rw [h, mem_bot] at hmem
    exact congrArg Subtype.val hmem
  · refine le_antisymm hSN fun x hx => ?_
    have hmem : (⟨x, hx⟩ : N) ∈ S.subgroupOf N := h ▸ mem_top _
    exact mem_subgroupOf.1 hmem

theorem commutator_mem_of_index_le_two [Finite H] {N : Subgroup H} (hidx : N.index ≤ 2)
    (a b : H) : a * b * a⁻¹ * b⁻¹ ∈ N := by
  have h0 : N.index ≠ 0 := index_ne_zero_of_finite
  rcases (show N.index = 1 ∨ N.index = 2 by omega) with h | h
  · rw [index_eq_one] at h
    rw [h]
    exact mem_top _
  · have hN := normal_of_index_eq_two h
    rw [mul_mem_iff_of_index_two h, inv_mem_iff]
    constructor
    · intro h1
      have h2 := hN.conj_mem _ h1 a⁻¹
      simpa [mul_assoc] using h2
    · intro h1
      exact hN.conj_mem b h1 a

theorem mem_of_odd_of_index_two {D : Subgroup H} (hD : D.index = 2) {y : H}
    (hy : Odd (orderOf y)) : y ∈ D := by
  obtain ⟨j, hj⟩ := hy
  have e : y = (y * y) ^ (j + 1) := by
    rw [← sq, ← pow_mul, show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, ← hj,
      pow_orderOf_eq_one, one_mul]
  rw [e]
  exact pow_mem (mul_self_mem_of_index_two hD y) _

theorem exists_odd_preimage {A B : Type*} [Group A] [Group B] [Finite A] {f : A →* B}
    (hf : Function.Surjective f) {g : B} (hg : Odd (orderOf g)) :
    ∃ a : A, Odd (orderOf a) ∧ f a = g := by
  obtain ⟨q, rfl⟩ := hf g
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos q).ne'
  have hr : orderOf (q ^ 2 ^ k) = m := by
    rw [orderOf_pow_of_dvd (by positivity) (by rw [hkm]; exact dvd_mul_right _ _), hkm,
      Nat.mul_div_cancel_left _ (by positivity)]
  have hcop : (2 ^ k).Coprime (orderOf (f q)) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hg.not_two_dvd_nat)
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  refine ⟨(q ^ 2 ^ k) ^ t, ?_, by rw [map_pow, map_pow, ht]⟩
  have hdvd : orderOf ((q ^ 2 ^ k) ^ t) ∣ m := hr ▸ orderOf_pow_dvd t
  exact Odd.of_dvd_nat hm hdvd

theorem eq_one_of_commute_odd [Finite H] (hZ : center H = ⊥) {N : Subgroup H} [N.Normal]
    (hidx : N.index ≤ 2) (hZN : center N = ⊥)
    (hgen : closure {h : H | h ∈ N ∧ Odd (orderOf h)} = N) {y : H}
    (hy : ∀ h : H, Odd (orderOf h) → y * h = h * y) : y = 1 := by
  have hyC : ∀ n ∈ N, n * y = y * n := by
    have hle : N ≤ centralizer {y} := by
      rw [← hgen, closure_le]
      intro h hh
      exact mem_centralizer_singleton_iff.2 (hy h hh.2).symm
    exact fun n hn => mem_centralizer_singleton_iff.1 (hle hn)
  have hcen : y ∈ center H := by
    rw [mem_center_iff]
    intro g
    set k := y⁻¹ * g * y * g⁻¹ with hk
    have hkN : k ∈ N := by
      have h := commutator_mem_of_index_le_two hidx y⁻¹ g
      rwa [inv_inv] at h
    have hkC : ∀ n ∈ N, n * k = k * n := by
      intro n hn
      have h1 := hyC n hn
      have h2 : g⁻¹ * n * g ∈ N := by
        have h := ‹N.Normal›.conj_mem n hn g⁻¹
        rwa [inv_inv] at h
      have h3 := hyC _ h2
      calc n * k = n * y⁻¹ * (g * y * g⁻¹) := by rw [hk]; group
        _ = y⁻¹ * n * (g * y * g⁻¹) := by
          rw [show n * y⁻¹ = y⁻¹ * (y * n * y⁻¹) by group, ← h1]; group
        _ = y⁻¹ * (g * ((g⁻¹ * n * g) * y) * g⁻¹) := by group
        _ = y⁻¹ * (g * (y * (g⁻¹ * n * g)) * g⁻¹) := by rw [h3]
        _ = k * n := by rw [hk]; group
    have hk1 : k = 1 := by
      have hmem : (⟨k, hkN⟩ : N) ∈ center N :=
        mem_center_iff.2 fun m => Subtype.ext (hkC m m.2)
      rw [hZN, mem_bot] at hmem
      exact congrArg Subtype.val hmem
    calc g * y = y * (y⁻¹ * g * y * g⁻¹) * g := by group
      _ = y * g := by rw [← hk, hk1, mul_one]
  rw [hZ, mem_bot] at hcen
  exact hcen

theorem false_of_odd_fixed [Finite H] {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k H V) (hirr : ρ.IsIrreducible)
    (hadj : Algebra.adjoin k (Set.range ρ) = ⊤) (hnc : ∃ f g : Module.End k V, f * g ≠ g * f)
    {N : Subgroup H} (hidx : N.index ≤ 2)
    (hgen : closure {h : H | h ∈ N ∧ Odd (orderOf h)} = N) {v : V} (hv : v ≠ 0)
    (hfix : ∀ h : H, Odd (orderOf h) → ρ h v = v) : False := by
  let F : Submodule k V :=
    { carrier := {w | ∀ h : H, Odd (orderOf h) → ρ h w = w}
      add_mem' := fun {a b} ha hb h hh => by rw [map_add, ha h hh, hb h hh]
      zero_mem' := fun h _ => map_zero _
      smul_mem' := fun c a ha h hh => by rw [map_smul, ha h hh] }
  have hFinv : ∀ (g : H) ⦃w : V⦄, w ∈ F → ρ g w ∈ F := by
    intro g w hw h hh
    have hodd : Odd (orderOf (g⁻¹ * h * g)) := by
      rw [show g⁻¹ * h * g = MulAut.conj g⁻¹ h by simp, MulEquiv.orderOf_eq]
      exact hh
    have e : ρ h (ρ g w) = ρ g (ρ (g⁻¹ * h * g) w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [e, hw _ hodd]
  let F' : Subrepresentation ρ := ⟨F, hFinv⟩
  have hF'top : F' = ⊤ := by
    rcases hirr.eq_bot_or_eq_top F' with h | h
    · exfalso
      apply hv
      have hvF : v ∈ F' := hfix
      rw [h] at hvF
      exact hvF
    · exact h
  have htriv : ∀ h : H, Odd (orderOf h) → ρ h = 1 := by
    intro h hh
    ext w
    have hw : w ∈ F' := by rw [hF'top]; trivial
    exact hw h hh
  have htrivN : ∀ n ∈ N, ρ n = 1 := by
    intro n hn
    rw [← hgen] at hn
    induction hn using closure_induction with
    | mem a ha => exact htriv a ha.2
    | one => exact map_one ρ
    | mul a b _ _ iha ihb => rw [map_mul, iha, ihb, one_mul]
    | inv a _ iha =>
      calc ρ a⁻¹ = ρ a⁻¹ * ρ a := by rw [iha, mul_one]
        _ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hcomm : ∀ a b : H, Commute (ρ a) (ρ b) := by
    intro a b
    have h1 := htrivN _ (commutator_mem_of_index_le_two hidx a b)
    have e : a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
    show ρ a * ρ b = ρ b * ρ a
    calc ρ a * ρ b = ρ (a * b) := (map_mul ρ a b).symm
      _ = ρ (a * b * a⁻¹ * b⁻¹) * ρ (b * a) := by rw [← map_mul, ← e]
      _ = ρ b * ρ a := by rw [h1, one_mul, map_mul]
  obtain ⟨f, g, hfg⟩ := hnc
  have hall : ∀ x ∈ Algebra.adjoin k (Set.range ρ), ∀ y ∈ Set.range ρ, Commute y x := by
    intro x hx y hy
    obtain ⟨b, rfl⟩ := hy
    exact Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun z hz => by
      obtain ⟨a, rfl⟩ := hz
      exact hcomm b a
  have hf : f ∈ Algebra.adjoin k (Set.range ρ) := by rw [hadj]; trivial
  have hg : g ∈ Algebra.adjoin k (Set.range ρ) := by rw [hadj]; trivial
  apply hfg
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hg fun y hy =>
    (hall f hf y hy).symm).eq

theorem false_of_odd_fixed_inv [Finite H] {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k H V) (hirr : ρ.IsIrreducible)
    (hadj : Algebra.adjoin k (Set.range ρ) = ⊤) (hnc : ∃ f g : Module.End k V, f * g ≠ g * f)
    {N : Subgroup H} (hidx : N.index ≤ 2)
    (hgen : closure {h : H | h ∈ N ∧ Odd (orderOf h)} = N) {v : V} (hv : v ≠ 0)
    (hfix : ∀ h : H, Odd (orderOf h) → ρ h⁻¹ v = v) : False :=
  false_of_odd_fixed ρ hirr hadj hnc hidx hgen hv fun h hh => by
    have h1 := hfix h⁻¹ (by rw [orderOf_inv]; exact hh)
    rwa [inv_inv] at h1

theorem exists_noncomm_of_basis {R M ι : Type*} [CommRing R] [Nontrivial R] [AddCommGroup M]
    [Module R M] [DecidableEq ι] (B : Module.Basis ι R M) {i j : ι} (hij : i ≠ j) :
    ∃ f g : Module.End R M, f * g ≠ g * f := by
  refine ⟨(B.coord i).smulRight (B j), (B.coord j).smulRight (B i), fun h => ?_⟩
  have h1 := LinearMap.congr_fun h (B j)
  simp only [Module.End.mul_apply, LinearMap.smulRight_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, one_smul,
    Finsupp.single_eq_of_ne hij, zero_smul, map_zero] at h1
  exact B.ne_zero j h1

end Generic

section Usig

open CFSG.Monster.B.TwoA

local notation "PSU6" => CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU Unitary.hF4 6

theorem exists_usig_normal
    : ∃ N : Subgroup Unitary.Usig, N.Normal ∧ N.index ≤ 2 ∧
    center N = ⊥ ∧ Subgroup.closure {h : Unitary.Usig | h ∈ N ∧ Odd (orderOf h)} = N := by
  have : Finite PSU6 :=
    Nat.finite_of_card_ne_zero (by rw [Unitary.natCard_unitaryPSU]; norm_num)
  set Φ : Unitary.Usig ≃* Unitary.PSU62 := Unitary.phiU.trans Unitary.thetaEquiv with hΦ
  set ι₀ : PSU6 →* Unitary.Usig :=
    Φ.symm.toMonoidHom.comp (SemidirectProduct.inl : PSU6 →* Unitary.PSU62) with hι₀
  have hinj : Function.Injective ι₀ :=
    Φ.symm.injective.comp SemidirectProduct.inl_injective
  have hNeq : ι₀.range = (SemidirectProduct.inl : PSU6 →* Unitary.PSU62).range.map
      Φ.symm.toMonoidHom := by
    rw [hι₀, MonoidHom.range_comp]
  have hinl : ((SemidirectProduct.inl : PSU6 →* Unitary.PSU62).range).Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact MonoidHom.normal_ker _
  have hNn : ι₀.range.Normal := by
    rw [hNeq]
    exact hinl.map _ Φ.symm.surjective
  have hidx : ι₀.range.index ≤ 2 := by
    rw [hNeq, index_map_of_bijective Φ.symm.bijective, SemidirectProduct.range_inl_eq_ker_rightHom,
      index_ker]
    calc Nat.card (SemidirectProduct.rightHom : Unitary.PSU62 →* Multiplicative (ZMod 2)).range
        ≤ Nat.card (Multiplicative (ZMod 2)) := card_le_card_group _
      _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl
  let e : PSU6 ≃* ι₀.range := MonoidHom.ofInjective hinj
  have hsimp : IsSimpleGroup ι₀.range := by
    have := Unitary.isSimpleGroup_unitaryPSU
    have : Nontrivial ι₀.range := e.symm.toEquiv.nontrivial
    exact IsSimpleGroup.isSimpleGroup_of_surjective e.toMonoidHom e.surjective
  have hZN : center ι₀.range = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [mem_bot]
    have h1 : e.symm z ∈ center PSU6 :=
      (CFSG.Monster.B.GSide.mem_center_iff_of_mulEquiv e.symm).1 hz
    rw [Sp8.center_PSU6, mem_bot] at h1
    rw [← e.apply_symm_apply z, h1, map_one]
  obtain ⟨a, ha⟩ : ∃ a : PSU6, orderOf a = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have := Fintype.ofFinite PSU6
    exact exists_prime_orderOf_dvd_card 3
      (by rw [← Nat.card_eq_fintype_card, Unitary.natCard_unitaryPSU]; norm_num)
  have ho : orderOf (ι₀ a) = 3 := by rw [orderOf_injective ι₀ hinj, ha]
  have hgen := closure_odd_eq hsimp (n := ι₀ a) ⟨a, rfl⟩
    (fun h => by rw [h, orderOf_one] at ho; exact absurd ho (by norm_num))
    (by rw [ho]; decide)
  exact ⟨ι₀.range, hNn, hidx, hZN, hgen⟩

theorem usig_eq_one_of_commute_odd
    {y : Unitary.Usig}
    (hy : ∀ g : Unitary.Usig, Odd (orderOf g) → y * g = g * y) : y = 1 := by
  obtain ⟨N, hNn, hidx, hZN, hgen⟩ := exists_usig_normal
  exact eq_one_of_commute_odd Sp8.center_Usig hidx hZN hgen hy

theorem exists_noncomm_w20 :
    ∃ f g : Module.End (ZMod 2) Unitary.W20, f * g ≠ g * f :=
  exists_noncomm_of_basis Unitary.b20 (show (0 : Fin 20) ≠ 1 by decide)

theorem w20_eq_zero_of_odd_fixed
    {v : Unitary.W20}
    (hfix : ∀ g : Unitary.Usig, Odd (orderOf g) → Unitary.w20End g v = v) : v = 0 := by
  by_contra hv
  obtain ⟨N, -, hidx, -, hgen⟩ := exists_usig_normal
  refine false_of_odd_fixed_inv Unitary.rep20 Unitary.isIrreducible_rep20 Unitary.adjoin_rep20
    exists_noncomm_w20 hidx hgen hv fun g hg => ?_
  rw [Unitary.rep20_apply, inv_inv]
  exact hfix g hg

end Usig

section Root

open CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

theorem exists_odd_lift_P1
    {g : Unitary.Usig} (hg : Odd (orderOf g)) :
    ∃ p : Sp8.P1, Odd (orderOf p) ∧ Sp8.p1Proj p = g :=
  exists_odd_preimage Sp8.p1Proj_surjective hg

theorem mem_N1_of_commute_odd
    {y : Dfull} (hy : y ∈ Sp8.P1)
    (hc : ∀ p : Sp8.P1, Odd (orderOf p) → y * p = p * y) : y ∈ Sp8.N1 := by
  have hπ : Sp8.p1Proj ⟨y, hy⟩ = 1 := by
    apply usig_eq_one_of_commute_odd
    intro g hg
    obtain ⟨p', hp'o, hp'⟩ := exists_odd_lift_P1 hg
    have hyp : (⟨y, hy⟩ : Sp8.P1) * p' = p' * ⟨y, hy⟩ := Subtype.ext (hc p' hp'o)
    rw [← hp', ← map_mul Sp8.p1Proj _ p', ← map_mul Sp8.p1Proj p' _, hyp]
  have h : (⟨y, hy⟩ : Sp8.P1) ∈ Sp8.p1Proj.ker := hπ
  rw [Sp8.ker_p1Proj, mem_subgroupOf] at h
  exact h

theorem w20End_fixed_of_commute_odd
    {y : Dfull} (hyN : y ∈ Sp8.N1)
    (hc : ∀ p : Sp8.P1, Odd (orderOf p) → y * p = p * y) {g : Unitary.Usig}
    (hg : Odd (orderOf g)) :
    Unitary.w20End g (Submodule.Quotient.mk ⟨psiW ⟨y, hyN.1⟩, psiW_mem_sigmaPerp hyN⟩) =
      Submodule.Quotient.mk ⟨psiW ⟨y, hyN.1⟩, psiW_mem_sigmaPerp hyN⟩ := by
  obtain ⟨p', hp'o, hp'⟩ := exists_odd_lift_P1 hg
  have hc' : (p' : Dfull)⁻¹ * y * p' = y := by
    calc (p' : Dfull)⁻¹ * y * p' = (p' : Dfull)⁻¹ * (y * p') := by group
      _ = (p' : Dfull)⁻¹ * (p' * y) := by rw [hc p' hp'o]
      _ = y := by group
  have h1 := psiW_conj (Sp8.P1_le_Jhat p'.2) hyN.1
  have h2 : (⟨(p' : Dfull)⁻¹ * y * p', conj_mem_Ehat (Sp8.P1_le_Jhat p'.2) hyN.1⟩ : Ehat) =
      ⟨y, hyN.1⟩ := Subtype.ext hc'
  rw [h2, ← Sp8.coe_p1Proj p', hp'] at h1
  rw [Unitary.w20End_mk]
  congr 1
  apply Subtype.ext
  rw [Unitary.perpEnd_apply]
  exact h1.symm

theorem mul_self_eq_one_of_mk_eq_zero
    {y : Dfull} (hyN : y ∈ Sp8.N1)
    (h : (Submodule.Quotient.mk ⟨psiW ⟨y, hyN.1⟩, psiW_mem_sigmaPerp hyN⟩ : Unitary.W20) = 0) :
    y * y = 1 := by
  have hcx : Sp8.cQ * xhat = xhat * Sp8.cQ :=
    xhat_comm_of_mem_Jhat (Ehat_le_Jhat Sp8.cQ_mem_Ehat)
  rw [Submodule.Quotient.mk_eq_zero, Unitary.sigLine, Submodule.mem_span_singleton] at h
  obtain ⟨a, ha⟩ := h
  have ha' : a • Unitary.sigmaW = psiW ⟨y, hyN.1⟩ := congrArg Subtype.val ha
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 a with rfl | rfl
  · rw [zero_smul] at ha'
    rcases (psiW_eq_zero_iff _).1 ha'.symm with h1 | h1
    · have h2 : y = 1 := congrArg Subtype.val h1
      rw [h2, mul_one]
    · have h2 : y = xhat := congrArg Subtype.val h1
      rw [h2, xhat_mul_self]
  · rw [one_smul, ← Sp8.psiW_cE] at ha'
    have h0 : psiW (⟨y, hyN.1⟩ * Sp8.cE⁻¹) = 0 := by
      rw [psiW_mul, psiW_inv, ← ha', add_neg_cancel]
    rcases (psiW_eq_zero_iff _).1 h0 with h1 | h1
    · have h2 : y * Sp8.cQ⁻¹ = 1 := congrArg Subtype.val h1
      rw [mul_inv_eq_one.1 h2, Sp8.cQ_mul_self]
    · have h2 : y * Sp8.cQ⁻¹ = xhat := congrArg Subtype.val h1
      rw [mul_inv_eq_iff_eq_mul.1 h2]
      calc xhat * Sp8.cQ * (xhat * Sp8.cQ) = xhat * (Sp8.cQ * xhat) * Sp8.cQ := by group
        _ = xhat * (xhat * Sp8.cQ) * Sp8.cQ := by rw [hcx]
        _ = 1 := by rw [← mul_assoc, xhat_mul_self, one_mul, Sp8.cQ_mul_self]

theorem mul_self_eq_one_of_N1_commute_odd
    {y : Dfull} (hyN : y ∈ Sp8.N1)
    (hc : ∀ p : Sp8.P1, Odd (orderOf p) → y * p = p * y) : y * y = 1 :=
  mul_self_eq_one_of_mk_eq_zero hyN
    (w20_eq_zero_of_odd_fixed fun _ hg => w20End_fixed_of_commute_odd hyN hc hg)

theorem rootFourTest :
    RootFourTest := by
  intro b hb2
  by_contra hcon
  push Not at hcon
  have hcc := Stroth21Aux.cE'_comm
  have hbx : b * xhatEam = xhatEam * b := by
    rcases hb2 with h | h
    · rw [← h]
      group
    · have h1 : b * (cE' * xhatEam) = cE' * xhatEam * b := by
        rw [← h]
        group
      calc b * xhatEam = cE'⁻¹ * (b * (cE' * xhatEam)) := by
            rw [← mul_assoc b cE' xhatEam, hcc b]
            group
        _ = cE'⁻¹ * (cE' * xhatEam * b) := by rw [h1]
        _ = xhatEam * b := by group
  have hbx' : (b : Dfull) * xhat = xhat * b := congrArg Subtype.val hbx
  have hbc' : (b : Dfull) * Sp8.cQ = Sp8.cQ * b := congrArg Subtype.val (hcc b)
  have hbP : (b : Dfull) ∈ Sp8.P1 :=
    ⟨by rw [← centralizer_xhat]; exact mem_centralizer_singleton_iff.2 hbx',
      mem_centralizer_singleton_iff.2 hbc'⟩
  have hodd_comm : ∀ p' : Sp8.P1, Odd (orderOf p') → (b : Dfull) * p' = p' * b := by
    intro p' hp'o
    have hp'E : (p' : Dfull) ∈ Eam := Pc_le_Eam 0 p'.2
    have he'o : Odd (orderOf (⟨p', hp'E⟩ : Eam)) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe]
      exact hp'o
    have he'C : (⟨p', hp'E⟩ : Eam) ∈ commutator Eam :=
      mem_of_odd_of_index_two Stroth21Aux.index_commutator_Eam he'o
    have he'x : (⟨p', hp'E⟩ : Eam) * xhatEam = xhatEam * ⟨p', hp'E⟩ :=
      Subtype.ext (xhat_comm_of_mem_Jhat (Sp8.P1_le_Jhat p'.2))
    have h := hcon _ he'C he'x he'o
    exact congrArg Subtype.val h
  have hbN := mem_N1_of_commute_odd hbP hodd_comm
  have hb1 := mul_self_eq_one_of_N1_commute_odd hbN hodd_comm
  rcases hb2 with h | h
  · have h2 : (b : Dfull) * b = xhat := congrArg Subtype.val h
    exact xhat_ne_one (h2.symm.trans hb1)
  · have h2 : (b : Dfull) * b = Sp8.cQ * xhat := congrArg Subtype.val h
    apply Sp8.cQ_ne_xhat
    calc Sp8.cQ = Sp8.cQ * xhat * xhat := by rw [mul_assoc, xhat_mul_self, mul_one]
      _ = xhat := by rw [← h2, hb1, one_mul]

theorem stroth21_of_oddSquareTest
    (hS : OddSquareTest) : Stroth21 :=
  stroth21_of_inputs hS rootFourTest

end Root

section N1

open CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

theorem exists_odd_sq_of_conj {E : Type*} [Group E] {D : Subgroup E} [D.Normal] (g : E)
    {u s : D}
    (hs : s ∈ closure {h : D | h * MulAut.conjNormal g u = MulAut.conjNormal g u * h ∧
      Odd (orderOf h)})
    (hss : s * s = MulAut.conjNormal g u) :
    ∃ s' ∈ closure {h : D | h * u = u * h ∧ Odd (orderOf h)}, s' * s' = u := by
  set φ : D ≃* D := MulAut.conjNormal g with hφ
  refine ⟨φ.symm s, ?_, ?_⟩
  · have h1 := mem_map_of_mem φ.symm.toMonoidHom hs
    rw [MonoidHom.map_closure] at h1
    refine closure_mono ?_ h1
    rintro _ ⟨h, ⟨hh1, hh2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · apply φ.injective
      simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
      exact hh1
    · rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
      exact hh2
  · apply φ.injective
    rw [map_mul, MulEquiv.apply_symm_apply, hss]

@[expose] def InvolutionsIntoN1Dfull :
    Prop :=
  ∀ u : commutator Eam, u * u = 1 → ∃ g : Eam, ((g * u * g⁻¹ : Eam) : Dfull) ∈ Sp8.N1

@[expose] def N1OddSquareTest :
    Prop :=
  ∀ y : commutator Eam, ((y : Eam) : Dfull) ∈ Sp8.N1 → y * y = 1 → (y : Eam) ≠ 1 →
    (y : Eam) ≠ cE' → ¬ IsConj xhatEam (y : Eam) → ¬ IsConj (cE' * xhatEam) (y : Eam) →
    ∃ s ∈ closure {h : commutator Eam | h * y = y * h ∧ Odd (orderOf h)}, s * s = y

theorem oddSquare_of_conj_into {E : Type*} [Group E] {D : Subgroup E} [D.Normal] {c x : E}
    (hcc : ∀ y : E, y * c = c * y) (P : Set E)
    (h1 : ∀ u : D, u * u = 1 → ∃ g : E, g * (u : E) * g⁻¹ ∈ P)
    (h2 : ∀ y : D, (y : E) ∈ P → y * y = 1 → (y : E) ≠ 1 → (y : E) ≠ c →
      ¬ IsConj x (y : E) → ¬ IsConj (c * x) (y : E) →
      ∃ s ∈ closure {h : D | h * y = y * h ∧ Odd (orderOf h)}, s * s = y)
    (u : D) (hu2 : u * u = 1) (hu1 : (u : E) ≠ 1) (huc : (u : E) ≠ c)
    (hx : ¬ IsConj x (u : E)) (hcx : ¬ IsConj (c * x) (u : E)) :
    ∃ s ∈ closure {h : D | h * u = u * h ∧ Odd (orderOf h)}, s * s = u := by
  obtain ⟨g, hg⟩ := h1 u hu2
  have hyv : ((MulAut.conjNormal g u : D) : E) = g * (u : E) * g⁻¹ := MulAut.conjNormal_apply g u
  have hconj : IsConj (u : E) ((MulAut.conjNormal g u : D) : E) :=
    isConj_iff.2 ⟨g, hyv.symm⟩
  have hy2 : MulAut.conjNormal g u * MulAut.conjNormal g u = 1 := by
    rw [← map_mul, hu2, map_one]
  have hy1 : ((MulAut.conjNormal g u : D) : E) ≠ 1 := by
    intro h
    apply hu1
    rw [hyv] at h
    calc (u : E) = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hyc : ((MulAut.conjNormal g u : D) : E) ≠ c := by
    intro h
    apply huc
    rw [hyv] at h
    calc (u : E) = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = g⁻¹ * c * g := by rw [h]
      _ = c := by rw [hcc g⁻¹]; group
  obtain ⟨s, hs, hss⟩ := h2 _ (hyv ▸ hg) hy2 hy1 hyc (fun h => hx (h.trans hconj.symm))
    (fun h => hcx (h.trans hconj.symm))
  exact exists_odd_sq_of_conj g hs hss

theorem oddSquareTest_of_N1
    (h1 : InvolutionsIntoN1Dfull) (h2 : N1OddSquareTest) :
    OddSquareTest :=
  oddSquare_of_conj_into Stroth21Aux.cE'_comm {y : Eam | (y : Dfull) ∈ Sp8.N1} h1 h2

theorem coe_mem_N1_of_mem_map_NH
    {y : Eam}
    (h : y ∈ Subgroup.map CFSG.Monster.B.GSide.vStabEam.toMonoidHom CFSG.Monster.B.GSide.NH) :
    (y : Dfull) ∈ Sp8.N1 := by
  obtain ⟨w, hw, rfl⟩ := h
  have hw' : CFSG.Monster.B.GSide.iotaH w ∈ Sp8.N1 := hw
  rw [CFSG.Monster.B.GSide.iotaH_apply] at hw'
  rw [MulEquiv.coe_toMonoidHom, CFSG.Monster.B.GSide.coe_vStabEam]
  exact hw'

theorem involutionsIntoN1Dfull_of
    (h : ∀ u : commutator Eam, u * u = 1 → ∃ g : Eam,
      g * (u : Eam) * g⁻¹ ∈
        Subgroup.map CFSG.Monster.B.GSide.vStabEam.toMonoidHom CFSG.Monster.B.GSide.NH) :
    InvolutionsIntoN1Dfull := fun u hu => by
  obtain ⟨g, hg⟩ := h u hu
  exact ⟨g, coe_mem_N1_of_mem_map_NH hg⟩

theorem stroth21_of_N1
    (h1 : InvolutionsIntoN1Dfull) (h2 : N1OddSquareTest) : Stroth21 :=
  stroth21_of_oddSquareTest (oddSquareTest_of_N1 h1 h2)

end N1

end CFSG.EvenSmallLie.TwoE6
