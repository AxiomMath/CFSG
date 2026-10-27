module

public import CFSG.Foundations.Basic
public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
import CFSG.LocalAnalysis.SectionRank.CentralLift

public section

namespace CFSG.GroupTheory.ComponentCentralRank

open Subgroup CFSG.SectionRank

variable {Y : Type*} [Group Y] [Finite Y]

private instance fact_prime_three : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private theorem commute_of_mem_of_isComponent {K L : Subgroup Y} (hK : CFSG.IsComponent K)
    (hL : CFSG.IsComponent L) (hKL : K ≠ L) (a b : Y) (ha : a ∈ K) (hb : b ∈ L) :
    Commute a b := by
  rcases CFSG.LocalCores.distinct_components_commute hK hL with h | h
  · exact absurd h hKL
  · exact (Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) b hb).symm

omit [Finite Y] in
private theorem commute_range_of_zpow_mul_pow {B : Type*} [Group B] {F : B →* Y} {z x y : Y}
    {K : Subgroup Y} (hF : ∀ a, ∃ b : zpowers z, ∃ n : ℕ, F a = (b : Y) * x ^ n)
    (hzy : Commute z y) (hxy : Commute x y) (hzK : ∀ k ∈ K, Commute k z)
    (hxK : ∀ k ∈ K, Commute k x) :
    ∀ a, Commute (F a) y ∧ ∀ k ∈ K, Commute k (F a) := by
  intro a
  obtain ⟨⟨_, m, rfl⟩, n, hn⟩ := hF a
  rw [hn]
  exact ⟨(hzy.zpow_left m).mul_left (hxy.pow_left n),
    fun k hk => ((hzK k hk).zpow_right m).mul_right ((hxK k hk).pow_right n)⟩

omit [Finite Y] in
private theorem commute_range_mul_pow {B B' : Type*} [Group B] [Group B'] {F' : B' →* Y}
    {F : B →* Y} {x y : Y} {K : Subgroup Y}
    (hF : ∀ a, ∃ b : B', ∃ n : ℕ, F a = F' b * x ^ n)
    (hF'y : ∀ b, Commute (F' b) y) (hF'K : ∀ b, ∀ k ∈ K, Commute k (F' b))
    (hxy : Commute x y) (hxK : ∀ k ∈ K, Commute k x) :
    ∀ a, Commute (F a) y ∧ ∀ k ∈ K, Commute k (F a) := by
  intro a
  obtain ⟨b, n, hn⟩ := hF a
  rw [hn]
  exact ⟨(hF'y b).mul_left (hxy.pow_left n),
    fun k hk => (hF'K b k hk).mul_right ((hxK k hk).pow_right n)⟩

private theorem exists_extend_zpowers {p : ℕ} [Fact p.Prime] {J : Subgroup Y} {z x : Y}
    (hz : z ∈ center Y) (hzp : orderOf z = p) (hxp : orderOf x = p)
    (hxc : ¬ ∀ k ∈ J, Commute k x) :
    ∃ F : (zpowers z × zpowers x) →* Y, Function.Injective F ∧
      (∀ a b : zpowers z × zpowers x, a * b = b * a) ∧
      (∀ a : zpowers z × zpowers x, a ^ p = 1) ∧
      Nat.card (zpowers z × zpowers x) = p ^ (1 + 1) ∧
      ∀ a, ∃ b : zpowers z, ∃ n : ℕ, F a = (b : Y) * x ^ n := by
  have hzc : ∀ (g : Y) (m : ℤ), Commute (z ^ m) g := fun g m =>
    (show Commute z g from (Subgroup.mem_center_iff.mp hz g).symm).zpow_left m
  have hcomm₀ : ∀ a b : zpowers z, a * b = b * a := by
    rintro ⟨_, m, rfl⟩ ⟨_, n, rfl⟩
    exact Subtype.ext (zpow_mul_comm z m n)
  have hpow₀ : ∀ a : zpowers z, a ^ p = 1 := by
    rintro ⟨_, m, rfl⟩
    refine Subtype.ext ?_
    change (z ^ m) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hzp,
      pow_orderOf_eq_one, one_zpow]
  have hcard₀ : Nat.card (zpowers z) = p ^ 1 := by rw [Nat.card_zpowers, hzp, pow_one]
  have hx1 : x ∉ (zpowers z).subtype.range := by
    rw [range_subtype]
    rintro ⟨m, rfl⟩
    exact hxc fun k _ => (hzc k m).symm
  obtain ⟨F, hF, hcomm, hpow, hcard, hrange⟩ := exists_extend hcomm₀ hpow₀ hcard₀
    (zpowers z).subtype (subtype_injective _) (hxp ▸ pow_orderOf_eq_one x) hx1
    (fun ⟨_, m, hm⟩ => hm ▸ hzc x m)
  exact ⟨F, hF, hcomm, hpow, hcard, hrange⟩

theorem four_le_pRank_of_three_components {p : ℕ} [Fact p.Prime] {J₁ J₂ J₃ : Subgroup Y}
    (h₁ : CFSG.IsComponent J₁) (h₂ : CFSG.IsComponent J₂) (h₃ : CFSG.IsComponent J₃)
    (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃) {z x₁ x₂ x₃ : Y}
    (hz : z ∈ center Y) (hzp : orderOf z = p) (hx₁ : x₁ ∈ J₁) (hx₂ : x₂ ∈ J₂) (hx₃ : x₃ ∈ J₃)
    (hx₁p : orderOf x₁ = p) (hx₂p : orderOf x₂ = p) (hx₃p : orderOf x₃ = p)
    (hx₁c : ¬ ∀ k ∈ J₁, Commute k x₁) (hx₂c : ¬ ∀ k ∈ J₂, Commute k x₂)
    (hx₃c : ¬ ∀ k ∈ J₃, Commute k x₃) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := by
  have hc₁₂ : ∀ a ∈ J₁, ∀ b ∈ J₂, Commute a b :=
    fun a ha b hb => commute_of_mem_of_isComponent h₁ h₂ h12 a b ha hb
  have hc₁₃ : ∀ a ∈ J₁, ∀ b ∈ J₃, Commute a b :=
    fun a ha b hb => commute_of_mem_of_isComponent h₁ h₃ h13 a b ha hb
  have hc₂₃ : ∀ a ∈ J₂, ∀ b ∈ J₃, Commute a b :=
    fun a ha b hb => commute_of_mem_of_isComponent h₂ h₃ h23 a b ha hb
  have hzc : ∀ (g : Y) (m : ℤ), Commute (z ^ m) g := fun g m =>
    (show Commute z g from (Subgroup.mem_center_iff.mp hz g).symm).zpow_left m
  obtain ⟨F₁, hF₁, hcomm₁, hpow₁, hcard₁, hrange₁⟩ :=
    exists_extend_zpowers hz hzp hx₁p hx₁c
  have hrange₁₂ : ∀ a, Commute (F₁ a) x₂ ∧ ∀ k ∈ J₂, Commute k (F₁ a) :=
    commute_range_of_zpow_mul_pow (x := x₁) (K := J₂) hrange₁
      (by simpa using hzc x₂ 1) (hc₁₂ x₁ hx₁ x₂ hx₂)
      (fun k _ => by simpa using (hzc k 1).symm)
      (fun k hk => (hc₁₂ x₁ hx₁ k hk).symm)
  have hx₂1 : x₂ ∉ F₁.range := by
    rintro ⟨a, rfl⟩
    exact hx₂c (hrange₁₂ a).2
  obtain ⟨F₂, hF₂, hcomm₂, hpow₂, hcard₂, hrange₂⟩ := exists_extend hcomm₁ hpow₁ hcard₁ F₁ hF₁
    (hx₂p ▸ pow_orderOf_eq_one x₂) hx₂1 fun a => (hrange₁₂ a).1
  have hrange₁₃ : ∀ a, Commute (F₁ a) x₃ ∧ ∀ k ∈ J₃, Commute k (F₁ a) :=
    commute_range_of_zpow_mul_pow (x := x₁) (K := J₃) hrange₁
      (by simpa using hzc x₃ 1) (hc₁₃ x₁ hx₁ x₃ hx₃)
      (fun k _ => by simpa using (hzc k 1).symm)
      (fun k hk => (hc₁₃ x₁ hx₁ k hk).symm)
  have hrange₂₃ : ∀ a, Commute (F₂ a) x₃ ∧ ∀ k ∈ J₃, Commute k (F₂ a) :=
    commute_range_mul_pow (F' := F₁) (x := x₂) (K := J₃) hrange₂
      (fun b => (hrange₁₃ b).1) (fun b k hk => (hrange₁₃ b).2 k hk)
      (hc₂₃ x₂ hx₂ x₃ hx₃) (fun k hk => (hc₂₃ x₂ hx₂ k hk).symm)
  have hx₃1 : x₃ ∉ F₂.range := by
    rintro ⟨a, rfl⟩
    exact hx₃c (hrange₂₃ a).2
  obtain ⟨F₃, hF₃, hcomm₃, hpow₃, hcard₃, -⟩ := exists_extend hcomm₂ hpow₂ hcard₂ F₂ hF₂
    (hx₃p ▸ pow_orderOf_eq_one x₃) hx₃1 fun a => (hrange₂₃ a).1
  exact le_pRank_of_injective (Fact.out : p.Prime).one_lt hcomm₃ hpow₃ hcard₃ F₃ hF₃ le_top

omit [Finite Y] in
private theorem mem_normalizer_of_pow_sq_mem {J : Subgroup Y} {u : Y} (hodd : Odd (orderOf u))
    (h : u ^ 2 ∈ normalizer (J : Set Y)) : u ∈ normalizer (J : Set Y) := by
  obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul (pow_orderOf_eq_one u) hodd 1
  have hu : u = (u ^ 2) ^ m := by
    rw [← pow_mul, ← hm]
    simp
  rw [hu]
  exact Subgroup.pow_mem _ h m

private theorem exists_order_three_not_central {J : Subgroup Y} (hJ3 : 3 ∣ Nat.card J)
    (hZJ : ¬ 3 ∣ Nat.card (center J)) :
    ∃ x : Y, x ∈ J ∧ orderOf x = 3 ∧ ¬ ∀ k ∈ J, Commute k x := by
  obtain ⟨xJ, hxord⟩ := exists_prime_orderOf_dvd_card' (G := J) 3 hJ3
  refine ⟨xJ, xJ.2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hxord]
  · intro h
    apply hZJ
    have hxZ : xJ ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (h (g : Y) g.2)
    have hdvd := Subgroup.orderOf_dvd_natCard (Subgroup.center J) hxZ
    rwa [hxord] at hdvd

omit [Finite Y] in
private theorem not_forall_commute_map_conj {J : Subgroup Y} {u x : Y}
    (h : ¬ ∀ k ∈ J, Commute k x) :
    ¬ ∀ k ∈ J.map (MulAut.conj u).toMonoidHom, Commute k ((MulAut.conj u) x) := by
  intro hc
  apply h
  intro k hk
  have hk' : (MulAut.conj u) k ∈ J.map (MulAut.conj u).toMonoidHom :=
    Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hk
  exact Commute.of_map (MulAut.conj u).injective (hc ((MulAut.conj u) k) hk')

omit [Finite Y] in
private theorem pow_two_mem_normalizer_of_conj_eq {J : Subgroup Y} {u : Y}
    (h : J.map (MulAut.conj u).toMonoidHom = J.map (MulAut.conj u⁻¹).toMonoidHom) :
    u ^ 2 ∈ normalizer (J : Set Y) := by
  have hLmul : MulAut.conj u * MulAut.conj u = MulAut.conj (u * u) := by
    rw [← map_mul]
  have hRmul : MulAut.conj u * MulAut.conj u⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hL : (MulAut.conj u).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      (MulAut.conj (u * u)).toMonoidHom := by
    ext x
    exact congrArg (fun f : MulAut Y => f x) hLmul
  have hR : (MulAut.conj u).toMonoidHom.comp (MulAut.conj u⁻¹).toMonoidHom =
      MonoidHom.id Y := by
    ext x
    exact congrArg (fun f : MulAut Y => f x) hRmul
  have hmap : J.map (MulAut.conj (u * u)).toMonoidHom = J := by
    have h' := congrArg (Subgroup.map (MulAut.conj u).toMonoidHom) h
    rw [Subgroup.map_map, Subgroup.map_map, hL, hR, Subgroup.map_id] at h'
    exact h'
  rw [pow_two]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmap

theorem le_normalizer_of_component (hY : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3)
    {z : Y} (hz : z ∈ center Y) (hz3 : orderOf z = 3) {J : Subgroup Y}
    (hJ : CFSG.IsComponent J) (hJ3 : 3 ∣ Nat.card J) (hZJ : ¬ 3 ∣ Nat.card (center J))
    {T : Subgroup Y} (hT : IsPGroup 3 T) : T ≤ normalizer (J : Set Y) := by
  intro u hu
  by_contra huN
  have huN' : J.map (MulAut.conj u).toMonoidHom ≠ J := fun h =>
    huN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  let J₂ : Subgroup Y := J.map (MulAut.conj u).toMonoidHom
  let J₃ : Subgroup Y := J.map (MulAut.conj u⁻¹).toMonoidHom
  have hJ₂ : CFSG.IsComponent J₂ :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj u) hJ
  have hJ₃ : CFSG.IsComponent J₃ :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj u⁻¹) hJ
  have hJ₁₂ : J ≠ J₂ := fun h => huN' h.symm
  have hJ₁₃ : J ≠ J₃ := by
    intro h
    have hmem : u⁻¹ ∈ normalizer (J : Set Y) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
    exact huN (by simpa using Subgroup.inv_mem _ hmem)
  have hJ₂₃ : J₂ ≠ J₃ := by
    intro h
    have hu2N : u ^ 2 ∈ normalizer (J : Set Y) := pow_two_mem_normalizer_of_conj_eq h
    obtain ⟨n, hn⟩ := hT.exists_pow_pow_eq_one (⟨u, hu⟩ : T)
    have hn' : u ^ 3 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have hodd : Odd (orderOf u) :=
      Odd.of_dvd_nat (show Odd (3 ^ n) from Odd.pow (by decide))
        (orderOf_dvd_of_pow_eq_one hn')
    exact huN (mem_normalizer_of_pow_sq_mem hodd hu2N)
  obtain ⟨x₁, hx₁, hx₁p, hx₁c⟩ := exists_order_three_not_central hJ3 hZJ
  let x₂ : Y := (MulAut.conj u) x₁
  let x₃ : Y := (MulAut.conj u⁻¹) x₁
  have hx₂J₂ : x₂ ∈ J₂ := Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hx₁
  have hx₃J₃ : x₃ ∈ J₃ := Subgroup.mem_map_of_mem (MulAut.conj u⁻¹).toMonoidHom hx₁
  have hx₂p : orderOf x₂ = 3 := by
    rw [show orderOf x₂ = orderOf x₁ from MulEquiv.orderOf_eq (MulAut.conj u) x₁, hx₁p]
  have hx₃p : orderOf x₃ = 3 := by
    rw [show orderOf x₃ = orderOf x₁ from MulEquiv.orderOf_eq (MulAut.conj u⁻¹) x₁, hx₁p]
  have hx₂c : ¬ ∀ k ∈ J₂, Commute k x₂ :=
    not_forall_commute_map_conj (u := u) hx₁c
  have hx₃c : ¬ ∀ k ∈ J₃, Commute k x₃ :=
    not_forall_commute_map_conj (u := u⁻¹) hx₁c
  have hfour := four_le_pRank_of_three_components hJ hJ₂ hJ₃ hJ₁₂ hJ₁₃ hJ₂₃ hz hz3
    hx₁ hx₂J₂ hx₃J₃ hx₁p hx₂p hx₃p hx₁c hx₂c hx₃c
  omega

omit [Finite Y] in
private theorem dvd_card_center_of_mem_center {J : Subgroup Y} {z : Y} (hz : z ∈ center Y)
    (hz3 : orderOf z = 3) (hzJ : z ∈ J) : 3 ∣ Nat.card (Subgroup.center J) := by
  have hzZ : (⟨z, hzJ⟩ : J) ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz (g : Y))
  have hord : orderOf (⟨z, hzJ⟩ : J) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hz3
  have hdvd := Subgroup.orderOf_dvd_natCard (Subgroup.center J) hzZ
  rwa [hord] at hdvd

private theorem mem_of_mem_zpowers_of_order_three {J : Subgroup Y} {z w : Y}
    (hz3 : orderOf z = 3) (hw3 : orderOf w = 3) (hwJ : w ∈ J) (hwz : w ∈ zpowers z) :
    z ∈ J := by
  have hcardz : Nat.card (zpowers z) = 3 := by rw [Nat.card_zpowers, hz3]
  have hcardw : Nat.card (zpowers w) = 3 := by rw [Nat.card_zpowers, hw3]
  have heq : Subgroup.zpowers w = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwz) (by rw [hcardz, hcardw])
  have hzmem : z ∈ Subgroup.zpowers w := by
    rw [heq]
    exact Subgroup.mem_zpowers z
  exact Subgroup.zpowers_le.mpr hwJ hzmem

private theorem sylow_inf_ne_bot {T J : Subgroup Y} (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤)
    (hTN : T ≤ normalizer (J : Set Y)) (hJ3 : 3 ∣ Nat.card J) : T ⊓ J ≠ ⊥ := by
  have hTp : IsPGroup 3 T := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.1
  let K : Subgroup Y := T ⊔ J
  have hTK : T ≤ K := le_sup_left
  have hJK : J ≤ K := le_sup_right
  have hKN : K ≤ normalizer (J : Set Y) := sup_le hTN Subgroup.le_normalizer
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 3 T K :=
    CFSG.ABGLocalTools.IsSylowOf.of_le hT hTK le_top
  have hSylJ : CFSG.ABGLocalTools.IsSylowOf 3 (T ⊓ J) J :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hSylK hJK hKN
  intro hbot
  have hJne : Nat.card J ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨⟨1, J.one_mem⟩⟩, inferInstance⟩
  have hpos : 0 < (Nat.card J).factorization 3 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_three hJne hJ3
  have hdvd : 3 ∣ Nat.card (T ⊓ J : Subgroup Y) := by
    rw [hSylJ.card_eq]
    exact dvd_pow_self 3 (Nat.ne_of_gt hpos)
  rw [hbot, Subgroup.card_bot] at hdvd
  exact Nat.Prime.not_dvd_one Nat.prime_three hdvd

private theorem exists_central_ne_one_mem_inf {T J : Subgroup Y} (hTp : IsPGroup 3 T)
    (hTN : T ≤ normalizer (J : Set Y)) (hne : T ⊓ J ≠ ⊥) :
    ∃ w : T, w ≠ 1 ∧ (w : Y) ∈ T ⊓ J ∧ w ∈ Subgroup.center T := by
  have hTN' : T ≤ normalizer (T ⊓ J : Set Y) :=
    (le_inf (Subgroup.le_normalizer (H := T)) hTN).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := T) (K := J))
  let N : Subgroup T := (T ⊓ J).subgroupOf T
  have hNnormal : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := T ⊓ J) (K := T) inf_le_left).mpr hTN'
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxN : (⟨x, (Subgroup.mem_inf.mp hx).1⟩ : T) ∈ N := hx
    rw [hbot, Subgroup.mem_bot] at hxN
    simpa using congrArg Subtype.val hxN
  obtain ⟨w, hwne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (@CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      T _ _ 3 _ hTp N hNnormal hNne)
  obtain ⟨hwN, hwZ⟩ := Subgroup.mem_inf.mp w.2
  let wT : T := w
  refine ⟨wT, ?_, ?_, ?_⟩
  · exact fun h => hwne (Subtype.ext h)
  · exact Subgroup.mem_subgroupOf.mp (by simpa [N, wT] using hwN)
  · simpa [wT] using hwZ

private theorem exists_pow_order_three {T J : Subgroup Y} (hTp : IsPGroup 3 T) {w : T}
    (hwne : w ≠ 1) (hwZ : w ∈ Subgroup.center T) (hwJ : (w : Y) ∈ J) :
    ∃ w' : T, w' ≠ 1 ∧ w' ∈ Subgroup.center T ∧ orderOf w' = 3 ∧ (w' : Y) ∈ J := by
  let w' : T := w ^ (orderOf w / 3)
  have h3dvd : 3 ∣ orderOf w :=
    IsPGroup.dvd_orderOf (p := 3) (G := T) hTp (g := w) hwne
  have hw'ord : orderOf w' = 3 := by
    have h := orderOf_pow_orderOf_div (x := w) (n := 3)
      (orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite w)) h3dvd
    simpa [w'] using h
  refine ⟨w', ?_, Subgroup.pow_mem _ hwZ _, hw'ord, ?_⟩
  · intro h
    rw [h, orderOf_one] at hw'ord
    omega
  · simpa [w'] using Subgroup.pow_mem J hwJ (orderOf w / 3)

theorem false_of_component_of_not_dvd_card_center
    (hY : CFSG.Open.pRank 3 (⊤ : Subgroup Y) ≤ 3)
    {z : Y} (hz : z ∈ center Y) (hz3 : orderOf z = 3)
    {T : Subgroup Y} (hT : CFSG.ABGLocalTools.IsSylowOf 3 T ⊤)
    (hTz : ∀ w ∈ T, (∀ g ∈ T, g * w = w * g) → w ^ 3 = 1 → w ∈ zpowers z)
    {J : Subgroup Y} (hJ : CFSG.IsComponent J) (hJ3 : 3 ∣ Nat.card J)
    (hZJ : ¬ 3 ∣ Nat.card (center J)) : False := by
  have hTp : IsPGroup 3 T := (CFSG.ABGLocalTools.isSylowOf_iff.mp hT).2.1
  have hTN : T ≤ normalizer (J : Set Y) :=
    le_normalizer_of_component hY hz hz3 hJ hJ3 hZJ hTp
  have hne : T ⊓ J ≠ ⊥ := sylow_inf_ne_bot hT hTN hJ3
  obtain ⟨w, hwne, hwS₀, hwZ⟩ := exists_central_ne_one_mem_inf hTp hTN hne
  obtain ⟨w', hw'ne, hw'Z, hw'ord, hw'J⟩ :=
    exists_pow_order_three hTp hwne hwZ (Subgroup.mem_inf.mp hwS₀).2
  have hw'cent : ∀ g ∈ T, g * (w' : Y) = (w' : Y) * g := fun g hg =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hw'Z ⟨g, hg⟩)
  have hw'pow : (w' : Y) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one w'
    rw [hw'ord] at h
    simpa using congrArg Subtype.val h
  have hw'z : (w' : Y) ∈ zpowers z := hTz (w' : Y) w'.2 hw'cent hw'pow
  have hw'ordY : orderOf (w' : Y) = 3 := by rw [Subgroup.orderOf_coe, hw'ord]
  exact hZJ (dvd_card_center_of_mem_center hz hz3
    (mem_of_mem_zpowers_of_order_three hz3 hw'ordY hw'J hw'z))

end CFSG.GroupTheory.ComponentCentralRank
