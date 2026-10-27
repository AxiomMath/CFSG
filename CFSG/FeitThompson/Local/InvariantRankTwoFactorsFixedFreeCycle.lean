module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
import CFSG.FeitThompson.Local.OutsideNormalizedLineFixedTrivial
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
import CFSG.FeitThompson.Foundations.LiftHallByNormalComplement
import CFSG.FeitThompson.Foundations.FullExponentCyclicLiftLayer
import CFSG.FeitThompson.Foundations.CoprimeSubgroupInConjugateComplement

open Pointwise

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem sup_eq_of_coe_mul_eq {S S₀ S₁ : Subgroup G}
    (hprod : (S₀ : Set G) * (S₁ : Set G) = (S : Set G)) : S₀ ⊔ S₁ = S := by
  have hS₀ : S₀ ≤ S := fun x hx => by
    have h : x * 1 ∈ (S₀ : Set G) * (S₁ : Set G) := Set.mul_mem_mul hx (one_mem S₁)
    rw [hprod, mul_one] at h
    exact h
  have hS₁ : S₁ ≤ S := fun x hx => by
    have h : 1 * x ∈ (S₀ : Set G) * (S₁ : Set G) := Set.mul_mem_mul (one_mem S₀) hx
    rw [hprod, one_mul] at h
    exact h
  refine le_antisymm (sup_le hS₀ hS₁) fun x hx => ?_
  have h : x ∈ (S₀ : Set G) * (S₁ : Set G) := by rw [hprod]; exact hx
  obtain ⟨a, ha, b, hb, rfl⟩ := h
  exact Subgroup.mul_mem_sup ha hb

theorem le_normalizer_of_normal_subgroupOf {Z K : Subgroup G} (hZK : Z ≤ K)
    (hn : (Z.subgroupOf K).Normal) : K ≤ normalizer (Z : Set G) :=
  Subgroup.le_normalizer_iff.2 fun k hk z hz =>
    (Subgroup.normal_subgroupOf_iff hZK).1 hn z k hz hk

theorem normal_subgroupOf_of_le_normalizer {Z K : Subgroup G} (hZK : Z ≤ K)
    (h : K ≤ normalizer (Z : Set G)) : (Z.subgroupOf K).Normal :=
  (Subgroup.normal_subgroupOf_iff hZK).2 fun z k hz hk =>
    Subgroup.le_normalizer_iff.1 h k hk z hz

theorem subgroupOf_ne_bot {S T : Subgroup G} (hTS : T ≤ S) (hT : T ≠ ⊥) : T.subgroupOf S ≠ ⊥ := by
  intro h
  rw [← Subgroup.map_subgroupOf_eq_of_le hTS, h, Subgroup.map_bot] at hT
  exact hT rfl

theorem exponent_subgroupOf_eq {S T : Subgroup G} (hTS : T ≤ S) :
    Monoid.exponent ↥(T.subgroupOf S) = Monoid.exponent ↥T :=
  Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hTS)

theorem isCyclic_of_isCyclic_subgroupOf {S T : Subgroup G} (hTS : T ≤ S)
    (h : IsCyclic ↥(T.subgroupOf S)) : IsCyclic ↥T :=
  isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hTS)
    (Subgroup.subgroupOfEquivOfLe hTS).surjective

theorem exponent_eq_of_sup_eq_top {A : Type*} [CommGroup A] {A₀ A₁ : Subgroup A}
    (hsup : A₀ ⊔ A₁ = ⊤) (hdvd : Monoid.exponent ↥A₁ ∣ Monoid.exponent ↥A₀) :
    Monoid.exponent A = Monoid.exponent ↥A₀ := by
  refine Nat.dvd_antisymm (Monoid.exponent_dvd_of_forall_pow_eq_one fun s => ?_)
    (Monoid.exponent_dvd_of_monoidHom A₀.subtype A₀.subtype_injective)
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.1 (hsup ▸ Subgroup.mem_top s)
  obtain ⟨c, hc⟩ := hdvd
  have hbpow : b ^ Monoid.exponent ↥A₀ = 1 := by
    rw [hc, pow_mul, Subgroup.pow_exponent_eq_one hb, one_pow]
  rw [← hab, mul_pow, Subgroup.pow_exponent_eq_one ha, hbpow, one_mul]

theorem card_omega1_of_isCyclic {C : Type*} [CommGroup C] [IsCyclic C] [Finite C] [Nontrivial C]
    (hp : p.Prime) (hC : IsPGroup p C) : Nat.card ↥(omega1 p C) = p := by
  have := Fact.mk hp
  obtain ⟨n, hn, hcard⟩ := hC.nontrivial_iff_card.mp ‹Nontrivial C›
  rw [omega1_eq_ker_powMonoidHom, IsCyclic.card_powMonoidHom_ker, hcard,
    Nat.gcd_eq_right (dvd_pow_self p hn.ne')]

theorem isCyclic_of_inf_eq_bot_of_three_notMem (hp : p.Prime) (hodd : Odd p) {A : Type*}
    [CommGroup A] [Finite A] (hAp : IsPGroup p A) (h3 : 3 ∉ elementaryAbelianRanks p A)
    {A₀ A₁ : Subgroup A} (hdisj : A₀ ⊓ A₁ = ⊥) (hA₁ : A₁ ≠ ⊥) : IsCyclic ↥A₀ := by
  have := Fact.mk hp
  by_contra hnc
  obtain ⟨E, hEA₀, -, ⟨f⟩⟩ := exists_normal_le_mulEquiv_pi_of_not_isCyclic hp hodd hAp A₀ hnc
  have hEcard : Nat.card ↥E = p ^ 2 := by
    rw [Nat.card_congr f.toEquiv, card_pi_multiplicative_zmod]
  have hEexp : ∀ x ∈ E, x ^ p = 1 := fun x hx =>
    congrArg (Subgroup.subtype E)
      (f.injective (by rw [map_pow, pow_eq_one_pi_multiplicative_zmod, map_one]) :
        (⟨x, hx⟩ : ↥E) ^ p = 1)
  have hA₁nt : Nontrivial ↥A₁ := (Subgroup.nontrivial_iff_ne_bot A₁).2 hA₁
  obtain ⟨n, hn, hncard⟩ := (hAp.to_subgroup A₁).nontrivial_iff_card.mp hA₁nt
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥A₁) p
    (hncard ▸ dvd_pow_self p hn.ne')
  have hZcard : Nat.card ↥(zpowers (b : A)) = p := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe b, hb]
  have hEZ : E ⊓ zpowers (b : A) = ⊥ :=
    le_bot_iff.1 ((inf_le_inf hEA₀ (zpowers_le.2 b.2)).trans hdisj.le)
  have hprod :
      (E : Set A) * (zpowers (b : A) : Set A) = ((E ⊔ zpowers (b : A) : Subgroup A) : Set A) :=
    (Subgroup.mul_normal E _).symm
  have hcard : Nat.card ↥(E ⊔ zpowers (b : A) : Subgroup A) = p ^ 3 := by
    rw [natCard_eq_mul_of_mul_eq_of_inf_eq_bot hprod hEZ, hEcard, hZcard]; ring
  refine h3 ((mem_elementaryAbelianRanks_iff_exists_subgroup hp).2
    ⟨E ⊔ zpowers (b : A), inferInstance, ?_, hcard⟩)
  intro x hx
  obtain ⟨e, he, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
  have hzp : z ^ p = 1 := by
    have h : (⟨z, hz⟩ : ↥(zpowers (b : A))) ^ Nat.card ↥(zpowers (b : A)) = 1 := pow_card_eq_one'
    rw [hZcard] at h
    exact congrArg (Subgroup.subtype _) h
  rw [mul_pow, hEexp e he, hzp, one_mul]

theorem normal_subgroupOf_and_inf_centralizer_singleton_eq_bot [Finite G] (hp : p.Prime)
    {M H U S Z : Subgroup G} (hZS : Z ≤ S) (hZU : Z ≤ U) (hSp : IsPGroup p ↥S)
    (hcyc : IsCyclic ↥Z) (hZnt : Z ≠ ⊥)
    (hNS : ¬ normalizer (S : Set G) ≤ M)
    (hNZ : normalizer (S : Set G) ≤ normalizer (Z : Set G))
    (hUN : U ≤ normalizer (S : Set G))
    (hreg : ∀ B : Subgroup G, B ≤ S → Nat.card ↥B = p →
      H ⊓ centralizer (B : Set G) ≠ ⊥ → normalizer (B : Set G) ≤ M) :
    (Z.subgroupOf U).Normal ∧ ∀ z ∈ Z, z ≠ 1 → H ⊓ centralizer ({z} : Set G) = ⊥ := by
  have := Fact.mk hp
  have hZp : IsPGroup p ↥Z := hSp.to_le hZS
  have hZntt : Nontrivial ↥Z := (Subgroup.nontrivial_iff_ne_bot Z).2 hZnt
  let _ : CommGroup ↥Z := IsCyclic.commGroup
  set B : Subgroup G := (omega1 p ↥Z).map Z.subtype with hBdef
  have hBS : B ≤ S := (Subgroup.map_subtype_le _).trans hZS
  have hBcard : Nat.card ↥B = p := by
    rw [hBdef, Subgroup.card_map_of_injective Z.subtype_injective, card_omega1_of_isCyclic hp hZp]
  have hOmega : {x ∈ (Z : Set G) | x ^ p = 1} = (B : Set G) :=
    coe_inf_omega1_map_eq Z.subtype Z.subtype_injective
      (by rw [← Subgroup.subgroupOf_self Z, Subgroup.map_subgroupOf_eq_of_le le_rfl]) rfl
      (top_inf_eq _)
  have hCB : H ⊓ centralizer (B : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of_normalizer_not_le hNS
      (hNZ.trans (normalizer_le_normalizer_map_subtype Z _)) (hreg B hBS hBcard)
  exact ⟨normal_subgroupOf_of_le_normalizer hZU (hUN.trans hNZ), fun z hz hz1 =>
    inf_centralizer_singleton_eq_bot_of_inf_centralizer_eq_bot hp hSp hZS hBcard hOmega hCB hz hz1⟩

theorem exists_cyclic_normal_exponent_eq_of_sup_eq [Finite G] (hp : p.Prime) (hodd : Odd p)
    {M H U S S₀ S₁ : Subgroup G} (hSU : S ≤ U) (hSab : IsMulCommutative ↥S)
    (hSp : IsPGroup p ↥S) (h3 : 3 ∉ elementaryAbelianRanks p ↥S)
    (hNS : ¬ normalizer (S : Set G) ≤ M)
    (hreg : ∀ B : Subgroup G, B ≤ S → Nat.card ↥B = p →
      H ⊓ centralizer (B : Set G) ≠ ⊥ → normalizer (B : Set G) ≤ M)
    (hSnormU : (S.subgroupOf U).Normal)
    (hsup : S₀ ⊔ S₁ = S) (hdisj : S₀ ⊓ S₁ = ⊥) (hS₀nt : S₀ ≠ ⊥) (hS₁nt : S₁ ≠ ⊥)
    (hS₀norm : (S₀.subgroupOf (normalizer (S : Set G))).Normal)
    (hS₁norm : (S₁.subgroupOf (normalizer (S : Set G))).Normal) :
    ∃ Z : Subgroup G, Z ≤ S ∧ IsCyclic ↥Z ∧ (Z.subgroupOf U).Normal ∧
      Monoid.exponent ↥Z = Monoid.exponent ↥S ∧
      ∀ z ∈ Z, z ≠ 1 → H ⊓ centralizer ({z} : Set G) = ⊥ := by
  have := Fact.mk hp
  let _ : CommGroup ↥S := { S.toGroup with mul_comm := fun a b => hSab.is_comm.comm a b }
  have hS₀S : S₀ ≤ S := hsup ▸ le_sup_left
  have hS₁S : S₁ ≤ S := hsup ▸ le_sup_right
  have hUN : U ≤ normalizer (S : Set G) := le_normalizer_of_normal_subgroupOf hSU hSnormU
  have hSN : S ≤ normalizer (S : Set G) := Subgroup.le_normalizer
  have hAdisj : S₀.subgroupOf S ⊓ S₁.subgroupOf S = ⊥ := by
    rw [← inf_subgroupOf, hdisj, Subgroup.bot_subgroupOf]
  have hc₀ : IsCyclic ↥S₀ := isCyclic_of_isCyclic_subgroupOf hS₀S
    (isCyclic_of_inf_eq_bot_of_three_notMem hp hodd hSp h3 hAdisj (subgroupOf_ne_bot hS₁S hS₁nt))
  have hc₁ : IsCyclic ↥S₁ := isCyclic_of_isCyclic_subgroupOf hS₁S
    (isCyclic_of_inf_eq_bot_of_three_notMem hp hodd hSp h3 (by rw [inf_comm]; exact hAdisj)
      (subgroupOf_ne_bot hS₀S hS₀nt))
  have key : ∀ T T' : Subgroup G, T ≤ S → T' ≤ S → T ⊔ T' = S → T ≠ ⊥ → IsCyclic ↥T →
      normalizer (S : Set G) ≤ normalizer (T : Set G) →
      Monoid.exponent ↥T' ∣ Monoid.exponent ↥T →
      ∃ Z : Subgroup G, Z ≤ S ∧ IsCyclic ↥Z ∧ (Z.subgroupOf U).Normal ∧
        Monoid.exponent ↥Z = Monoid.exponent ↥S ∧
        ∀ z ∈ Z, z ≠ 1 → H ⊓ centralizer ({z} : Set G) = ⊥ := by
    intro T T' hTS hT'S hTsup hTnt hTcyc hTnorm hdvd
    have hexpS : Monoid.exponent ↥S = Monoid.exponent ↥T := by
      rw [exponent_eq_of_sup_eq_top (A₀ := T.subgroupOf S) (A₁ := T'.subgroupOf S)
          (by rw [← Subgroup.subgroupOf_sup hTS hT'S, hTsup, Subgroup.subgroupOf_self])
          (by rw [exponent_subgroupOf_eq hT'S, exponent_subgroupOf_eq hTS]; exact hdvd),
        exponent_subgroupOf_eq hTS]
    obtain ⟨hnorm, hff⟩ := normal_subgroupOf_and_inf_centralizer_singleton_eq_bot hp hTS
      (hTS.trans hSU) hSp hTcyc hTnt hNS hTnorm hUN hreg
    exact ⟨T, hTS, hTcyc, hnorm, hexpS.symm, hff⟩
  have hN₀ : normalizer (S : Set G) ≤ normalizer (S₀ : Set G) :=
    le_normalizer_of_normal_subgroupOf (hS₀S.trans hSN) hS₀norm
  have hN₁ : normalizer (S : Set G) ≤ normalizer (S₁ : Set G) :=
    le_normalizer_of_normal_subgroupOf (hS₁S.trans hSN) hS₁norm
  obtain ⟨k₀, hk₀⟩ := (hSp.to_le hS₀S).exists_exponent_eq_pow
  obtain ⟨k₁, hk₁⟩ := (hSp.to_le hS₁S).exists_exponent_eq_pow
  rcases Nat.le_total k₁ k₀ with hle | hle
  · exact key S₀ S₁ hS₀S hS₁S hsup hS₀nt hc₀ hN₀ (by rw [hk₀, hk₁]; exact pow_dvd_pow p hle)
  · exact key S₁ S₀ hS₁S hS₀S (by rw [sup_comm]; exact hsup) hS₁nt hc₁ hN₁
      (by rw [hk₀, hk₁]; exact pow_dvd_pow p hle)

theorem exists_cyclic_normal_exponent_eq_of_mul_eq [Finite G] (hp : p.Prime) (hodd : Odd p)
    {M H U S S₀ S₁ : Subgroup G} (hSU : S ≤ U) (hSab : IsMulCommutative ↥S)
    (hSp : IsPGroup p ↥S) (h3 : 3 ∉ elementaryAbelianRanks p ↥S)
    (hNS : ¬ normalizer (S : Set G) ≤ M)
    (hreg : ∀ B : Subgroup G, B ≤ S → Nat.card ↥B = p →
      H ⊓ centralizer (B : Set G) ≠ ⊥ → normalizer (B : Set G) ≤ M)
    (hSnormU : (S.subgroupOf U).Normal)
    (hprod : (S₀ : Set G) * (S₁ : Set G) = (S : Set G)) (hdisj : S₀ ⊓ S₁ = ⊥)
    (hS₀nt : S₀ ≠ ⊥) (hS₁nt : S₁ ≠ ⊥)
    (hS₀norm : (S₀.subgroupOf (normalizer (S : Set G))).Normal)
    (hS₁norm : (S₁.subgroupOf (normalizer (S : Set G))).Normal) :
    ∃ Z : Subgroup G, Z ≤ S ∧ IsCyclic ↥Z ∧ (Z.subgroupOf U).Normal ∧
      Monoid.exponent ↥Z = Monoid.exponent ↥S ∧
      ∀ z ∈ Z, z ≠ 1 → H ⊓ centralizer ({z} : Set G) = ⊥ :=
  exists_cyclic_normal_exponent_eq_of_sup_eq hp hodd hSU hSab hSp h3 hNS hreg hSnormU
    (sup_eq_of_coe_mul_eq hprod) hdisj hS₀nt hS₁nt hS₀norm hS₁norm

end

end CFSG.FeitThompson
