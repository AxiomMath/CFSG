module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87EngAb
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87EngCC
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Orders.Symplectic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Ly.KeySpec

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4

theorem card_comap_proj {F : Type} [Field F] (hodd : ringChar F ≠ 2) (X : Subgroup (StatedProj (StatedSp 2 F))) :
    Nat.card (X.comap (proj 2 F)) = Nat.card X * 2 := by
  have h2 := Ring.two_ne_zero hodd
  set Y := X.comap (proj 2 F) with hY
  have hZle : spScalars 2 F ≤ Y := fun z hz => by
    change proj 2 F z ∈ X
    rw [(MonoidHom.mem_ker).mp ((ker_proj (K := F)).symm ▸ hz)]
    exact X.one_mem
  have hker : ((proj 2 F).subgroupComap X).ker = (spScalars 2 F).subgroupOf Y := by
    ext g
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← ker_proj, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hkc : Nat.card ((proj 2 F).subgroupComap X).ker = 2 := by
    rw [hker, Nat.card_congr (subgroupOfEquivOfLe hZle).toEquiv, card_spScalars h2]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ((proj 2 F).subgroupComap X).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      ((proj 2 F).subgroupComap_surjective X proj_surjective)).toEquiv, hkc]


theorem exists_lift {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {X : Subgroup (StatedProj (StatedSp 2 F))} (hX : IsPGroup p X) :
    ∃ X₀ : Subgroup (StatedSp 2 F), IsPGroup p X₀ ∧ X₀.map (proj 2 F) = X ∧ Nat.card X₀ = Nat.card X ∧
      ∀ u : StatedSp 2 F, proj 2 F u ∈ normalizer (X : Set (StatedProj (StatedSp 2 F))) →
        ∀ z ∈ X₀, u * z * u⁻¹ ∈ X₀ := by
  classical
  have h2 := Ring.two_ne_zero hodd
  set Y := X.comap (proj 2 F) with hY
  have hcard : Nat.card Y = Nat.card X * 2 := card_comap_proj hodd X
  obtain ⟨a, ha⟩ := hX.exists_card_eq
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  let Q : Sylow p Y := default
  set X₀ : Subgroup (StatedSp 2 F) := (Q : Subgroup Y).map Y.subtype with hX₀
  have hQcard : Nat.card (Q : Subgroup Y) = p ^ a := by
    rw [Sylow.card_eq_multiplicity, hcard, ha, Nat.factorization_mul (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      (by norm_num), Finsupp.add_apply, (Fact.out : p.Prime).factorization_pow, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (fun h => hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp h))]
    rfl
  have hQp : IsPGroup p (Q : Subgroup Y) := Q.isPGroup'
  have hX₀p : IsPGroup p X₀ := hQp.map _
  have hX₀le : X₀ ≤ Y := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hX₀card : Nat.card X₀ = p ^ a := by
    rw [← hQcard]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ Y.subtype Subtype.val_injective).toEquiv.symm
  have hinj : Function.Injective ((proj 2 F).comp X₀.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hz1 : proj 2 F (z : StatedSp 2 F) = 1 := hz
    have hzs : (z : StatedSp 2 F) ∈ spScalars 2 F := by
      rw [← ker_proj]; exact hz1
    obtain ⟨k, hk⟩ := hX₀p z
    rw [mem_spScalars_iff] at hzs
    rw [Subgroup.mem_bot]
    rcases hzs with h | h
    · apply Subtype.ext
      apply sp_ext
      rw [h]
      rfl
    · exfalso
      have hz' : ((z : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) ^ p ^ k = 1 := by
        have := congrArg (fun y : X₀ => ((y : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)) hk
        simpa using this
      have hm := congrArg (fun g : GL (Fin 2 ⊕ Fin 2) F => (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hz'
      simp only [Units.val_pow_eq_pow_val, h, Units.val_one] at hm
      rw [(hpodd.pow : Odd (p ^ k)).neg_one_pow] at hm
      have hneg := congrFun (congrFun hm (Sum.inl 0)) (Sum.inl 0)
      simp at hneg
      apply h2
      linear_combination -hneg
  have hmapcard : Nat.card (X₀.map (proj 2 F)) = p ^ a := by
    have hr : ((proj 2 F).comp X₀.subtype).range = X₀.map (proj 2 F) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hr, ← hX₀card]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hmapleX : X₀.map (proj 2 F) ≤ X := fun x hx => by
    obtain ⟨z, hz, rfl⟩ := hx
    exact hX₀le hz
  have hmapeq : X₀.map (proj 2 F) = X :=
    Subgroup.eq_of_le_of_card_ge hmapleX (by rw [hmapcard, ha])
  have hidx : (Q : Subgroup Y).index = 2 := by
    have := (Q : Subgroup Y).card_mul_index
    rw [hQcard, hcard, ha] at this
    have hpos : 0 < p ^ a := pow_pos (Fact.out : p.Prime).pos a
    have : p ^ a * (Q : Subgroup Y).index = p ^ a * 2 := by rw [this]
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have hQnormal : (Q : Subgroup Y).Normal := Subgroup.normal_of_index_eq_two hidx
  have hsq : ∀ w : StatedSp 2 F, w ∈ Y → w ^ 2 ∈ X₀ := by
    intro w hw
    have := (Q : Subgroup Y).pow_index_mem (⟨w, hw⟩ : Y)
    rw [hidx] at this
    exact ⟨_, this, rfl⟩
  have hpel : ∀ w : StatedSp 2 F, w ∈ Y → ∀ k : ℕ, w ^ p ^ k = 1 → w ∈ X₀ := by
    intro w hw k hk
    obtain ⟨m, hm⟩ := (hpodd.pow : Odd (p ^ k))
    have hw2 := hsq w hw
    have : w = (w ^ 2) ^ (m + 1) := by
      have h1 : w ^ (2 * m + 1) = 1 := by rw [← hm]; exact hk
      calc w = w ^ (2 * m + 1) * w := by rw [h1, one_mul]
        _ = (w ^ 2) ^ (m + 1) := by rw [← pow_mul, ← pow_succ]; ring_nf
    rw [this]
    exact X₀.pow_mem hw2 _
  refine ⟨X₀, hX₀p, hmapeq, by rw [hX₀card, ha], ?_⟩
  intro u hu z hz
  have hzY : z ∈ Y := hX₀le hz
  have huzY : u * z * u⁻¹ ∈ Y := by
    change proj 2 F (u * z * u⁻¹) ∈ X
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hu (proj 2 F z)).mp hzY
  obtain ⟨k, hk⟩ := hX₀p ⟨z, hz⟩
  have hk' : z ^ p ^ k = 1 := congrArg Subtype.val hk
  apply hpel _ huzY k
  rw [conj_pow, hk', mul_one, mul_inv_cancel]


theorem cross_centralizes {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpl : ringChar F ≠ p) {X : Subgroup (StatedProj (StatedSp 2 F))} (hX : IsPGroup p X)
    {E : Subgroup (StatedSp 2 F)} (hE : Group.IsPerfect E)
    (hEN : ∀ e ∈ E, proj 2 F e ∈ normalizer (X : Set (StatedProj (StatedSp 2 F)))) :
    ∃ X₀ : Subgroup (StatedSp 2 F), IsPGroup p X₀ ∧ X₀.map (proj 2 F) = X ∧
      (∀ x ∈ X₀, ∀ y ∈ X₀, x * y = y * x) ∧ ∀ z ∈ X₀, ∀ e ∈ E, e * z = z * e := by
  classical
  obtain ⟨X₀, hX₀p, hmap, -, hnorm⟩ := exists_lift hodd hp2 hX
  have hab := pGroup_sp4_abelian hodd hp2 hpl X₀ hX₀p
  refine ⟨X₀, hX₀p, hmap, hab, ?_⟩
  let Z : Subgroup (GL (Fin 2 ⊕ Fin 2) F) := X₀.map (StatedSp 2 F).subtype
  let E' : Subgroup (GL (Fin 2 ⊕ Fin 2) F) := E.map (StatedSp 2 F).subtype
  have hℓ : (ringChar F).Prime := CharP.prime_ringChar F
  have hZab : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hab x hx y hy)
  have hZcard : Nat.card Z = Nat.card X₀ :=
    (Nat.card_congr (Subgroup.equivMapOfInjective X₀ (StatedSp 2 F).subtype Subtype.val_injective).toEquiv).symm
  obtain ⟨m, hm⟩ := hX₀p.exists_card_eq
  have hcop : Nat.Coprime (Nat.card Z) (ringChar F) := by
    rw [hZcard, hm]
    exact (Nat.Coprime.pow_left m ((Nat.coprime_primes (Fact.out : p.Prime) hℓ).mpr (Ne.symm hpl)))
  have hE' : Group.IsPerfect E' := Group.IsPerfect.map _
  have hEN' : ∀ e ∈ E', ∀ z ∈ Z, e * z * e⁻¹ ∈ Z := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨z, hz, rfl⟩
    exact ⟨e * z * e⁻¹, hnorm e (hEN e he) z hz, by simp⟩
  have key := perfect_centralizes_coprime_abelian (ι := Fin 2 ⊕ Fin 2) (by simp) Z E' hZab hcop hE' hEN'
  intro z hz e he
  exact Subtype.ext (key _ ⟨e, he, rfl⟩ _ ⟨z, hz, rfl⟩)


theorem card_psp4_three {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) (hF : Nat.card F = 3) :
    Nat.card (StatedProj (StatedSp 2 F)) = 25920 := by
  have h2 := Ring.two_ne_zero hodd
  have hP := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero (K := F) (n := 2) h2 (by norm_num)
  have hprod : ∏ j ∈ Finset.Icc 1 2, (Nat.card F ^ (2 * j) - 1) = (Nat.card F ^ 2 - 1) * (Nat.card F ^ 4 - 1) := by
    have e : Finset.Icc 1 2 = {1, 2} := by decide
    rw [e]; simp
  rw [hprod, hF] at hP
  norm_num at hP
  omega

theorem zmod5_cube (x : ZMod 5) (h : x * x * x = 1) : x = 1 := by
  revert x
  decide

theorem three_centralizes {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2) (hF : Nat.card F = 3)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hpl : ringChar F ≠ p)
    {X : Subgroup (StatedProj (StatedSp 2 F))} {X₀ : Subgroup (StatedSp 2 F)} (hX₀ : IsPGroup p X₀)
    (hcard : Nat.card X₀ = Nat.card X) (t : StatedSp 2 F) (ht : t ^ 3 = 1)
    (htN : ∀ z ∈ X₀, t * z * t⁻¹ ∈ X₀) : ∀ z ∈ X₀, t * z = z * t := by
  classical
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1]; simp
  have hℓ : ringChar F = 3 := by
    have h3 : ((3 : ℕ) : F) = 0 := by
      rw [← hF]
      have : Fintype F := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card]
      exact FiniteField.cast_card_eq_zero F
    have hd : ringChar F ∣ 3 := (CharP.cast_eq_zero_iff F (ringChar F) 3).mp h3
    exact (Nat.prime_dvd_prime_iff_eq (CharP.prime_ringChar F) Nat.prime_three).mp hd
  have hp3 : p ≠ 3 := fun h => hpl (by rw [hℓ, h])
  have hP := card_psp4_three hodd hF
  have hdvd : Nat.card X₀ ∣ 25920 := by
    rw [hcard, ← hP]
    exact Subgroup.card_subgroup_dvd_card X
  obtain ⟨m, hm⟩ := hX₀.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : Nat.card X₀ = 1 := by simpa using hm
    rw [Nat.card_eq_one_iff_unique] at this
    exact hz1 (congrArg Subtype.val (this.1.elim ⟨z, hz⟩ 1))
  have hp5 : p = 5 := by
    have h1 : p ∣ 25920 := by
      refine dvd_trans ?_ hdvd
      rw [hm]
      exact dvd_pow_self p hm0
    have h2 : p ∣ 2 ^ 6 * 3 ^ 4 * 5 := by norm_num; exact h1
    rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp h2 with h | h
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).mp h with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).mp ((Fact.out : p.Prime).dvd_of_dvd_pow h)) hp2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).mp ((Fact.out : p.Prime).dvd_of_dvd_pow h)) hp3
    · exact (Nat.prime_dvd_prime_iff_eq (Fact.out) (by norm_num)).mp h
  subst hp5
  have hm1 : m = 1 := by
    by_contra hne
    have h25 : 25 ∣ 25920 := by
      refine dvd_trans ?_ hdvd
      rw [hm]
      have : 2 ≤ m := by omega
      calc 25 = 5 ^ 2 := by norm_num
        _ ∣ 5 ^ m := pow_dvd_pow 5 this
    norm_num at h25
  subst hm1
  have hc5 : Nat.card X₀ = 5 := by simpa using hm
  set g : X₀ := ⟨z, hz⟩ with hg
  have hg1 : g ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have htop := zpowers_eq_top_of_prime_card (G := X₀) (p := 5) hc5 hg1
  have hmem : (⟨t * z * t⁻¹, htN z hz⟩ : X₀) ∈ Subgroup.zpowers g := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : t * z * t⁻¹ = z ^ k := congrArg Subtype.val hk.symm
  have hz5 : z ^ 5 = 1 := by
    have := pow_card_eq_one' (G := X₀) (x := g)
    rw [hc5] at this
    exact congrArg Subtype.val this
  have hord : orderOf z = 5 := orderOf_eq_prime hz5 hz1
  set c : MulAut (StatedSp 2 F) := MulAut.conj t with hc
  have hc1 : c z = z ^ k := by rw [hc, MulAut.conj_apply]; exact hk'
  have hc3 : c (c (c z)) = z := by
    have : (c * c * c) z = z := by
      have e : c * c * c = MulAut.conj (t * t * t) := by simp [hc, map_mul]
      rw [e]
      have : t * t * t = 1 := (pow_three' t).symm.trans ht
      rw [this, map_one]; rfl
    exact this
  have hc2 : c (c (c z)) = z ^ (k * k * k) := by
    have e2 : c (z ^ k) = z ^ (k * k) := by rw [map_zpow, hc1, ← zpow_mul]
    have e3 : c (z ^ (k * k)) = z ^ (k * k * k) := by rw [map_zpow, hc1, ← zpow_mul, mul_assoc]
    rw [hc1, e2, e3]
  rw [hc2] at hc3
  have hdiv : (5 : ℤ) ∣ k * k * k - 1 := by
    have h1 : z ^ (k * k * k - 1) = 1 := by rw [zpow_sub_one, hc3, mul_inv_cancel]
    have := (orderOf_dvd_iff_zpow_eq_one (x := z) (i := k * k * k - 1)).mpr h1
    rw [hord] at this
    exact_mod_cast this
  have hk1 : (5 : ℤ) ∣ k - 1 := by
    have h1 : (((k * k * k - 1 : ℤ)) : ZMod 5) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr (by exact_mod_cast hdiv)
    have h2 : (k : ZMod 5) = 1 := zmod5_cube _ (by
      push_cast at h1
      linear_combination h1)
    have h3 : (((k - 1 : ℤ)) : ZMod 5) = 0 := by push_cast; rw [h2]; ring
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mp h3
  have hzk : z ^ k = z := by
    have h1 : z ^ (k - 1) = 1 :=
      (orderOf_dvd_iff_zpow_eq_one (x := z) (i := k - 1)).mp (by rw [hord]; exact_mod_cast hk1)
    rw [zpow_sub_one] at h1
    exact mul_inv_eq_one.mp h1
  rw [hzk] at hk'
  calc t * z = (t * z * t⁻¹) * t := by group
    _ = z * t := by rw [hk']

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
