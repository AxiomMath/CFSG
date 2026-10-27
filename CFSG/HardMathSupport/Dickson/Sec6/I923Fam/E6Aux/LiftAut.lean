module

public import CFSG.RankThree.PerfectCover.HopfCentralCoversSetup
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral
public import CFSG.Open.GLADefs

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG.RankThree.PerfectCover CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms
open Subgroup

theorem center_threeGroup_of_primeCore {Y : Type} [Group Y] [Finite Y]
    (hcore : CFSG.Open.GLAPPrimeCore 3 Y = ⊥) :
    ∀ z ∈ center Y, ∃ k : ℕ, z ^ (3 ^ k) = 1 := by
  intro z hz
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' 3 (by norm_num)
  refine ⟨a, ?_⟩
  have hwc : z ^ (3 ^ a) ∈ center Y := Subgroup.pow_mem _ hz _
  have hdvd : 3 ^ a ∣ orderOf z := ⟨m, hn⟩
  have hwo : orderOf (z ^ (3 ^ a)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a (by norm_num)) hdvd, hn,
      Nat.mul_div_cancel_left _ (pow_pos (by norm_num) a)]
  have hWn : (zpowers (z ^ (3 ^ a))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnc : n ∈ center Y := zpowers_le.2 hwc hn
    rw [mem_center_iff.1 hnc g, mul_inv_cancel_right]
    exact hn
  have hcop : Nat.Coprime 3 (Nat.card (zpowers (z ^ (3 ^ a)))) := by
    rw [Nat.card_zpowers, hwo]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm
  have hle : zpowers (z ^ (3 ^ a)) ≤ CFSG.Open.GLAPPrimeCore 3 Y := le_sSup ⟨hWn, hcop⟩
  rw [hcore] at hle
  exact Subgroup.mem_bot.1 (hle (mem_zpowers _))

theorem exists_mulAut_lift {Y P : Type} [Group Y] [Finite Y] [Group.IsPerfect Y] [Group P]
    (p : Y →* P) (hp : Function.Surjective p) (hker : p.ker ≤ center Y)
    (h3 : ∀ z ∈ p.ker, ∃ k : ℕ, z ^ (3 ^ k) = 1)
    (hM : ¬ 9 ∣ Nat.card (hopfMultiplier P)) (β : MulAut P) :
    ∃ β' : MulAut Y, ∀ y, p (β' y) = β (p y) := by
  classical
  haveI : Finite P := Finite.of_surjective p hp
  haveI hPperf : Group.IsPerfect P := Group.IsPerfect.ofSurjective (f := p) hp
  haveI : Group.IsPerfect (HopfCover P) := hopfCover_isPerfect
  haveI : Finite (HopfCover P) := finite_hopfCover hPperf
  set u : HopfCover P →* P := hopfCoverMap P with hu_def
  have hu : Function.Surjective u := hopfCoverMap_surjective
  have huc : u.ker ≤ center (HopfCover P) := hopfMultiplier_le_center
  set g : HopfCover P →* Y := hopfLift p hp hker with hg_def
  have hpg : p.comp g = u := comp_hopfLift p hp hker
  have hg : Function.Surjective g := hopfLift_surjective p hp hker
  set q : HopfCover P →* P := (β⁻¹ : MulAut P).toMonoidHom.comp u with hq_def
  have hq : Function.Surjective q := (β⁻¹ : MulAut P).surjective.comp hu
  have hqc : q.ker ≤ center (HopfCover P) := by
    intro x hx
    apply huc
    have h1 : (β⁻¹ : MulAut P) (u x) = 1 := hx
    rw [MonoidHom.mem_ker]
    simpa using h1
  set h : HopfCover P →* HopfCover P := hopfLift q hq hqc with hh_def
  have hqh : q.comp h = u := comp_hopfLift q hq hqc
  have hh : Function.Surjective h := hopfLift_surjective q hq hqc
  have huh : ∀ x, u (h x) = β (u x) := by
    intro x
    have h1 : q (h x) = u x := by rw [← MonoidHom.comp_apply, hqh]
    have h2 : (β⁻¹ : MulAut P) (u (h x)) = u x := h1
    rw [← h2]
    simp
  have hK : ∀ m ∈ g.ker, h m ∈ g.ker := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm ⊢
    have hum : u m = 1 := by rw [← hpg, MonoidHom.comp_apply, hm, map_one]
    have hzk : g (h m) ∈ p.ker := by
      rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hpg, huh, hum, map_one]
    by_cases htriv : p.ker = ⊥
    · rw [htriv] at hzk
      exact Subgroup.mem_bot.1 hzk
    · obtain ⟨w, hwk, hw1⟩ : ∃ w ∈ p.ker, w ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact htriv (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx))
      obtain ⟨k, hk⟩ := h3 w hwk
      have h3dvd : 3 ∣ Nat.card p.ker := by
        have h1 : orderOf (⟨w, hwk⟩ : p.ker) ∣ Nat.card p.ker := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk] at h1
        have h2 : orderOf w ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
        obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
        have hi0 : i ≠ 0 := by
          rintro rfl
          rw [pow_zero] at hio
          exact hw1 (orderOf_eq_one_iff.1 hio)
        exact (dvd_pow_self 3 hi0).trans (hio ▸ h1)
      set ψ := hopfMultiplierToKer p hp hker with hψ_def
      have hψs : Function.Surjective ψ := hopfMultiplierToKer_surjective p hp hker
      have hcard : Nat.card (hopfMultiplier P) = Nat.card p.ker * Nat.card ψ.ker :=
        card_eq_card_mul_card_ker ψ hψs
      have h3nd : ¬ 3 ∣ Nat.card ψ.ker := by
        intro hd
        exact hM (by
          rw [hcard]
          exact (Nat.mul_dvd_mul h3dvd hd : 3 * 3 ∣ _))
      have hmM : m ∈ hopfMultiplier P := hum
      have hmker : (⟨m, hmM⟩ : hopfMultiplier P) ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        exact Subtype.ext hm
      have hord3 : ¬ 3 ∣ orderOf m := by
        intro hd
        apply h3nd
        have h1 : orderOf (⟨⟨m, hmM⟩, hmker⟩ : ψ.ker) ∣ Nat.card ψ.ker := orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at h1
        exact hd.trans h1
      have hzo : orderOf (g (h m)) ∣ orderOf m :=
        orderOf_map_dvd (g.comp h) m
      have hz3 : ∃ i, orderOf (g (h m)) = 3 ^ i := by
        obtain ⟨k', hk'⟩ := h3 _ hzk
        obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1
          (orderOf_dvd_of_pow_eq_one hk')
        exact ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hz3
      have hi0 : i = 0 := by
        by_contra hne
        exact hord3 ((dvd_pow_self 3 hne).trans (hi ▸ hzo))
      rw [hi0, pow_zero] at hi
      exact orderOf_eq_one_iff.1 hi
  have hker' : g.ker ≤ (g.comp h).ker := fun m hm => by
    rw [MonoidHom.mem_ker]
    exact MonoidHom.mem_ker.1 (hK m hm)
  set β'hom : Y →* Y := (MonoidHom.liftOfSurjective g hg) ⟨g.comp h, hker'⟩ with hβ'hom
  have hβ'g : ∀ x, β'hom (g x) = g (h x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply g (Function.surjInv hg)
      (Function.rightInverse_surjInv hg) ⟨g.comp h, hker'⟩ x
  have hsurj : Function.Surjective β'hom := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    obtain ⟨x', rfl⟩ := hh x
    exact ⟨g x', hβ'g x'⟩
  have hbij : Function.Bijective β'hom := ⟨Finite.injective_iff_surjective.2 hsurj, hsurj⟩
  refine ⟨MulEquiv.ofBijective β'hom hbij, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hg y
  change p (β'hom (g x)) = β (p (g x))
  rw [hβ'g, ← MonoidHom.comp_apply p g, hpg, ← MonoidHom.comp_apply p g, hpg, huh]

theorem centerDescend_injective_of_perfect {Y : Type} [Group Y] [Group.IsPerfect Y] :
    Function.Injective (centerDescend Y) := by
  refine (injective_iff_map_eq_one (centerDescend Y)).2 fun α hα => ?_
  refine eq_one_of_forall_mul_inv_mem_center fun s => ?_
  have h1 := congrArg (fun τ : MulAut (Y ⧸ center Y) => τ (s : Y ⧸ center Y)) hα
  simp only [centerDescend_mk, MulAut.one_apply] at h1
  exact QuotientGroup.eq.mp h1.symm

theorem mem_commutator_of_descend_mem_commutator {Y P : Type} [Group Y] [Group.IsPerfect Y]
    [Group P] (e : (Y ⧸ center Y) ≃* P)
    (hlift : ∀ β : MulAut P, ∃ β' : MulAut Y, MulAut.congr e (centerDescend Y β') = β)
    {α : MulAut Y} (h : MulAut.congr e (centerDescend Y α) ∈ commutator (MulAut P)) :
    α ∈ commutator (MulAut Y) := by
  let Φ : MulAut Y →* MulAut P := (MulAut.congr e).toMonoidHom.comp (centerDescend Y)
  have hΦinj : Function.Injective Φ :=
    (MulAut.congr e).injective.comp centerDescend_injective_of_perfect
  have hΦsurj : Function.Surjective Φ := fun β => by
    obtain ⟨β', hβ'⟩ := hlift β
    exact ⟨β', hβ'⟩
  have hmap : (commutator (MulAut Y)).map Φ = commutator (MulAut P) := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hΦsurj,
      ← commutator_def]
  have hmem : Φ α ∈ (commutator (MulAut Y)).map Φ := by
    rw [hmap]
    exact h
  obtain ⟨α', hα', hαα'⟩ := hmem
  rw [← hΦinj hαα']
  exact hα'

theorem exists_descend_lift {Y P : Type} [Group Y] [Finite Y] [Group.IsPerfect Y] [Group P]
    (hcore : CFSG.Open.GLAPPrimeCore 3 Y = ⊥) (e : (Y ⧸ center Y) ≃* P)
    (hM : ¬ 9 ∣ Nat.card (hopfMultiplier P)) (β : MulAut P) :
    ∃ β' : MulAut Y, MulAut.congr e (centerDescend Y β') = β := by
  have hker : (centralQuotientMap e).ker = center Y := centralQuotientMap_ker e
  obtain ⟨β', hβ'⟩ := exists_mulAut_lift (centralQuotientMap e) (centralQuotientMap_surjective e)
    hker.le (fun z hz => center_threeGroup_of_primeCore hcore z (hker ▸ hz)) hM β
  refine ⟨β', MulEquiv.ext fun x => ?_⟩
  obtain ⟨y, rfl⟩ := centralQuotientMap_surjective e x
  have h1 : centerDescend Y β' (e.symm (centralQuotientMap e y)) =
      ((β' y : Y) : Y ⧸ center Y) := by
    rw [centralQuotientMap_apply, e.symm_apply_apply]
    rfl
  show e (centerDescend Y β' (e.symm (centralQuotientMap e y))) = β (centralQuotientMap e y)
  rw [h1, ← hβ' y]
  rfl

end CFSG.HardMathSupport.Dickson.Sec6.I923
