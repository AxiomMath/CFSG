module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.XFiveLemma

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup

section Sup

variable {X : Type*} [Group X]

theorem exists_zpow_mul_of_mem_sup {A : Subgroup X} {t : X} (h : ∀ a ∈ A, a * t = t * a) {g : X}
    (hg : g ∈ zpowers t ⊔ A) : ∃ n : ℤ, ∃ a ∈ A, g = t ^ n * a := by
  have hc : ∀ (n : ℤ) (a : X), a ∈ A → a * t ^ n = t ^ n * a := fun n a ha =>
    ((show Commute a t from h a ha).zpow_right n)
  let S : Subgroup X :=
    { carrier := {g | ∃ n : ℤ, ∃ a ∈ A, g = t ^ n * a}
      mul_mem' := by
        rintro _ _ ⟨n, a, ha, rfl⟩ ⟨m, b, hb, rfl⟩
        refine ⟨n + m, a * b, A.mul_mem ha hb, ?_⟩
        calc t ^ n * a * (t ^ m * b) = t ^ n * (a * t ^ m) * b := by simp only [mul_assoc]
          _ = t ^ n * (t ^ m * a) * b := by rw [hc m a ha]
          _ = t ^ (n + m) * (a * b) := by rw [zpow_add]; simp only [mul_assoc]
      one_mem' := ⟨0, 1, A.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨n, a, ha, rfl⟩
        refine ⟨-n, a⁻¹, A.inv_mem ha, ?_⟩
        have := hc (-n) a ha
        calc (t ^ n * a)⁻¹ = a⁻¹ * (t ^ n)⁻¹ := mul_inv_rev _ _
          _ = a⁻¹ * t ^ (-n) := by rw [zpow_neg]
          _ = t ^ (-n) * a⁻¹ := by
            exact (show Commute a (t ^ (-n)) from this).inv_left }
  have hle : zpowers t ⊔ A ≤ S := by
    refine sup_le ?_ (fun a ha => ⟨0, a, ha, by simp⟩)
    rintro _ ⟨n, rfl⟩
    exact ⟨n, 1, A.one_mem, by simp⟩
  exact hle hg

end Sup

section OddCore

variable (X : Type*) [Group X]

theorem natCard_fusionOddCore_odd' [Finite X] : Odd (Nat.card (Open.fusionOddCore X)) := by
  have h : Open.fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold Open.fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

variable {X}

theorem le_fusionOddCore_of_odd' {N : Subgroup X} [N.Normal] (hN : Odd (Nat.card N)) :
    N ≤ Open.fusionOddCore X :=
  le_sSup ⟨inferInstance, hN⟩

theorem natCard_comap_of_surjective' {E H : Type*} [Group E] [Group H] (f : E →* H)
    (hf : Function.Surjective f) (P : Subgroup H) [Finite E] :
    Nat.card (P.comap f) = Nat.card f.ker * Nat.card P := by
  let g : P.comap f →* P := (f.comp (P.comap f).subtype).codRestrict P (fun x => x.2)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change f x ∈ P
    rw [hx]
    exact y.2
  have hker : g.ker = f.ker.subgroupOf (P.comap f) := by
    ext x
    change ((g x : P) = 1) ↔ f x = 1
    exact Subtype.ext_iff
  have h1 := Subgroup.card_ker_mul_card_of_surjective hg
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (P.ker_le_comap f)).toEquiv] at h1
  exact h1.symm

theorem fusionOddCore_quotient_eq_bot' (X : Type*) [Group X] [Finite X] :
    Open.fusionOddCore (X ⧸ Open.fusionOddCore X) = ⊥ := by
  let π : X →* X ⧸ Open.fusionOddCore X := QuotientGroup.mk' (Open.fusionOddCore X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = Open.fusionOddCore X := QuotientGroup.ker_mk' _
  let N : Subgroup X := (Open.fusionOddCore (X ⧸ Open.fusionOddCore X)).comap π
  have hNnormal : N.Normal :=
    (inferInstance : (Open.fusionOddCore (X ⧸ Open.fusionOddCore X)).Normal).comap π
  have hcard : Nat.card N =
      Nat.card (Open.fusionOddCore X) *
        Nat.card (Open.fusionOddCore (X ⧸ Open.fusionOddCore X)) := by
    rw [natCard_comap_of_surjective' π hπ, hker]
  have hodd : Odd (Nat.card N) := by
    rw [hcard]
    exact (natCard_fusionOddCore_odd' X).mul (natCard_fusionOddCore_odd' _)
  have hle : N ≤ Open.fusionOddCore X := le_fusionOddCore_of_odd' hodd
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hπ x
  have hy : y ∈ Open.fusionOddCore X := hle hx
  have : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  rw [this]
  exact one_mem _

end OddCore

section Five

theorem perm5_card : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm]
  simp [Nat.factorial]

theorem perm5_odd_normal (N : Subgroup (Equiv.Perm (Fin 5))) [N.Normal]
    (hN : Odd (Nat.card N)) : N = ⊥ := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := a5_isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5))) with
    h | h
  · rw [eq_bot_iff]
    intro n hn
    rw [mem_bot]
    have hn2A : n ^ 2 ∈ alternatingGroup (Fin 5) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_pow, Int.units_pow_two]
    have hn2 : (⟨n ^ 2, hn2A⟩ : alternatingGroup (Fin 5)) ∈
        N.subgroupOf (alternatingGroup (Fin 5)) := N.pow_mem hn 2
    rw [h, mem_bot] at hn2
    have hsq : n ^ 2 = 1 := congrArg Subtype.val hn2
    have h1 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have h2 : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
    have h3 : Odd (orderOf n) := Odd.of_dvd_nat hN h2
    have : orderOf n = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h4 | h4
      · exact h4
      · rw [h4] at h3; exact absurd h3 (by decide)
    exact orderOf_eq_one_iff.1 this
  · exfalso
    have hle : alternatingGroup (Fin 5) ≤ N := by
      intro a ha
      have : (⟨a, ha⟩ : alternatingGroup (Fin 5)) ∈ N.subgroupOf (alternatingGroup (Fin 5)) := by
        rw [h]; exact mem_top _
      exact this
    have hd := Subgroup.card_dvd_of_le hle
    rw [a5_card] at hd
    have h2 : 2 ∣ Nat.card N := Nat.dvd_trans (by norm_num) hd
    exact (Nat.not_even_iff_odd.2 hN) (even_iff_two_dvd.2 h2)

variable {X : Type*} [Group X]

theorem inf_eq_bot_of_odd {K : Subgroup X} (e : K ≃* Equiv.Perm (Fin 5)) {N : Subgroup X}
    [N.Normal] [Finite N] (hN : Odd (Nat.card N)) : N ⊓ K = ⊥ := by
  have hnorm : (N.subgroupOf K).Normal := inferInstance
  have hM : ((N.subgroupOf K).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map hnorm e.toMonoidHom e.surjective
  let f : N.subgroupOf K →* N :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    have h' : (f a).1 = (f b).1 := by rw [hab]
    exact Subtype.ext (Subtype.ext h')
  have hdvd : Nat.card (N.subgroupOf K) ∣ Nat.card N := Subgroup.card_dvd_of_injective f hf
  have hodd : Odd (Nat.card ((N.subgroupOf K).map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact Odd.of_dvd_nat hN hdvd
  have hbot := perm5_odd_normal _ hodd
  rw [eq_bot_iff]
  intro n hn
  rw [mem_bot]
  have hnK : n ∈ K := hn.2
  have hmem : e ⟨n, hnK⟩ ∈ (N.subgroupOf K).map e.toMonoidHom := ⟨⟨n, hnK⟩, hn.1, rfl⟩
  rw [hbot, mem_bot] at hmem
  have : (⟨n, hnK⟩ : K) = 1 := e.injective (by rw [hmem, map_one])
  exact congrArg Subtype.val this

end Five

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
