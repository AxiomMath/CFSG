module

public import CFSG.CharacterTheory.Semidihedral.OddProjectiveCoverKernel
public import CFSG.GH74.GLS.Stage4.RestSetup

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup

theorem ng_isCyclic_pSubgroup_of_surjective {X Y : Type} [Group X] [Finite X] [Group Y] [Finite Y]
    {p : ℕ} [Fact p.Prime] (hX : ∀ P : Subgroup X, IsPGroup p ↥P → IsCyclic ↥P) (ψ : X →* Y)
    (hψ : Function.Surjective ψ) (P : Subgroup Y) (hP : IsPGroup p ↥P) : IsCyclic ↥P := by
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hψ p S
  have hcycT : IsCyclic ↥(T : Subgroup X) := hX _ T.isPGroup'
  have hmap : (T : Subgroup X).map ψ = (S : Subgroup Y) := by
    rw [← Sylow.coe_mapSurjective hψ, hT]
  have hS : IsCyclic ↥(S : Subgroup Y) := by
    rw [← hmap]
    exact isCyclic_of_surjective (ψ.subgroupMap (T : Subgroup X)) (ψ.subgroupMap_surjective _)
  have : IsCyclic ↥(P.subgroupOf (S : Subgroup Y)) := inferInstance
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPS).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hPS).surjective

theorem ng_card_le_of_cyclic_exp {P : Type} [Group P] [Finite P] [IsCyclic P] {p : ℕ} (hp : p.Prime)
    (hexp : ∀ x : P, x ^ p = 1) : Nat.card P ≤ p := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := P)
  have hord : orderOf g = Nat.card P := orderOf_eq_card_of_forall_mem_zpowers hg
  have hd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (hexp g)
  rw [hord] at hd
  exact Nat.le_of_dvd hp.pos hd

theorem rank_pSubgroup_K {G : Type} [Group G] [Finite G] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁] [Finite F₂]
    (e₁ : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁)
    (e₂ : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂) (hodd₁ : Odd (Nat.card F₁))
    (h₂ : Nat.card F₂ = p ^ n) (h₁ : ¬ p ∣ Nat.card F₁)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x)
    {A : Subgroup G} (hA : A ≤ K₁ ⊔ K₂) (hAp : IsPGroup p ↥A)
    (hAexp : ∀ x ∈ A, x ^ p = 1) :
    Nat.card ↥A ≤ p ^ (n + 1) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set M : Subgroup G := K₁ ⊔ K₂ with hM
  have hcycSL : ∀ P : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F₁), IsPGroup p ↥P → IsCyclic ↥P := by
    intro P hP
    obtain ⟨R, hPR⟩ := hP.exists_le_sylow
    have : IsCyclic ↥(R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F₁)) := by
      have := Fintype.ofFinite F₁
      obtain ⟨p₁, -, n₁, hp₁, hcard⟩ := FiniteField.card' F₁
      have hcard' : Nat.card F₁ = p₁ ^ (n₁ : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
      have hp₁2 : p₁ ≠ 2 := by
        rintro rfl
        have := hodd₁
        rw [hcard'] at this
        exact (Nat.not_even_iff_odd.2 this) (Nat.even_pow.2 ⟨even_two, n₁.pos.ne'⟩)
      have : Fact p₁.Prime := ⟨hp₁⟩
      have hcharF : CharP F₁ p₁ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
      have hring : ringChar F₁ = p₁ := ringChar.eq F₁ p₁
      have hpp₁ : p ≠ p₁ := by
        rintro rfl
        exact h₁ (by rw [hcard']; exact dvd_pow_self p n₁.pos.ne')
      exact CFSG.Semidihedral.OddProjectiveCoverKernel.nativeSL_odd_sylow_cyclic F₁ hp₁
        (by rw [hring]; exact hp₁2) hcard' hp hp2 hpp₁ R
    have h2 : IsCyclic ↥(P.subgroupOf (R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F₁))) := inferInstance
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPR).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPR).surjective
  have hnormQ : (K₂.subgroupOf M).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨a, ha, b, hb, hgab⟩ := (mem_sup_iff_of_comm hcomm (g : G)).1 g.2
    have hcx : (b * (x : G) * b⁻¹) ∈ K₂ := K₂.mul_mem (K₂.mul_mem hb hx) (K₂.inv_mem hb)
    have hac : a * (b * (x : G) * b⁻¹) = (b * (x : G) * b⁻¹) * a := hcomm a ha _ hcx
    have : ((g * x * g⁻¹ : ↥M) : G) = b * (x : G) * b⁻¹ := by
      show (g : G) * (x : G) * (g : G)⁻¹ = _
      rw [hgab]
      calc a * b * (x : G) * (a * b)⁻¹ = a * (b * (x : G) * b⁻¹) * a⁻¹ := by group
        _ = b * (x : G) * b⁻¹ := by rw [hac]; group
    rw [this]
    exact hcx
  let mkQ : ↥M →* ↥M ⧸ K₂.subgroupOf M := QuotientGroup.mk' (K₂.subgroupOf M)
  let ψ : ↥K₁ →* ↥M ⧸ K₂.subgroupOf M := mkQ.comp (Subgroup.inclusion le_sup_left)
  have hψ : Function.Surjective ψ := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, ha, b, hb, hmab⟩ := (mem_sup_iff_of_comm hcomm (m : G)).1 m.2
    refine ⟨⟨a, ha⟩, ?_⟩
    show mkQ (Subgroup.inclusion le_sup_left ⟨a, ha⟩) = mkQ m
    have hm : m = Subgroup.inclusion le_sup_left ⟨a, ha⟩ * Subgroup.inclusion le_sup_right ⟨b, hb⟩ :=
      Subtype.ext (by simpa using hmab)
    have hb1 : mkQ (Subgroup.inclusion le_sup_right ⟨b, hb⟩) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hb
    have : mkQ m = mkQ (Subgroup.inclusion le_sup_left ⟨a, ha⟩) := by
      conv_lhs => rw [hm]
      rw [map_mul, hb1, mul_one]
    exact this.symm
  have hcycK₁ : ∀ P : Subgroup ↥K₁, IsPGroup p ↥P → IsCyclic ↥P := by
    intro P hP
    have hP' : IsPGroup p ↥(P.map e₁.toMonoidHom) := hP.of_equiv (Subgroup.equivMapOfInjective P e₁.toMonoidHom e₁.injective)
    have := hcycSL _ hP'
    exact isCyclic_of_surjective (Subgroup.equivMapOfInjective P e₁.toMonoidHom e₁.injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective P e₁.toMonoidHom e₁.injective).symm.surjective
  let f : ↥A →* ↥M ⧸ K₂.subgroupOf M := mkQ.comp (Subgroup.inclusion hA)
  have hrange : Nat.card ↥f.range ≤ p := by
    have hpr : IsPGroup p ↥f.range := by
      exact hAp.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hcyc : IsCyclic ↥f.range :=
      ng_isCyclic_pSubgroup_of_surjective hcycK₁ ψ hψ f.range hpr
    refine ng_card_le_of_cyclic_exp hp (fun x => ?_)
    obtain ⟨a, ha⟩ := f.rangeRestrict_surjective x
    rw [← ha, ← map_pow]
    have : (a ^ p : ↥A) = 1 := Subtype.ext (by simpa using hAexp a a.2)
    rw [this, map_one]
  have hker : Nat.card ↥f.ker ≤ p ^ n := by
    have hn0 : n ≠ 0 := by
      rintro rfl
      have h1q : 1 < Nat.card F₂ := Finite.one_lt_card
      rw [h₂] at h1q
      simp at h1q
    set B : Subgroup G := f.ker.map A.subtype with hB
    have hBK₂ : B ≤ K₂ := by
      rintro _ ⟨a, ha, rfl⟩
      have h1 : f a = 1 := ha
      change mkQ (Subgroup.inclusion hA a) = 1 at h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hBcard : Nat.card ↥B = Nat.card ↥f.ker := Subgroup.card_map_of_injective A.subtype_injective
    obtain ⟨k, hk⟩ := hAp.exists_card_eq
    have hdvdA : Nat.card ↥f.ker ∣ Nat.card ↥A := by
      have := Subgroup.card_ker_mul_card_range f
      exact Dvd.intro _ this
    rw [hk] at hdvdA
    obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1 hdvdA
    have hK₂card : Nat.card ↥K₂ = p ^ n * ((p ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr e₂.toEquiv,
        CFSG.BenderSuzuki.External.huppert614_card_specialLinearGroup, h₂]
    have hBK₂dvd : Nat.card ↥B ∣ Nat.card ↥K₂ := by
      have h1 : Nat.card ↥(B.subgroupOf K₂) = Nat.card ↥B :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK₂).toEquiv
      rw [← h1]
      exact Subgroup.card_subgroup_dvd_card _
    rw [hBcard, ha, hK₂card] at hBK₂dvd
    have hnd : ¬ p ∣ (p ^ n) ^ 2 - 1 := by
      intro hd
      have h1 : p ∣ (p ^ n) ^ 2 := dvd_pow (dvd_pow_self p hn0) (by norm_num)
      have h2' : p ∣ (p ^ n) ^ 2 - ((p ^ n) ^ 2 - 1) := Nat.dvd_sub h1 hd
      have hpos : 1 ≤ (p ^ n) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos _)
      rw [Nat.sub_sub_self hpos] at h2'
      exact hp.one_lt.ne' (Nat.dvd_one.1 h2')
    have hcop : Nat.Coprime (p ^ a) ((p ^ n) ^ 2 - 1) :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    have hdvd : p ^ a ∣ p ^ n := hcop.dvd_of_dvd_mul_right hBK₂dvd
    rw [ha]
    exact Nat.le_of_dvd (pow_pos hp.pos _) hdvd
  have := Subgroup.card_ker_mul_card_range f
  calc Nat.card ↥A = Nat.card ↥f.ker * Nat.card ↥f.range := this.symm
    _ ≤ p ^ n * p := Nat.mul_le_mul hker hrange
    _ = p ^ (n + 1) := by ring

end CFSG.GH74.GLS.Stage4.Rest
