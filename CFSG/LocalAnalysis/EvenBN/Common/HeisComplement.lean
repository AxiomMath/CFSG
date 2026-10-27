module

public import CFSG.LocalAnalysis.EvenBN.Common.HeisLikeSL3
public import CFSG.LocalAnalysis.EvenBN.Common.TwoElementary

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup CFSG.Blueprint
open CFSG.LocalAnalysis.ComponentInitial.LinearCover (HeisenbergRoots)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)

theorem sup_eq_of_inf_eq_bot_of_card_le {G : Type*} [Group G] [Finite G] {E C S : Subgroup G}
    (hES : E ≤ S) (hCS : C ≤ S) (hinf : E ⊓ C = ⊥)
    (hcard : Nat.card S ≤ Nat.card E * Nat.card C) : E ⊔ C = S := by
  refine Subgroup.eq_of_le_of_card_ge (sup_le hES hCS) (hcard.trans ?_)
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p : E × C => (⟨(p.1 : G) * p.2,
    mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2)⟩ : (E ⊔ C : Subgroup G))) ?_
  rintro ⟨e, c⟩ ⟨e', c'⟩ h
  obtain ⟨h1, h2⟩ := eq_and_eq_of_mul_eq_mul hinf e.2 e'.2 c.2 c'.2 (congrArg Subtype.val h)
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

section Roots

variable {G : Type*} [Group G] {K : Type*} [Field K] (R : HeisenbergRoots K G)

theorem heisRoots_coords_injective [Finite K] (hcard : Nat.card R.S = Nat.card K ^ 3)
    {a b c a' b' c' : K} (h : R.w c * R.x a * R.y b = R.w c' * R.x a' * R.y b') :
    a = a' ∧ b = b' ∧ c = c' := by
  classical
  let μ : K × K × K → R.S := fun p => ⟨R.w p.2.2 * R.x p.1 * R.y p.2.1,
    mul_mem (mul_mem (R.w_mem _) (R.x_mem _)) (R.y_mem _)⟩
  have hμ : Function.Surjective μ := by
    intro s
    obtain ⟨a, b, c, hs⟩ := R.mem_S s s.2
    exact ⟨(a, b, c), Subtype.ext hs.symm⟩
  have hbij := hμ.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_prod, Nat.card_prod]
    ring_nf
    exact le_rfl)
  have h2 : ((a, b, c) : K × K × K) = (a', b', c') := hbij.1 (Subtype.ext h)
  simp only [Prod.mk.injEq] at h2
  exact h2

theorem heisRoots_w_injective [Finite K] (hcard : Nat.card R.S = Nat.card K ^ 3) :
    Function.Injective R.w := fun c c' h =>
  (heisRoots_coords_injective R hcard (a := 0) (b := 0) (a' := 0) (b' := 0) (by rw [h])).2.2

theorem heisRoots_mul_self (hK2 : ∀ a : K, a + a = 0) (a b c : K) :
    R.w c * R.x a * R.y b * (R.w c * R.x a * R.y b) = R.w (a * b) := by
  rw [TrialityD4.heis_mul_D4 hK2 R.x_add R.y_add R.w_add R.w_mul_x R.w_mul_y R.x_mul_y, hK2 a,
    hK2 b, hK2 c, zero_add, R.x_zero, R.y_zero, mul_one, mul_one]

theorem heisRoots_exists_inf_eq_bot [Finite K] [CharP K 2] (hcard : Nat.card R.S = Nat.card K ^ 3)
    {E : Subgroup G} (hEe : ∀ e ∈ E, e * e = 1) (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) :
    ∃ C : Subgroup G, C ≤ R.S ∧ E ⊓ C = ⊥ ∧ Nat.card C = Nat.card K := by
  have hK2 : ∀ a : K, a + a = 0 := CharTwo.add_self_eq_zero
  have hwinj := heisRoots_w_injective R hcard
  have hsq : ∀ {a b c : K}, R.w c * R.x a * R.y b ∈ E → a * b = 0 := fun {a b c} he => by
    have h1 := hEe _ he
    rw [heisRoots_mul_self R hK2] at h1
    exact hwinj (h1.trans R.w_zero.symm)
  have hcomm : ∀ {a b c a' b' c' : K}, R.w c * R.x a * R.y b ∈ E →
      R.w c' * R.x a' * R.y b' ∈ E → a' * b = a * b' := fun {a b c a' b' c'} he he' =>
    (TrialityD4.heis_commute_iff_D4 hK2 R.x_add R.y_add R.w_add R.w_mul_x R.w_mul_y R.x_mul_y
      hwinj a b c a' b' c').1 (hEc _ he _ he')
  by_cases hb : ∀ a b c : K, R.w c * R.x a * R.y b ∈ E → b = 0
  · have hyinj : Function.Injective R.y := fun b b' h =>
      (heisRoots_coords_injective R hcard (a := 0) (c := 0) (a' := 0) (c' := 0)
        (by rw [h])).2.1
    refine ⟨{ carrier := Set.range R.y
              mul_mem' := by
                rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
                exact ⟨b + b', R.y_add b b'⟩
              one_mem' := ⟨0, R.y_zero⟩
              inv_mem' := by
                rintro _ ⟨b, rfl⟩
                exact ⟨b, by rw [eq_inv_iff_mul_eq_one, ← R.y_add, hK2, R.y_zero]⟩ },
      ?_, ?_, Nat.card_range_of_injective hyinj⟩
    · rintro _ ⟨b, rfl⟩
      exact R.y_mem b
    · rw [eq_bot_iff]
      rintro _ ⟨hgE, b, rfl⟩
      have hb0 := hb 0 b 0 (by rwa [R.w_zero, R.x_zero, one_mul, one_mul])
      rw [hb0, R.y_zero]
      exact one_mem _
  · push Not at hb
    obtain ⟨a₀, b₀, c₀, he₀, hb₀⟩ := hb
    have ha₀ : a₀ = 0 := (mul_eq_zero.1 (hsq he₀)).resolve_right hb₀
    have ha : ∀ a b c : K, R.w c * R.x a * R.y b ∈ E → a = 0 := fun a b c he => by
      have h := hcomm he he₀
      rw [ha₀, zero_mul] at h
      exact (mul_eq_zero.1 h.symm).resolve_right hb₀
    have hxinj : Function.Injective R.x := fun a a' h =>
      (heisRoots_coords_injective R hcard (b := 0) (c := 0) (b' := 0) (c' := 0)
        (by rw [h])).1
    refine ⟨{ carrier := Set.range R.x
              mul_mem' := by
                rintro _ _ ⟨a, rfl⟩ ⟨a', rfl⟩
                exact ⟨a + a', R.x_add a a'⟩
              one_mem' := ⟨0, R.x_zero⟩
              inv_mem' := by
                rintro _ ⟨a, rfl⟩
                exact ⟨a, by rw [eq_inv_iff_mul_eq_one, ← R.x_add, hK2, R.x_zero]⟩ },
      ?_, ?_, Nat.card_range_of_injective hxinj⟩
    · rintro _ ⟨a, rfl⟩
      exact R.x_mem a
    · rw [eq_bot_iff]
      rintro _ ⟨hgE, a, rfl⟩
      have ha0 := ha a 0 0 (by rwa [R.w_zero, R.y_zero, one_mul, mul_one])
      rw [ha0, R.x_zero]
      exact one_mem _

end Roots

theorem exists_heisRoots_of_isSylowOf_lieModel {Y : Type} [Group Y] [Finite Y] {Kc : Subgroup Y}
    {g : ℕ} (hg : 1 ≤ g) (hKc : LieModel Kc .PSL 3 2 g) {V : Subgroup Y}
    (hV : IsSylowOf 2 V Kc) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (R : HeisenbergRoots F Y),
      R.S = V ∧ Nat.card F = 2 ^ g ∧ Nat.card R.S = Nat.card F ^ 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, hFf, hFfin, hF, ⟨ψ⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hKc
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hF
  obtain ⟨U, hU⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.exists_sylow_projUnitriangular
    (K := F) 2 (n := 3) (by norm_num)
  obtain ⟨S, hS⟩ := hV.exists_sylow_eq_subgroupOf
  set S' : Sylow 2 (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    S.mapSurjective (f := ψ.toMonoidHom) ψ.surjective with hS'
  obtain ⟨x, hx⟩ : ∃ x : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F,
      x • U = S' := MulAction.exists_smul_eq _ U S'
  set ι : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F →* Y :=
    Kc.subtype.comp (ψ.symm.toMonoidHom.comp (MulAut.conj x).toMonoidHom) with hι
  have hιinj : Function.Injective ι :=
    Kc.subtype_injective.comp (ψ.symm.injective.comp (MulAut.conj x).injective)
  have hιU : (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projUnitriangular 3 F).map ι = V := by
    have e1 : (U : Subgroup _).map (MulAut.conj x).toMonoidHom = (S' : Subgroup _) := by
      rw [← hx]
      rfl
    have e2 : ((S : Subgroup Kc).map ψ.toMonoidHom).map ψ.symm.toMonoidHom =
        (S : Subgroup Kc) := by
      rw [map_map]
      convert Subgroup.map_id (S : Subgroup Kc)
      ext y
      simp
    rw [← hU, hι, ← map_map, ← map_map, e1]
    rw [show (S' : Subgroup _) = (S : Subgroup Kc).map ψ.toMonoidHom from rfl, e2, hS,
      subgroupOf_map_subtype, inf_eq_left.2 hV.le]
  set R₀ := CFSG.LocalAnalysis.ComponentInitial.LinearCover.projRoots (K := F) with hR₀
  refine ⟨F, hFf, hFfin, hchar,
    { x := fun a => ι (R₀.x a)
      y := fun b => ι (R₀.y b)
      w := fun c => ι (R₀.w c)
      x_add := fun a b => by rw [R₀.x_add, map_mul]
      y_add := fun a b => by rw [R₀.y_add, map_mul]
      w_add := fun a b => by rw [R₀.w_add, map_mul]
      w_mul_x := fun c a => by rw [← map_mul, R₀.w_mul_x, map_mul]
      w_mul_y := fun c b => by rw [← map_mul, R₀.w_mul_y, map_mul]
      x_mul_y := fun a b => by rw [← map_mul, R₀.x_mul_y, map_mul, map_mul]
      gx := ι R₀.gx
      gy := ι R₀.gy
      gx_conj := fun a => by rw [← map_inv, ← map_mul, ← map_mul, R₀.gx_conj]
      gy_conj := fun b => by rw [← map_inv, ← map_mul, ← map_mul, R₀.gy_conj]
      S := V
      x_mem := fun a => by
        rw [← hιU]
        exact ⟨R₀.x a, R₀.x_mem a, rfl⟩
      y_mem := fun b => by
        rw [← hιU]
        exact ⟨R₀.y b, R₀.y_mem b, rfl⟩
      w_mem := fun c => by
        rw [← hιU]
        exact ⟨R₀.w c, R₀.w_mem c, rfl⟩
      mem_S := fun s hs => by
        rw [← hιU] at hs
        obtain ⟨u, hu, rfl⟩ := hs
        obtain ⟨a, b, c, rfl⟩ := R₀.mem_S u hu
        exact ⟨a, b, c, by rw [map_mul, map_mul]⟩ }, rfl, hF, ?_⟩
  show Nat.card V = Nat.card F ^ 3
  rw [← hιU, Subgroup.card_map_of_injective hιinj,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_projUnitriangular]

theorem exists_inf_eq_bot_of_isSylowOf_lieModel {Y : Type} [Group Y] [Finite Y]
    {Kc : Subgroup Y} {g : ℕ} (hg : 1 ≤ g) (hKc : LieModel Kc .PSL 3 2 g) {V : Subgroup Y}
    (hV : IsSylowOf 2 V Kc) {E : Subgroup Y} (hEe : ∀ e ∈ E, e * e = 1)
    (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) :
    ∃ C : Subgroup Y, C ≤ V ∧ E ⊓ C = ⊥ ∧ Nat.card C = 2 ^ g := by
  obtain ⟨F, _, _, _, R, hRV, hF, hcard⟩ := exists_heisRoots_of_isSylowOf_lieModel hg hKc hV
  obtain ⟨C, hCS, hinf, hC⟩ := heisRoots_exists_inf_eq_bot R hcard hEe hEc
  exact ⟨C, hRV ▸ hCS, hinf, hC.trans hF⟩

theorem exists_complement_of_isSylowOf_sup {W : Type} [Group W] [Finite W] {Kc Kc' : Subgroup W}
    {g : ℕ} (hg : 1 ≤ g)
    (hcase : (Kc' = Kc ∧ LieModel Kc .PSL 3 2 (2 * g)) ∨
      ((∀ x ∈ Kc, ∀ y ∈ Kc', x * y = y * x) ∧ Kc ⊓ Kc' = ⊥ ∧ LieModel Kc .PSL 3 2 g ∧
        LieModel Kc' .PSL 3 2 g))
    {V : Subgroup W} (hV : IsSylowOf 2 V (Kc ⊔ Kc')) {E : Subgroup W} (hEV : E ≤ V)
    (hEe : ∀ e ∈ E, e * e = 1) (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e)
    (hEcard : Nat.card E = 2 ^ (4 * g)) :
    ∃ C : Subgroup W, C ≤ V ∧ E ⊓ C = ⊥ ∧ Nat.card E * Nat.card C = Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hcase with ⟨rfl, hlie⟩ | ⟨hKcc, hKcinf, hlie, hlie'⟩
  · rw [sup_idem] at hV
    obtain ⟨F, _, _, _, R, hRV, hF, hcard⟩ :=
      exists_heisRoots_of_isSylowOf_lieModel (by omega) hlie hV
    obtain ⟨C, hCS, hinf, hC⟩ := heisRoots_exists_inf_eq_bot R hcard hEe hEc
    refine ⟨C, hRV ▸ hCS, hinf, ?_⟩
    rw [← hRV, hcard, hEcard, hC, hF, ← pow_mul, ← pow_add]
    congr 1
    ring
  · have hNKc : Kc ⊔ Kc' ≤ normalizer (Kc : Set W) :=
      sup_le le_normalizer (fun y hy => mem_normalizer_fintype fun x hx => by
        rw [← hKcc x hx y hy, mul_inv_cancel_right]
        exact hx)
    have hNKc' : Kc ⊔ Kc' ≤ normalizer (Kc' : Set W) :=
      sup_le (fun y hy => mem_normalizer_fintype fun x hx => by
        rw [hKcc y hy x hx, mul_inv_cancel_right]
        exact hx) le_normalizer
    set A := V ⊓ Kc with hA
    set B := V ⊓ Kc' with hB
    have hAsyl : IsSylowOf 2 A Kc := hV.inf_of_le_normalizer le_sup_left hNKc
    have hBsyl : IsSylowOf 2 B Kc' := hV.inf_of_le_normalizer le_sup_right hNKc'
    have hAB : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
      hKcc x (Subgroup.mem_inf.1 hx).2 y (Subgroup.mem_inf.1 hy).2
    have hinfAB : A ⊓ B = ⊥ :=
      le_bot_iff.1 (hKcinf ▸ inf_le_inf inf_le_right inf_le_right)
    have hVAB : V = A ⊔ B := by
      symm
      refine eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
      have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB).1
      rw [hinfAB, card_bot, mul_one] at h1
      have h2 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute Kc Kc' hKcc).1
      rw [hKcinf, card_bot, mul_one] at h2
      rw [h1, hV.card_eq, hAsyl.card_eq, hBsyl.card_eq, h2,
        Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add]
    have hBN : V ≤ normalizer (B : Set W) := by
      rw [hVAB]
      exact sup_le (fun a ha => mem_normalizer_fintype fun b hb => by
        rw [hAB a ha b hb, mul_inv_cancel_right]
        exact hb) le_normalizer
    have hAN : V ≤ normalizer (A : Set W) := by
      rw [hVAB]
      exact sup_le le_normalizer (fun b hb => mem_normalizer_fintype fun a ha => by
        rw [← hAB a ha b hb, mul_inv_cancel_right]
        exact ha)
    have hBA : ∀ x ∈ B, ∀ y ∈ A, x * y = y * x := fun x hx y hy => (hAB y hy x hx).symm
    have hinfBA : B ⊓ A = ⊥ := by rw [inf_comm, hinfAB]
    have hproj : ∀ {P Q : Subgroup W}, (∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) → P ⊓ Q = ⊥ →
        E ≤ normalizer (Q : Set W) →
        (∀ s ∈ P ⊓ (E ⊔ Q), s * s = 1) ∧
          ∀ s ∈ P ⊓ (E ⊔ Q), ∀ s' ∈ P ⊓ (E ⊔ Q), s * s' = s' * s := by
      intro P Q hPQ hinfPQ hEQ
      have hdec : ∀ s ∈ P ⊓ (E ⊔ Q), ∃ q ∈ Q, s * q⁻¹ ∈ E := fun s hs => by
        obtain ⟨e, he, q, hq, hsq⟩ :=
          exists_mul_of_le_normalizer' hEQ s (Subgroup.mem_inf.1 hs).2
        exact ⟨q, hq, by rw [hsq, mul_inv_cancel_right]; exact he⟩
      refine ⟨fun s hs => ?_, fun s hs s' hs' => ?_⟩
      · obtain ⟨q, hq, he⟩ := hdec s hs
        have hsP := (Subgroup.mem_inf.1 hs).1
        have hsq : s * q = q * s := hPQ s hsP q hq
        have h1 := hEe _ he
        have hqs : q⁻¹ * s * q = s := by
          rw [mul_assoc, hsq, ← mul_assoc, inv_mul_cancel, one_mul]
        have e1 : s * s = q * q := by
          calc s * s = s * (q⁻¹ * s * q) := by rw [hqs]
            _ = (s * q⁻¹) * (s * q⁻¹) * (q * q) := by group
            _ = q * q := by rw [h1, one_mul]
        have h2 : s * s ∈ P ⊓ Q := Subgroup.mem_inf.2 ⟨mul_mem hsP hsP, e1 ▸ mul_mem hq hq⟩
        rw [hinfPQ, mem_bot] at h2
        exact h2
      · obtain ⟨q, hq, he⟩ := hdec s hs
        obtain ⟨q', hq', he'⟩ := hdec s' hs'
        have hsP := (Subgroup.mem_inf.1 hs).1
        have hsP' := (Subgroup.mem_inf.1 hs').1
        have hc := hEc _ he _ he'
        have e1 : s * q⁻¹ * (s' * q'⁻¹) = s * s' * (q⁻¹ * q'⁻¹) := by
          rw [show s * q⁻¹ * (s' * q'⁻¹) = s * (q⁻¹ * s') * q'⁻¹ by group,
            ← hPQ s' hsP' q⁻¹ (inv_mem hq)]
          group
        have e2 : s' * q'⁻¹ * (s * q⁻¹) = s' * s * (q'⁻¹ * q⁻¹) := by
          rw [show s' * q'⁻¹ * (s * q⁻¹) = s' * (q'⁻¹ * s) * q⁻¹ by group,
            ← hPQ s hsP q'⁻¹ (inv_mem hq')]
          group
        rw [e1, e2] at hc
        exact (eq_and_eq_of_mul_eq_mul hinfPQ (mul_mem hsP hsP') (mul_mem hsP' hsP)
          (mul_mem (inv_mem hq) (inv_mem hq')) (mul_mem (inv_mem hq') (inv_mem hq)) hc).1
    obtain ⟨hE₁e, hE₁c⟩ := hproj hAB hinfAB (hEV.trans hBN)
    obtain ⟨hE₂e, hE₂c⟩ := hproj hBA hinfBA (hEV.trans hAN)
    obtain ⟨C₁, hC₁A, hinf₁, hC₁⟩ :=
      exists_inf_eq_bot_of_isSylowOf_lieModel hg hlie hAsyl hE₁e hE₁c
    obtain ⟨C₂, hC₂B, hinf₂, hC₂⟩ :=
      exists_inf_eq_bot_of_isSylowOf_lieModel hg hlie' hBsyl hE₂e hE₂c
    have hC₁₂ : ∀ x ∈ C₁, ∀ y ∈ C₂, x * y = y * x := fun x hx y hy => hAB x (hC₁A hx) y (hC₂B hy)
    have hCinf : C₁ ⊓ C₂ = ⊥ := le_bot_iff.1 (hinfAB ▸ inf_le_inf hC₁A hC₂B)
    refine ⟨C₁ ⊔ C₂, sup_le (hC₁A.trans inf_le_left) (hC₂B.trans inf_le_left), ?_, ?_⟩
    · rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzE, hzC⟩ := Subgroup.mem_inf.1 hz
      obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := exists_mul_of_le_normalizer'
        (fun x hx => mem_normalizer_fintype fun y hy => by
          rw [hC₁₂ x hx y hy, mul_inv_cancel_right]
          exact hy) _ hzC
      have h1 : c₁ ∈ A ⊓ (E ⊔ B) := Subgroup.mem_inf.2 ⟨hC₁A hc₁, by
        rw [show c₁ = c₁ * c₂ * c₂⁻¹ by group]
        exact mul_mem (mem_sup_left hzE) (mem_sup_right (inv_mem (hC₂B hc₂)))⟩
      have hc₁1 : c₁ = 1 := by
        have := Subgroup.mem_inf.2 ⟨h1, hc₁⟩
        rwa [hinf₁, mem_bot] at this
      subst hc₁1
      rw [one_mul] at hzE ⊢
      have h2 : c₂ ∈ B ⊓ (E ⊔ A) := Subgroup.mem_inf.2 ⟨hC₂B hc₂, mem_sup_left hzE⟩
      have := Subgroup.mem_inf.2 ⟨h2, hc₂⟩
      rwa [hinf₂] at this
    · have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C₁ C₂ hC₁₂).1
      rw [hCinf, card_bot, mul_one, hC₁, hC₂] at h1
      have h2 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB).1
      rw [hinfAB, card_bot, mul_one, (heisLike_of_isSylowOf_of_lieModel hg hlie hAsyl).card_eq,
        (heisLike_of_isSylowOf_of_lieModel hg hlie' hBsyl).card_eq, ← hVAB] at h2
      rw [h1, h2, hEcard]
      ring

theorem exists_complement_of_isSylowOf_of_map_eq {Y : Type} [Group Y] [Finite Y]
    {B V : Subgroup Y} {Kc Kc' : Subgroup (Y ⧸ CFSG.oddCore Y)}
    (hB : B.map (QuotientGroup.mk' (CFSG.oddCore Y)) = Kc ⊔ Kc') {g : ℕ} (hg : 1 ≤ g)
    (hcase : (Kc' = Kc ∧ LieModel Kc .PSL 3 2 (2 * g)) ∨
      ((∀ x ∈ Kc, ∀ y ∈ Kc', x * y = y * x) ∧ Kc ⊓ Kc' = ⊥ ∧ LieModel Kc .PSL 3 2 g ∧
        LieModel Kc' .PSL 3 2 g))
    (hV : IsSylowOf 2 V B) {E : Subgroup Y} (hEV : E ≤ V) (hEe : ∀ e ∈ E, e * e = 1)
    (hEc : ∀ e ∈ E, ∀ e' ∈ E, e * e' = e' * e) (hEcard : Nat.card E = 2 ^ (4 * g)) :
    ∃ C : Subgroup Y, C ≤ V ∧ E ⊓ C = ⊥ ∧ Nat.card E * Nat.card C = Nat.card V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.oddCore Y with hO
  set π := QuotientGroup.mk' O with hπ
  have hinj : ∀ x ∈ V, π x = 1 → x = 1 := by
    intro x hx hπx
    have hxO : x ∈ O := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hπx
      exact hπx
    obtain ⟨k, hk⟩ := hV.isPGroup ⟨x, hx⟩
    exact TrialityD4.eq_one_of_mem_oddCore_of_pow_D4 hxO (k := k) (by
      have := congrArg Subtype.val hk
      simpa using this)
  have hVsyl : IsSylowOf 2 (V.map π) (Kc ⊔ Kc') := by
    refine isSylowOf_of_card (hB ▸ map_mono hV.le) ?_
    rw [TrialityD4.card_map_of_injOn_D4 π hinj le_rfl, hV.card_eq]
    have hk := Subgroup.card_ker_mul_card_range (π.domRestrict B)
    rw [MonoidHom.domRestrict_range, hB, MonoidHom.ker_domRestrict, hπ,
      QuotientGroup.ker_mk'] at hk
    have hodd : Odd (Nat.card (O.subgroupOf B)) := by
      have e : Nat.card (O.subgroupOf B) = Nat.card (O ⊓ B : Subgroup Y) := by
        rw [← subgroupOf_map_subtype, card_map_of_injective B.subtype_injective]
      rw [e]
      exact Odd.of_dvd_nat (CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.odd_card_oddCore Y)
        (card_dvd_of_le inf_le_left)
    rw [← hk, TrialityD4.factorization_two_mul_of_odd_D4 hodd Nat.card_pos.ne']
  have hEcard' : Nat.card (E.map π) = Nat.card E := TrialityD4.card_map_of_injOn_D4 π hinj hEV
  obtain ⟨C', hC'V, hinf', hcard'⟩ := exists_complement_of_isSylowOf_sup hg hcase hVsyl
    (map_mono hEV)
    (by
      rintro _ ⟨e, he, rfl⟩
      rw [← map_mul, hEe e he, map_one])
    (by
      rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
      rw [← map_mul, ← map_mul, hEc e he e' he'])
    (hEcard'.trans hEcard)
  refine ⟨V ⊓ C'.comap π, inf_le_left, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzE, hzVC⟩ := Subgroup.mem_inf.1 hz
    obtain ⟨hzV, hzC⟩ := Subgroup.mem_inf.1 hzVC
    have h1 : π z ∈ E.map π ⊓ C' := Subgroup.mem_inf.2 ⟨⟨z, hzE, rfl⟩, hzC⟩
    rw [hinf', mem_bot] at h1
    exact (mem_bot).2 (hinj z hzV h1)
  · have e : (V ⊓ C'.comap π).map π = C' := by
      refine le_antisymm (map_le_iff_le_comap.2 inf_le_right) fun c hc => ?_
      obtain ⟨v, hv, rfl⟩ := hC'V hc
      exact ⟨v, Subgroup.mem_inf.2 ⟨hv, hc⟩, rfl⟩
    rw [← TrialityD4.card_map_of_injOn_D4 π hinj (inf_le_left : V ⊓ C'.comap π ≤ V), e,
      ← hEcard', hcard', TrialityD4.card_map_of_injOn_D4 π hinj le_rfl]

end CFSG.LocalAnalysis.EvenBN.Common
