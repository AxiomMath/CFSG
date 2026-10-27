module

public import CFSG.GH74.Generic.S45.PumpB2

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.Blueprint Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section Normal

theorem commute_of_commutator_eq_bot {X : Type*} [Group X] {K L : Subgroup X} (h : ⁅K, L⁆ = ⊥)
    {a b : X} (ha : a ∈ K) (hb : b ∈ L) : a * b = b * a :=
  ((Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h ha)) b hb).symm

theorem component_normal_of_gen4 {X : Type} [Group X] [Finite X] (hX : Gen4 X) {z : X}
    (hzc : ∀ g : X, g * z = z * g) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    {J W E : Subgroup X} (hJ : IsComponent J) (hWJ : W ≤ J) (hEW : E ≤ W)
    (hWs : IsSimpleGroup ↥W) (hWnab : ∃ a b : ↥W, a * b ≠ b * a)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEsq : ∀ a ∈ E, a * a = 1)
    (hE4 : 4 ≤ Nat.card ↥E) : J.Normal := by
  classical
  have hW1 : ∀ w ∈ W, (∀ u ∈ J, u * w = w * u) → w = 1 := by
    intro w hw hcomm
    have h1 : (⟨w, hw⟩ : ↥W) = 1 :=
      eq_one_of_central_of_simple hWs hWnab (fun u => Subtype.ext (hcomm u (hWJ u.2)))
    exact congrArg Subtype.val h1
  have key : ∀ g : X, J.map (MulAut.conj g).toMonoidHom = J := by
    intro g
    by_contra hne
    set J₂ : Subgroup X := J.map (MulAut.conj g).toMonoidHom with hJ₂
    have hJ₂c : IsComponent J₂ := LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJ
    have hcomm : ⁅J, J₂⁆ = ⊥ := by
      rcases LocalCores.distinct_components_commute hJ hJ₂c with h | h
      · exact absurd h.symm hne
      · exact h
    have hcomm' : ∀ a ∈ J, ∀ b ∈ J₂, a * b = b * a :=
      fun a ha b hb => commute_of_commutator_eq_bot hcomm ha hb
    set E₂ : Subgroup X := E.map (MulAut.conj g).toMonoidHom with hE₂
    have hEJ : E ≤ J := hEW.trans hWJ
    have hE₂J₂ : E₂ ≤ J₂ := Subgroup.map_mono hEJ
    have hE₂comm : ∀ a ∈ E₂, ∀ b ∈ E₂, a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      show g * a * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * a * g⁻¹)
      have h1 := hEcomm a ha b hb
      calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
        _ = g * (b * a) * g⁻¹ := by rw [h1]
        _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
    have hc : ∀ (m : ↥E) (n : ↥E₂), Commute (E.subtype m) (E₂.subtype n) :=
      fun m n => hcomm' m (hEJ m.2) n (hE₂J₂ n.2)
    let Ψ : ↥E × ↥E₂ →* X := MonoidHom.noncommCoprod E.subtype E₂.subtype hc
    have hΨ : ∀ p : ↥E × ↥E₂, Ψ p = (p.1 : X) * (p.2 : X) := fun p => rfl
    have hinj : Function.Injective Ψ := by
      rw [MonoidHom.noncommCoprod_injective]
      refine ⟨E.subtype_injective, E₂.subtype_injective, ?_⟩
      rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.disjoint_def]
      intro u hu1 hu2
      exact hW1 u (hEW hu1) (fun a ha => hcomm' a ha u (hE₂J₂ hu2))
    have hKcard : Nat.card ↥Ψ.range = Nat.card ↥E * Nat.card ↥E := by
      have e1 : Nat.card ↥Ψ.range = Nat.card (↥E × ↥E₂) :=
        (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      rw [e1, Nat.card_prod]
      congr 1
      exact Nat.card_congr (E.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv.symm
    have hKcomm : ∀ a b : ↥Ψ.range, a * b = b * a := by
      rintro ⟨_, ⟨p, rfl⟩⟩ ⟨_, ⟨q, rfl⟩⟩
      apply Subtype.ext
      show Ψ p * Ψ q = Ψ q * Ψ p
      rw [hΨ, hΨ]
      have c1 : Commute (p.1 : X) (q.1 : X) := hEcomm _ p.1.2 _ q.1.2
      have c2 : Commute (p.2 : X) (q.2 : X) := hE₂comm _ p.2.2 _ q.2.2
      exact ((c1.mul_right (hc p.1 q.2)).mul_left ((hc q.1 p.2).symm.mul_right c2))
    have hKsq : ∀ a : ↥Ψ.range, a ^ 2 = 1 := by
      rintro ⟨_, ⟨p, rfl⟩⟩
      apply Subtype.ext
      show (Ψ p) ^ 2 = 1
      have hcm : Commute (p.1 : X) (p.2 : X) := hc p.1 p.2
      rw [hΨ, hcm.mul_pow]
      have h1 : (p.1 : X) ^ 2 = 1 := by rw [pow_two]; exact hEsq _ p.1.2
      have h2 : (p.2 : X) ^ 2 = 1 := by
        obtain ⟨a, ha, haf⟩ := Subgroup.mem_map.1 p.2.2
        have : (p.2 : X) = g * a * g⁻¹ := haf.symm
        rw [this, pow_two]
        calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
          _ = 1 := by rw [hEsq a ha]; group
      rw [h1, h2, one_mul]
    have hnsl : ¬ SectionalTwoRankLE ↥Ψ.range 3 :=
      not_sectionalTwoRankLE_of_elementary 3 hKcomm hKsq (by rw [hKcard]; nlinarith [hE4])
    have hrc : RankCertified ↥Ψ.range 3 := rankCertified_iff.2 hnsl
    have hzK : z ∉ Ψ.range := by
      rintro ⟨p, hp⟩
      have hp' : (p.1 : X) * (p.2 : X) = z := hp
      have hfJ₂ : (p.2 : X) ∈ J₂ := hE₂J₂ p.2.2
      have he1 : (p.1 : X) = 1 := by
        apply hW1 _ (hEW p.1.2)
        intro u hu
        have hfinv : (p.2 : X)⁻¹ ∈ J₂ := inv_mem hfJ₂
        have h1 : (p.1 : X) = z * (p.2 : X)⁻¹ := by rw [← hp']; group
        calc u * (p.1 : X) = u * (z * (p.2 : X)⁻¹) := by rw [h1]
          _ = z * (u * (p.2 : X)⁻¹) := by rw [← mul_assoc, hzc u, mul_assoc]
          _ = z * ((p.2 : X)⁻¹ * u) := by rw [hcomm' u hu _ hfinv]
          _ = (z * (p.2 : X)⁻¹) * u := by rw [mul_assoc]
          _ = (p.1 : X) * u := by rw [h1]
      have hfz : (p.2 : X) = z := by rw [he1, one_mul] at hp'; exact hp'
      obtain ⟨a, ha, haf⟩ := Subgroup.mem_map.1 p.2.2
      have h1 : g * a * g⁻¹ = z := by rw [← hfz]; exact haf
      have haz : a = z := by
        calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
          _ = g⁻¹ * z * g := by rw [h1]
          _ = z * g⁻¹ * g := by rw [hzc g⁻¹]
          _ = z := by group
      have hzE : z ∈ E := haz ▸ ha
      exact hz1 (hW1 z (hEW hzE) (fun u _ => hzc u))
    exact not_rankCertified_three_of_gen4 hX hzc hz2 hzK hrc
  exact ⟨fun n hn g => by
    have : g * n * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom := ⟨n, hn, rfl⟩
    rwa [key g] at this⟩

end Normal

section Tail

theorem false_of_elementary_sixteen {X : Type} [Group X] [Finite X] (hX : Gen4 X) {z : X}
    (hzc : ∀ g : X, g * z = z * g) (hz2 : z * z = 1) {A : Subgroup X}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hsq : ∀ a ∈ A, a * a = 1)
    (hcard : 16 ≤ Nat.card ↥A) (hzA : z ∉ A) : False := by
  have hnsl : ¬ SectionalTwoRankLE ↥A 3 :=
    not_sectionalTwoRankLE_of_elementary 3 (fun a b => Subtype.ext (hcomm a a.2 b b.2))
      (fun a => by
        apply Subtype.ext
        show (a : X) ^ 2 = 1
        rw [pow_two]
        exact hsq a a.2) (by omega)
  exact not_rankCertified_three_of_gen4 hX hzc hz2 hzA (rankCertified_iff.2 hnsl)

end Tail

end CFSG.GH74.Generic.S45
