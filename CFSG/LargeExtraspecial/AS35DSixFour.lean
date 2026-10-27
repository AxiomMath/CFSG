module

public import CFSG.LargeExtraspecial.AS35DFourEight

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Asc77

namespace Asc77

variable {G : Type} [Group G]

theorem conj_mem_closure_conjIn {z : G} {H : Subgroup G} {h : G} (hh : h ∈ H) {x : G}
    (hx : x ∈ closure (conjIn z H)) : h * x * h⁻¹ ∈ closure (conjIn z H) := by
  induction hx using closure_induction with
  | mem x hx => exact subset_closure (conj_mem_conjIn_of_mem hh hx)
  | one => rw [mul_one, mul_inv_cancel]; exact one_mem _
  | mul x y _ _ ihx ihy =>
    rw [show h * (x * y) * h⁻¹ = (h * x * h⁻¹) * (h * y * h⁻¹) by group]
    exact mul_mem ihx ihy
  | inv x _ ihx =>
    rw [show h * x⁻¹ * h⁻¹ = (h * x * h⁻¹)⁻¹ by group]
    exact inv_mem ihx

end Asc77

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem sixFour (h22 : S14.AschbacherTwoTwoStmt)
    (hW : ∀ g : G, g * S.z * g⁻¹ ∈ S.QG → g * S.z * g⁻¹ = S.z) {H : Subgroup G}
    (hH : S.IsHStar H) {g : G} (hgH : g ∈ H) (hgM : g ∉ S.M) :
    S.IsAFive H ∧ H = S.QG ⊔ S.Qa g ∧ ¬ IsConj S.z (S.z * (g * S.z * g⁻¹)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t := g * S.z * g⁻¹ with ht
  have htΩ : t ∈ S.zConj H := conj_mem_conjIn hgH
  have htz : t ≠ S.z := by
    intro h
    apply hgM
    rw [S.mem_M_iff]
    calc g * S.z = g * S.z * g⁻¹ * g := by group
      _ = S.z * g := by rw [← ht, h]
  have hA : S.IsAFive H := by
    rcases S.fourEight h22 hH with ⟨-, -, hle⟩ | hA
    · exact absurd (hW g (hle (subset_closure htΩ))) htz
    · exact hA
  obtain ⟨⟨hQH, -, -⟩, hmin⟩ := hH
  refine ⟨hA, ?_, ?_⟩
  ·
    obtain ⟨⟨_, _, -, -, hV, -, -⟩, hC⟩ := hA
    have hQaH : S.Qa g ≤ H := by
      rw [S.Qa_eq_map]
      rintro _ ⟨q, hq, rfl⟩
      exact H.mul_mem (H.mul_mem hgH (hQH hq)) (H.inv_mem hgH)
    have hle : S.QG ⊔ S.Qa g ≤ H := sup_le hQH hQaH
    have hV2 : IsPGroup 2 (closure (S.zConj H)) := by
      rw [hC, card_bot, mul_one] at hV
      exact IsPGroup.of_card (n := 4) (by rw [hV]; norm_num)
    have hset : S.IsHSet (S.QG ⊔ S.Qa g) := by
      refine ⟨le_sup_left, pCore_ne_bot_of (X := closure (S.zConj H) ⊓ (S.QG ⊔ S.Qa g))
        inf_le_right (fun h hh x hx => mem_inf.mpr ⟨conj_mem_closure_conjIn (hle hh)
          (mem_inf.mp hx).1, mul_mem (mul_mem hh (mem_inf.mp hx).2) (inv_mem hh)⟩)
        (hV2.to_le inf_le_left) ?_, ?_⟩
      · intro h0
        have : S.z ∈ closure (S.zConj H) ⊓ (S.QG ⊔ S.Qa g) :=
          mem_inf.mpr ⟨subset_closure (self_mem_conjIn _ _), le_sup_left (a := S.QG) S.z_mem_QG⟩
        rw [h0, mem_bot] at this
        exact S.z_ne_one this
      · intro hM
        apply hgM
        have hc : ∀ q ∈ S.QG, q * (g⁻¹ * S.z * g) = (g⁻¹ * S.z * g) * q := by
          intro q hq
          have h1 : g * q * g⁻¹ ∈ S.M := hM (le_sup_right (a := S.QG) (by
            rw [S.Qa_eq_map]
            exact ⟨q, hq, rfl⟩))
          have h2 := S.mem_M_iff.mp h1
          calc q * (g⁻¹ * S.z * g) = g⁻¹ * ((g * q * g⁻¹) * S.z) * g := by group
            _ = g⁻¹ * (S.z * (g * q * g⁻¹)) * g := by rw [h2]
            _ = (g⁻¹ * S.z * g) * q := by group
        have h1 : g⁻¹ * S.z * g ≠ 1 := by
          intro h
          apply S.z_ne_one
          calc S.z = g * (g⁻¹ * S.z * g) * g⁻¹ := by group
            _ = 1 := by rw [h]; group
        have h3 := S.eq_z_of_commute_QG hc h1
        rw [S.mem_M_iff]
        calc g * S.z = g * (g⁻¹ * S.z * g) := by rw [h3]
          _ = S.z * g := by group
    exact (hmin _ hset hle).symm
  ·
    obtain ⟨⟨_, _, hcard, hcomm, -, -, hsurj⟩, -⟩ := hA
    set Ω := S.zConj H with hΩ
    have hzΩ : S.z ∈ Ω := self_mem_conjIn _ _
    have hconjΩ : ∀ x ∈ Ω, x * x = 1 := by
      rintro _ ⟨h, -, rfl⟩
      rw [show h * S.z * h⁻¹ * (h * S.z * h⁻¹) = h * (S.z * S.z) * h⁻¹ by group, S.z_mul_z]
      group
    have hne1 : ∀ x ∈ Ω, x ≠ 1 := by
      rintro _ ⟨h, -, rfl⟩ h1
      apply S.z_ne_one
      calc S.z = h⁻¹ * (h * S.z * h⁻¹) * h := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨q, hq, hqt⟩ : ∃ q ∈ S.QG, q * t * q⁻¹ ≠ t := by
      by_contra! hall
      refine htz (S.eq_z_of_commute_QG (fun q hq => ?_) (hne1 t htΩ))
      calc q * t = q * t * q⁻¹ * q := by group
        _ = t * q := by rw [hall q hq]
    set t' := q * t * q⁻¹ with ht'
    have ht'Ω : t' ∈ Ω := conj_mem_conjIn_of_mem (hQH hq) htΩ
    have ht'z : t' ≠ S.z := by
      intro h
      apply htz
      have hqz : q⁻¹ * S.z * q = S.z := by
        rw [mul_assoc, ← S.z_comm_QG hq]
        group
      calc t = q⁻¹ * t' * q := by rw [ht']; group
        _ = S.z := by rw [h, hqz]
    have htM : t ∈ S.M := S.mem_M_iff.mpr (hcomm t htΩ S.z hzΩ)
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (hconjΩ t htΩ)
    have hxQ : t * t' ∈ S.QG := by
      rw [ht', show t * (q * t * q⁻¹) = (t * q * t⁻¹) * q⁻¹ by rw [htinv]; group]
      exact S.QG.mul_mem (S.conj_mem_QG htM hq) (S.QG.inv_mem hq)
    have hsub : ({S.z, t, t'} : Set G) ⊆ Ω := by
      rintro x (rfl | rfl | rfl)
      · exact hzΩ
      · exact htΩ
      · exact ht'Ω
    have h3 : ({S.z, t, t'} : Set G).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨htz.symm, ht'z.symm⟩), Set.ncard_pair hqt.symm]
    have hdiff : (Ω \ {S.z, t, t'}).ncard = 2 := by
      rw [Set.ncard_sdiff hsub, hcard, h3]
    obtain ⟨a, b, hab, hdab⟩ := Set.ncard_eq_two.mp hdiff
    have haΩ : a ∈ Ω \ {S.z, t, t'} := by rw [hdab]; exact Or.inl rfl
    have hbΩ : b ∈ Ω \ {S.z, t, t'} := by rw [hdab]; exact Or.inr rfl
    simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at haΩ hbΩ
    obtain ⟨haΩ, haz, hat, hat'⟩ := haΩ
    obtain ⟨hbΩ, hbz, hbt, hbt'⟩ := hbΩ
    set Z : Ω := ⟨S.z, hzΩ⟩
    set T : Ω := ⟨t, htΩ⟩
    set T' : Ω := ⟨t', ht'Ω⟩
    set A : Ω := ⟨a, haΩ⟩
    set B : Ω := ⟨b, hbΩ⟩
    have hne : ∀ {x y : Ω}, (x : G) ≠ y → x ≠ y := fun h h' => h (congrArg Subtype.val h')
    have hTA : T ≠ A := hne (Ne.symm hat)
    have hTB : T ≠ B := hne (Ne.symm hbt)
    have hTZ : T ≠ Z := hne htz
    have hT'A : T' ≠ A := hne (Ne.symm hat')
    have hT'B : T' ≠ B := hne (Ne.symm hbt')
    have hT'Z : T' ≠ Z := hne ht'z
    have hZA : Z ≠ A := hne (Ne.symm haz)
    have hZB : Z ≠ B := hne (Ne.symm hbz)
    have hAB : A ≠ B := hne hab
    have hTT' : T ≠ T' := hne (Ne.symm hqt)
    have hconjσ : ∀ σ : Equiv.Perm Ω, Equiv.Perm.sign σ = 1 →
        ∃ h ∈ H, ∀ p : Ω, h * (p : G) * h⁻¹ = σ p := by
      intro σ hσ
      obtain ⟨h, hh⟩ := hsurj σ hσ
      exact ⟨h, h.2, fun p => by rw [← hh]; rfl⟩
    have hsign : ∀ {u v w y : Ω}, u ≠ v → w ≠ y →
        Equiv.Perm.sign (Equiv.swap u v * Equiv.swap w y) = 1 := by
      intro u v w y h1 h2
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap h1, Equiv.Perm.sign_swap h2]
      decide
    have hxz : t * t' ≠ S.z := by
      intro hx
      obtain ⟨h, -, hh⟩ := hconjσ _ (hsign hZA hAB)
      have e1 := hh T
      have e2 := hh T'
      have e3 := hh Z
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hTA hTB,
        Equiv.swap_apply_of_ne_of_ne hTZ hTA] at e1
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hT'A hT'B,
        Equiv.swap_apply_of_ne_of_ne hT'Z hT'A] at e2
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hZA hZB,
        Equiv.swap_apply_left] at e3
      apply haz
      calc a = h * S.z * h⁻¹ := e3.symm
        _ = h * (t * t') * h⁻¹ := by rw [hx]
        _ = (h * t * h⁻¹) * (h * t' * h⁻¹) := by group
        _ = t * t' := by rw [e1, e2]
        _ = S.z := hx
    have hx1 : t * t' ≠ 1 := by
      intro hx
      apply hqt
      calc t' = t⁻¹ := eq_inv_of_mul_eq_one_right hx
        _ = t := htinv
    obtain ⟨h, -, hh⟩ := hconjσ _ (hsign hT'Z hAB)
    have e1 := hh T
    have e2 := hh T'
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hTA hTB,
      Equiv.swap_apply_of_ne_of_ne hTT' hTZ] at e1
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hT'A hT'B,
      Equiv.swap_apply_left] at e2
    have hxconj : h * (t * t') * h⁻¹ = S.z * t := by
      calc h * (t * t') * h⁻¹ = (h * t * h⁻¹) * (h * t' * h⁻¹) := by group
        _ = t * S.z := by rw [e1, e2]
        _ = S.z * t := hcomm t htΩ S.z hzΩ
    intro hc
    obtain ⟨c, hcz⟩ := isConj_iff.mp hc
    have hx' : (h⁻¹ * c) * S.z * (h⁻¹ * c)⁻¹ = t * t' := by
      calc (h⁻¹ * c) * S.z * (h⁻¹ * c)⁻¹ = h⁻¹ * (c * S.z * c⁻¹) * h := by group
        _ = h⁻¹ * (h * (t * t') * h⁻¹) * h := by rw [hcz, hxconj]
        _ = t * t' := by group
    have := hW (h⁻¹ * c) (hx' ▸ hxQ)
    rw [hx'] at this
    exact hxz this

end Setting

end CFSG.LargeExtraspecial
