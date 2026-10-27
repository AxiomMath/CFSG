module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84C6Inv
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Ker

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace C10

open Subgroup

variable {G : Type} [Group G] {E B : Subgroup G} {u : MulAut ↥E}
  {A H : Subgroup (MulAut ↥E)}

private theorem finite_A (S : HCtx E B u A H) : Finite ↥A := by
  obtain ⟨φA⟩ := S.A_iso
  exact Finite.of_equiv (alternatingGroup (Fin 6)) φA.toEquiv.symm

private theorem mem_zpowers_u_eq (S : HCtx E B u A H) {v : MulAut ↥E}
    (hv : v ∈ zpowers u) : v = 1 ∨ v = u := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have h2 : orderOf u = 2 := by
    have hdvd : orderOf u ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact S.u_sq)
    have hne1 : orderOf u ≠ 1 := by
      intro h
      exact S.u_A (by rw [orderOf_eq_one_iff.mp h]; exact A.one_mem)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have h3 : u ^ (i % (orderOf u : ℤ)) = u ^ i := zpow_mod_orderOf u i
  rw [h2] at h3
  push_cast at h3
  rcases Int.emod_two_eq_zero_or_one i with h | h
  · left; rw [← h3, h]; simp
  · right; rw [← h3, h]; simp

private theorem card_fix_resHom (hInv : Sec8T84FactInv) (S : HCtx E B u A H)
    {a : MulAut ↥E} (ha : a ∈ A) (h1 : a ≠ 1) (h2 : a * a = 1) :
    Nat.card {b : ↥B //
      (T84Mod.resHom S.hBE u S.fix A S.A_comm ⟨a, ha⟩) b = b} = 4 := by
  refine (Nat.card_congr ?_).trans (HCtx.card_fixB_of_inv hInv S ha h1 h2)
  refine
    { toFun := fun b => ⟨T84Mod.embB S.hBE b.1,
        ⟨b.1.2, (HCtx.resHom_apply_eq_self_iff S ha b.1).mp b.2⟩⟩
      invFun := fun e => ⟨⟨(e.1 : G), e.2.1⟩, by
        have hemb : T84Mod.embB S.hBE (⟨(e.1 : G), e.2.1⟩ : ↥B) = e.1 :=
          Subtype.ext rfl
        refine (HCtx.resHom_apply_eq_self_iff S ha ⟨(e.1 : G), e.2.1⟩).mpr ?_
        rw [hemb]; exact e.2.2⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }

theorem HCtx.card_le_four (hInv : Sec8T84FactInv) (S : HCtx E B u A H)
    {R : Subgroup (MulAut ↥E)} (hRA : R ≤ A) (hR2 : ∀ r ∈ R, r * r = 1) :
    Nat.card ↥R ≤ 4 := by
  classical
  haveI : Finite ↥A := finite_A S
  haveI : Finite ↥R :=
    Finite.of_injective (fun r : ↥R => (⟨(r : MulAut ↥E), hRA r.2⟩ : ↥A))
      (fun a b h => Subtype.ext (congrArg (fun z : ↥A => (z : MulAut ↥E)) h))
  haveI : Finite ↥B :=
    Nat.finite_of_card_ne_zero (by rw [S.hB.2]; norm_num)
  let ψ : ↥R →* ↥A :=
    { toFun := fun r => ⟨(r : MulAut ↥E), hRA r.2⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl }
  let ρ : ↥R →* Equiv.Perm ↥B :=
    (MulAction.toPermHom (MulAut ↥B) ↥B).comp
      ((T84Mod.resHom S.hBE u S.fix A S.A_comm).comp ψ)
  have hX : Nat.card ↥B = 16 := by rw [S.hB.2]; norm_num
  have hsq : ∀ r : ↥R, r * r = 1 := fun r => Subtype.ext (hR2 r.1 r.2)
  have hfix : ∀ r : ↥R, r ≠ 1 → Nat.card {x : ↥B // ρ r x = x} = 4 := by
    intro r hr
    have hra : (r : MulAut ↥E) ≠ 1 := by
      intro h
      exact hr (Subtype.ext h)
    have hr2 : (r : MulAut ↥E) * (r : MulAut ↥E) = 1 := hR2 r.1 r.2
    have hiff : ∀ x : ↥B, ρ r x = x ↔
        (T84Mod.resHom S.hBE u S.fix A S.A_comm
          ⟨(r : MulAut ↥E), hRA r.2⟩) x = x := by
      intro x
      rw [show ρ r x = (T84Mod.resHom S.hBE u S.fix A S.A_comm
          ⟨(r : MulAut ↥E), hRA r.2⟩) x from rfl]
    refine (Nat.card_congr (Equiv.subtypeEquivRight hiff)).trans ?_
    exact card_fix_resHom hInv S (hRA r.2) hra hr2
  exact card_le_four_of_fix_four hX ρ hsq hfix

theorem HCtx.card_le_eight_of_le_C (hInv : Sec8T84FactInv) (S : HCtx E B u A H)
    {R : Subgroup (MulAut ↥E)} (hRC : R ≤ A ⊔ zpowers u) (hR2 : ∀ r ∈ R, r * r = 1) :
    Nat.card ↥R ≤ 8 := by
  classical
  have hR0 : Nat.card ↥(R ⊓ A) ≤ 4 :=
    HCtx.card_le_four hInv S inf_le_right (fun r hr => hR2 r hr.1)
  haveI : Finite ↥E :=
    Nat.finite_of_card_ne_zero (by rw [S.hE.2]; norm_num)
  haveI : Finite (MulAut ↥E) :=
    Finite.of_injective (fun f : MulAut ↥E => (fun x : ↥E => f x))
      (fun f g h => MulEquiv.ext (fun x => congrArg (fun φ : ↥E → ↥E => φ x) h))
  have hAcomm : ∀ a ∈ A, ∀ v ∈ zpowers u, a * v = v * a := by
    intro a ha v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact Commute.zpow_right (show Commute a u from S.A_comm a ha) i
  have hdecomp : ∀ r ∈ R, r ∈ A ∨ ∃ a ∈ A, r = a * u := by
    intro r hr
    obtain ⟨a, ha, v, hv, hav⟩ := A3.exists_mul_of_comm hAcomm (hRC hr)
    rcases mem_zpowers_u_eq S hv with hv1 | hvu
    · left
      rw [hv1, mul_one] at hav
      rw [hav]
      exact ha
    · right; exact ⟨a, ha, by rw [hvu] at hav; exact hav⟩
  have hle : Nat.card ↥R ≤ Nat.card ↥(R ⊓ A) * 2 := by
    by_cases h : ∃ r : MulAut ↥E, r ∈ R ∧ r ∉ A
    · obtain ⟨r₁, hr₁R, hr₁A⟩ := h
      have hkey : ∀ r ∈ R, r ∉ A → r * r₁⁻¹ ∈ A := by
        intro r hr hrA
        obtain ⟨a, ha, hav⟩ := (hdecomp r hr).resolve_left hrA
        obtain ⟨a₁, ha₁, ha₁v⟩ := (hdecomp r₁ hr₁R).resolve_left hr₁A
        rw [hav, ha₁v]
        have heq : (a * u) * (a₁ * u)⁻¹ = a * a₁⁻¹ := by group
        rw [heq]
        exact A.mul_mem ha (A.inv_mem ha₁)
      let g : ↥R → ↥(R ⊓ A) × Bool := fun r =>
        if hr : (r : MulAut ↥E) ∈ A then
          (⟨(r : MulAut ↥E), ⟨r.2, hr⟩⟩, false)
        else
          (⟨(r : MulAut ↥E) * r₁⁻¹,
            ⟨R.mul_mem r.2 (R.inv_mem hr₁R), hkey (r : MulAut ↥E) r.2 hr⟩⟩, true)
      have hg : Function.Injective g := by
        intro x y hxy
        by_cases hx : (x : MulAut ↥E) ∈ A
        · by_cases hy : (y : MulAut ↥E) ∈ A
          · have hfst : (⟨(x : MulAut ↥E), ⟨x.2, hx⟩⟩ : ↥(R ⊓ A)) =
                ⟨(y : MulAut ↥E), ⟨y.2, hy⟩⟩ := by
              have := congrArg Prod.fst hxy
              simpa [g, dif_pos hx, dif_pos hy] using this
            exact Subtype.ext (congrArg (fun z : ↥(R ⊓ A) => (z : MulAut ↥E)) hfst)
          · have hsnd := congrArg Prod.snd hxy
            simp [g, dif_pos hx, dif_neg hy] at hsnd
        · by_cases hy : (y : MulAut ↥E) ∈ A
          · have hsnd := congrArg Prod.snd hxy
            simp [g, dif_neg hx, dif_pos hy] at hsnd
          · have hfst : (⟨(x : MulAut ↥E) * r₁⁻¹,
                ⟨R.mul_mem x.2 (R.inv_mem hr₁R), hkey (x : MulAut ↥E) x.2 hx⟩⟩ :
                  ↥(R ⊓ A)) =
                ⟨(y : MulAut ↥E) * r₁⁻¹,
                ⟨R.mul_mem y.2 (R.inv_mem hr₁R), hkey (y : MulAut ↥E) y.2 hy⟩⟩ := by
              have := congrArg Prod.fst hxy
              simpa [g, dif_neg hx, dif_neg hy] using this
            have hval : (x : MulAut ↥E) * r₁⁻¹ = (y : MulAut ↥E) * r₁⁻¹ :=
              congrArg (fun z : ↥(R ⊓ A) => (z : MulAut ↥E)) hfst
            exact Subtype.ext (mul_right_cancel hval)
      haveI : Finite ↥(R ⊓ A) := by
        haveI : Finite ↥A := finite_A S
        exact Finite.of_injective
          (fun x : ↥(R ⊓ A) => (⟨(x : MulAut ↥E), x.2.2⟩ : ↥A))
          (fun a b h => Subtype.ext (congrArg (fun z : ↥A => (z : MulAut ↥E)) h))
      calc Nat.card ↥R ≤ Nat.card (↥(R ⊓ A) × Bool) :=
            Nat.card_le_card_of_injective g hg
        _ = Nat.card ↥(R ⊓ A) * Nat.card Bool := Nat.card_prod _ _
        _ = Nat.card ↥(R ⊓ A) * 2 := by
              rw [show Nat.card Bool = 2 from by
                rw [Nat.card_eq_fintype_card]; decide]
    · have hRA : R ≤ A := fun r hr => by
        by_contra hnr
        exact h ⟨r, hr, hnr⟩
      have hEq : R ⊓ A = R := le_antisymm inf_le_left (le_inf le_rfl hRA)
      calc Nat.card ↥R = Nat.card ↥R * 1 := (Nat.mul_one _).symm
        _ ≤ Nat.card ↥R * 2 := Nat.mul_le_mul_left _ (by norm_num)
        _ = Nat.card ↥(R ⊓ A) * 2 := by rw [hEq]
  calc Nat.card ↥R ≤ Nat.card ↥(R ⊓ A) * 2 := hle
    _ ≤ 4 * 2 := Nat.mul_le_mul_right 2 hR0
    _ = 8 := by norm_num

end C10

end CFSG.OddStandard.SmallF3.Omega
