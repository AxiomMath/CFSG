module

public import CFSG.GH74.Generic.BProg.B3.Obs

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Blueprint CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

namespace LocBalSL4Abs

variable {X : Type} [Group X]

@[expose] def phi {H : Subgroup (MulAut X)} (hH : (MulAut.conj : X →* MulAut X).range ≤ H) :
    X →* ↥H :=
  (MulAut.conj : X →* MulAut X).codRestrict H (fun x => hH ⟨x, rfl⟩)

theorem coe_phi {H : Subgroup (MulAut X)} (hH : (MulAut.conj : X →* MulAut X).range ≤ H) (x : X) :
    ((phi hH x : ↥H) : MulAut X) = MulAut.conj x := rfl

theorem aut_mul_conj_mul_inv (σ : MulAut X) (w : X) :
    σ * MulAut.conj w * σ⁻¹ = MulAut.conj (σ w) := by
  ext x
  simp [MulAut.conj_apply]

theorem commute_conj_of_fix (σ : MulAut X) {w : X} (hw : σ w = w) :
    σ * MulAut.conj w = MulAut.conj w * σ := by
  have h := aut_mul_conj_mul_inv σ w
  rw [hw, mul_inv_eq_iff_eq_mul] at h
  exact h

theorem centerless_quotient_of_quasisimple {Y : Type} [Group Y] (hq : CFSG.IsQuasisimple Y) :
    ∀ k : Y ⧸ Subgroup.center Y, (∀ g : Y ⧸ Subgroup.center Y, g * k = k * g) → k = 1 := by
  intro k hk
  obtain ⟨-, hs, a, b, hab⟩ := hq
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (Y ⧸ Subgroup.center Y)) with
    h | h
  · have hk' : k ∈ Subgroup.center (Y ⧸ Subgroup.center Y) :=
      Subgroup.mem_center_iff.mpr fun g => hk g
    rw [h] at hk'
    exact hk'
  · exfalso
    have ha : a ∈ Subgroup.center (Y ⧸ Subgroup.center Y) := by
      rw [h]
      trivial
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

end LocBalSL4Abs

open LocBalSL4Abs in
theorem locBal32_of_fix {K X : Type} [Group K] [Group X] [Finite X] (π : K →* X)
    (hπ : Function.Surjective π) (hZ : ∀ x : X, (∀ g : X, g * x = x * g) → x = 1)
    {Ab : Subgroup K} (hAe : CFSG.IsElementaryAbelian 2 ↥Ab) (hA8 : Nat.card ↥Ab = 8)
    {z : K} (hzA : z ∈ Ab) (hz1 : z ≠ 1) (hπz : π z = 1)
    (hgen : (⨆ (b : K) (_ : b ∈ Ab ∧ π b ≠ 1), centralizer ({b} : Set K)) = ⊤)
    (hP : ∀ u ∈ Ab, π u ≠ 1 → ∀ (H : Subgroup (MulAut X))
      (hH : (MulAut.conj : X →* MulAut X).range ≤ H), ∀ c ∈ involutionOddCore (phi hH (π u)),
      ∀ w ∈ (centralizer ({u} : Set K)).map π, ((c : ↥H) : MulAut X) w = w)
    (B : Subgroup (MulAut X)) (hB : B ≤ (Ab.map π).map (MulAut.conj : X →* MulAut X)) :
    IsLocBal32 X B := by
  intro H hH hBH
  have hAcomm : ∀ a ∈ Ab, ∀ a' ∈ Ab, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥Ab)).comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hconj_inj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    apply hZ t
    intro g
    have h2 := congrArg (fun f : MulAut X => f g) ht
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    rw [mul_inv_eq_iff_eq_mul] at h2
    exact h2.symm
  refine ⟨?_, ?_⟩
  · intro b hb hb1 c hc b' hb'
    have hbB : (b : MulAut X) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hb'B : (b' : MulAut X) ∈ B := Subgroup.mem_subgroupOf.mp hb'
    obtain ⟨y, ⟨a, haA, rfl⟩, hya⟩ := Subgroup.mem_map.mp (hB hbB)
    obtain ⟨y', ⟨a', ha'A, rfl⟩, hya'⟩ := Subgroup.mem_map.mp (hB hb'B)
    have hbphi : b = phi hH (π a) := Subtype.ext hya.symm
    have hb'phi : b' = phi hH (π a') := Subtype.ext hya'.symm
    have hπa : π a ≠ 1 := by
      intro h1
      apply hb1
      rw [hbphi, h1, map_one]
    rw [hbphi] at hc
    have hfix := hP a haA hπa H hH c hc (π a')
      ⟨a', Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm a' ha'A a haA), rfl⟩
    rw [hb'phi, commutatorElement_eq_one_iff_mul_comm]
    apply Subtype.ext
    simp only [Subgroup.coe_mul, coe_phi]
    exact commute_conj_of_fix (c : MulAut X) hfix
  · intro D hD hcard hsq
    let f : ↥Ab →* MulAut X := ((MulAut.conj : X →* MulAut X).comp π).comp Ab.subtype
    have hfrange : f.range = (Ab.map π).map (MulAut.conj : X →* MulAut X) := by
      ext g
      simp only [MonoidHom.mem_range, Subgroup.mem_map]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨π a, ⟨a, a.2, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
    have hker : 2 ≤ Nat.card f.ker := by
      have h1 : (1 : ↥Ab) ∈ f.ker := Subgroup.one_mem _
      have h2 : (⟨z, hzA⟩ : ↥Ab) ∈ f.ker := by
        show ((MulAut.conj : X →* MulAut X).comp π).comp Ab.subtype ⟨z, hzA⟩ = 1
        simp [hπz]
      have hne : (⟨z, hzA⟩ : ↥Ab) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
      have hbot : f.ker ≠ ⊥ := fun h => hne (by simpa [h] using h2)
      have : Finite ↥Ab := Nat.finite_of_card_ne_zero (by omega)
      exact Nat.succ_le_of_lt ((Subgroup.one_lt_card_iff_ne_bot f.ker).mpr hbot)
    have hrange4 : Nat.card f.range ≤ 4 := by
      have h1 := Subgroup.card_mul_index f.ker
      rw [Subgroup.index_ker, hA8] at h1
      by_contra hlt
      push Not at hlt
      have : 2 * 5 ≤ Nat.card f.ker * Nat.card f.range := Nat.mul_le_mul hker hlt
      omega
    let D' : Subgroup (MulAut X) := D.map H.subtype
    have hD'B : D' ≤ B := by
      rintro _ ⟨d, hd, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hD hd)
    have hD'card : Nat.card ↥D' = 4 := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact hcard
    have hD'E : D' = f.range := by
      rw [hfrange]
      apply Subgroup.eq_of_le_of_card_ge
      · exact hD'B.trans hB
      · rw [← hfrange, hD'card]
        exact hrange4
    rw [eq_bot_iff]
    intro c hc
    have hfixall : ∀ u ∈ Ab, π u ≠ 1 → ∀ w ∈ (centralizer ({u} : Set K)).map π,
        ((c : ↥H) : MulAut X) w = w := by
      intro u huA hπu
      have hmemE : MulAut.conj (π u) ∈ f.range := ⟨⟨u, huA⟩, rfl⟩
      rw [← hD'E] at hmemE
      obtain ⟨d, hd, hdu⟩ := hmemE
      have hdphi : d = phi hH (π u) := Subtype.ext hdu
      have hd1 : d ≠ 1 := by
        intro h1
        have : MulAut.conj (π u) = 1 := by rw [← hdu, h1]; rfl
        exact hπu (hconj_inj (by rw [this, map_one]))
      have hcd : c ∈ involutionOddCore d := deltaCore_le_involutionOddCore hd hd1 hc
      rw [hdphi] at hcd
      exact hP u huA hπu H hH c hcd
    let Kc : Subgroup X := ((c : ↥H) : MulAut X).toMonoidHom.eqLocus (MonoidHom.id X)
    have hle : (⨆ (b : K) (_ : b ∈ Ab ∧ π b ≠ 1), centralizer ({b} : Set K)).map π ≤ Kc := by
      rw [Subgroup.map_iSup]
      refine iSup_le fun b => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hb => ?_
      intro w hw
      exact hfixall b hb.1 hb.2 w hw
    rw [hgen, Subgroup.map_top_of_surjective _ hπ] at hle
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    exact hle (Subgroup.mem_top x)

end CFSG.GH74.Generic.BProg.B3
