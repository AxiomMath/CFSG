module

public import CFSG.CGT.PushingUpLit.LIT.A4.L34Cfg

public section

namespace CFSG.CGT.PushingUpLit.A4.L34

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.SolK
  CFSG.RankThree.PartOne.SolD3 CFSG.CGT.PushingUpLit.A4

variable {G : Type} [Group G]

theorem klein_sq {U : Subgroup G} (hU : IsKleinFour ↥U) {u : G} (hu : u ∈ U) : u * u = 1 := by
  have := IsKleinFour.mul_self (G := ↥U) ⟨u, hu⟩
  exact congrArg Subtype.val this

theorem isKleinFour_of_card_four {U : Subgroup G} (h4 : Nat.card U = 4)
    (hsq : ∀ x ∈ U, x * x = 1) : IsKleinFour ↥U := by
  refine ⟨h4, ?_⟩
  have hex : Monoid.exponent ↥U ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
      apply Subtype.ext
      have := hsq x.1 x.2
      simpa [pow_two] using this
  rcases (Nat.dvd_prime Nat.prime_two).mp hex with h | h
  · exfalso
    have : Subsingleton ↥U := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : ↥U)
    omega
  · exact h

theorem klein_pGroup {U : Subgroup G} (hU : IsKleinFour ↥U) : IsPGroup 2 ↥U :=
  IsPGroup.of_card (n := 2) (by rw [IsKleinFour.card_four]; norm_num)

theorem exists_ne_of_card_four [Finite G] {U : Subgroup G} (h4 : Nat.card U = 4)
    (hsq : ∀ x ∈ U, x * x = 1) {u : G} (hu : u ∈ U) : ∃ x ∈ U, x ≠ 1 ∧ x ≠ u := by
  by_contra hcon
  push Not at hcon
  have hle : U ≤ Subgroup.zpowers u := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · rw [hcon x hx hx1]; exact Subgroup.mem_zpowers u
  have h1 := Subgroup.card_le_of_le hle
  have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq u hu)
  rw [Nat.card_zpowers, h4] at h1
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem klein_exists_ne [Finite G] {U : Subgroup G} (hU : IsKleinFour ↥U) {u : G} (hu : u ∈ U) :
    ∃ x ∈ U, x ≠ 1 ∧ x ≠ u :=
  exists_ne_of_card_four IsKleinFour.card_four (fun _ hx => klein_sq hU hx) hu

theorem exists_centralizing [Finite G] {X : Subgroup G} {a : G} (hb : Blk3 X a) {U : Subgroup G}
    (hU : IsKleinFour ↥U) (hn : ∀ s ∈ U, conjSub s X = X) :
    ∃ u ∈ U, u ≠ 1 ∧ ∀ w ∈ pCoreOf 2 X, w * u = u * w := by
  have hcard := card_le_two_mul_card_centralizer hb (klein_pGroup hU)
    (fun s hs w hw => conj_mem_pCoreOf (hn s hs) hw)
  rw [IsKleinFour.card_four] at hcard
  have hne : (Subgroup.centralizer (pCoreOf 2 X : Set G) ⊓ U) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    omega
  obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hu' := Subgroup.mem_inf.1 u.2
  refine ⟨u, hu'.2, fun e => hu1 (Subtype.ext e), fun w hw => ?_⟩
  exact Subgroup.mem_centralizer_iff.1 hu'.1 w hw

theorem mul_conj_mem_centralizer {u x : G} (huu : u * u = 1)
    (hc : x * (u * x * u⁻¹) = (u * x * u⁻¹) * x) :
    x * (u * x * u⁻¹) ∈ Subgroup.centralizer ({u} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have huu' : u⁻¹ * u⁻¹ = 1 := by rw [← mul_inv_rev, huu, inv_one]
  have e : u * (x * (u * x * u⁻¹)) * u⁻¹ = x * (u * x * u⁻¹) := by
    calc u * (x * (u * x * u⁻¹)) * u⁻¹
        = (u * x * u⁻¹) * ((u * u) * x * (u⁻¹ * u⁻¹)) := by group
      _ = (u * x * u⁻¹) * x := by rw [huu, huu']; group
      _ = x * (u * x * u⁻¹) := hc.symm
  exact (mul_inv_eq_iff_eq_mul.1 e).symm

theorem lemma1a [Finite G] {X : Subgroup G} {a : G} (hb : Blk3 X a) {N U : Subgroup G}
    (hU : IsKleinFour ↥U) (hn : ∀ s ∈ U, conjSub s X = X)
    (hC : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ N) : pCoreOf 2 X ≤ N := by
  intro w hw
  obtain ⟨u, huU, hu1, hcomm⟩ := exists_centralizing hb hU hn
  exact hC u huU hu1 (Subgroup.mem_centralizer_singleton_iff.2 (hcomm w hw))

theorem lemma1b [Finite G] {X Y : Subgroup G} {a : G} (hb : Blk3 X a)
    (hcomm : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hXY : Y ≠ X) {N U : Subgroup G}
    (hU : IsKleinFour ↥U) {u : G} (huU : u ∈ U) (hu₂ : conjSub u X = Y ∧ conjSub u Y = X)
    (hperm : ∀ x ∈ U, conjSub x X = X ∨ conjSub x X = Y)
    (hC : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ N) :
    pCoreOf 2 X ≤ N ∧ pCoreOf 2 Y ≤ N := by
  have hUN : ∀ u ∈ U, u ∈ N := by
    intro u hu
    by_cases hu1 : u = 1
    · rw [hu1]
      exact N.one_mem
    · exact hC u hu hu1 (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hsq : ∀ u ∈ U, u * u = 1 := fun u hu => klein_sq hU hu
  have hu1 : u ≠ 1 := fun e => hXY (by rw [← hu₂.1, e, conjSub_one])
  have hv : ∃ v ∈ U, v ≠ 1 ∧ conjSub v X = X := by
    obtain ⟨x, hxU, hx1, hxu⟩ := klein_exists_ne hU huU
    rcases hperm x hxU with ex1 | ex1
    · exact ⟨x, hxU, hx1, ex1⟩
    · refine ⟨u * x, U.mul_mem huU hxU, ?_, ?_⟩
      · intro e
        apply hxu
        have h1 : x = u⁻¹ := eq_inv_of_mul_eq_one_right e
        rw [h1]
        exact inv_eq_of_mul_eq_one_right (hsq u huU)
      · rw [← conjSub_conjSub, ex1, hu₂.2]
  obtain ⟨v, hvU, hv1, hvn⟩ := hv
  let S : Subgroup G := U ⊓ Subgroup.normalizer (X : Set G)
  have hSv : v ∈ S := Subgroup.mem_inf.2 ⟨hvU, mem_normalizer_iff_conjSub.2 hvn⟩
  have hS2 : IsPGroup 2 ↥S := (klein_pGroup hU).to_le inf_le_left
  have hSn : ∀ s ∈ S, ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ ∈ pCoreOf 2 X := fun s hs w hw =>
    conj_mem_pCoreOf (mem_normalizer_iff_conjSub.1 (Subgroup.mem_inf.1 hs).2) hw
  obtain ⟨c, hcV, hc1, hcv⟩ := Blk3.exists_fixed hb hS2 hSn hSv
  have hcN : c ∈ N := by
    refine hC v hvU hv1 (Subgroup.mem_centralizer_singleton_iff.2 ?_)
    have := mul_inv_eq_iff_eq_mul.1 hcv
    exact this.symm
  have hx2 : ∀ x ∈ X, u * x * u⁻¹ ∈ Y := fun x hx => by
    rw [← hu₂.1]
    exact conj_mem_conjSub hx
  have hℓ : ∀ x ∈ X, x * (u * x * u⁻¹) ∈ N := by
    intro x hx
    exact hC u huU hu1 (mul_conj_mem_centralizer (hsq u huU) (hcomm x hx _ (hx2 x hx)))
  have hcx : ∀ x ∈ X, x⁻¹ * c * x ∈ N := by
    intro x hx
    have hℓN := hℓ x hx
    have hcXV : c ∈ X := (pCoreOf_le_self X) hcV
    have h1 : (x⁻¹ * c * x) * (u * x * u⁻¹) = (u * x * u⁻¹) * (x⁻¹ * c * x) :=
      hcomm _ (X.mul_mem (X.mul_mem (X.inv_mem hx) hcXV) hx) _ (hx2 x hx)
    have e : (x * (u * x * u⁻¹))⁻¹ * c * (x * (u * x * u⁻¹)) = x⁻¹ * c * x := by
      calc (x * (u * x * u⁻¹))⁻¹ * c * (x * (u * x * u⁻¹))
          = (u * x * u⁻¹)⁻¹ * ((x⁻¹ * c * x) * (u * x * u⁻¹)) := by group
        _ = (u * x * u⁻¹)⁻¹ * ((u * x * u⁻¹) * (x⁻¹ * c * x)) := by rw [h1]
        _ = x⁻¹ * c * x := by group
    have := N.mul_mem (N.mul_mem (N.inv_mem hℓN) hcN) hℓN
    rwa [e] at this
  have hV1N : pCoreOf 2 X ≤ N := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact N.one_mem
    · obtain ⟨x, hx, hxw⟩ := Blk3.exists_conj_of_ne_one hb hcV hc1 hw hw1
      have := hcx x⁻¹ (X.inv_mem hx)
      simpa [hxw] using this
  refine ⟨hV1N, ?_⟩
  intro w hw
  have hV : pCoreOf 2 Y = conjSub u (pCoreOf 2 X) := by
    rw [← pCoreOf_conjSub, hu₂.1]
  rw [hV, mem_conjSub_iff] at hw
  have h1 := hV1N hw
  have hu' := hUN u huU
  have := N.mul_mem (N.mul_mem hu' h1) (N.inv_mem hu')
  simpa [mul_assoc] using this

theorem lemma1 [Finite G] {t : Two G} (h : t.Cfg) {N U : Subgroup G} (hUM : U ≤ t.M)
    (hU : IsKleinFour ↥U)
    (hC : ∀ u ∈ U, u ≠ 1 → Subgroup.centralizer ({u} : Set G) ≤ N) :
    t.V₁ ≤ N ∧ t.V₂ ≤ N := by
  by_cases hI : ∀ u ∈ U, conjSub u t.X₁ = t.X₁
  · have hI2 : ∀ u ∈ U, conjSub u t.X₂ = t.X₂ := by
      intro u hu
      rcases h.perm u (hUM hu) with ⟨-, e2⟩ | ⟨e1, -⟩
      · exact e2
      · exact absurd ((hI u hu).symm.trans e1) h.X_ne
    exact ⟨lemma1a h.blk₁ hU hI hC, lemma1a h.blk₂ hU hI2 hC⟩
  · push Not at hI
    obtain ⟨u, huU, hu⟩ := hI
    have hu₂ : conjSub u t.X₁ = t.X₂ ∧ conjSub u t.X₂ = t.X₁ := by
      rcases h.perm u (hUM huU) with hh | hh
      · exact absurd hh.1 hu
      · exact hh
    exact lemma1b h.blk₁ h.comm h.X_ne.symm hU huU hu₂
      (fun x hx => by
        rcases h.perm x (hUM hx) with ⟨e1, -⟩ | ⟨e1, -⟩
        · exact Or.inl e1
        · exact Or.inr e1) hC

end CFSG.CGT.PushingUpLit.A4.L34
