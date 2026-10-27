module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co2Std.Exclusion.XN0e
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.EvenSporadicStandard.Co2Std.Exclusion

open Subgroup

variable {V : Type*} [Group V] {X : Type*} [Group X] {ρ : X →* MulAut V} {Q : Subgroup X}
  {V₁ V₂ : Subgroup V} {z : X} {Q₁ : Subgroup (MulAut ↥V₁)} {t₁ : ↥V₁}

theorem XHyp.commutator_le_layer [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁) (hE : layer X ≠ ⊥) :
    ⁅Q, Q⁆ ≤ layer X := by
  haveI : (layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  have hEnorm : (layer X).Normal := Subgroup.normal_of_characteristic (layer X)
  haveI : Group.IsPerfect ↥(layer X) := CFSG.LocalCores.layer_isPerfect
  set E := layer X with hEdef
  set J : Subgroup X := E ⊓ Subgroup.centralizer ({z} : Set X) with hJdef
  have hJle : J ≤ Subgroup.centralizer ({z} : Set X) := inf_le_right
  have hJn : ∀ c ∈ Subgroup.centralizer ({z} : Set X), ∀ y ∈ J, c * y * c⁻¹ ∈ J := by
    intro c hc y hy
    refine ⟨hEnorm.conj_mem y hy.1 c, ?_⟩
    have hc' : Commute c z := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hy' : Commute y z := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (((hc'.mul_left hy').mul_left hc'.inv_left).eq)
  rcases h.le_zpowers_or_le hJle hJn with hJz | hQ'J
  · by_cases hzE : z ∈ E
    ·
      exfalso
      have hJeq : J = Subgroup.zpowers z := by
        refine le_antisymm hJz ?_
        rw [Subgroup.zpowers_le]
        exact ⟨hzE, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
      let zE : ↥E := ⟨z, hzE⟩
      have hzE_ne : zE ≠ 1 := by
        intro h1
        exact h.z_ne_one (by simpa [zE] using congrArg Subtype.val h1)
      have hzE2 : zE * zE = 1 := Subtype.ext (by simpa [zE] using h.mul_self)
      have hzEord : orderOf zE = 2 := by
        rw [Subgroup.orderOf_mk z hzE, h.orderOf_z]
      have hCE : Subgroup.centralizer ({zE} : Set ↥E) ≤ Subgroup.zpowers zE := by
        intro x hx
        have hx' : ((x : X)) ∈ Subgroup.centralizer ({z} : Set X) := by
          rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
          simpa [zE] using congrArg Subtype.val hx
        have hxJ : (x : X) ∈ J := ⟨x.2, hx'⟩
        rw [hJeq] at hxJ
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxJ
        exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa [zE] using hk)⟩
      have hzEcard : Nat.card (Subgroup.zpowers zE) = 2 := by
        rw [Nat.card_zpowers, hzEord]
      obtain ⟨S, hzS⟩ : ∃ S : Sylow 2 ↥E, zE ∈ S := by
        have h2 : IsPGroup 2 (Subgroup.zpowers zE) :=
          IsPGroup.of_card (n := 1) (by simpa using hzEcard)
        obtain ⟨S, hle⟩ := h2.exists_le_sylow
        exact ⟨S, hle (Subgroup.mem_zpowers zE)⟩
      have hSne : Nontrivial ↥S := by
        refine ⟨⟨zE, hzS⟩, ⟨1, S.one_mem⟩, ?_⟩
        intro h1
        exact hzE_ne (congrArg Subtype.val h1)
      have hcenter : Nontrivial (center ↥S) := S.isPGroup'.center_nontrivial
      obtain ⟨w, hw⟩ := exists_ne (1 : center ↥S)
      have hwS : ((w : ↥S)) ≠ 1 := fun h1 => hw (Subtype.ext (by simpa using h1))
      have hwz : ((w : ↥S) : ↥E) ∈ Subgroup.centralizer ({zE} : Set ↥E) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcomm : ∀ g : ↥S, g * (w : ↥S) = (w : ↥S) * g :=
          Subgroup.mem_center_iff.mp w.2
        have h1 := congrArg (fun t : ↥S => (t : ↥E)) (hcomm ⟨zE, hzS⟩)
        simpa using h1.symm
      have hwz' : ((w : ↥S) : ↥E) = zE := by
        rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hzEord).mp (hCE hwz) with h1 | h2
        · exact absurd (Subtype.ext h1) hwS
        · exact h2
      have hzS_center : (⟨zE, hzS⟩ : ↥S) ∈ center ↥S := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hcomm : ∀ g : ↥S, g * (w : ↥S) = (w : ↥S) * g :=
          Subgroup.mem_center_iff.mp w.2
        have h1 := hcomm g
        rwa [show (w : ↥S) = ⟨zE, hzS⟩ from Subtype.ext hwz'] at h1
      have hSle : (S : Subgroup ↥E) ≤ Subgroup.zpowers zE := by
        intro s hs
        apply hCE
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := Subgroup.mem_center_iff.mp hzS_center (⟨s, hs⟩ : ↥S)
        simpa using h1
      have hzpS : Subgroup.zpowers zE ≤ (S : Subgroup ↥E) := Subgroup.zpowers_le.mpr hzS
      have hScard : Nat.card ↥S = 2 := by
        change Nat.card ↥(S : Subgroup ↥E) = 2
        rw [le_antisymm hSle hzpS, hzEcard]
      have hScyc : IsCyclic ↥S := by
        haveI : Fact (Nat.card ↥S).Prime := ⟨by rw [hScard]; exact Nat.prime_two⟩
        exact isCyclic_of_prime_card (p := Nat.card ↥S) rfl
      obtain ⟨N, hNnorm, hNS⟩ := exists_normal_isComplement'_of_isCyclic_sylow_two S hScyc
      haveI : N.Normal := hNnorm
      have hquot : Nat.card (↥E ⧸ N) = 2 := by
        rw [← Subgroup.index_eq_card, hNS.symm.index_eq_card]
        exact hScard
      have hcommle : commutator ↥E ≤ N :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mp (by
          haveI : Fact (Nat.card (↥E ⧸ N)).Prime := ⟨by rw [hquot]; exact Nat.prime_two⟩
          exact (isCyclic_of_prime_card (p := Nat.card (↥E ⧸ N)) rfl).isMulCommutative)
      have hNtop : N = ⊤ := by
        refine le_antisymm le_top ?_
        rw [← Group.IsPerfect.commutator_eq_top (G := ↥E)]
        exact hcommle
      have h1 : N.index = 1 := by rw [hNtop, Subgroup.index_top]
      have h2 : N.index = 2 := by rw [hNS.symm.index_eq_card]; exact hScard
      omega
    ·
      exfalso
      have hJbot : J = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro y hy
        by_contra hy1
        have hyz : y ∈ Subgroup.zpowers z := hJz hy
        have hdvd : orderOf y ∣ orderOf z := orderOf_dvd_of_mem_zpowers hyz
        rw [h.orderOf_z] at hdvd
        have hy2 : orderOf y = 2 := by
          rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
          · exact absurd (orderOf_eq_one_iff.mp h1) hy1
          · exact h2
        have hzy : Subgroup.zpowers y = Subgroup.zpowers z := by
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyz) ?_
          rw [Nat.card_zpowers, Nat.card_zpowers, hy2, h.orderOf_z]
        have hzEy : z ∈ E := by
          have hzmem : z ∈ Subgroup.zpowers y := by rw [hzy]; exact Subgroup.mem_zpowers z
          exact Subgroup.zpowers_le.mpr hy.1 hzmem
        exact hzE hzEy
      have hσfree : MonoidHom.FixedPointFree (MulAut.conjNormal (H := E) z).toMonoidHom := by
        intro e he
        have hval : z * (e : X) * z⁻¹ = (e : X) := by
          have h1 := congrArg Subtype.val he
          simpa [MulAut.conjNormal_apply] using h1
        have h1 : z * (e : X) = (e : X) * z := by
          conv_rhs => rw [← hval]
          group
        have hmem : (e : X) ∈ J :=
          ⟨e.2, Subgroup.mem_centralizer_singleton_iff.mpr h1.symm⟩
        rw [hJbot] at hmem
        exact Subtype.ext (by simpa using hmem)
      have hσinv : Function.Involutive (MulAut.conjNormal (H := E) z).toMonoidHom := by
        intro e
        have hzz : MulAut.conjNormal (H := E) z * MulAut.conjNormal (H := E) z = 1 := by
          rw [← map_mul, h.mul_self, map_one]
        show MulAut.conjNormal z (MulAut.conjNormal z e) = e
        rw [← MulAut.mul_apply, hzz, MulAut.one_apply]
      haveI : IsMulCommutative ↥E :=
        IsMulCommutative.of_comm fun a b => (hσfree.commute_all_of_involutive hσinv a b).eq
      exact hE ((Subgroup.eq_bot_iff_forall (layer X)).mpr fun x hx => by
        have h1 : (⟨x, hx⟩ : ↥E) = 1 := Subsingleton.elim _ _
        exact congrArg Subtype.val h1)
  · exact hQ'J.trans inf_le_left

theorem XHyp.odd_card_center_layer [Finite X] (h : XHyp ρ Q V₁ V₂ z Q₁ t₁)
    (hX : zpowers z ⊔ Q ≠ ⊤) : Odd (Nat.card (center (layer X))) := by
  haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [h.card_V]; norm_num)
  haveI : (layer X).Characteristic := CFSG.LocalCores.layer_characteristic
  have hEnorm : (layer X).Normal := Subgroup.normal_of_characteristic (layer X)
  let S : Subgroup X :=
    { carrier := {c : X | c ∈ layer X ∧
        c ∈ Subgroup.centralizer ((layer X : Subgroup X) : Set X) ∧
        c ^ (2 ^ Nat.card X) = 1}
      one_mem' := by
        refine ⟨(layer X).one_mem, Subgroup.one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haE, hac, ha2⟩ ⟨hbE, hbc, hb2⟩
        refine ⟨(layer X).mul_mem haE hbE, Subgroup.mul_mem _ hac hbc, ?_⟩
        have hcomm : Commute a b := by
          have h1 := (Subgroup.mem_centralizer_iff.mp hac) b hbE
          exact h1.symm
        rw [hcomm.mul_pow, ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨haE, hac, ha2⟩
        exact ⟨(layer X).inv_mem haE, Subgroup.inv_mem _ hac, by rw [inv_pow, ha2, inv_one]⟩ }
  have hSnorm : S.Normal := by
    refine ⟨fun c hc x => ?_⟩
    obtain ⟨hcE, hcc, hc2⟩ := hc
    have hcc' : ∀ e ∈ layer X, e * c = c * e := Subgroup.mem_centralizer_iff.mp hcc
    refine ⟨hEnorm.conj_mem c hcE x, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro e he
      have hxe : x⁻¹ * e * x ∈ layer X := by simpa using hEnorm.conj_mem e he x⁻¹
      have h1 : (x⁻¹ * e * x) * c = c * (x⁻¹ * e * x) := hcc' _ hxe
      calc e * (x * c * x⁻¹) = x * ((x⁻¹ * e * x) * c) * x⁻¹ := by group
        _ = x * (c * (x⁻¹ * e * x)) * x⁻¹ := by rw [h1]
        _ = (x * c * x⁻¹) * e := by group
    · have hconj : x * c * x⁻¹ = MulAut.conj x c := (MulAut.conj_apply x c).symm
      rw [hconj, ← map_pow, hc2, map_one]
  have hS2 : IsPGroup 2 S := by
    intro g
    exact ⟨Nat.card X, Subtype.ext (by simpa using g.2.2.2)⟩
  have hSbot : S = ⊥ := h.eq_bot_of_isPGroup hX hSnorm hS2
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2dvd
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
  have hc2 : ((c : ↥(layer X)) : X) ^ 2 = 1 := by
    have h2 : c ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
    simpa using congrArg Subtype.val (congrArg Subtype.val h2)
  have hmem : ((c : ↥(layer X)) : X) ∈ S := by
    refine ⟨(c : ↥(layer X)).2, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro e he
      have h1 := Subgroup.mem_center_iff.mp c.2 (⟨e, he⟩ : ↥(layer X))
      simpa using congrArg Subtype.val h1
    · have hdvd : 2 ∣ 2 ^ Nat.card X := by
        have h1 : (1 : ℕ) ≤ Nat.card X := by have := Nat.card_pos (α := X); omega
        exact pow_dvd_pow 2 h1
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, pow_mul, hc2, one_pow]
  rw [hSbot] at hmem
  have h1 : c = 1 := Subtype.ext (Subtype.ext (by simpa using Subgroup.mem_bot.mp hmem))
  rw [h1, orderOf_one] at hc
  omega

end CFSG.EvenSporadicStandard.Co2Std.Exclusion
