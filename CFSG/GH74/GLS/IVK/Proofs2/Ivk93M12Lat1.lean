module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12Spec

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

namespace BarShape.Spec

variable {zc : P} {W A B A₃ : Subgroup P} (hS : BarShape.Spec zc W A B A₃)
include hS

theorem exists_gen₃ : ∃ g : P, g ∈ A₃ ∧ orderOf g = 3 ∧ A₃ = zpowers g := by
  obtain ⟨e⟩ := hS.eA₃
  set g' : ↥A₃ := e.symm (Multiplicative.ofAdd (1 : ZMod 3)) with hg'
  have ho : orderOf g' = 3 := by
    rw [hg', MulEquiv.orderOf_eq, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hcard : Nat.card ↥A₃ = 3 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have hz : Nat.card ↥(zpowers (g' : P)) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, ho]
  refine ⟨(g' : P), g'.2, by rw [Subgroup.orderOf_coe]; exact ho, ?_⟩
  symm
  exact Subgroup.eq_of_le_of_card_ge (zpowers_le.2 g'.2) (by rw [hz, hcard])

omit [Finite P] in
theorem card_A₃ : Nat.card ↥A₃ = 3 := by
  obtain ⟨e⟩ := hS.eA₃
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    ZMod.card]

noncomputable def piHom : P →* Equiv.Perm (Fin 3) :=
  letI := hS.normal_W
  (Classical.choice hS.quot).toMonoidHom.comp (QuotientGroup.mk' W)

omit [Finite P] in
theorem piHom_ker (x : P) : hS.piHom x = 1 ↔ x ∈ W := by
  have := hS.normal_W
  classical
  unfold piHom
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply]
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

omit [Finite P] in
theorem piHom_surjective : Function.Surjective hS.piHom := by
  have := hS.normal_W
  unfold piHom
  exact (Classical.choice hS.quot).surjective.comp (QuotientGroup.mk'_surjective W)

omit [Finite P] in
theorem mem_zpowers_zc_iff (hz1 : zc ≠ 1) (hz2 : zc * zc = 1) {x : P} :
    x ∈ zpowers zc ↔ x = 1 ∨ x = zc := by
  have hord : orderOf zc = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have h := zpow_mod_orderOf zc k
    rw [hord] at h
    simp only [Nat.cast_ofNat] at h
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · left; rw [← h, h0]; simp
    · right; rw [← h, h0]; simp
  · rintro (rfl | rfl)
    · exact one_mem _
    · exact mem_zpowers _

theorem fix_gen (hP : BarShape P zc) {g : P} (hgA : A₃ = zpowers g) (hg3 : orderOf g = 3)
    {w : P} (hw : w ∈ W) (h : g * w * g⁻¹ * w⁻¹ ∈ zpowers zc) : w ∈ zpowers zc := by
  apply hS.fix w hw
  have hg1 : g * g * g = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg3] at this
    simpa [pow_succ, mul_assoc] using this
  have hg4 : g * g * (g * g) = g := by
    calc g * g * (g * g) = g * (g * g * g) := by simp only [mul_assoc]
      _ = g := by rw [hg1, mul_one]
  have hzc := hP.central
  have hz2 := hP.sq
  set z' := g * w * g⁻¹ * w⁻¹ with hz'
  have hz'1 : z' * z' = 1 := by
    rcases (hS.mem_zpowers_zc_iff hP.ne_one hz2).1 h with h1 | h1 <;> rw [h1]
    · simp
    · exact hz2
  have hz'c : ∀ x : P, x * z' = z' * x := by
    intro x
    rcases (hS.mem_zpowers_zc_iff hP.ne_one hz2).1 h with h1 | h1 <;> rw [h1]
    · simp
    · exact hzc x
  have hgw : g * w * g⁻¹ = z' * w := by rw [hz']; group
  have h2 : g * g * w * (g * g)⁻¹ = w := by
    have : g * g * w * (g * g)⁻¹ = g * (g * w * g⁻¹) * g⁻¹ := by group
    rw [this, hgw]
    have h3 : g * (z' * w) * g⁻¹ = (g * z' * g⁻¹) * (g * w * g⁻¹) := by group
    rw [h3, hgw]
    have h4 : g * z' * g⁻¹ = z' := by rw [hz'c g, mul_assoc]; simp
    rw [h4, ← mul_assoc, hz'1, one_mul]
  have h5 : g * w * g⁻¹ = w := by
    have h6 : g * w * g⁻¹ = (g * g * (g * g)) * w * (g * g * (g * g))⁻¹ := by rw [hg4]
    rw [h6]
    have h7 : g * g * (g * g) * w * (g * g * (g * g))⁻¹ =
        g * g * (g * g * w * (g * g)⁻¹) * (g * g)⁻¹ := by group
    rw [h7, h2, h2]
  have hcomm : g * w = w * g := by
    have := congrArg (· * g) h5
    simpa [mul_assoc] using this
  intro a ha
  rw [hgA] at ha
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  exact ((Commute.zpow_left (show Commute g w from hcomm) k)).eq

omit hS in
noncomputable def sylow3_of_card (hP : BarShape P zc) (H : Subgroup P) (hH : Nat.card ↥H = 3) :
    Sylow 3 P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpg : IsPGroup 3 ↥H := IsPGroup.of_card (n := 1) (by rw [hH]; norm_num)
  have h1 := Subgroup.card_mul_index H
  rw [hH, hP.card_eq] at h1
  have h2 : H.index = 64 := by omega
  exact hpg.toSylow (by rw [h2]; norm_num)

omit hS in
theorem coe_sylow3_of_card (hP : BarShape P zc) (H : Subgroup P) (hH : Nat.card ↥H = 3) :
    (sylow3_of_card hP H hH : Subgroup P) = H := by
  unfold sylow3_of_card
  exact IsPGroup.toSylow_coe _ _

theorem W_le_of_not_le (hP : BarShape P zc) (N : Subgroup P) [hN : N.Normal] (hNW : ¬ N ≤ W) :
    W ≤ N := by
  classical
  have hWn := hS.normal_W
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hnN, hnW⟩ := IsConcreteLE.not_le_iff_exists.1 hNW
  have hπn : hS.piHom n ≠ 1 := fun h => hnW ((hS.piHom_ker n).1 h)
  have key : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → σ * σ * σ = 1 ∨
      ((σ * (finRotate 3 * σ * (finRotate 3)⁻¹)) * (σ * (finRotate 3 * σ * (finRotate 3)⁻¹)) *
        (σ * (finRotate 3 * σ * (finRotate 3)⁻¹)) = 1 ∧
        σ * (finRotate 3 * σ * (finRotate 3)⁻¹) ≠ 1) := by decide +kernel
  obtain ⟨m, hmN, hm3, hm1⟩ : ∃ m ∈ N, hS.piHom m * hS.piHom m * hS.piHom m = 1 ∧
      hS.piHom m ≠ 1 := by
    rcases key _ hπn with h | ⟨h3, h1⟩
    · exact ⟨n, hnN, h, hπn⟩
    · obtain ⟨c, hc⟩ := hS.piHom_surjective (finRotate 3)
      refine ⟨n * (c * n * c⁻¹), N.mul_mem hnN (hN.conj_mem _ hnN c), ?_, ?_⟩
      · simpa only [map_mul, map_inv, hc] using h3
      · simpa only [map_mul, map_inv, hc] using h1
  have hord3 : orderOf (hS.piHom m) = 3 := by
    apply orderOf_eq_prime _ hm1
    simpa [pow_succ, mul_assoc] using hm3
  have h3m : 3 ∣ orderOf m := hord3 ▸ orderOf_map_dvd hS.piHom m
  have h3N : 3 ∣ Nat.card ↥N := by
    have := orderOf_dvd_natCard (⟨m, hmN⟩ : ↥N)
    rw [Subgroup.orderOf_mk] at this
    exact h3m.trans this
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) 3 h3N
  set g' : P := (x : P) with hg'
  have hg'N : g' ∈ N := x.2
  have hg'3 : orderOf g' = 3 := by rw [hg', Subgroup.orderOf_coe]; exact hx
  have hcard1 : Nat.card ↥(zpowers g') = 3 := by rw [Nat.card_zpowers, hg'3]
  obtain ⟨g, hgA, hg3, hgz⟩ := hS.exists_gen₃
  have hcard2 : Nat.card ↥A₃ = 3 := hS.card_A₃
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq P (sylow3_of_card hP (zpowers g') hcard1)
    (sylow3_of_card hP A₃ hcard2)
  have hA₃N : A₃ ≤ N := by
    intro a ha
    have h1 : a ∈ ((c • sylow3_of_card hP (zpowers g') hcard1 : Sylow 3 P) : Subgroup P) := by
      rw [hc, coe_sylow3_of_card]; exact ha
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, coe_sylow3_of_card,
      Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
    have h2 : (MulAut.conj c)⁻¹ • a = g' ^ k := hk.symm
    have h3 : (MulAut.conj c)⁻¹ • a = c⁻¹ * a * c := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
    have h4 : g' ^ k ∈ N := zpow_mem hg'N k
    have h5 : c⁻¹ * a * c ∈ N := by rw [← h3, h2]; exact h4
    have h6 : a = c * (c⁻¹ * a * c) * c⁻¹ := by group
    rw [h6]
    exact hN.conj_mem _ h5 c
  rw [← hS.comm_eq]
  refine Subgroup.commutator_le.2 fun w hw a ha => ?_
  have haN : a ∈ N := hA₃N ha
  have : ⁅w, a⁆ = (w * a * w⁻¹) * a⁻¹ := rfl
  rw [this]
  exact N.mul_mem (hN.conj_mem _ haN w) (N.inv_mem haN)

theorem card_normal_le_W (hP : BarShape P zc) (N : Subgroup P) [hN : N.Normal] (hNW : N ≤ W)
    (hz : zc ∈ N) : Nat.card ↥N = 2 ∨ Nat.card ↥N = 8 ∨ Nat.card ↥N = 32 := by
  classical
  obtain ⟨g, hgA, hg3, hgz⟩ := hS.exists_gen₃
  let _ : Fintype ↥N := Fintype.ofFinite _
  have hg1 : g * g * g = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg3] at this
    simpa [pow_succ, mul_assoc] using this
  let f : Function.End ↥N := fun n => ⟨g * n * g⁻¹, hN.conj_mem _ n.2 g⟩
  have hf3 : f ^ 3 ^ 1 = 1 := by
    funext n
    apply Subtype.ext
    have h1 : (f ^ 3 : Function.End ↥N) n = f (f (f n)) := rfl
    show ((f ^ 3 : Function.End ↥N) n : P) = n
    rw [h1]
    show g * (g * (g * (n : P) * g⁻¹) * g⁻¹) * g⁻¹ = n
    have : g * (g * (g * (n : P) * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * (n : P) * (g * g * g)⁻¹ := by
      group
    rw [this, hg1]; simp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := ↥N) (f := f) (p := 3) (n := 1) hf3
  have hfix : Fintype.card ↥(Function.fixedPoints f) = 2 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_eq_two_iff]
    have h1 : Function.IsFixedPt f (1 : ↥N) := Subtype.ext (by simp [f])
    have h2 : Function.IsFixedPt f (⟨zc, hz⟩ : ↥N) :=
      Subtype.ext (by
        show g * zc * g⁻¹ = zc
        rw [hP.central g]; simp)
    refine ⟨⟨1, h1⟩, ⟨⟨zc, hz⟩, h2⟩, ?_, ?_⟩
    · intro h
      have := congrArg (fun x : ↥(Function.fixedPoints f) => ((x : ↥N) : P)) h
      exact hP.ne_one (by simpa using this.symm)
    · apply Set.eq_univ_of_forall
      rintro ⟨n, hn⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      have hfn : g * (n : P) * g⁻¹ = n := congrArg Subtype.val hn
      have hcomm : g * (n : P) = (n : P) * g := by
        have := congrArg (· * g) hfn
        simpa [mul_assoc] using this
      have hnW : (n : P) ∈ W := hNW n.2
      have hmem : (n : P) ∈ zpowers zc := by
        apply hS.fix _ hnW
        intro a ha
        rw [hgz] at ha
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        exact (Commute.zpow_left (show Commute g (n : P) from hcomm) k).eq
      rcases (hS.mem_zpowers_zc_iff hP.ne_one hP.sq).1 hmem with h | h
      · left
        apply Subtype.ext; apply Subtype.ext
        simpa using h
      · right
        apply Subtype.ext; apply Subtype.ext
        simpa using h
  rw [hfix] at hmod
  have hdvd : Nat.card ↥N ∣ 2 ^ 5 := by
    have := Subgroup.card_dvd_of_le hNW
    rw [hS.card_W] at this
    simpa using this
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [← Nat.card_eq_fintype_card, hk'] at hmod
  rw [hk']
  interval_cases k <;> first | omega | (exfalso; revert hmod; decide)

end BarShape.Spec

end CFSG.GH74.GLS.IVK.Proofs2.Ivk93M12
