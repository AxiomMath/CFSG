module

public import CFSG.GroupTheory.CyclicSylowNormalOddComplement

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2016

open Subgroup

theorem le_map_pPrimeCore (p : ℕ) [Fact p.Prime] {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] (e : X ≃* Y) : (CFSG.pPrimeCore p X).map e.toMonoidHom ≤ CFSG.pPrimeCore p Y := by
  haveI : (CFSG.pPrimeCore p X).Normal := Subgroup.sSup_normal _ fun _ hN => hN.1
  apply CFSG.le_pPrimeCore_of_normal_coprime
  · exact (inferInstance : (CFSG.pPrimeCore p X).Normal).map e.toMonoidHom e.surjective
  · rw [Subgroup.card_map_of_injective e.injective]
    exact CFSG.pPrimeCore_coprime_card

theorem map_pPrimeCore (p : ℕ) [Fact p.Prime] {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] (e : X ≃* Y) :
    (CFSG.pPrimeCore p X).map e.toMonoidHom = CFSG.pPrimeCore p Y := by
  apply le_antisymm (le_map_pPrimeCore p e)
  have h2 := le_map_pPrimeCore p e.symm
  have h3 : ((CFSG.pPrimeCore p Y).map e.symm.toMonoidHom).map e.toMonoidHom =
      CFSG.pPrimeCore p Y := by
    rw [Subgroup.map_map]
    ext y
    simp
  calc CFSG.pPrimeCore p Y = _ := h3.symm
    _ ≤ _ := Subgroup.map_mono (f := e.toMonoidHom) h2

variable {G : Type} [Group G]

@[expose] def conjJ (J : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    ↥J ≃* ↥J where
  toFun j := ⟨g * j * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg j).1 j.2⟩
  invFun j := ⟨g⁻¹ * j * g, by
    have h := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * j * g)).2
    apply h
    simpa [mul_assoc] using j.2⟩
  left_inv j := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv j := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

theorem conjJ_val (J : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (J : Set G)) (j : ↥J) :
    ((conjJ J g hg j : ↥J) : G) = g * j * g⁻¹ := rfl

theorem conjJ_mul (J : Subgroup G) (g h : G) (hg : g ∈ Subgroup.normalizer (J : Set G))
    (hh : h ∈ Subgroup.normalizer (J : Set G)) (j : ↥J) :
    conjJ J (g * h) (Subgroup.mul_mem _ hg hh) j = conjJ J g hg (conjJ J h hh j) := by
  apply Subtype.ext
  simp only [conjJ_val]
  group

theorem conjJ_one (J : Subgroup G) (j : ↥J) :
    conjJ J 1 (Subgroup.one_mem _) j = j := by
  apply Subtype.ext
  rw [conjJ_val]
  simp

variable [Finite G] (p : ℕ) [Fact p.Prime]

@[expose] abbrev PQ (J : Subgroup G) : Type := ↥J ⧸ CFSG.pPrimeCore p ↥J

@[expose] noncomputable def sigmaQ (J : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    PQ p J ≃* PQ p J :=
  QuotientGroup.congr (CFSG.pPrimeCore p ↥J) (CFSG.pPrimeCore p ↥J) (conjJ J g hg)
    (map_pPrimeCore p (conjJ J g hg))

theorem sigmaQ_mk (J : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (J : Set G))
    (j : ↥J) :
    sigmaQ p J g hg (QuotientGroup.mk j) = QuotientGroup.mk (conjJ J g hg j) :=
  QuotientGroup.congr_mk _ _ _ _ _

theorem sigmaQ_one (J : Subgroup G) : sigmaQ p J 1 (Subgroup.one_mem _) = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H j => simp only [sigmaQ_mk, conjJ_one, MulAut.one_apply]

theorem sigmaQ_mul (J : Subgroup G) (g h : G) (hg : g ∈ Subgroup.normalizer (J : Set G))
    (hh : h ∈ Subgroup.normalizer (J : Set G)) :
    sigmaQ p J (g * h) (Subgroup.mul_mem _ hg hh) = sigmaQ p J g hg * sigmaQ p J h hh := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H j => rw [MulAut.mul_apply, sigmaQ_mk, sigmaQ_mk, sigmaQ_mk, conjJ_mul]

@[expose] noncomputable def sigmaHom (J : Subgroup G) :
    Subgroup.normalizer (J : Set G) →* MulAut (PQ p J) where
  toFun g := sigmaQ p J g.1 g.2
  map_one' := sigmaQ_one p J
  map_mul' a b := sigmaQ_mul p J a.1 b.1 a.2 b.2

section Sylow2

variable {P : Type} [Group P] [Finite P]

theorem sylow_two_normal_of_central (Z : Subgroup P) (hZ : Z ≤ Subgroup.center P) {k : ℕ}
    (hk : Nat.card (P ⧸ Z) = 2 ^ k) (R : Sylow 2 P) : (R : Subgroup P).Normal := by
  have hZn : Z ≤ Subgroup.normalizer (R : Set P) := by
    intro z hz
    show z ∈ Subgroup.normalizer ((R : Subgroup P) : Set P)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc := Subgroup.mem_center_iff.1 (hZ hz) h
    have hzh : z * h * z⁻¹ = h := by
      rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [hzh]
  have h2 : (Subgroup.normalizer (R : Set P)).index ∣ 2 ^ k := by
    rw [← hk]
    exact Subgroup.index_dvd_of_le hZn
  have h1 : Nat.card (Sylow 2 P) = (Subgroup.normalizer (R : Set P)).index :=
    Sylow.card_eq_index_normalizer R
  have h3 : Nat.card (Sylow 2 P) ≡ 1 [MOD 2] := card_sylow_modEq_one 2 P
  have hodd : Nat.Coprime (Subgroup.normalizer (R : Set P)).index 2 := by
    rw [← h1]
    rw [Nat.ModEq] at h3
    apply Nat.Coprime.symm
    apply (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
    intro hd
    have := Nat.mod_eq_zero_of_dvd hd
    omega
  have hidx : (Subgroup.normalizer (R : Set P)).index = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hodd) h2
  exact Subgroup.normalizer_eq_top_iff.1 (Subgroup.index_eq_one.1 hidx)

@[expose] def restrictEquiv {Q : Type} [Group Q] (P : Subgroup Q) (α : Q ≃* Q)
    (h1 : ∀ p ∈ P, α p ∈ P) (h2 : ∀ p ∈ P, α.symm p ∈ P) : ↥P ≃* ↥P where
  toFun p := ⟨α p, h1 p p.2⟩
  invFun p := ⟨α.symm p, h2 p p.2⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv p := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp

theorem map_normal_sylow_eq {Q : Type} [Group Q] [Finite Q] (P : Subgroup Q) (R : Sylow 2 ↥P)
    (hR : (R : Subgroup ↥P).Normal) (α : Q ≃* Q) (h1 : ∀ p ∈ P, α p ∈ P)
    (h2 : ∀ p ∈ P, α.symm p ∈ P) :
    ((R : Subgroup ↥P).map (restrictEquiv P α h1 h2).toMonoidHom).map P.subtype =
      (R : Subgroup ↥P).map P.subtype := by
  have hc : (R : Subgroup ↥P).Characteristic := Sylow.characteristic_of_normal R hR
  have hm := Subgroup.characteristic_iff_map_eq.1 hc (restrictEquiv P α h1 h2)
  rw [hm]

end Sylow2

theorem exists_fixed_of_pow_three {X : Type} [Finite X] (f : Equiv.Perm X) (hf : f ^ 3 = 1)
    (hc : Nat.Coprime 3 (Nat.card X)) : ∃ x, f x = x := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf f ∣ 3 := orderOf_dvd_of_pow_eq_one hf
  have hT3p : IsPGroup 3 (Subgroup.zpowers f) := by
    rw [IsPGroup.iff_card]
    rcases (Nat.dvd_prime Nat.prime_three).1 hord with h | h
    · exact ⟨0, by rw [Nat.card_zpowers, h]; norm_num⟩
    · exact ⟨1, by rw [Nat.card_zpowers, h]; norm_num⟩
  have hmod := IsPGroup.card_modEq_card_fixedPoints hT3p X
  have hne : (MulAction.fixedPoints (Subgroup.zpowers f) X).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : Nat.card (MulAction.fixedPoints (Subgroup.zpowers f) X) = 0 := by
      rw [hne]
      simp
    rw [h0] at hmod
    have h3 : 3 ∣ Nat.card X := (Nat.modEq_zero_iff_dvd).1 hmod
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hc h3
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, ?_⟩
  have := hx ⟨f, Subgroup.mem_zpowers f⟩
  simpa using this

theorem exists_two_sup_eq_top {M : Type} [Group M] [Finite M] (N : Subgroup M) [N.Normal] {k : ℕ}
    (hk : Nat.card (M ⧸ N) = 2 ^ k) : ∃ W : Subgroup M, IsPGroup 2 W ∧ W ⊔ N = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨W₁⟩ : Nonempty (Sylow 2 M) := inferInstance
  refine ⟨(W₁ : Subgroup M), W₁.isPGroup', ?_⟩
  have h2 : ((W₁ : Subgroup M) ⊔ N).index ∣ N.index := Subgroup.index_dvd_of_le le_sup_right
  have h3 : ((W₁ : Subgroup M) ⊔ N).index ∣ (W₁ : Subgroup M).index :=
    Subgroup.index_dvd_of_le le_sup_left
  have hcop : Nat.Coprime ((W₁ : Subgroup M) ⊔ N).index 2 := by
    apply Nat.Coprime.symm
    apply (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2
    intro hd
    exact W₁.not_dvd_index (hd.trans h3)
  have hN : N.index = 2 ^ k := by
    rw [← hk]
    rfl
  have hone : ((W₁ : Subgroup M) ⊔ N).index = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) (hN ▸ h2)
  exact Subgroup.index_eq_one.1 hone

theorem exists_fixed_in_fiber (J : Subgroup G) (y : G) (hy : y ∈ Subgroup.normalizer (J : Set G))
    (hy3 : y ^ 3 = 1) (j : ↥J)
    (hfix : sigmaQ 3 J y hy (QuotientGroup.mk j) = QuotientGroup.mk j) :
    ∃ x : ↥J, (QuotientGroup.mk x : PQ 3 J) = QuotientGroup.mk j ∧ conjJ J y hy x = x := by
  classical
  let S := {x : ↥J // (QuotientGroup.mk x : PQ 3 J) = QuotientGroup.mk j}
  have hS : ∀ x : S, (QuotientGroup.mk (conjJ J y hy x.1) : PQ 3 J) = QuotientGroup.mk j := by
    intro x
    rw [← sigmaQ_mk, x.2, hfix]
  let F : S → S := fun x => ⟨conjJ J y hy x.1, hS x⟩
  have hFinj : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact (conjJ J y hy).injective this
  let Fe : Equiv.Perm S := Equiv.ofBijective F (Finite.injective_iff_bijective.1 hFinj)
  have hyy : y * y * y = 1 := by rw [← pow_three']; exact hy3
  have key : ∀ z : ↥J, conjJ J y hy (conjJ J y hy (conjJ J y hy z)) = z := by
    intro z
    apply Subtype.ext
    simp only [conjJ_val]
    have : y * (y * (y * (z : G) * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * (z : G) * (y * y * y)⁻¹ := by
      group
    rw [this, hyy]
    simp
  have hFe3 : Fe ^ 3 = 1 := by
    ext x
    rw [pow_three', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    simp only [Fe, Equiv.ofBijective_apply, F]
    exact congrArg (fun z : ↥J => (z : G)) (key x.1)
  have hcard : Nat.card S = Nat.card (CFSG.pPrimeCore 3 ↥J) := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨j⁻¹ * x.1, QuotientGroup.eq.1 x.2.symm⟩
        invFun := fun n => ⟨j * n.1, by
          apply QuotientGroup.eq.2
          have := (CFSG.pPrimeCore 3 ↥J).inv_mem n.2
          simpa [mul_assoc] using this⟩
        left_inv := fun x => by
          apply Subtype.ext
          simp
        right_inv := fun n => by
          apply Subtype.ext
          simp }
  have hc : Nat.Coprime 3 (Nat.card S) := by
    rw [hcard]
    exact CFSG.pPrimeCore_coprime_card
  obtain ⟨x, hx⟩ := exists_fixed_of_pow_three Fe hFe3 hc
  have hx' : conjJ J y hy x.1 = x.1 := by
    have := congrArg Subtype.val hx
    simpa [Fe, Equiv.ofBijective_apply, F] using this
  exact ⟨x.1, x.2, hx'⟩

end CFSG.LocalAnalysis.GLTheoremA.I2016
