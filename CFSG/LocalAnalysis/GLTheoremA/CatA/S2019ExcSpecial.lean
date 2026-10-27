module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ExcHyper
import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddCore
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcArith

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

private noncomputable def resHomW {W : Type} [CommGroup W] {R : Type*} [Group R]
    (ψ : R →* MulAut W) (V : Subgroup W) (hV : ∀ r, ∀ v ∈ V, ψ r v ∈ V) : R →* MulAut V where
  toFun r :=
    { toFun := fun v => ⟨ψ r (v : W), hV r v v.2⟩
      invFun := fun v => ⟨ψ r⁻¹ (v : W), hV r⁻¹ v v.2⟩
      left_inv := fun v => Subtype.ext (by
        change ψ r⁻¹ (ψ r (v : W)) = v
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply])
      right_inv := fun v => Subtype.ext (by
        change ψ r (ψ r⁻¹ (v : W)) = v
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply])
      map_mul' := fun a b => Subtype.ext (map_mul (ψ r) (a : W) (b : W)) }
  map_one' := by
    ext v
    change ψ 1 (v : W) = v
    rw [map_one, MulAut.one_apply]
  map_mul' := fun a b => by
    ext v
    change ψ (a * b) (v : W) = ψ a (ψ b (v : W))
    rw [map_mul, MulAut.mul_apply]

private theorem zmod_five_pow (t : ℕ) (h2 : 2 ≤ t) (h3 : t ≤ 3) : (2 : ZMod 5) ^ t ≠ 1 := by
  interval_cases t <;> decide

private theorem zmod_seven_pow (t : ℕ) (h2 : 2 ≤ t) (h3 : t ≤ 2) : (2 : ZMod 7) ^ t ≠ 1 := by
  interval_cases t
  decide

private theorem eq_three_of_pow_mul_le {q r : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2) (hr : 1 ≤ r)
    (h : q ^ r * orderOf (2 : ZMod q) ≤ 17) : q = 3 ∧ r = 1 := by
  have ht := CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.two_le_orderOf_two_zmod (p := q) hq2
  have hq3 : 3 ≤ q := by have := hq.out.two_le; omega
  have h8 : q ^ r ≤ 8 := by nlinarith
  have hr1 : r = 1 := by
    by_contra hr1
    have : q ^ 2 ≤ q ^ r := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  subst hr1
  rw [pow_one] at h8 h
  refine ⟨?_, rfl⟩
  have hpow := pow_orderOf_eq_one (2 : ZMod q)
  generalize orderOf (2 : ZMod q) = t at ht h hpow
  have h4 : q ≠ 4 := by
    rintro rfl
    exact absurd hq.out (by norm_num)
  have h6 : q ≠ 6 := by
    rintro rfl
    exact absurd hq.out (by norm_num)
  have h8' : q ≠ 8 := by
    rintro rfl
    exact absurd hq.out (by norm_num)
  rcases (show q = 3 ∨ q = 5 ∨ q = 7 by omega) with h3 | h5 | h7
  · exact h3
  · subst h5
    exact absurd hpow (zmod_five_pow t ht (by omega))
  · subst h7
    exact absurd hpow (zmod_seven_pow t ht (by omega))

theorem eq_three_of_special {J : Type} [Group J] [Finite J] {Y : Type} [Group Y]
    (e : J ⧸ Subgroup.center J ≃* Y) {q : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hZ : ¬ q ∣ Nat.card (Subgroup.center J)) {R : Subgroup Y} (hRq : IsPGroup q R)
    (hRexp : ∀ r ∈ R, r ^ q = 1) {Q : ℕ} (hRcard : Nat.card R = Q ^ 3)
    (hZR : Nat.card (Subgroup.center ↥R) = Q) (hQ : 1 < Q)
    (hext : ∀ (Z : Subgroup ↥R) [Z.Normal], Z ≤ Subgroup.center ↥R →
      Z.relIndex (Subgroup.center ↥R) = q → CFSG.IsExtraspecialPGroup q (↥R ⧸ Z))
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1) (hW17 : Nat.card W ≤ 2 ^ 17)
    (ρ : J →* MulAut W) (hρ : ∀ x : J, x ^ q = 1 → ρ x = 1 → x ∈ Subgroup.center J) :
    q = 3 ∧ Q = 3 := by
  classical
  haveI : Finite (MulAut W) := Finite.of_injective (fun f : MulAut W => (f : W → W))
    (fun f g h => MulEquiv.ext (congrFun h))
  haveI : Finite Y := Finite.of_equiv _ e.toEquiv
  have hqp : q.Prime := hq.out
  have hqodd : Odd q := hqp.odd_of_ne_two hq2
  let π : J →* Y := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ x, π x = 1 ↔ x ∈ Subgroup.center J := by
    intro x
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hZq : ∀ x ∈ Subgroup.center J, ∀ k : ℕ, x ^ q ^ k = 1 → x = 1 := by
    intro x hx k hk
    have h1 : orderOf x ∣ q ^ k := orderOf_dvd_of_pow_eq_one hk
    have h2 : orderOf x ∣ Nat.card (Subgroup.center J) := by
      have := orderOf_dvd_natCard (⟨x, hx⟩ : Subgroup.center J)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (q ^ k) (Nat.card (Subgroup.center J)) :=
      Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hqp).2 hZ)
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  obtain ⟨P, hPq, hPR⟩ := CFSG.RankThree.PartTwo.Sec4.L34Odd.exists_isPGroup_map_eq q π R hRq
    (by rw [MonoidHom.range_eq_top.2 hπ]; exact le_top)
  have hPinj : ∀ x ∈ P, π x = 1 → x = 1 := by
    intro x hx h1
    obtain ⟨k, hk⟩ := hPq ⟨x, hx⟩
    exact hZq x ((hker x).1 h1) k (by simpa using congrArg Subtype.val hk)
  let πP : ↥P →* ↥R := (π.comp P.subtype).codRestrict R fun x => by
    rw [← hPR]
    exact Subgroup.mem_map_of_mem π x.2
  have hπPinj : Function.Injective πP := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hPinj x x.2 (congrArg Subtype.val hx))
  have hπPsurj : Function.Surjective πP := by
    rintro ⟨y, hy⟩
    rw [← hPR] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  let σ : ↥R ≃* ↥P := (MulEquiv.ofBijective πP ⟨hπPinj, hπPsurj⟩).symm
  let ψ : ↥R →* MulAut W := ρ.comp (P.subtype.comp σ.toMonoidHom)
  have hRexp' : ∀ r : ↥R, r ^ q = 1 := fun r => Subtype.ext (by simpa using hRexp r r.2)
  have hψ1 : ∀ r, ψ r = 1 → r = 1 := by
    intro r hr
    have hσq : ((σ r : P) : J) ^ q = 1 := by
      have h1 : σ (r ^ q) = 1 := by rw [hRexp' r, map_one]
      rw [map_pow] at h1
      simpa using congrArg Subtype.val h1
    have h1 := hPinj _ (σ r).2 ((hker _).2 (hρ _ hσq hr))
    have : σ r = 1 := Subtype.ext h1
    exact σ.injective (this.trans (map_one σ).symm)
  have hψinj : Function.Injective ψ := (injective_iff_map_eq_one ψ).2 hψ1
  set A : Subgroup (MulAut W) := (Subgroup.center ↥R).map ψ with hAdef
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, -, rfl⟩
    rw [← map_mul, ← map_mul, ← Subgroup.mem_center_iff.1 hx y]
  have hAq : ∀ a ∈ A, a ^ q = 1 := by
    rintro _ ⟨x, -, rfl⟩
    rw [← map_pow, hRexp' x, map_one]
  have hcardA : Nat.card A = Q := by rw [Subgroup.card_map_of_injective hψinj, hZR]
  have hA1 : A ≠ ⊥ := by
    intro hbot
    rw [← Subgroup.card_eq_one, hcardA] at hbot
    omega
  obtain ⟨N, hNA, hN, hne⟩ := exists_range_eW_ne_bot hW hq2 hAc hAq hA1
  set Z : Subgroup ↥R := N.comap ψ ⊓ Subgroup.center ↥R with hZdef
  have hZc : Z ≤ Subgroup.center ↥R := inf_le_right
  haveI hZn : Z.Normal := Subgroup.normal_of_le_center hZc
  have hZmap : Z.map ψ = N := by
    apply le_antisymm
    · rintro _ ⟨x, ⟨hxN, -⟩, rfl⟩
      exact hxN
    · intro n hn
      obtain ⟨x, hx, rfl⟩ := hNA hn
      exact ⟨x, ⟨hn, hx⟩, rfl⟩
  have hcardZ : Nat.card Z = Nat.card N := by
    rw [← hZmap, Subgroup.card_map_of_injective hψinj]
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hrel : Z.relIndex (Subgroup.center ↥R) = q := by
    have h1 : Z.relIndex (Subgroup.center ↥R) * Nat.card Z = Nat.card (Subgroup.center ↥R) := by
      rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZc).toEquiv,
        Subgroup.index_mul_card]
    rw [hZR, ← hcardA, hN, ← hcardZ] at h1
    exact Nat.eq_of_mul_eq_mul_right hZpos h1
  have hE := hext Z hZc hrel
  obtain ⟨r, hr⟩ := (hRq.to_subgroup (Subgroup.center ↥R)).exists_card_eq
  rw [hZR] at hr
  have hr1 : 1 ≤ r := by
    by_contra h0
    rw [show r = 0 by omega, pow_zero] at hr
    omega
  have hcardZ' : Nat.card Z = q ^ (r - 1) := by
    have h1 : q * Nat.card Z = q * q ^ (r - 1) := by
      rw [hcardZ, ← hN, hcardA, hr, ← pow_succ']
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left hqp.pos h1
  have hcardE : Nat.card (↥R ⧸ Z) = q ^ (1 + 2 * r) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
    rw [hRcard, hr, hcardZ', ← pow_mul,
      show r * 3 = (1 + 2 * r) + (r - 1) by omega, pow_add] at h1
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos hqp.pos _) h1).symm
  have hexpE : ∀ g : ↥R ⧸ Z, g ^ q = 1 := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_pow, hRexp' x, QuotientGroup.mk_one]
  set V : Subgroup W := (eW N A).range with hVdef
  have hcommA : ∀ x : ↥R, ∀ a ∈ A, ψ x * a = a * ψ x := by
    rintro x _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hy x]
  have hV : ∀ x : ↥R, ∀ v ∈ V, ψ x v ∈ V := by
    rintro x _ ⟨u, rfl⟩
    refine ⟨ψ x u, ?_⟩
    rw [eW_apply, eW_apply, map_mul, apply_avgW_of_comm fun n hn => hcommA x n (hNA hn),
      apply_avgW_of_comm fun a ha => hcommA x a ha]
  have hfixN : ∀ n ∈ N, ∀ v ∈ V, n v = v := by
    rintro n hn _ ⟨u, rfl⟩
    rw [eW_apply, map_mul, apply_avgW hn, apply_avgW (hNA hn)]
  let φ₀ : ↥R →* MulAut V := resHomW ψ V hV
  have hZker : Z ≤ φ₀.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    ext v
    change ψ z (v : W) = v
    exact hfixN _ hz.1 v v.2
  let φ : ↥R ⧸ Z →* MulAut V := QuotientGroup.lift Z φ₀ hZker
  obtain ⟨z₀, hz₀c, hz₀Z⟩ : ∃ z₀ ∈ Subgroup.center ↥R, z₀ ∉ Z := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (show Subgroup.center ↥R ≤ Z from hcon)
    rw [hZR, ← hcardA, hN, ← hcardZ] at hle
    nlinarith [hqp.two_le]
  have hz : (z₀ : ↥R ⧸ Z) ∈ Subgroup.center (↥R ⧸ Z) := by
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H x => rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hz₀c x]
  have hφz : φ (z₀ : ↥R ⧸ Z) ≠ 1 := by
    intro h1
    have h2 : φ₀ z₀ = 1 := by rwa [QuotientGroup.lift_mk] at h1
    have hψz₀A : ψ z₀ ∈ A := ⟨z₀, hz₀c, rfl⟩
    have hψz₀N : ψ z₀ ∉ N := fun h => hz₀Z ⟨h, hz₀c⟩
    obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    refine hv1 (Subtype.ext ?_)
    refine eq_one_of_mem_range_eW hW hqodd hAq hNA hN hψz₀A hψz₀N v.2 ?_
    have h3 := congrArg (fun f : MulAut V => ((f v : V) : W)) h2
    exact h3
  have hVW : ∀ w : V, w * w = 1 := fun w => Subtype.ext (hW _)
  have hbound := two_pow_le_card_of_extraspecial hqodd hE hexpE hcardE hVW φ hz hφz
  have hVcard : Nat.card V ≤ Nat.card W := Subgroup.card_le_card_group V
  have h17 : q ^ r * orderOf (2 : ZMod q) ≤ 17 :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 ((hbound.trans hVcard).trans hW17)
  obtain ⟨h3, rfl⟩ := eq_three_of_pow_mul_le hq2 hr1 h17
  exact ⟨h3, by rw [hr, h3, pow_one]⟩

end CFSG.LocalAnalysis.GLTheoremA.S2019
