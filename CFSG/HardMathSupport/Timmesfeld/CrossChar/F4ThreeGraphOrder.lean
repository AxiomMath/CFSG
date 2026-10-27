module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidDescent
public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LieType.Ree CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial

set_option linter.unusedSectionVars false

@[expose] def reeF4Order (q : ℕ) : ℕ :=
  q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)

theorem reeF4Order_cofactor {q : ℕ} (hq1 : 1 ≤ q) :
    reeF4Order q = (q + 1) ^ 2 *
      (q ^ 12 * (q - 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)) ∧
    ((q ^ 12 * (q - 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1) : ℕ) :
      ZMod (q + 1)) = ((48 : ℕ) : ZMod (q + 1)) := by
  refine ⟨by rw [reeF4Order]; ring, ?_⟩
  have hq : (q : ZMod (q + 1)) = -1 := by
    have h1 := (ZMod.natCast_eq_zero_iff (q + 1) (q + 1)).2 dvd_rfl
    push_cast at h1
    exact eq_neg_of_add_eq_zero_left h1
  have hq2 : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
  have hq4 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  push_cast [Nat.cast_sub hq1, Nat.cast_sub hq2, Nat.cast_sub hq4]
  rw [hq]
  norm_num

theorem f4Graph_not_cube_dvd {m : ℕ} (hm : 1 ≤ m) :
    ¬ (2 ^ (2 * m + 1) + 1) ^ 3 ∣ reeF4Order (2 ^ (2 * m + 1)) := by
  intro h
  set q := 2 ^ (2 * m + 1) with hqdef
  have hq8 : 8 ≤ q := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hfor, hval⟩ := reeF4Order_cofactor (q := q) (by omega)
  set X := q ^ 12 * (q - 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)
  rw [hfor, show (q + 1) ^ 3 = (q + 1) ^ 2 * (q + 1) by ring] at h
  have hX : q + 1 ∣ X := Nat.dvd_of_mul_dvd_mul_left (by positivity) h
  have h0 := (ZMod.natCast_eq_zero_iff X (q + 1)).2 hX
  rw [hval] at h0
  have h48 : q + 1 ∣ 48 := (ZMod.natCast_eq_zero_iff 48 (q + 1)).1 h0
  have hqeven : q % 2 = 0 := by
    rw [hqdef, pow_succ]
    omega
  have hodd : Nat.Coprime (q + 1) 2 := Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))
  have h16 : Nat.Coprime (q + 1) 16 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact hodd.pow_right 4
  have h3 : q + 1 ∣ 3 := by
    rw [show (48 : ℕ) = 16 * 3 by norm_num] at h48
    exact h16.dvd_of_dvd_mul_left h48
  have := Nat.le_of_dvd (by norm_num) h3
  omega

theorem f4Graph_not_fourth_dvd {m : ℕ} (hm : 1 ≤ m) :
    ¬ (2 ^ (2 * m + 1) + 1) ^ 4 ∣ 3 * reeF4Order (2 ^ (2 * m + 1)) := by
  intro h
  set q := 2 ^ (2 * m + 1) with hqdef
  have hq8 : 8 ≤ q := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨hfor, hval⟩ := reeF4Order_cofactor (q := q) (by omega)
  set X := q ^ 12 * (q - 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) * (q ^ 4 - q ^ 2 + 1)
    with hXdef
  rw [hfor, show (q + 1) ^ 4 = (q + 1) ^ 2 * (q + 1) ^ 2 by ring,
    show 3 * ((q + 1) ^ 2 * X) = (q + 1) ^ 2 * (3 * X) by ring] at h
  have hX2 : (q + 1) ^ 2 ∣ 3 * X := Nat.dvd_of_mul_dvd_mul_left (by positivity) h
  have hX : q + 1 ∣ 3 * X := (Dvd.intro_left _ (pow_two (q + 1)).symm).trans hX2
  have h0 := (ZMod.natCast_eq_zero_iff (3 * X) (q + 1)).2 hX
  have h1 : ((3 * X : ℕ) : ZMod (q + 1)) = ((3 * 48 : ℕ) : ZMod (q + 1)) := by
    rw [Nat.cast_mul, hval, Nat.cast_mul]
  rw [h1] at h0
  have h144 : q + 1 ∣ 3 * 48 := (ZMod.natCast_eq_zero_iff _ (q + 1)).1 h0
  have hqeven : q % 2 = 0 := by
    rw [hqdef, pow_succ]
    omega
  have h16 : Nat.Coprime (q + 1) 16 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    exact (Nat.coprime_two_right.2 (Nat.odd_iff.2 (by omega))).pow_right 4
  have h9 : q + 1 ∣ 9 := by
    rw [show (3 * 48 : ℕ) = 16 * 9 by norm_num] at h144
    exact h16.dvd_of_dvd_mul_left h144
  have h9' := Nat.le_of_dvd (by norm_num) h9
  have hq : q = 8 := by
    rcases (Nat.dvd_prime_pow (show Nat.Prime 3 from Nat.prime_three)).1
      (show q + 1 ∣ 3 ^ 2 by simpa using h9) with ⟨k, hk, hk'⟩
    interval_cases k <;> simp at hk' <;> omega
  rw [hq] at hX2
  revert hX2
  rw [hXdef, hq]
  decide

section Fixed


variable (K : Type) [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  (hFr : ∀ c, Fr c = c ^ Nat.card K) {w : WeylGroup Tag.F4}
  {g0 : ModGL Tag.F4 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
  (hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)
  {p : ℕ} (S : LangSetup Tag.F4 (AlgebraicClosure K) p)
  (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)

include hSD in
theorem f4Graph_card_dvd {m : ℕ} (hK : Nat.card K = 2 ^ (2 * m + 1)) (δ : MulAut S.Γ)
    (hδ2 : δ ^ 2 = 1) (hδo : δ ∉ (MulAut.conj : S.Γ →* MulAut S.Γ).range) :
    Nat.card (δ.toMonoidHom.eqLocus (MonoidHom.id S.Γ)) ∣ reeF4Order (2 ^ (2 * m + 1)) := by
  classical
  have hf : 1 ≤ 2 * m + 1 := by omega
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := langDescent_ofFrobenius (Or.inl rfl) w K hFr hg0C hg0
  rw [← hSD] at hd
  have hι : Function.Injective ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (adjointGroup Tag.F4 K).subtype) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  set e : adjointGroup Tag.F4 K ≃* S.Γ := hd.mulEquiv' hι with he_def
  set φ : MulAut (adjointGroup Tag.F4 K) := ReeTag.F4.finiteExceptionalAut K with hφ
  obtain ⟨-, -, -, -, -, -, hODD⟩ := even_F4_exact_automorphism_normal_form hf K hK
  have hFIX : ∀ g : adjointGroup Tag.F4 K,
      g ∈ ReeTag.F4.finiteReeFixedGroup K m ↔ (φ ^ (2 * m + 1)) g = g :=
    (hODD m rfl).2.2
  set α : MulAut (adjointGroup Tag.F4 K) := (e.trans δ).trans e.symm with hαdef
  have hα2 : α ^ 2 = 1 := by
    ext h
    simp only [hαdef, pow_two, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
      MulAut.one_apply]
    have h1 : δ (δ (e h)) = e h := by
      rw [← MulAut.mul_apply, ← pow_two, hδ2, MulAut.one_apply]
    rw [h1, MulEquiv.symm_apply_apply]
  have hαo : α ∉ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range := by
    rintro ⟨x, hx⟩
    refine hδo ⟨e x, ?_⟩
    ext y
    have h1 := congrArg (fun β : MulAut (adjointGroup Tag.F4 K) => e (β (e.symm y))) hx
    simp only [hαdef, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulAut.conj_apply,
      map_mul, map_inv] at h1
    rw [MulAut.conj_apply, h1]
  have hOUT : ∃ ψ : MulAut (adjointGroup Tag.F4 K), ψ * α * ψ⁻¹ = φ ^ (2 * m + 1) := by
    obtain ⟨ψ, hψ, -⟩ := even_F4_all_outer_involutions_canonical hf K hK α hα2 hαo
    exact ⟨ψ, hψ⟩
  obtain ⟨ψ, hψ⟩ := hOUT
  set Fδ := δ.toMonoidHom.eqLocus (MonoidHom.id S.Γ) with hFδ
  set Φ : S.Γ →* adjointGroup Tag.F4 K := ψ.toMonoidHom.comp e.symm.toMonoidHom with hΦ
  have hΦinj : Function.Injective Φ := ψ.injective.comp e.symm.injective
  have hle : Fδ.map Φ ≤ ReeTag.F4.finiteReeFixedGroup K m := by
    rintro _ ⟨y, hy, rfl⟩
    refine (hFIX _).2 ?_
    have hyF : δ y = y := hy
    have hαy : α (e.symm y) = e.symm y := by
      simp only [hαdef, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, hyF]
    rw [← hψ]
    change ψ (α (ψ⁻¹ (ψ (e.symm y)))) = ψ (e.symm y)
    rw [MulAut.inv_apply_self, hαy]
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective hΦinj] at hdvd
  have hR : Nat.card (ReeTag.F4.finiteReeFixedGroup K m) =
      Nat.card (ReeTag.F4.reeGamma K m) :=
    (Subgroup.card_map_of_injective (adjointGroup ReeTag.F4.tag K).subtype_injective).symm
  have h2 := hdvd.trans (dvd_of_eq hR)
  rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
    m K hK).1] at h2
  unfold reeF4Order
  exact h2

end Fixed

end CFSG.HardMathSupport.Timmesfeld.CrossChar
