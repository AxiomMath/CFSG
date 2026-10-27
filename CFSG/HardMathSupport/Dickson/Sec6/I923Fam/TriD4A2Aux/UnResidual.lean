module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddMinusPolar
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.UnGlue
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.UnLang
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.PolarityData
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.RankOne
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.Fold
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4A2Aux.SimpleCore

public section

open scoped Pointwise

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.LieType.Steinberg Multiplicative
  CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem count_bound {q m : ℕ} (hq : 2 ≤ q) (hm : m ∣ q ^ 2 - 1) :
    (q ^ 3 * m) * (1 + q ^ 3) ≤ q ^ 3 * q ^ 5 := by
  have h4 : 4 ≤ q ^ 2 := by nlinarith
  have hm' : m ≤ q ^ 2 - 1 := Nat.le_of_dvd (by omega) hm
  obtain ⟨r, hr⟩ : ∃ r, q ^ 2 = r + 1 := ⟨q ^ 2 - 1, by omega⟩
  have hq23 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hrr : r ≤ q ^ 3 := by omega
  have hm'' : m ≤ r := by omega
  have h1 : m * (1 + q ^ 3) ≤ q ^ 5 := by
    calc m * (1 + q ^ 3) ≤ r * (1 + q ^ 3) := Nat.mul_le_mul_right _ hm''
      _ = r + r * q ^ 3 := by ring
      _ ≤ q ^ 3 + r * q ^ 3 := Nat.add_le_add_right hrr _
      _ = q ^ 3 * (r + 1) := by ring
      _ = q ^ 5 := by rw [← hr]; ring
  calc (q ^ 3 * m) * (1 + q ^ 3) = q ^ 3 * (m * (1 + q ^ 3)) := by ring
    _ ≤ q ^ 3 * q ^ 5 := Nat.mul_le_mul_left _ h1

theorem un_residual {p f : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hf : 0 < f)
    {X : Type*} [Group X] [Finite X] (D : RankTwoSystem X 3) (hBsolv : Group.IsSolvable ↥D.B)
    (τ e : X ≃* X) (hτ : D.IsOpposition τ) (hτe : ∀ y, τ (τ y) = e y)
    (he : ∀ b ∈ D.B, e b ∈ D.B) (hτ4 : ∀ y, τ (τ (τ (τ y))) = y)
    {k : Type} [Field k] [Finite k] [CharP k p] (hk : Nat.card k = (p ^ f) ^ 4)
    (ε : k ≃+* k) (hε : ∀ a, ε a = a ^ (p ^ f))
    (ρ : Matrix.SpecialLinearGroup (Fin 2) k →* X) (hρinj : Function.Injective ρ) (κ : kˣ)
    (hu : ∀ a, τ (ρ (sl2Upper a)) = ρ (sl2Lower ((κ : k) * ε a)))
    (hl : ∀ a, τ (ρ (sl2Lower a)) = ρ (sl2Upper (((κ⁻¹ : kˣ) : k) * ε a)))
    (hρ2 : ∀ a, ρ (sl2Upper a) ∈ D.root 2) (hρ2' : ∀ y ∈ D.root 2, ∃ a, y = ρ (sl2Upper a))
    (hρm2 : ∀ a, ρ (sl2Lower a) ∈ D.root (-2))
    (hρN : ∃ m₀ : D.N, (m₀ : X) = ρ unSL2W ∧ (m₀ : D.Weyl) = D.w₀)
    (hρH : ∀ u : kˣ, ρ (unSL2Diag u) ∈ D.B ⊓ D.N)
    (x₁ : Multiplicative k →* X) (hx₁inj : Function.Injective x₁)
    (hx₁ : ∀ a, x₁ a ∈ D.root 1) (hx₁s : ∀ y ∈ D.root 1, ∃ a, y = x₁ a)
    (hx₁torus : ∀ h ∈ D.B ⊓ D.N, ∃ χ : kˣ,
      ∀ a : k, h * x₁ (ofAdd a) * h⁻¹ = x₁ (ofAdd ((χ : k) * a)))
    (hx₁e : ∀ a : k, e (x₁ (ofAdd a)) = x₁ (ofAdd (ε (ε a))))
    (hab₁ : ∀ a ∈ D.root 1, ∀ b ∈ D.root 1, a * b = b * a)
    (hab₃ : ∀ a ∈ D.root 3, ∀ b ∈ D.root 3, a * b = b * a)
    (hTor : ∀ h ∈ D.B ⊓ D.N, ∀ y ∈ D.root 1, y ≠ 1 → ∀ z ∈ D.root 3, z ≠ 1 →
      h * y = y * h → h * z = z * h → h = 1)
    (hĉ : ∃ c ∈ D.B ⊓ D.N, τ c = c ∧ c * c = 1 ∧ ∀ y ∈ D.root (-2), c * y * c⁻¹ = y⁻¹) :
    SimpleCore ↥(foldFix τ) ((p ^ f) ^ 3) ((p ^ f) ^ 5) := by
  have hpp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hq5 : 5 ≤ p ^ f := le_trans hp5 (Nat.le_self_pow hf.ne' p)
  obtain ⟨m, hm, hcardτ⟩ := un_final_card hp2 hf D τ e hτ hτe he hτ4 hk ε hε ρ hρinj κ hu hl hρ2
    hρ2' hρm2 hρN hρH x₁ hx₁inj hx₁ hx₁s hx₁torus hx₁e hab₁ hab₃ hTor hĉ
  obtain ⟨t, ht⟩ := un_norm_solution hf hk ε hε κ (un_norm_eq ρ hρinj τ hτ4 ε κ hu hl)
  have hg : (ρ (sl2Lower (t : k)))⁻¹ * τ (ρ (sl2Lower (t : k))) *
      ((D.lift D.w₀ : D.N) : X) ∈ D.B := un_adapted_mem_B D ρ τ ε κ hl hρ2 hρN hρH t ht
  have hθpol := hτ.isPolarity hg
  have hθapp := un_theta_apply τ (ρ (sl2Lower (t : k)))
  have hθ4 := un_theta_four τ hτ4 (ρ (sl2Lower (t : k)))
  obtain ⟨l₂, hθ₂⟩ := un_theta_x2 ρ τ ε κ hu hl t ht
  obtain ⟨ν, hθ₁₁⟩ := un_theta_sq_x1 D τ e hτ hτe he ε x₁ hx₁ hx₁torus hx₁e hab₁ hab₃ hg
  have hθ₁ := fun y (hy : y ∈ D.root 1) => hτ.theta_root₁ hg hy
  have hθ₃ := fun z (hz : z ∈ D.root 3) => hτ.theta_root₃ hg hz
  have hθ₂m := fun b (hb : b ∈ D.root 2) => hτ.theta_root₂ hg hb
  have hU1 : D.root 1 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU2 : D.root 2 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hU3 : D.root 3 ≤ D.U := D.root_le_U (by norm_num) (by norm_num)
  have hκt : (κ : k) = (t : k) * ε t := by
    have hκ0 : (κ : k) ≠ 0 := κ.ne_zero
    have h1 : ((κ⁻¹ : kˣ) : k) = (κ : k)⁻¹ := by simp
    rw [h1] at ht
    field_simp at ht
    linear_combination -ht
  set x : X := ρ (sl2Lower (t : k)) with hxdef
  set θ : X ≃* X := τ.trans (MulAut.conj (x⁻¹ * τ x)) with hθdef
  have hx₂inj : Function.Injective (ρ.comp (unSL2UpperHom k)) := fun a b h =>
    Multiplicative.toAdd.injective
      (@un_sl2Upper_injective k _ (toAdd a) (toAdd b) (hρinj h))
  obtain ⟨hcard, hfix⟩ := un_heis_fixed D hp2 hf hk ε hε x₁ (ρ.comp (unSL2UpperHom k)) hx₁inj
    hx₂inj hx₁ (fun a => hρ2 _) hx₁s
    (fun y hy => by
      obtain ⟨a, ha⟩ := hρ2' y hy
      exact ⟨ofAdd a, ha⟩) hab₁ hab₃ θ hθpol.mem_U hθ4 l₂ ν hθ₂ hθ₁ hθ₃ hθ₁₁
  have hKC := un_hKC D hab₁ hab₃ hTor θ hfix
  obtain ⟨c, hcH, hcτ, -, hcinv⟩ := hĉ
  have hc₀ := un_c0_mem_dc D ρ hρ2 hρm2 hρN hρH (un_two_ne_zero hp2) hcH hcinv t
  have hc₀f : θ (x⁻¹ * c * x) = x⁻¹ * c * x := by
    rw [hθapp]
    have e' : x * (x⁻¹ * c * x) * x⁻¹ = c := by group
    rw [e', hcτ]
  have hdata := polarity_rankOne_data hθpol hc₀ hc₀f hKC
  have hBsolv' : Group.IsSolvable ↥(polB D θ) := by
    haveI := hBsolv
    let f₀ : ↥(polB D θ) →* ↥D.B :=
      ((foldFix θ).subtype.comp (polB D θ).subtype).codRestrict D.B
        fun g => (mem_polB g.1).1 g.2
    exact solvable_of_solvable_injective (f := f₀) fun a b hab =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ↥D.B => (z : X)) hab))
  have h2 : (2 : k) ≠ 0 := un_two_ne_zero hp2
  have h3 : (3 : k) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : k) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((CharP.cast_eq_zero_iff k p 3).1 h')
    omega
  obtain ⟨w, hw0, hεw⟩ := exists_neg_frob (q := p ^ f) ((hpp.odd_of_ne_two hp2).pow)
    (by omega) hk ε hε
  let F : Subfield k := ε.toRingHom.eqLocusField (RingHom.id k)
  have hF : ∀ a ∈ F, ε a = a := fun a ha => ha
  have hτρ := tau_rho_eq ρ τ ε κ hu hl
  let Ψ : Matrix.SpecialLinearGroup (Fin 2) F →* ↥(foldFix θ) :=
    (ρ.comp (phiHom F t.ne_zero hw0 h2)).codRestrict (foldFix θ) (fun N => by
      rw [mem_foldFix]
      exact theta_rho_fixed ρ τ ε κ hτρ (t : k) (tauHat_phi ε hκt hw0 hεw h2 F hF N))
  obtain ⟨S, hSn, hSperf, hSsolv⟩ := exists_residual ↥(foldFix θ)
  haveI := hSn
  have hperfΨ : ⁅Ψ.range, Ψ.range⁆ = Ψ.range := by
    haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
      CFSG.LinearGroups.special_linear_dimension_two_perfect
        (exists_finset_card_four_subfield hp5 F)
    haveI : Group.IsPerfect Ψ.range := Group.IsPerfect.range _
    exact Subgroup.isPerfect_iff.1 inferInstance
  have hΨS : Ψ.range ≤ S := perfect_le_of_solvable_quotient hperfΨ S hSsolv
  let a : ↥F := ⟨2, show ε 2 = 2 from map_ofNat ε 2⟩
  have ha0 : a ≠ 0 := fun h' => h2 (congrArg Subtype.val h')
  have ha2 : (a : k) = 2 := rfl
  have ha0' : (a : k) ≠ 0 := fun h' => ha0 (Subtype.ext h')
  let b₀ : ↥(foldFix θ) := Ψ (diagSL F a ha0)
  have hb₀S : b₀ ∈ S := hΨS ⟨_, rfl⟩
  let u : kˣ := Units.mk0 (a : k) ha0'
  let s : k := (((a : k) - (a : k)⁻¹) / (2 * (t : k))) * (a : k)⁻¹
  have hΦeq : phiHom F t.ne_zero hw0 h2 (diagSL F a ha0) = unSL2Diag u * sl2Upper s :=
    sl2_eq_diag_mul_upper ha0' (coe_phiHom_diagSL F t.ne_zero hw0 h2 a ha0)
  have hb₀val : (b₀ : X) = ρ (unSL2Diag u) * ρ (sl2Upper s) := by
    show ρ (phiHom F t.ne_zero hw0 h2 (diagSL F a ha0)) = _
    rw [hΦeq, map_mul]
  have hh : ρ (unSL2Diag u) ∈ D.B ⊓ D.N := hρH u
  have heU : ρ (sl2Upper s) ∈ D.U := hU2 (hρ2 s)
  have hu2 : (u : k) ^ 2 ≠ 1 := by
    intro h'
    apply h3
    have h'' : (2 : k) ^ 2 = 1 := by rw [← ha2]; exact h'
    linear_combination h''
  have hh1 : ρ (unSL2Diag u) ≠ 1 := by
    intro h'
    have h1 : unSL2Diag u = 1 := hρinj (h'.trans (map_one ρ).symm)
    have h4 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
      (M : Matrix (Fin 2) (Fin 2) k) 0 0) h1
    simp only [coe_unSL2Diag, Matrix.SpecialLinearGroup.coe_one] at h4
    simp at h4
    apply hu2
    rw [h4]
    norm_num
  have hmid : ∀ b ∈ D.root 2, (ρ (unSL2Diag u) * ρ (sl2Upper s)) * b *
      (ρ (unSL2Diag u) * ρ (sl2Upper s))⁻¹ = b → b = 1 := by
    intro b hb hbc
    obtain ⟨a', rfl⟩ := hρ2' b hb
    exact torus_upper_fixed ρ hρinj u s a' hu2 hbc
  have hb₀B : (b₀ : X) ∈ D.B := by
    rw [hb₀val]
    exact D.B.mul_mem hh.1 (D.U_le_B heU)
  have hb₀polB : b₀ ∈ polB D θ := (mem_polB b₀).2 hb₀B
  have hUS : polU D θ ≤ S := by
    refine le_of_normal_of_centralizer_trivial hb₀S
      (fun g hg => hdata.2.1 b₀ hb₀polB g hg) ?_
    intro g hg hcomm
    apply Subtype.ext
    have hgU : (g : X) ∈ D.U := (mem_polU g).1 hg
    have hgθ : θ (g : X) = g := mem_foldFix.1 g.2
    have hcomm' : (ρ (unSL2Diag u) * ρ (sl2Upper s)) * (g : X) =
        (g : X) * (ρ (unSL2Diag u) * ρ (sl2Upper s)) := by
      rw [← hb₀val]
      exact congrArg Subtype.val hcomm
    have hc : (ρ (unSL2Diag u) * ρ (sl2Upper s)) * (g : X) *
        (ρ (unSL2Diag u) * ρ (sl2Upper s))⁻¹ = g := mul_inv_eq_iff_eq_mul.2 hcomm'
    exact lang_fixfree D θ hθ₂m hθ₁ hθ₃ hab₁ hab₃ hTor hh heU hh1 hmid hgU hgθ hc
  have hcardU : Nat.card ↥(polU D θ) = (p ^ f) ^ 3 := by
    have hUc : Nat.card ↥(polU D θ) = Nat.card ↥(D.U ⊓ foldFix θ) := by
      unfold polU
      rw [← Subgroup.inf_subgroupOf_right]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right)).toEquiv
    rw [hUc]
    exact hcard
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hUbot : polU D θ = ⊥ := le_bot_iff.1 (hbot ▸ hUS)
    rw [hUbot, Subgroup.card_bot] at hcardU
    have : 1 < (p ^ f) ^ 3 := Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow hf.ne' hpp.one_lt)
    omega
  have hSsimple : IsSimpleGroup ↥S := by
    refine isSimpleGroup_of_dichotomy S hSne fun A hAS hAn => ?_
    exact rankOne_simple_normal (polB D θ) (polU D θ) hdata.1 hdata.2.1
      (⟨x⁻¹ * c * x, hc₀f⟩ : ↥(foldFix θ)) hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2 hBsolv' S
      hSperf hUS hSne A hAS hAn
  have hnab := exists_noncomm_of_perfect_sub S hSne hSperf
  have hxS : (p ^ f) ^ 3 ∣ Nat.card ↥S := by
    rw [← hcardU]
    exact Subgroup.card_dvd_of_le hUS
  have hSC : Nat.card ↥S ≤ (p ^ f) ^ 3 * (p ^ f) ^ 5 := by
    calc Nat.card ↥S ≤ Nat.card ↥(foldFix θ) := Subgroup.card_le_card_group S
      _ = Nat.card ↥(foldFix τ) := Nat.card_congr (unFixEquiv τ θ x hθapp).toEquiv
      _ = ((p ^ f) ^ 3 * m) * (1 + (p ^ f) ^ 3) := hcardτ
      _ ≤ (p ^ f) ^ 3 * (p ^ f) ^ 5 := count_bound (by omega) hm
  exact SimpleCore.of_equiv (unFixEquiv τ θ x hθapp) ⟨S, hSn, hSsolv, hSsimple, hnab, hxS, hSC⟩

end CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4A2
