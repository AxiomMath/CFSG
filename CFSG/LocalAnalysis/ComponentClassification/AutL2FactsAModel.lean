module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldInv
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel

public noncomputable section

namespace CFSG.ComponentClassification.AutL2Facts

open CFSG GorensteinWalter Subgroup
open scoped Pointwise

universe u

variable {F : Type u} [Field F] [Finite F]

theorem right_sq_of_centralizes_sylow {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (T : Sylow 2 (PSL2 F)) (hT : 8 ≤ Nat.card T) (x : PGammaL2 F)
    {k : ℕ} (hk : x.right ^ 2 ^ k = 1)
    (hxT : ∀ t ∈ (T : Subgroup (PSL2 F)), x * incl F t = incl F t * x) : x.right ^ 2 = 1 := by
  have hodd := isOddPrimePower_of hp hp2 hf hF
  rcases Nat.even_or_odd f with hfe | hfo
  · have hq4 : Nat.card F % 4 = 1 := by rw [hF]; exact pow_mod_four_of_even hp hp2 hfe
    have hsq : IsSquare (-1 : F) := by
      have : Fintype F := Fintype.ofFinite F
      classical
      rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
      omega
    obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (PSL2 F) (stdSylow F hodd hsq hq4) T
    have hn : 3 ≤ twoVal F := by
      have hc : Nat.card T = 2 ^ twoVal F := by
        rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity (stdSylow F hodd hsq hq4),
          coe_stdSylow, card_stdT hodd hsq]
      rw [hc] at hT
      by_contra hlt
      push Not at hlt
      have : 2 ^ twoVal F ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨t₀, ht₀⟩ := torSub_stdGen_le_range hsq ⟨stdGen F ^ 2, mem_zpowers _, false,
      (mul_one _).symm⟩
    have ht₀T : h * t₀ * h⁻¹ ∈ (T : Subgroup (PSL2 F)) := by
      rw [← hh, mem_smul_sylow_iff, coe_stdSylow, show h⁻¹ * (h * t₀ * h⁻¹) * h = t₀ by group]
      change Matrix.ProjectiveSpecialLinearGroup.toPGL t₀ ∈ torSub F _
      rw [ht₀]
      exact ⟨stdGen F ^ 2, mem_zpowers _, false, (mul_one _).symm⟩
    have hc := hxT _ ht₀T
    set c := incl F h
    have e1 : incl F (h * t₀ * h⁻¹) = c * SemidirectProduct.inl (tor F (stdGen F ^ 2)) * c⁻¹ := by
      rw [map_mul, map_mul, map_inv, incl_apply F t₀, ht₀]
    rw [e1] at hc
    have hx' : c⁻¹ * x * c * SemidirectProduct.inl (tor F (stdGen F ^ 2)) =
        SemidirectProduct.inl (tor F (stdGen F ^ 2)) * (c⁻¹ * x * c) := by
      calc c⁻¹ * x * c * SemidirectProduct.inl (tor F (stdGen F ^ 2)) =
          c⁻¹ * (x * (c * SemidirectProduct.inl (tor F (stdGen F ^ 2)) * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * SemidirectProduct.inl (tor F (stdGen F ^ 2)) * c⁻¹) * x) * c := by
            rw [hc]
        _ = _ := by group
    have hright : (c⁻¹ * x * c).right = x.right := by simp [c, incl_apply]
    have := fieldProj_sq_of_commute_tor hp hp2 hF (c⁻¹ * x * c) (orderOf_stdGen_sq hodd)
      (by omega) hx' (k := k) (by rw [hright]; exact hk)
    rwa [hright] at this
  · rw [eq_one_of_two_power_ringAut hp hF hfo x.right k hk, one_pow]

omit [Finite F] in
theorem mem_klein_of_commute (hodd : IsOddPrimePower (Nat.card F)) [Finite F] {a b x : PGL2 F}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b)
    (hc : Commute a b) (hxa : x * a = a * x) (hxb : x * b = b * x) :
    x = a * b ∨ x = a ∨ x = b ∨ x = 1 := by
  have hK := isKleinFour_kleinFourOfCommutingInvolutions a b ha hb ha1 hb1 hab hc
  have hC := pgl2_kleinFour_centralizer_eq_self F hodd _ hK
  have hx : x ∈ kleinFourOfCommutingInvolutions a b ha hb hc := by
    rw [← hC, mem_centralizer_iff]
    intro w hw
    change w ∈ ({a * b, a, b, 1} : Set (PGL2 F)) at hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · rw [mul_assoc, ← hxb, ← mul_assoc, ← hxa, mul_assoc]
    · exact hxa.symm
    · exact hxb.symm
    · rw [one_mul, mul_one]
  change x ∈ ({a * b, a, b, 1} : Set (PGL2 F)) at hx
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx

theorem ringAut_eq_of_sq {σ τ : F ≃+* F} (hσ : σ * σ = 1) (hτ : τ * τ = 1) (hσ1 : σ ≠ 1)
    (hτ1 : τ ≠ 1) : σ = τ := by
  by_contra hne
  classical
  have := isCyclic_ringAut F
  have : Fintype (F ≃+* F) := Fintype.ofFinite _
  have h := IsCyclic.card_pow_eq_one_le (α := F ≃+* F) (n := 2) two_pos
  have hsub : ({1, σ, τ} : Finset (F ≃+* F)) ⊆ Finset.univ.filter fun x => x ^ 2 = 1 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pow_two]
    rcases hx with rfl | rfl | rfl
    · exact mul_one 1
    · exact hσ
    · exact hτ
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [Ne.symm hσ1, Ne.symm hτ1]),
    Finset.card_pair hne] at hcard
  omega

theorem right_sq_of_dihedral {m : ℕ} (D₁ : Subgroup (PGammaL2 F))
    (ψ : D₁ ≃* DihedralGroup m) (d : PGammaL2 F) (hd : d ∈ D₁) : d.right * d.right = 1 := by
  obtain ⟨i, j, hi, hj, hij⟩ := dihedral_eq_mul_involutions (ψ ⟨d, hd⟩)
  have hcomm : ∀ σ τ : F ≃+* F, σ * τ = τ * σ := fun σ τ => by
    have := isCyclic_ringAut F
    exact IsCyclic.commGroup.mul_comm σ τ
  have hi' : ((ψ.symm i : PGammaL2 F)).right * ((ψ.symm i : PGammaL2 F)).right = 1 := by
    have : (ψ.symm i : PGammaL2 F) * ψ.symm i = 1 := by
      have := congrArg Subtype.val (show ψ.symm i * ψ.symm i = 1 by rw [← map_mul, hi, map_one])
      exact this
    have := congrArg SemidirectProduct.right this
    simpa using this
  have hj' : ((ψ.symm j : PGammaL2 F)).right * ((ψ.symm j : PGammaL2 F)).right = 1 := by
    have : (ψ.symm j : PGammaL2 F) * ψ.symm j = 1 := by
      have := congrArg Subtype.val (show ψ.symm j * ψ.symm j = 1 by rw [← map_mul, hj, map_one])
      exact this
    have := congrArg SemidirectProduct.right this
    simpa using this
  have hd' : d = (ψ.symm i : PGammaL2 F) * ψ.symm j := by
    have := congrArg Subtype.val (show (⟨d, hd⟩ : D₁) = ψ.symm i * ψ.symm j by
      rw [← map_mul, ← hij, MulEquiv.symm_apply_apply])
    exact this
  rw [hd', SemidirectProduct.mul_right]
  calc _ = ((ψ.symm i : PGammaL2 F)).right * ((ψ.symm i : PGammaL2 F)).right *
      (((ψ.symm j : PGammaL2 F)).right * ((ψ.symm j : PGammaL2 F)).right) := by
        rw [mul_assoc, ← mul_assoc ((ψ.symm j : PGammaL2 F)).right,
          hcomm ((ψ.symm j : PGammaL2 F)).right, mul_assoc, mul_assoc]
    _ = 1 := by rw [hi', hj', mul_one]

theorem exists_central_involution {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    (hE : IsPGroup 2 E) (hE1 : E ≠ ⊥) :
    ∃ e ∈ E, e ≠ 1 ∧ e * e = 1 ∧ ∀ y ∈ E, y * e = e * y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).mpr hE1
  have hZ := hE.center_nontrivial
  have hZ2 : IsPGroup 2 (center E) := hE.to_subgroup _
  have hdvd : 2 ∣ Nat.card (center E) := by
    rcases hZ2.card_eq_or_dvd with h | h
    · exfalso
      exact not_nontrivial_iff_subsingleton.mpr (Nat.card_eq_one_iff_unique.mp h).1 hZ
    · exact h
  have : Fintype (center E) := Fintype.ofFinite _
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := center E) 2
    (by rwa [← Nat.card_eq_fintype_card])
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx]; exact pow_orderOf_eq_one x
  refine ⟨((x : E) : G), (x : E).2, ?_, ?_, ?_⟩
  · intro h
    have h1 : x = 1 := Subtype.ext (Subtype.ext h)
    rw [h1, orderOf_one] at hx
    exact absurd hx (by norm_num)
  · exact congrArg (fun y : center E => ((y : E) : G)) hx2
  · intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp x.2 ⟨y, hy⟩)

omit [Finite F] in
theorem left_mem_of_right_eq_one {x : PGammaL2 F} (hx : x.right = 1) :
    x = SemidirectProduct.inl x.left := SemidirectProduct.ext rfl hx

omit [Finite F] in
theorem commute_left_of_right_eq_one {x y : PGammaL2 F} (hx : x.right = 1) (hy : y.right = 1)
    (h : x * y = y * x) : x.left * y.left = y.left * x.left := by
  rw [left_mem_of_right_eq_one hx, left_mem_of_right_eq_one hy, ← map_mul, ← map_mul] at h
  exact SemidirectProduct.inl_injective h

omit [Finite F] in
theorem left_mul_self_of_right_eq_one {x : PGammaL2 F} (hx : x.right = 1) (h : x * x = 1) :
    x.left * x.left = 1 := by
  rw [left_mem_of_right_eq_one hx, ← map_mul] at h
  exact SemidirectProduct.inl_injective (h.trans (map_one _).symm)

omit [Finite F] in
theorem left_ne_one_of_right_eq_one {x : PGammaL2 F} (hx : x.right = 1) (h : x ≠ 1) :
    x.left ≠ 1 := by
  intro h1
  apply h
  rw [left_mem_of_right_eq_one hx, h1, map_one]

theorem eq_of_commute_klein (hodd : IsOddPrimePower (Nat.card F)) {a b e : PGammaL2 F}
    (har : a.right = 1) (hbr : b.right = 1) (her : e.right = 1) (ha : a * a = 1)
    (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a)
    (hea : e * a = a * e) (heb : e * b = b * e) : e = a * b ∨ e = a ∨ e = b ∨ e = 1 := by
  have hab' : a.left ≠ b.left := by
    intro h
    apply hab
    rw [left_mem_of_right_eq_one har, left_mem_of_right_eq_one hbr, h]
  have := mem_klein_of_commute hodd (left_mul_self_of_right_eq_one har ha)
    (left_mul_self_of_right_eq_one hbr hb) (left_ne_one_of_right_eq_one har ha1)
    (left_ne_one_of_right_eq_one hbr hb1) hab' (commute_left_of_right_eq_one har hbr hc)
    (commute_left_of_right_eq_one her har hea) (commute_left_of_right_eq_one her hbr heb)
  rw [left_mem_of_right_eq_one her, left_mem_of_right_eq_one har (x := a),
    left_mem_of_right_eq_one hbr (x := b)]
  rcases this with h | h | h | h
  · left; rw [h, map_mul]
  · right; left; rw [h]
  · right; right; left; rw [h]
  · right; right; right; rw [h, map_one]

theorem dihedral_elements {G : Type*} [Group G] (D₁ : Subgroup G) {m : ℕ} (hm : 1 ≤ m)
    (ψ : D₁ ≃* DihedralGroup (2 ^ m)) :
    ∃ z₁ ∈ D₁, ∃ s₁ ∈ D₁, ∃ s₂ ∈ D₁, ∃ c₁ ∈ D₁,
      z₁ * z₁ = 1 ∧ s₁ * s₁ = 1 ∧ s₂ * s₂ = 1 ∧ z₁ ≠ 1 ∧ s₁ ≠ 1 ∧ s₂ ≠ 1 ∧ z₁ ≠ s₁ ∧
      z₁ ≠ s₂ ∧ (∀ d ∈ D₁, z₁ * d = d * z₁) ∧ c₁ = s₁ * s₂ ∧ orderOf c₁ = 2 ^ m ∧
      z₁ = c₁ ^ (2 ^ m / 2) := by
  set N := 2 ^ m with hNdef
  have hN : 2 ≤ N := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have : NeZero N := ⟨by omega⟩
  have heven : Even N := by rw [hNdef, Nat.even_pow]; exact ⟨even_two, by omega⟩
  let f : DihedralGroup N → G := fun x => ((ψ.symm x : D₁) : G)
  have hfmul : ∀ x y, f x * f y = f (x * y) := fun x y => by
    simp only [f, map_mul, Subgroup.coe_mul]
  have hfone : f 1 = 1 := by simp [f]
  have hfinj : ∀ x y, f x = f y → x = y := fun x y h => ψ.symm.injective (Subtype.ext h)
  have hfmem : ∀ x, f x ∈ D₁ := fun x => (ψ.symm x).2
  have hz2 : DihedralGroup.r ((N / 2 : ℕ) : ZMod N) * DihedralGroup.r ((N / 2 : ℕ) : ZMod N) =
      1 := by
    rw [DihedralGroup.r_mul_r, ← Nat.cast_add, DihedralGroup.one_def]
    obtain ⟨k, hk⟩ := heven
    rw [hk, show (k + k) / 2 = k by omega, ZMod.natCast_self]
  have hz1 : DihedralGroup.r ((N / 2 : ℕ) : ZMod N) ≠ 1 := by
    rw [DihedralGroup.one_def, ne_eq, DihedralGroup.r.injEq, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  refine ⟨f (DihedralGroup.r ((N / 2 : ℕ) : ZMod N)), hfmem _, f (DihedralGroup.sr 0), hfmem _,
    f (DihedralGroup.sr 1), hfmem _, f (DihedralGroup.r 1), hfmem _, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfmul, hz2, hfone]
  · rw [hfmul, DihedralGroup.sr_mul_self, hfone]
  · rw [hfmul, DihedralGroup.sr_mul_self, hfone]
  · intro h
    rw [← hfone] at h
    exact hz1 (hfinj _ _ h)
  · intro h
    rw [← hfone] at h
    exact absurd (hfinj _ _ h) (by rintro ⟨⟩)
  · intro h
    rw [← hfone] at h
    exact absurd (hfinj _ _ h) (by rintro ⟨⟩)
  · intro h
    exact absurd (hfinj _ _ h) (by rintro ⟨⟩)
  · intro h
    exact absurd (hfinj _ _ h) (by rintro ⟨⟩)
  · intro d hd
    have hc := mem_center_iff.mp (r_half_mem_center heven) (ψ ⟨d, hd⟩)
    have : f (DihedralGroup.r ((N / 2 : ℕ) : ZMod N)) * f (ψ ⟨d, hd⟩) =
        f (ψ ⟨d, hd⟩) * f (DihedralGroup.r ((N / 2 : ℕ) : ZMod N)) := by
      rw [hfmul, hfmul, hc]
    simpa [f] using this
  · rw [hfmul, DihedralGroup.sr_mul_sr, sub_zero]
  · have : orderOf (f (DihedralGroup.r 1)) = orderOf (DihedralGroup.r 1 : DihedralGroup N) := by
      have h1 := orderOf_injective (D₁.subtype.comp ψ.symm.toMonoidHom)
        (Subtype.val_injective.comp ψ.symm.injective) (DihedralGroup.r 1)
      exact h1
    rw [this, DihedralGroup.orderOf_r_one]
  · have h1 : ∀ k : ℕ, f (DihedralGroup.r 1) ^ k = f (DihedralGroup.r 1 ^ k) := by
      intro k
      induction k with
      | zero => simp [hfone]
      | succ k ih => rw [pow_succ, ih, hfmul, ← pow_succ]
    rw [h1, DihedralGroup.r_one_pow]

theorem card_sylow_eq (hodd : IsOddPrimePower (Nat.card F)) (hsq : IsSquare (-1 : F))
    (hq4 : Nat.card F % 4 = 1) (T : Sylow 2 (PSL2 F)) : Nat.card T = 2 ^ twoVal F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity (stdSylow F hodd hsq hq4),
    coe_stdSylow, card_stdT hodd hsq]

theorem even_of_ringAut {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f) {σ : F ≃+* F}
    (hσ : σ * σ = 1) (hσ1 : σ ≠ 1) : Even f := by
  have h2 : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ) hσ1
  have := orderOf_dvd_natCard σ
  rw [h2, card_ringAut F hp hF] at this
  exact even_iff_two_dvd.mpr this

theorem l2A_case_linear {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (D₁ : Subgroup (PGammaL2 F)) (T : Sylow 2 (PSL2 F))
    {m : ℕ} (hm : 1 ≤ m) (ψ : D₁ ≃* DihedralGroup (2 ^ m)) (hTcard : Nat.card T = 2 ^ (m + 1))
    (e : PGammaL2 F) (he1 : e ≠ 1) (he2 : e * e = 1) (heD : e ∉ D₁)
    (hed : ∀ d ∈ D₁, e * d = d * e) (her : e.right = 1) : False := by
  have hodd := isOddPrimePower_of hp hp2 hf hF
  obtain ⟨z₁, hz, s₁, hs₁, s₂, hs₂, c₁, hc₁, hz2, hs₁2, hs₂2, hz1, hs₁1, hs₂1, hzs₁, hzs₂,
    hzc, hc, hord, hzpow⟩ := dihedral_elements D₁ hm ψ
  have hsq : ∀ d ∈ D₁, d.right * d.right = 1 := right_sq_of_dihedral D₁ ψ
  have hklein : ∀ a ∈ D₁, ∀ b ∈ D₁, a.right = 1 → b.right = 1 → a * a = 1 → b * b = 1 → a ≠ 1 →
      b ≠ 1 → a ≠ b → a * b = b * a → False := by
    intro a ha b hb har hbr haa hbb ha1 hb1 hab hc'
    rcases eq_of_commute_klein hodd har hbr her haa hbb ha1 hb1 hab hc' (hed a ha) (hed b hb) with
      h | h | h | h
    · exact heD (h ▸ D₁.mul_mem ha hb)
    · exact heD (h ▸ ha)
    · exact heD (h ▸ hb)
    · exact he1 h
  by_cases hzr : z₁.right = 1 ∧ s₁.right = 1
  · exact hklein z₁ hz s₁ hs₁ hzr.1 hzr.2 hz2 hs₁2 hz1 hs₁1 hzs₁ (hzc s₁ hs₁)
  have hfe : Even f := by
    by_cases h1 : z₁.right = 1
    · exact even_of_ringAut hp hF (hsq s₁ hs₁) (fun h => hzr ⟨h1, h⟩)
    · exact even_of_ringAut hp hF (hsq z₁ hz) h1
  have hq4 : Nat.card F % 4 = 1 := by rw [hF]; exact pow_mod_four_of_even hp hp2 hfe
  have hsqF : IsSquare (-1 : F) := by
    have : Fintype F := Fintype.ofFinite F
    classical
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  have hn : 3 ≤ twoVal F := by
    have h8 : 2 ^ 3 ∣ Nat.card F - 1 := by rw [hF]; exact eight_dvd_of_even hp hp2 hfe
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by
      have := Finite.one_lt_card (α := F); omega)).mp h8
  have hm2 : 2 ≤ m := by
    have h := card_sylow_eq hodd hsqF hq4 T
    rw [hTcard] at h
    have := Nat.pow_right_injective (le_refl 2) h
    omega
  have hz1r : z₁.right = 1 := by
    rw [hzpow]
    have hc2 := hsq c₁ hc₁
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ m / 2 = 2 * k := ⟨2 ^ (m - 2), by
      rw [show 2 ^ m = 2 * (2 * 2 ^ (m - 2)) by
        rw [← mul_assoc, ← pow_two, ← pow_add]; congr 1; omega]
      omega⟩
    have : (c₁ ^ (2 ^ m / 2)).right = (c₁.right * c₁.right) ^ k := by
      rw [hk]
      change fieldProj F (c₁ ^ (2 * k)) = _
      rw [map_pow, pow_mul, pow_two]
      rfl
    rw [this, hc2, one_pow]
  have hs₁r : s₁.right ≠ 1 := fun h => hzr ⟨hz1r, h⟩
  have hs₂r : s₂.right ≠ 1 := fun h =>
    hklein z₁ hz s₂ hs₂ hz1r h hz2 hs₂2 hz1 hs₂1 hzs₂ (hzc s₂ hs₂)
  have hsame := ringAut_eq_of_sq (hsq s₁ hs₁) (hsq s₂ hs₂) hs₁r hs₂r
  have hc1r : c₁.right = 1 := by
    rw [hc, SemidirectProduct.mul_right, ← hsame, hsq s₁ hs₁]
  have hze : z₁ ≠ e := fun h => heD (h ▸ hz)
  rcases eq_of_commute_klein hodd hz1r her hc1r hz2 he2 hz1 he1 hze (hed z₁ hz).symm
    (hzc c₁ hc₁).symm (hed c₁ hc₁).symm with h | h | h | h
  · have hcc : c₁ * c₁ = 1 := by
      have hez := hed z₁ hz
      calc c₁ * c₁ = z₁ * (e * z₁) * e := by rw [h]; group
        _ = z₁ * (z₁ * e) * e := by rw [hez]
        _ = (z₁ * z₁) * (e * e) := by group
        _ = 1 := by rw [hz2, he2, one_mul]
    have := orderOf_dvd_of_pow_eq_one (show c₁ ^ 2 = 1 by rw [pow_two]; exact hcc)
    rw [hord] at this
    have := Nat.le_of_dvd (by norm_num) this
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  · have := orderOf_dvd_of_pow_eq_one (show c₁ ^ 2 = 1 by rw [h, pow_two, hz2])
    rw [hord] at this
    have := Nat.le_of_dvd (by norm_num) this
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  · have := orderOf_dvd_of_pow_eq_one (show c₁ ^ 2 = 1 by rw [h, pow_two, he2])
    rw [hord] at this
    have := Nat.le_of_dvd (by norm_num) this
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  · rw [h, orderOf_one] at hord
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega

omit [Finite F] in
theorem right_pow_half_eq_one {c : PGammaL2 F} (hc : c.right * c.right = 1) {m : ℕ}
    (hm : 2 ≤ m) : (c ^ (2 ^ m / 2)).right = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ m / 2 = 2 * k := ⟨2 ^ (m - 2), by
    rw [show 2 ^ m = 2 * (2 * 2 ^ (m - 2)) by
      rw [← mul_assoc, ← pow_two, ← pow_add]; congr 1; omega]
    omega⟩
  rw [hk]
  change fieldProj F (c ^ (2 * k)) = 1
  rw [map_pow, pow_mul, pow_two]
  change (c.right * c.right) ^ k = 1
  rw [hc, one_pow]

theorem l2A_case_field {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (R D₁ E : Subgroup (PGammaL2 F)) (hR : IsPGroup 2 R)
    (hD₁R : D₁ ≤ R) (hER : E ≤ R) (hED : ∀ y ∈ E, ∀ d ∈ D₁, y * d = d * y)
    (hDE : D₁ ⊓ E = ⊥) (hE1 : E ≠ ⊥) (T : Sylow 2 (PSL2 F)) {m : ℕ} (hm : 1 ≤ m)
    (ψ : D₁ ≃* DihedralGroup (2 ^ m)) (hDcard : Nat.card D₁ = Nat.card T) (e : PGammaL2 F)
    (heE : e ∈ E) (he1 : e ≠ 1) (he2 : e * e = 1) (heZ : ∀ y ∈ E, y * e = e * y)
    (her : e.right ≠ 1) :
    Nat.card E = 2 ∧ 8 ≤ Nat.card T ∧
      ∃ T' : Sylow 2 (PSL2 F), (T' : Subgroup (PSL2 F)).map (incl F) ≤ D₁ ⊔ E := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := isOddPrimePower_of hp hp2 hf hF
  have hesq : e.right * e.right = 1 := by
    have := congrArg SemidirectProduct.right he2
    simpa using this
  have hfe : Even f := even_of_ringAut hp hF hesq her
  have hq4 : Nat.card F % 4 = 1 := by rw [hF]; exact pow_mod_four_of_even hp hp2 hfe
  have hsqF : IsSquare (-1 : F) := by
    have : Fintype F := Fintype.ofFinite F
    classical
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card]
    omega
  have hn : 3 ≤ twoVal F := by
    have h8 : 2 ^ 3 ∣ Nat.card F - 1 := by rw [hF]; exact eight_dvd_of_even hp hp2 hfe
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by
      have := Finite.one_lt_card (α := F); omega)).mp h8
  have hTc := card_sylow_eq hodd hsqF hq4 T
  have h8 : 8 ≤ Nat.card T := by
    rw [hTc]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ twoVal F := Nat.pow_le_pow_right (by norm_num) hn
  have hm2 : 2 ≤ m := by
    have h1 : Nat.card D₁ = 2 ^ (m + 1) := by
      rw [Nat.card_congr ψ.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
    rw [hDcard, hTc] at h1
    have := Nat.pow_right_injective (le_refl 2) h1
    omega
  obtain ⟨z₁, hz, -, -, -, -, c₁, hc₁, -, -, -, hz1, -, -, -, -, hzc, -, -, hzpow⟩ :=
    dihedral_elements D₁ hm ψ
  have hsqD : ∀ d ∈ D₁, d.right * d.right = 1 := right_sq_of_dihedral D₁ ψ
  have hz1r : z₁.right = 1 := by rw [hzpow]; exact right_pow_half_eq_one (hsqD c₁ hc₁) hm2
  have heD : e ∉ D₁ := by
    intro h
    have : e ∈ D₁ ⊓ E := ⟨h, heE⟩
    rw [hDE, mem_bot] at this
    exact he1 this
  set P := D₁ ⊔ zpowers e
  have hPR : P ≤ R := sup_le hD₁R (zpowers_le.mpr (hER heE))
  have hPE : P ≤ D₁ ⊔ E := sup_le le_sup_left (le_sup_of_le_right (zpowers_le.mpr heE))
  have hcent : ∀ y : PGammaL2 F, (∀ d ∈ D₁, y * d = d * y) → y * e = e * y →
      ∀ x ∈ P, y * x = x * y := by
    intro y hyD hye x hx
    have hle : P ≤ centralizer ({y} : Set (PGammaL2 F)) := by
      apply sup_le
      · intro d hd
        rw [mem_centralizer_iff]
        rintro _ rfl
        exact hyD d hd
      · rw [zpowers_le, mem_centralizer_iff]
        rintro _ rfl
        exact hye
    exact (mem_centralizer_iff.mp (hle hx) y rfl)
  have hPe : ∀ x ∈ P, x * e = e * x := fun x hx =>
    (hcent e (hED e heE) rfl x hx).symm
  set T' := P ⊓ (SemidirectProduct.inl : PGL2 F →* PGammaL2 F).range
  have hT'L : T' ≤ pGammaL2PSLRange F := by
    rintro x ⟨hxP, g, rfl⟩
    exact mem_pslRange_of_commute_fieldInv hp hp2 hF e he2 her g (hPe _ hxP).symm
  have hcardT' : Nat.card D₁ ≤ Nat.card T' := by
    have hι : ∀ d : D₁, (if (d : PGammaL2 F).right = 1 then (d : PGammaL2 F) else d * e) ∈ T' := by
      intro d
      split_ifs with h
      · exact ⟨le_sup_left (a := D₁) d.2, (d : PGammaL2 F).left,
          (left_mem_of_right_eq_one h).symm⟩
      · refine ⟨P.mul_mem (le_sup_left (a := D₁) d.2) (le_sup_right (a := D₁) (mem_zpowers e)),
          (d * e : PGammaL2 F).left, (left_mem_of_right_eq_one ?_).symm⟩
        rw [SemidirectProduct.mul_right, ringAut_eq_of_sq (hsqD d d.2) hesq h her, hesq]
    refine Nat.card_le_card_of_injective (fun d => ⟨_, hι d⟩) ?_
    intro d d' hdd
    have hdd' := congrArg Subtype.val hdd
    simp only at hdd'
    apply Subtype.ext
    split_ifs at hdd' with h1 h2 h2
    · exact hdd'
    · exfalso
      apply heD
      have : e = (d' : PGammaL2 F)⁻¹ * d := by rw [hdd']; group
      rw [this]
      exact D₁.mul_mem (D₁.inv_mem d'.2) d.2
    · exfalso
      apply heD
      have : e = (d : PGammaL2 F)⁻¹ * d' := by rw [← hdd']; group
      rw [this]
      exact D₁.mul_mem (D₁.inv_mem d.2) d'.2
    · exact mul_right_cancel hdd'
  set T'' := T'.comap (incl F)
  have hT'range : T' ≤ (incl F).range := hT'L
  have hT''map : T''.map (incl F) = T' := Subgroup.map_comap_eq_self hT'range
  have hT''card : Nat.card T'' = Nat.card T' := by
    rw [← hT''map, Subgroup.card_map_of_injective (incl_injective F)]
  have hT''2 : IsPGroup 2 T'' :=
    (hR.to_le (le_trans inf_le_left hPR)).comap_of_injective (incl F) (incl_injective F)
  have hT''le : Nat.card T'' ≤ 2 ^ twoVal F := by
    obtain ⟨S, hS⟩ := hT''2.exists_le_sylow
    calc Nat.card T'' ≤ Nat.card S := Subgroup.card_le_of_le hS
      _ = 2 ^ twoVal F := card_sylow_eq hodd hsqF hq4 S
  have hT''eq : Nat.card T'' = 2 ^ (Nat.card (PSL2 F)).factorization 2 := by
    rw [psl2_factorization_two hodd hq4]
    apply le_antisymm hT''le
    rw [hT''card, ← hTc, ← hDcard]
    exact hcardT'
  set TS : Sylow 2 (PSL2 F) := Sylow.ofCard T'' hT''eq
  have hTS : (TS : Subgroup (PSL2 F)) = T'' := Sylow.coe_ofCard _ _
  have hTSmap : (TS : Subgroup (PSL2 F)).map (incl F) = T' := by rw [hTS, hT''map]
  have hTS8 : 8 ≤ Nat.card TS := by rw [card_sylow_eq hodd hsqF hq4 TS, ← hTc]; exact h8
  have hET : ∀ y ∈ E, ∀ t ∈ (TS : Subgroup (PSL2 F)), y * incl F t = incl F t * y := by
    intro y hy t ht
    have htT' : incl F t ∈ T' := by rw [← hTSmap]; exact ⟨t, ht, rfl⟩
    exact hcent y (hED y hy) (heZ y hy) _ htT'.1
  have hE2 : ∀ y ∈ E, ∃ k : ℕ, y ^ 2 ^ k = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := hR ⟨y, hER hy⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hz₁T' : z₁ ∈ T' := ⟨le_sup_left (a := D₁) hz, z₁.left, (left_mem_of_right_eq_one hz1r).symm⟩
  set Z := ((TS : Subgroup (PSL2 F)) ⊓ centralizer ((TS : Subgroup (PSL2 F)) :
    Set (PSL2 F))).map (incl F)
  have hz₁Z : z₁ ∈ Z := by
    rw [← hTSmap] at hz₁T'
    obtain ⟨w, hw, hwz⟩ := hz₁T'
    have hwC : w ∈ centralizer ((TS : Subgroup (PSL2 F)) : Set (PSL2 F)) := by
      rw [mem_centralizer_iff]
      intro t ht
      apply incl_injective F
      rw [map_mul, map_mul, hwz]
      have htT' : incl F t ∈ T' := by rw [← hTSmap]; exact ⟨t, ht, rfl⟩
      exact (hcent z₁ (hzc) (hED e heE z₁ hz).symm _ htT'.1).symm
    exact ⟨w, ⟨hw, hwC⟩, hwz⟩
  have hZcard : Nat.card Z = 2 := by
    rw [Subgroup.card_map_of_injective (incl_injective F), (sylow_noncomm_center hodd TS hTS8).2]
  have hlin : linearPart E = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [mem_bot]
    have hgE : SemidirectProduct.inl g ∈ E := hg
    obtain ⟨k, hk⟩ := hE2 _ hgE
    have hyZ := mem_center_of_right_eq_one hodd TS hTS8 (SemidirectProduct.inl g) rfl hk
      (hET _ hgE)
    obtain ⟨y', -, hy'⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZcard
    by_contra hg1
    have hy1 : (⟨SemidirectProduct.inl g, hyZ⟩ : Z) ≠ 1 := by
      intro h
      apply hg1
      exact SemidirectProduct.inl_injective ((congrArg Subtype.val h).trans (map_one _).symm)
    have hz1' : (⟨z₁, hz₁Z⟩ : Z) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
    have := congrArg Subtype.val ((hy' _ hy1).trans (hy' _ hz1').symm)
    simp only at this
    have hzE : z₁ ∈ D₁ ⊓ E := ⟨hz, this ▸ hgE⟩
    rw [hDE, mem_bot] at hzE
    exact hz1 hzE
  have hpi : Nat.card (E.map (fieldProj F)) ≤ 2 := by
    apply card_le_two_of_sq_ringAut
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hE2 y hy
    have hk' : y.right ^ 2 ^ k = 1 := by
      have := congrArg (fieldProj F) hk
      rwa [map_pow, map_one] at this
    rw [← pow_two]
    exact right_sq_of_centralizes_sylow hp hp2 hf hF TS hTS8 y hk' (hET y hy)
  have hEcard : Nat.card E ≤ 2 := by
    rw [card_eq_linearPart_mul, hlin, Subgroup.card_bot, one_mul]
    exact hpi
  have hE1' : 1 < Nat.card E := (Subgroup.one_lt_card_iff_ne_bot E).mpr hE1
  refine ⟨by omega, h8, TS, ?_⟩
  rw [hTSmap]
  exact le_trans inf_le_left hPE

theorem l2A_model {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (R D₁ E : Subgroup (PGammaL2 F)) (hR : IsPGroup 2 R)
    (hD₁R : D₁ ≤ R) (hER : E ≤ R) (hED : ∀ y ∈ E, ∀ d ∈ D₁, y * d = d * y)
    (hDE : D₁ ⊓ E = ⊥) (hE1 : E ≠ ⊥) (T : Sylow 2 (PSL2 F))
    (φ : D₁ ≃* (T : Subgroup (PSL2 F))) :
    Nat.card E = 2 ∧ 8 ≤ Nat.card T ∧
      ∃ T' : Sylow 2 (PSL2 F), (T' : Subgroup (PSL2 F)).map (incl F) ≤ D₁ ⊔ E := by
  have hodd := isOddPrimePower_of hp hp2 hf hF
  obtain ⟨m, hm, ⟨χ⟩⟩ := sylow_two_dihedral_of_equiv (MulEquiv.refl (PSL2 F)) hodd T
  have hDcard : Nat.card D₁ = Nat.card T := Nat.card_congr φ.toEquiv
  have hTcard : Nat.card T = 2 ^ (m + 1) := by
    rw [Nat.card_congr χ.toEquiv, DihedralGroup.nat_card, pow_succ, mul_comm]
  obtain ⟨e, heE, he1, he2, heZ⟩ := exists_central_involution E (hR.to_le hER) hE1
  have heD : e ∉ D₁ := by
    intro h
    have : e ∈ D₁ ⊓ E := ⟨h, heE⟩
    rw [hDE, mem_bot] at this
    exact he1 this
  by_cases her : e.right = 1
  · exact (l2A_case_linear hp hp2 hf hF D₁ T hm (φ.trans χ) hTcard e he1 he2 heD
      (fun d hd => hED e heE d hd) her).elim
  · exact l2A_case_field hp hp2 hf hF R D₁ E hR hD₁R hER hED hDE hE1 T hm (φ.trans χ) hDcard e
      heE he1 he2 heZ her

end CFSG.ComponentClassification.AutL2Facts
