module

public import CFSG.Fischer.Classification.PartIII.Symp.Kill
public import CFSG.Fischer.Classification.PartIII.Symp.Exact
public import CFSG.Fischer.Classification.PartIII.Symp.Gauss
public import CFSG.Fischer.Classification.PartIII.Symp.Params
public import CFSG.Fischer.Classification.PartIII.Symp.Prime
public import CFSG.Fischer.Classification.PartIII.Symp.SymCount

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Open Symplectic LocalSymp Matrix

namespace LocalSymp

section Models

variable {H : Type} [Group H] {F : Set H}

theorem symModel_params {n : ℕ} (φ : H ≃* Equiv.Perm (Fin n))
    (hφ : ∀ g, g ∈ F ↔ (φ g).IsSwap) :
    F.ncard = n.choose 2 ∧ ∀ q ∈ F, (LocalClass F q).ncard = (n - 2).choose 2 := by
  have hφ' : ∀ g, g ∈ F ↔ φ g ∈ {σ : Equiv.Perm (Fin n) | σ.IsSwap} := hφ
  refine ⟨(ncard_of_mulEquiv φ hφ').trans ncard_isSwap, fun q hq => ?_⟩
  obtain ⟨a, b, hab, hq'⟩ := (hφ q).1 hq
  rw [localClass_eq_preimage φ hφ', Set.ncard_preimage_of_injective_subset_range φ.injective
    (by simp), hq', ncard_localClass_isSwap hab]

theorem oModel_params [Finite H] {m : ℕ} {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hmod : fischerLinearModel F (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    F.ncard = {v | Q v = 1}.ncard ∧
      (∀ q ∈ F, 4 * ((LocalClass F q).ncard + 1) = 4 ^ m) ∧
      ∀ q ∈ F, ∀ r ∈ F, q * r ≠ r * q →
        4 * ({v | Q v = 1}.ncard + 2 * (muSet F q r).ncard) = 3 * 4 ^ m := by
  obtain ⟨φ, hφ⟩ := hmod
  set B := QuadraticMap.polarBilin Q
  have hpol : ∀ x y, QuadraticMap.polar Q x y = B x y := fun x y =>
    (QuadraticMap.polarBilin_apply_apply Q x y).symm
  have hsymm : ∀ x y, B x y = B y x := fun x y => by
    rw [← hpol, ← hpol, QuadraticMap.polar_comm]
  have halt : ∀ x, B x x = 0 := fun x => by
    rw [← hpol, QuadraticMap.polar_self, two_nsmul, zmod2_add_self]
  have hnd' : ∀ x, (∀ y, B y x = 0) → x = 0 := fun x hx =>
    hnd x fun y => by rw [hpol, hsymm]; exact hx y
  have hP0 : ∀ v, Q v = 1 → v ≠ 0 := by
    rintro v hv rfl
    rw [QuadraticMap.map_zero] at hv
    exact zero_ne_one hv
  have hF : ∀ f ∈ F, ∃ v, Q v = 1 ∧ modelAct φ f = tv B v := by
    intro f hf
    obtain ⟨v, hv, h⟩ := (hφ f).1 hf
    refine ⟨v, hv, funext fun x => ?_⟩
    rw [tv_apply, ← hpol]
    exact h x
  have hsurj : ∀ w, Q w = 1 → ∃ f ∈ F, modelAct φ f = tv B w := by
    intro w hw
    refine ⟨φ.symm ⟨_, fischerTransvections_polar_subset
      (orthTransvectionGL_mem_fischerTransvections hw)⟩, ?_, ?_⟩
    · rw [hφ, MulEquiv.apply_symm_apply]
      exact orthTransvectionGL_mem_fischerTransvections hw
    · rw [modelAct_symm]
      funext x
      rw [tv_apply, ← hpol]
      exact orthTransvectionGL_mulVec hw x
  have hV : Nat.card (Fin (2 * m) → ZMod 2) = 4 ^ m := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, pow_mul]
    norm_num
  refine ⟨ncard_eq_of_tv B (modelAct φ) hnd' (modelAct_injective φ) hP0 hF hsurj, ?_, ?_⟩
  · intro q hq
    obtain ⟨s, hs, h₀⟩ := hF q hq
    rw [ncard_localClass_eq_of_tv B (modelAct φ) hsymm hnd' (modelAct_mul φ)
      (modelAct_injective φ) hP0 (fun v _ => halt v) hF hsurj hq h₀]
    have h4 := four_mul_ncard_quadratic_perp Q hnd hs
    have hset : {w | Q w = 1 ∧ B w s = 0 ∧ w ≠ s} =
        {w | Q w = 1 ∧ QuadraticMap.polar Q w s = 0} \ {s} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, hpol, and_assoc]
    have hmem : s ∈ {w | Q w = 1 ∧ QuadraticMap.polar Q w s = 0} :=
      ⟨hs, by rw [hpol]; exact halt s⟩
    rw [hset, Set.ncard_sdiff_singleton_add_one hmem, h4, hV]
  · intro q hq r hr hqr
    obtain ⟨s, hs, h₀⟩ := hF q hq
    obtain ⟨s', hs', h₁⟩ := hF r hr
    have hss' := bilin_eq_one_of_not_commute B (modelAct φ) hsymm (modelAct_mul φ)
      (modelAct_injective φ) h₀ h₁ hqr
    rw [ncard_muSet_eq_of_tv B (modelAct φ) hsymm hnd' (modelAct_mul φ) (modelAct_injective φ)
      hP0 (fun v _ => halt v) hF hsurj h₀ h₁ hss']
    have hcount := ncard_quadratic_add B Q hpol hs hs' hss'
    have hW := card_eq_four_mul B (halt s) (halt s') hss' (by rw [hsymm]; exact hss')
    rw [hV] at hW
    omega

end Models

theorem ncard_muSet_eq_of_forall {X : Type} [Group X] {E : Set X} (hP : Pair X E) {d : X}
    (hd : d ∈ E) {μ : ℕ} (hμ : ∀ c ∈ E, c * d ≠ d * c → (muSet E d c).ncard = μ) {x y : X}
    (hx : x ∈ E) (hy : y ∈ E) (hxy : x * y ≠ y * x) : (muSet E x y).ncard = μ := by
  obtain ⟨g, hg⟩ := isConj_iff.1 (Pair.isConj hP hx hd)
  have hyd : g * y * g⁻¹ * d ≠ d * (g * y * g⁻¹) := by
    rw [← hg, Ne, conj_commute_iff]
    exact fun h => hxy h.symm
  rw [← Set.ncard_image_of_injective _ (conj_injective g), Pair.image_conj_muSet hP, hg]
  exact hμ _ (Pair.conj_mem hP hy g) hyd

section Arith

theorem pow_eq_of_three_le {m : ℕ} (hm : 3 ≤ m) :
    2 ^ m = 8 * 2 ^ (m - 3) ∧ 4 ^ m = 64 * (2 ^ (m - 3) * 2 ^ (m - 3)) ∧
      4 ^ (m - 1) = 16 * (2 ^ (m - 3) * 2 ^ (m - 3)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp only [Nat.add_sub_cancel_left, show 3 + k - 1 = 2 + k by omega]
  refine ⟨by rw [pow_add]; norm_num, ?_, ?_⟩
  · rw [← mul_pow, pow_add, show (2 * 2 : ℕ) = 4 by norm_num]
    norm_num
  · rw [← mul_pow, pow_add, show (2 * 2 : ℕ) = 4 by norm_num]
    norm_num

theorem minus_arith {m μ δ A N : ℕ} (hm : 4 ≤ m) (hN : 2 * N = 4 ^ m + 2 ^ m) (hδ : Even δ)
    (hμ : μ = 1 + (3 * 4 ^ (m - 1) - N) / 2 + δ) (h4 : 4 * μ ≤ N)
    (hA : μ * A = N * (N - 1 - (4 ^ (m - 1) - 1))) : False := by
  obtain ⟨h2, h4m, h4m1⟩ := pow_eq_of_three_le (show 3 ≤ m by omega)
  set t := 2 ^ (m - 3) with ht
  have ht2 : 2 ≤ t := by
    rw [ht]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (m - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨s, hs⟩ : ∃ s, s = t * t := ⟨_, rfl⟩
  rw [← hs] at h4m h4m1
  have hs2 : 2 * t ≤ s := by rw [hs]; exact Nat.mul_le_mul_right t ht2
  obtain ⟨e, rfl⟩ := hδ
  have hNv : N = 32 * s + 4 * t := by omega
  have hμv : μ = 1 + (8 * s - 2 * t) + (e + e) := by rw [hμ, h4m1, hNv]; omega
  have hA' : μ * A = 16 * s * (32 * s + 12 * t + 1) := by
    rw [hA, h4m1, hNv, show 32 * s + 4 * t - 1 - (16 * s - 1) = 16 * s + 4 * t by omega, hs]
    ring
  have hodd : Odd μ := ⟨4 * s - t + e, by omega⟩
  have hcop : μ.Coprime (16 * s) := by
    have h2c := Odd.coprime_two_right hodd
    have : 16 * s = 2 ^ (4 + (m - 3) + (m - 3)) := by rw [hs, ht, pow_add, pow_add]; ring
    rw [this]
    exact h2c.pow_right _
  obtain ⟨q, hq⟩ := hcop.dvd_of_dvd_mul_left ⟨A, hA'.symm⟩
  have hμpos : 0 < μ := by omega
  have h3q : 3 < q := by
    have : μ * 3 < μ * q := by rw [← hq]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hq6 : q < 6 := by
    have : μ * q < μ * 6 := by rw [← hq]; omega
    exact Nat.lt_of_mul_lt_mul_left this
  interval_cases q
  · omega
  · rcases Nat.lt_or_ge t 3 with h | h
    · have ht2' : t = 2 := by omega
      rw [ht2'] at hs
      omega
    · have : 3 * t ≤ s := by rw [hs]; exact Nat.mul_le_mul_right t h
      omega

theorem minus_arith_three {μ δ A N : ℕ} (hN : 2 * N = 4 ^ 3 + 2 ^ 3) (hδ : Even δ)
    (hμ : μ = 1 + (3 * 4 ^ 2 - N) / 2 + δ) (h4 : 4 * μ ≤ N)
    (hA : μ * A = N * (N - 1 - (4 ^ 2 - 1))) : μ = 9 ∧ δ = 2 ∧ A = 80 := by
  obtain ⟨e, rfl⟩ := hδ
  have hNv : N = 36 := by omega
  subst hNv
  have hμv : μ = 7 + (e + e) := by omega
  subst hμv
  norm_num at hA h4
  rcases Nat.lt_or_ge e 1 with h | h
  · have he : e = 0 := by omega
    subst he
    omega
  · have he : e = 1 := by omega
    subst he
    omega

theorem arith_ten {μ A : ℕ} (h2 : 2 ≤ μ) (h4 : 4 * μ ≤ 10) (hA : μ * A = 10 * (10 - 1 - 3)) :
    μ = 2 ∧ A = 30 := by
  have : μ = 2 := by omega
  subst this
  omega

end Arith

end LocalSymp

variable {G : Type} [Group G] {D : Set G}

theorem false_of_localSym5 (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hnot : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D)
    (φ : LocalQuotient D d ≃* Equiv.Perm (Fin 5))
    (hφ : ∀ g, g ∈ LocalImages D d ↔ (φ g).IsSwap) : False := by
  obtain ⟨hk, hlam⟩ := symModel_params φ hφ
  have hsymp := isSymplecticType_of_perm φ hφ
  obtain ⟨μ, hμ, h4, hA, hE⟩ := Pair.params_basic hH hna hnot hd hsymp hlam
  obtain ⟨hP, hZ, hS⟩ := hH
  have h3 : 3 ≤ 5 := by norm_num
  have hφ' : ∀ g, g ∈ LocalImages D d ↔ φ g ∈ {σ : Equiv.Perm (Fin 5) | σ.IsSwap} := hφ
  have hq : φ.symm (Equiv.swap (i0 h3) (i1 h3)) ∈ LocalImages D d := by
    rw [hφ', MulEquiv.apply_symm_apply]
    exact ⟨_, _, i0_ne_i1 h3, rfl⟩
  have hr : φ.symm (Equiv.swap (i1 h3) (i2 h3)) ∈ LocalImages D d := by
    rw [hφ', MulEquiv.apply_symm_apply]
    exact ⟨_, _, i1_ne_i2 h3, rfl⟩
  have hqr : φ.symm (Equiv.swap (i0 h3) (i1 h3)) * φ.symm (Equiv.swap (i1 h3) (i2 h3)) ≠
      φ.symm (Equiv.swap (i1 h3) (i2 h3)) * φ.symm (Equiv.swap (i0 h3) (i1 h3)) := by
    rw [Ne, ← commute_iff_map φ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact swap_mul_swap_ne h3
  rw [← range_starImage] at hq hr
  obtain ⟨x, hx⟩ := hq
  obtain ⟨y, hy⟩ := hr
  have hxy : (x : G) * y ≠ y * x := fun h =>
    hqr (by rw [← hx, ← hy]; exact (Pair.starImage_commute_iff hP x y).2 h)
  have h1 := Pair.ncard_muSet_localImages_add_one_le hP hZ hS hd x y
  rw [hx, hy, ncard_muSet_of_mulEquiv φ hφ', MulEquiv.apply_symm_apply,
    MulEquiv.apply_symm_apply, ncard_muSet_eq_of_forall hP hd hμ x.2.1 y.2.1 hxy] at h1
  have h5 := choose_le_ncard_muSet_isSwap h3
  have hc52 : Nat.choose 5 2 = 10 := by decide
  have hc32 : Nat.choose (5 - 2) 2 = 3 := by decide
  have hc22 : Nat.choose (5 - 3) 2 = 1 := by decide
  rw [hk, hc52] at h4 hA hE
  rw [hc22] at h5
  obtain ⟨-, hA30⟩ := arith_ten (by omega) h4 (by rw [hc32] at hA; exact hA)
  apply Pair.not_prime_ncard ⟨hP, hZ, hS⟩ hna
  rw [hE, hA30]
  norm_num

theorem false_of_localO_residual (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hnot : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D) {m : ℕ} (hm : m = 2 ∨ 4 ≤ m)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hQ : 2 ^ (2 * m - 1) < {v | Q v = 1}.ncard)
    (hmod : fischerLinearModel (LocalImages D d)
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) : False := by
  have := Pair.finite hH.pair
  obtain ⟨hk₀, hlam', hμH'⟩ := oModel_params hnd hmod
  have hk : (LocalImages D d).ncard = {v | Q v = 1}.ncard := hk₀
  have hsymp := isSymplecticType_of_o hmod
  have hV : Nat.card (Fin (2 * m) → ZMod 2) = 4 ^ m := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin, pow_mul]
    norm_num
  have hm1 : 1 ≤ m := by omega
  have h4m : 4 ^ m = 4 * 4 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h2m : 2 * 2 ^ (2 * m - 1) = 4 ^ m := by
    rw [← pow_succ', show 2 * m - 1 + 1 = 2 * m by omega, pow_mul]
    norm_num
  have hN : 2 * {v | Q v = 1}.ncard = 4 ^ m + 2 ^ m := by
    have hG : 2 * {v | Q v = 1}.ncard + 2 ^ m = 4 ^ m ∨
        2 * {v | Q v = 1}.ncard = 4 ^ m + 2 ^ m := two_mul_ncard_quadratic Q hnd hV
    rcases hG with h | h
    · have h1 : 2 * {v | Q v = 1}.ncard ≤ 4 ^ m := by
        rw [← h]
        exact Nat.le_add_right _ _
      have h2 : 4 ^ m < 2 * {v | Q v = 1}.ncard := by
        rw [← h2m]
        exact Nat.mul_lt_mul_of_pos_left hQ (by norm_num)
      exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)
    · exact h
  have hlam : ∀ q ∈ LocalImages D d,
      (LocalClass (LocalImages D d) q).ncard = 4 ^ (m - 1) - 1 := fun q hq => by
    have : 4 * ((LocalClass (LocalImages D d) q).ncard + 1) = 4 ^ m := hlam' q hq
    omega
  have hμH : ∀ q ∈ LocalImages D d, ∀ r ∈ LocalImages D d, q * r ≠ r * q →
      (muSet (LocalImages D d) q r).ncard = (3 * 4 ^ (m - 1) - {v | Q v = 1}.ncard) / 2 :=
    fun q hq r hr hqr => by
      have : 4 * ({v | Q v = 1}.ncard + 2 * (muSet (LocalImages D d) q r).ncard) = 3 * 4 ^ m :=
        hμH' q hq r hr hqr
      omega
  obtain ⟨μ, δ, hδ, hμδ, -, h4, hA, hE⟩ := Pair.params_of_local hH hna hnot hd hsymp hlam hμH
  rw [hk] at h4 hA hE
  rcases hm with rfl | hm4
  ·
    norm_num at hN hμδ hA
    have hN10 : {v | Q v = 1}.ncard = 10 := by omega
    rw [hN10] at hμδ hA h4 hE
    obtain ⟨-, hA30⟩ := arith_ten (by omega) h4 hA
    apply Pair.not_prime_ncard hH hna
    rw [hE, hA30]
    norm_num
  · exact minus_arith hm4 hN hδ hμδ h4 hA

theorem params_of_localO6 (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hnot : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hQ : 2 ^ (2 * 3 - 1) < {v | Q v = 1}.ncard)
    (hmod : fischerLinearModel (LocalImages D d)
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) :
    D.ncard = 117 ∧ ∀ c ∈ D, c * d ≠ d * c → (muSet D d c).ncard = 9 ∧
      ∀ f ∈ muSet D d c, (muSet D d c ∩ LocalClass D f).ncard = 6 ∧
        (muSet D d c ∩ {g | g * f ≠ f * g}).ncard = 2 := by
  have := Pair.finite hH.pair
  obtain ⟨hk₀, hlam', hμH'⟩ := oModel_params hnd hmod
  have hk : (LocalImages D d).ncard = {v | Q v = 1}.ncard := hk₀
  have hsymp := isSymplecticType_of_o hmod
  have hV : Nat.card (Fin (2 * 3) → ZMod 2) = 4 ^ 3 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  have hN : 2 * {v | Q v = 1}.ncard = 4 ^ 3 + 2 ^ 3 := by
    have hG : 2 * {v | Q v = 1}.ncard + 2 ^ 3 = 4 ^ 3 ∨
        2 * {v | Q v = 1}.ncard = 4 ^ 3 + 2 ^ 3 := two_mul_ncard_quadratic Q hnd hV
    rcases hG with h | h
    · norm_num at h hQ
      omega
    · exact h
  have hlam : ∀ q ∈ LocalImages D d, (LocalClass (LocalImages D d) q).ncard = 4 ^ 2 - 1 :=
    fun q hq => by
      have : 4 * ((LocalClass (LocalImages D d) q).ncard + 1) = 4 ^ 3 := hlam' q hq
      omega
  have hμH : ∀ q ∈ LocalImages D d, ∀ r ∈ LocalImages D d, q * r ≠ r * q →
      (muSet (LocalImages D d) q r).ncard = (3 * 4 ^ 2 - {v | Q v = 1}.ncard) / 2 :=
    fun q hq r hr hqr => by
      have : 4 * ({v | Q v = 1}.ncard + 2 * (muSet (LocalImages D d) q r).ncard) = 3 * 4 ^ 3 :=
        hμH' q hq r hr hqr
      omega
  obtain ⟨μ, δ, hδ, hμδ, hμ, h4, hA, hE⟩ := Pair.params_of_local hH hna hnot hd hsymp hlam hμH
  rw [hk] at h4 hA hE
  obtain ⟨hμ9, -, hA80⟩ := minus_arith_three hN hδ hμδ h4 hA
  have hN36 : {v | Q v = 1}.ncard = 36 := by omega
  refine ⟨by rw [hE, hN36, hA80], fun c hc hcd => ⟨by rw [hμ c hc hcd, hμ9], fun f hf => ?_⟩⟩
  obtain ⟨hP, hZ, hS⟩ := hH
  have h6 := Pair.ncard_muSet_inter_localClass_eq hP hZ hS hd hc hcd hf hμH
  rw [hN36] at h6
  have hdec := Pair.ncard_muSet_eq_add hP hf
  rw [hμ c hc hcd, hμ9, h6] at hdec
  exact ⟨h6, by omega⟩

section Lines

variable {X : Type} [Group X] {E : Set X}

namespace LocalSymp

theorem ncard_line (hP : Pair X E) {f g : X} (hf : f ∈ E) (hg : g ∈ E) (hgf : g * f ≠ f * g) :
    ({f, g, f * g * f} : Set X).ncard = 3 := by
  obtain ⟨h1, h2', h3, -⟩ := Pair.line_ne hP hf hg fun h => hgf h.symm
  rw [Set.ncard_insert_of_notMem (by
    rintro (h | h)
    · exact h1 h
    · exact h2' h.symm), Set.ncard_pair (Ne.symm h3)]

variable (hP : Pair X E) {M : Set X} (hME : M ⊆ E) (hτ : ∀ f ∈ M, ∀ g ∈ M, f * g * f ∈ M)
  (h2 : ∀ f ∈ M, (M ∩ {g | g * f ≠ f * g}).ncard = 2)
include hP hME hτ h2

theorem inter_far_eq_pair [Finite X] {f g : X} (hf : f ∈ M) (hg : g ∈ M)
    (hgf : g * f ≠ f * g) : M ∩ {h | h * f ≠ f * h} = {g, f * g * f} := by
  have hfE := hME hf
  have hgE := hME hg
  have hfgf : f * g * f * f ≠ f * (f * g * f) := by
    rw [mul_assoc (f * g), Pair.mul_self hP hfE, mul_one, ← mul_assoc, ← mul_assoc,
      Pair.mul_self hP hfE, one_mul]
    exact fun h => hgf h.symm
  have hsub : ({g, f * g * f} : Set X) ⊆ M ∩ {h | h * f ≠ f * h} := by
    rintro x (rfl | rfl)
    · exact ⟨hg, hgf⟩
    · exact ⟨hτ f hf g hg, hfgf⟩
  have hne : g ≠ f * g * f := fun h => hgf ((Pair.mul_mul_eq_self_iff hP hfE g).1 h.symm).symm
  refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
  rw [h2 f hf, Set.ncard_pair hne]

theorem commute_of_notMem_line [Finite X] {f g x : X} (hf : f ∈ M) (hg : g ∈ M)
    (hgf : g * f ≠ f * g) (hx : x ∈ M) (hxL : x ∉ ({f, g, f * g * f} : Set X)) :
    x * f = f * x ∧ x * g = g * x ∧ x * (f * g * f) = f * g * f * x := by
  have hfE := hME hf
  have hgE := hME hg
  have hxf : x * f = f * x := by
    by_contra h
    have := inter_far_eq_pair hP hME hτ h2 hf hg hgf ▸ (show x ∈ M ∩ {h | h * f ≠ f * h} from
      ⟨hx, h⟩)
    rcases this with h' | h'
    · exact hxL (Or.inr (Or.inl h'))
    · exact hxL (Or.inr (Or.inr h'))
  have hxg : x * g = g * x := by
    by_contra h
    have hfg : f * g ≠ g * f := fun h' => hgf h'.symm
    have := inter_far_eq_pair hP hME hτ h2 hg hf hfg ▸ (show x ∈ M ∩ {h | h * g ≠ g * h} from
      ⟨hx, h⟩)
    rcases this with h' | h'
    · exact hxL (Or.inl h')
    · exact hxL (Or.inr (Or.inr (Set.mem_singleton_iff.2
        ((Set.mem_singleton_iff.1 h').trans (Pair.mul_mul_eq hP hfE hgE hfg).symm))))
  exact ⟨hxf, hxg, ((Commute.mul_right hxf hxg).mul_right hxf : Commute x (f * g * f))⟩

end LocalSymp

open LocalSymp in
theorem eq_three_lines [Finite X] (hP : Pair X E) {M : Set X} (hME : M ⊆ E)
    (hτ : ∀ f ∈ M, ∀ g ∈ M, f * g * f ∈ M) (h2 : ∀ f ∈ M, (M ∩ {g | g * f ≠ f * g}).ncard = 2)
    (h9 : M.ncard = 9) :
    ∃ a₁ b₁ a₂ b₂ a₃ b₃ : X, b₁ * a₁ ≠ a₁ * b₁ ∧ b₂ * a₂ ≠ a₂ * b₂ ∧ b₃ * a₃ ≠ a₃ * b₃ ∧
      M = {a₁, b₁, a₁ * b₁ * a₁} ∪ {a₂, b₂, a₂ * b₂ * a₂} ∪ {a₃, b₃, a₃ * b₃ * a₃} ∧
      (∀ x ∈ ({a₁, b₁, a₁ * b₁ * a₁} : Set X), ∀ y ∈ ({a₂, b₂, a₂ * b₂ * a₂} : Set X),
        x * y = y * x) ∧
      (∀ x ∈ ({a₁, b₁, a₁ * b₁ * a₁} : Set X), ∀ y ∈ ({a₃, b₃, a₃ * b₃ * a₃} : Set X),
        x * y = y * x) ∧
      (∀ x ∈ ({a₂, b₂, a₂ * b₂ * a₂} : Set X), ∀ y ∈ ({a₃, b₃, a₃ * b₃ * a₃} : Set X),
        x * y = y * x) := by
  have hline : ∀ f ∈ M, ∃ g ∈ M, g * f ≠ f * g := fun f hf => by
    obtain ⟨g, hg⟩ := Set.nonempty_of_ncard_ne_zero (s := M ∩ {g | g * f ≠ f * g})
      (by rw [h2 f hf]; norm_num)
    exact ⟨g, hg.1, hg.2⟩
  have hLsub : ∀ f ∈ M, ∀ g ∈ M, ({f, g, f * g * f} : Set X) ⊆ M := by
    rintro f hf g hg x (rfl | rfl | rfl)
    · exact hf
    · exact hg
    · exact hτ f hf g hg
  have hcomm : ∀ f ∈ M, ∀ g ∈ M, g * f ≠ f * g → ∀ x ∈ M, x ∉ ({f, g, f * g * f} : Set X) →
      ∀ y ∈ ({f, g, f * g * f} : Set X), x * y = y * x := by
    rintro f hf g hg hgf x hx hxL y (rfl | rfl | rfl)
    · exact (commute_of_notMem_line hP hME hτ h2 hf hg hgf hx hxL).1
    · exact (commute_of_notMem_line hP hME hτ h2 hf hg hgf hx hxL).2.1
    · exact (commute_of_notMem_line hP hME hτ h2 hf hg hgf hx hxL).2.2
  have havoid : ∀ (S : Set X), (∀ x ∈ M \ S, ∀ y ∈ S, x * y = y * x) → ∀ f ∈ M \ S, ∀ g ∈ M,
      g * f ≠ f * g → ({f, g, f * g * f} : Set X) ⊆ M \ S := by
    intro S hS f hf g hg hgf
    have hfS := hf.2
    have hgfgf : f * g * f * f ≠ f * (f * g * f) := by
      rw [mul_assoc (f * g), Pair.mul_self hP (hME hf.1), mul_one, ← mul_assoc, ← mul_assoc,
        Pair.mul_self hP (hME hf.1), one_mul]
      exact fun h => hgf h.symm
    rintro x (rfl | rfl | rfl)
    · exact hf
    · exact ⟨hg, fun hxS => hgf (hS f hf x hxS).symm⟩
    · exact ⟨hτ f hf.1 g hg, fun hxS => hgfgf (hS f hf _ hxS).symm⟩
  obtain ⟨f₁, hf₁⟩ := Set.nonempty_of_ncard_ne_zero (s := M) (by rw [h9]; norm_num)
  obtain ⟨g₁, hg₁, hg₁f₁⟩ := hline f₁ hf₁
  set L₁ : Set X := {f₁, g₁, f₁ * g₁ * f₁}
  have hL₁ := ncard_line hP (hME hf₁) (hME hg₁) hg₁f₁
  have hL₁M := hLsub f₁ hf₁ g₁ hg₁
  have hS₁ : ∀ x ∈ M \ L₁, ∀ y ∈ L₁, x * y = y * x := fun x hx =>
    hcomm f₁ hf₁ g₁ hg₁ hg₁f₁ x hx.1 hx.2
  have hM₁ : (M \ L₁).ncard = 6 := by
    rw [Set.ncard_sdiff hL₁M, h9, hL₁]
  obtain ⟨f₂, hf₂⟩ := Set.nonempty_of_ncard_ne_zero (s := M \ L₁) (by rw [hM₁]; norm_num)
  obtain ⟨g₂, hg₂, hg₂f₂⟩ := hline f₂ hf₂.1
  set L₂ : Set X := {f₂, g₂, f₂ * g₂ * f₂}
  have hL₂ := ncard_line hP (hME hf₂.1) (hME hg₂) hg₂f₂
  have hL₂M := havoid L₁ hS₁ f₂ hf₂ g₂ hg₂ hg₂f₂
  have hS₂ : ∀ x ∈ M \ (L₁ ∪ L₂), ∀ y ∈ L₁ ∪ L₂, x * y = y * x := by
    rintro x hx y (hy | hy)
    · exact hS₁ x ⟨hx.1, fun h => hx.2 (Or.inl h)⟩ y hy
    · exact hcomm f₂ hf₂.1 g₂ hg₂ hg₂f₂ x hx.1 (fun h => hx.2 (Or.inr h)) y hy
  have hM₂ : (M \ (L₁ ∪ L₂)).ncard = 3 := by
    rw [← Set.sdiff_sdiff, Set.ncard_sdiff hL₂M, hM₁, hL₂]
  obtain ⟨f₃, hf₃⟩ := Set.nonempty_of_ncard_ne_zero (s := M \ (L₁ ∪ L₂))
    (by rw [hM₂]; norm_num)
  obtain ⟨g₃, hg₃, hg₃f₃⟩ := hline f₃ hf₃.1
  set L₃ : Set X := {f₃, g₃, f₃ * g₃ * f₃}
  have hL₃ := ncard_line hP (hME hf₃.1) (hME hg₃) hg₃f₃
  have hL₃M := havoid (L₁ ∪ L₂) hS₂ f₃ hf₃ g₃ hg₃ hg₃f₃
  have hL₃eq : L₃ = M \ (L₁ ∪ L₂) :=
    Set.eq_of_subset_of_ncard_le hL₃M (by rw [hM₂, hL₃]) (Set.toFinite _)
  refine ⟨f₁, g₁, f₂, g₂, f₃, g₃, hg₁f₁, hg₂f₂, hg₃f₃, ?_, fun x hx y hy => ?_,
    fun x hx y hy => ?_, fun x hx y hy => ?_⟩
  · show M = L₁ ∪ L₂ ∪ L₃
    rw [hL₃eq, Set.union_sdiff_self, Set.union_eq_self_of_subset_left (Set.union_subset hL₁M
      (fun x hx => (hL₂M hx).1))]
  · exact (hS₁ y (hL₂M hy) x hx).symm
  · exact (hS₂ y (hL₃M hy) x (Or.inl hx)).symm
  · exact (hS₂ y (hL₃M hy) x (Or.inr hx)).symm

end Lines

theorem muSet_eq_three_lines_of_localO6 (hH : Hyp G D) (hna : NonabelianCommutator G)
    (hnot : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D)
    {Q : QuadraticForm (ZMod 2) (Fin (2 * 3) → ZMod 2)}
    (hnd : ∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0)
    (hQ : 2 ^ (2 * 3 - 1) < {v | Q v = 1}.ncard)
    (hmod : fischerLinearModel (LocalImages D d)
      (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
      (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1))
    {c : G} (hc : c ∈ D) (hcd : c * d ≠ d * c) :
    ∃ a₁ b₁ a₂ b₂ a₃ b₃ : G, b₁ * a₁ ≠ a₁ * b₁ ∧ b₂ * a₂ ≠ a₂ * b₂ ∧ b₃ * a₃ ≠ a₃ * b₃ ∧
      muSet D d c = {a₁, b₁, a₁ * b₁ * a₁} ∪ {a₂, b₂, a₂ * b₂ * a₂} ∪ {a₃, b₃, a₃ * b₃ * a₃} ∧
      (∀ x ∈ ({a₁, b₁, a₁ * b₁ * a₁} : Set G), ∀ y ∈ ({a₂, b₂, a₂ * b₂ * a₂} : Set G),
        x * y = y * x) ∧
      (∀ x ∈ ({a₁, b₁, a₁ * b₁ * a₁} : Set G), ∀ y ∈ ({a₃, b₃, a₃ * b₃ * a₃} : Set G),
        x * y = y * x) ∧
      (∀ x ∈ ({a₂, b₂, a₂ * b₂ * a₂} : Set G), ∀ y ∈ ({a₃, b₃, a₃ * b₃ * a₃} : Set G),
        x * y = y * x) := by
  have := Pair.finite hH.pair
  obtain ⟨-, hM⟩ := params_of_localO6 hH hna hnot hd hnd hQ hmod
  obtain ⟨h9, hf⟩ := hM c hc hcd
  exact eq_three_lines hH.pair (fun f hf => hf.1.1) (fun f hf g hg => Pair.mul_mul_mem_muSet
    hH.pair hf hg) (fun f hf' => (hf f hf').2) h9

end CFSG.Fischer.Classification
