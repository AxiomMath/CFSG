module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Step410Act
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step16Main
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cent
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoFoundationFinal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoL3FourE16Check
public import CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace Out410

variable {G : Type} [Group G] [Finite G]

theorem card_le_two_mul_card_inf_normalizer {S₁ R : Subgroup G} {pts : Set (Subgroup G)}
    (hpts : Nat.card pts = 2) (hR : R ∈ pts) (hS : ∀ s ∈ S₁, rightConjugate R s ∈ pts) :
    Nat.card S₁ ≤ 2 * Nat.card (S₁ ⊓ normalizer (R : Set G) : Subgroup G) := by
  classical
  by_cases h : S₁ ≤ normalizer (R : Set G)
  · rw [inf_eq_left.mpr h]
    omega
  obtain ⟨s₀, hs₀, hs₀N⟩ := IsConcreteLE.not_le_iff_exists.mp h
  have hne : rightConjugate R s₀ ≠ R := fun he =>
    hs₀N ((rightConjugate_eq_self_iff R s₀).mp he)
  have hpair : ∀ P ∈ pts, P = R ∨ P = rightConjugate R s₀ := by
    have hsub : ({R, rightConjugate R s₀} : Set (Subgroup G)) ⊆ pts := by
      rintro P (rfl | rfl)
      · exact hR
      · exact hS s₀ hs₀
    have heq : ({R, rightConjugate R s₀} : Set (Subgroup G)) = pts :=
      Set.eq_of_subset_of_ncard_le hsub
        (by rw [← Nat.card_coe_set_eq, hpts, Set.ncard_pair hne.symm]) (Set.toFinite _)
    intro P hP
    rw [← heq] at hP
    exact hP
  set W := S₁ ⊓ normalizer (R : Set G) with hW
  have hsub : (S₁ : Set G) ⊆ (W : Set G) ∪ (fun w => w * s₀) '' (W : Set G) := by
    intro s hs
    by_cases hsN : s ∈ normalizer (R : Set G)
    · exact Or.inl ⟨hs, hsN⟩
    · right
      rcases hpair _ (hS s hs) with h1 | h1
      · exact absurd ((rightConjugate_eq_self_iff R s).mp h1) hsN
      · refine ⟨s * s₀⁻¹, mem_inf.mpr ⟨mul_mem hs (inv_mem hs₀), ?_⟩, by simp⟩
        show s * s₀⁻¹ ∈ normalizer (R : Set G)
        rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul, h1, rightConjugate_mul,
          mul_inv_cancel, rightConjugate_one]
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (W : Set G) ((fun w => w * s₀) '' (W : Set G))
  have h3 : ((fun w => w * s₀) '' (W : Set G)).ncard = (W : Set G).ncard :=
    Set.ncard_image_of_injective _ (mul_left_injective s₀)
  have e1 : Nat.card S₁ = (S₁ : Set G).ncard := Nat.card_coe_set_eq _
  have e2 : Nat.card W = (W : Set G).ncard := Nat.card_coe_set_eq _
  omega

theorem mem_of_mem_centralizer_of_le {A R : Subgroup G}
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRA : R ≤ A) {x : G}
    (hxK : x ∈ centralizer (A : Set G)) {e : ℕ} (hx : x ^ 2 ^ e = 1) : x ∈ R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 (zpowers x) := AS76b.isPGroup_zpowers_of_pow_eq_one hx
  have hxN : zpowers x ≤ normalizer (R : Set G) := by
    rw [zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [mem_centralizer_iff]
    intro r hr
    exact mem_centralizer_iff.mp hxK r (hRA hr)
  have hsup : R ⊔ zpowers x = R :=
    hR.eq_of_le le_sup_left (sup_le hR.le (zpowers_le.mpr hxK))
      (hR.isPGroup.to_sup_of_normal_left' h2 hxN)
  exact hsup ▸ mem_sup_right (mem_zpowers _)

omit [Finite G] in
theorem commute_of_pow_commute {a x : G} {m k : ℕ} (hk : a ^ k = 1) (hmk : Nat.Coprime m k)
    (h : Commute (a ^ m) x) : Commute a x := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · rw [Nat.coprime_zero_right] at hmk
      rw [hmk, pow_one] at h
      exact h
    · rw [pow_one] at hk
      rw [hk]
      exact Commute.one_left x
  obtain ⟨c, hc⟩ := Nat.exists_mul_mod_eq_one_of_coprime hmk (by omega)
  have ha : a = (a ^ m) ^ c := by
    rw [← pow_mul, pow_eq_pow_mod (m * c) hk, hc.2, pow_one]
  rw [ha]
  exact h.pow_left c

theorem commute_of_fpf_three {R : Subgroup G} (hR4 : Nat.card R = 4) {y n : G}
    (hyR : y ∈ normalizer (R : Set G)) (hnR : n ∈ normalizer (R : Set G)) {j e : ℕ}
    (hy3 : y ^ 3 ^ j = 1) (hn2 : n ^ 2 ^ e = 1) (hfpf : ∀ r ∈ R, r ≠ 1 → y * r ≠ r * y)
    (hcomm : ∀ r ∈ R, (y * n * y⁻¹) * r * (y * n * y⁻¹)⁻¹ = n * r * n⁻¹) :
    ∀ r ∈ R, n * r = r * n := by
  classical
  have hκ : ∀ r ∈ R, y * r * y⁻¹ ∈ R := fun r hr => (mem_normalizer_iff.mp hyR r).mp hr
  have hν : ∀ r ∈ R, n * r * n⁻¹ ∈ R := fun r hr => (mem_normalizer_iff.mp hnR r).mp hr
  have hκν : ∀ r ∈ R, y * (n * r * n⁻¹) * y⁻¹ = n * (y * r * y⁻¹) * n⁻¹ := by
    intro r hr
    have := hcomm _ (hκ r hr)
    calc y * (n * r * n⁻¹) * y⁻¹ = (y * n * y⁻¹) * (y * r * y⁻¹) * (y * n * y⁻¹)⁻¹ := by group
      _ = _ := this
  have hmove : ∀ r ∈ R, r ≠ 1 → y * r * y⁻¹ ≠ r := fun r hr hr1 h =>
    hfpf r hr hr1 (by
      calc y * r = y * r * y⁻¹ * y := by group
        _ = r * y := by rw [h])
  have hmove2 : ∀ r ∈ R, r ≠ 1 → y ^ 2 * r * (y ^ 2)⁻¹ ≠ r := by
    intro r hr hr1 h
    have hc : Commute (y ^ 2) r := by
      show y ^ 2 * r = r * y ^ 2
      calc y ^ 2 * r = y ^ 2 * r * (y ^ 2)⁻¹ * y ^ 2 := by group
        _ = r * y ^ 2 := by rw [h]
    have hco : Nat.Coprime 2 (3 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
    exact hfpf r hr hr1 (commute_of_pow_commute hy3 hco hc).eq
  intro r hr
  by_cases hr1 : r = 1
  · rw [hr1, mul_one, one_mul]
  set r₁ := y * r * y⁻¹ with hr₁
  set r₂ := y * r₁ * y⁻¹ with hr₂
  have hr₁R : r₁ ∈ R := hκ r hr
  have hr₂R : r₂ ∈ R := hκ r₁ hr₁R
  have hr₁1 : r₁ ≠ 1 := fun h => hr1 (by
    rw [hr₁, mul_inv_eq_one, mul_eq_left] at h
    exact h)
  have hr₂1 : r₂ ≠ 1 := fun h => hr₁1 (by
    rw [hr₂, mul_inv_eq_one, mul_eq_left] at h
    exact h)
  have hne01 : r₁ ≠ r := hmove r hr hr1
  have hne12 : r₂ ≠ r₁ := hmove r₁ hr₁R hr₁1
  have hne02 : r₂ ≠ r := by
    have : r₂ = y ^ 2 * r * (y ^ 2)⁻¹ := by rw [hr₂, hr₁, sq, mul_inv_rev]; group
    rw [this]
    exact hmove2 r hr hr1
  have hall : ∀ s ∈ R, s = 1 ∨ s = r ∨ s = r₁ ∨ s = r₂ := by
    have hsub : ({1, r, r₁, r₂} : Set G) ⊆ (R : Set G) := by
      rintro s (rfl | rfl | rfl | rfl)
      exacts [one_mem _, hr, hr₁R, hr₂R]
    have hcard : ({1, r, r₁, r₂} : Set G).ncard = 4 := by
      rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_pair hne12.symm]
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hne01.symm, hne02.symm⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => hr1 h.symm, fun h => hr₁1 h.symm, fun h => hr₂1 h.symm⟩
    have heq : ({1, r, r₁, r₂} : Set G) = (R : Set G) :=
      Set.eq_of_subset_of_ncard_le hsub
        (by rw [hcard, ← Nat.card_coe_set_eq, ← hR4]; rfl) (Set.toFinite _)
    intro s hs
    have : s ∈ ({1, r, r₁, r₂} : Set G) := by rw [heq]; exact hs
    simpa using this
  have hr₃ : y * r₂ * y⁻¹ = r := by
    have h3R : y * r₂ * y⁻¹ ∈ R := hκ r₂ hr₂R
    rcases hall _ h3R with h | h | h | h
    · exact absurd (by rw [mul_inv_eq_one, mul_eq_left] at h; exact h) hr₂1
    · exact h
    · exact absurd (by
        have : y * r₂ * y⁻¹ = y * r * y⁻¹ := h
        exact mul_left_cancel (mul_right_cancel this)) hne02
    · exact absurd (by
        have : y * r₂ * y⁻¹ = y * r₁ * y⁻¹ := h
        exact mul_left_cancel (mul_right_cancel this)) hne12
  have hνr : n * r * n⁻¹ ∈ R := hν r hr
  have hνr1 : n * r * n⁻¹ ≠ 1 := fun h => hr1 (by
    rw [mul_inv_eq_one, mul_eq_left] at h
    exact h)
  have hνκ : ∀ s ∈ R, n * (y * s * y⁻¹) * n⁻¹ = y * (n * s * n⁻¹) * y⁻¹ :=
    fun s hs => (hκν s hs).symm
  rcases hall _ hνr with h | h | h | h
  · exact absurd h hνr1
  ·
    calc n * r = n * r * n⁻¹ * n := by group
      _ = r * n := by rw [h]
  ·
    exfalso
    have e1 : n * r₁ * n⁻¹ = r₂ := by rw [hr₁, hνκ r hr, h]
    have e2 : n * r₂ * n⁻¹ = r := by rw [hr₂, hνκ r₁ hr₁R, e1, hr₃]
    have hc : Commute (n ^ 3) r := by
      show n ^ 3 * r = r * n ^ 3
      have : n ^ 3 * r * (n ^ 3)⁻¹ = r := by
        calc n ^ 3 * r * (n ^ 3)⁻¹ = n * (n * (n * r * n⁻¹) * n⁻¹) * n⁻¹ := by
              rw [show n ^ 3 = n * n * n by rw [pow_succ, pow_succ, pow_one]]
              group
          _ = r := by rw [h, e1, e2]
      calc n ^ 3 * r = n ^ 3 * r * (n ^ 3)⁻¹ * n ^ 3 := by group
        _ = r * n ^ 3 := by rw [this]
    have hco : Nat.Coprime 3 (2 ^ e) := Nat.Coprime.pow_right _ (by norm_num)
    have := (commute_of_pow_commute hn2 hco hc).eq
    apply hne01
    calc r₁ = n * r * n⁻¹ := h.symm
      _ = r * n * n⁻¹ := by rw [this]
      _ = r := by group
  ·
    exfalso
    have e1 : n * r₁ * n⁻¹ = r := by rw [hr₁, hνκ r hr, h, hr₃]
    have e2 : n * r₂ * n⁻¹ = r₁ := by rw [hr₂, hνκ r₁ hr₁R, e1]
    have hc : Commute (n ^ 3) r := by
      show n ^ 3 * r = r * n ^ 3
      have : n ^ 3 * r * (n ^ 3)⁻¹ = r := by
        calc n ^ 3 * r * (n ^ 3)⁻¹ = n * (n * (n * r * n⁻¹) * n⁻¹) * n⁻¹ := by
              rw [show n ^ 3 = n * n * n by rw [pow_succ, pow_succ, pow_one]]
              group
          _ = r := by rw [h, e2, e1]
      calc n ^ 3 * r = n ^ 3 * r * (n ^ 3)⁻¹ * n ^ 3 := by group
        _ = r * n ^ 3 := by rw [this]
    have hco : Nat.Coprime 3 (2 ^ e) := Nat.Coprime.pow_right _ (by norm_num)
    have := (commute_of_pow_commute hn2 hco hc).eq
    apply hne02
    calc r₂ = n * r * n⁻¹ := h.symm
      _ = r * n * n⁻¹ := by rw [this]
      _ = r := by group

theorem card_le_of_isPGroup_projectiveSL {k : Type} [Field k] [Finite k] (hk : Nat.card k = 4)
    {X : Subgroup (projectiveSL 3 k)} (hX : IsPGroup 2 X) : Nat.card X ≤ 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, ⟨S₀, hS₀⟩, hcard, -⟩ := FieldFourCover.field_four_central_two_cover_parabolic_normalizers hk
    (MonoidHom.id (projectiveSL 3 k)) Function.surjective_id
    (by rw [MonoidHom.ker_id]; exact bot_le)
    (by
      rw [MonoidHom.ker_id]
      exact FieldFourCover.isElementaryAbelian_of_sq_eq_one fun x hx => by
        rw [mem_bot] at hx
        rw [hx, one_pow])
  rw [MonoidHom.ker_id, card_bot, mul_one, ← hS₀] at hcard
  obtain ⟨S, hS⟩ := hX.exists_le_sylow
  calc Nat.card X ≤ Nat.card S := Subgroup.card_le_of_le hS
    _ = Nat.card S₀ := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    _ = 64 := hcard

end Out410

open Out410 L34Out LinearThreeFourOuter in
theorem step410Outer_of
    (h11 : Step11) : Step410Outer := by
  intro G _ _ A R g E F S₁ Q z hQ hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ, hφ, hker⟩ := hP
  have hF := hQ.setting.frame
  have hL := hQ.setting.type
  have heven := hQ.setting.even
  have hstd := hF.base.hyp.standard
  have hR := hF.sylowR
  have hKte := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hS₁C : S₁ ≤ centralizer ({z} : Set G) := hQ.le_centralizer
  have hcardC : Nat.card (centralizer ({z} : Set G)) = 2 ^ 11 * 21 := by
    rw [card_eq_card_ker_mul φ hφ, hker, card_PGL27,
      Nat.card_congr (subgroupOfEquivOfLe (hQ.le.trans hS₁C)).toEquiv, hQ.card]
    norm_num
  have hS₁C' : IsSylowOf 2 S₁ (centralizer ({z} : Set G)) := hQ.sylow.of_le hS₁C le_top
  have hcS₁ : Nat.card S₁ = 2 ^ 11 := by
    rw [hS₁C'.card_eq, hcardC, factorization_two_pow_mul (by decide)]
  obtain ⟨hRA, -, -, y, hyA, ⟨j, hyj⟩, -, hyR⟩ :=
    step16 RankTwoL3Four.HypII.l34_checkE16 h11 G A R g E F hF heven
  have hy3 : y ^ 3 ^ j = 1 := by rw [← hyj]; exact pow_orderOf_eq_one y
  have h2pts : Nat.card (pointsIn R (E ⊓ F)) = 2 := by
    rcases card_pointsIn_inf RankTwoL3Four.HypII.l34_checkE16 h11 hF hL with h | h
    · exact h
    · exact absurd h (step16NotFourPoints RankTwoL3Four.HypII.l34_checkE16 h11 G A R g E F hF
        heven)
  have hR1 : R ≠ ⊥ := by
    intro h
    have := hF.cardR
    rw [h, Subgroup.card_bot] at this
    omega
  have hNRA : normalizer (R : Set G) ≤ normalizer (A : Set G) := by
    rw [← hNK]
    exact normalizer_two_subgroup_le _ _ hKte hR.isPGroup hR.le hR1
  have hRK : ∀ r ∈ R, ∀ a ∈ A, a * r = r * a := fun r hr a ha =>
    mem_centralizer_iff.mp (hR.le hr) a ha
  have hNAR : normalizer (A : Set G) ≤ normalizer (R : Set G) := by
    intro x hx
    have hxK : x ∈ normalizer (centralizer (A : Set G) : Set G) := by rw [hNK]; exact hx
    have hle : rightConjugate R x ≤ R := by
      intro u hu
      rw [mem_rightConjugate_iff] at hu
      have huK : u ∈ centralizer (A : Set G) := by
        have := (mem_normalizer_iff.mp (inv_mem hxK) (x * u * x⁻¹)).mp (hR.le hu)
        simpa [mul_assoc] using this
      obtain ⟨e, he⟩ := (hR.isPGroup.to_le le_rfl) ⟨x * u * x⁻¹, hu⟩
      have he' : u ^ 2 ^ e = 1 := by
        have h1 : (x * u * x⁻¹) ^ 2 ^ e = 1 := congrArg Subtype.val he
        rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h1
        exact h1
      exact mem_of_mem_centralizer_of_le hR hRA huK he'
    rw [← rightConjugate_eq_self_iff]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [rightConjugate_card])
  set W := S₁ ⊓ normalizer (R : Set G) with hWdef
  have hRV : R ≤ E ⊓ F := le_inf hF.R_le_E hF.R_le_F
  have hWcard : 2 ^ 11 ≤ 2 * Nat.card W := by
    rw [← hcS₁]
    refine card_le_two_mul_card_inf_normalizer h2pts ⟨hRV, 1, (rightConjugate_one R).symm⟩
      fun s hs => ⟨?_, s, rfl⟩
    have hsN : s ∈ normalizer ((E ⊓ F : Subgroup G) : Set G) := by
      rw [hF.inf_eq_center]
      exact mem_normalizer_centerIn (hQ.sylowN.le hs)
    have h1 := AschbacherTheorem3.rightConjugate_le_rightConjugate hRV s
    rwa [(rightConjugate_eq_self_iff _ s).mpr hsN] at h1
  have hWN : W ≤ normalizer (A : Set G) := inf_le_right.trans hNRA
  have hW2 : IsPGroup 2 W := hQ.sylow.isPGroup.to_le inf_le_left
  have hO := oddCore_le_center hstd.1.1 hstd.1.2
  obtain ⟨cv⟩ := exists_l34Cover hstd.1.1 hL hstd.1.2 (sq_eq_one_of_mem_center hR hF.elemR)
  have hk := cv.card_k
  obtain ⟨T⟩ : Nonempty (Sylow 2 ↥A) := inferInstance
  obtain ⟨φA, hφA, hkerA, -⟩ := cv.exists_std hO T
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  set σ := frobeniusEquiv cv.k 2 with hσdef
  have hσ : ∀ a, σ a = a ^ 2 := fun a => frobeniusEquiv_apply cv.k 2 a
  obtain ⟨Ψ, hΨ⟩ := exists_outerHom hσ hk
  set α := quotCenterAct φA hφA hkerA with hαdef
  set β := fieldAut 3 cv.k σ * dualAut 3 cv.k with hβdef
  have hββ : β * β = 1 := LinearThreeFourFixedNine.beta_mul_beta hσ hk
  have hcentA : ∀ n : ↥(normalizer (A : Set G)), α n = 1 ↔ (n : G) ∈ centralizer (A : Set G) :=
    quotCenterAct_eq_one_iff φA hφA hkerA hstd.1.1
  have hαA : ∀ a : ↥A, α ⟨a, le_normalizer a.2⟩ = MulAut.conj (φA a) :=
    quotCenterAct_of_mem φA hφA hkerA
  have hconj_inj : Function.Injective
      (MulAut.conj : projectiveSL 3 cv.k →* MulAut (projectiveSL 3 cv.k)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro p hp
    have hpc : p ∈ center (projectiveSL 3 cv.k) := by
      rw [mem_center_iff]
      intro x
      have := congrArg (fun γ : MulAut (projectiveSL 3 cv.k) => γ x) (MonoidHom.mem_ker.mp hp)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc x * p = p * x * p⁻¹ * p := by rw [this]
        _ = p * x := by group
    rw [center_projectiveSL_three_eq_bot hk] at hpc
    exact hpc
  set f : ↥W →* MulAut (projectiveSL 3 cv.k) := α.comp (Subgroup.inclusion hWN) with hfdef
  have hker8 : Nat.card (Ψ.comp f).ker ≤ 2 ^ 8 := by
    set K₀ := (Ψ.comp f).ker with hK₀
    set h₀ : ↥K₀ →* MulAut (projectiveSL 3 cv.k) := f.comp K₀.subtype with hh₀
    have h1 := card_eq_card_quotient_mul_card_subgroup h₀.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange h₀).toEquiv] at h1
    have hk1 : Nat.card h₀.ker ≤ 4 := by
      rw [← hF.cardR]
      refine Nat.card_le_card_of_injective
        (fun x => (⟨(((x : ↥K₀) : ↥W) : G), ?_⟩ : ↥R)) fun a b hab => ?_
      · have hx1 : α ⟨((x : ↥K₀) : ↥W), hWN ((x : ↥K₀) : ↥W).2⟩ = 1 := x.2
        have hxK := (hcentA _).mp hx1
        obtain ⟨e, he⟩ := hW2 ((x : ↥K₀) : ↥W)
        exact mem_of_mem_centralizer_of_le hR hRA hxK
          (by simpa using congrArg Subtype.val he)
      · exact Subtype.ext (Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))
    have hk2 : Nat.card h₀.range ≤ 64 := by
      have hle : h₀.range ≤ (MulAut.conj : projectiveSL 3 cv.k →*
          MulAut (projectiveSL 3 cv.k)).range := by
        rintro _ ⟨x, rfl⟩
        rw [← ker_eq_range_conj hσ hk hΨ]
        exact x.2
      have hK02 : IsPGroup 2 ↥K₀ := hW2.to_subgroup K₀
      have hrange2 : IsPGroup 2 h₀.range :=
        hK02.of_surjective h₀.rangeRestrict h₀.rangeRestrict_surjective
      have hcomap : Nat.card (h₀.range.comap MulAut.conj) = Nat.card h₀.range := by
        refine Nat.card_congr (Equiv.ofBijective (fun p => (⟨MulAut.conj (p : _), p.2⟩ :
          ↥h₀.range)) ⟨fun a b hab => Subtype.ext (hconj_inj (congrArg Subtype.val hab)),
            fun q => ?_⟩)
        obtain ⟨p, hp⟩ := hle q.2
        exact ⟨⟨p, by rw [mem_comap, hp]; exact q.2⟩, Subtype.ext hp⟩
      rw [← hcomap]
      exact card_le_of_isPGroup_projectiveSL hk (hrange2.comap_of_injective _ hconj_inj)
    rw [h1]
    calc Nat.card h₀.range * Nat.card h₀.ker ≤ 64 * 4 := Nat.mul_le_mul hk2 hk1
      _ = 2 ^ 8 := by norm_num
  obtain ⟨w, hw⟩ := exists_psi_eq_beta hk hΨ hW2 f (by omega)
  have hwβ : f w * β⁻¹ ∈ (MulAut.conj : projectiveSL 3 cv.k →*
      MulAut (projectiveSL 3 cv.k)).range := by
    rw [← ker_eq_range_conj hσ hk hΨ, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    exact hw
  obtain ⟨p, hp⟩ := hwβ
  obtain ⟨b, rfl⟩ := hφA p
  set n₀ : ↥(normalizer (A : Set G)) := ⟨b, le_normalizer b.2⟩⁻¹ * ⟨w, hWN w.2⟩ with hn₀
  have hαn₀ : α n₀ = β := by
    have hfw : f w = α ⟨w, hWN w.2⟩ := rfl
    rw [hn₀, map_mul, map_inv, hαA, ← hfw, hp]
    group
  obtain ⟨e, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n₀).ne'
  set n := n₀ ^ m with hndef
  have hn2e : n ^ 2 ^ e = 1 := by
    rw [hndef, ← pow_mul, mul_comm, ← hord, pow_orderOf_eq_one]
  have hαn : α n = β := by
    obtain ⟨c, rfl⟩ := hm
    rw [hndef, map_pow, hαn₀, pow_succ, pow_mul, sq, hββ, one_pow, one_mul]
  have hn2eG : (n : G) ^ 2 ^ e = 1 := by
    have := congrArg Subtype.val hn2e
    simpa using this
  have hsqR : ∀ x : ↥(normalizer (A : Set G)), α x * α x = 1 → (x : G) ^ 2 ^ e = 1 →
      (x : G) * x ∈ R := by
    intro x hx hx2
    have hxK : ((x * x : ↥(normalizer (A : Set G))) : G) ∈ centralizer (A : Set G) :=
      (hcentA _).mp (by rw [map_mul]; exact hx)
    refine mem_of_mem_centralizer_of_le hR hRA hxK (e := e) ?_
    rw [← sq, ← pow_mul, mul_comm, pow_mul, hx2, one_pow]
  have hnR : (n : G) * n ∈ R := hsqR n (by rw [hαn, hββ]) hn2eG
  set yN : ↥(normalizer (A : Set G)) := ⟨y, hyA⟩ with hyN
  have hαy3 : α yN ^ 3 ^ j = 1 := by
    rw [← map_pow]
    have : yN ^ 3 ^ j = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  obtain ⟨a, μ, hay⟩ := exists_eq_conj_mul_diag hσ hk hΨ hαy3
  obtain ⟨b', rfl⟩ := hφA a
  have hdβ : conjAut 3 cv.k (LinearThreeFourOuter.diagGL μ) * β =
      β * conjAut 3 cv.k (LinearThreeFourOuter.diagGL μ) := conjAut_diagGL_mul_beta hσ hk μ
  set m₁ : ↥(normalizer (A : Set G)) := ⟨b', le_normalizer b'.2⟩ * n * ⟨b', le_normalizer b'.2⟩⁻¹
    with hm₁
  set m₂ : ↥(normalizer (A : Set G)) := yN * n * yN⁻¹ with hm₂
  have hαm : α m₁ = α m₂ := by
    rw [hm₁, hm₂, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hαA, hαn, hay,
      _root_.mul_inv_rev]
    calc MulAut.conj (φA b') * β * (MulAut.conj (φA b'))⁻¹ =
        MulAut.conj (φA b') * (conjAut 3 cv.k (LinearThreeFourOuter.diagGL μ) * β) *
          ((conjAut 3 cv.k (LinearThreeFourOuter.diagGL μ))⁻¹ * (MulAut.conj (φA b'))⁻¹) := by
          rw [hdβ]
          group
      _ = _ := by group
  have hc : ((m₁⁻¹ * m₂ : ↥(normalizer (A : Set G))) : G) ∈ centralizer (A : Set G) :=
    (hcentA _).mp (by rw [map_mul, map_inv, hαm, inv_mul_cancel])
  set c : G := ((m₁⁻¹ * m₂ : ↥(normalizer (A : Set G))) : G) with hcdef
  have hm₂c : (m₂ : G) = (m₁ : G) * c := by
    have : c = (m₁ : G)⁻¹ * (m₂ : G) := rfl
    rw [this, mul_inv_cancel_left]
  have hm₁G : (m₁ : G) = (b' : G) * n * (b' : G)⁻¹ := rfl
  have hm₂G : (m₂ : G) = y * n * y⁻¹ := rfl
  have hRC : ∀ r ∈ R, ∀ x ∈ centralizer (A : Set G), x * r = r * x := fun r hr x hx =>
    (mem_centralizer_iff.mp hx r (hRA hr)).symm
  have hnRmem : ∀ r ∈ R, (n : G) * r * (n : G)⁻¹ ∈ R := fun r hr =>
    (mem_normalizer_iff.mp (hNAR n.2) r).mp hr
  have hcomm : ∀ r ∈ R, (y * n * y⁻¹) * r * (y * n * y⁻¹)⁻¹ = (n : G) * r * (n : G)⁻¹ := by
    intro r hr
    have h1 : c * r = r * c := (hRC r hr c hc)
    have h2 : (b' : G) * r = r * b' := hRK r hr b' b'.2
    have h3 : (b' : G) * ((n : G) * r * (n : G)⁻¹) = ((n : G) * r * (n : G)⁻¹) * b' :=
      hRK _ (hnRmem r hr) b' b'.2
    rw [← hm₂G, hm₂c, hm₁G]
    calc (b' : G) * n * (b' : G)⁻¹ * c * r * ((b' : G) * n * (b' : G)⁻¹ * c)⁻¹
        = (b' : G) * n * (b' : G)⁻¹ * (c * r) * c⁻¹ * (b' : G) * (n : G)⁻¹ * (b' : G)⁻¹ := by
          group
      _ = (b' : G) * n * ((b' : G)⁻¹ * r * b') * (n : G)⁻¹ * (b' : G)⁻¹ := by
          rw [h1]
          group
      _ = (b' : G) * ((n : G) * r * (n : G)⁻¹) * (b' : G)⁻¹ := by
          rw [show (b' : G)⁻¹ * r * b' = r by rw [mul_assoc, ← h2]; group]
          group
      _ = (n : G) * r * (n : G)⁻¹ := by rw [h3]; group
  have hnC : ∀ r ∈ R, (n : G) * r = r * n :=
    commute_of_fpf_three hF.cardR (hNAR hyA) (hNAR n.2) hy3 hn2eG hyR hcomm
  have hm₁C : ∀ r ∈ R, (m₁ : G) * r = r * m₁ := by
    intro r hr
    rw [hm₁G]
    have h2 : (b' : G) * r = r * b' := hRK r hr b' b'.2
    have h3 : (b' : G)⁻¹ * r = r * (b' : G)⁻¹ := by
      calc (b' : G)⁻¹ * r = (b' : G)⁻¹ * (r * b') * (b' : G)⁻¹ := by group
        _ = (b' : G)⁻¹ * (b' * r) * (b' : G)⁻¹ := by rw [h2]
        _ = r * (b' : G)⁻¹ := by group
    calc (b' : G) * n * (b' : G)⁻¹ * r = (b' : G) * n * ((b' : G)⁻¹ * r) := by group
      _ = (b' : G) * (n * r) * (b' : G)⁻¹ := by rw [h3]; group
      _ = (b' : G) * (r * n) * (b' : G)⁻¹ := by rw [hnC r hr]
      _ = (b' * r) * n * (b' : G)⁻¹ := by group
      _ = r * ((b' : G) * n * (b' : G)⁻¹) := by rw [h2]; group
  have hKdec := centralizer_eq_sup_oddCoreIn_of_le hR hRA
  set O := AS76b.oddCoreIn (centralizer (A : Set G)) with hO'
  have hRO : R ≤ normalizer (O : Set G) :=
    hR.le.trans (AS76b.le_normalizer_oddCoreIn _)
  have hcRO : c ∈ ((R ⊔ O : Subgroup G) : Set G) := by rw [← hKdec]; exact hc
  rw [Subgroup.coe_mul_of_left_le_normalizer_right R O hRO] at hcRO
  obtain ⟨r, hr, o, ho, hro⟩ := hcRO
  have hoC : o ∈ centralizer (A : Set G) := AS76b.oddCoreIn_le _ ho
  have hm₁O : (m₁ : G) ∈ normalizer (O : Set G) := by
    refine AS76b.normalizer_le_normalizer_oddCoreIn _ ?_
    rw [hNK]
    exact m₁.2
  have ho' : (m₁ : G)⁻¹ * o * m₁ ∈ O := by
    have := (mem_normalizer_iff.mp (inv_mem hm₁O) o).mp ho
    simpa using this
  have hsq_eq : (m₁ : G)⁻¹ * (m₁ : G)⁻¹ * ((m₂ : G) * m₂) = ((m₁ : G)⁻¹ * o * m₁) * o := by
    rw [hm₂c, ← hro]
    have h1 : (m₁ : G)⁻¹ * r = r * (m₁ : G)⁻¹ := by
      calc (m₁ : G)⁻¹ * r = (m₁ : G)⁻¹ * (r * m₁) * (m₁ : G)⁻¹ := by group
        _ = (m₁ : G)⁻¹ * (m₁ * r) * (m₁ : G)⁻¹ := by rw [hm₁C r hr]
        _ = r * (m₁ : G)⁻¹ := by group
    have h2 : ((m₁ : G)⁻¹ * o * m₁) * r = r * ((m₁ : G)⁻¹ * o * m₁) :=
      (hRC r hr _ (AS76b.oddCoreIn_le _ ho'))
    have hrr : r * r = 1 := by rw [← sq]; exact hF.elemR.2 r hr
    calc (m₁ : G)⁻¹ * (m₁ : G)⁻¹ * ((m₁ : G) * (r * o) * ((m₁ : G) * (r * o)))
        = ((m₁ : G)⁻¹ * r) * o * m₁ * r * o := by group
      _ = r * (((m₁ : G)⁻¹ * o * m₁) * r) * o := by rw [h1]; group
      _ = r * r * ((m₁ : G)⁻¹ * o * m₁) * o := by rw [h2]; group
      _ = ((m₁ : G)⁻¹ * o * m₁) * o := by rw [hrr, one_mul]
  have hm₂R : (m₂ : G) * m₂ ∈ R := by
    refine hsqR m₂ ?_ ?_
    · rw [hm₂, map_mul, map_mul, map_inv, hαn]
      calc α yN * β * (α yN)⁻¹ * (α yN * β * (α yN)⁻¹) = α yN * (β * β) * (α yN)⁻¹ := by group
        _ = 1 := by rw [hββ]; group
    · rw [hm₂G, conj_pow, hn2eG, mul_one, mul_inv_cancel]
  have hm₁R : (m₁ : G) * m₁ = (n : G) * n := by
    rw [hm₁G]
    have h2 : (b' : G) * ((n : G) * n) = ((n : G) * n) * b' := hRK _ hnR b' b'.2
    calc (b' : G) * n * (b' : G)⁻¹ * ((b' : G) * n * (b' : G)⁻¹)
        = (b' : G) * ((n : G) * n) * (b' : G)⁻¹ := by group
      _ = (n : G) * n := by rw [h2]; group
  have hdiff : (m₁ : G)⁻¹ * (m₁ : G)⁻¹ * ((m₂ : G) * m₂) = 1 := by
    have hmemO : (m₁ : G)⁻¹ * (m₁ : G)⁻¹ * ((m₂ : G) * m₂) ∈ O := by
      rw [hsq_eq]
      exact mul_mem ho' ho
    have hmemR : (m₁ : G)⁻¹ * (m₁ : G)⁻¹ * ((m₂ : G) * m₂) ∈ R := by
      rw [show (m₁ : G)⁻¹ * (m₁ : G)⁻¹ = ((m₁ : G) * m₁)⁻¹ by group, hm₁R]
      exact mul_mem (inv_mem hnR) hm₂R
    have h := AS76b.oddCoreIn_inf_eq_bot (K := centralizer (A : Set G)) hR.isPGroup
    have : (m₁ : G)⁻¹ * (m₁ : G)⁻¹ * ((m₂ : G) * m₂) ∈ O ⊓ R := ⟨hmemO, hmemR⟩
    rw [h, mem_bot] at this
    exact this
  have hnn : (n : G) * n = 1 := by
    have h1 : (m₂ : G) * m₂ = (m₁ : G) * m₁ := by
      have := congrArg (fun x => (m₁ : G) * m₁ * x) hdiff
      simpa [mul_assoc] using this
    rw [hm₁R, hm₂G] at h1
    have h2 : y * ((n : G) * n) = ((n : G) * n) * y := by
      calc y * ((n : G) * n) = y * n * y⁻¹ * (y * n * y⁻¹) * y := by group
        _ = (n : G) * n * y := by rw [h1]
    by_contra hne
    exact hyR _ hnR hne h2
  have htN : (n : G) ∈ normalizer (A : Set G) := n.2
  have ht1 : (n : G) ≠ 1 := by
    intro h
    have h1 : n = 1 := Subtype.ext h
    rw [h1, map_one] at hαn
    exact beta_ne_conj hσ hk hΨ 1 (by rw [map_one]; exact hαn)
  have ht2 : orderOf (n : G) = 2 := orderOf_eq_prime (by rw [sq]; exact hnn) ht1
  have htA : (n : G) ∉ A := by
    intro h
    have h1 : n = ⟨((⟨(n : G), h⟩ : ↥A) : G), le_normalizer (⟨(n : G), h⟩ : ↥A).2⟩ :=
      Subtype.ext rfl
    rw [h1, hαA] at hαn
    exact beta_ne_conj hσ hk hΨ _ hαn
  set eZ := (LinearThreeFourFixedNine.qSub (k := cv.k)).map (proj 3 cv.k) with heZ
  have heZ9 : Nat.card eZ = 9 := LinearThreeFourFixedNine.card_map_proj_qSub hk
  set Pe := eZ.comap φA with hPe
  have hPecard : Nat.card Pe = 9 * Nat.card (center ↥A) := by
    rw [hPe, FieldFourCover.card_comap_of_surjective hφA, heZ9, hkerA]
  set γ := RankTwoAltFive.conjActHom (le_refl (normalizer (A : Set G))) n with hγ
  have hγφ : ∀ x : ↥A, φA (γ x) = α n (φA x) := by
    intro x
    rw [quotCenterAct_apply]
    rfl
  have hfixed : ∀ p ∈ Pe, γ p * p⁻¹ ∈ center ↥A := by
    intro p hp
    rw [← hkerA, MonoidHom.mem_ker, map_mul, map_inv, hγφ, hαn,
      LinearThreeFourFixedNine.beta_fixed hσ hk hp, mul_inv_cancel]
  let ζ : ↥Pe →* ↥(center ↥A) :=
    { toFun := fun p => ⟨γ p * (p : ↥A)⁻¹, hfixed p p.2⟩
      map_one' := by ext; simp
      map_mul' := fun p q => by
        apply Subtype.ext
        show γ ((p : ↥A) * q) * ((p : ↥A) * q)⁻¹ = (γ p * (p : ↥A)⁻¹) * (γ q * (q : ↥A)⁻¹)
        have hc := mem_center_iff.mp (hfixed q q.2) (p : ↥A)⁻¹
        calc γ ((p : ↥A) * q) * ((p : ↥A) * q)⁻¹ = γ p * ((γ q * (q : ↥A)⁻¹) * (p : ↥A)⁻¹) := by
              rw [map_mul]
              group
          _ = γ p * ((p : ↥A)⁻¹ * (γ q * (q : ↥A)⁻¹)) := by rw [hc]
          _ = (γ p * (p : ↥A)⁻¹) * (γ q * (q : ↥A)⁻¹) := by group }
  have h9 : 3 ^ 2 ∣ Nat.card ζ.ker := by
    have h1 := card_eq_card_quotient_mul_card_subgroup ζ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ζ).toEquiv, hPecard] at h1
    obtain ⟨q, hq⟩ := Subgroup.card_subgroup_dvd_card ζ.range
    rw [hq] at h1
    have hpos : 0 < Nat.card ζ.range := Nat.card_pos
    have : Nat.card ζ.ker = 9 * q := by
      have h2 : Nat.card ζ.range * Nat.card ζ.ker = Nat.card ζ.range * (9 * q) := by
        rw [← h1]
        ring
      exact Nat.eq_of_mul_eq_mul_left hpos h2
    rw [this]
    exact Dvd.intro q rfl
  obtain ⟨U₀, hU₀⟩ := Sylow.exists_subgroup_card_pow_prime 3 h9
  set U : Subgroup G := ((U₀.map ζ.ker.subtype).map Pe.subtype).map A.subtype with hU
  have hUcard : Nat.card U = 9 := by
    rw [hU, card_map_of_injective A.subtype_injective, card_map_of_injective Pe.subtype_injective,
      card_map_of_injective ζ.ker.subtype_injective, hU₀]
    norm_num
  have hUt : U ≤ centralizer ({(n : G)} : Set G) := by
    rintro _ ⟨_, ⟨_, ⟨x, -, rfl⟩, rfl⟩, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hx : γ ((x : ↥Pe) : ↥A) * ((x : ↥Pe) : ↥A)⁻¹ = 1 := congrArg Subtype.val x.2
    rw [mul_inv_eq_one] at hx
    have hx' := congrArg Subtype.val hx
    rw [hγ, RankTwoAltFive.conjActHom_apply] at hx'
    simp only [Subgroup.coe_subtype]
    calc (((x : ↥Pe) : ↥A) : G) * n = (n : G) * (((x : ↥Pe) : ↥A) : G) * (n : G)⁻¹ * n := by
          rw [hx']
      _ = (n : G) * (((x : ↥Pe) : ↥A) : G) := by group
  have hAKR : A ⊔ centralizer (A : Set G) ≤ centralizer (R : Set G) := by
    refine sup_le (fun a ha => mem_centralizer_iff.mpr fun r hr => (hRK r hr a ha).symm)
      (fun x hx => mem_centralizer_iff.mpr fun r hr => (hRC r hr x hx).symm)
  have htR : ∀ h : G, h⁻¹ * (n : G) * h ∉ R := by
    intro h hmem
    have hr1 : h⁻¹ * (n : G) * h ≠ 1 := by
      intro h1
      apply ht1
      calc (n : G) = h * (h⁻¹ * (n : G) * h) * h⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have hrr : (h⁻¹ * (n : G) * h) ^ 2 = 1 := by
      rw [sq]
      calc h⁻¹ * (n : G) * h * (h⁻¹ * (n : G) * h) = h⁻¹ * ((n : G) * n) * h := by group
        _ = 1 := by rw [hnn]; group
    have hTC : ∀ x ∈ rightConjugate R h, x * (h⁻¹ * (n : G) * h) = (h⁻¹ * (n : G) * h) * x := by
      intro x hx
      rw [mem_rightConjugate_iff] at hx
      have := hnC _ hx
      calc x * (h⁻¹ * (n : G) * h) = h⁻¹ * ((h * x * h⁻¹) * n) * h := by group
        _ = h⁻¹ * ((n : G) * (h * x * h⁻¹)) * h := by rw [this]
        _ = (h⁻¹ * (n : G) * h) * x := by group
    have hTN : rightConjugate R h ≤ normalizer (A : Set G) := by
      intro x hx
      rw [← hNK]
      exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hKte (hR.le hmem) hr1
        hrr (hTC x hx)
    have hhN : h ∉ normalizer (A : Set G) := by
      intro hh
      apply htA
      have hhR := hNAR hh
      have : (n : G) = h * (h⁻¹ * (n : G) * h) * h⁻¹ := by group
      rw [this]
      exact hRA ((mem_normalizer_iff.mp hhR _).mp hmem)
    have hTsyl := AschbacherTheorem3.isSylowOf_rightConjugate hR h
    have hT1 : rightConjugate R h ≠ ⊥ := by
      intro h1
      have := rightConjugate_card R h
      rw [h1, Subgroup.card_bot, hF.cardR] at this
      omega
    have hT := RankTwoFoundation.lemma33Two G A hF.base.hyp31 R hR h hhN (rightConjugate R h)
      (hTsyl.of_le (le_inf hTsyl.le hTN) inf_le_left) hT1 (hTN.trans hNAR) hTsyl
    have hC : rightConjugate R h⁻¹ ≤ centralizer (R : Set G) := by
      intro x hx
      rw [mem_rightConjugate_iff, inv_inv] at hx
      rw [mem_centralizer_iff]
      intro r hr
      have hu : h⁻¹ * r * h ∈ rightConjugate R h := by
        rw [mem_rightConjugate_iff]
        simpa [mul_assoc] using hr
      have h1 := mem_centralizer_iff.mp (hAKR (hT hu)) _ hx
      calc r * x = h * ((h⁻¹ * x * h) * (h⁻¹ * r * h)) * h⁻¹ := by
            rw [h1]
            group
        _ = x * r := by group
    have hhinvN : h⁻¹ ∉ normalizer (A : Set G) := fun hh => hhN (by simpa using inv_mem hh)
    have h11c := (h11 G A hF.base R hR).2.2 h⁻¹ hhinvN hC
    rw [sup_eq_left.mpr hRA] at h11c
    apply htA
    refine h11c ?_
    rw [mem_rightConjugate_iff, inv_inv]
    exact hmem
  obtain ⟨a, -, ha⟩ := AS76b.exists_conj_mem_of_isSylowOf hQ.sylow (mem_top (n : G)) (n := 1)
    (by rw [pow_one, sq]; exact hnn)
  refine ⟨a * n * a⁻¹, ha, ?_, ⟨rightConjugate U a⁻¹, ?_, by rw [rightConjugate_card, hUcard]⟩,
    fun h hh => htR (a⁻¹ * h) ?_⟩
  · rw [show a * (n : G) * a⁻¹ = a⁻¹⁻¹ * n * a⁻¹ by rw [inv_inv], orderOf_inv_mul_mul, ht2]
  · intro x hx
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have h1 := mem_centralizer_singleton_iff.mp (hUt hx)
    rw [mem_centralizer_singleton_iff]
    calc x * (a * n * a⁻¹) = a * ((a⁻¹ * x * a) * n) * a⁻¹ := by group
      _ = a * ((n : G) * (a⁻¹ * x * a)) * a⁻¹ := by rw [h1]
      _ = a * n * a⁻¹ * x := by group
  · simpa [mul_assoc] using hh

end CFSG.ComponentClassification.AS81

