module

public import CFSG.GH74.Uniqueness.Bender.Linear
public import CFSG.GH74.Uniqueness.Bender.Embedding
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsAlternating

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

variable {K : Type*} [Group K]

theorem IsStronglyEmbedded.normalizer_le [Finite K] {M : Subgroup K} (hM : IsStronglyEmbedded M)
    {V : Subgroup K} (hVM : V ≤ M) (hV2 : IsPGroup 2 V) (hV : V ≠ ⊥) :
    normalizer (V : Set K) ≤ M := fun _ hg =>
  IsStronglyEmbedded.mem_of_conj_mem hM hVM
    (fun v hv => hVM ((Subgroup.mem_normalizer_iff.mp hg v).mp hv)) hV2 hV

theorem le_normalizer_of_forall_conj_mem {J V : Subgroup K}
    (hV : ∀ g ∈ J, ∀ v ∈ V, g * v * g⁻¹ ∈ V) : J ≤ normalizer (V : Set K) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact hV g hg v hv
  · intro hv
    have := hV g⁻¹ (J.inv_mem hg) _ hv
    simpa [mul_assoc] using this

theorem BenderType.exists_le_borel_of_normal
    [Finite K] {n i e : ℕ} (h : BenderType K n i e)
    (J : Subgroup K) (N : Subgroup J) [N.Normal] (hN2 : IsPGroup 2 N) (hN : N ≠ ⊥) :
    ∃ Q : Sylow 2 K, J ≤ borel (Q : Subgroup K) := by
  set V : Subgroup K := N.map J.subtype with hVdef
  have hVcard : Nat.card V = Nat.card N := Subgroup.card_map_of_injective J.subtype_injective
  have hV2 : IsPGroup 2 V := by
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    exact IsPGroup.of_card (hVcard.trans hk)
  have hVne : V ≠ ⊥ := by
    intro hbot
    apply hN
    rw [← Subgroup.card_eq_one] at hbot ⊢
    rw [← hVcard]
    exact hbot
  obtain ⟨Q, hVQ⟩ := hV2.exists_le_sylow
  obtain ⟨t, hc⟩ := h.exists_benderCore Q
  refine ⟨Q, ?_⟩
  have hnorm : J ≤ normalizer (V : Set K) := by
    apply le_normalizer_of_forall_conj_mem
    intro g hg v hv
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * x * ⟨g, hg⟩⁻¹, ?_, ?_⟩
    · exact Normal.conj_mem inferInstance x hx ⟨g, hg⟩
    · simp
  exact hnorm.trans (IsStronglyEmbedded.normalizer_le hc.strong (hVQ.trans (le_borel _)) hV2 hVne)

theorem BenderType.exists_le_borel_of_comm_involutions
    [Finite K] {n i : ℕ}
    (h : BenderType K n i 1) (J : Subgroup K)
    (hcomm : ∀ x ∈ J, ∀ y ∈ J, x * x = 1 → y * y = 1 → x * y = y * x)
    {x₀ : K} (hx₀ : x₀ ∈ J) (hx₀2 : x₀ * x₀ = 1) (hx₀1 : x₀ ≠ 1) :
    Even (Nat.card J) ∧ ∃ Q : Sylow 2 K, J ≤ borel (Q : Subgroup K) := by
  have hord : orderOf x₀ = 2 := by
    apply orderOf_eq_prime _ hx₀1
    rw [sq]; exact hx₀2
  refine ⟨even_iff_two_dvd.mpr (hord ▸ Subgroup.orderOf_dvd_natCard J hx₀), ?_⟩
  have hP : IsPGroup 2 (zpowers x₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord]; simp)
  obtain ⟨Q₀, hQ₀⟩ := hP.exists_le_sylow
  have hx₀Q : x₀ ∈ Q₀ := hQ₀ (Subgroup.mem_zpowers x₀)
  obtain ⟨t, hc⟩ := h.exists_benderCore Q₀
  have hrc := hc.involution_iff.mp ⟨le_borel _ hx₀Q, hord⟩
  have hcen := hc.centralizer_eq_of_e_one hrc.1 hrc.2
  set I : Set K := {y | y ∈ J ∧ y * y = 1} with hI
  have hIQ : I ⊆ (Q₀ : Subgroup K) := by
    intro y hy
    have : y ∈ centralizer ({x₀} : Set K) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hcomm x₀ hx₀ y hy.1 hx₀2 hy.2
    rw [hcen] at this
    exact this
  set V : Subgroup K := Subgroup.closure I with hV
  have hVQ : V ≤ (Q₀ : Subgroup K) := (Subgroup.closure_le _).mpr hIQ
  have hx₀V : x₀ ∈ V := Subgroup.subset_closure ⟨hx₀, hx₀2⟩
  have hVne : V ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hx₀V
    exact hx₀1 hx₀V
  have hV2 : IsPGroup 2 V := IsPGroup.to_le Q₀.isPGroup' hVQ
  have hnorm : J ≤ normalizer (V : Set K) := by
    apply le_normalizer_of_forall_conj_mem
    intro g hg v hv
    induction hv using Subgroup.closure_induction with
    | mem y hy =>
      refine Subgroup.subset_closure ⟨J.mul_mem (J.mul_mem hg hy.1) (J.inv_mem hg), ?_⟩
      have : (g * y * g⁻¹) * (g * y * g⁻¹) = g * (y * y) * g⁻¹ := by group
      rw [this, hy.2]; group
    | one => simp
    | mul a b _ _ ha hb =>
      have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      rw [this]; exact V.mul_mem ha hb
    | inv a _ ha =>
      have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [this]; exact V.inv_mem ha
  exact ⟨Q₀, hnorm.trans
    (IsStronglyEmbedded.normalizer_le hc.strong (hVQ.trans (le_borel _)) hV2 hVne)⟩

section Arithmetic

theorem odd_two_pow_sub_one (m : ℕ) (hm : 1 ≤ m) : Odd (2 ^ m - 1) := by
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  generalize 2 ^ m = a at *
  exact ⟨(a - 2) / 2, by omega⟩

theorem odd_two_pow_add_one (m : ℕ) (hm : 1 ≤ m) : Odd (2 ^ m + 1) := by
  have h2 : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
  generalize 2 ^ m = a at *
  exact ⟨a / 2, by omega⟩

theorem not_sixteen_dvd (n : ℕ) (hn : 1 ≤ n) : ¬ 16 ∣ 2 ^ (2 * n) - 1 := by
  have h2 : 2 ∣ 2 ^ (2 * n) := dvd_pow_self 2 (by omega)
  have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
  generalize 2 ^ (2 * n) = a at *
  omega

theorem even_of_five_dvd (n : ℕ) (h : 5 ∣ 2 ^ (2 * n) - 1) : Even n := by
  by_contra hodd
  obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp hodd
  have h4 : 2 ^ (2 * (2 * k + 1)) = 4 * 16 ^ k := by
    rw [show 2 * (2 * k + 1) = 2 + 4 * k by ring, pow_add, pow_mul]
    norm_num
  have h16 : 16 ^ k % 5 = 1 := by
    rw [Nat.pow_mod]; norm_num
  rw [h4] at h
  have h1 : 1 ≤ 16 ^ k := Nat.one_le_pow _ _ (by norm_num)
  generalize 16 ^ k = a at *
  omega

end Arithmetic

section PSL2Even

open CFSG.BenderSuzuki.External CFSG.BenderSuzuki.MatrixGroups

theorem card_psl2_even (m : ℕ) (hm : 1 ≤ m) :
    Nat.card (PSL2MatrixGroup (GaloisField 2 m)) = 2 ^ m * ((2 ^ m) ^ 2 - 1) := by
  have hKcard : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  have hneg_one : (-1 : GaloisField 2 m) = 1 := CharTwo.neg_eq 1
  have hcenter := huppert614_card_center_of_neg_one_eq_one hneg_one
  have hPSLcard := huppert614_card_psl_mul_center (K := GaloisField 2 m)
  rw [hcenter, mul_one, hKcard] at hPSLcard
  exact hPSLcard

theorem nonempty_pgl2_mulEquiv_psl2 (m : ℕ) (hm : 1 ≤ m) :
    Nonempty (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m) ≃*
      PSL2MatrixGroup (GaloisField 2 m)) := by
  have hcard : Nat.card (PSL2MatrixGroup (GaloisField 2 m)) =
      Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m)) := by
    rw [card_psl2_even m hm, huppertXI13_card_pgl2, GaloisField.card 2 m (by omega)]
  have : Finite (Matrix.ProjGenLinGroup (Fin 2) (GaloisField 2 m)) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  exact ⟨(MulEquiv.ofBijective CFSG.Glauberman.Dickson.h826_pslToPGL
    ((Nat.bijective_iff_injective_and_card CFSG.Glauberman.Dickson.h826_pslToPGL).2
      ⟨CFSG.Glauberman.Dickson.h826_pslToPGL_injective, hcard⟩)).symm⟩

end PSL2Even

section TorusNormalizer

@[expose] def IsTorusNormalizer (n : ℕ) (N : Subgroup K) : Prop :=
  ∃ x w : K, x ≠ 1 ∧ Odd (orderOf x) ∧ w * w = 1 ∧ IsCyclic ↥(centralizer ({x} : Set K)) ∧
    (Nat.card ↥(centralizer ({x} : Set K)) = 2 ^ n - 1 ∨
      Nat.card ↥(centralizer ({x} : Set K)) = 2 ^ n + 1) ∧
    (∀ y ∈ centralizer ({x} : Set K), w * y * w⁻¹ = y⁻¹) ∧
    N = centralizer ({x} : Set K) ⊔ zpowers w ∧
    ∀ R : Subgroup K, R ≤ centralizer ({x} : Set K) → R ≠ ⊥ → normalizer (R : Set K) = N

theorem BenderType.exists_torusNormalizer [Finite K] {n : ℕ} (h : BenderType K n 1 1) {x : K}
    (hx : x ≠ 1) (hxodd : Odd (orderOf x)) :
    ∃ N : Subgroup K, IsTorusNormalizer n N ∧ centralizer ({x} : Set K) ≤ N ∧
      normalizer (zpowers x : Set K) = N := by
  obtain ⟨hcyc, hcard, -, w, hw2, hwinv, hN⟩ := h.linear_odd_element hx hxodd
  have hz : zpowers x ≤ centralizer ({x} : Set K) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr fun a ha => by rw [Set.mem_singleton_iff] at ha; rw [ha]
  have hzne : zpowers x ≠ ⊥ := by
    intro hbot
    rw [Subgroup.zpowers_eq_bot] at hbot
    exact hx hbot
  exact ⟨centralizer ({x} : Set K) ⊔ zpowers w,
    ⟨x, w, hx, hxodd, hw2, hcyc, hcard, hwinv, rfl, hN⟩, le_sup_left, hN _ hz hzne⟩

theorem le_normalizer_zpowers_of_card_eq [Finite K] {J : Subgroup K} {x : K} (hx : x ∈ J)
    (hcard : Nat.card J = 2 * orderOf x) : J ≤ normalizer (zpowers x : Set K) := by
  have hle : zpowers x ≤ J := Subgroup.zpowers_le.mpr hx
  set X : Subgroup J := (zpowers x).subgroupOf J with hX
  have hXcard : Nat.card X = orderOf x := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers]
  have hidx : X.index = 2 := by
    have := X.card_mul_index
    rw [hXcard, hcard] at this
    have hpos : 0 < orderOf x := by
      by_contra h0
      rw [Nat.not_lt, Nat.le_zero] at h0
      rw [h0] at this
      simp at this
      have := Nat.card_pos (α := J)
      omega
    exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  have : X.Normal := Subgroup.normal_of_index_eq_two hidx
  apply le_normalizer_of_forall_conj_mem
  intro g hg v hv
  have hvJ : v ∈ J := hle hv
  have hvX : (⟨v, hvJ⟩ : J) ∈ X := hv
  exact Subgroup.Normal.conj_mem (inferInstance : X.Normal) _ hvX (⟨g, hg⟩ : J)

end TorusNormalizer

section Cases

open CFSG.Glauberman.Dickson CFSG.BenderSuzuki.MatrixGroups

theorem A4_involutions_commute :
    ∀ a b : alternatingGroup (Fin 4), a * a = 1 → b * b = 1 → a * b = b * a := by
  decide

theorem A4_exists_involution : ∃ a : alternatingGroup (Fin 4), a * a = 1 ∧ a ≠ 1 := by
  decide

theorem cyclic_cases {J : Subgroup K} (hcyc : IsCyclic J) (hodd : Odd (Nat.card J)) :
    IsPGroup 2 J ∨ (J ≠ ⊥ ∧ IsCyclic J ∧ Odd (Nat.card J)) := by
  by_cases hJ : J = ⊥
  · left
    apply IsPGroup.of_card (n := 0)
    rw [pow_zero, hJ]
    exact Subgroup.card_bot
  · right
    exact ⟨hJ, hcyc, hodd⟩

theorem BenderType.linear_subgroup_cases
    [Finite K] {n : ℕ} (h : BenderType K n 1 1)
    (J : Subgroup K) :
    IsPGroup 2 J ∨ (J ≠ ⊥ ∧ IsCyclic J ∧ Odd (Nat.card J)) ∨
      (∃ z : ℕ, 3 ≤ z ∧ Odd z ∧ Nat.card J = 2 * z ∧ Nonempty (J ≃* DihedralGroup z)) ∨
      (Even (Nat.card J) ∧ ∃ Q : Sylow 2 K, J ≤ borel (Q : Subgroup K)) ∨
      (∃ m : ℕ, 2 ≤ m ∧ m ∣ n ∧ Nonempty (J ≃* PSL2MatrixGroup (GaloisField 2 m))) ∨
      Nat.card J = 6 := by
  obtain ⟨hn, ⟨e⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSL2Model n) := by
    cases h with
    | linear n hn e => exact ⟨hn, ⟨e⟩⟩
  have hFcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  set J' : Subgroup (PSL2MatrixGroup (GaloisField 2 n)) := J.map e.toMonoidHom with hJ'
  let eJ : J ≃* J' := MulEquiv.subgroupMap e J
  have hcardJ : Nat.card J = Nat.card J' := Nat.card_congr eJ.toEquiv
  have hodd1 : Odd (2 ^ n - 1) := odd_two_pow_sub_one n (by omega)
  have hodd2 : Odd (2 ^ n + 1) := odd_two_pow_add_one n (by omega)
  have hgcd : Nat.gcd (2 ^ n - 1) 2 = 1 := by
    apply Nat.Coprime.symm
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    exact fun h2 => Nat.not_even_iff_odd.mpr hodd1 (even_iff_two_dvd.mpr h2)
  have hOddz : ∀ z : ℕ, (z ∣ (Nat.card (GaloisField 2 n) - 1) /
        Nat.gcd (Nat.card (GaloisField 2 n) - 1) 2 ∨
      z ∣ (Nat.card (GaloisField 2 n) + 1) / Nat.gcd (Nat.card (GaloisField 2 n) - 1) 2) →
      Odd z := by
    intro z hz
    rw [hFcard, hgcd, Nat.div_one, Nat.div_one] at hz
    rcases hz with hz | hz
    · exact Odd.of_dvd_nat hodd1 hz
    · exact Odd.of_dvd_nat hodd2 hz
  have hpg : ∀ k : ℕ, Nat.card J' = 2 ^ k → IsPGroup 2 J := fun k hk =>
    IsPGroup.of_card (hcardJ.trans hk)
  have key : ∀ m : ℕ, m ≠ 0 → m ∣ n → Nonempty (J' ≃* PSL2MatrixGroup (GaloisField 2 m)) →
      (∃ m : ℕ, 2 ≤ m ∧ m ∣ n ∧ Nonempty (J ≃* PSL2MatrixGroup (GaloisField 2 m))) ∨
        Nat.card J = 6 := by
    intro m hm0 hmn ⟨hPSL⟩
    by_cases hm2 : m = 1
    · right
      subst hm2
      rw [hcardJ, Nat.card_congr hPSL.toEquiv, card_psl2_even 1 le_rfl]
      norm_num
    · left
      exact ⟨m, by omega, hmn, ⟨eJ.trans hPSL⟩⟩
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification (p := 2) hFcard J' with
    hEA | ⟨z, hz, hzcard, hcyc⟩ | ⟨z, hz, hzcard, ⟨hD⟩⟩ | ⟨-, ⟨hA4⟩⟩ | ⟨h16, -⟩ |
      ⟨h5, ⟨hA5⟩⟩ | ⟨m, t, ht1, ht2, N, C, hNn, hNe, hNc, hCc, hCcard, hdisj, hsup⟩ |
      ⟨m, hm0, hmn, hPSL⟩ | ⟨m, hm0, hmn, ⟨hPGL⟩⟩
  ·
    left
    obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 J').exists_card_eq
    exact hpg k hk
  ·
    have hoz : Odd z := hOddz z hz
    have hJcyc : IsCyclic J := (MulEquiv.isCyclic eJ).mpr hcyc
    rcases cyclic_cases hJcyc (by rw [hcardJ, hzcard]; exact hoz) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
  ·
    have hoz : Odd z := hOddz z hz
    by_cases hz1 : z = 1
    · left
      apply IsPGroup.of_card (n := 1)
      rw [hcardJ, hzcard, hz1]
      norm_num
    · right; right; left
      refine ⟨z, ?_, hoz, hcardJ.trans hzcard, ⟨eJ.trans hD⟩⟩
      obtain ⟨k, hk⟩ := hoz
      omega
  ·
    right; right; right; left
    let φ : J ≃* alternatingGroup (Fin 4) := eJ.trans hA4
    obtain ⟨a₀, ha₀, ha₀1⟩ := A4_exists_involution
    set x₀ : J := φ.symm a₀ with hx₀
    have hx₀2 : x₀ * x₀ = 1 := by
      rw [hx₀, ← map_mul, ha₀, map_one]
    have hx₀1 : x₀ ≠ 1 := by
      intro h1
      apply ha₀1
      have := congrArg φ h1
      simpa [hx₀] using this
    refine h.exists_le_borel_of_comm_involutions J ?_ (x₀ := (x₀ : K)) x₀.2 ?_ ?_
    · intro x hx y hy hx2 hy2
      have hxJ : (⟨x, hx⟩ : J) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
      have hyJ : (⟨y, hy⟩ : J) * ⟨y, hy⟩ = 1 := Subtype.ext hy2
      have h1 := A4_involutions_commute (φ ⟨x, hx⟩) (φ ⟨y, hy⟩)
        (by rw [← map_mul, hxJ, map_one]) (by rw [← map_mul, hyJ, map_one])
      have h2 : (⟨x, hx⟩ : J) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
        apply φ.injective
        rw [map_mul, map_mul]
        exact h1
      exact congrArg Subtype.val h2
    · exact congrArg Subtype.val hx₀2
    · intro h1
      exact hx₀1 (Subtype.ext h1)
  ·
    exact absurd h16 (not_sixteen_dvd n (by omega))
  ·
    have h5' : 5 ∣ 2 ^ (2 * n) - 1 := by
      rcases h5 with h5 | h5
      · omega
      · exact h5
    have hn2 : 2 ∣ n := even_iff_two_dvd.mp (even_of_five_dvd n h5')
    obtain ⟨e5⟩ := CFSG.ProperTwoGeneratedCore.BenderFacts.nonempty_psl2Binary_two_mulEquiv_alternatingGroup_five
    right; right; right; right; left
    exact ⟨2, le_rfl, hn2, ⟨eJ.trans (hA5.trans e5.symm)⟩⟩
  ·
    by_cases hm : m = 0
    · have hN1 : N = ⊥ := Subgroup.card_eq_one.mp (by rw [hNc, hm]; rfl)
      have hC : C = ⊤ := by
        rw [hN1, bot_sup_eq] at hsup
        exact hsup
      have hJ'cyc : IsCyclic J' := by
        rw [hC] at hCc
        exact (MulEquiv.isCyclic Subgroup.topEquiv).mp hCc
      have hJcard : Nat.card J' = t := by
        rw [← hCcard, hC, Subgroup.card_top]
      have hot : Odd t := by
        rw [hgcd, Nat.div_one] at ht2
        exact Odd.of_dvd_nat hodd1 ht2
      rcases cyclic_cases ((MulEquiv.isCyclic eJ).mpr hJ'cyc)
        (by rw [hcardJ, hJcard]; exact hot) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
    · set NJ : Subgroup J := N.map eJ.symm.toMonoidHom with hNJ
      have : NJ.Normal := hNn.map eJ.symm.toMonoidHom eJ.symm.surjective
      have hNJcard : Nat.card NJ = 2 ^ m := by
        rw [Subgroup.card_map_of_injective eJ.symm.injective, hNc]
      have hNJ2 : IsPGroup 2 NJ := IsPGroup.of_card hNJcard
      have hNJne : NJ ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hNJcard
        have : 1 < 2 ^ m := Nat.one_lt_two_pow hm
        omega
      obtain ⟨Q, hQ⟩ := h.exists_le_borel_of_normal J NJ hNJ2 hNJne
      have heven : Even (Nat.card J) := by
        rw [even_iff_two_dvd]
        have h2 : 2 ∣ Nat.card NJ := by rw [hNJcard]; exact dvd_pow_self 2 hm
        exact dvd_trans h2 (Subgroup.card_subgroup_dvd_card NJ)
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨heven, Q, hQ⟩)))
  ·
    rcases key m hm0 hmn hPSL with h1 | h1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))
  ·
    obtain ⟨ePGL⟩ := nonempty_pgl2_mulEquiv_psl2 m (Nat.one_le_iff_ne_zero.mpr hm0)
    have hmn' : m ∣ n := dvd_trans (dvd_mul_left m 2) hmn
    rcases key m hm0 hmn' ⟨hPGL.trans ePGL⟩ with h1 | h1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))

end Cases

section Main

open CFSG.BenderSuzuki.MatrixGroups

theorem BenderType.exists_odd_element
    [Finite K] {n : ℕ} (h : BenderType K n 1 1) :
    ∃ x : K, x ≠ 1 ∧ Odd (orderOf x) := by
  have h3 : 3 ∣ Nat.card K := by
    rw [h.card_eq]
    exact three_dvd_linear_card n
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨x, ?_, by rw [hx]; decide⟩
  intro h1
  rw [h1, orderOf_one] at hx
  omega

theorem BenderType.torus_of_cyclic [Finite K] {n : ℕ} (h : BenderType K n 1 1) {J : Subgroup K}
    (hJ : J ≠ ⊥) (hcyc : IsCyclic J) (hodd : Odd (Nat.card J)) :
    ∃ N : Subgroup K, IsTorusNormalizer n N ∧ J ≤ N := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg1 : (g : K) ≠ 1 := by
    intro h1
    apply hJ
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    have : (⟨y, hy⟩ : J) = 1 := by
      rw [← hk]
      have : g = 1 := Subtype.ext h1
      rw [this, one_zpow]
    exact congrArg Subtype.val this
  have hord : orderOf (g : K) = Nat.card J := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨N, hN, hcent, -⟩ := h.exists_torusNormalizer hg1 (hord ▸ hodd)
  refine ⟨N, hN, fun y hy => hcent ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have hyk : y = (g : K) ^ k := by
    have := congrArg Subtype.val hk.symm
    simpa using this
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rw [Set.mem_singleton_iff] at ha
  rw [ha, hyk]
  exact ((Commute.refl (g : K)).zpow_right k).eq

theorem BenderType.torus_of_normalizes [Finite K] {n : ℕ} (h : BenderType K n 1 1) {J : Subgroup K}
    {x : K} (hx : x ∈ J) (hx1 : x ≠ 1) (hxo : Odd (orderOf x))
    (hcard : Nat.card J = 2 * orderOf x) :
    ∃ N : Subgroup K, IsTorusNormalizer n N ∧ J ≤ N := by
  obtain ⟨N, hN, -, hnorm⟩ := h.exists_torusNormalizer hx1 hxo
  exact ⟨N, hN, hnorm ▸ le_normalizer_zpowers_of_card_eq hx hcard⟩

theorem exists_le_borel_of_isPGroup [Finite K] {J : Subgroup K} (hJ : IsPGroup 2 J) :
    ∃ Q : Sylow 2 K, J ≤ borel (Q : Subgroup K) := by
  obtain ⟨Q, hQ⟩ := hJ.exists_le_sylow
  exact ⟨Q, hQ.trans (le_borel _)⟩

theorem BenderType.linear_subgroup_type_B [Finite K] {n : ℕ} (h : BenderType K n 1 1)
    (J : Subgroup K)
    (hB : (J ≠ ⊥ ∧ IsCyclic J ∧ Odd (Nat.card J)) ∨
      (∃ z : ℕ, 3 ≤ z ∧ Odd z ∧ Nat.card J = 2 * z ∧ Nonempty (J ≃* DihedralGroup z)) ∨
      Nat.card J = 6) : ∃ N : Subgroup K, IsTorusNormalizer n N ∧ J ≤ N := by
  rcases hB with ⟨hJ, hcyc, hodd⟩ | ⟨z, hz3, hzo, hcard, ⟨φ⟩⟩ | hcard
  · exact h.torus_of_cyclic hJ hcyc hodd
  · set x : J := φ.symm (DihedralGroup.r 1) with hx
    have hord : orderOf (x : K) = z := by
      rw [Subgroup.orderOf_coe, hx, MulEquiv.orderOf_eq]
      exact DihedralGroup.orderOf_r_one
    refine h.torus_of_normalizes x.2 ?_ (hord ▸ hzo) (by rw [hord, hcard])
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  · have h3 : 3 ∣ Nat.card J := by rw [hcard]; norm_num
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hord : orderOf (x : K) = 3 := by rw [Subgroup.orderOf_coe, hx]
    refine h.torus_of_normalizes x.2 ?_ (hord ▸ (by decide)) (by rw [hord, hcard])
    intro h1
    rw [h1, orderOf_one] at hord
    omega

theorem BenderType.not_solvable_of_psl2 {J : Subgroup K} [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (φ : J ≃* PSL2MatrixGroup (GaloisField 2 m)) : ¬ Group.IsSolvable J := by
  intro hsolv
  have : Finite (PSL2MatrixGroup (GaloisField 2 m)) := Finite.of_equiv J φ.toEquiv
  have hG : BenderType (PSL2MatrixGroup (GaloisField 2 m)) m 1 1 :=
    BenderType.linear m hm (MulEquiv.refl _)
  have : IsSimpleGroup (PSL2MatrixGroup (GaloisField 2 m)) := hG.isSimple
  have hsolv' : Group.IsSolvable (PSL2MatrixGroup (GaloisField 2 m)) :=
    Group.isSolvable_of_surjective (f := φ.toMonoidHom) φ.surjective
  exact hG.isSimpleBenderGroup.not_commutative (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv')

theorem BenderType.even_card_of_psl2
    {J : Subgroup K} [Finite K] {m : ℕ} (hm : 2 ≤ m)
    (φ : J ≃* PSL2MatrixGroup (GaloisField 2 m)) : Even (Nat.card J) := by
  have : Finite (PSL2MatrixGroup (GaloisField 2 m)) := Finite.of_equiv J φ.toEquiv
  have hG : BenderType (PSL2MatrixGroup (GaloisField 2 m)) m 1 1 :=
    BenderType.linear m hm (MulEquiv.refl _)
  rw [Nat.card_congr φ.toEquiv, hG.card_eq]
  have h2 : Even ((2 : ℕ) ^ m) := (Nat.even_pow' (by omega)).mpr even_two
  exact Even.mul_left (Even.mul_right (by rwa [pow_one]) _) _

theorem BenderType.lemma_3_7
    [Finite K] {n : ℕ} (h : BenderType K n 1 1) (J : Subgroup K)
    (hJ : J ≠ ⊤) :
    (∃ Q : Sylow 2 K, J ≤ borel (Q : Subgroup K)) ∨
      (∃ N : Subgroup K, IsTorusNormalizer n N ∧ J ≤ N) ∨
      (∃ n₀ m : ℕ, 1 ≤ n₀ ∧ 2 ≤ m ∧ n = n₀ * m ∧
        Nonempty (J ≃* PSL2MatrixGroup (GaloisField 2 n₀))) := by
  rcases h.linear_subgroup_cases J with h1 | h1 | h1 | ⟨-, h1⟩ | ⟨m, hm, hmn, ⟨φ⟩⟩ | h1
  · exact Or.inl (exists_le_borel_of_isPGroup h1)
  · exact Or.inr (Or.inl (h.linear_subgroup_type_B J (Or.inl h1)))
  · exact Or.inr (Or.inl (h.linear_subgroup_type_B J (Or.inr (Or.inl h1))))
  · exact Or.inl h1
  · right; right
    have hmne : m ≠ n := by
      rintro rfl
      apply hJ
      apply Subgroup.eq_top_of_card_eq
      have hn2 : 2 ≤ m := hm
      obtain ⟨hn, ⟨e⟩⟩ : 2 ≤ m ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSL2Model m) := by
        cases h with
        | linear n hn e => exact ⟨hn, ⟨e⟩⟩
      rw [Nat.card_congr φ.toEquiv, Nat.card_congr e.toEquiv]
    obtain ⟨k, hk⟩ := hmn
    have hn2 := h.two_le.2
    have hk2 : 2 ≤ k := by
      by_contra hlt
      have : k ≤ 1 := by omega
      interval_cases k
      · omega
      · exact hmne (by omega)
    exact ⟨m, k, by omega, hk2, by rw [hk], ⟨φ⟩⟩
  · exact Or.inr (Or.inl (h.linear_subgroup_type_B J (Or.inr (Or.inr h1))))

theorem BenderType.lemma_3_7_solvable
    [Finite K] {n : ℕ} (h : BenderType K n 1 1)
    (J : Subgroup K) [Group.IsSolvable J] :
    (∃ Q : Sylow 2 K, J ≤ borel (Q : Subgroup K)) ∨
      (∃ N : Subgroup K, IsTorusNormalizer n N ∧ J ≤ N) := by
  rcases h.linear_subgroup_cases J with h1 | h1 | h1 | ⟨-, h1⟩ | ⟨m, hm, hmn, ⟨φ⟩⟩ | h1
  · exact Or.inl (exists_le_borel_of_isPGroup h1)
  · exact Or.inr (h.linear_subgroup_type_B J (Or.inl h1))
  · exact Or.inr (h.linear_subgroup_type_B J (Or.inr (Or.inl h1)))
  · exact Or.inl h1
  · exact absurd ‹Group.IsSolvable J› (BenderType.not_solvable_of_psl2 hm φ)
  · exact Or.inr (h.linear_subgroup_type_B J (Or.inr (Or.inr h1)))

theorem BenderType.lemma_3_7_odd
    [Finite K] {n : ℕ} (h : BenderType K n 1 1)
    (J : Subgroup K) (hodd : Odd (Nat.card J)) :
    ∃ N : Subgroup K, IsTorusNormalizer n N ∧ J ≤ N := by
  rcases h.linear_subgroup_cases J with h1 | h1 | h1 | ⟨h2, -⟩ | ⟨m, hm, hmn, ⟨φ⟩⟩ | h1
  ·
    obtain ⟨k, hk⟩ := h1.exists_card_eq
    have hk0 : k = 0 := by
      by_contra hk0
      have : 2 ∣ Nat.card J := by rw [hk]; exact dvd_pow_self 2 hk0
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    have hbot : J = ⊥ := Subgroup.card_eq_one.mp (by rw [hk, hk0]; rfl)
    subst hbot
    obtain ⟨x, hx1, hxo⟩ := h.exists_odd_element
    obtain ⟨N, hN, -, -⟩ := h.exists_torusNormalizer hx1 hxo
    exact ⟨N, hN, bot_le⟩
  · exact h.linear_subgroup_type_B J (Or.inl h1)
  · exact absurd hodd (by
      obtain ⟨z, -, -, hc, -⟩ := h1
      rw [hc]; simp)
  · exact absurd hodd (Nat.not_odd_iff_even.mpr h2)
  · exact absurd hodd (Nat.not_odd_iff_even.mpr (BenderType.even_card_of_psl2 hm φ))
  · exact h.linear_subgroup_type_B J (Or.inr (Or.inr h1))

end Main

end CFSG.GH74.Uniqueness.Bender
