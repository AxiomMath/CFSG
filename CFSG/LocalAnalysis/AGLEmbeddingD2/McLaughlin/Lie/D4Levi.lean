module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviFam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits CFSG.LieType.RootSystem

section Six

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_central_of_card_six {L : Subgroup G} (h6 : Nat.card L = 6)
    (hnc : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) {z : G} (hzL : z ∈ L)
    (hz : ∀ l ∈ L, z * l = l * z) : z = 1 := by
  by_contra hz1
  obtain ⟨a, ha, b, hb, hab⟩ := hnc
  set Z := Subgroup.center ↥L with hZ
  have hzZ : (⟨z, hzL⟩ : ↥L) ∈ Z := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hz l l.2).symm
  have hZne : Z ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hzZ
    exact hz1 (congrArg Subtype.val hzZ)
  have hZ1 : 1 < Nat.card Z := by
    rw [Subgroup.one_lt_card_iff_ne_bot]
    exact hZne
  have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  rw [h6] at hq
  have hcyc : IsCyclic (↥L ⧸ Z) := by
    have hle : Nat.card (↥L ⧸ Z) ≤ 3 := by
      by_contra hlt
      push Not at hlt
      have : Nat.card (↥L ⧸ Z) * Nat.card Z ≥ 4 * 2 := Nat.mul_le_mul (by omega) hZ1
      omega
    have hpos : 0 < Nat.card (↥L ⧸ Z) := Nat.pos_of_ne_zero (by intro h; rw [h] at hq; omega)
    interval_cases hc : Nat.card (↥L ⧸ Z)
    · have : Subsingleton (↥L ⧸ Z) := (Nat.card_eq_one_iff_unique.mp hc).1
      exact isCyclic_of_subsingleton
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact isCyclic_of_prime_card hc
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact isCyclic_of_prime_card hc
  have := (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' Z)
    (by rw [QuotientGroup.ker_mk'])).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact hab (congrArg Subtype.val this)

theorem eq_bot_of_isPGroup_two_of_card_six {L N : Subgroup G} (h6 : Nat.card L = 6)
    (hnc : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) (hNL : N ≤ L)
    (hnorm : L ≤ Subgroup.normalizer (N : Set G)) (h2 : IsPGroup 2 N) : N = ⊥ := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  have hdvd : Nat.card N ∣ 6 := h6 ▸ Subgroup.card_dvd_of_le hNL
  have hk1 : k ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h4 : 4 ∣ Nat.card N := by
      rw [hk]
      have : (2 : ℕ) ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hlt
      simpa using this
    have := h4.trans hdvd
    omega
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · exact Subgroup.eq_bot_of_card_eq N (by simpa using hk)
  · exfalso
    have hN2 : Nat.card N = 2 := by simpa using hk
    obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
      by_contra hno
      push Not at hno
      have : N = ⊥ := (Subgroup.eq_bot_iff_forall N).mpr hno
      rw [this, Subgroup.card_bot] at hN2
      omega
    apply hn1
    refine eq_one_of_central_of_card_six h6 hnc (hNL hnN) fun l hl => ?_
    have h := conj_eq_self_of_card_two hN2 (g := l)
      (fun x hx => (Subgroup.mem_normalizer_iff.mp (hnorm hl) x).mp hx) hnN
    calc n * l = (l * n * l⁻¹) * l := by rw [h]
      _ = l * n := by group

theorem inf_eq_bot_of_commutes_of_card_six {L₁ L₂ : Subgroup G} (h6 : Nat.card L₁ = 6)
    (hnc : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    L₁ ⊓ L₂ = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hz₁, hz₂⟩
  exact Subgroup.mem_bot.mpr (eq_one_of_central_of_card_six h6 hnc hz₁ fun l hl =>
    (hc l hl z hz₂).symm)

theorem le_normalizer_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    B ≤ Subgroup.normalizer (A : Set G) := fun b hb =>
  Subgroup.mem_normalizer_fintype fun a ha => by
    rw [← h a ha b hb, mul_inv_cancel_right]
    exact ha

omit [Finite G] in
theorem le_normalizer_sup_of {A B X : Subgroup G} (hA : X ≤ Subgroup.normalizer (A : Set G))
    (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun x hx => by
    rw [Subgroup.map_sup]
    exact sup_le_sup (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hx)).le
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hx)).le

omit [Finite G] in
theorem commute_sup_of {A B C : Subgroup G} (hA : ∀ a ∈ A, ∀ c ∈ C, a * c = c * a)
    (hB : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b) : ∀ x ∈ A ⊔ B, ∀ c ∈ C, x * c = c * x := by
  have hle : A ⊔ B ≤ Subgroup.centralizer (C : Set G) :=
    sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr fun c hc => (hA a ha c hc).symm)
      (fun b hb => Subgroup.mem_centralizer_iff.mpr fun c hc => (hB b hb c hc).symm)
  intro x hx c hc
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) c hc).symm

theorem card_sup_le_mul {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  have hc := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer h
  have hpos : 0 < Nat.card (A ⊓ B : Subgroup G) := Nat.card_pos
  calc Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) :=
        Nat.le_mul_of_pos_right _ hpos
    _ = Nat.card A * Nat.card B := hc

theorem card_sup_sup_of_commutes_of_card_six {L₁ L₂ L₃ : Subgroup G}
    (h₁ : Nat.card L₁ = 6) (h₂ : Nat.card L₂ = 6) (h₃ : Nat.card L₃ = 6)
    (hnc₁ : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a) (hnc₃ : ∃ a ∈ L₃, ∃ b ∈ L₃, a * b ≠ b * a)
    (h12 : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (h13 : ∀ a ∈ L₁, ∀ c ∈ L₃, a * c = c * a)
    (h23 : ∀ b ∈ L₂, ∀ c ∈ L₃, b * c = c * b) :
    Nat.card (L₁ ⊔ L₂ ⊔ L₃ : Subgroup G) = 216 := by
  have c12 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (le_normalizer_of_commute h12)
  rw [inf_eq_bot_of_commutes_of_card_six h₁ hnc₁ h12, Subgroup.card_bot, mul_one, h₁, h₂] at c12
  have h123 := commute_sup_of h13 h23
  have c3 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (le_normalizer_of_commute h123)
  rw [inf_comm, inf_eq_bot_of_commutes_of_card_six h₃ hnc₃ fun c hc x hx => (h123 x hx c hc).symm,
    Subgroup.card_bot, mul_one, c12, h₃] at c3
  exact c3

end Six

theorem root_eq_single_of_coord_one {γ : Fin 4 → ℤ}
    (hγ : γ ∈ CFSG.LieType.RootSystem.roots (isFiniteType_cartanD 4) ∅) (h1 : γ 1 = 0) :
    ∃ k : Fin 4, k ≠ 1 ∧ (γ = Pi.single k 1 ∨ γ = -Pi.single k 1) := by
  rw [rootsD_eq (n := 4) (by norm_num)] at hγ
  obtain ⟨i, j, s, t, hij, hs, ht, h⟩ := hγ
  have e0 := congrFun h 0
  have e1 := congrFun h 1
  have e2 := congrFun h 2
  have e3 := congrFun h 3
  simp only [toStdD] at e0 e1 e2 e3
  norm_num at e0 e1 e2 e3
  have key : ((γ 0 = 1 ∨ γ 0 = -1) ∧ γ 2 = 0 ∧ γ 3 = 0) ∨
      (γ 0 = 0 ∧ (γ 2 = 1 ∨ γ 2 = -1) ∧ γ 3 = 0) ∨
      (γ 0 = 0 ∧ γ 2 = 0 ∧ (γ 3 = 1 ∨ γ 3 = -1)) := by
    fin_cases i <;> fin_cases j <;> simp at e0 e1 e2 e3 hij ⊢ <;>
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> omega
  clear h e0 e1 e2 e3
  have hfun : ∀ k : Fin 4, ∀ c : ℤ, (∀ a : Fin 4, γ a = if a = k then c else 0) →
      γ = Pi.single k c := fun k c hk => funext fun a => by
    rw [hk a, Pi.single_apply]
  rcases key with ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩ | ⟨h0, h2, h3⟩
  · refine ⟨0, by decide, ?_⟩
    rcases h0 with h0 | h0
    · left; exact hfun 0 1 fun a => by fin_cases a <;> simp [h0, h1, h2, h3]
    · right; rw [← Pi.single_neg]; exact hfun 0 (-1) fun a => by fin_cases a <;> simp [h0, h1, h2, h3]
  · refine ⟨2, by decide, ?_⟩
    rcases h2 with h2 | h2
    · left; exact hfun 2 1 fun a => by fin_cases a <;> simp [h0, h1, h2, h3]
    · right; rw [← Pi.single_neg]; exact hfun 2 (-1) fun a => by fin_cases a <;> simp [h0, h1, h2, h3]
  · refine ⟨3, by decide, ?_⟩
    rcases h3 with h3 | h3
    · left; exact hfun 3 1 fun a => by fin_cases a <;> simp [h0, h1, h2, h3]
    · right; rw [← Pi.single_neg]; exact hfun 3 (-1) fun a => by fin_cases a <;> simp [h0, h1, h2, h3]

section Radicals

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem posUnipotent_isPGroup_of {p : ℕ} (hext : SteinbergExtras D n H)
    (hX : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) : IsPGroup p (posUnipotent D) :=
  isPGroup_iSup_pos hext hX

theorem borel_le_sup_radicals (hH : ∀ i, H i = ⊥) (I : Set (Fin D.rank)) (Λ : Subgroup K)
    (hroots : ∀ γ ∈ D.roots, 0 < ht γ → (∀ j ∉ I, γ j = 0) → D.rootGroup γ ≤ Λ) :
    borel D H ≤ Λ ⊔ ⨆ j ∈ Iᶜ, radical D j := by
  refine sup_le ?_ ?_
  · exact iSup_le fun k => by rw [hH k]; exact bot_le
  · refine iSup₂_le fun γ hγ => ?_
    by_cases h : ∃ j ∉ I, γ j ≠ 0
    · obtain ⟨j, hj, hγj⟩ := h
      have hpos : 0 < γ j :=
        lt_of_le_of_ne (coord_nonneg_of_ht_pos hγ.1 hγ.2 j) (Ne.symm hγj)
      exact (rootGroup_le_radical hγ.1 hpos).trans (le_sup_of_le_right
        (le_iSup₂_of_le (f := fun j (_ : j ∈ Iᶜ) => radical D j) j hj le_rfl))
    · push Not at h
      exact (hroots γ hγ.1 hγ.2 h).trans le_sup_left

theorem le_normalizer_sup_radicals (I : Set (Fin D.rank)) {X : Subgroup K}
    (h : ∀ j ∉ I, X ≤ Subgroup.normalizer (radical D j : Set K)) :
    X ≤ Subgroup.normalizer ((⨆ j ∈ Iᶜ, radical D j : Subgroup K) : Set K) :=
  CFSG.LieType.Steinberg.le_normalizer_iSup fun j =>
    CFSG.LieType.Steinberg.le_normalizer_iSup fun hj => h j hj

theorem sup_radicals_isPGroup {p : ℕ} (hU : IsPGroup p (posUnipotent D)) (I : Set (Fin D.rank)) :
    IsPGroup p (⨆ j ∈ Iᶜ, radical D j : Subgroup K) :=
  hU.to_le (iSup₂_le fun j _ => radical_le_posUnipotent j)

end Radicals

section Lines

variable {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem not_nine_dvd_card_borel_sup_rankOne_of
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)
    (hH : ∀ k, H k = ⊥) (hU2 : IsPGroup 2 (posUnipotent D)) (i : Fin D.rank)
    (h6 : Nat.card (rankOne D.rootGroup i) = 6) :
    ¬ 9 ∣ Nat.card (borel D H ⊔ rankOne D.rootGroup i : Subgroup K) := by
  set L := rankOne D.rootGroup i with hL
  set U := ⨆ j ∈ ({i} : Set (Fin D.rank))ᶜ, radical D j with hU
  have hB : borel D H ≤ L ⊔ U := borel_le_sup_radicals hH ({i} : Set (Fin D.rank)) L
    fun γ hγ _ h => hct.le_rankOne i γ hγ fun k hk => h k hk
  have hLN : L ≤ Subgroup.normalizer (U : Set K) :=
    le_normalizer_sup_radicals ({i} : Set (Fin D.rank)) fun j hj =>
      rankOne_le_normalizer_radical hext fun h => hj h.symm
  have hle : borel D H ⊔ L ≤ U ⊔ L := sup_le (hB.trans (le_of_eq (sup_comm _ _))) le_sup_right
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hLN
  obtain ⟨m, hm⟩ : ∃ m, Nat.card U = 2 ^ m :=
    IsPGroup.iff_card.mp (sup_radicals_isPGroup hU2 ({i} : Set (Fin D.rank)))
  rw [hm, h6] at hcard
  intro h9
  have h9' : 9 ∣ 2 ^ m * 6 := (h9.trans (Subgroup.card_dvd_of_le hle)).trans (Dvd.intro _ hcard)
  have hcop : Nat.Coprime 9 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
  have := hcop.dvd_of_dvd_mul_left h9'
  omega

theorem exists_line_of_two_nodes (hext : SteinbergExtras D n H) (hH : ∀ k, H k = ⊥)
    (hU2 : IsPGroup 2 (posUnipotent D)) {i j : Fin D.rank}
    (hc : ∀ a ∈ rankOne D.rootGroup i, ∀ b ∈ rankOne D.rootGroup j, a * b = b * a)
    (h6i : Nat.card (rankOne D.rootGroup i) = 6) (h6j : Nat.card (rankOne D.rootGroup j) = 6)
    (hnc : ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    (hroots : ∀ γ ∈ D.roots, 0 < ht γ → (∀ k ∉ ({i, j} : Set (Fin D.rank)), γ k = 0) →
      D.rootGroup γ ≤ rankOne D.rootGroup i ⊔ rankOne D.rootGroup j)
    {A : Subgroup K} (hA : A ≤ borel D H ⊔ (rankOne D.rootGroup i ⊔ rankOne D.rootGroup j))
    {E : Subgroup K} (hEA : E ≤ A) (hE : Nat.card E = 9) :
    ∃ E₁ : Subgroup K, E₁ ≤ E ∧ Nat.card E₁ = 3 ∧
      A ⊓ Subgroup.normalizer (E : Set K) ≤ Subgroup.normalizer (E₁ : Set K) := by
  set Li := rankOne D.rootGroup i with hLi
  set Lj := rankOne D.rootGroup j with hLj
  set U := ⨆ k ∈ ({i, j} : Set (Fin D.rank))ᶜ, radical D k with hU
  have hB : borel D H ≤ (Li ⊔ Lj) ⊔ U :=
    borel_le_sup_radicals hH ({i, j} : Set (Fin D.rank)) (Li ⊔ Lj) hroots
  have hA' : A ≤ (Li ⊔ Lj) ⊔ U := hA.trans (sup_le hB le_sup_left)
  have hLiU : Li ≤ Subgroup.normalizer (U : Set K) :=
    le_normalizer_sup_radicals ({i, j} : Set (Fin D.rank)) fun k hk =>
      rankOne_le_normalizer_radical hext fun h => hk (by subst h; exact Set.mem_insert _ _)
  have hLjU : Lj ≤ Subgroup.normalizer (U : Set K) :=
    le_normalizer_sup_radicals ({i, j} : Set (Fin D.rank)) fun k hk =>
      rankOne_le_normalizer_radical hext fun h => hk (by subst h; exact Set.mem_insert_of_mem _ rfl)
  have hLjLi : Lj ≤ Subgroup.normalizer (Li : Set K) := le_normalizer_of_commute hc
  have hWN : (Li ⊔ Lj) ⊔ U ≤ Subgroup.normalizer ((U ⊔ Li : Subgroup K) : Set K) :=
    sup_le (sup_le (le_sup_right.trans Subgroup.le_normalizer)
      (le_normalizer_sup_of hLjU hLjLi)) (le_sup_left.trans Subgroup.le_normalizer)
  have hAW : A ≤ Subgroup.normalizer ((U ⊔ Li : Subgroup K) : Set K) := hA'.trans hWN
  have hU2' : IsPGroup 2 U := sup_radicals_isPGroup hU2 ({i, j} : Set (Fin D.rank))
  obtain ⟨m, hm⟩ : ∃ m, Nat.card U = 2 ^ m := IsPGroup.iff_card.mp hU2'
  have hUL : U ⊓ Li = ⊥ :=
    eq_bot_of_isPGroup_two_of_card_six h6i hnc inf_le_right
      ((le_inf hLiU Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf)
      (hU2'.to_le inf_le_left)
  have hcW := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hLiU
  rw [hUL, Subgroup.card_bot, mul_one, hm, h6i] at hcW
  have hLL : Nat.card (Li ⊔ Lj : Subgroup K) ≤ 36 := by
    have := card_sup_le_mul hLjLi
    rwa [h6i, h6j] at this
  have hP : Nat.card ((Li ⊔ Lj) ⊔ U : Subgroup K) ≤ 2 ^ m * 36 := by
    rw [sup_comm (Li ⊔ Lj) U]
    refine (card_sup_le_mul (sup_le hLiU hLjU)).trans ?_
    rw [hm]
    exact Nat.mul_le_mul_left _ hLL
  have hc' := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (hEA.trans hAW)
  rw [hcW, hE] at hc'
  have hWE : Nat.card ((U ⊔ Li) ⊔ E : Subgroup K) ≤ 2 ^ m * 36 :=
    (Subgroup.card_le_of_le (sup_le (sup_le le_sup_right (le_sup_left.trans le_sup_left))
      (hEA.trans hA'))).trans hP
  refine ⟨(U ⊔ Li) ⊓ E, inf_le_right, ?_, (le_inf (inf_le_left.trans hAW) inf_le_right).trans
    Subgroup.inf_normalizer_le_normalizer_inf⟩
  have hdvd9 : Nat.card ((U ⊔ Li) ⊓ E : Subgroup K) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hE]
    exact Subgroup.card_dvd_of_le inf_le_right
  have hdvdW : Nat.card ((U ⊔ Li) ⊓ E : Subgroup K) ∣ 2 ^ m * 6 := by
    rw [← hcW]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hpos : 0 < 2 ^ m := by positivity
  have hcop : Nat.Coprime 9 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨k, hk, hke⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd9
  interval_cases k
  · exfalso
    rw [hke, pow_zero, mul_one] at hc'
    rw [hc'] at hWE
    generalize 2 ^ m = u at hWE hpos
    omega
  · simpa using hke
  · exfalso
    rw [hke] at hdvdW
    have := hcop.dvd_of_dvd_mul_left (by simpa using hdvdW : 9 ∣ 2 ^ m * 6)
    omega

end Lines

theorem cartanD_four_leaves {x y : Fin 4} (hxy : x ≠ y) (hx : x ≠ 1) (hy : y ≠ 1) :
    cartanD 4 x y = 0 := by
  fin_cases x <;> fin_cases y <;> simp_all [cartanD]

theorem d4_orthogonal_cases (I : Set (Fin 4))
    (h : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → cartanD 4 i j = 0) :
    (∃ i, I ⊆ {i}) ∨ (∃ x y : Fin 4, x ≠ y ∧ x ≠ 1 ∧ y ≠ 1 ∧ I ⊆ {x, y}) ∨
      ((0 : Fin 4) ∈ I ∧ (2 : Fin 4) ∈ I ∧ (3 : Fin 4) ∈ I) := by
  by_cases h1 : (1 : Fin 4) ∈ I
  · refine Or.inl ⟨1, fun k hk => ?_⟩
    by_contra hk1
    have hc := h 1 h1 k hk (Ne.symm hk1)
    clear h
    fin_cases k <;> simp_all [cartanD]
  · clear h
    by_cases h0 : (0 : Fin 4) ∈ I <;> by_cases h2 : (2 : Fin 4) ∈ I <;>
      by_cases h3 : (3 : Fin 4) ∈ I
    · exact Or.inr (Or.inr ⟨h0, h2, h3⟩)
    · exact Or.inr (Or.inl ⟨0, 2, by decide, by decide, by decide, fun k hk => by
        fin_cases k <;> simp_all⟩)
    · exact Or.inr (Or.inl ⟨0, 3, by decide, by decide, by decide, fun k hk => by
        fin_cases k <;> simp_all⟩)
    · exact Or.inl ⟨0, fun k hk => by fin_cases k <;> simp_all⟩
    · exact Or.inr (Or.inl ⟨2, 3, by decide, by decide, by decide, fun k hk => by
        fin_cases k <;> simp_all⟩)
    · exact Or.inl ⟨2, fun k hk => by fin_cases k <;> simp_all⟩
    · exact Or.inl ⟨3, fun k hk => by fin_cases k <;> simp_all⟩
    · exact Or.inl ⟨0, fun k hk => by fin_cases k <;> simp_all⟩

section Spin

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem three_le_four : 3 ≤ 4 := by norm_num

omit [CharP F 2] in
theorem finite_spinFour : Finite (spinGroup (quadPlus 4 F)) := by
  have : NeZero 4 := ⟨by norm_num⟩
  exact finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := 4) (K := F))

theorem rankOne_spin_facts (hF : Nat.card F = 2) (i : Fin 4) :
    Nat.card (rankOne (plusDatum 4 F three_le_four).rootGroup i) = 6 ∧
    (∃ a ∈ rankOne (plusDatum 4 F three_le_four).rootGroup i,
      ∃ b ∈ rankOne (plusDatum 4 F three_le_four).rootGroup i, a * b ≠ b * a) ∧
    (∃ c ∈ rankOne (plusDatum 4 F three_le_four).rootGroup i, c ≠ 1 ∧ c ^ 3 = 1) := by
  have hn : 3 ≤ 4 := three_le_four
  have := finite_spinFour (F := F)
  set L := rankOne (plusDatum 4 F hn).rootGroup i with hL
  obtain ⟨φ, hφ, hx, hy⟩ := SpinPlus.rankOne (K := F) hn i
  have hpar := SpinPlus.isParametrization (K := F) hn
  have hα : (Pi.single i 1 : Fin 4 → ℤ) ∈ (SpinPlus.Φ 4 F hn).roots :=
    (RootSystem.ofCartan (plusDatum 4 F hn).isFiniteType (plusDatum 4 F hn).divisible).single_mem i
  have hα' : (-Pi.single i 1 : Fin 4 → ℤ) ∈ (SpinPlus.Φ 4 F hn).roots :=
    (RootSystem.ofCartan (plusDatum 4 F hn).isFiniteType (plusDatum 4 F hn).divisible).neg_mem _ hα
  set u := φ (sl2Upper 1) with hu
  set l := φ (sl2Lower 1) with hl
  have huL : u ∈ L := by
    apply (le_sup_left : (plusDatum 4 F hn).rootGroup (Pi.single i 1) ≤ L)
    rw [hu, hx 1]
    exact ((hpar _ hα).1 _).2 ⟨1, rfl⟩
  have hlL : l ∈ L := by
    apply (le_sup_right : (plusDatum 4 F hn).rootGroup (-Pi.single i 1) ≤ L)
    rw [hl, hy 1]
    exact ((hpar _ hα').1 _).2 ⟨1, rfl⟩
  have hnc : u * l ≠ l * u := by
    intro h
    apply sl2_upper_lower_not_commute (F := F)
    apply hφ
    simp only [map_mul]
    rw [← hu, ← hl, mul_assoc, ← h]
  have hu2 : u ^ 2 = 1 := by
    have h11 : (1 : F) + 1 = 0 := by simpa [one_add_one_eq_two] using CharP.cast_eq_zero F 2
    have hx0 : SpinPlus.x 4 F hn (Pi.single i 1) 0 = 1 := by
      have h0 := (hpar _ hα).2.1 0 0
      rw [add_zero] at h0
      exact left_eq_mul.mp h0
    rw [hu, hx 1, sq, ← (hpar _ hα).2.1 1 1, h11, hx0]
  have hu1 : u ≠ 1 := fun h => hnc (by rw [h, one_mul, mul_one])
  have hc1 : u * l ≠ 1 := by
    intro h
    apply hnc
    have hl' : l = u⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [hl', mul_inv_cancel, inv_mul_cancel]
  have hc3 : (u * l) ^ 3 = 1 := by
    rw [hu, hl, ← map_mul, ← map_pow, sl2_upper_lower_cube, map_one]
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd6 : Nat.card L ∣ 6 := card_rankOne_dvd_six_of_sl2 hF hpar hx hy
  have hd2 : 2 ∣ Nat.card L := by
    have := Subgroup.orderOf_dvd_natCard L huL
    rwa [orderOf_eq_prime hu2 hu1] at this
  have hd3 : 3 ∣ Nat.card L := by
    have := Subgroup.orderOf_dvd_natCard L (L.mul_mem huL hlL)
    rwa [orderOf_eq_prime hc3 hc1] at this
  refine ⟨?_, ⟨u, huL, l, hlL, hnc⟩, ⟨u * l, L.mul_mem huL hlL, hc1, hc3⟩⟩
  have h6 : 6 ∣ Nat.card L := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hd2 hd3
  exact Nat.dvd_antisymm hdvd6 h6

omit [Finite F] [CharP F 2] in
theorem spinFour_ct : IsCTGroupDatum
    (coxeterMatrix (plusDatum 4 F three_le_four).isFiniteType).toCoxeterSystem
    (weylAction (plusDatum 4 F three_le_four).isFiniteType) (plusDatum 4 F three_le_four).roots
    (plusDatum 4 F three_le_four).rootGroup (weylD F three_le_four)
    (fun k => (torusD F three_le_four k).range) :=
  plusDatum_isCTGroupDatum three_le_four (plusDatum_iSup_eq_top 4 F three_le_four)

omit [Finite F] [CharP F 2] in
theorem spinFour_extras : SteinbergExtras (plusDatum 4 F three_le_four) (weylD F three_le_four)
    (fun k => (torusD F three_le_four k).range) :=
  plusDatum_steinbergExtras three_le_four

omit [CharP F 2] in
theorem torusD_range_eq_bot (hF : Nat.card F = 2) (k : Fin 4) :
    (torusD F three_le_four k).range = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  have h := torusD_pow_eq_one three_le_four k hg
  rw [hF] at h
  simpa using h

omit [Finite F] in
theorem rootGroup_spinFour_isPGroup {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (plusDatum 4 F three_le_four).roots) :
    IsPGroup 2 ((plusDatum 4 F three_le_four).rootGroup γ) :=
  isPGroup_of_isParametrization (SpinPlus.isParametrization three_le_four) hγ

omit [Finite F] in
theorem posUnipotent_spinFour_isPGroup :
    IsPGroup 2 (posUnipotent (plusDatum 4 F three_le_four)) :=
  posUnipotent_isPGroup_of spinFour_extras fun _ hγ => rootGroup_spinFour_isPGroup hγ

theorem not_nine_dvd_card_borel_sup_rankOne (hF : Nat.card F = 2) (i : Fin 4) :
    ¬ 9 ∣ Nat.card (borel (plusDatum 4 F three_le_four)
      (fun k => (torusD F three_le_four k).range) ⊔
        rankOne (plusDatum 4 F three_le_four).rootGroup i : Subgroup _) := by
  have := finite_spinFour (F := F)
  exact not_nine_dvd_card_borel_sup_rankOne_of spinFour_ct spinFour_extras
    (torusD_range_eq_bot hF) posUnipotent_spinFour_isPGroup i (rankOne_spin_facts hF i).1

theorem spin_lines_core (hF : Nat.card F = 2) {A : Subgroup (spinGroup (quadPlus 4 F))}
    (hBA : borel (plusDatum 4 F three_le_four) (fun k => (torusD F three_le_four k).range) ≤ A)
    (hperf : ∀ V : Subgroup (spinGroup (quadPlus 4 F)), V ≤ A → ⁅V, V⁆ = V → ¬ 3 ∣ Nat.card V)
    (h3 : ∀ V : Subgroup (spinGroup (quadPlus 4 F)), V ≤ A → IsPGroup 3 V → Nat.card V ≤ 9)
    {E : Subgroup (spinGroup (quadPlus 4 F))} (hEA : E ≤ A) (hE : Nat.card E = 9) :
    ∃ E₁ : Subgroup (spinGroup (quadPlus 4 F)), E₁ ≤ E ∧ Nat.card E₁ = 3 ∧
      A ⊓ Subgroup.normalizer (E : Set _) ≤ Subgroup.normalizer (E₁ : Set _) := by
  have := finite_spinFour (F := F)
  have hct := spinFour_ct (F := F)
  have hext := spinFour_extras (F := F)
  have hH := torusD_range_eq_bot hF
  have hU2 := posUnipotent_spinFour_isPGroup (F := F)
  have hfacts := rankOne_spin_facts hF
  have hL := twoLevi_spinPlus hF three_le_four hct hext
  have hAeq := eq_borel_sup_rankOne hct hext hBA
  set D := plusDatum 4 F three_le_four with hD
  have hLA : ∀ i ∈ negIndices D A, rankOne D.rootGroup i ≤ A := fun i hi =>
    rankOne_le_of_mem_negIndices hBA hi
  have hAS : ∀ S : Set (Fin D.rank), negIndices D A ⊆ S →
      A ≤ borel D (fun k => (torusD F three_le_four k).range) ⊔ ⨆ k ∈ S, rankOne D.rootGroup k :=
    fun S hS => hAeq.le.trans (sup_le_sup_left (biSup_mono fun k hk => hS hk) _)
  have hnp : ∀ i ∈ negIndices D A,
      ⁅rankOne D.rootGroup i, rankOne D.rootGroup i⁆ ≠ rankOne D.rootGroup i :=
    fun i hi hp => hperf _ (hLA i hi) hp (by rw [(hfacts i).1]; norm_num)
  have hcart : ∀ i ∈ negIndices D A, ∀ j ∈ negIndices D A, i ≠ j → cartanD 4 i j = 0 := by
    intro i hi j hj hij
    by_contra hA
    rcases hL.pair i j hij hA (hnp i hi) (hnp j hj) with hp | he
    · exact hperf _ (sup_le (hLA i hi) (hLA j hj)) hp
        ((show 3 ∣ Nat.card (rankOne D.rootGroup i) by rw [(hfacts i).1]; norm_num).trans
          (Subgroup.card_dvd_of_le le_sup_left))
    · exact he
  rcases d4_orthogonal_cases (negIndices D A) hcart with ⟨i, hi⟩ |
    ⟨x, y, hxy, hx1, hy1, hsub⟩ | ⟨h0, h2, h3'⟩
  ·
    exfalso
    have hAi : A ≤ borel D (fun k => (torusD F three_le_four k).range) ⊔ rankOne D.rootGroup i :=
      (hAS {i} hi).trans (sup_le_sup_left iSup_singleton.le _)
    apply not_nine_dvd_card_borel_sup_rankOne hF i
    rw [← hE]
    exact Subgroup.card_dvd_of_le (hEA.trans hAi)
  ·
    have hAxy : A ≤ borel D (fun k => (torusD F three_le_four k).range) ⊔
        (rankOne D.rootGroup x ⊔ rankOne D.rootGroup y) :=
      (hAS {x, y} hsub).trans (sup_le_sup_left iSup_pair.le _)
    refine exists_line_of_two_nodes hext hH hU2
      (commutes_rankOne_of_cartan_eq_zero hext hxy (cartanD_four_leaves hxy hx1 hy1))
      (hfacts x).1 (hfacts y).1 (hfacts x).2.1 ?_ hAxy hEA hE
    intro γ hγ _ hvan
    have h1 : γ (1 : Fin 4) = 0 := hvan (1 : Fin 4) fun h =>
      (Set.mem_insert_iff.mp h).elim (fun e => hx1 e.symm) fun e =>
        hy1 (Set.mem_singleton_iff.mp e).symm
    obtain ⟨k, -, hk⟩ := root_eq_single_of_coord_one hγ h1
    have hkxy : k = x ∨ k = y := by
      by_contra h
      push Not at h
      have h0 := hvan k fun hm =>
        (Set.mem_insert_iff.mp hm).elim h.1 fun e => h.2 (Set.mem_singleton_iff.mp e)
      rcases hk with rfl | rfl <;> simp at h0
    have hle : D.rootGroup γ ≤ rankOne D.rootGroup k := by
      rcases hk with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    rcases hkxy with rfl | rfl
    · exact hle.trans le_sup_left
    · exact hle.trans le_sup_right
  ·
    exfalso
    have h216 := card_sup_sup_of_commutes_of_card_six (hfacts 0).1 (hfacts 2).1 (hfacts 3).1
      (hfacts 0).2.1 (hfacts 3).2.1
      (commutes_rankOne_of_cartan_eq_zero (i := (0 : Fin 4)) (j := (2 : Fin 4)) hext
        (by decide : (0 : Fin 4) ≠ 2) (cartanD_four_leaves (by decide) (by decide) (by decide)))
      (commutes_rankOne_of_cartan_eq_zero (i := (0 : Fin 4)) (j := (3 : Fin 4)) hext
        (by decide : (0 : Fin 4) ≠ 3) (cartanD_four_leaves (by decide) (by decide) (by decide)))
      (commutes_rankOne_of_cartan_eq_zero (i := (2 : Fin 4)) (j := (3 : Fin 4)) hext
        (by decide : (2 : Fin 4) ≠ 3) (cartanD_four_leaves (by decide) (by decide) (by decide)))
    have h27 : 3 ^ 3 ∣ Nat.card A := by
      have := Subgroup.card_dvd_of_le
        (sup_le (sup_le (hLA (0 : Fin 4) h0) (hLA (2 : Fin 4) h2)) (hLA (3 : Fin 4) h3'))
      rw [h216] at this
      exact (show 3 ^ 3 ∣ 216 by norm_num).trans this
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime 3 h27
    have hQ' : Nat.card (Q.map A.subtype) = 3 ^ 3 := by
      rw [Subgroup.card_map_of_injective A.subtype_injective, hQ]
    have := h3 _ (Subgroup.map_subtype_le Q) (IsPGroup.of_card hQ')
    rw [hQ'] at this
    norm_num at this

end Spin

end CFSG.AGLEmbeddingD2.McLaughlin.Lie
