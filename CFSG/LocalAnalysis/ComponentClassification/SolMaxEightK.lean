module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightF
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxThreeCent
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxEightJ
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveN
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxTwoA

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_pow_three_pow_eq_map {G P : Type*} [Group G] [Finite G] [Group P] (f : G →* P)
    (x : G) (h3 : orderOf (f x) = 3) :
    ∃ k : ℕ, (∃ a : ℕ, orderOf (x ^ k) = 3 ^ a) ∧ f (x ^ k) = f x := by
  obtain ⟨a, m, hm3, hxm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' 3
    (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hxm
    exact (orderOf_pos x).ne' hxm
  have hy : orderOf (x ^ m) = 3 ^ a := by
    rw [orderOf_pow_of_dvd hm0 (by rw [hxm]; exact Dvd.intro_left _ rfl), hxm,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  rcases (by omega : m % 3 = 1 ∨ m % 3 = 2) with h1 | h2
  · refine ⟨m, ⟨a, hy⟩, ?_⟩
    rw [map_pow, ← pow_mod_orderOf, h3, h1, pow_one]
  · refine ⟨2 * m, ⟨a, ?_⟩, ?_⟩
    · have hcop : (orderOf (x ^ m)).Coprime 2 := by
        rw [hy]
        exact Nat.Coprime.pow_left a (by norm_num)
      rw [mul_comm, pow_mul, Nat.Coprime.orderOf_pow hcop, hy]
    · rw [map_pow, ← pow_mod_orderOf, h3, show 2 * m % 3 = 1 by omega, pow_one]

theorem inf_centralizer_le_zpowers_of_three [Finite X]
    {M H Q : Subgroup X} {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)}
    (hHN : H ≤ normalizer (M : Set X)) (hQ2 : IsPGroup 2 Q) {t s g x : X}
    (hto : orderOf t = 2) (htQ : t ∈ Q) (hst : s * t = t * s)
    (hgC : ∀ y : X, y * s = s * y → g * y * g⁻¹ ∈ H)
    (hd4 : ∀ y ∈ Q, y * s = s * y → y ≠ 1 → ∀ hy : g * y * g⁻¹ ∈ normalizer (M : Set X),
      6 ≤ (ρ ⟨g * y * g⁻¹, hy⟩).support.card)
    (hxs : x * s = s * x) (hxC : ∀ y ∈ Q, y * s = s * y → x * y = y * x) {a : ℕ}
    (hxa : orderOf x = 3 ^ a) (hψx : ρ ⟨g * x * g⁻¹, hHN (hgC x hxs)⟩ ≠ 1) :
    Q ⊓ centralizer ({s} : Set X) ≤ zpowers t := by
  classical
  set C := Q ⊓ centralizer ({s} : Set X) with hCdef
  have hC2 : IsPGroup 2 C := hQ2.to_le inf_le_left
  have hyC : ∀ y : X, y ∈ C ↔ y ∈ Q ∧ y * s = s * y := fun y => by
    rw [hCdef, mem_inf, mem_centralizer_singleton_iff]
  set w := ρ ⟨g * x * g⁻¹, hHN (hgC x hxs)⟩ with hwdef
  have hw3 : w ^ 3 ^ a = 1 := by
    have h1 : (g * x * g⁻¹) ^ 3 ^ a = 1 := by
      rw [conj_pow, ← hxa, pow_orderOf_eq_one]
      group
    have h2 : (⟨g * x * g⁻¹, hHN (hgC x hxs)⟩ : ↥(normalizer (M : Set X))) ^ 3 ^ a = 1 :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact h1)
    rw [hwdef, ← map_pow, h2, map_one]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hw3)
  have hj1 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hψx hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  set u := w ^ 3 ^ i with hudef
  have hu3 : orderOf u = 3 := by
    rw [hudef, orderOf_pow_of_dvd (by positivity) (by rw [hj]; exact pow_dvd_pow 3 (by omega)),
      hj, pow_succ, Nat.mul_div_cancel_left _ (by positivity)]
  let ι : ↥C →* ↥(normalizer (M : Set X)) :=
    ((MulAut.conj g).toMonoidHom.comp C.subtype).codRestrict (normalizer (M : Set X))
      fun y => hHN (hgC y ((hyC y).mp y.2).2)
  let φC : ↥C →* Perm (Fin 9) := ρ.comp ι
  have hφC : ∀ y : ↥C, φC y = ρ ⟨g * y * g⁻¹, hHN (hgC y ((hyC y).mp y.2).2)⟩ := fun y => rfl
  have hφ6 : ∀ y : ↥C, y ≠ 1 → 6 ≤ (φC y).support.card := by
    intro y hy1
    rw [hφC]
    exact hd4 y ((hyC y).mp y.2).1 ((hyC y).mp y.2).2 (fun h => hy1 (Subtype.ext h)) _
  have hinj : Function.Injective φC := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    by_contra hy1
    have h1 := hφ6 y hy1
    rw [hy, Perm.support_one, Finset.card_empty] at h1
    omega
  have hYu : φC.range ≤ centralizer ({u} : Set (Perm (Fin 9))) := by
    rintro _ ⟨y, rfl⟩
    rw [mem_centralizer_singleton_iff, hudef]
    refine (Commute.pow_right ?_ _).eq
    have h1 : x * (y : X) = (y : X) * x := hxC y ((hyC y).mp y.2).1 ((hyC y).mp y.2).2
    show φC y * w = w * φC y
    rw [hφC, hwdef, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change g * y * g⁻¹ * (g * x * g⁻¹) = g * x * g⁻¹ * (g * y * g⁻¹)
    calc g * y * g⁻¹ * (g * x * g⁻¹) = g * ((y : X) * x) * g⁻¹ := by group
      _ = g * (x * (y : X)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  have hY2 : IsPGroup 2 φC.range := hC2.of_equiv (MonoidHom.ofInjective hinj)
  have hY6 : ∀ z ∈ φC.range, z ≠ 1 → 6 ≤ z.support.card := by
    rintro _ ⟨y, rfl⟩ hz
    exact hφ6 y (fun h => hz (by rw [h, map_one]))
  have hYcard := card_le_two_of_centralizer_three hu3 hYu hY2 hY6
  have hCcard : Nat.card C ≤ 2 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact hYcard
  have htC : t ∈ C := (hyC t).mpr ⟨htQ, hst.symm⟩
  have heq : zpowers t = C := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr htC) ?_
    rw [Nat.card_zpowers, hto]
    exact hCcard
  rw [← heq]

theorem signalizerNineEightKernelCentralizerInput_holds
    (hT13 : Sol76T13.SolomonThm13Simple) (hML : Sol78.MaximalityLemmaInput)
    (hSch : SolAltLit.SchurAlternatingMultiplierInput) (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) : SignalizerNineEightKernelCentralizerInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 hρs1 h5 hsA hsplit
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hsH : s ∈ H := hSH hsS
  have hst : s * t = t * s := htZ s hsS
  set C := Q ⊓ centralizer ({s} : Set X) with hCdef
  have hCQ' : C ≤ Q := inf_le_left
  have hC2 : IsPGroup 2 C := hQ2.to_le hCQ'
  have hCN : C ≤ normalizer (M : Set X) := fun y hy => hHN (hQK (hCQ' hy)).1
  have hyC : ∀ y : X, y ∈ C ↔ y ∈ Q ∧ y * s = s * y := fun y => by
    rw [hCdef, mem_inf, mem_centralizer_singleton_iff]
  have hsNC : s ∈ normalizer (C : Set X) :=
    Subgroup.centralizer_le_normalizer (C : Set X)
      (mem_centralizer_iff.mpr fun y hy => ((hyC y).mp hy).2)
  set B := C ⊔ zpowers s with hBdef
  have hB2 : IsPGroup 2 B :=
    hC2.to_sup_of_normal_left' (isPGroup_zpowers_of_mul_self hs2) (zpowers_le.mpr hsNC)
  have hBN : B ≤ normalizer (M : Set X) := sup_le hCN (zpowers_le.mpr (hHN hsH))
  set σ := ρ ⟨s, hHN hsH⟩ with hσdef
  have h8 : σ.support.card = 8 := card_support_eq_eight_of_mem_alternatingGroup hρs2 h5 hsA
  have hbB : ∀ b : Perm (Fin 9), b * σ = σ * b →
      ∀ (y : X) (hy : y ∈ B), b * ρ ⟨y, hBN hy⟩ = ρ ⟨y, hBN hy⟩ * b := by
    intro b hbσ
    set Z : Subgroup X := ((centralizer ({b} : Set (Perm (Fin 9)))).comap ρ).map
      (normalizer (M : Set X)).subtype with hZdef
    have hCZ : C ≤ Z := fun y hy => by
      refine ⟨⟨y, hCN hy⟩, ?_, rfl⟩
      have h1 : ρ ⟨y, hCN hy⟩ = 1 :=
        hρ.eq_one_of_mem_coreActionKernel (by norm_num) (hQK (hCQ' hy)).2
      show ρ ⟨y, hCN hy⟩ ∈ centralizer ({b} : Set (Perm (Fin 9)))
      rw [h1]
      exact one_mem _
    have hsZ : s ∈ Z :=
      ⟨⟨s, hHN hsH⟩, mem_comap.mpr (mem_centralizer_singleton_iff.mpr hbσ.symm), rfl⟩
    intro y hy
    obtain ⟨y', hy', hyy⟩ := sup_le hCZ (zpowers_le.mpr hsZ) hy
    have h1 : (⟨y, hBN hy⟩ : ↥(normalizer (M : Set X))) = y' := Subtype.ext hyy.symm
    rw [h1]
    exact (mem_centralizer_singleton_iff.mp (mem_comap.mp hy')).symm
  let fM : ↥M →* Perm (Fin 9) := ρ.comp (Subgroup.inclusion le_normalizer)
  have hlift : ∀ b : Perm (Fin 9), b ∈ alternatingGroup (Fin 9) → b * σ = σ * b →
      orderOf b = 3 → ∃ x : X, ∃ hxM : x ∈ M, x ∈ centralizer (B : Set X) ∧
        (∃ a : ℕ, orderOf x = 3 ^ a) ∧ ρ ⟨x, le_normalizer hxM⟩ = b := by
    intro b hbA hbσ hb3
    obtain ⟨x₁, hx₁B, hx₁θ⟩ := hρ.exists_lift_of_isPGroup hBN hB2 (b := ⟨b, hbA⟩) (hbB b hbσ)
    have hρx₁ : fM x₁ = b := by
      change ρ ⟨x₁, le_normalizer x₁.2⟩ = b
      rw [hρ.apply_of_mem (by norm_num) x₁, hx₁θ]
    obtain ⟨k, ⟨a, hxa⟩, hxk⟩ := exists_pow_three_pow_eq_map fM x₁ (by rw [hρx₁, hb3])
    refine ⟨((x₁ ^ k : ↥M) : X), (x₁ ^ k).2, ?_, ⟨a, by rw [Subgroup.orderOf_coe, hxa]⟩, ?_⟩
    · rw [Subgroup.coe_pow]
      exact pow_mem hx₁B k
    · change fM (x₁ ^ k) = b
      rw [hxk, hρx₁]
  set σ₀ : Perm (Fin 9) := SixGen.permOf [(0, 1), (2, 3), (4, 5), (6, 7)] with hσ₀def
  have hσ₀2 : σ₀ * σ₀ = 1 := by decide
  have hσ₀8 : σ₀.support.card = 8 := by decide
  have hct : σ.cycleType = σ₀.cycleType := by
    rw [SixGen.cycleType_of_mul_self (k := 4) hρs2 (by norm_num) h8,
      SixGen.cycleType_of_mul_self (k := 4) hσ₀2 (by norm_num) hσ₀8]
  obtain ⟨π, hπ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct.symm)
  set c₁ : Perm (Fin 9) := SixGen.permOf [(2, 4), (4, 6), (3, 5), (5, 7)] with hc₁def
  set c₂ : Perm (Fin 9) := SixGen.permOf [(2, 6), (6, 5), (3, 7), (7, 4)] with hc₂def
  have hc₁3 : c₁ ^ 3 = 1 := by decide
  have hc₂3 : c₂ ^ 3 = 1 := by decide
  have hc₁1 : c₁ ≠ 1 := by decide
  have hc₂1 : c₂ ≠ 1 := by decide
  have hc₁σ : c₁ * σ₀ = σ₀ * c₁ := by decide
  have hc₂σ : c₂ * σ₀ = σ₀ * c₂ := by decide
  have hc₁A : c₁ ∈ alternatingGroup (Fin 9) := by rw [Perm.mem_alternatingGroup]; decide
  have hc₂A : c₂ ∈ alternatingGroup (Fin 9) := by rw [Perm.mem_alternatingGroup]; decide
  have hc₁₂ : c₁ * c₂ * (c₁ * c₂) = 1 := by decide
  have hc₁₂4 : (c₁ * c₂).support.card = 4 := by decide
  have hconj : ∀ c : Perm (Fin 9), c ^ 3 = 1 → c ≠ 1 → c * σ₀ = σ₀ * c →
      c ∈ alternatingGroup (Fin 9) → π * c * π⁻¹ ∈ alternatingGroup (Fin 9) ∧
        π * c * π⁻¹ * σ = σ * (π * c * π⁻¹) ∧ orderOf (π * c * π⁻¹) = 3 := by
    intro c hc3 hc1 hcσ hcA
    refine ⟨(alternatingGroup.normal (α := Fin 9)).conj_mem c hcA π, ?_, ?_⟩
    · rw [← hπ]
      calc π * c * π⁻¹ * (π * σ₀ * π⁻¹) = π * (c * σ₀) * π⁻¹ := by group
        _ = π * (σ₀ * c) * π⁻¹ := by rw [hcσ]
        _ = π * σ₀ * π⁻¹ * (π * c * π⁻¹) := by group
    · refine orderOf_eq_prime (by rw [conj_pow, hc3]; group) fun h => hc1 ?_
      have := congrArg (fun z => π⁻¹ * z * π) h
      simpa [mul_assoc] using this
  obtain ⟨hb₁A, hb₁σ, hb₁3⟩ := hconj c₁ hc₁3 hc₁1 hc₁σ hc₁A
  obtain ⟨hb₂A, hb₂σ, hb₂3⟩ := hconj c₂ hc₂3 hc₂1 hc₂σ hc₂A
  have hb₁₂ : π * c₁ * π⁻¹ * (π * c₂ * π⁻¹) = π * (c₁ * c₂) * π⁻¹ := by group
  have hb₁₂2 : π * (c₁ * c₂) * π⁻¹ * (π * (c₁ * c₂) * π⁻¹) = 1 := by
    rw [show π * (c₁ * c₂) * π⁻¹ * (π * (c₁ * c₂) * π⁻¹) =
      π * (c₁ * c₂ * (c₁ * c₂)) * π⁻¹ by group, hc₁₂]
    group
  have hb₁₂4 : (π * (c₁ * c₂) * π⁻¹).support.card = 4 := by
    rw [Perm.card_support_conj]
    exact hc₁₂4
  obtain ⟨x₁, hx₁M, hx₁B, ⟨a₁, hx₁a⟩, hx₁ρ⟩ := hlift _ hb₁A hb₁σ hb₁3
  obtain ⟨x₂, hx₂M, hx₂B, ⟨a₂, hx₂a⟩, hx₂ρ⟩ := hlift _ hb₂A hb₂σ hb₂3
  have hxs : ∀ x ∈ centralizer (B : Set X), x * s = s * x := fun x hx =>
    (mem_centralizer_iff.mp hx s (mem_sup_right (mem_zpowers s))).symm
  have hxC : ∀ x ∈ centralizer (B : Set X), ∀ y ∈ Q, y * s = s * y → x * y = y * x :=
    fun x hx y hyQ hys =>
      (mem_centralizer_iff.mp hx y (mem_sup_left ((hyC y).mpr ⟨hyQ, hys⟩))).symm
  have hto : orderOf t = 2 := S₀.pair.1.1
  have hCt : centralizer ({t} : Set X) ≤ H := hCQ t htQ hto
  have hts : t = g * s * g⁻¹ := by rw [← hgs]; group
  have hgC : ∀ y : X, y * s = s * y → g * y * g⁻¹ ∈ H := by
    intro y hys
    apply hCt
    rw [mem_centralizer_singleton_iff, hts]
    calc g * y * g⁻¹ * (g * s * g⁻¹) = g * (y * s) * g⁻¹ := by group
      _ = g * (s * y) * g⁻¹ := by rw [hys]
      _ = g * s * g⁻¹ * (g * y * g⁻¹) := by group
  by_cases h₁ : ρ ⟨g * x₁ * g⁻¹, hHN (hgC x₁ (hxs x₁ hx₁B))⟩ = 1
  swap
  · exact inf_centralizer_le_zpowers_of_three hHN hQ2 hto htQ hst hgC hd4 (hxs x₁ hx₁B)
      (hxC x₁ hx₁B) hx₁a h₁
  by_cases h₂ : ρ ⟨g * x₂ * g⁻¹, hHN (hgC x₂ (hxs x₂ hx₂B))⟩ = 1
  swap
  · exact inf_centralizer_le_zpowers_of_three hHN hQ2 hto htQ hst hgC hd4 (hxs x₂ hx₂B)
      (hxC x₂ hx₂B) hx₂a h₂
  exfalso
  set y := x₁ * x₂ with hydef
  have hyM : y ∈ M := M.mul_mem hx₁M hx₂M
  have hyB : y ∈ centralizer (B : Set X) := mul_mem hx₁B hx₂B
  have hyρ : ρ ⟨y, le_normalizer hyM⟩ = π * (c₁ * c₂) * π⁻¹ := by
    have h1 : (⟨y, le_normalizer hyM⟩ : ↥(normalizer (M : Set X))) =
        ⟨x₁, le_normalizer hx₁M⟩ * ⟨x₂, le_normalizer hx₂M⟩ := rfl
    rw [h1, map_mul, hx₁ρ, hx₂ρ, hb₁₂]
  obtain ⟨c, m, hmodd, hym⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  set f := y ^ m with hfdef
  have hfM : f ∈ M := M.pow_mem hyM m
  have hfB : f ∈ centralizer (B : Set X) := pow_mem hyB m
  have hfρ : ρ ⟨f, le_normalizer hfM⟩ = π * (c₁ * c₂) * π⁻¹ := by
    have h1 : (⟨f, le_normalizer hfM⟩ : ↥(normalizer (M : Set X))) =
        ⟨y, le_normalizer hyM⟩ ^ m := rfl
    rw [h1, map_pow, hyρ]
    obtain ⟨r, rfl⟩ := hmodd
    rw [pow_succ, pow_mul, sq, hb₁₂2, one_pow, one_mul]
  have hf2c : f ^ 2 ^ c = 1 := by rw [hfdef, ← pow_mul, mul_comm, ← hym, pow_orderOf_eq_one]
  have hf2 : f * f = 1 := by
    have hff : f * f ∈ M := M.mul_mem hfM hfM
    have hρff : ρ ⟨f * f, le_normalizer hff⟩ = 1 := by
      have h1 : (⟨f * f, le_normalizer hff⟩ : ↥(normalizer (M : Set X))) =
          ⟨f, le_normalizer hfM⟩ * ⟨f, le_normalizer hfM⟩ := rfl
      rw [h1, map_mul, hfρ, hb₁₂2]
    have hodd := odd_orderOf_of_rho_eq_one hρ hff hρff
    have h2 : (f * f) ^ 2 ^ c = 1 := by
      rw [← sq, ← pow_mul, mul_comm, pow_mul, hf2c, one_pow]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2)
    rcases j with _ | j
    · rw [pow_zero] at hj
      exact orderOf_eq_one_iff.mp hj
    · rw [hj, pow_succ] at hodd
      exact absurd hodd (by simp [Nat.odd_mul])
  have hf4 : (ρ ⟨f, le_normalizer hfM⟩).support.card = 4 := by rw [hfρ, hb₁₂4]
  have hfs : f * s = s * f := hxs f hfB
  have hft : g * f * g⁻¹ * t = t * (g * f * g⁻¹) := by
    rw [hts]
    calc g * f * g⁻¹ * (g * s * g⁻¹) = g * (f * s) * g⁻¹ := by group
      _ = g * (s * f) * g⁻¹ := by rw [hfs]
      _ = g * s * g⁻¹ * (g * f * g⁻¹) := by group
  have hρgf : ρ ⟨g * f * g⁻¹, hHN (hgC f hfs)⟩ = 1 := by
    have h1 : (⟨g * f * g⁻¹, hHN (hgC f hfs)⟩ : ↥(normalizer (M : Set X))) =
        (⟨g * x₁ * g⁻¹, hHN (hgC x₁ (hxs x₁ hx₁B))⟩ *
          ⟨g * x₂ * g⁻¹, hHN (hgC x₂ (hxs x₂ hx₂B))⟩) ^ m := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subgroup.coe_mul]
      rw [show g * x₁ * g⁻¹ * (g * x₂ * g⁻¹) = g * y * g⁻¹ by rw [hydef]; group, conj_pow]
    rw [h1, map_pow, map_mul, h₁, h₂, one_mul, one_pow]
  have hgfJ : g * f * g⁻¹ ∈ normalizer (J : Set X) :=
    S₀.centralizer_le_normalizer hT13 hML hSch (mem_centralizer_singleton_iff.mpr hft)
  obtain ⟨ρJ, hρJ⟩ := exists_isPermAction (M := J) (by norm_num) (by norm_num) e
  obtain ⟨π', hπ'⟩ := exists_conj_rho_of_sup (by norm_num) hJM hsup hρ hρJ
  have hρJgf : ρJ ⟨g * f * g⁻¹, hgfJ⟩ = 1 := by
    have h1 := hπ' (g * f * g⁻¹) hgfJ (hHN (hgC f hfs))
    rw [hρgf] at h1
    have h2 : ρJ ⟨g * f * g⁻¹, hgfJ⟩ = π'⁻¹ * (π' * ρJ ⟨g * f * g⁻¹, hgfJ⟩ * π'⁻¹) * π' := by
      group
    rw [h2, ← h1]
    group
  exact S₀.false_of_fourPoint_mem_coreActionKernel_conj hPump hN1 hNoA9 hfM hf2 hf4 hft
    (hρJ.mem_coreActionKernel hgfJ hρJgf)

end CFSG.ComponentClassification.SolMax
