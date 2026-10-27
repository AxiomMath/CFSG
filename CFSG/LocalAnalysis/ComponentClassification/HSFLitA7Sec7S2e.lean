module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7S2d

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec7

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem act_one_eq (A : Subgroup X) : act 1 A = A := by ext x; simp

omit [Finite X] in
theorem act_inv_eq {q : X} {A B : Subgroup X} (h : act q A = B) : act q⁻¹ B = A := by
  rw [← h, ← act_mul, inv_mul_cancel, act_one_eq]

namespace Setup

variable {S : A7Base X} (C : Setup S)

abbrev K : Subgroup X := normalizer (C.D₁.Q₁ : Set X) ⊓ normalizer (C.E₁ : Set X) ⊓
  normalizer (C.G₁ : Set X) ⊓ normalizer (C.G₂ : Set X)

theorem mem_K {κ : X} (hκ : κ ∈ normalizer (C.D₁.Q₁ : Set X)) (h0 : act κ C.E₁ = C.E₁)
    (h1 : act κ C.G₁ = C.G₁) (h2 : act κ C.G₂ = C.G₂) : κ ∈ C.K :=
  ⟨⟨⟨hκ, mem_normalizer_of_map_eq h0⟩, mem_normalizer_of_map_eq h1⟩,
    mem_normalizer_of_map_eq h2⟩

theorem K_act {κ : X} (hκ : κ ∈ C.K) :
    act κ C.E₁ = C.E₁ ∧ act κ C.G₁ = C.G₁ ∧ act κ C.G₂ = C.G₂ ∧ act κ C.G₃ = C.G₃ := by
  obtain ⟨⟨⟨hN, h0⟩, h1⟩, h2⟩ := hκ
  have e0 := map_conj_eq_of_mem_normalizer h0
  have e1 := map_conj_eq_of_mem_normalizer h1
  have e2 := map_conj_eq_of_mem_normalizer h2
  refine ⟨e0, e1, e2, ?_⟩
  have inj : ∀ {A B : Subgroup X}, act κ A = act κ B → A = B := fun h => map_conj_inj h
  rcases C.mem_Ω_iff.mp (C.act_mem_Ω hN C.mem_Ω_G₃) with h | h | h | h
  · exact absurd (inj (h.trans e0.symm)) C.E₁_ne_G₃.symm
  · exact absurd (inj (h.trans e1.symm)) C.G₁_ne_G₃.symm
  · exact absurd (inj (h.trans e2.symm)) C.G₂_ne_G₃.symm
  · exact h

theorem K_le : C.K ≤ normalizer (C.D₁.Q₁ : Set X) := fun _ h => h.1.1.1

theorem le_normalizer_K : normalizer (C.D₁.Q₁ : Set X) ≤ normalizer (C.K : Set X) := by
  intro n hn
  refine mem_normalizer_of_map_le ?_
  rintro _ ⟨κ, hκ, rfl⟩
  show n * κ * n⁻¹ ∈ C.K
  obtain ⟨a0, a1, a2, a3⟩ := C.K_act hκ
  have hfix : ∀ A ∈ C.Ω, act κ A = A := by
    intro A hA
    rcases C.mem_Ω_iff.mp hA with rfl | rfl | rfl | rfl
    · exact a0
    · exact a1
    · exact a2
    · exact a3
  have key : ∀ A ∈ C.Ω, act (n * κ * n⁻¹) A = A := fun A hA => by
    rw [act_mul, act_mul, hfix _ (C.act_mem_Ω (inv_mem hn) hA), ← act_mul, mul_inv_cancel,
      act_one_eq]
  exact C.mem_K (mul_mem (mul_mem hn (C.K_le hκ)) (inv_mem hn)) (key _ C.mem_Ω_E₁)
    (key _ C.mem_Ω_G₁) (key _ C.mem_Ω_G₂)

theorem Q₁_le_K : C.D₁.Q₁ ≤ C.K := fun a ha =>
  C.mem_K (le_normalizer ha) (by rw [C.E₁_eq]; exact C.act_Q₁ ha C.t_mem_Q₁)
    (C.act_Q₁ ha C.r₁_mem) (C.act_Q₁ ha C.r₂_mem)

theorem S₂_inf_K : C.S₂ ⊓ C.K = C.D₁.Q₁ := by
  refine le_antisymm (fun s hs => ?_) (le_inf (C.Q₁_le_S₁.trans C.S₁_le_S₂) C.Q₁_le_K)
  obtain ⟨a0, -, a2, -⟩ := C.K_act hs.2
  exact C.mem_Q₁_of_fix hs.1 a0 a2

theorem isSylowOf_Q₁_K : ABGLocalTools.IsSylowOf 2 C.D₁.Q₁ C.K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := C.S₂_sylow.inf_of_le_normalizer C.K_le C.le_normalizer_K
  rwa [C.S₂_inf_K] at h

theorem cong_of_K {κ : X} (hκ : κ ∈ C.K) {y : X} (hy : y ∈ C.D₁.Q₁) :
    C.Cong (κ * y * κ⁻¹) y := by
  obtain ⟨a0, a1, a2, -⟩ := C.K_act hκ
  have hN := C.K_le hκ
  have hE := C.conj_E0_K hN a0 a1 a2
  obtain ⟨c0, c1, c2⟩ := C.cong_K hN a0 a1 a2
  let H : Subgroup X :=
    { carrier := {y | y ∈ C.D₁.Q₁ ∧ C.Cong (κ * y * κ⁻¹) y}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨mul_mem ha hb, ?_⟩
        rw [conj_mul_eq]
        exact C.cong_mul (C.conj_mem_Q₁ hN ha) ha' hb'
      one_mem' := ⟨one_mem _, by rw [mul_one, mul_inv_cancel]; exact C.cong_refl _⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨inv_mem ha, ?_⟩
        rw [show κ * a⁻¹ * κ⁻¹ = (κ * a * κ⁻¹)⁻¹ by group]
        exact C.cong_inv ha ha' }
  have hle : C.D₁.Q₁ ≤ H := by
    rw [C.Q₁_eq]
    refine sup_le (sup_le (sup_le ?_ (zpowers_le.mpr ⟨C.v'_mem_Q₁, C.cong_v' hN⟩))
      (zpowers_le.mpr ⟨C.w₁'_mem_Q₁, c1⟩)) (zpowers_le.mpr ⟨C.w₂_mem_Q₁, c2⟩)
    rw [C.E₁_eq]
    refine sup_le (fun e he => ⟨C.E0_le_Q₁ he, ?_⟩) (zpowers_le.mpr ⟨C.t_mem_Q₁, c0⟩)
    rw [hE e he]; exact C.cong_refl _
  exact (hle hy).2

theorem sq_K_comm {κ : X} (hκ : κ ∈ C.K) {y : X} (hy : y ∈ C.D₁.Q₁) :
    κ ^ 2 * y * (κ ^ 2)⁻¹ = y := by
  obtain ⟨a0, a1, a2, -⟩ := C.K_act hκ
  have hE := C.conj_E0_K (C.K_le hκ) a0 a1 a2
  obtain ⟨e, he, hey⟩ : ∃ e ∈ C.E₀, κ * y * κ⁻¹ = e * y :=
    ⟨κ * y * κ⁻¹ * y⁻¹, C.cong_def.mp (C.cong_of_K hκ hy), by group⟩
  have hel := C.isRefl_y.elemAbelianTwo_E0 C.isK_k
  rw [show κ ^ 2 * y * (κ ^ 2)⁻¹ = κ * (κ * y * κ⁻¹) * κ⁻¹ by rw [pow_two]; group, hey,
    conj_mul_eq, hE e he, hey, ← mul_assoc, ← pow_two, hel.sq_eq_one e he, one_mul]

def Inn : Subgroup X where
  carrier := {x | x ∈ normalizer (C.D₁.Q₁ : Set X) ∧
    ∃ b ∈ C.D₁.Q₁, ∀ y ∈ C.D₁.Q₁, x * y * x⁻¹ = b * y * b⁻¹}
  mul_mem' := by
    rintro x x' ⟨hx, b, hb, hxb⟩ ⟨hx', b', hb', hxb'⟩
    refine ⟨mul_mem hx hx', b * b', mul_mem hb hb', fun y hy => ?_⟩
    rw [show x * x' * y * (x * x')⁻¹ = x * (x' * y * x'⁻¹) * x⁻¹ by group, hxb' y hy,
      hxb _ (mul_mem (mul_mem hb' hy) (inv_mem hb'))]
    group
  one_mem' := ⟨one_mem _, 1, one_mem _, fun y _ => by group⟩
  inv_mem' := by
    rintro x ⟨hx, b, hb, hxb⟩
    refine ⟨inv_mem hx, b⁻¹, inv_mem hb, fun y hy => ?_⟩
    have h1 := hxb (b⁻¹ * y * b) (mul_mem (mul_mem (inv_mem hb) hy) hb)
    rw [show b * (b⁻¹ * y * b) * b⁻¹ = y by group] at h1
    calc x⁻¹ * y * x⁻¹⁻¹ = x⁻¹ * (x * (b⁻¹ * y * b) * x⁻¹) * x⁻¹⁻¹ := by rw [h1]
      _ = b⁻¹ * y * b⁻¹⁻¹ := by group

theorem mem_Inn {x : X} : x ∈ C.Inn ↔ x ∈ normalizer (C.D₁.Q₁ : Set X) ∧
    ∃ b ∈ C.D₁.Q₁, ∀ y ∈ C.D₁.Q₁, x * y * x⁻¹ = b * y * b⁻¹ := by
  unfold Inn; rfl

theorem exists_inner {κ : X} (hκ : κ ∈ C.K) :
    ∃ b ∈ C.D₁.Q₁, ∀ y ∈ C.D₁.Q₁, κ * y * κ⁻¹ = b * y * b⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := C.Inn ⊓ C.K with hM
  have hQM : C.D₁.Q₁ ≤ M := fun a ha =>
    ⟨C.mem_Inn.mpr ⟨le_normalizer ha, a, ha, fun _ _ => rfl⟩, C.Q₁_le_K ha⟩
  by_contra hne
  have hκM : κ ∉ M := fun h => hne (C.mem_Inn.mp h.1).2
  have hκN : κ ∈ normalizer (M : Set X) := by
    refine mem_normalizer_of_map_le ?_
    rintro _ ⟨x, ⟨hxI, hxK⟩, rfl⟩
    obtain ⟨hxN, b, hb, hxb⟩ := C.mem_Inn.mp hxI
    have hκN₁ := C.K_le hκ
    refine ⟨C.mem_Inn.mpr ⟨mul_mem (mul_mem hκN₁ hxN) (inv_mem hκN₁), κ * b * κ⁻¹,
      C.conj_mem_Q₁ hκN₁ hb, fun y hy => ?_⟩, C.K.mul_mem (C.K.mul_mem hκ hxK) (C.K.inv_mem hκ)⟩
    have hy' : κ⁻¹ * y * κ ∈ C.D₁.Q₁ := by
      have := C.conj_mem_Q₁ (inv_mem hκN₁) hy
      rwa [inv_inv] at this
    show κ * x * κ⁻¹ * y * (κ * x * κ⁻¹)⁻¹ = κ * b * κ⁻¹ * y * (κ * b * κ⁻¹)⁻¹
    rw [show κ * x * κ⁻¹ * y * (κ * x * κ⁻¹)⁻¹ = κ * (x * (κ⁻¹ * y * κ) * x⁻¹) * κ⁻¹ by group,
      hxb _ hy']
    group
  have hκ2 : κ ^ 2 ∈ M :=
    ⟨C.mem_Inn.mpr ⟨pow_mem (C.K_le hκ) 2, 1, one_mem _, fun y hy => by
      rw [C.sq_K_comm hκ hy]; group⟩, pow_mem hκ 2⟩
  have hcard := card_sup_zpowers_eq hκN hκ2 hκM
  have hML : M ≤ M ⊔ zpowers κ := le_sup_left
  have hLK : M ⊔ zpowers κ ≤ C.K := sup_le inf_le_right (zpowers_le.mpr hκ)
  have hidx : M.relIndex (M ⊔ zpowers κ) = 2 := by
    have h := Subgroup.relIndex_mul_card M (M ⊔ zpowers κ)
    rw [inf_eq_left.mpr hML, hcard] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hodd := (ABGLocalTools.isSylowOf_iff.mp C.isSylowOf_Q₁_K).2.2
  apply hodd
  rw [← Subgroup.relIndex_mul_relIndex C.D₁.Q₁ M C.K hQM (inf_le_right),
    ← Subgroup.relIndex_mul_relIndex M (M ⊔ zpowers κ) C.K hML hLK, hidx]
  exact dvd_mul_of_dvd_right (dvd_mul_right 2 _) _

theorem not_swap {δ : X} (hδ : δ ∈ C.D₁.D₁₁) {A B : Subgroup X} (h1 : act δ A = B)
    (h2 : act δ B = A) (hAB : A ≠ B) : False := by
  obtain ⟨m, hm⟩ := C.D₁.isPGroup_D₁₁ ⟨δ, hδ⟩
  have hm' : δ ^ (3 ^ m) = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  obtain ⟨j, hj⟩ : Odd (3 ^ m) := Odd.pow (by decide)
  have hsq : δ ^ 2 ∈ normalizer (A : Set X) := by
    refine mem_normalizer_of_map_eq ?_
    change act (δ ^ 2) A = A
    rw [pow_two, act_mul, h1, h2]
  have hpow : act ((δ ^ 2) ^ j) A = A := map_conj_eq_of_mem_normalizer (pow_mem hsq j)
  apply hAB
  calc A = act (δ ^ (3 ^ m)) A := by rw [hm', act_one_eq]
    _ = act δ (act ((δ ^ 2) ^ j) A) := by rw [hj, ← act_mul, ← pow_mul, pow_succ']
    _ = B := by rw [hpow, h1]

theorem exists_δ : ∃ δ ∈ normalizer (C.D₁.Q₁ : Set X), act δ C.E₁ = C.E₁ ∧
    act δ C.G₁ = C.G₂ ∧ act δ C.G₂ = C.G₃ ∧ act δ C.G₃ = C.G₁ := by
  have hα1 : alpha S (S.t * C.v' * C.w₁') ∉ zpowers C.F.kF := by
    rw [C.alpha_r₁]
    intro h
    rcases eq_one_or_eq_of_mem_zpowers C.F.kF_sq h with h' | h'
    · exact C.kz_ne_one h'
    · exact C.kz_ne_k h'
  obtain ⟨δ, hδ, hmove⟩ := C.exists_D₁₁_moves C.r₁_mem C.r₁_sq hα1
  have hN := C.D₁₁_le_normalizer hδ
  have hE : act δ C.E₁ = C.E₁ := map_conj_eq_of_mem_normalizer (C.D₁.D₁₁_le hδ).1.1
  have inj : ∀ {A B : Subgroup X}, act δ A = act δ B → A = B := fun h => map_conj_inj h
  have hΩ : ∀ {A : Subgroup X}, A ∈ C.Ω → act δ A ∈ C.Ω := fun hA => C.act_mem_Ω hN hA
  have d01 := C.E₁_ne_G₁
  have d02 := C.E₁_ne_G₂
  have d03 := C.E₁_ne_G₃
  have d12 := C.G₁_ne_G₂
  have d13 := C.G₁_ne_G₃
  have d23 := C.G₂_ne_G₃
  rcases C.mem_Ω_iff.mp (hΩ C.mem_Ω_G₁) with h1 | h1 | h1 | h1
  · exact absurd (inj (h1.trans hE.symm)) d01.symm
  · exact absurd h1 hmove
  · rcases C.mem_Ω_iff.mp (hΩ C.mem_Ω_G₂) with h2 | h2 | h2 | h2
    · exact absurd (inj (h2.trans hE.symm)) d02.symm
    · exact (C.not_swap hδ h1 h2 d12).elim
    · exact absurd (inj (h2.trans h1.symm)) d12.symm
    · rcases C.mem_Ω_iff.mp (hΩ C.mem_Ω_G₃) with h3 | h3 | h3 | h3
      · exact absurd (inj (h3.trans hE.symm)) d03.symm
      · exact ⟨δ, hN, hE, h1, h2, h3⟩
      · exact absurd (inj (h3.trans h1.symm)) d13.symm
      · exact absurd (inj (h3.trans h2.symm)) d23.symm
  · rcases C.mem_Ω_iff.mp (hΩ C.mem_Ω_G₃) with h3 | h3 | h3 | h3
    · exact absurd (inj (h3.trans hE.symm)) d03.symm
    · exact (C.not_swap hδ h1 h3 d13).elim
    · rcases C.mem_Ω_iff.mp (hΩ C.mem_Ω_G₂) with h2 | h2 | h2 | h2
      · exact absurd (inj (h2.trans hE.symm)) d02.symm
      · exact ⟨δ⁻¹, inv_mem hN, act_inv_eq hE, act_inv_eq h2, act_inv_eq h3, act_inv_eq h1⟩
      · exact absurd (inj (h2.trans h3.symm)) d23
      · exact absurd (inj (h2.trans h1.symm)) d12.symm
    · exact absurd (inj (h3.trans h1.symm)) d13.symm

theorem conj_Fv_of {q : X} (hqv : q * C.v' = C.v' * q) (hqE : ∀ e ∈ C.E₀, q * e * q⁻¹ = e) :
    ∀ f ∈ C.Fv, q * f * q⁻¹ = f := by
  have hle : C.Fv ≤ centralizer ({q} : Set X) := by
    refine sup_le (fun e he => ?_) (zpowers_le.mpr ?_)
    · rw [mem_centralizer_singleton_iff]
      calc e * q = (q * e * q⁻¹) * q := by rw [hqE e he]
        _ = q * e := by group
    · rw [mem_centralizer_singleton_iff]; exact hqv.symm
  intro f hf
  rw [← mem_centralizer_singleton_iff.mp (hle hf), mul_inv_cancel_right]

theorem conj_conj_Fv {δ q : X} (hδ : δ ∈ normalizer (C.D₁.Q₁ : Set X))
    (hq : ∀ f ∈ C.Fv, q * f * q⁻¹ = f) : ∀ f ∈ C.Fv, (δ * q * δ⁻¹) * f * (δ * q * δ⁻¹)⁻¹ = f := by
  intro f hf
  have hf' : δ⁻¹ * f * δ⁻¹⁻¹ ∈ C.Fv := by
    rw [← act_Fv C (inv_mem hδ)]; exact ⟨f, hf, rfl⟩
  rw [inv_inv] at hf'
  rw [show δ * q * δ⁻¹ * f * (δ * q * δ⁻¹)⁻¹ = δ * (q * (δ⁻¹ * f * δ) * q⁻¹) * δ⁻¹ by group,
    hq _ hf']
  group

theorem sq_conj_mem_Fv {δ q : X} (hδ : δ ∈ normalizer (C.D₁.Q₁ : Set X)) (hq : q ^ 2 ∈ C.Fv) :
    (δ * q * δ⁻¹) ^ 2 ∈ C.Fv := by
  rw [show (δ * q * δ⁻¹) ^ 2 = δ * q ^ 2 * δ⁻¹ by rw [pow_two, pow_two]; group,
    ← act_Fv C hδ]
  exact ⟨q ^ 2, hq, rfl⟩

theorem transfer {n q : X} (hn : n ∈ normalizer (C.D₁.Q₁ : Set X))
    (hnF : ∀ f ∈ C.Fv, n * f * n⁻¹ = f) (hn2 : n ^ 2 ∈ C.Fv) (hq : q ∈ C.S₂)
    (hqF : ∀ f ∈ C.Fv, q * f * q⁻¹ = f) (hq2 : q ^ 2 ∈ C.D₁.Q₁)
    (h0 : act n C.E₁ = act q C.E₁) (h1 : act n C.G₁ = act q C.G₁)
    (h2 : act n C.G₂ = act q C.G₂) :
    ∃ b ∈ C.D₁.Q₁, b * C.v' = C.v' * b ∧ (q * b) ^ 2 ∈ C.Fv := by
  have hqN := C.S₂_le hq
  have hfix : ∀ {A : Subgroup X}, act n A = act q A → act (q⁻¹ * n) A = A := fun {A} h => by
    rw [act_mul, h, ← act_mul, inv_mul_cancel, act_one_eq]
  have hκ : q⁻¹ * n ∈ C.K := C.mem_K (mul_mem (inv_mem hqN) hn) (hfix h0) (hfix h1) (hfix h2)
  obtain ⟨b, hb, hbκ⟩ := C.exists_inner hκ
  have hvF : C.v' ∈ C.Fv := mem_sup_right (mem_zpowers _)
  have hcQ : ∀ y ∈ C.D₁.Q₁, (b⁻¹ * (q⁻¹ * n)) * y * (b⁻¹ * (q⁻¹ * n))⁻¹ = y := by
    intro y hy
    rw [show b⁻¹ * (q⁻¹ * n) * y * (b⁻¹ * (q⁻¹ * n))⁻¹ =
      b⁻¹ * ((q⁻¹ * n) * y * (q⁻¹ * n)⁻¹) * b by group, hbκ y hy]
    group
  have hbv : b * C.v' = C.v' * b := by
    have h1 := hcQ _ C.v'_mem_Q₁
    have hn' := hnF _ hvF
    have hq' : q⁻¹ * C.v' * q = C.v' := by
      calc q⁻¹ * C.v' * q = q⁻¹ * (q * C.v' * q⁻¹) * q := by rw [hqF _ hvF]
        _ = C.v' := by group
    have : b⁻¹ * C.v' * b = C.v' := by
      calc b⁻¹ * C.v' * b = b⁻¹ * (q⁻¹ * (n * C.v' * n⁻¹) * q) * b := by rw [hn', hq']
        _ = b⁻¹ * (q⁻¹ * n) * C.v' * (b⁻¹ * (q⁻¹ * n))⁻¹ := by group
        _ = C.v' := h1
    calc b * C.v' = b * (b⁻¹ * C.v' * b) := by rw [this]
      _ = C.v' * b := by group
  refine ⟨b, hb, hbv, ?_⟩
  set c := b⁻¹ * (q⁻¹ * n) with hc
  have hqb := mul_mem hqN (le_normalizer hb)
  have hqb2 : (q * b) ^ 2 ∈ C.D₁.Q₁ := by
    rw [show (q * b) ^ 2 = (q * b * q⁻¹) * q ^ 2 * b by rw [pow_two, pow_two]; group]
    exact mul_mem (mul_mem (C.conj_mem_Q₁ hqN hb) hq2) hb
  set c' := (q * b)⁻¹ * c * (q * b) with hc'
  have hc'Q : ∀ y ∈ C.D₁.Q₁, c' * y * c'⁻¹ = y := by
    intro y hy
    have hy' := C.conj_mem_Q₁ hqb hy
    rw [hc', show (q * b)⁻¹ * c * (q * b) * y * ((q * b)⁻¹ * c * (q * b))⁻¹ =
      (q * b)⁻¹ * (c * ((q * b) * y * (q * b)⁻¹) * c⁻¹) * (q * b) by group, hcQ _ hy']
    group
  have hn2' : n ^ 2 = (q * b) ^ 2 * (c' * c) := by
    rw [hc', hc]; rw [pow_two, pow_two]; group
  have hccQ : c' * c ∈ C.D₁.Q₁ := by
    rw [show c' * c = ((q * b) ^ 2)⁻¹ * n ^ 2 by rw [hn2']; group]
    exact mul_mem (inv_mem hqb2) (C.Fv_le_Q₁ hn2)
  have hccE : c' * c ∈ C.E₀ := by
    refine C.mem_E0_of_mem_center hccQ fun g hg => ?_
    have h1 : (c' * c) * g * (c' * c)⁻¹ = g := by
      rw [show c' * c * g * (c' * c)⁻¹ = c' * (c * g * c⁻¹) * c'⁻¹ by group, hcQ g hg,
        hc'Q g hg]
    calc c' * c * g = (c' * c) * g * (c' * c)⁻¹ * (c' * c) := by group
      _ = g * (c' * c) := by rw [h1]
  rw [show (q * b) ^ 2 = n ^ 2 * (c' * c)⁻¹ by rw [hn2']; group]
  exact mul_mem hn2 (mem_sup_left (inv_mem hccE))

end Setup

end Sec7

end CFSG.ComponentClassification.HSFLit
