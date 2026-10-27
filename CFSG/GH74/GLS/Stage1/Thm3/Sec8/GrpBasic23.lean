module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic8
public import CFSG.GH74.GLS.Bg.TwoGroups.Lemma21i

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups

theorem perm3_no_two_elt : ∀ σ : Equiv.Perm (Fin 3), σ ≠ 1 → σ ^ 3 = 1 →
    ∀ τ : Equiv.Perm (Fin 3), τ * σ = σ * τ → τ ^ 2 = 1 → τ = 1 := by
  decide

theorem exp4_Z4Z4 : ∀ q : Z4Z4, q ^ 4 = 1 := by decide

theorem exp4_of_Z4Z4 {G : Type*} [Group G] {A : Subgroup G} (hZ : Nonempty (↥A ≃* Z4Z4)) :
    ∀ a ∈ A, (a * a) * (a * a) = 1 := by
  obtain ⟨e⟩ := hZ
  intro a ha
  have h1 : (e ⟨a, ha⟩) ^ 4 = 1 := exp4_Z4Z4 _
  have h2 : (⟨a, ha⟩ : ↥A) ^ 4 = 1 := e.injective (by rw [map_pow, h1, map_one])
  have h3 := congrArg Subtype.val h2
  simpa [pow_succ, mul_assoc] using h3

section Core85

variable {G : Type} [Group G]

theorem conjHom_comm_h {A W : Subgroup G} {h : G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hWN : W ≤ normalizer (A : Set G)) (hh : h ∈ normalizer (A : Set G))
    (hcon : ∀ w ∈ W, w * h * w⁻¹ * h⁻¹ ∈ A) (w : ↥W) :
    conjAut A h hh * conjHom A W hWN w = conjHom A W hWN w * conjAut A h hh := by
  ext a
  show h * ((w : G) * (a : G) * (w : G)⁻¹) * h⁻¹ = (w : G) * (h * (a : G) * h⁻¹) * (w : G)⁻¹
  have hc := hcon (w : G) w.2
  obtain ⟨c, hcdef⟩ : ∃ c : G, c = (w : G) * h * (w : G)⁻¹ * h⁻¹ := ⟨_, rfl⟩
  rw [← hcdef] at hc
  have hwh : (w : G) * h * (w : G)⁻¹ = c * h := by rw [hcdef]; group
  have hwh' : (w : G) * h⁻¹ * (w : G)⁻¹ = h⁻¹ * c⁻¹ := by
    have : (w : G) * h⁻¹ * (w : G)⁻¹ = ((w : G) * h * (w : G)⁻¹)⁻¹ := by group
    rw [this, hwh]; group
  have hwa : (w : G) * (a : G) * (w : G)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hWN w.2) a).1 a.2
  have hhwa : h * ((w : G) * (a : G) * (w : G)⁻¹) * h⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.1 hh _).1 hwa
  have hX := hAc c hc _ hhwa
  have e1 : (w : G) * (h * (a : G) * h⁻¹) * (w : G)⁻¹ =
      ((w : G) * h * (w : G)⁻¹) * ((w : G) * (a : G) * (w : G)⁻¹) * ((w : G) * h⁻¹ * (w : G)⁻¹) := by
    group
  rw [e1, hwh, hwh']
  calc h * ((w : G) * (a : G) * (w : G)⁻¹) * h⁻¹
      = (h * ((w : G) * (a : G) * (w : G)⁻¹) * h⁻¹ * c) * c⁻¹ := by group
    _ = (c * (h * ((w : G) * (a : G) * (w : G)⁻¹) * h⁻¹)) * c⁻¹ := by rw [hX]
    _ = c * h * ((w : G) * (a : G) * (w : G)⁻¹) * (h⁻¹ * c⁻¹) := by group

theorem core85 [Finite G] {A W : Subgroup G} {h : G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hZ : Nonempty (↥A ≃* Z4Z4))
    (hAW : A ≤ W) (hWN : W ≤ normalizer (A : Set G)) (hW2 : ∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) = 1)
    (hh : h ∈ normalizer (A : Set G)) (hhord : orderOf (conjAut A h hh) = 3)
    (hcentA : ∀ w ∈ W, (∀ a ∈ A, w * a = a * w) → w ∈ A)
    (hC1 : ∀ a ∈ A, h * a * h⁻¹ = a → a = 1)
    (hcon : ∀ w ∈ W, w * h * w⁻¹ * h⁻¹ ∈ A)
    (hW : 4 * Nat.card ↥A ≤ Nat.card ↥W) :
    Nat.card ↥W ≤ 4 * Nat.card ↥A ∧ ∃ δ ∈ W, δ * δ = 1 ∧ δ * h = h * δ ∧
      (∀ a ∈ A, δ * a * δ⁻¹ = a ↔ a * a = 1) ∧
      (∀ a ∈ A, a * (δ * a * δ⁻¹) = 1 → a * a = 1) := by
  classical
  let _inst : CommGroup ↥A :=
    { (inferInstance : Group ↥A) with mul_comm := fun a b => Subtype.ext (hAc a a.2 b b.2) }
  obtain ⟨d, hd⟩ := iv2_2_1_d ↥A hZ (conjAut A h hh) hhord
  have hd' := hd
  obtain ⟨hd0, hdcent, hdcard, hdsq, hdCB, -⟩ := hd
  let ρ : ↥W →* MulAut ↥A := conjHom A W hWN
  have hker : ∀ w : ↥W, ρ w = 1 ↔ (w : G) ∈ A := by
    intro w
    constructor
    · intro h1
      apply hcentA w.1 w.2
      intro a ha
      have h2 : (w : G) * a * (w : G)⁻¹ = a := by
        have := congrArg (fun f : MulAut ↥A => ((f ⟨a, ha⟩ : ↥A) : G)) h1
        exact this
      calc (w : G) * a = ((w : G) * a * (w : G)⁻¹) * (w : G) := by group
        _ = a * (w : G) := by rw [h2]
    · intro h1
      ext a
      show (w : G) * (a : G) * (w : G)⁻¹ = (a : G)
      have := hAc _ h1 a a.2
      calc (w : G) * (a : G) * (w : G)⁻¹ = ((a : G) * (w : G)) * (w : G)⁻¹ := by rw [this]
        _ = a := by group
  have hkerA : ρ.ker = A.subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, hker w, Subgroup.mem_subgroupOf]
  have hcardker : Nat.card ρ.ker = Nat.card ↥A := by
    rw [hkerA]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv
  have hcardW : Nat.card ρ.ker * Nat.card ρ.range = Nat.card ↥W := by
    have h1 := Subgroup.card_mul_index ρ.ker
    rwa [Subgroup.index_ker] at h1
  obtain ⟨φ, -, hφk⟩ := iv2_2_1_b ↥A hZ
  obtain ⟨-, -, hA016⟩ := iv2_2_1_a ↥A hZ
  have hxne : φ (conjAut A h hh) ≠ 1 := by
    intro h1
    have hmem : conjAut A h hh ∈ A0 ↥A := by
      rw [← hφk]
      exact h1
    have hdvd : orderOf (conjAut A h hh) ∣ Nat.card (A0 ↥A) := by
      have := orderOf_dvd_natCard (⟨conjAut A h hh, hmem⟩ : A0 ↥A)
      rwa [Subgroup.orderOf_mk] at this
    rw [hhord, hA016] at hdvd
    omega
  have hx3 : φ (conjAut A h hh) ^ 3 = 1 := by
    have h3 : conjAut A h hh ^ 3 = 1 := by
      have := pow_orderOf_eq_one (conjAut A h hh)
      rwa [hhord] at this
    rw [← map_pow, h3, map_one]
  have hrange_le : ρ.range ≤ centralizer ({conjAut A h hh} : Set (MulAut ↥A)) ⊓ A0 ↥A := by
    rintro τ ⟨w, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (conjHom_comm_h hAc hWN hh hcon w).symm
    · rw [← hφk, MonoidHom.mem_ker]
      obtain ⟨k, hk⟩ := hW2 (w : G) w.2
      have hτ2k : ρ w ^ (2 ^ k) = 1 := by
        rw [← map_pow]
        have : w ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
        rw [this, map_one]
      have hφτ : φ (ρ w) ^ (2 ^ k) = 1 := by
        rw [← map_pow, hτ2k, map_one]
      have hcomm : φ (ρ w) * φ (conjAut A h hh) = φ (conjAut A h hh) * φ (ρ w) := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact (conjHom_comm_h hAc hWN hh hcon w).symm
      have hsq : φ (ρ w) ^ 2 = 1 := by
        have h1 : orderOf (φ (ρ w)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hφτ
        have h2 : orderOf (φ (ρ w)) ∣ 6 := by
          have := orderOf_dvd_natCard (φ (ρ w))
          rw [Nat.card_eq_fintype_card, Fintype.card_perm] at this
          simpa [Nat.factorial] using this
        have h3 : orderOf (φ (ρ w)) ∣ 2 := by
          have h4 : orderOf (φ (ρ w)) ∣ Nat.gcd (2 ^ k) 6 := Nat.dvd_gcd h1 h2
          have h5 : Nat.gcd (2 ^ k) 6 ∣ 2 := by
            rcases k with _ | k
            · simp
            · rw [pow_succ]
              have : Nat.gcd (2 ^ k * 2) 6 = 2 * Nat.gcd (2 ^ k) 3 := by
                rw [mul_comm, show (6 : ℕ) = 2 * 3 from rfl, Nat.gcd_mul_left]
              rw [this]
              have : Nat.gcd (2 ^ k) 3 = 1 := by
                apply Nat.Coprime.pow_left
                norm_num
              rw [this]
          exact h4.trans h5
        exact orderOf_dvd_iff_pow_eq_one.1 h3
      exact perm3_no_two_elt _ hxne hx3 _ hcomm hsq
  have hcardT : Nat.card ρ.range ≤ 4 := by
    have h1 := Subgroup.card_le_of_le hrange_le
    rw [hdcent] at h1
    omega
  have hAcard_pos : 0 < Nat.card ↥A := Nat.card_pos
  have hT4 : Nat.card ρ.range = 4 := by
    rw [hcardker] at hcardW
    by_contra hne
    have hlt : Nat.card ρ.range ≤ 3 := by omega
    have : Nat.card ↥A * Nat.card ρ.range ≤ Nat.card ↥A * 3 := Nat.mul_le_mul_left _ hlt
    omega
  have hTeq : ρ.range = zpowers (iotaB ↥A) ⊔ zpowers d := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [← hdcent]; exact hrange_le
    · omega
  have hdT : d ∈ ρ.range := by
    rw [hTeq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  obtain ⟨w₀, hw₀⟩ := hdT
  have hw₀G : (w₀ : G) ∈ W := w₀.2
  have ha₀ : (w₀ : G)⁻¹ * h * (w₀ : G) * h⁻¹ ∈ A := by
    have := hcon _ (inv_mem hw₀G)
    simpa using this
  let θ : ↥A →* ↥A := MonoidHom.id ↥A * ((conjAut A h hh).toMonoidHom)⁻¹
  have hθ : ∀ a : ↥A, ((θ a : ↥A) : G) = (a : G) * (h * (a : G) * h⁻¹)⁻¹ := by
    intro a
    show ((a * ((conjAut A h hh a))⁻¹ : ↥A) : G) = _
    simp [conjAut_apply]
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply Subtype.ext
    have h1 : (a : G) * (h * (a : G) * h⁻¹)⁻¹ = 1 := by rw [← hθ a, ha]; rfl
    have h2 : h * (a : G) * h⁻¹ = a := by
      have : (a : G) = h * (a : G) * h⁻¹ := mul_inv_eq_one.1 h1
      exact this.symm
    exact hC1 a a.2 h2
  obtain ⟨a₁, ha₁⟩ := Finite.surjective_of_injective hθinj ⟨_, ha₀⟩
  have ha₁G : (a₁ : G) * (h * (a₁ : G) * h⁻¹)⁻¹ = (w₀ : G)⁻¹ * h * (w₀ : G) * h⁻¹ := by
    rw [← hθ a₁, ha₁]
  set δ : G := (w₀ : G) * (a₁ : G) with hδdef
  have hδW : δ ∈ W := mul_mem hw₀G (hAW a₁.2)
  have hδh : δ * h = h * δ := by
    have e1 : h * (w₀ : G) * h⁻¹ = (w₀ : G) * ((w₀ : G)⁻¹ * h * (w₀ : G) * h⁻¹) := by group
    have e2 : h * δ * h⁻¹ = δ := by
      calc h * δ * h⁻¹ = (h * (w₀ : G) * h⁻¹) * (h * (a₁ : G) * h⁻¹) := by rw [hδdef]; group
        _ = (w₀ : G) * (((w₀ : G)⁻¹ * h * (w₀ : G) * h⁻¹) * (h * (a₁ : G) * h⁻¹)) := by rw [e1]; group
        _ = (w₀ : G) * (((a₁ : G) * (h * (a₁ : G) * h⁻¹)⁻¹) * (h * (a₁ : G) * h⁻¹)) := by rw [ha₁G]
        _ = δ := by rw [hδdef]; group
    calc δ * h = (h * δ * h⁻¹) * h := by rw [e2]
      _ = h * δ := by group
  let δW : ↥W := ⟨δ, hδW⟩
  have hρδ : ρ δW = d := by
    have hmul : δW = w₀ * ⟨(a₁ : G), hAW a₁.2⟩ := rfl
    rw [hmul, map_mul, hw₀]
    have : ρ ⟨(a₁ : G), hAW a₁.2⟩ = 1 := (hker _).2 a₁.2
    rw [this, mul_one]
  have hδ2 : δ * δ = 1 := by
    have h1 : ρ (δW * δW) = 1 := by
      rw [map_mul, hρδ]
      exact hdsq d (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
    have h2 : ((δW * δW : ↥W) : G) ∈ A := (hker _).1 h1
    have h3 : h * (δ * δ) * h⁻¹ = δ * δ := by
      calc h * (δ * δ) * h⁻¹ = (h * δ * h⁻¹) * (h * δ * h⁻¹) := by group
        _ = δ * δ := by
          have : h * δ * h⁻¹ = δ := by
            calc h * δ * h⁻¹ = (δ * h) * h⁻¹ := by rw [hδh]
              _ = δ := by group
          rw [this]
    exact hC1 _ h2 h3
  have hWle : Nat.card ↥W ≤ 4 * Nat.card ↥A := by
    rw [← hcardW, hcardker]
    calc Nat.card ↥A * Nat.card ρ.range ≤ Nat.card ↥A * 4 := Nat.mul_le_mul_left _ hcardT
      _ = 4 * Nat.card ↥A := mul_comm _ _
  refine ⟨hWle, δ, hδW, hδ2, hδh, ?_, ?_⟩
  · intro a ha
    have key : ((d ⟨a, ha⟩ : ↥A) : G) = δ * a * δ⁻¹ := by
      rw [← hρδ]; rfl
    constructor
    · intro h1
      have : d ⟨a, ha⟩ = ⟨a, ha⟩ := Subtype.ext (by rw [key, h1])
      have hmem : (⟨a, ha⟩ : ↥A) ∈ CB ↥A d := this
      rw [hdCB, mem_ZB] at hmem
      have := congrArg Subtype.val hmem
      simpa [pow_two] using this
    · intro h1
      have hmem : (⟨a, ha⟩ : ↥A) ∈ ZB ↥A := by
        rw [mem_ZB]
        apply Subtype.ext
        simpa [pow_two] using h1
      rw [← hdCB] at hmem
      have h2 : d ⟨a, ha⟩ = ⟨a, ha⟩ := hmem
      rw [← key, h2]
  · intro a ha h1
    have hE := iv2_2_1_e ↥A hZ
    have hΦ : ∀ z : ↥A, ∃ φ : MulAut ↥A, z ∈ ZB ↥A → z ≠ 1 → IsPhi ↥A z φ := by
      intro z
      by_cases hz : z ∈ ZB ↥A ∧ z ≠ 1
      · obtain ⟨φ, hφ, -⟩ := hE z hz.1 hz.2
        exact ⟨φ, fun _ _ => hφ⟩
      · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ hz⟩
    choose Φ hΦ using hΦ
    have hd1 : d ≠ 1 := by
      intro h0
      rw [h0, Subgroup.zpowers_one_eq_bot, sup_bot_eq] at hdcard
      have h2 : iotaB ↥A * iotaB ↥A = 1 := hdsq _ (by rw [h0]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
      have h3 : orderOf (iotaB ↥A) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
      have h4 : Nat.card (zpowers (iotaB ↥A)) = orderOf (iotaB ↥A) := Nat.card_zpowers _
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    have hf1 := iv2_2_1_f1 ↥A hZ (conjAut A h hh) hhord d hd' Φ hΦ
    obtain ⟨-, hf1⟩ := hf1
    have hdA' := (hf1 d hd0 hd1).1 (Or.inl (Or.inl rfl))
    have hb : d ⟨a, ha⟩ = (⟨a, ha⟩ : ↥A)⁻¹ := by
      apply Subtype.ext
      have h2 : ((d ⟨a, ha⟩ : ↥A) : G) = δ * a * δ⁻¹ := by rw [← hρδ]; rfl
      rw [h2]
      show δ * a * δ⁻¹ = a⁻¹
      exact eq_inv_of_mul_eq_one_right h1
    have hsq := hdA' ⟨a, ha⟩ hb
    have := congrArg Subtype.val hsq
    simpa [pow_two] using this

end Core85

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
