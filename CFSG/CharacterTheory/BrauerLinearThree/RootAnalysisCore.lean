module

public import CFSG.CharacterTheory.BrauerLinearThree.RootAnalysisBasic
public import CFSG.CharacterTheory.BrauerLinearThree.CentralizerPCore

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes

section Group

variable {G : Type} [Group G]

theorem commutes_sup_left {H K L : Subgroup G} (hH : Commutes H L) (hK : Commutes K L) :
    Commutes (H ⊔ K) L := by
  have hle : H ⊔ K ≤ Subgroup.centralizer (L : Set G) := by
    apply sup_le
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hH x hx y hy).symm
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hK x hx y hy).symm
  intro a ha b hb
  exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) b hb).symm

theorem mem_smul_sylow_iff {p : ℕ} {P : Sylow p G} {h x : G} :
    x ∈ ((h • P : Sylow p G) : Subgroup G) ↔ ∃ y ∈ (P : Subgroup G), h * y * h⁻¹ = x := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  simp only [MulAut.smul_def, MulAut.conj_apply]

theorem conj_mem_centralizer_of_map_eq {H : Subgroup G} {t : G} (h : H.map (conjHom t) = H)
    {k : G} (hk : k ∈ Subgroup.centralizer (H : Set G)) :
    t * k * t⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hk ⊢
  intro x hx
  have hx' : x ∈ H.map (conjHom t) := by rw [h]; exact hx
  obtain ⟨y, hy, rfl⟩ := hx'
  rw [conjHom_apply]
  have := hk y hy
  calc t * y * t⁻¹ * (t * k * t⁻¹) = t * (y * k) * t⁻¹ := by group
    _ = t * (k * y) * t⁻¹ := by rw [this]
    _ = t * k * t⁻¹ * (t * y * t⁻¹) := by group

end Group

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)
  {Y : G} (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)

omit [Finite F] in
include hY₁ in
theorem card_centralizer_invJ₁ :
    Nat.card (Subgroup.centralizer ({invJ₁ φ} : Set G)) =
      Nat.card (Subgroup.centralizer ({J} : Set G)) := by
  rw [← hY₁, show Y⁻¹ * J * Y = Y⁻¹ * J * Y⁻¹⁻¹ by rw [inv_inv], card_centralizer_conj]

omit [Finite F] in
include hY₁ hY₂ in
theorem card_centralizer_invJ₂ :
    Nat.card (Subgroup.centralizer ({invJ₂ φ} : Set G)) =
      Nat.card (Subgroup.centralizer ({J} : Set G)) := by
  rw [← hY₂, show Y⁻¹ * invJ₁ φ * Y = Y⁻¹ * invJ₁ φ * Y⁻¹⁻¹ by rw [inv_inv],
    card_centralizer_conj, card_centralizer_invJ₁ φ hY₁]

omit [Finite F] in
include hY₁ hY₂ in
theorem conj_Y_sq_invJ₂ : Y ^ 2 * invJ₂ φ * (Y ^ 2)⁻¹ = J := by
  have h1 : Y * invJ₂ φ * Y⁻¹ = invJ₁ φ := conj_eq_of_inv_conj_eq hY₂
  have h3 : Y * invJ₁ φ * Y⁻¹ = J := conj_eq_of_inv_conj_eq hY₁
  rw [show Y ^ 2 * invJ₂ φ * (Y ^ 2)⁻¹ = Y * (Y * invJ₂ φ * Y⁻¹) * Y⁻¹ by
    simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc], h1, h3]

include hZ h2 hY₁ hY₂ in
theorem card_centralizer_eq_of_commute_D {z : G} (hz1 : z ≠ 1) (hzp : z ^ ringChar F = 1)
    (hz : J * z = z * J ∨ invJ₁ φ * z = z * invJ₁ φ ∨ invJ₂ φ * z = z * invJ₂ φ) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) =
      Nat.card (Subgroup.centralizer ({rootUp φ 1} : Set G)) := by
  have key : ∀ g : G, g * z * g⁻¹ * J = J * (g * z * g⁻¹) →
      Nat.card (Subgroup.centralizer ({z} : Set G)) =
        Nat.card (Subgroup.centralizer ({rootUp φ 1} : Set G)) := by
    intro g hg
    have h1 : g * z * g⁻¹ ≠ 1 := by
      intro h
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    have h3 : (g * z * g⁻¹) ^ ringChar F = 1 := by
      rw [conj_pow, hzp, mul_one, mul_inv_cancel]
    rw [← card_centralizer_conj g z, card_centralizer_eq_rootUp_one φ hZ h2 hg.symm h1 h3]
  rcases hz with h | h | h
  · exact key 1 (by simpa using h.symm)
  · apply key Y
    have := commute_conj Y h
    rw [conj_eq_of_inv_conj_eq hY₁] at this
    exact this.symm
  · apply key (Y ^ 2)
    have := commute_conj (Y ^ 2) h
    rw [conj_Y_sq_invJ₂ φ hY₁ hY₂] at this
    exact this.symm

include hZ hZodd h2 hJ in
theorem exists_fixed_of_isPGroup [Finite G] (M : Subgroup G) (hMp : IsPGroup (ringChar F) M)
    (hMJ : ∀ m ∈ M, J * m * J⁻¹ ∈ M) (hMJ₁ : ∀ m ∈ M, invJ₁ φ * m * (invJ₁ φ)⁻¹ ∈ M)
    (hM : M ≠ ⊥) :
    ∃ z ∈ M, z ≠ 1 ∧ z ^ ringChar F = 1 ∧
      (J * z = z * J ∨ invJ₁ φ * z = z * invJ₁ φ ∨ invJ₂ φ * z = z * invJ₂ φ) := by
  have hcard := card_eq_mul_of_isPGroup φ hZ hZodd h2 hJ M hMp hMJ hMJ₁
  have h1 : 1 < Nat.card M := (Subgroup.one_lt_card_iff_ne_bot M).mpr hM
  have hex : ∃ s : G, (s = J ∨ s = invJ₁ φ ∨ s = invJ₂ φ) ∧
      (M ⊓ Subgroup.centralizer {s} : Subgroup G) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have e0 := hcon J (Or.inl rfl)
    have e1 := hcon (invJ₁ φ) (Or.inr (Or.inl rfl))
    have e2 := hcon (invJ₂ φ) (Or.inr (Or.inr rfl))
    rw [e0, e1, e2, Subgroup.card_bot] at hcard
    omega
  obtain ⟨s, hs, hne⟩ := hex
  obtain ⟨w, hw, hw1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hne
  obtain ⟨hwM, hws⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨k, hk⟩ := hMp ⟨w, hwM⟩
  have hk' : w ^ (ringChar F ^ k) = 1 := by simpa using congrArg Subtype.val hk
  obtain ⟨j, hj1, hjp⟩ := exists_pow_ne_one_pow_eq_one hw1 hk'
  refine ⟨w ^ (ringChar F ^ j), M.pow_mem hwM _, hj1, hjp, ?_⟩
  have hws' : s * w ^ (ringChar F ^ j) = w ^ (ringChar F ^ j) * s :=
    (Commute.pow_right (Subgroup.mem_centralizer_singleton_iff.mp hws).symm _).eq
  rcases hs with rfl | rfl | rfl
  · exact Or.inl hws'
  · exact Or.inr (Or.inl hws')
  · exact Or.inr (Or.inr hws')

section PCore

variable (N : Subgroup G) (hN : N ≤ Subgroup.centralizer {rootUp φ 1})
  (hNp : IsPGroup (ringChar F) N)
  (hNall : ∀ x ∈ Subgroup.centralizer ({rootUp φ 1} : Set G), ∀ k : ℕ,
    x ^ (ringChar F ^ k) = 1 → x ∈ N)

include hZ hZodd h2 hJ hNp hNall in
theorem sup_three_le_pcore [Finite G] (B₀ B₁ B₂ : Subgroup G)
    (h₀ : B₀ ≤ Subgroup.centralizer {J}) (h₁ : B₁ ≤ Subgroup.centralizer {invJ₁ φ})
    (h₂ : B₂ ≤ Subgroup.centralizer {invJ₂ φ})
    (c₀ : Nat.card B₀ = Nat.card F) (c₁ : Nat.card B₁ = Nat.card F)
    (c₂ : Nat.card B₂ = Nat.card F)
    (p₀ : ∀ x ∈ B₀, x ^ ringChar F = 1) (p₁ : ∀ x ∈ B₁, x ^ ringChar F = 1)
    (p₂ : ∀ x ∈ B₂, x ^ ringChar F = 1)
    (t₀ : ∀ t, IsTorus φ t → B₀.map (conjHom t) = B₀)
    (t₁ : ∀ t, IsTorus φ t → B₁.map (conjHom t) = B₁)
    (t₂ : ∀ t, IsTorus φ t → B₂.map (conjHom t) = B₂)
    (q₀ : B₀ ≤ Subgroup.centralizer {rootUp φ 1}) (q₁ : B₁ ≤ Subgroup.centralizer {rootUp φ 1})
    (q₂ : B₂ ≤ Subgroup.centralizer {rootUp φ 1}) :
    B₀ ⊔ B₁ ⊔ B₂ ≤ N ∧ Nat.card F ^ 3 ∣ Nat.card (B₀ ⊔ B₁ ⊔ B₂ : Subgroup G) := by
  have hB : ∀ B : Subgroup G, (∀ x ∈ B, x ^ ringChar F = 1) →
      B ≤ Subgroup.centralizer {rootUp φ 1} → B ≤ N :=
    fun B hp hq x hx => hNall x (hq hx) 1 (by rw [pow_one]; exact hp x hx)
  have hle : B₀ ⊔ B₁ ⊔ B₂ ≤ N := sup_le (sup_le (hB _ p₀ q₀) (hB _ p₁ q₁)) (hB _ p₂ q₂)
  refine ⟨hle, ?_⟩
  have hHT : ∀ t, IsTorus φ t → (B₀ ⊔ B₁ ⊔ B₂).map (conjHom t) = B₀ ⊔ B₁ ⊔ B₂ := by
    intro t ht
    rw [Subgroup.map_sup, Subgroup.map_sup, t₀ t ht, t₁ t ht, t₂ t ht]
  have hHJ : ∀ m ∈ B₀ ⊔ B₁ ⊔ B₂, J * m * J⁻¹ ∈ B₀ ⊔ B₁ ⊔ B₂ := fun m hm => by
    rw [← hHT J (isTorus_J φ)]
    exact ⟨m, hm, rfl⟩
  have hHJ₁ : ∀ m ∈ B₀ ⊔ B₁ ⊔ B₂, invJ₁ φ * m * (invJ₁ φ)⁻¹ ∈ B₀ ⊔ B₁ ⊔ B₂ := fun m hm => by
    rw [← hHT _ (isTorus_invJ₁ φ)]
    exact ⟨m, hm, rfl⟩
  have hcard := card_eq_mul_of_isPGroup φ hZ hZodd h2 hJ _ (hNp.to_le hle) hHJ hHJ₁
  have d₀ : Nat.card F ∣ Nat.card ((B₀ ⊔ B₁ ⊔ B₂) ⊓ Subgroup.centralizer {J} : Subgroup G) := by
    rw [← c₀]
    exact Subgroup.card_dvd_of_le (le_inf (le_sup_left.trans le_sup_left) h₀)
  have d₁ : Nat.card F ∣
      Nat.card ((B₀ ⊔ B₁ ⊔ B₂) ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) := by
    rw [← c₁]
    exact Subgroup.card_dvd_of_le (le_inf (le_sup_right.trans le_sup_left) h₁)
  have d₂ : Nat.card F ∣
      Nat.card ((B₀ ⊔ B₁ ⊔ B₂) ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) := by
    rw [← c₂]
    exact Subgroup.card_dvd_of_le (le_inf le_sup_right h₂)
  rw [hcard, pow_succ, sq]
  exact mul_dvd_mul (mul_dvd_mul d₀ d₁) d₂

end PCore

section Seven

theorem pow_dvd_card_normalizer {G : Type} [Group G] [Finite G] {p f : ℕ} [hp : Fact p.Prime]
    (hf : 1 ≤ f) {M : Subgroup G} (hMp : IsPGroup p M) (hM : p ^ (2 * f) ∣ Nat.card M)
    (hG : p ^ (3 * f) ∣ Nat.card G) :
    p ^ (2 * f + 1) ∣ Nat.card (Subgroup.normalizer (M : Set G)) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hMp
  have hn2 : 2 * f ≤ n := by
    rw [hn] at hM
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).mp hM
  by_cases hn3 : n + 1 ≤ 3 * f
  · have hGn : p ^ (n + 1) ∣ Nat.card G := (pow_dvd_pow _ hn3).trans hG
    have hmod := Sylow.card_normalizer_modEq_card (p := p) hn
    have : p ^ (n + 1) ∣ Nat.card (Subgroup.normalizer (M : Set G)) :=
      Nat.modEq_zero_iff_dvd.mp (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hGn))
    exact (pow_dvd_pow _ (by omega)).trans this
  · have : p ^ n ∣ Nat.card (Subgroup.normalizer (M : Set G)) := by
      rw [← hn]
      exact Subgroup.card_dvd_of_le Subgroup.le_normalizer
    exact (pow_dvd_pow _ (by omega)).trans this

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem eq_one_of_mem_normalizer_root_pair [Finite G] (B₁ B₂ : Subgroup G)
    (hMp : IsPGroup (ringChar F) (B₁ ⊔ B₂ : Subgroup G))
    (hB₁J₁ : B₁ ≤ Subgroup.centralizer {invJ₁ φ}) (hB₂J₂ : B₂ ≤ Subgroup.centralizer {invJ₂ φ})
    (hB₁card : Nat.card B₁ = Nat.card F) (hB₂card : Nat.card B₂ = Nat.card F)
    (hMT : ∀ t, IsTorus φ t → (B₁ ⊔ B₂).map (conjHom t) = B₁ ⊔ B₂)
    (hMW : (B₁ ⊔ B₂).map (conjHom (swapW φ)) = B₁ ⊔ B₂)
    (hQ₀ : ¬ Nat.card F ^ 3 ∣ Nat.card (Subgroup.centralizer ({rootUp φ 1} : Set G)))
    {x : G} (hxE : x ∈ Subgroup.normalizer ((B₁ ⊔ B₂ : Subgroup G) : Set G))
    (hxJ : J * x = x * J) (hxp : x ^ ringChar F = 1) : x = 1 := by
  by_contra hx1
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp⟩
  set M := B₁ ⊔ B₂ with hM_def
  have hWE := mem_normalizer_of_map_eq hMW
  have hTE : ∀ t, IsTorus φ t → t ∈ Subgroup.normalizer (M : Set G) :=
    fun t ht => mem_normalizer_of_map_eq (hMT t ht)
  have hX₁E : rootX₁ φ ≤ Subgroup.normalizer (M : Set G) :=
    rootX₁_le_of_unipotent φ hZ h2 _ hWE hTE hxE hxJ hx1 hxp
  have hX₁p : IsPGroup (ringChar F) (rootX₁ φ) :=
    isPGroup_of_forall_pow (fun y hy => pow_ringChar_of_mem_rootX₁ hy)
  have hGp : IsPGroup (ringChar F) (rootX₁ φ ⊔ M : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hX₁p hMp hX₁E
  have hGT : ∀ t, IsTorus φ t → (rootX₁ φ ⊔ M).map (conjHom t) = rootX₁ φ ⊔ M := by
    intro t ht
    rw [Subgroup.map_sup, torus_map_rootX₁ φ hZ hZodd h2 ht, hMT t ht]
  have hGJ : ∀ m ∈ rootX₁ φ ⊔ M, J * m * J⁻¹ ∈ rootX₁ φ ⊔ M := fun m hm => by
    rw [← hGT J (isTorus_J φ)]
    exact ⟨m, hm, rfl⟩
  have hGJ₁ : ∀ m ∈ rootX₁ φ ⊔ M, invJ₁ φ * m * (invJ₁ φ)⁻¹ ∈ rootX₁ φ ⊔ M := fun m hm => by
    rw [← hGT _ (isTorus_invJ₁ φ)]
    exact ⟨m, hm, rfl⟩
  have hG3 : Nat.card F ^ 3 ∣ Nat.card (rootX₁ φ ⊔ M : Subgroup G) := by
    have hcard := card_eq_mul_of_isPGroup φ hZ hZodd h2 hJ _ hGp hGJ hGJ₁
    have d₀ : Nat.card F ∣
        Nat.card ((rootX₁ φ ⊔ M) ⊓ Subgroup.centralizer {J} : Subgroup G) := by
      rw [← card_rootX₁ hZ (φ := φ)]
      refine Subgroup.card_dvd_of_le (le_inf le_sup_left ?_)
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (commute_J_of_mem_rootX₁ hy).symm
    have d₁ : Nat.card F ∣
        Nat.card ((rootX₁ φ ⊔ M) ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) := by
      rw [← hB₁card]
      exact Subgroup.card_dvd_of_le (le_inf (le_sup_left.trans le_sup_right) hB₁J₁)
    have d₂ : Nat.card F ∣
        Nat.card ((rootX₁ φ ⊔ M) ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) := by
      rw [← hB₂card]
      exact Subgroup.card_dvd_of_le (le_inf (le_sup_right.trans le_sup_right) hB₂J₂)
    rw [hcard, pow_succ, sq]
    exact mul_dvd_mul (mul_dvd_mul d₀ d₁) d₂
  set Zc : Subgroup G := (rootX₁ φ ⊔ M) ⊓ Subgroup.centralizer ((rootX₁ φ ⊔ M : Subgroup G) : Set G)
  have hZcp : IsPGroup (ringChar F) Zc := hGp.to_le inf_le_left
  have hZcJ : ∀ m ∈ Zc, J * m * J⁻¹ ∈ Zc := fun m hm =>
    Subgroup.mem_inf.mpr ⟨hGJ m (Subgroup.mem_inf.mp hm).1,
      conj_mem_centralizer_of_map_eq (hGT J (isTorus_J φ)) (Subgroup.mem_inf.mp hm).2⟩
  have hZcJ₁ : ∀ m ∈ Zc, invJ₁ φ * m * (invJ₁ φ)⁻¹ ∈ Zc := fun m hm =>
    Subgroup.mem_inf.mpr ⟨hGJ₁ m (Subgroup.mem_inf.mp hm).1,
      conj_mem_centralizer_of_map_eq (hGT _ (isTorus_invJ₁ φ)) (Subgroup.mem_inf.mp hm).2⟩
  have hZc : Zc ≠ ⊥ := by
    have hnt : Nontrivial ↥(rootX₁ φ ⊔ M) := by
      refine nontrivial_of_ne
        (⟨rootUp φ 1, Subgroup.mem_sup_left (rootUp_one_mem φ)⟩ : ↥(rootX₁ φ ⊔ M)) 1 ?_
      intro h
      exact rootUp_one_ne_one φ hZ (congrArg Subtype.val h)
    have := hGp.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center ↥(rootX₁ φ ⊔ M))
    intro hbot
    have hzmem : ((z : ↥(rootX₁ φ ⊔ M)) : G) ∈ Zc := by
      refine Subgroup.mem_inf.mpr ⟨(z : ↥(rootX₁ φ ⊔ M)).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hbot, Subgroup.mem_bot] at hzmem
    apply hz1
    apply Subtype.ext
    apply Subtype.ext
    exact hzmem
  obtain ⟨z, hzZc, hz1, hzp, hzD⟩ :=
    exists_fixed_of_isPGroup φ hZ hZodd h2 hJ Zc hZcp hZcJ hZcJ₁ hZc
  have hCz := card_centralizer_eq_of_commute_D φ hZ h2 hY₁ hY₂ hz1 hzp hzD
  have hle : (rootX₁ φ ⊔ M : Subgroup G) ≤ Subgroup.centralizer {z} := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzZc).2) y hy
  apply hQ₀
  rw [← hCz]
  exact hG3.trans (Subgroup.card_dvd_of_le hle)

variable (hcard : Nat.card G * Nat.card Z =
  Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))

include hZ hZodd h2 hJ hY₁ hY₂ hcard in
theorem cube_dvd_of_commuting_root_pair [Finite G] (B₁ B₂ : Subgroup G)
    (hB₁J₁ : B₁ ≤ Subgroup.centralizer {invJ₁ φ}) (hB₂J₂ : B₂ ≤ Subgroup.centralizer {invJ₂ φ})
    (hB₁card : Nat.card B₁ = Nat.card F) (hB₂card : Nat.card B₂ = Nat.card F)
    (hB₁p : ∀ x ∈ B₁, x ^ ringChar F = 1) (hB₂p : ∀ x ∈ B₂, x ^ ringChar F = 1)
    (hB₁c : Commutes B₁ B₁) (hB₂c : Commutes B₂ B₂)
    (hB₁inv : Inverts J B₁) (hB₂inv : Inverts J B₂) (hcomm : Commutes B₁ B₂)
    (hW₁ : B₁.map (conjHom (swapW φ)) = B₂) (hW₂ : B₂.map (conjHom (swapW φ)) = B₁)
    (hT₁ : ∀ t, IsTorus φ t → B₁.map (conjHom t) = B₁)
    (hT₂ : ∀ t, IsTorus φ t → B₂.map (conjHom t) = B₂) :
    Nat.card F ^ 3 ∣ Nat.card (Subgroup.centralizer ({rootUp φ 1} : Set G)) := by
  classical
  by_contra hQ₀
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp⟩
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  have hJJ : J * J = 1 := J_mul_self hJ
  have hJ1 : J ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hJ
    exact absurd hJ (by norm_num)
  set M := B₁ ⊔ B₂ with hM_def
  have hMc : Commutes M M := commutes_sup hB₁c hB₂c hcomm
  have hMinv : Inverts J M := hB₁inv.sup hB₂inv hMc
  have hB₁N : B₁ ≤ Subgroup.normalizer (B₂ : Set G) := by
    intro x hx
    apply mem_normalizer_of_map_eq
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [conjHom_apply, hcomm x hx z hz, mul_inv_cancel_right]
      exact hz
    · intro hy
      exact ⟨y, hy, by rw [conjHom_apply, hcomm x hx y hy, mul_inv_cancel_right]⟩
  have hMp : IsPGroup (ringChar F) M := IsPGroup.to_sup_of_normal_right'
    (isPGroup_of_forall_pow hB₁p) (isPGroup_of_forall_pow hB₂p) hB₁N
  have hMT : ∀ t, IsTorus φ t → M.map (conjHom t) = M := fun t ht => by
    rw [hM_def, Subgroup.map_sup, hT₁ t ht, hT₂ t ht]
  have hMW : M.map (conjHom (swapW φ)) = M := by
    rw [hM_def, Subgroup.map_sup, hW₁, hW₂, sup_comm]
  have hMJ : ∀ m ∈ M, J * m * J⁻¹ ∈ M := fun m hm => by
    rw [hMinv m hm]
    exact M.inv_mem hm
  have hMJ₁ : ∀ m ∈ M, invJ₁ φ * m * (invJ₁ φ)⁻¹ ∈ M := fun m hm => by
    rw [← hMT _ (isTorus_invJ₁ φ)]
    exact ⟨m, hm, rfl⟩
  have hM2 : Nat.card F ^ 2 ∣ Nat.card M := by
    have hcard' := card_eq_mul_of_isPGroup φ hZ hZodd h2 hJ M hMp hMJ hMJ₁
    have d₁ : Nat.card F ∣ Nat.card (M ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) := by
      rw [← hB₁card]
      exact Subgroup.card_dvd_of_le (le_inf le_sup_left hB₁J₁)
    have d₂ : Nat.card F ∣ Nat.card (M ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) := by
      rw [← hB₂card]
      exact Subgroup.card_dvd_of_le (le_inf le_sup_right hB₂J₂)
    rw [hcard', sq, mul_assoc]
    exact dvd_mul_of_dvd_right (mul_dvd_mul d₁ d₂) _
  set E := Subgroup.normalizer (M : Set G) with hE_def
  have hTE : ∀ t, IsTorus φ t → t ∈ E := fun t ht => mem_normalizer_of_map_eq (hMT t ht)
  have hJE : J ∈ E := hTE J (isTorus_J φ)
  have hJ₁E : invJ₁ φ ∈ E := hTE _ (isTorus_invJ₁ φ)
  have hE : Nat.card F ^ 2 * ringChar F ∣ Nat.card E := by
    have h1 : ringChar F ^ (2 * f) ∣ Nat.card M := by
      rwa [hq, ← pow_mul, mul_comm] at hM2
    have h3 : ringChar F ^ (3 * f) ∣ Nat.card G := by
      have := cube_dvd_card hZ hcard
      rwa [hq, ← pow_mul, mul_comm] at this
    have := pow_dvd_card_normalizer hf hMp h1 h3
    rwa [hq, ← pow_mul, ← pow_succ, mul_comm f 2]
  have hD : ∀ x ∈ E, J * x = x * J → x ^ ringChar F = 1 → x = 1 := fun x hxE hxJ hxp =>
    eq_one_of_mem_normalizer_root_pair φ hZ hZodd h2 hJ hY₁ hY₂ B₁ B₂ hMp hB₁J₁ hB₂J₂
      hB₁card hB₂card hMT hMW hQ₀ hxE hxJ hxp
  by_cases hiso : ∀ e ∈ E, (e * J * e⁻¹) * J = J * (e * J * e⁻¹) → e * J * e⁻¹ = J
  ·
    obtain ⟨N', hN'E, hN'n, hN'odd, hdvd⟩ := exists_card_dvd_of_isolated E hJE hJ1 hJJ hiso
    have hpD : ¬ ringChar F ∣ Nat.card (E ⊓ Subgroup.centralizer {J} : Subgroup G) := by
      intro hdvd'
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (ringChar F) hdvd'
      have hxE := (Subgroup.mem_inf.mp x.2).1
      have hxJ := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
      have hx' : orderOf (x : G) = ringChar F := by rw [Subgroup.orderOf_coe, hx]
      have hxp : (x : G) ^ ringChar F = 1 := by
        rw [← hx']
        exact pow_orderOf_eq_one _
      have h1 := hD x hxE hxJ.symm hxp
      rw [h1, orderOf_one] at hx'
      exact hp.one_lt.ne hx'
    have hcopD : Nat.Coprime (Nat.card F ^ 2 * ringChar F)
        (Nat.card (E ⊓ Subgroup.centralizer {J} : Subgroup G)) := by
      rw [hq, ← pow_mul, ← pow_succ]
      exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpD)
    have hN' : Nat.card F ^ 2 * ringChar F ∣ Nat.card N' :=
      hcopD.dvd_of_dvd_mul_right (hE.trans hdvd)
    have hid := card_mul_card_sq_eq_of_four hJ (orderOf_invJ₁ φ hZ h2) (J_commute_invJ₁ φ)
      (J_ne_invJ₁ φ hZ h2) N' hN'odd (fun m hm => hN'n J hJE m hm)
      (fun m hm => hN'n _ hJ₁E m hm)
    rw [← invJ₂_eq φ hZ hZodd h2 hJ] at hid
    have h1 : Nat.card N' ∣ Nat.card (N' ⊓ Subgroup.centralizer {J} : Subgroup G) *
        Nat.card (N' ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) *
        Nat.card (N' ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) := Dvd.intro _ hid
    have hpN'J : Nat.Coprime (Nat.card F ^ 2 * ringChar F)
        (Nat.card (N' ⊓ Subgroup.centralizer {J} : Subgroup G)) :=
      hcopD.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_inf_right _ hN'E))
    have h3 : Nat.card F ^ 2 * ringChar F ∣
        Nat.card (N' ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) *
        Nat.card (N' ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) := by
      have := hN'.trans h1
      rw [mul_assoc] at this
      exact hpN'J.dvd_of_dvd_mul_left this
    have h4 : Nat.card (N' ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) *
        Nat.card (N' ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) ∣
        Nat.card (Subgroup.centralizer ({J} : Set G)) ^ 2 := by
      rw [sq]
      refine mul_dvd_mul ?_ ?_
      · rw [← card_centralizer_invJ₁ φ hY₁]
        exact Subgroup.card_dvd_of_le inf_le_right
      · rw [← card_centralizer_invJ₂ φ hY₁ hY₂]
        exact Subgroup.card_dvd_of_le inf_le_right
    exact not_dvd_sq_card_centralizer φ hZ (h3.trans h4)
  ·
    push Not at hiso
    obtain ⟨e, heE, hcomm', hne⟩ := hiso
    set J' := e * J * e⁻¹ with hJ'_def
    have hJ'J' : J' * J' = 1 := by
      rw [hJ'_def]
      calc e * J * e⁻¹ * (e * J * e⁻¹) = e * (J * J) * e⁻¹ := by group
        _ = 1 := by rw [hJJ]; group
    have hsJ : J * (J * J') = (J * J') * J := by rw [mul_assoc J J' J, hcomm']
    have hs2 : (J * J') * (J * J') = 1 := by
      calc (J * J') * (J * J') = J * (J' * J) * J' := by group
        _ = J * (J * J') * J' := by rw [hcomm']
        _ = (J * J) * (J' * J') := by group
        _ = 1 := by rw [hJJ, hJ'J', one_mul]
    have hs1 : J * J' ≠ 1 := by
      intro h
      apply hne
      rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hJJ]
    have hsJne : J * J' ≠ J := by
      intro h
      have h' : J' = 1 := by
        calc J' = J⁻¹ * (J * J') := by group
          _ = 1 := by rw [h, inv_mul_cancel]
      apply hJ1
      calc J = e⁻¹ * J' * e := by rw [hJ'_def]; group
        _ = 1 := by rw [h']; group
    obtain ⟨h, -, hhs⟩ := exists_conj_invJ₁ φ hZ hZodd h2 hJ hsJ hs2 hs1 hsJne
    have hCs : Nat.card (Subgroup.centralizer ({J * J'} : Set G)) =
        Nat.card (Subgroup.centralizer ({J} : Set G)) := by
      rw [← hhs, card_centralizer_conj, card_centralizer_invJ₁ φ hY₁]
    have hMs : M ≤ Subgroup.centralizer {J * J'} := by
      intro m hm
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hm' : e⁻¹ * m * e ∈ M := by
        have := (Subgroup.mem_normalizer_iff.mp (E.inv_mem heE) m).mp hm
        rwa [inv_inv] at this
      have hJ'm : J' * m * J'⁻¹ = m⁻¹ := by
        rw [hJ'_def]
        calc e * J * e⁻¹ * m * (e * J * e⁻¹)⁻¹ = e * (J * (e⁻¹ * m * e) * J⁻¹) * e⁻¹ := by
              group
          _ = e * (e⁻¹ * m * e)⁻¹ * e⁻¹ := by rw [hMinv _ hm']
          _ = m⁻¹ := by group
      have hJm : J * m⁻¹ * J⁻¹ = m := by
        rw [show J * m⁻¹ * J⁻¹ = (J * m * J⁻¹)⁻¹ by group, hMinv m hm, inv_inv]
      have hsm : (J * J') * m * (J * J')⁻¹ = m := by
        calc (J * J') * m * (J * J')⁻¹ = J * (J' * m * J'⁻¹) * J⁻¹ := by group
          _ = J * m⁻¹ * J⁻¹ := by rw [hJ'm]
          _ = m := hJm
      calc m * (J * J') = ((J * J') * m * (J * J')⁻¹) * (J * J') := by rw [hsm]
        _ = (J * J') * m := by group
    have : Nat.card F ^ 2 ∣ Nat.card (Subgroup.centralizer ({J} : Set G)) := by
      rw [← hCs]
      exact hM2.trans (Subgroup.card_dvd_of_le hMs)
    exact not_sq_dvd_card_centralizer φ hZ this

variable (hcent : ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 →
    Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
        Nat.card F ^ 3 * (Nat.card F - 1) ∧
      ((∀ g : G, g * Q * g⁻¹ ∉ rootX₁ φ) →
        Nat.card (Subgroup.centralizer ({Q} : Set G)) ∣ Nat.card F ^ 3))

omit [Finite F] in
include h2 in
theorem ringChar_ne_two : ringChar F ≠ 2 := by
  intro h
  apply h2
  have := ringChar.Nat.cast_ringChar (R := F)
  rw [h] at this
  exact_mod_cast this

include hZ hZodd h2 hJ hcard hcent in
theorem false_of_pcore_comm [Finite G] [IsSimpleGroup G] (N : Subgroup G)
    (hN : N ≤ Subgroup.centralizer {rootUp φ 1}) (hNp : IsPGroup (ringChar F) N)
    (hNall : ∀ x ∈ Subgroup.centralizer ({rootUp φ 1} : Set G), ∀ k : ℕ,
      x ^ (ringChar F ^ k) = 1 → x ∈ N)
    (hNc : Commutes N N) (hNcard : Nat.card N = Nat.card F ^ 3) : False := by
  classical
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp⟩
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  have hq2 : 2 ≤ Nat.card F := by
    rw [hq]
    exact Nat.one_lt_pow hf.ne' hp.one_lt
  obtain ⟨P, hNP⟩ := hNp.exists_le_sylow
  have hPN : (P : Subgroup G) = N := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hNP
    rw [hNcard]
    exact Nat.le_of_dvd (by positivity) (card_dvd_cube_of_isPGroup hZ hcard P.isPGroup')
  have hTI : ∀ Q : Sylow (ringChar F) G, ∀ g ∈ (P : Subgroup G), g ∈ (Q : Subgroup G) →
      g ≠ 1 → Q = P := by
    intro Q g hgP hgQ hg1
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hgP⟩
    have hk' : g ^ (ringChar F ^ k) = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨j, hj1, hjp⟩ := exists_pow_ne_one_pow_eq_one hg1 hk'
    have hg'P : g ^ (ringChar F ^ j) ∈ (P : Subgroup G) := Subgroup.pow_mem _ hgP _
    have hg'Q : g ^ (ringChar F ^ j) ∈ (Q : Subgroup G) := Subgroup.pow_mem _ hgQ _
    obtain ⟨N', -, hN'p, hN'all⟩ :=
      exists_pcore_centralizer φ hZ hZodd h2 hJ hcard hcent hj1 hjp
    obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G P Q
    have hPc : Commutes (P : Subgroup G) (P : Subgroup G) := by
      rw [hPN]
      exact hNc
    have hQc : Commutes ((h • P : Sylow (ringChar F) G) : Subgroup G)
        ((h • P : Sylow (ringChar F) G) : Subgroup G) := by
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := mem_smul_sylow_iff.mp ha
      obtain ⟨b', hb', rfl⟩ := mem_smul_sylow_iff.mp hb
      calc h * a' * h⁻¹ * (h * b' * h⁻¹) = h * (a' * b') * h⁻¹ := by group
        _ = h * (b' * a') * h⁻¹ := by rw [hPc a' ha' b' hb']
        _ = h * b' * h⁻¹ * (h * a' * h⁻¹) := by group
    have hle : ∀ S : Sylow (ringChar F) G, Commutes (S : Subgroup G) (S : Subgroup G) →
        g ^ (ringChar F ^ j) ∈ (S : Subgroup G) → (S : Subgroup G) ≤ N' := by
      intro S hSc hgS y hy
      obtain ⟨k', hk'⟩ := S.isPGroup' ⟨y, hy⟩
      apply hN'all y _ k' (by simpa using congrArg Subtype.val hk')
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hSc y hy _ hgS
    have hN'le : Nat.card N' ≤ Nat.card (P : Subgroup G) := by
      rw [hPN, hNcard]
      exact Nat.le_of_dvd (by positivity) (card_dvd_cube_of_isPGroup hZ hcard hN'p)
    have e1 : (P : Subgroup G) = N' := Subgroup.eq_of_le_of_card_ge (hle P hPc hg'P) hN'le
    have e2 : ((h • P : Sylow (ringChar F) G) : Subgroup G) = N' :=
      Subgroup.eq_of_le_of_card_ge (hle _ hQc hg'Q) (by
        rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity P]
        exact hN'le)
    exact Sylow.ext (e2.trans e1.symm)
  have hn := card_sylow_modEq_one_of_ti P hTI
  rw [hPN, hNcard] at hn
  have hcQ : ∀ c ∈ Subgroup.centralizer ({rootUp φ 1} : Set G),
      c * rootUp φ 1 * c⁻¹ = rootUp φ 1 := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    rw [hc, mul_inv_cancel_right]
  have hCN : Subgroup.centralizer ({rootUp φ 1} : Set G) ≤
      Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff, hPN]
    intro x
    constructor
    · intro hx
      exact conj_mem_pcore φ N hN hNp hNall (Or.inl (hcQ c hc)) hx
    · intro hx
      have := conj_mem_pcore φ N hN hNp hNall (Or.inl (hcQ _ (Subgroup.inv_mem _ hc))) hx
      simpa [mul_assoc] using this
  have hAle : centerSub φ ≤ Subgroup.centralizer ({rootUp φ 1} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_mem_centerSub φ hz (commute_J_of_mem_rootX₁ (rootUp_one_mem φ))
  have hA : Nat.card (centerSub φ) * Nat.card Z = Nat.card F - 1 := card_scalarImage φ hZ
  have hCQ : Nat.card (Subgroup.centralizer ({rootUp φ 1} : Set G)) =
      Nat.card F ^ 3 * Nat.card (centerSub φ) := by
    apply Nat.dvd_antisymm
    · have h1 := (hcent _ (rootUp_one_ne_one φ hZ) (rootUp_pow_ringChar φ 1)).1
      rw [← hA, ← mul_assoc] at h1
      exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h1
    · have h1 : Nat.card F ^ 3 ∣ Nat.card (Subgroup.centralizer ({rootUp φ 1} : Set G)) := by
        rw [← hNcard]
        exact Subgroup.card_dvd_of_le hN
      have h3 := Subgroup.card_dvd_of_le hAle
      have hcop : Nat.Coprime (Nat.card F ^ 3) (Nat.card (centerSub φ)) := by
        rw [hq, ← pow_mul]
        exact Nat.Coprime.pow_left _ ((coprime_ringChar_card_sub_one F).coprime_dvd_right
          ⟨Nat.card Z, hA.symm⟩)
      exact hcop.mul_dvd_of_dvd_of_dvd h1 h3
  have hidx : (Subgroup.centralizer ({rootUp φ 1} : Set G)).index =
      (Nat.card F ^ 3 - 1) * (Nat.card F + 1) := by
    have h1 := Subgroup.card_mul_index (Subgroup.centralizer ({rootUp φ 1} : Set G))
    have hpos : 0 < Nat.card F ^ 3 * (Nat.card F - 1) := Nat.mul_pos (by positivity) (by omega)
    apply Nat.eq_of_mul_eq_mul_left hpos
    have e1 : Nat.card F ^ 3 * (Nat.card F - 1) *
        (Subgroup.centralizer ({rootUp φ 1} : Set G)).index = Nat.card G * Nat.card Z := by
      rw [← h1, hCQ, ← hA]
      ring
    rw [e1, hcard]
    have hq1 : 1 ≤ Nat.card F := by omega
    have hq3 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow _ _ (by omega)
    have hq2' : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [hq1, hq3, hq2']
    ring
  have hnp : Nat.card (Sylow (ringChar F) G) =
      (Subgroup.normalizer ((P : Subgroup G) : Set G)).index := Sylow.card_eq_index_normalizer P
  have hmul := Subgroup.relIndex_mul_index hCN
  rw [hidx, ← hnp] at hmul
  have hn1 : Nat.card (Sylow (ringChar F) G) ≠ 1 := by
    intro h1
    rw [hnp, Subgroup.index_eq_one, Subgroup.normalizer_eq_top_iff] at h1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G) with hb | ht
    · have : rootUp φ 1 ∈ (P : Subgroup G) := by
        rw [hPN]
        exact rootX₁_le_pcore φ N hNall (rootUp_one_mem φ)
      rw [hb, Subgroup.mem_bot] at this
      exact rootUp_one_ne_one φ hZ this
    · have hJP : J ∈ (P : Subgroup G) := by
        rw [ht]
        exact Subgroup.mem_top J
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨J, hJP⟩
      have hk' : J ^ (ringChar F ^ k) = 1 := by simpa using congrArg Subtype.val hk
      have hdvd : 2 ∣ ringChar F ^ k := by
        rw [← hJ]
        exact orderOf_dvd_of_pow_eq_one hk'
      have h2p : 2 = ringChar F :=
        (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow hdvd)
      exact ringChar_ne_two h2 h2p.symm
  exact false_of_sylow_count hq2 hn hn1 (by rw [mul_comm]; exact hmul)

end Seven

end CFSG.BrauerLinearThree
