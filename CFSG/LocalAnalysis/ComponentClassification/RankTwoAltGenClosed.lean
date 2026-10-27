module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenPStruct
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenLocal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenRoot
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenNoComp

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools

section Alt

variable {N : ℕ}

@[expose] noncomputable def pi0A (h8 : 2 * 4 ≤ N) : alternatingGroup (Fin N) :=
  ⟨pi0 h8, mem_alternatingGroup.mpr pi0_mem_Y8.1⟩

@[expose] def Y8A (h8 : 2 * 4 ≤ N) : Subgroup (alternatingGroup (Fin N)) :=
  (Y8 h8).comap (alternatingGroup (Fin N)).subtype

@[expose] def V8A (h8 : 2 * 4 ≤ N) : Subgroup (alternatingGroup (Fin N)) :=
  (V8 h8).comap (alternatingGroup (Fin N)).subtype

variable {h8 : 2 * 4 ≤ N}

theorem coe_pi0A : ((pi0A h8 : alternatingGroup (Fin N)) : Perm (Fin N)) = pi0 h8 :=
  rfl

theorem pi0A_mem_Y8A : pi0A h8 ∈ Y8A h8 :=
  pi0_mem_Y8

theorem pi0A_mul_self : pi0A h8 * pi0A h8 = 1 :=
  Subtype.ext pi0_mul_self

theorem pi0A_ne_one : pi0A h8 ≠ 1 := by
  intro h
  have h1 := congrArg (fun σ : alternatingGroup (Fin N) => (σ : Perm (Fin N)) (pairEmb h8 (0, 0)))
    h
  simp only [coe_pi0A, OneMemClass.coe_one, Perm.one_apply, pi0_pairEmb] at h1
  exact zPair_ne _ ((pairEmb h8).injective h1)

theorem cycleType_pi0A :
    ((pi0A h8 : alternatingGroup (Fin N)) : Perm (Fin N)).cycleType = {2, 2, 2, 2} := by
  rw [coe_pi0A, pi0, cycleType_viaEmbeddingHom', cycleType_zPair]
  rfl

theorem mem_Y8_of_mem_V8 {σ : Perm (Fin N)} (hσ : σ ∈ V8 h8) : σ ∈ Y8 h8 :=
  (mem_V8_iff.mp hσ).1

theorem V8A_le_Y8A : V8A h8 ≤ Y8A h8 := fun _ h => mem_Y8_of_mem_V8 h

theorem flipB_mul_self (c : Fin 4 → Bool) : flipB c * flipB c = 1 := by
  rw [← cz_one, cz_sq, one_mul, one_eq_cz, cz_eq_cz_iff]
  exact ⟨rfl, funext fun k => by simp⟩

theorem card_support_flipB : ∀ c : Fin 4 → Bool, evenB c = true → c ≠ (fun _ => false) →
    c ≠ (fun _ => true) → (flipB c).support.card = 4 := by
  decide

theorem cycleType_of_mem_Y8 {σ : Perm (Fin N)} (hσ : σ ∈ Y8 h8) (h1 : σ ≠ 1)
    (h2 : σ ≠ pi0 h8) : σ.cycleType = {2, 2} := by
  obtain ⟨c, hc, hrc⟩ := exists_rho8_of_mem_Y8 hσ
  rw [eq_lift_of_mem_Y8 hσ hc hrc, cycleType_viaEmbeddingHom',
    cycleType_eq_replicate_of_mul_self (flipB_mul_self c),
    card_support_flipB c hc (flipB_ne_one_of_ne hσ hc hrc h1) (flipB_ne_zPair_of_ne hσ hc hrc h2)]
  rfl

theorem mem_alternating_of_mem_Y8 {σ : Perm (Fin N)} (hσ : σ ∈ Y8 h8) :
    σ ∈ alternatingGroup (Fin N) :=
  mem_alternatingGroup.mpr hσ.1

end Alt

section Ye

variable {G : Type} [Group G] {N : ℕ}

@[expose] def yeOf (Φ : alternatingGroup (Fin N) →* G) (h8 : 2 * 4 ≤ N) : Subgroup G :=
  (Y8A h8).map Φ

@[expose] def veOf (Φ : alternatingGroup (Fin N) →* G) (h8 : 2 * 4 ≤ N) : Subgroup G :=
  (V8A h8).map Φ

end Ye

section YeFacts

variable {G : Type} [Group G] {n : ℕ} {Φ : alternatingGroup (Fin (n + 4)) →* G}
  {h8 : 2 * 4 ≤ n + 4}

theorem e_mem_ye : Φ (pi0A h8) ∈ yeOf Φ h8 :=
  ⟨_, pi0A_mem_Y8A, rfl⟩

theorem ye_le_range : yeOf Φ h8 ≤ Φ.range :=
  map_le_range _ _

theorem ye_le_sup : yeOf Φ h8 ≤ Φ.range ⊔ centralizer (Φ.range : Set G) :=
  ye_le_range.trans le_sup_left

theorem ye_le_centralizer : yeOf Φ h8 ≤ centralizer ({Φ (pi0A h8)} : Set G) := by
  rintro _ ⟨σ, hσ, rfl⟩
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (Y8_le_centralizer hσ))

theorem ye_mul_self {x : G} (hx : x ∈ yeOf Φ h8) : x * x = 1 := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  rw [← map_mul, show σ * σ = 1 from Subtype.ext (mul_self_of_mem_Y8 hσ), map_one]

theorem ye_comm {x y : G} (hx : x ∈ yeOf Φ h8) (hy : y ∈ yeOf Φ h8) : x * y = y * x := by
  have h1 := inv_eq_of_mul_eq_one_right (ye_mul_self hx)
  have h2 := inv_eq_of_mul_eq_one_right (ye_mul_self hy)
  have h3 := inv_eq_of_mul_eq_one_right (ye_mul_self (mul_mem hx hy))
  calc x * y = (x * y)⁻¹ := h3.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
    _ = y * x := by rw [h1, h2]

theorem e_mul_self : Φ (pi0A h8) * Φ (pi0A h8) = 1 := by
  rw [← map_mul, pi0A_mul_self, map_one]

theorem ve_le_ye : veOf Φ h8 ≤ yeOf Φ h8 :=
  map_mono V8A_le_Y8A

theorem isElemAbelian_ve : CFSG.Open.IsElemAbelian 2 (veOf Φ h8) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (ye_comm (ve_le_ye a.2) (ve_le_ye b.2))⟩⟩, fun x hx => ?_⟩
  rw [sq]
  exact ye_mul_self (ve_le_ye hx)

end YeFacts

namespace AltGenCore

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenCore A R T g n Φ)
  {h8 : 2 * 4 ≤ n + 4}
include s

theorem card_ye : Nat.card (yeOf Φ h8) = 8 := by
  rw [yeOf, card_map_of_injective s.injective, ← card_Y8 (h8 := h8)]
  have h : (Y8A h8).map (alternatingGroup (Fin (n + 4))).subtype = Y8 h8 := by
    rw [Y8A, map_comap_eq, range_subtype]
    exact inf_eq_right.mpr fun σ hσ => mem_alternating_of_mem_Y8 hσ
  rw [← h, card_map_of_injective (alternatingGroup (Fin (n + 4))).subtype_injective]

omit [Finite G] s in
theorem exists_root_of_mem_ye {x : G} (hx : x ∈ yeOf Φ h8) (h1 : x ≠ 1)
    (h2 : x ≠ Φ (pi0A h8)) : ∃ ρ : alternatingGroup (Fin (n + 4)),
      (ρ : Perm (Fin (n + 4))) ∈ Y8 h8 ∧ (ρ : Perm (Fin (n + 4))).cycleType = {2, 2} ∧
        Φ ρ = x := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  refine ⟨σ, hσ, cycleType_of_mem_Y8 hσ (fun h => h1 ?_) (fun h => h2 ?_), rfl⟩
  · rw [show σ = 1 from Subtype.ext h, map_one]
  · rw [show σ = pi0A h8 from Subtype.ext h]

theorem eq_one_of_mem_centralizer_range {π : alternatingGroup (Fin (n + 4))}
    (hπ : Φ π ∈ centralizer (Φ.range : Set G)) : π = 1 := by
  apply Subtype.ext
  refine LocalAnalysis.ComponentInitial.AlternatingFourGroup.eq_one_of_forall_commute_alternating
    (by simp only [Fintype.card_fin]; have := s.five_le; omega) fun β hβ => ?_
  have h1 : π * ⟨β, hβ⟩ = ⟨β, hβ⟩ * π := by
    apply s.injective
    rw [map_mul, map_mul]
    exact (mem_centralizer_iff.mp hπ (Φ ⟨β, hβ⟩) ⟨⟨β, hβ⟩, rfl⟩).symm
  exact congrArg Subtype.val h1

omit [Finite G] s in
open scoped Pointwise in
theorem exists_mul_of_mem_sup {x : G} (hx : x ∈ Φ.range ⊔ centralizer (Φ.range : Set G)) :
    ∃ β : alternatingGroup (Fin (n + 4)), ∃ c ∈ centralizer (Φ.range : Set G), x = Φ β * c := by
  have hle : centralizer (Φ.range : Set G) ≤ normalizer (Φ.range : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hx' : x ∈ ((Φ.range : Set G) * (centralizer (Φ.range : Set G) : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hle]
    exact hx
  obtain ⟨y, ⟨β, rfl⟩, c, hc, rfl⟩ := Set.mem_mul.mp hx'
  exact ⟨β, c, hc, rfl⟩

theorem mem_range_of_pow_two_pow {x : G} (hx : x ∈ Φ.range ⊔ centralizer (Φ.range : Set G))
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ Φ.range := by
  obtain ⟨β, c, hc, rfl⟩ := exists_mul_of_mem_sup hx
  have hcomm : Φ β * c = c * Φ β := mem_centralizer_iff.mp hc (Φ β) ⟨β, rfl⟩
  have hpow : (Φ β * c) ^ 2 ^ k = Φ β ^ 2 ^ k * c ^ 2 ^ k := (Commute.mul_pow hcomm _)
  rw [hpow] at hk
  have hβc : Φ (β ^ 2 ^ k) = (c ^ 2 ^ k)⁻¹ := by
    rw [map_pow]
    exact eq_inv_of_mul_eq_one_left hk
  have hβ1 : β ^ 2 ^ k = 1 :=
    s.eq_one_of_mem_centralizer_range (by rw [hβc]; exact inv_mem (pow_mem hc _))
  have hc1 : c ^ 2 ^ k = 1 := by
    rw [hβ1, map_one] at hβc
    exact inv_eq_one.mp hβc.symm
  have hcodd : Odd (orderOf c) :=
    s.odd_card_centralizer.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hc)
  have hcdvd : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc1
  have hc' : c = 1 := by
    have h1 : orderOf c = 1 := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcdvd
      rcases j with _ | j
      · simpa using hj
      · rw [hj, pow_succ] at hcodd
        exact absurd (Nat.even_mul.mpr (Or.inr even_two)) (Nat.not_even_iff_odd.mpr hcodd)
    exact orderOf_eq_one_iff.mp h1
  rw [hc', mul_one]
  exact ⟨β, rfl⟩

theorem centralizer_root_le
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    {ρ : alternatingGroup (Fin (n + 4))}
    (hρ : (ρ : Perm (Fin (n + 4))).cycleType = {2, 2}) :
    centralizer ({Φ ρ} : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  obtain ⟨β, hβ⟩ := exists_conj_eq_of_cycleType_eq (σ := rootLast n) (τ := ρ)
    (by rw [cycleType_rootLast, hρ]) rootLast_mul_rootLast rootLast_ne_one
  intro x hx
  set y := (Φ β)⁻¹ * x * Φ β with hy
  have hyc : y ∈ centralizer ({Φ (rootLast n)} : Set G) := by
    rw [mem_centralizer_singleton_iff] at hx ⊢
    have h1 : Φ ρ = Φ β * Φ (rootLast n) * (Φ β)⁻¹ := by rw [← hβ, map_mul, map_mul, map_inv]
    rw [h1] at hx
    rw [hy]
    calc (Φ β)⁻¹ * x * Φ β * Φ (rootLast n)
        = (Φ β)⁻¹ * (x * (Φ β * Φ (rootLast n) * (Φ β)⁻¹)) * Φ β := by group
      _ = (Φ β)⁻¹ * ((Φ β * Φ (rootLast n) * (Φ β)⁻¹) * x) * Φ β := by rw [hx]
      _ = Φ (rootLast n) * ((Φ β)⁻¹ * x * Φ β) := by group
  have h2 := s.centralizer_rootLast_le_of hN hyc
  have hβY : Φ β ∈ Φ.range ⊔ centralizer (Φ.range : Set G) := mem_sup_left ⟨β, rfl⟩
  have h3 : x = Φ β * y * (Φ β)⁻¹ := by rw [hy]; group
  rw [h3]
  exact mul_mem (mul_mem hβY h2) (inv_mem hβY)

theorem exists_sylow_ye
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    (hF : RootFusionAt A Φ) :
    ∃ S : Subgroup G, IsSylowOf 2 S (centralizer ({Φ (pi0A h8)} : Set G)) ∧
      yeOf Φ h8 ≤ S ∧ S ≤ Φ.range ⊔ centralizer (Φ.range : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hPY⟩ := s.exists_isSylowOf_centralizer_le_of hN hF pi0A_mul_self pi0A_ne_one
  set D := centralizer ({Φ (pi0A h8)} : Set G) ⊓ (Φ.range ⊔ centralizer (Φ.range : Set G))
  have hPD : P ≤ D := le_inf hP.le hPY
  have hYeD : yeOf Φ h8 ≤ D := le_inf ye_le_centralizer ye_le_sup
  have hYe2 : IsPGroup 2 (yeOf Φ h8) := IsPGroup.of_card (n := 3) (by rw [s.card_ye]; norm_num)
  obtain ⟨S, hS, hYeS⟩ := AS76b.exists_isSylowOf_le hYeD hYe2
  have hPD' : IsSylowOf 2 P D := hP.of_le hPD inf_le_left
  refine ⟨S, isSylowOf_of_card (hS.le.trans inf_le_left) ?_, hYeS, hS.le.trans inf_le_right⟩
  rw [hS.card_eq, ← hPD'.card_eq, hP.card_eq]

theorem ye_closed
    (hN : normalizer (A : Set G) ≤ Φ.range ⊔ centralizer (Φ.range : Set G))
    (hF : RootFusionAt A Φ) {S : Subgroup G}
    (hSY : S ≤ Φ.range ⊔ centralizer (Φ.range : Set G)) :
    ∀ x ∈ yeOf Φ h8, ∀ h ∈ centralizer ({Φ (pi0A h8)} : Set G), h⁻¹ * x * h ∈ S →
      h⁻¹ * x * h ∈ yeOf Φ h8 := by
  intro x hx h hh hxS
  by_cases hx1 : x = 1
  · rw [hx1, mul_one, inv_mul_cancel]
    exact one_mem _
  by_cases hxe : x = Φ (pi0A h8)
  · have h1 : h⁻¹ * x * h = x := by
      rw [hxe, mul_assoc, ← mem_centralizer_singleton_iff.mp hh, inv_mul_cancel_left]
    rw [h1]
    exact hx
  obtain ⟨ρ, hρY, hρ, rfl⟩ := exists_root_of_mem_ye hx hx1 hxe
  have hh' : h⁻¹ ∈ Φ.range ⊔ centralizer (Φ.range : Set G) :=
    s.mem_sup_of_conj_root_mem_of hN hF hρ (by rw [inv_inv]; exact hSY hxS)
  have hhY := inv_inv h ▸ inv_mem hh'
  obtain ⟨β, c, hc, rfl⟩ := exists_mul_of_mem_sup hhY
  have hce : c * Φ (pi0A h8) = Φ (pi0A h8) * c :=
    (mem_centralizer_iff.mp hc (Φ (pi0A h8)) ⟨_, rfl⟩).symm
  have hβe : β * pi0A h8 = pi0A h8 * β := by
    apply s.injective
    have h1 := mem_centralizer_singleton_iff.mp hh
    rw [mul_assoc, hce, ← mul_assoc, ← mul_assoc] at h1
    have h2 := mul_right_cancel h1
    rw [map_mul, map_mul]
    exact h2
  have hβ' : (β⁻¹ : alternatingGroup (Fin (n + 4))) * pi0A h8 = pi0A h8 * β⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hβe, mul_assoc, mul_inv_cancel, mul_one]
  have hconj : (β⁻¹ * ρ * β⁻¹⁻¹ : alternatingGroup (Fin (n + 4))) ∈ Y8A h8 :=
    conj_mem_Y8 (congrArg Subtype.val hβ') hρY
  refine ⟨_, hconj, ?_⟩
  have hw : Φ (β⁻¹ * ρ * β⁻¹⁻¹) * c = c * Φ (β⁻¹ * ρ * β⁻¹⁻¹) :=
    mem_centralizer_iff.mp hc _ ⟨_, rfl⟩
  calc Φ (β⁻¹ * ρ * β⁻¹⁻¹) = c⁻¹ * (c * Φ (β⁻¹ * ρ * β⁻¹⁻¹)) := by group
    _ = c⁻¹ * (Φ (β⁻¹ * ρ * β⁻¹⁻¹) * c) := by rw [hw]
    _ = (Φ β * c)⁻¹ * Φ ρ * (Φ β * c) := by
        rw [inv_inv, map_mul, map_mul, map_inv]
        group

omit s in
theorem ye_trans {x y : G} (hx : x ∈ yeOf Φ h8) (hy : y ∈ yeOf Φ h8)
    (hx1 : x ∉ zpowers (Φ (pi0A h8))) (hy1 : y ∉ zpowers (Φ (pi0A h8))) :
    ∃ c ∈ centralizer ({Φ (pi0A h8)} : Set G),
      c ∈ normalizer ((yeOf Φ h8 : Subgroup G) : Set G) ∧ c * x * c⁻¹ = y := by
  rw [mem_zpowers_iff_of_mul_self e_mul_self, not_or] at hx1 hy1
  obtain ⟨σ, hσ, rfl⟩ := hx
  obtain ⟨σ', hσ', rfl⟩ := hy
  have hne : ∀ {τ : alternatingGroup (Fin (n + 4))}, Φ τ ≠ 1 → (τ : Perm (Fin (n + 4))) ≠ 1 :=
    fun h h' => h (by rw [show _ = (1 : alternatingGroup (Fin (n + 4))) from Subtype.ext h',
      map_one])
  have hne' : ∀ {τ : alternatingGroup (Fin (n + 4))}, Φ τ ≠ Φ (pi0A h8) →
      (τ : Perm (Fin (n + 4))) ≠ pi0 h8 :=
    fun h h' => h (by rw [show _ = pi0A h8 from Subtype.ext h'])
  obtain ⟨β, hβs, hβe, hβσ⟩ := exists_conj_eq_of_mem_Y8 hσ hσ' (hne hx1.1) (hne' hx1.2)
    (hne hy1.1) (hne' hy1.2)
  set βA : alternatingGroup (Fin (n + 4)) := ⟨β, mem_alternatingGroup.mpr hβs⟩
  have hβeA : βA * pi0A h8 = pi0A h8 * βA := Subtype.ext hβe
  refine ⟨Φ βA, ?_, ?_, ?_⟩
  · rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hβeA]
  · refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨_, ⟨τ, hτ, rfl⟩, rfl⟩
    refine ⟨βA * τ * βA⁻¹, conj_mem_Y8 (congrArg Subtype.val hβeA) hτ, ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl
  · rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hβσ

theorem ye_omega_of {S P : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer ({Φ (pi0A h8)} : Set G))
    (hSY : S ≤ Φ.range ⊔ centralizer (Φ.range : Set G)) (hYP : yeOf Φ h8 ≤ P) (hPS : P ≤ S)
    (hΩ : ∀ x ∈ P, x * x ∈ zpowers (Φ (pi0A h8)) → x ∈ yeOf Φ h8) :
    (∀ x ∈ P, ∃ σ : alternatingGroup (Fin (n + 4)), Φ σ = x) ∧
      OmegaHyp h8 ((P.comap Φ).map (alternatingGroup (Fin (n + 4))).subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrange : ∀ x ∈ P, ∃ σ : alternatingGroup (Fin (n + 4)), Φ σ = x := by
    intro x hx
    obtain ⟨k, hk⟩ := hS2 ⟨x, hPS hx⟩
    exact s.mem_range_of_pow_two_pow (hSY (hPS hx)) (by simpa using congrArg Subtype.val hk)
  refine ⟨hrange, ?_⟩
  set P₀ : Subgroup (Perm (Fin (n + 4))) := (P.comap Φ).map (alternatingGroup _).subtype
  have hmemP₀ : ∀ {σ : alternatingGroup (Fin (n + 4))}, Φ σ ∈ P →
      (σ : Perm (Fin (n + 4))) ∈ P₀ := fun h => ⟨_, h, rfl⟩
  have hP₀ : ∀ τ ∈ P₀, ∃ σ : alternatingGroup (Fin (n + 4)), Φ σ ∈ P ∧
      (σ : Perm (Fin (n + 4))) = τ := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, rfl⟩
  refine ⟨fun τ => ?_, fun τ hτ => ?_, fun τ hτ => ?_, fun τ hτ hsq => ?_⟩
  · obtain ⟨σ, hσ, hστ⟩ := hP₀ τ τ.2
    obtain ⟨k, hk⟩ := hS2 ⟨Φ σ, hPS hσ⟩
    have h1 : Φ (σ ^ 2 ^ k) = 1 := by rw [map_pow]; simpa using congrArg Subtype.val hk
    have h2 : σ ^ 2 ^ k = 1 := s.injective (by rw [h1, map_one])
    have h3 : (σ : Perm (Fin (n + 4))) ^ 2 ^ k = 1 := by
      rw [← SubgroupClass.coe_pow, h2]
      rfl
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, ← hστ, h3]
    rfl
  · obtain ⟨σ, hσ, rfl⟩ := hP₀ τ hτ
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.mp (hSC (hPS hσ))
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (s.injective h1)
  · exact hmemP₀ (σ := ⟨τ, mem_alternating_of_mem_Y8 hτ⟩) (hYP ⟨_, hτ, rfl⟩)
  · obtain ⟨σ, hσ, rfl⟩ := hP₀ τ hτ
    have hsq' : Φ σ * Φ σ ∈ zpowers (Φ (pi0A h8)) := by
      rw [mem_zpowers_iff_of_mul_self e_mul_self, ← map_mul]
      rcases hsq with h | h
      · left
        rw [show σ * σ = 1 from Subtype.ext h, map_one]
      · right
        rw [show σ * σ = pi0A h8 from Subtype.ext h]
    obtain ⟨σ', hσ', hσσ'⟩ := hΩ _ hσ hsq'
    rw [← s.injective hσσ']
    exact hσ'

theorem ye_mul_mem_of_omega {S P : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer ({Φ (pi0A h8)} : Set G))
    (hSY : S ≤ Φ.range ⊔ centralizer (Φ.range : Set G)) (hYP : yeOf Φ h8 ≤ P) (hPS : P ≤ S)
    (hΩ : ∀ x ∈ P, x * x ∈ zpowers (Φ (pi0A h8)) → x ∈ yeOf Φ h8) :
    ∀ x ∈ P, ∀ y ∈ P, x ∉ yeOf Φ h8 → y ∉ yeOf Φ h8 → x * y ∈ yeOf Φ h8 := by
  obtain ⟨hrange, hO⟩ := s.ye_omega_of hS2 hSC hSY hYP hPS hΩ
  intro x hx y hy hxY hyY
  obtain ⟨σ, rfl⟩ := hrange x hx
  obtain ⟨σ', rfl⟩ := hrange y hy
  have hσY : (σ : Perm (Fin (n + 4))) ∉ Y8 h8 := fun h => hxY ⟨σ, h, rfl⟩
  have hσ'Y : (σ' : Perm (Fin (n + 4))) ∉ Y8 h8 := fun h => hyY ⟨σ', h, rfl⟩
  have h := hO.mul_mem_Y8 ⟨σ, hx, rfl⟩ ⟨σ', hy, rfl⟩ hσY hσ'Y
  rw [← map_mul]
  exact ⟨σ * σ', h, rfl⟩

theorem card_ve : Nat.card (veOf Φ h8) = 4 := by
  rw [veOf, card_map_of_injective s.injective]
  have h : (V8A h8).map (alternatingGroup (Fin (n + 4))).subtype = V8 h8 := by
    rw [V8A, map_comap_eq, range_subtype]
    exact inf_eq_right.mpr fun σ hσ => mem_alternating_of_mem_Y8 (mem_Y8_of_mem_V8 hσ)
  have h4 := card_V8 (h8 := h8)
  rw [← h, card_map_of_injective (alternatingGroup (Fin (n + 4))).subtype_injective] at h4
  exact h4

omit [Finite G] s in
theorem exists_root_of_mem_ve {x : G} (hx : x ∈ veOf Φ h8) (h1 : x ≠ 1) :
    ∃ ρ : alternatingGroup (Fin (n + 4)), (ρ : Perm (Fin (n + 4))).cycleType = {2, 2} ∧
      Φ ρ = x := by
  obtain ⟨σ, hσ, rfl⟩ := hx
  refine ⟨σ, cycleType_of_mem_Y8 (mem_Y8_of_mem_V8 hσ) (fun h => h1 ?_) (fun h => ?_), rfl⟩
  · rw [show σ = 1 from Subtype.ext h, map_one]
  · have hσ' : (σ : Perm (Fin (n + 4))) ∈ V8 h8 := hσ
    exact pi0_notMem_V8 (h ▸ hσ')

end AltGenCore

end CFSG.ComponentClassification.RankTwoAlt
