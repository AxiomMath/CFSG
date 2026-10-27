module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L12EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aVec
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L123aS5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10K0Aux

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec123_eq_one_of_odd_two {x : G} (hodd : Odd (orderOf x))
    (h2 : ∃ m : ℕ, x ^ (2 ^ m) = 1) : x = 1 := by
  obtain ⟨m, hm⟩ := h2
  have hdvd : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one hm
  have hcop : Nat.Coprime (orderOf x) (2 ^ m) :=
    (Nat.coprime_two_right.mpr hodd).pow_right m
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd)

theorem sec123_mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  exact and_congr (hA x) (hB x)

theorem sec123_exists_mul_of_normalizer {N S : Subgroup G} (hSN : S ≤ normalizer (N : Set G))
    {x : G} (hx : x ∈ N ⊔ S) : ∃ n ∈ N, ∃ s ∈ S, x = n * s := by
  let D : Subgroup G :=
    { carrier := {x | ∃ n ∈ N, ∃ s ∈ S, x = n * s}
      one_mem' := ⟨1, N.one_mem, 1, S.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨n, hn, s, hs, rfl⟩ ⟨n', hn', s', hs', rfl⟩
        have hc : s * n' * s⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hSN hs) n').mp hn'
        refine ⟨n * (s * n' * s⁻¹), N.mul_mem hn hc, s * s', S.mul_mem hs hs', ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨n, hn, s, hs, rfl⟩
        have hc : s⁻¹ * n⁻¹ * s ∈ N := by
          have := (Subgroup.mem_normalizer_iff.mp (hSN (S.inv_mem hs)) n⁻¹).mp (N.inv_mem hn)
          simpa using this
        refine ⟨s⁻¹ * n⁻¹ * s, hc, s⁻¹, S.inv_mem hs, ?_⟩
        group }
  have hle : N ⊔ S ≤ D :=
    sup_le (fun n hn => ⟨n, hn, 1, S.one_mem, by simp⟩)
      (fun s hs => ⟨1, N.one_mem, s, hs, by simp⟩)
  exact hle hx

theorem sec123_mem_normalizer_B [Finite G] {t : G} {L S : Subgroup G} (hf : Sec12Frame t L S)
    {m : G}
    (hm : m ∈ secM t S L) : m ∈ normalizer (secB S L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hf.normB m hm x hx, fun hx => ?_⟩
  have := hf.normB m⁻¹ (Subgroup.inv_mem _ hm) _ hx
  simpa [mul_assoc] using this

theorem sec123_B_data {t : G} {L S : Subgroup G} (hb : Sec10BData t L S) :
    ∃ φ : (Fin 5 → ZMod 2) → G, SecNatCoord φ (secB S L) ∧
      (∀ l ∈ L ⊓ normalizer (secB S L : Set G),
        ∃ σ ∈ alternatingGroup (Fin 5), SecActs φ l σ) ∧
      (∀ g ∈ normalizer (L : Set G) ⊓ normalizer (secB S L : Set G), ∃ σ, SecActs φ g σ) := by
  obtain ⟨-, -, -, -, -, φ, ⟨hmul, hinj, hmem, hA5, -⟩, -, -, hS5⟩ := hb
  refine ⟨φ, ⟨fun v hv => (hmem _).mpr ⟨v, hv, rfl⟩, hmul, hinj, fun x hx => ?_⟩, ?_, ?_⟩
  · obtain ⟨v, hv, hvx⟩ := (hmem x).mp hx
    exact ⟨v, hv, hvx⟩
  · intro l hl
    obtain ⟨σ, hσ, hact⟩ := hA5 l hl
    exact ⟨σ, hσ, hact⟩
  · intro g hg
    obtain ⟨σ, hσ⟩ := hS5 g hg
    exact ⟨σ, hσ⟩

theorem sec123_Y_le [Finite G] {t : G} {L S : Subgroup G} (hf : Sec12Frame t L S)
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) :
    (secM t S L ⊓ L) ⊔ S ≤ (normalizer (L : Set G) ⊓ normalizer (secB S L : Set G)) ⊓
      centralizer ({t} : Set G) := by
  have hLt : L ≤ centralizer ({t} : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (Subgroup.mem_centralizer_iff.mp hf.htC l hl).symm
  have hML : secM t S L ⊓ L = L ⊓ normalizer (secB S L : Set G) := hf.bdata.2.2.2.2.1
  refine sup_le ?_ ?_
  · intro m hm
    rw [hML] at hm
    exact ⟨⟨Subgroup.le_normalizer hm.1, hm.2⟩, hLt hm.1⟩
  · intro s hs
    exact ⟨⟨hf.hCt (hS.1 hs), sec123_mem_normalizer_B hf (hf.hSM hs)⟩, hS.1 hs⟩

theorem sec123_odd_mem_sup [Finite G] {N S : Subgroup G} (hSN : S ≤ normalizer (N : Set G))
    (hS : IsPGroup 2 S) {x : G} (hx : x ∈ N ⊔ S) (hodd : Odd (orderOf x)) : x ∈ N := by
  obtain ⟨n, hn, s, hs, rfl⟩ := sec123_exists_mul_of_normalizer hSN hx
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  have hk' : s ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hpow : ∀ j : ℕ, ∃ m ∈ N, (n * s) ^ j = m * s ^ j := by
    intro j
    induction j with
    | zero => exact ⟨1, N.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨m, hm, hmj⟩ := ih
      refine ⟨m * (s ^ j * n * (s ^ j)⁻¹), N.mul_mem hm ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (pow_mem (hSN hs) j) n).mp hn
      · rw [pow_succ, hmj]
        group
  obtain ⟨m, hm, hmx⟩ := hpow (2 ^ k)
  rw [hk', mul_one] at hmx
  have hcop : Nat.Coprime (2 ^ k) (orderOf (n * s)) :=
    ((Nat.coprime_two_right.mpr hodd).pow_right k).symm
  obtain ⟨u, hu⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hu, hmx]
  exact N.pow_mem hm u

theorem sec123_odd_mem_Y [Finite G] {t : G} {L S : Subgroup G} (hf : Sec12Frame t L S)
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) {x : G} (hx : x ∈ (secM t S L ⊓ L) ⊔ S)
    (hodd : Odd (orderOf x)) : x ∈ secM t S L ⊓ L := by
  have hML : secM t S L ⊓ L = L ⊓ normalizer (secB S L : Set G) := hf.bdata.2.2.2.2.1
  have hSN : S ≤ normalizer ((secM t S L ⊓ L : Subgroup G) : Set G) := by
    intro s hs
    rw [hML]
    exact sec123_mem_normalizer_inf (hf.hCt (hS.1 hs))
      (Subgroup.le_normalizer (sec123_mem_normalizer_B hf (hf.hSM hs)))
  exact sec123_odd_mem_sup hSN hS.2.1 hx hodd

theorem sec123_rhoB_injective [Finite G] {t : G} {L S X : Subgroup G} (hf : Sec12Frame t L S)
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (hXY : X ≤ (secM t S L ⊓ L) ⊔ S)
    (e : ↥X ≃* Equiv.Perm (Fin 5)) {φ : (Fin 5 → ZMod 2) → G}
    (hφ : SecNatCoord φ (secB S L)) (ρ : ↥X →* Equiv.Perm (Fin 5))
    (hρ : ∀ x : ↥X, SecActs φ (x : G) (ρ x)) : Function.Injective ρ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hne
  have hK : ρ.ker ≠ ⊥ := by
    intro h
    apply hne
    have hxk : x ∈ ρ.ker := hx
    rw [h] at hxk
    exact hxk
  obtain ⟨y, hyK, hy1, hyodd⟩ := sec123_normal_odd e (MonoidHom.normal_ker ρ) hK
  have hyρ : ρ y = 1 := hyK
  have hyY : (y : G) ∈ (secM t S L ⊓ L) ⊔ S := hXY y.2
  have hyodd' : Odd (orderOf (y : G)) := by rwa [Subgroup.orderOf_coe]
  have hyM := sec123_odd_mem_Y hf hS hyY hyodd'
  have hyc : ∀ b ∈ secB S L, (y : G) * b = b * (y : G) := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := hφ.onto b hb
    have h1 := hρ y v hv
    rw [hyρ, permVec_one] at h1
    calc (y : G) * φ v = ((y : G) * φ v * (y : G)⁻¹) * (y : G) := by group
      _ = φ v * (y : G) := by rw [h1]
  have hyB : (y : G) ∈ secB S L := by
    have h := hf.bdata.2.2.1
    rw [← h]
    exact ⟨Subgroup.mem_centralizer_iff.mpr (fun b hb => (hyc b hb).symm), hyM.2⟩
  have hpow : (y : G) ^ (2 ^ 4) = 1 := by
    have h1 := pow_card_eq_one' (G := ↥(secB S L)) (x := ⟨(y : G), hyB⟩)
    rw [hf.bdata.2.1] at h1
    simpa using congrArg Subtype.val h1
  exact hy1 (Subtype.ext (sec123_eq_one_of_odd_two hyodd' ⟨4, hpow⟩))

theorem sec123_not_mem_sup {L S : Subgroup G} {φ : (Fin 5 → ZMod 2) → G}
    (hφ : SecNatCoord φ (secB S L)) (hBL : secB S L ≤ L)
    (hA5 : ∀ l ∈ L ⊓ normalizer (secB S L : Set G),
      ∃ σ ∈ alternatingGroup (Fin 5), SecActs φ l σ)
    {g : G} (hg : g ∈ normalizer (secB S L : Set G)) {σ : Equiv.Perm (Fin 5)}
    (hσ : SecActs φ g σ) (hodd : Equiv.Perm.sign σ = -1) : g ∉ L ⊔ centralizer (L : Set G) := by
  intro hmem
  have hcomm : ∀ l ∈ L, ∀ c ∈ centralizer (L : Set G), l * c = c * l :=
    fun l hl c hc => Subgroup.mem_centralizer_iff.mp hc l hl
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm hmem
  have hcx : ∀ c' ∈ centralizer (L : Set G), ∀ y ∈ secB S L, c' * y * c'⁻¹ = y := by
    intro c' hc' y hy
    have h1 : c' * y = y * c' := (Subgroup.mem_centralizer_iff.mp hc' y (hBL hy)).symm
    rw [h1]
    group
  have hcB : ∀ b ∈ secB S L, c * b = b * c := fun b hb =>
    (Subgroup.mem_centralizer_iff.mp hc b (hBL hb)).symm
  have hcN : c ∈ normalizer (secB S L : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [hcx c hc x hx]
      exact hx
    · intro hx
      have h2 := hcx c⁻¹ (Subgroup.inv_mem _ hc) _ hx
      have h3 : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
      rw [h3] at h2
      rw [h2]
      exact hx
  have hlN : l ∈ normalizer (secB S L : Set G) := by
    have h1 : l = (l * c) * c⁻¹ := by group
    rw [h1]
    exact Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hcN)
  obtain ⟨σl, hσl, hl_act⟩ := hA5 l ⟨hl, hlN⟩
  have hg_act : SecActs φ (l * c) σl := by
    intro v hv
    have hφv : c * φ v = φ v * c := hcB _ (hφ.mem v hv)
    have e1 : c * φ v * c⁻¹ = φ v := by
      rw [hφv]
      group
    calc l * c * φ v * (l * c)⁻¹ = l * (c * φ v * c⁻¹) * l⁻¹ := by group
      _ = l * φ v * l⁻¹ := by rw [e1]
      _ = φ (permVec σl v) := hl_act v hv
  have huniq := SecActs.unique hφ hσ hg_act
  rw [huniq] at hodd
  have h1 : Equiv.Perm.sign σl = 1 := Equiv.Perm.mem_alternatingGroup.mp hσl
  rw [h1] at hodd
  exact absurd hodd (by decide)

theorem sec123_s0 [Finite G] {t : G} {L S X V₁ V₂ : Subgroup G} (hf : Sec12Frame t L S)
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) (hXY : X ≤ (secM t S L ⊓ L) ⊔ S)
    (e : ↥X ≃* Equiv.Perm (Fin 5)) (hV₁ : IsNatModS5 V₁ ⊥ X) (hV₂ : IsNatModS5 V₂ ⊥ X) :
    ∃ (s₀ : G) (φ₁ φ₂ : (Fin 5 → ZMod 2) → G) (a₁ b₁ a₂ b₂ : Fin 5),
      s₀ ∈ X ∧ orderOf s₀ = 2 ∧ s₀ ∈ centralizer ({t} : Set G) ∧
      s₀ ∈ normalizer (L : Set G) ⊓ normalizer (secB S L : Set G) ∧
      s₀ ∉ L ⊔ centralizer (L : Set G) ∧ SecNatCoord φ₁ V₁ ∧ SecNatCoord φ₂ V₂ ∧
      a₁ ≠ b₁ ∧ a₂ ≠ b₂ ∧ SecActs φ₁ s₀ (Equiv.swap a₁ b₁) ∧ SecActs φ₂ s₀ (Equiv.swap a₂ b₂) := by
  obtain ⟨φ₁, ρ₁, hφ₁, hsurj₁, hρ₁⟩ := sec123_natmod_hom hV₁
  obtain ⟨φ₂, ρ₂, hφ₂, hsurj₂, hρ₂⟩ := sec123_natmod_hom hV₂
  have hYle := sec123_Y_le hf hS
  have hXle : ∀ x ∈ X, x ∈ normalizer (L : Set G) ⊓ normalizer (secB S L : Set G) :=
    fun x hx => (hYle (hXY hx)).1
  obtain ⟨φB, hφB, hA5, hBact⟩ := sec123_B_data hf.bdata
  obtain ⟨ρB, hρB⟩ := sec123_hom hφB (H := X) (fun h hh => hBact h (hXle h hh))
  have hinjB := sec123_rhoB_injective hf hS hXY e hφB ρB hρB
  have bij₁ := sec123_bijective e (Or.inr hsurj₁)
  have bij₂ := sec123_bijective e (Or.inr hsurj₂)
  have bijB := sec123_bijective e (Or.inl hinjB)
  obtain ⟨x, hx2, hx1, ⟨a₂, b₂, hab₂, hx2'⟩, hxB⟩ :=
    sec123_s0_alg (MulEquiv.ofBijective ρ₁ bij₁) (MulEquiv.ofBijective ρ₂ bij₂)
      (MulEquiv.ofBijective ρB bijB)
  have hx1' : ρ₁ x = Equiv.swap 0 1 := hx1
  have hx2'' : ρ₂ x = Equiv.swap a₂ b₂ := hx2'
  have hxB' : Equiv.Perm.sign (ρB x) = -1 := hxB
  have hxY := hYle (hXY x.2)
  refine ⟨(x : G), φ₁, φ₂, 0, 1, a₂, b₂, x.2, by rwa [Subgroup.orderOf_coe], hxY.2, hxY.1,
    sec123_not_mem_sup hφB hf.bdata.1 hA5 hxY.1.2 (hρB x) hxB', hφ₁, hφ₂, by decide, hab₂,
    ?_, ?_⟩
  · have := hρ₁ x
    rwa [hx1'] at this
  · have := hρ₂ x
    rwa [hx2''] at this

end CFSG.OddStandard.SmallF3.Omega
