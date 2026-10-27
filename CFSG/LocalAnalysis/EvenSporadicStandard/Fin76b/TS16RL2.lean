module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RL1
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.Fin76b

namespace LiftRL

variable {G : Type*} [Group G] [Finite G]

theorem conjOrbit_dichotomy {N : Subgroup G} [N.Normal] (hN : ∀ n ∈ N, Odd (orderOf n))
    {t η : G} (ht2 : t * t = 1) (htc : ∀ m : G, m * t = t * m) (htN : t ∉ N) (hη : η * η = 1)
    {D : Subgroup G} (hND : N ≤ D)
    (hD : ∀ d ∈ D, η⁻¹ * (d * η * d⁻¹) ∈ (N : Set G) ∪ (fun x => x * t) '' (N : Set G))
    (hDt : ∀ d : G, d * η * d⁻¹ = η * t → d ∈ D) :
    (η * t ∉ conjOrbit D η ∧ (conjOrbit D η).ncard = (conjOrbit N η).ncard) ∨
      (η * t ∈ conjOrbit D η ∧ (conjOrbit D η).ncard = 2 * (conjOrbit N η).ncard) := by
  have hcm : ∀ n ∈ N, ∀ g : G, g * n * g⁻¹ ∈ N :=
    fun n hn g => Subgroup.Normal.conj_mem inferInstance n hn g
  have hconjD : ∀ y ∈ conjOrbit D η, ∀ a ∈ D, a * y * a⁻¹ ∈ conjOrbit D η := by
    rintro y ⟨d, hd, rfl⟩ a ha
    exact ⟨a * d, mul_mem ha hd, by group⟩
  have hONsub : conjOrbit N η ⊆ conjOrbit D η := by
    rintro y ⟨a, ha, rfl⟩
    exact ⟨a, hND ha, rfl⟩
  have hsub : ∀ x ∈ conjOrbit D η,
      x ∈ conjOrbit N η ∨ x ∈ (fun y => y * t) '' conjOrbit N η := by
    rintro x ⟨d, hd, rfl⟩
    have hxx : (d * η * d⁻¹) * (d * η * d⁻¹) = 1 := by
      rw [show (d * η * d⁻¹) * (d * η * d⁻¹) = d * (η * η) * d⁻¹ by group, hη, mul_one,
        mul_inv_cancel]
    rcases hD d hd with hn | ⟨n, hn, hnt⟩
    · left
      have hnt' : η * (η⁻¹ * (d * η * d⁻¹)) = d * η * d⁻¹ := mul_inv_cancel_left η _
      have hinv : (η * (η⁻¹ * (d * η * d⁻¹))) * (η * (η⁻¹ * (d * η * d⁻¹))) = 1 := by
        rw [hnt']
        exact hxx
      rw [← hnt']
      exact mem_conjOrbit_of_involution (hN _ hn) hn hη hinv
    · right
      have hnt' : n * t = η⁻¹ * (d * η * d⁻¹) := hnt
      have hx2 : d * η * d⁻¹ = η * n * t := by
        calc d * η * d⁻¹ = η * (η⁻¹ * (d * η * d⁻¹)) := (mul_inv_cancel_left η _).symm
          _ = η * (n * t) := by rw [hnt']
          _ = η * n * t := (mul_assoc η n t).symm
      have hww : (η * n) * (η * n) = 1 := by
        have e : (η * n * t) * (η * n * t) = (η * n) * (η * n) := by
          calc (η * n * t) * (η * n * t) = (η * n) * (t * (η * n)) * t := by
                simp only [mul_assoc]
            _ = (η * n) * ((η * n) * t) * t := by rw [← htc (η * n)]
            _ = (η * n) * (η * n) * (t * t) := by simp only [mul_assoc]
            _ = (η * n) * (η * n) := by rw [ht2, mul_one]
        rw [← e, ← hx2]
        exact hxx
      exact ⟨η * n, mem_conjOrbit_of_involution (hN n hn) hn hη hww, hx2.symm⟩
  by_cases hmem : η * t ∈ conjOrbit D η
  ·
    right
    refine ⟨hmem, ?_⟩
    have hdisj : Disjoint (conjOrbit N η) ((fun y => y * t) '' conjOrbit N η) := by
      rw [Set.disjoint_left]
      rintro x ⟨a, ha, hax⟩ ⟨y, ⟨b, hb, hby⟩, hyx⟩
      have hyt : y * t = x := hyx
      have hx' : b * η * b⁻¹ * t = x := by rw [hby, hyt]
      have hc : (b⁻¹ * a) * η * (b⁻¹ * a)⁻¹ = η * t := by
        calc (b⁻¹ * a) * η * (b⁻¹ * a)⁻¹ = b⁻¹ * (a * η * a⁻¹) * b := by group
          _ = b⁻¹ * (b * η * b⁻¹ * t) * b := by rw [hax, hx']
          _ = η * (b⁻¹ * t * b) := by group
          _ = η * (t * b⁻¹ * b) := by rw [htc b⁻¹]
          _ = η * t := by group
      have hcN : b⁻¹ * a ∈ N := N.mul_mem (N.inv_mem hb) ha
      have ht_mem : t ∈ N := by
        have e2 : η⁻¹ * (b⁻¹ * a) * η⁻¹⁻¹ * (b⁻¹ * a)⁻¹ = t := by
          rw [inv_inv]
          calc η⁻¹ * (b⁻¹ * a) * η * (b⁻¹ * a)⁻¹
              = η⁻¹ * ((b⁻¹ * a) * η * (b⁻¹ * a)⁻¹) := by group
            _ = η⁻¹ * (η * t) := by rw [hc]
            _ = t := by group
        rw [← e2]
        exact N.mul_mem (hcm _ hcN η⁻¹) (N.inv_mem hcN)
      exact htN ht_mem
    have hunion : conjOrbit D η = conjOrbit N η ∪ (fun y => y * t) '' conjOrbit N η := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hsub x hx with h | h
        · exact Set.mem_union_left _ h
        · exact Set.mem_union_right _ h
      · apply Set.union_subset hONsub
        rintro x ⟨y, ⟨a, ha, hya⟩, hyx⟩
        have hyt : y * t = x := hyx
        have hya' : a * η * a⁻¹ = y := hya
        have h1 := hconjD (η * t) hmem a (hND ha)
        have e : a * (η * t) * a⁻¹ = x := by
          rw [← hyt, ← hya']
          calc a * (η * t) * a⁻¹ = a * η * (t * a⁻¹) := by simp only [mul_assoc]
            _ = a * η * (a⁻¹ * t) := by rw [← htc a⁻¹]
            _ = a * η * a⁻¹ * t := by simp only [mul_assoc]
        rw [← e]
        exact h1
    rw [hunion, Set.ncard_union_eq hdisj, Set.ncard_image_of_injective _ (mul_left_injective t)]
    ring
  ·
    left
    refine ⟨hmem, ?_⟩
    have hOeq : conjOrbit D η = conjOrbit N η := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hsub x hx with h | ⟨y, ⟨a, ha, hya⟩, hyx⟩
        · exact h
        · exfalso
          have hyt : y * t = x := hyx
          have hya' : a * η * a⁻¹ = y := hya
          have e : a⁻¹ * x * a⁻¹⁻¹ = η * t := by
            rw [← hyt, ← hya', inv_inv]
            calc a⁻¹ * (a * η * a⁻¹ * t) * a = η * (a⁻¹ * t) * a := by group
              _ = η * (t * a⁻¹) * a := by rw [htc a⁻¹]
              _ = η * t := by group
          exact hmem (by rw [← e]; exact hconjD x hx a⁻¹ (hND (N.inv_mem ha)))
      · exact hONsub
    rw [hOeq]

end LiftRL

open LiftRL

theorem lift_cent_dvd {M Γ : Type*} [Group M] [Finite M] [Group Γ] [Finite Γ]
    (φ : M →* Γ) (hφ : Function.Surjective φ) {N : Subgroup M} [N.Normal] {t : M}
    (hN : ∀ n ∈ N, Odd (orderOf n)) (ht2 : t * t = 1) (ht1 : t ≠ 1) (htc : ∀ m : M, m * t = t * m)
    (hker : φ.ker = N ⊔ Subgroup.zpowers t) {η : M} (hη : η * η = 1) (k : ℕ) :
    (2 ^ k ∣ Nat.card (Subgroup.centralizer ({φ η} : Set Γ)) →
        2 ^ k ∣ Nat.card (Subgroup.centralizer ({η} : Set M))) ∧
    ((∃ d : M, d * η * d⁻¹ = η * t) →
      2 ^ k ∣ Nat.card (Subgroup.centralizer ({η} : Set M)) →
        2 ^ k ∣ Nat.card (Subgroup.centralizer ({φ η} : Set Γ))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card N) := odd_card_of_odd_orders N hN
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have htN : t ∉ N := by
    intro h
    have h2 := hN t h
    rw [hord] at h2
    exact absurd h2 (by decide)
  have htK : t ∈ φ.ker := by
    rw [hker]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hφt : φ t = 1 := MonoidHom.mem_ker.1 htK
  have hNK : N ≤ φ.ker := by
    rw [hker]
    exact le_sup_left
  have hφN : ∀ a ∈ N, φ a = 1 := fun a ha => MonoidHom.mem_ker.1 (hNK ha)
  have hKset : (φ.ker : Set M) = (N : Set M) ∪ (fun x => x * t) '' (N : Set M) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_union, Set.mem_image]
    rw [hker, Subgroup.mem_sup_of_normal_left]
    constructor
    · rintro ⟨y, hy, z, hz, rfl⟩
      rcases mem_zpowers_involution ht2 ht1 hz with h | h
      · left
        rw [h, mul_one]
        exact hy
      · right
        exact ⟨y, hy, by rw [h]⟩
    · rintro (hx | ⟨y, hy, rfl⟩)
      · exact ⟨x, hx, 1, one_mem _, mul_one x⟩
      · exact ⟨y, hy, t, Subgroup.mem_zpowers t, rfl⟩
  have hKcard : Nat.card φ.ker = 2 * Nat.card N := by
    have hdisj : Disjoint (N : Set M) ((fun x => x * t) '' (N : Set M)) := by
      rw [Set.disjoint_left]
      rintro x hxN ⟨y, hy, hyx⟩
      have hyt : y * t = x := hyx
      apply htN
      have e : t = y⁻¹ * x := by
        rw [← hyt, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact N.mul_mem (N.inv_mem hy) hxN
    have h1 : Nat.card φ.ker = (φ.ker : Set M).ncard := Nat.card_coe_set_eq (φ.ker : Set M)
    have h2 : Nat.card N = (N : Set M).ncard := Nat.card_coe_set_eq (N : Set M)
    rw [h1, h2, hKset, Set.ncard_union_eq hdisj,
      Set.ncard_image_of_injective _ (mul_left_injective t)]
    ring
  set C : Subgroup Γ := Subgroup.centralizer ({φ η} : Set Γ) with hCdef
  set D : Subgroup M := C.comap φ with hDdef
  have hCD : Subgroup.centralizer ({η} : Set M) ≤ D := by
    intro x hx
    have h1 := congrArg φ (Subgroup.mem_centralizer_singleton_iff.1 hx)
    simp only [map_mul] at h1
    exact Subgroup.mem_comap.2 (Subgroup.mem_centralizer_singleton_iff.2 h1)
  have hND : N ≤ D := by
    intro a ha
    exact Subgroup.mem_comap.2 (by rw [hφN a ha]; exact one_mem _)
  have hD : ∀ d ∈ D, η⁻¹ * (d * η * d⁻¹) ∈ (N : Set M) ∪ (fun x => x * t) '' (N : Set M) := by
    intro d hd
    rw [← hKset]
    have hcomm : φ d * φ η = φ η * φ d :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_comap.1 hd)
    have hconj : φ d * φ η * (φ d)⁻¹ = φ η := by rw [hcomm, mul_inv_cancel_right]
    show η⁻¹ * (d * η * d⁻¹) ∈ φ.ker
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hconj, inv_mul_cancel]
  have hDt : ∀ d : M, d * η * d⁻¹ = η * t → d ∈ D := by
    intro d hd
    have h1 : φ d * φ η * (φ d)⁻¹ = φ η := by
      have h2 := congrArg φ hd
      simp only [map_mul, map_inv, hφt, mul_one] at h2
      exact h2
    have h3 : φ d * φ η = φ η * φ d := mul_inv_eq_iff_eq_mul.1 h1
    exact Subgroup.mem_comap.2 (Subgroup.mem_centralizer_singleton_iff.2 h3)
  have hOrb : (conjOrbit D η).ncard * Nat.card (Subgroup.centralizer ({η} : Set M)) =
      Nat.card D := by
    have h := conjOrbit_card_mul D η
    rwa [inf_eq_right.2 hCD] at h
  have hDcard : Nat.card D = 2 * Nat.card N * Nat.card C := by
    rw [hDdef, card_comap_surj φ hφ C, hKcard]
  have hdich := conjOrbit_dichotomy hN ht2 htc htN hη hND hD hDt
  have hONdvd : (conjOrbit N η).ncard ∣ Nat.card N := by
    have h := conjOrbit_card_mul N η
    exact ⟨_, h.symm⟩
  have hu : Odd (conjOrbit N η).ncard := Odd.of_dvd_nat hodd hONdvd
  have hmain : (conjOrbit D η).ncard * Nat.card (Subgroup.centralizer ({η} : Set M)) =
      2 * Nat.card N * Nat.card C := hOrb.trans hDcard
  set u := (conjOrbit N η).ncard with hudef
  set s := Nat.card (Subgroup.centralizer ({η} : Set M)) with hsdef
  set n := Nat.card N with hndef
  set c := Nat.card C with hcdef
  have hB : (conjOrbit D η).ncard = 2 * u → u * s = n * c := by
    intro hcardB
    have h2 : 2 * (u * s) = 2 * (n * c) := by
      calc 2 * (u * s) = (2 * u) * s := by ring
        _ = (conjOrbit D η).ncard * s := by rw [hcardB]
        _ = 2 * n * c := hmain
        _ = 2 * (n * c) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have part1 : 2 ^ k ∣ c → 2 ^ k ∣ s := by
    intro hc
    rcases hdich with ⟨_, hcardA⟩ | ⟨_, hcardB⟩
    · have hA : u * s = 2 * n * c := by
        rw [← hcardA]
        exact hmain
      have h3 : 2 ^ (k + 1) ∣ u * s := by
        rw [hA, pow_succ', mul_assoc]
        exact mul_dvd_mul_left 2 (dvd_mul_of_dvd_right hc n)
      have h4 : 2 ^ (k + 1) ∣ s :=
        Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left (k + 1) (Nat.coprime_two_left.2 hu)) h3
      exact (pow_dvd_pow 2 (Nat.le_succ k)).trans h4
    · have h3 : 2 ^ k ∣ u * s := by
        rw [hB hcardB]
        exact dvd_mul_of_dvd_right hc n
      exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hu)) h3
  have part2 : (∃ d : M, d * η * d⁻¹ = η * t) → 2 ^ k ∣ s → 2 ^ k ∣ c := by
    rintro ⟨d, hd⟩ hs
    have hmemO : η * t ∈ conjOrbit D η := ⟨d, hDt d hd, hd⟩
    rcases hdich with ⟨hnot, _⟩ | ⟨_, hcardB⟩
    · exact absurd hmemO hnot
    · have h3 : 2 ^ k ∣ n * c := by
        rw [← hB hcardB]
        exact dvd_mul_of_dvd_right hs u
      exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)) h3
  exact ⟨part1, part2⟩

theorem exists_two_subgroup_cent {M Γ : Type*} [Group M] [Finite M] [Group Γ] [Finite Γ]
    (φ : M →* Γ) (hφ : Function.Surjective φ) {N : Subgroup M} [N.Normal] {t : M}
    (hN : ∀ n ∈ N, Odd (orderOf n)) (ht2 : t * t = 1) (ht1 : t ≠ 1) (htc : ∀ m : M, m * t = t * m)
    (hker : φ.ker = N ⊔ Subgroup.zpowers t) {η : M} (hη : η * η = 1) {k : ℕ}
    (hk : 2 ^ k ∣ Nat.card (Subgroup.centralizer ({φ η} : Set Γ))) :
    ∃ R : Subgroup M, IsPGroup 2 R ∧ R ≤ Subgroup.centralizer ({η} : Set M) ∧
      Nat.card R = 2 ^ k := by
  have hk' := (lift_cent_dvd φ hφ hN ht2 ht1 htc hker hη k).1 hk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨H, hH⟩ : ∃ H : Subgroup ↥(Subgroup.centralizer ({η} : Set M)),
      Nat.card H = 2 ^ k :=
    Sylow.exists_subgroup_card_pow_prime 2 hk'
  refine ⟨H.map (Subgroup.centralizer ({η} : Set M)).subtype, (IsPGroup.of_card hH).map _, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · rw [Subgroup.card_map_of_injective Subtype.val_injective, hH]

end CFSG.EvenSporadicStandard.Fin76b
