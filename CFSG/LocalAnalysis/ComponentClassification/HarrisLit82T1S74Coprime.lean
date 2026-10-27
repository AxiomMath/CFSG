module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Endgame

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open Subgroup

theorem exists_eq_of_involutive {α : Type*} [Finite α] (hα : Odd (Nat.card α)) {f : α → α}
    (hf : Function.Involutive f) : ∃ a, f a = a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ := Fintype.ofFinite α
  let σ : Equiv.Perm α := hf.toPerm f
  have hσ : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    exact Equiv.ext fun a => hf a
  have h := Equiv.Perm.card_compl_support_modEq hσ
  rw [Nat.card_eq_fintype_card] at hα
  have hne : σ.supportᶜ.card ≠ 0 := by
    intro h0
    rw [h0] at h
    obtain ⟨r, hr⟩ := hα
    rw [hr] at h
    simp [Nat.ModEq, Nat.add_mod] at h
  obtain ⟨a, ha⟩ := Finset.card_ne_zero.mp hne
  rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at ha
  exact ⟨a, ha⟩

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_sup_mul_card_inf_of_normal' (A L : Subgroup G) [L.Normal] :
    Nat.card (A ⊔ L : Subgroup G) * Nat.card (A ⊓ L : Subgroup G) = Nat.card A * Nat.card L := by
  have h1 := Subgroup.relIndex_mul_card (H := L) (K := A ⊔ L)
  have h2 := Subgroup.relIndex_mul_card (H := L) (K := A)
  rw [Subgroup.relIndex_sup_right, inf_of_le_left (le_sup_right : L ≤ A ⊔ L)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

omit [Finite G] in
theorem card_sup_mul_card_inf_of_le_normalizer' {A B : Subgroup G}
    (hB : B ≤ normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set G)
  have hAN : A ≤ N := le_normalizer
  have : (A.subgroupOf N).Normal := normal_in_normalizer
  have h := card_sup_mul_card_inf_of_normal' (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup G, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

omit [Finite G] in
theorem le_normalizer_of_conj_mem {Y K M : Subgroup G} (hKn : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K)
    (hMY : M ≤ Y) : M ≤ normalizer (K : Set G) := by
  intro m hm
  rw [mem_normalizer_iff]
  intro k
  refine ⟨hKn m (hMY hm) k, fun h => ?_⟩
  have := hKn m⁻¹ (inv_mem (hMY hm)) _ h
  simpa [mul_assoc] using this

theorem exists_mul_of_mem_centralizer {Y K M : Subgroup G}
    (hKn : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hodd : Odd (Nat.card K)) (hMY : M ≤ Y)
    (hY : Y ≤ K ⊔ M) {u : G} (huM : u ∈ M) (hu : u * u = 1) {y : G} (hyY : y ∈ Y)
    (hyu : y ∈ centralizer ({u} : Set G)) :
    ∃ k ∈ K ⊓ centralizer ({u} : Set G), ∃ m ∈ M ⊓ centralizer ({u} : Set G), y = k * m := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hMN := le_normalizer_of_conj_mem hKn hMY
  have hyKM : y ∈ ((K ⊔ M : Subgroup G) : Set G) := hY hyY
  rw [coe_mul_of_right_le_normalizer_left K M hMN] at hyKM
  obtain ⟨k₀, hk₀, m₀, hm₀, hkm⟩ := hyKM
  have hk₀' : k₀ ∈ K := hk₀
  have hm₀' : m₀ ∈ M := hm₀
  have hy : y = k₀ * m₀ := hkm.symm
  subst hy
  have hcomm : u * (k₀ * m₀) = k₀ * m₀ * u := (mem_centralizer_singleton_iff.mp hyu).symm
  obtain ⟨c, hc⟩ : ∃ c : G, c = u * m₀⁻¹ * u * m₀ := ⟨_, rfl⟩
  have hcM : c ∈ M := by
    rw [hc]
    exact mul_mem (mul_mem (mul_mem huM (inv_mem hm₀')) huM) hm₀'
  have hdK : m₀ * u * m₀⁻¹ * u ∈ K := by
    have h1 : m₀ * u * m₀⁻¹ = k₀⁻¹ * u * k₀ := by
      have : k₀ * m₀ * u * (k₀ * m₀)⁻¹ = u := by
        rw [← hcomm]
        group
      calc m₀ * u * m₀⁻¹ = k₀⁻¹ * (k₀ * m₀ * u * (k₀ * m₀)⁻¹) * k₀ := by group
        _ = k₀⁻¹ * u * k₀ := by rw [this]
    rw [h1]
    have h2 : u * k₀ * u⁻¹ ∈ K := hKn u (hMY huM) k₀ hk₀'
    rw [huinv] at h2
    have : k₀⁻¹ * u * k₀ * u = k₀⁻¹ * (u * k₀ * u) := by group
    rw [this]
    exact mul_mem (inv_mem hk₀') h2
  have hcK : c ∈ K := by
    have : c = m₀⁻¹ * (m₀ * u * m₀⁻¹ * u) * m₀⁻¹⁻¹ := by
      rw [hc]
      group
    rw [this]
    exact hKn _ (hMY (inv_mem hm₀')) _ hdK
  have hσ : ∀ n ∈ K ⊓ M, c⁻¹ * (u * n * u) ∈ K ⊓ M := by
    intro n hn
    have h1 : u * n * u ∈ K := by
      have := hKn u (hMY huM) n (mem_inf.mp hn).1
      rwa [huinv] at this
    exact mem_inf.mpr ⟨mul_mem (inv_mem hcK) h1,
      mul_mem (inv_mem hcM) (mul_mem (mul_mem huM (mem_inf.mp hn).2) huM)⟩
  let τ : ↥(K ⊓ M) → ↥(K ⊓ M) := fun n => ⟨c⁻¹ * (u * n * u), hσ n n.2⟩
  have hucu : u * c * u = c⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [hc]
    calc u * (u * m₀⁻¹ * u * m₀) * u * (u * m₀⁻¹ * u * m₀) =
        (u * u) * m₀⁻¹ * u * m₀ * (u * u) * m₀⁻¹ * u * m₀ := by group
      _ = m₀⁻¹ * (u * m₀ * m₀⁻¹ * u) * m₀ := by rw [hu]; group
      _ = m₀⁻¹ * (u * u) * m₀ := by group
      _ = 1 := by rw [hu]; group
  have h1 : u * c⁻¹ * u = c := by
    calc u * c⁻¹ * u = u⁻¹ * c⁻¹ * u⁻¹ := by rw [huinv]
      _ = (u * c * u)⁻¹ := by group
      _ = c := by rw [hucu, inv_inv]
  have hτ : Function.Involutive τ := by
    intro n
    apply Subtype.ext
    change c⁻¹ * (u * (c⁻¹ * (u * (n : G) * u)) * u) = n
    calc c⁻¹ * (u * (c⁻¹ * (u * (n : G) * u)) * u)
        = c⁻¹ * (u * c⁻¹ * u) * (n : G) * (u * u) := by group
      _ = n := by rw [h1, hu]; group
  have hNodd : Odd (Nat.card ↥(K ⊓ M)) :=
    Odd.of_dvd_nat hodd (card_dvd_of_le inf_le_left)
  obtain ⟨n₀, hn₀⟩ := exists_eq_of_involutive hNodd hτ
  have hn₀' : c⁻¹ * (u * (n₀ : G) * u) = n₀ := congrArg Subtype.val hn₀
  have hn₀K : (n₀ : G) ∈ K := (mem_inf.mp n₀.2).1
  have hn₀M : (n₀ : G) ∈ M := (mem_inf.mp n₀.2).2
  have hun : u * (n₀ : G) * u = c * n₀ := by
    calc u * (n₀ : G) * u = c * (c⁻¹ * (u * (n₀ : G) * u)) := by group
      _ = c * n₀ := by rw [hn₀']
  have hmC : m₀ * (n₀ : G) ∈ centralizer ({u} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h2 : u * (m₀ * (n₀ : G)) * u = m₀ * n₀ := by
      calc u * (m₀ * (n₀ : G)) * u = u * m₀ * u⁻¹ * (u * (n₀ : G) * u) := by
            rw [huinv]
            calc u * (m₀ * (n₀ : G)) * u = u * m₀ * 1 * (n₀ : G) * u := by group
              _ = u * m₀ * (u * u) * (n₀ : G) * u := by rw [hu]
              _ = u * m₀ * u * (u * (n₀ : G) * u) := by group
        _ = u * m₀ * u⁻¹ * (c * n₀) := by rw [hun]
        _ = u * m₀ * u⁻¹ * (u * m₀⁻¹ * u * m₀ * n₀) := by rw [hc]
        _ = (u * u) * m₀ * n₀ := by group
        _ = m₀ * n₀ := by rw [hu]; group
    calc m₀ * (n₀ : G) * u = (u * u) * (m₀ * (n₀ : G)) * u := by rw [hu]; group
      _ = u * (u * (m₀ * (n₀ : G)) * u) := by group
      _ = u * (m₀ * n₀) := by rw [h2]
  have hmM : m₀ * (n₀ : G) ∈ M := mul_mem hm₀' hn₀M
  refine ⟨k₀ * m₀ * (m₀ * (n₀ : G))⁻¹, mem_inf.mpr ⟨?_, ?_⟩, m₀ * n₀, mem_inf.mpr ⟨hmM, hmC⟩,
    by group⟩
  · have : k₀ * m₀ * (m₀ * (n₀ : G))⁻¹ = k₀ * (m₀ * (n₀ : G)⁻¹ * m₀⁻¹) := by group
    rw [this]
    exact mul_mem hk₀' (hKn _ (hMY hm₀') _ (inv_mem hn₀K))
  · exact mul_mem hyu (inv_mem hmC)

theorem card_inf_centralizer_mul {Y K M : Subgroup G} (hKY : K ≤ Y)
    (hKn : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hodd : Odd (Nat.card K)) (hMY : M ≤ Y)
    (hY : Y ≤ K ⊔ M) {u : G} (huM : u ∈ M) (hu : u * u = 1) :
    Nat.card ↥(Y ⊓ centralizer ({u} : Set G)) *
        Nat.card ↥(K ⊓ M ⊓ centralizer ({u} : Set G)) =
      Nat.card ↥(K ⊓ centralizer ({u} : Set G)) * Nat.card ↥(M ⊓ centralizer ({u} : Set G)) := by
  set A := K ⊓ centralizer ({u} : Set G)
  set B := M ⊓ centralizer ({u} : Set G)
  have hBA : B ≤ normalizer (A : Set G) := by
    intro b hb
    rw [mem_normalizer_iff]
    intro a
    have hbN := le_normalizer_of_conj_mem hKn hMY hb.1
    have hbC : b ∈ normalizer (centralizer ({u} : Set G) : Set G) := le_normalizer hb.2
    rw [mem_normalizer_iff] at hbN hbC
    exact ⟨fun ha => ⟨(hbN a).mp ha.1, (hbC a).mp ha.2⟩,
      fun ha => ⟨(hbN a).mpr ha.1, (hbC a).mpr ha.2⟩⟩
  have hsup : A ⊔ B = Y ⊓ centralizer ({u} : Set G) := by
    apply le_antisymm
    · exact sup_le (le_inf (inf_le_left.trans hKY) inf_le_right)
        (le_inf (inf_le_left.trans hMY) inf_le_right)
    · rintro y ⟨hyY, hyu⟩
      obtain ⟨k, hk, m, hm, rfl⟩ :=
        exists_mul_of_mem_centralizer hKn hodd hMY hY huM hu hyY hyu
      exact mul_mem_sup hk hm
  have hinf : A ⊓ B = K ⊓ M ⊓ centralizer ({u} : Set G) := by
    ext x
    simp only [A, B, mem_inf]
    tauto
  rw [← hsup, ← hinf]
  exact card_sup_mul_card_inf_of_le_normalizer' hBA

omit [Finite G] in
theorem card_inf_centralizer_conj {X : Subgroup G} {g : G} (hg : g ∈ normalizer (X : Set G))
    (t : G) :
    Nat.card ↥(X ⊓ centralizer ({g * t * g⁻¹} : Set G)) =
      Nat.card ↥(X ⊓ centralizer ({t} : Set G)) := by
  have hmap : (X ⊓ centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom =
      X ⊓ centralizer ({g * t * g⁻¹} : Set G) := by
    ext x
    simp only [mem_map, mem_inf, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, ⟨hyX, hyt⟩, rfl⟩
      refine ⟨(mem_normalizer_iff.mp hg y).mp hyX, ?_⟩
      calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
        _ = g * (t * y) * g⁻¹ := by rw [hyt]
        _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
    · rintro ⟨hxX, hxt⟩
      refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, by group⟩
      · have := (mem_normalizer_iff.mp (inv_mem hg) x).mp hxX
        simpa using this
      · calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hxt]
          _ = t * (g⁻¹ * x * g) := by group
  rw [← hmap, card_map_of_injective (MulAut.conj g).injective]

theorem card_mul_card_le_of_brauerWielandt {Y K M : Subgroup G} (hKY : K ≤ Y)
    (hKn : ∀ y ∈ Y, ∀ k ∈ K, y * k * y⁻¹ ∈ K) (hodd : Odd (Nat.card K)) (hMY : M ≤ Y)
    (hY : Y ≤ K ⊔ M) {z t i : G} (hMz : M ≤ centralizer ({z} : Set G)) (hz : z * z = 1)
    (ht : t * t = 1) (hi : i * i = 1) (hz1 : z ≠ 1) (ht1 : t ≠ 1) (hi1 : i ≠ 1)
    (hzt : z ≠ t) (hzi : z ≠ i) (hzM : z ∈ M) (htM : t ∈ M) (hiM : i ∈ M)
    (hKT : K ⊓ centralizer ({z, t} : Set G) ≤ M) (hct : ∃ g ∈ M, g * t * g⁻¹ = z * t)
    (hci : ∃ g ∈ M, g * i * g⁻¹ = z * i) :
    Nat.card ↥(Y ⊓ centralizer ({t} : Set G)) * Nat.card ↥(M ⊓ centralizer ({i} : Set G)) ≤
      Nat.card ↥(Y ⊓ centralizer ({i} : Set G)) * Nat.card ↥(M ⊓ centralizer ({t} : Set G)) := by
  have hMN := le_normalizer_of_conj_mem hKn hMY
  have hcomm : ∀ x ∈ M, Commute z x := fun x hx =>
    (mem_centralizer_singleton_iff.mp (hMz hx)).symm
  have bw1 := card_mul_card_inf_centralizer_sq hodd hz ht (hcomm t htM) hz1 ht1 hzt
    (hMN hzM) (hMN htM)
  have bw2 := card_mul_card_inf_centralizer_sq hodd hz hi (hcomm i hiM) hz1 hi1 hzi
    (hMN hzM) (hMN hiM)
  obtain ⟨g, hgM, hg⟩ := hct
  obtain ⟨g', hg'M, hg'⟩ := hci
  have hK1 : Nat.card ↥(K ⊓ centralizer ({z * t} : Set G)) =
      Nat.card ↥(K ⊓ centralizer ({t} : Set G)) := by
    rw [← hg]
    exact card_inf_centralizer_conj (hMN hgM) t
  have hK2 : Nat.card ↥(K ⊓ centralizer ({z * i} : Set G)) =
      Nat.card ↥(K ⊓ centralizer ({i} : Set G)) := by
    rw [← hg']
    exact card_inf_centralizer_conj (hMN hg'M) i
  rw [hK1] at bw1
  rw [hK2] at bw2
  have f1 := card_inf_centralizer_mul hKY hKn hodd hMY hY htM ht
  have f2 := card_inf_centralizer_mul hKY hKn hodd hMY hY hiM hi
  have hT : K ⊓ M ⊓ centralizer ({t} : Set G) = K ⊓ centralizer ({z, t} : Set G) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxKM, hxt⟩ := mem_inf.mp hx
      obtain ⟨hxK, hxM⟩ := mem_inf.mp hxKM
      refine mem_inf.mpr ⟨hxK, mem_centralizer_iff.mpr ?_⟩
      rintro y (rfl | rfl)
      · exact (mem_centralizer_iff.mp (hMz hxM)) _ rfl
      · exact (mem_centralizer_iff.mp hxt) _ rfl
    · intro x hx
      obtain ⟨hxK, hxzt⟩ := mem_inf.mp hx
      refine mem_inf.mpr ⟨mem_inf.mpr ⟨hxK, hKT hx⟩, mem_centralizer_iff.mpr ?_⟩
      rintro y rfl
      exact (mem_centralizer_iff.mp hxzt) _ (Set.mem_insert_of_mem _ rfl)
  have hT₂ : K ⊓ M ⊓ centralizer ({i} : Set G) ≤ K ⊓ centralizer ({z, i} : Set G) := by
    intro x hx
    obtain ⟨hxKM, hxi⟩ := mem_inf.mp hx
    obtain ⟨hxK, hxM⟩ := mem_inf.mp hxKM
    refine mem_inf.mpr ⟨hxK, mem_centralizer_iff.mpr ?_⟩
    rintro y (rfl | rfl)
    · exact (mem_centralizer_iff.mp (hMz hxM)) _ rfl
    · exact (mem_centralizer_iff.mp hxi) _ rfl
  rw [hT] at f1
  have f2' := Subgroup.card_le_of_le hT₂
  set a := Nat.card K
  set b := Nat.card ↥(K ⊓ centralizer ({z} : Set G))
  set c₁ := Nat.card ↥(K ⊓ centralizer ({z, t} : Set G))
  set c₂ := Nat.card ↥(K ⊓ centralizer ({z, i} : Set G))
  set kt := Nat.card ↥(K ⊓ centralizer ({t} : Set G))
  set ki := Nat.card ↥(K ⊓ centralizer ({i} : Set G))
  set yt := Nat.card ↥(Y ⊓ centralizer ({t} : Set G))
  set yi := Nat.card ↥(Y ⊓ centralizer ({i} : Set G))
  set mt := Nat.card ↥(M ⊓ centralizer ({t} : Set G))
  set mi := Nat.card ↥(M ⊓ centralizer ({i} : Set G))
  set d := Nat.card ↥(K ⊓ M ⊓ centralizer ({i} : Set G))
  have hc₁ : 0 < c₁ := Nat.card_pos
  have hb : 0 < b := Nat.card_pos
  have e1 : a * mt ^ 2 = b * yt ^ 2 := by
    have h : a * c₁ ^ 2 * mt ^ 2 = b * yt ^ 2 * c₁ ^ 2 := by
      calc a * c₁ ^ 2 * mt ^ 2 = b * (kt * mt) ^ 2 := by rw [bw1]; ring
        _ = b * (yt * c₁) ^ 2 := by rw [← f1]
        _ = b * yt ^ 2 * c₁ ^ 2 := by ring
    have hc : 0 < c₁ ^ 2 := pow_pos hc₁ 2
    have h' : a * mt ^ 2 * c₁ ^ 2 = b * yt ^ 2 * c₁ ^ 2 := by
      calc a * mt ^ 2 * c₁ ^ 2 = a * c₁ ^ 2 * mt ^ 2 := by ring
        _ = b * yt ^ 2 * c₁ ^ 2 := h
    exact Nat.eq_of_mul_eq_mul_right hc h'
  have e2 : a * mi ^ 2 ≤ b * yi ^ 2 := by
    have hc₂ : 0 < c₂ := Nat.card_pos
    have h1 : ki * mi ≤ yi * c₂ := by
      calc ki * mi = yi * d := f2.symm
        _ ≤ yi * c₂ := Nat.mul_le_mul_left _ f2'
    have h : a * c₂ ^ 2 * mi ^ 2 ≤ b * yi ^ 2 * c₂ ^ 2 := by
      calc a * c₂ ^ 2 * mi ^ 2 = b * (ki * mi) ^ 2 := by rw [bw2]; ring
        _ ≤ b * (yi * c₂) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 2)
        _ = b * yi ^ 2 * c₂ ^ 2 := by ring
    have hc : 0 < c₂ ^ 2 := pow_pos hc₂ 2
    have h' : a * mi ^ 2 * c₂ ^ 2 ≤ b * yi ^ 2 * c₂ ^ 2 := by
      calc a * mi ^ 2 * c₂ ^ 2 = a * c₂ ^ 2 * mi ^ 2 := by ring
        _ ≤ b * yi ^ 2 * c₂ ^ 2 := h
    exact Nat.le_of_mul_le_mul_right h' hc
  have h3 : b * (yt * mi) ^ 2 ≤ b * (yi * mt) ^ 2 := by
    calc b * (yt * mi) ^ 2 = (b * yt ^ 2) * mi ^ 2 := by ring
      _ = a * mt ^ 2 * mi ^ 2 := by rw [e1]
      _ = (a * mi ^ 2) * mt ^ 2 := by ring
      _ ≤ (b * yi ^ 2) * mt ^ 2 := Nat.mul_le_mul_right _ e2
      _ = b * (yi * mt) ^ 2 := by ring
  have h4 := Nat.le_of_mul_le_mul_left h3 hb
  exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp h4

end CFSG.ComponentClassification.HarrisLit.T1.S74
