module

public import CFSG.GH74.Uniqueness.Section15Defs
public import CFSG.GH74.Uniqueness.Section128Index

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X]

namespace Facts15

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V : Subgroup X}

theorem K_le_D (F : Facts15 M n L D K J Mo V) : K ≤ D := F.K_eq ▸ inf_le_left

theorem K_le_L (F : Facts15 M n L D K J Mo V) : K ≤ L := F.K_eq ▸ inf_le_right

theorem K_le_M (F : Facts15 M n L D K J Mo V) : K ≤ M := F.K_le_D.trans F.D_le

theorem J_le_M (F : Facts15 M n L D K J Mo V) : J ≤ M := F.J_le_D.trans F.D_le

theorem odd_card_K (F : Facts15 M n L D K J Mo V) : Odd (Nat.card K) := by
  rw [F.card_K]
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by linarith [F.two_le])
  have heven : Even (2 ^ n) := (Nat.even_pow' (by linarith [F.two_le])).mpr even_two
  obtain ⟨k, hk⟩ := heven
  exact ⟨k - 1, by omega⟩

theorem Mo_isPGroup (F : Facts15 M n L D K J Mo V) : IsPGroup 2 Mo :=
  IsPGroup.of_card F.card_Mo

theorem Mo_le_V (F : Facts15 M n L D K J Mo V) : Mo ≤ V :=
  F.V_max Mo F.Mo_le_M F.Mo_normal F.Mo_isPGroup

theorem eq_one_of_mem_odd {H : Subgroup X} (hH : Odd (Nat.card H)) {x : X} (hx : x ∈ H)
    (hx2 : x * x = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have h2 : orderOf x ∣ Nat.card H := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥H)
    rwa [Subgroup.orderOf_mk] at this
  have h3 : orderOf x ∣ Nat.gcd 2 (Nat.card H) := Nat.dvd_gcd h1 h2
  have h4 : Nat.gcd 2 (Nat.card H) = 1 :=
    (Nat.coprime_two_left.mpr hH)
  rw [h4, Nat.dvd_one, orderOf_eq_one_iff] at h3
  exact h3

theorem J_comm (F : Facts15 M n L D K J Mo V) {j : X} (hj : j ∈ J) {l : X} (hl : l ∈ L) :
    j * l = l * j := by
  rw [F.J_eq] at hj
  exact (mem_centralizer_iff.mp hj l hl).symm

theorem J_comm_Mo (F : Facts15 M n L D K J Mo V) {j : X} (hj : j ∈ J) {x : X} (hx : x ∈ Mo) :
    j * x = x * j := F.J_comm hj (F.Mo_le_L hx)

theorem eq_one_of_mem_L_J (F : Facts15 M n L D K J Mo V) {x : X} (hxL : x ∈ L) (hxJ : x ∈ J) :
    x = 1 := by
  have : x ∈ L ⊓ J := mem_inf.mpr ⟨hxL, hxJ⟩
  rw [F.L_inf_J] at this
  exact mem_bot.mp this

theorem eq_one_of_mem_Mo_D (F : Facts15 M n L D K J Mo V) {x : X} (hxMo : x ∈ Mo)
    (hxD : x ∈ D) : x = 1 := by
  have hxK : x ∈ K := by
    rw [F.K_eq]
    exact mem_inf.mpr ⟨hxD, F.Mo_le_L hxMo⟩
  exact eq_one_of_mem_odd F.odd_card_K hxK (F.Mo_sq x hxMo)

theorem D_conj_L (F : Facts15 M n L D K J Mo V) {d : X} (hd : d ∈ D) {l : X} (hl : l ∈ L) :
    d * l * d⁻¹ ∈ L := (mem_normalizer_iff.mp (F.D_le_N hd) l).mp hl

theorem D_conj_K (F : Facts15 M n L D K J Mo V) {d : X} (hd : d ∈ D) {k : X} (hk : k ∈ K) :
    d * k * d⁻¹ ∈ K := by
  rw [F.K_eq] at hk ⊢
  obtain ⟨hkD, hkL⟩ := mem_inf.mp hk
  exact mem_inf.mpr ⟨mul_mem (mul_mem hd hkD) (inv_mem hd), F.D_conj_L hd hkL⟩

theorem N_conj_J (F : Facts15 M n L D K J Mo V) {g : X} (hg : g ∈ normalizer (L : Set X))
    {j : X} (hj : j ∈ J) : g * j * g⁻¹ ∈ J := by
  rw [F.J_eq] at hj ⊢
  rw [mem_centralizer_iff]
  intro l hl
  have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L := (mem_normalizer_iff.mp (inv_mem hg) l).mp hl
  have h1 := mem_centralizer_iff.mp hj _ hl'
  rw [inv_inv] at h1 hl'
  calc l * (g * j * g⁻¹) = g * ((g⁻¹ * l * g) * j) * g⁻¹ := by group
    _ = g * (j * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
    _ = g * j * g⁻¹ * l := by group

theorem D_conj_J (F : Facts15 M n L D K J Mo V) {d : X} (hd : d ∈ D) {j : X} (hj : j ∈ J) :
    d * j * d⁻¹ ∈ J := F.N_conj_J (F.D_le_N hd) hj

theorem eq_one_of_mem_K_J (F : Facts15 M n L D K J Mo V) {x : X} (hxK : x ∈ K) (hxJ : x ∈ J) :
    x = 1 := F.eq_one_of_mem_L_J (F.K_le_L hxK) hxJ

theorem C0_conj (F : Facts15 M n L D K J Mo V) {g : X} (hg : g ∈ M) {x : X}
    (hx : x ∈ centralizer (Mo : Set X)) : g * x * g⁻¹ ∈ centralizer (Mo : Set X) := by
  rw [mem_centralizer_iff]
  intro m hm
  have hm' : g⁻¹ * m * g⁻¹⁻¹ ∈ Mo := F.Mo_normal g⁻¹ (inv_mem hg) m hm
  rw [inv_inv] at hm'
  have h1 := mem_centralizer_iff.mp hx _ hm'
  calc m * (g * x * g⁻¹) = g * ((g⁻¹ * m * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * m * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * m := by group

theorem J_le_C0 (F : Facts15 M n L D K J Mo V) : J ≤ centralizer (Mo : Set X) := by
  intro j hj
  rw [mem_centralizer_iff]
  intro x hx
  exact (F.J_comm_Mo hj hx).symm

theorem V_le_C0 (F : Facts15 M n L D K J Mo V) : V ≤ centralizer (Mo : Set X) := by
  intro v hv
  rw [mem_centralizer_iff]
  intro x hx
  exact (F.V_comm v hv x hx).symm

theorem mem_J_of_comm (F : Facts15 M n L D K J Mo V) {d : X} (hd : d ∈ D)
    (hcomm : ∀ x ∈ Mo, d * x = x * d) : d ∈ J := by
  obtain ⟨m, hm, j, hj, rfl⟩ := F.cent_Mo_N d (F.D_le_N hd) hcomm
  have hmD : m ∈ D := by
    have e : m = m * j * j⁻¹ := by group
    rw [e]
    exact mul_mem hd (inv_mem (F.J_le_D hj))
  rw [F.eq_one_of_mem_Mo_D hm hmD, one_mul]
  exact hj

theorem C0_inf_D (F : Facts15 M n L D K J Mo V) : centralizer (Mo : Set X) ⊓ D = J := by
  apply le_antisymm
  · intro d hd
    obtain ⟨hdC, hdD⟩ := mem_inf.mp hd
    exact F.mem_J_of_comm hdD fun x hx => (mem_centralizer_iff.mp hdC x hx).symm
  · exact le_inf F.J_le_C0 F.J_le_D

theorem card_C0_dvd [Finite X] (F : Facts15 M n L D K J Mo V) :
    Nat.card (centralizer (Mo : Set X)) ∣ 2 ^ (3 * n) * Nat.card J := by
  have hDN : D ≤ normalizer (centralizer (Mo : Set X) : Set X) := by
    intro d hd
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact F.C0_conj (F.D_le hd) hx
    · intro hx
      have := F.C0_conj (inv_mem (F.D_le hd)) hx
      have e : d⁻¹ * (d * x * d⁻¹) * d⁻¹⁻¹ = x := by group
      rwa [e] at this
  have h1 := Sec128.card_sup_mul_card_inf_of_le_normalizer hDN
  rw [F.C0_inf_D] at h1
  have hsupM : centralizer (Mo : Set X) ⊔ D ≤ M := sup_le F.cent_Mo_le F.D_le
  have h2 : Nat.card ↥(centralizer (Mo : Set X) ⊔ D) ∣ Nat.card M :=
    Subgroup.card_dvd_of_le hsupM
  rw [F.card_M] at h2
  have hD : 0 < Nat.card D := Nat.card_pos
  have h3 : Nat.card (centralizer (Mo : Set X)) * Nat.card D ∣
      2 ^ (3 * n) * Nat.card J * Nat.card D := by
    rw [← h1]
    calc Nat.card ↥(centralizer (Mo : Set X) ⊔ D) * Nat.card J
        ∣ 2 ^ (3 * n) * Nat.card D * Nat.card J := Nat.mul_dvd_mul_right h2 _
      _ = 2 ^ (3 * n) * Nat.card J * Nat.card D := by ring
  exact Nat.dvd_of_mul_dvd_mul_right hD h3

end Facts15

end CFSG.GH74.Uniqueness
