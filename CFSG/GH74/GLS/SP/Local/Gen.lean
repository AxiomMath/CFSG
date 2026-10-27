module

public import CFSG.GH74.GLS.SP.Local.Defs
public import CFSG.GH74.GLS.LU.Local.SL2Sylow

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS
open CFSG.GH74.GLS.LU.Local

section Gen

variable {G : Type} [Group G] [Finite G] {q : ℕ} {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem SPSyl.z_mem (h : SPSyl G z S K₁ K₂ t) : z ∈ (S : Subgroup G) := by
  have hz : z ∈ (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype := by
    rw [h.z_cen]; exact mem_zpowers z
  obtain ⟨y, -, hyz⟩ := Subgroup.mem_map.mp hz
  rw [← hyz]; exact y.2

omit [Finite G] in
theorem SPSyl.comm_z (h : SPSyl G z S K₁ K₂ t) {s : G} (hs : s ∈ (S : Subgroup G)) :
    s * z = z * s := by
  have hz : z ∈ (center ↥(S : Subgroup G)).map (S : Subgroup G).subtype := by
    rw [h.z_cen]; exact mem_zpowers z
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
  have h1 := Subgroup.mem_center_iff.mp hy ⟨s, hs⟩
  have h3 : s * (y : G) = (y : G) * s := congrArg Subtype.val h1
  have h4 : (y : G) = z := hyz
  rw [h4] at h3
  exact h3

theorem mem_zpowers_of_central (hc : LUComps G q z K₁ K₂) {s : G} (hs : s ∈ K₁ ⊔ K₂)
    (hsK : ∀ k ∈ K₁ ⊔ K₂, s * k = k * s) : s ∈ zpowers z := by
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := mem_sup_of_commute hc.comm hs
  have h1 : ∀ x ∈ K₁, k₁ * x = x * k₁ := by
    intro x hx
    have e := hsK x (Subgroup.mem_sup_left hx)
    have hk₂x : k₂ * x = x * k₂ := (hc.comm x hx k₂ hk₂).symm
    have : k₁ * x * k₂ = x * k₁ * k₂ := by
      calc k₁ * x * k₂ = k₁ * (x * k₂) := by group
        _ = k₁ * (k₂ * x) := by rw [← hk₂x]
        _ = k₁ * k₂ * x := by group
        _ = x * (k₁ * k₂) := e
        _ = x * k₁ * k₂ := by group
    exact mul_right_cancel this
  have h2 : ∀ x ∈ K₂, k₂ * x = x * k₂ := by
    intro x hx
    have e := hsK x (Subgroup.mem_sup_right hx)
    have hk₁x : x * k₁ = k₁ * x := (hc.comm k₁ hk₁ x hx).symm
    have : k₁ * (k₂ * x) = k₁ * (x * k₂) := by
      calc k₁ * (k₂ * x) = k₁ * k₂ * x := by group
        _ = x * (k₁ * k₂) := e
        _ = (x * k₁) * k₂ := by group
        _ = (k₁ * x) * k₂ := by rw [hk₁x]
        _ = k₁ * (x * k₂) := by group
    exact mul_left_cancel this
  have z₁ : k₁ ∈ (center ↥K₁).map K₁.subtype := ⟨⟨k₁, hk₁⟩, Subgroup.mem_center_iff.mpr
    (fun g => Subtype.ext (h1 g g.2).symm), rfl⟩
  have z₂ : k₂ ∈ (center ↥K₂).map K₂.subtype := ⟨⟨k₂, hk₂⟩, Subgroup.mem_center_iff.mpr
    (fun g => Subtype.ext (h2 g g.2).symm), rfl⟩
  rw [hc.cen₁] at z₁
  rw [hc.cen₂] at z₂
  exact Subgroup.mul_mem _ z₁ z₂

theorem SPSyl.toGen (hc : LUComps G q z K₁ K₂) (h : SPSyl G z S K₁ K₂ t) :
    GenSyl G z S K₁ K₂ t 1 := by
  refine ⟨h.z_inv, h.z_mem, fun s hs => h.comm_z hs, h.t_mem, h.t_swap, Subgroup.one_mem _,
    Subgroup.one_mem _, mul_one 1, ?_⟩
  intro s hs hsK
  have hsn : s ∈ normalizer (K₁ : Set G) := by
    refine Subgroup.centralizer_le_normalizer (K₁ : Set G) ?_
    refine mem_centralizer_iff.mpr (fun k hk => ?_)
    exact (hsK k (Subgroup.mem_sup_left hk)).symm
  set Q : Subgroup G := (S : Subgroup G) ⊓ (K₁ ⊔ K₂) with hQ
  set N₁ : Subgroup G := (S : Subgroup G) ⊓ normalizer (K₁ : Set G) with hN₁
  have hQN : Q ≤ N₁ := inf_le_inf_left _ hc.le_normalizer₁
  have htn : t ∉ normalizer (K₁ : Set G) := by
    intro htn
    have := Subgroup.mem_normalizer_iff_map_conj_eq.mp htn
    exact hc.ne (this.symm.trans h.t_swap)
  have hN1 : N₁ = Q := by
    have hd1 : Nat.card ↥Q ∣ Nat.card ↥N₁ := Subgroup.card_dvd_of_le hQN
    have hd2 : Nat.card ↥N₁ ∣ Nat.card ↥(S : Subgroup G) := Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨m, hm⟩ := hd1
    have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
    rw [h.index, hm] at hd2
    have hm2 : m ∣ 2 := by
      have : Nat.card ↥Q * m ∣ Nat.card ↥Q * 2 := by rwa [mul_comm 2] at hd2
      exact Nat.dvd_of_mul_dvd_mul_left hQpos this
    rcases (Nat.dvd_prime Nat.prime_two).mp hm2 with h1 | h2
    · refine (Subgroup.eq_of_le_of_card_ge hQN ?_).symm
      rw [hm, h1, mul_one]
    · exfalso
      apply htn
      have hS : N₁ = (S : Subgroup G) := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left
        rw [h.index, hm, h2, mul_comm]
      have : t ∈ N₁ := by rw [hS]; exact h.t_mem
      exact this.2
  have hsQ : s ∈ Q := by rw [← hN1]; exact ⟨hs, hsn⟩
  exact mem_zpowers_of_central hc hsQ.2 hsK

theorem sp_gen {F : Type} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) (hodd : Odd (Nat.card F))
    (hc : LUComps G (Nat.card F) z K₁ K₂) (hs : SPSyl G z S K₁ K₂ t) (hA : pPrimeCoreOf 2 (Cz z) = ⊥) :
    ∀ c ∈ Cz z, ∃ k ∈ K₁ ⊔ K₂, ∃ s ∈ (S : Subgroup G),
      ∃ y ∈ pPrimeCoreOf 2 (centralizer (((S : Subgroup G) ⊓ (K₁ ⊔ K₂) : Subgroup G) : Set G)),
        c = k * s * y := by
  have hAbot : A0 z = ⊥ := hA
  have : IsCyclic ↥(A0 z) := by rw [hAbot]; infer_instance
  have h5 : 5 ≤ Nat.card F := by
    obtain ⟨m, hm⟩ := hodd
    omega
  have hu : ∀ a ∈ A0 z, (1 : G) * a * (1 : G)⁻¹ = a := fun a _ => by group
  intro c hc'
  obtain ⟨a, ha, k, hk, s, hsS, y, hy, hcy⟩ :=
    lu_gen_of_sl2 SL2.sl2SylowLeaf hc (hs.toGen hc) hodd h5 hu c hc'
  have ha1 : a = 1 := by
    rw [hAbot] at ha; exact (Subgroup.mem_bot.mp ha)
  have hF1 : Fstar (S : Subgroup G) K₁ K₂ 1 =
      pPrimeCoreOf 2 (centralizer (((S : Subgroup G) ⊓ (K₁ ⊔ K₂) : Subgroup G) : Set G)) := by
    unfold Fstar
    rw [zpowers_one_eq_bot, sup_bot_eq]
  refine ⟨k, hk, s, hsS, y, by rw [← hF1]; exact hy, ?_⟩
  rw [hcy, ha1, one_mul]

end Gen

end CFSG.GH74.GLS.SP.Local
