module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.KS.Co2I301

open Subgroup

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem card_cent_le {G : Subgroup (Equiv.Perm α)} {x : Equiv.Perm α} {N : ℕ}
    (y : ℕ → Equiv.Perm α) (hy : ∀ j < N, ∃ h ∈ G, y j = h * x * h⁻¹)
    (hinj : ∀ i < N, ∀ j < N, y i = y j → i = j) :
    N * Nat.card ↥(G ⊓ centralizer {x}) ≤ Nat.card G := by
  choose! hh hhG hhy using hy
  let F : Fin N × ↥(G ⊓ centralizer {x}) → ↥G := fun p =>
    ⟨hh p.1 * p.2, G.mul_mem (hhG p.1 p.1.2) (mem_inf.1 p.2.2).1⟩
  have hF : Function.Injective F := by
    rintro ⟨i, c⟩ ⟨j, c'⟩ e
    have e' : hh i * c = hh j * c' := congrArg Subtype.val e
    have hc : (c : Equiv.Perm α) * x = x * c :=
      (mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2)
    have hc' : (c' : Equiv.Perm α) * x = x * c' :=
      (mem_centralizer_singleton_iff.1 (mem_inf.1 c'.2).2)
    have hyi : y i = (hh i * c) * x * (hh i * c)⁻¹ := by
      rw [hhy i i.2, mul_inv_rev, mul_assoc (hh i) (c : Equiv.Perm α), hc]
      group
    have hyj : y j = (hh j * c') * x * (hh j * c')⁻¹ := by
      rw [hhy j j.2, mul_inv_rev, mul_assoc (hh j) (c' : Equiv.Perm α), hc']
      group
    have hij : i = j := Fin.ext (hinj i i.2 j j.2 (by rw [hyi, hyj, e']))
    subst hij
    refine Prod.ext rfl (Subtype.ext ?_)
    exact mul_left_cancel e'
  have := Nat.card_le_card_of_injective F hF
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin] at this

theorem exists_of_card_le {H : Subgroup (Equiv.Perm α)} {M : ℕ} (z : ℕ → Equiv.Perm α)
    (hz : ∀ i < M, z i ∈ H) (hinj : ∀ i < M, ∀ j < M, z i = z j → i = j)
    (hcard : Nat.card H ≤ M) : ∀ c ∈ H, ∃ i < M, z i = c := by
  let F : Fin M → ↥H := fun i => ⟨z i, hz i i.2⟩
  have hF : Function.Injective F := fun i j e =>
    Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val e))
  have hbij : Function.Bijective F := by
    refine hF.bijective_of_nat_card_le ?_
    rw [Nat.card_eq_fintype_card (α := Fin M), Fintype.card_fin]
    exact hcard
  intro c hc
  obtain ⟨i, hi⟩ := hbij.2 ⟨c, hc⟩
  exact ⟨i, i.2, congrArg Subtype.val hi⟩

theorem card_eq_of_cover {H : Subgroup (Equiv.Perm α)} {N : ℕ} (z : ℕ → Equiv.Perm α)
    (hz : ∀ i < N, z i ∈ H) (hinj : ∀ i < N, ∀ j < N, z i = z j → i = j)
    (hcov : ∀ c ∈ H, ∃ i < N, z i = c) : Nat.card H = N := by
  let F : Fin N → ↥H := fun i => ⟨z i, hz i i.2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun i j e => Fin.ext (hinj i i.2 j j.2 (congrArg Subtype.val e)), fun c => ?_⟩
    obtain ⟨i, hi, e⟩ := hcov c c.2
    exact ⟨⟨i, hi⟩, Subtype.ext e⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem mul_inv_mem_of_mul {M : Set (Equiv.Perm α)} {g : Equiv.Perm α}
    (h : ∀ m ∈ M, m * g ∈ M) : ∀ m ∈ M, m * g⁻¹ ∈ M := by
  have hfin : M.Finite := Set.toFinite M
  have hinj : Set.InjOn (fun m => m * g) M := fun a _ b _ e => mul_right_cancel e
  have hsurj : Set.SurjOn (fun m => m * g) M M :=
    ((Set.Finite.injOn_iff_bijOn_of_mapsTo hfin fun m hm => h m hm).1 hinj).surjOn
  intro m hm
  obtain ⟨m', hm', e⟩ := hsurj hm
  have : m * g⁻¹ = m' := by rw [← e]; group
  rw [this]
  exact hm'

theorem closure_subset_of_mul {M : Set (Equiv.Perm α)} {S : Set (Equiv.Perm α)} (h1 : 1 ∈ M)
    (h : ∀ m ∈ M, ∀ g ∈ S, m * g ∈ M) : (closure S : Set (Equiv.Perm α)) ⊆ M := by
  suffices key : ∀ x ∈ closure S, ∀ m ∈ M, m * x ∈ M by
    intro x hx
    have := key x hx 1 h1
    rwa [one_mul] at this
  intro x hx
  induction hx using closure_induction with
  | mem g hg => exact fun m hm => h m hm g hg
  | one => exact fun m hm => by rwa [mul_one]
  | mul a b _ _ ha hb => exact fun m hm => by rw [← mul_assoc]; exact hb _ (ha m hm)
  | inv a _ ha => exact mul_inv_mem_of_mul ha

theorem conj_inv_mem_of_conj {M : Set (Equiv.Perm α)} {g : Equiv.Perm α}
    (h : ∀ m ∈ M, g * m * g⁻¹ ∈ M) : ∀ m ∈ M, g⁻¹ * m * g ∈ M := by
  have hfin : M.Finite := Set.toFinite M
  have hinj : Set.InjOn (fun m => g * m * g⁻¹) M := fun a _ b _ e => by
    simpa using e
  have hsurj : Set.SurjOn (fun m => g * m * g⁻¹) M M :=
    ((Set.Finite.injOn_iff_bijOn_of_mapsTo hfin fun m hm => h m hm).1 hinj).surjOn
  intro m hm
  obtain ⟨m', hm', e⟩ := hsurj hm
  have : g⁻¹ * m * g = m' := by rw [← e]; group
  rw [this]
  exact hm'

theorem conj_mem_of_closure {M : Set (Equiv.Perm α)} {S : Set (Equiv.Perm α)}
    (h : ∀ m ∈ M, ∀ g ∈ S, g * m * g⁻¹ ∈ M) :
    ∀ x ∈ closure S, ∀ m ∈ M, x * m * x⁻¹ ∈ M := by
  intro x hx
  induction hx using closure_induction with
  | mem g hg => exact fun m hm => h m hm g hg
  | one => exact fun m hm => by rwa [one_mul, inv_one, mul_one]
  | mul a b _ _ ha hb =>
    intro m hm
    have e : a * b * m * (a * b)⁻¹ = a * (b * m * b⁻¹) * a⁻¹ := by group
    rw [e]
    exact ha _ (hb m hm)
  | inv a _ ha =>
    intro m hm
    rw [inv_inv]
    exact conj_inv_mem_of_conj ha m hm

theorem exists_conj_mem_of_sylow {G T : Subgroup (Equiv.Perm α)} (hTG : T ≤ G) {a : ℕ}
    (hT : Nat.card T = 2 ^ a) (hodd : ¬ 2 ∣ Nat.card G / Nat.card T) {g : Equiv.Perm α}
    (hg : g ∈ G) (hg2 : g * g = 1) : ∃ h ∈ G, h⁻¹ * g * h ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T' : Subgroup G := T.subgroupOf G
  have hcT' : Nat.card T' = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTG).toEquiv
  have hpT : IsPGroup 2 T' := IsPGroup.of_card (hcT'.trans hT)
  have hidx : T'.index = Nat.card G / Nat.card T := by
    have h := T'.card_mul_index
    rw [hcT'] at h
    have hpos : 0 < Nat.card T := Nat.card_pos
    rw [← h, Nat.mul_div_cancel_left _ hpos]
  let P : Sylow 2 G := hpT.toSylow (by rw [hidx]; exact hodd)
  set gG : G := ⟨g, hg⟩
  have hg2' : gG ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hg2)
  have hpg : IsPGroup 2 (zpowers gG) := by
    have hd : orderOf gG ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hg2')
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := hpg.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G P Q
  have hgQ : gG ∈ (Q : Subgroup G) := hQ (mem_zpowers gG)
  rw [← hh, Sylow.smul_def, Sylow.pointwise_smul_def,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hgQ
  refine ⟨h, h.2, ?_⟩
  have e : (MulAut.conj h)⁻¹ • gG = h⁻¹ * gG * h := by
    rw [MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  rw [e] at hgQ
  have hm : h⁻¹ * gG * h ∈ T' := by
    have := hgQ
    rwa [IsPGroup.toSylow_coe] at this
  rw [Subgroup.mem_subgroupOf] at hm
  simpa using hm

end CFSG.KS.Co2I301

end
