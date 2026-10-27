module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Klein
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Perfect

variable {G : Type*} [Group G] [Finite G]

theorem le_of_perfect_of_relIndex_le_two {Y Y₀ : Subgroup G} (hY : ⁅Y, Y⁆ = Y)
    (h2 : Y₀.relIndex Y ≤ 2) : Y ≤ Y₀ := by
  have hP : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hY
  set H : Subgroup ↥Y := Y₀.subgroupOf Y with hH
  have hidx : H.index = Y₀.relIndex Y := rfl
  have hpos : 0 < H.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have htop : H = ⊤ := by
    rcases Nat.lt_or_ge H.index 2 with hlt | hge
    · have : H.index = 1 := by omega
      exact Subgroup.index_eq_one.mp this
    · have h2' : H.index = 2 := by omega
      have : H.Normal := Subgroup.normal_of_index_eq_two h2'
      have hc : IsCyclic (↥Y ⧸ H) := by
        apply isCyclic_of_prime_card (p := 2)
        · show Nat.card (↥Y ⧸ H) = 2
          exact h2'
      let _ : CommGroup (↥Y ⧸ H) := IsCyclic.commGroup
      have hk := Abelianization.commutator_subset_ker (QuotientGroup.mk' H)
      rw [Group.isPerfect_def.mp hP] at hk
      rw [QuotientGroup.ker_mk'] at hk
      exact eq_top_iff.mpr hk
  intro y hy
  have : (⟨y, hy⟩ : ↥Y) ∈ H := by rw [htop]; exact Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp this

end Perfect

section Product

variable {G : Type*} [Group G]

theorem eq_and_eq_of_mul_eq_mul {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {a a' b b' : G}
    (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ A ⊓ B := ⟨A.mul_mem (A.inv_mem ha') ha, h1 ▸ B.mul_mem hb' (B.inv_mem hb)⟩
  rw [hAB, Subgroup.mem_bot] at h2
  have h3 : a = a' := (inv_mul_eq_one.mp h2).symm
  refine ⟨h3, ?_⟩
  subst h3
  exact mul_left_cancel h

end Product

section Nine

variable {X Y : Type} [Group X] [Group Y]

theorem isElemAbelian_map_hom (p : ℕ) (f : X →* Y) {A : Subgroup X} (hA : IsElemAbelian p A) :
    IsElemAbelian p (A.map f) := CFSG.Open.IsElemAbelian.map hA _

theorem card_map_of_trivial_ker (f : X →* Y) (A : Subgroup X)
    (h : ∀ a ∈ A, f a = 1 → a = 1) : Nat.card (A.map f) = Nat.card A := by
  have hinj : Function.Injective
      (fun a : A => (⟨f a, Subgroup.mem_map_of_mem f a.2⟩ : A.map f)) := by
    intro a b hab
    apply Subtype.ext
    have h1 : f a = f b := congrArg Subtype.val hab
    have h2 : f ((a : X)⁻¹ * b) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
    exact inv_mul_eq_one.mp (h _ (A.mul_mem (A.inv_mem a.2) b.2) h2)
  have hsurj : Function.Surjective
      (fun a : A => (⟨f a, Subgroup.mem_map_of_mem f a.2⟩ : A.map f)) := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm

@[expose] def HasElemAb (p n : ℕ) (Y : Type) [Group Y] : Prop :=
  ∃ A : Subgroup Y, IsElemAbelian p A ∧ Nat.card A = n

theorem HasElemAb.of_mulEquiv {p n : ℕ} (e : X ≃* Y) (h : HasElemAb p n X) : HasElemAb p n Y := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A.map e.toMonoidHom, isElemAbelian_map_hom p e.toMonoidHom hA, by
    rw [Subgroup.card_map_of_injective e.injective]; exact hc⟩

theorem HasElemAb.of_subgroup {p n : ℕ} {G : Type} [Group G] {K A : Subgroup G} (hAK : A ≤ K)
    (hA : IsElemAbelian p A) (hc : Nat.card A = n) : HasElemAb p n ↥K := by
  refine ⟨A.subgroupOf K, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨hcomm, -⟩ := hA
    apply Subtype.ext; apply Subtype.ext
    exact setLike_mul_comm (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)
  · apply Subtype.ext
    exact hA.2 (x : G) hx
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]
    exact hc

theorem HasElemAb.exists_subgroup {p n : ℕ} {G : Type} [Group G] {K : Subgroup G}
    (h : HasElemAb p n ↥K) : ∃ A : Subgroup G, A ≤ K ∧ IsElemAbelian p A ∧ Nat.card A = n := by
  obtain ⟨A, hA, hc⟩ := h
  refine ⟨A.map K.subtype, Subgroup.map_subtype_le A, isElemAbelian_map_hom p K.subtype hA, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective]
  exact hc

theorem HasElemAb.quotient_two {n : ℕ} (N : Subgroup X) [N.Normal] (hN : IsPGroup 2 N)
    (h : HasElemAb 3 n X) : HasElemAb 3 n (X ⧸ N) := by
  obtain ⟨A, hA, hc⟩ := h
  refine ⟨A.map (QuotientGroup.mk' N), isElemAbelian_map_hom 3 _ hA, ?_⟩
  rw [card_map_of_trivial_ker _ A ?_]
  · exact hc
  · intro a ha hmk
    have haN : a ∈ N := by
      rw [← QuotientGroup.ker_mk' N]
      exact hmk
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hN ⟨a, haN⟩
    have hk' : orderOf a = 2 ^ k := (Subgroup.orderOf_coe (⟨a, haN⟩ : N)).trans hk
    have h3 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (hA.2 a ha)
    rw [hk'] at h3
    have : (2 ^ k).Coprime 3 := Nat.Coprime.pow_left _ (by norm_num)
    have h1 : 2 ^ k = 1 := Nat.Coprime.eq_one_of_dvd this h3
    rw [h1] at hk'
    exact orderOf_eq_one_iff.mp hk'

end Nine

end CFSG.QuasithinUnique.Id2519
