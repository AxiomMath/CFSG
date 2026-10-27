module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G]

private lemma mul_injective_of_inf_eq_bot {A B : Subgroup G} (hAB : A ⊓ B = ⊥) :
    Function.Injective (fun p : ↥A × ↥B => ((p.1 : G) * (p.2 : G))) := by
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ heq
  change a * b = a' * b' at heq
  have hmem : (a' : G)⁻¹ * a = b' * b⁻¹ := by
    calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * b⁻¹ := by group
      _ = (a' : G)⁻¹ * (a' * b') * b⁻¹ := by rw [heq]
      _ = b' * b⁻¹ := by group
  have hmemA : (a' : G)⁻¹ * a ∈ A := A.mul_mem (A.inv_mem ha') ha
  have hmemB : (a' : G)⁻¹ * a ∈ B := by rw [hmem]; exact B.mul_mem hb' (B.inv_mem hb)
  have hbot : (a' : G)⁻¹ * a ∈ (⊥ : Subgroup G) := by
    rw [← hAB]; exact ⟨hmemA, hmemB⟩
  have h1 : a = a' := (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hbot)).symm
  have h2 : b = b' := by
    rw [h1] at heq
    exact mul_left_cancel heq
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

theorem mem_sup_iff_of_normalizes {H K : Subgroup G} (hK : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    {x : G} : x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  let T : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ k ∈ K, x = h * k}
      mul_mem' := by
        rintro x y ⟨h, hh, k, hk, rfl⟩ ⟨h', hh', k', hk', rfl⟩
        exact ⟨h * (k * h' * k⁻¹), H.mul_mem hh (hK k hk h' hh'),
          k * k', K.mul_mem hk hk', by group⟩
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by group⟩
      inv_mem' := by
        rintro x ⟨h, hh, k, hk, rfl⟩
        exact ⟨k⁻¹ * h⁻¹ * k, by simpa using hK k⁻¹ (K.inv_mem hk) h⁻¹ (H.inv_mem hh),
          k⁻¹, K.inv_mem hk, by group⟩ }
  constructor
  · intro hx
    have hHT : H ≤ T := fun x hx => ⟨x, hx, 1, K.one_mem, by group⟩
    have hKT : K ≤ T := fun x hx => ⟨1, H.one_mem, x, hx, by group⟩
    exact sup_le hHT hKT hx
  · rintro ⟨h, hh, k, hk, rfl⟩
    exact Subgroup.mul_mem_sup hh hk

theorem card_sup_eq_mul [Finite G] {H K : Subgroup G}
    (hK : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hHK : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  let f : ↥H × ↥K → ↥(H ⊔ K) :=
    fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective f := by
    intro p q hp
    exact mul_injective_of_inf_eq_bot (A := H) (B := K) hHK (congrArg Subtype.val hp)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨h, hh, k, hk, hx⟩ := (mem_sup_iff_of_normalizes hK).mp x.2
    exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hx.symm⟩
  have hcongr := Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Nat.card_prod] at hcongr
  exact hcongr.symm

theorem exists_mul_of_card_eq [Finite G] {A B C : Subgroup G} (hA : A ≤ C) (hB : B ≤ C)
    (hAB : A ⊓ B = ⊥) (hcard : Nat.card A * Nat.card B = Nat.card C) :
    ∀ x ∈ C, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let g : ↥A × ↥B → ↥C :=
    fun p => ⟨(p.1 : G) * (p.2 : G), C.mul_mem (hA p.1.2) (hB p.2.2)⟩
  have hinj : Function.Injective g := by
    intro p q hp
    exact mul_injective_of_inf_eq_bot (A := A) (B := B) hAB (congrArg Subtype.val hp)
  have hle : Nat.card ↥C ≤ Nat.card (↥A × ↥B) := by
    rw [Nat.card_prod]; exact hcard.ge
  have hsurj : Function.Surjective g := (hinj.bijective_of_nat_card_le hle).2
  intro x hx
  obtain ⟨p, hp⟩ := hsurj ⟨x, hx⟩
  exact ⟨p.1, p.1.2, p.2, p.2.2, (congrArg Subtype.val hp).symm⟩

theorem isElemAbelian_sup {H K : Subgroup G} (hH : CFSG.Open.IsElemAbelian 2 H)
    (hK : CFSG.Open.IsElemAbelian 2 K) (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    CFSG.Open.IsElemAbelian 2 (H ⊔ K) := by
  have hnorm : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H := by
    intro k hk h hh
    rw [← hHK h hh k hk, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hmem : ∀ x : G, x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, x = h * k :=
    fun x => mem_sup_iff_of_normalizes (H := H) (K := K) hnorm
  have hcommH : ∀ h h' : G, h ∈ H → h' ∈ H → h * h' = h' * h := by
    intro h h' hh hh'
    haveI : IsMulCommutative ↥H := hH.1
    have key := mul_comm' (⟨h, hh⟩ : ↥H) (⟨h', hh'⟩ : ↥H)
    simpa using congrArg Subtype.val key
  have hcommK : ∀ k k' : G, k ∈ K → k' ∈ K → k * k' = k' * k := by
    intro k k' hk hk'
    haveI : IsMulCommutative ↥K := hK.1
    have key := mul_comm' (⟨k, hk⟩ : ↥K) (⟨k', hk'⟩ : ↥K)
    simpa using congrArg Subtype.val key
  refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
  · intro x y
    apply Subtype.ext
    show (x : G) * (y : G) = (y : G) * (x : G)
    obtain ⟨h, hh, k, hk, hx⟩ := (hmem _).mp x.2
    obtain ⟨h', hh', k', hk', hy⟩ := (hmem _).mp y.2
    rw [hx, hy]
    have hkh' : k * h' = h' * k := (hHK h' hh' k hk).symm
    have hk'h : k' * h = h * k' := (hHK h hh k' hk').symm
    have hA : (h * k) * (h' * k') = h' * h * (k' * k) := by
      calc (h * k) * (h' * k') = h * (k * h') * k' := by group
        _ = h * (h' * k) * k' := by rw [hkh']
        _ = h * h' * (k * k') := by group
        _ = h' * h * (k' * k) := by rw [hcommH h h' hh hh', hcommK k k' hk hk']
    have hB : (h' * k') * (h * k) = h' * h * (k' * k) := by
      calc (h' * k') * (h * k) = h' * (k' * h) * k := by group
        _ = h' * (h * k') * k := by rw [hk'h]
        _ = h' * h * (k' * k) := by group
    exact hA.trans hB.symm
  · intro x hx
    obtain ⟨h, hh, k, hk, hx⟩ := (hmem x).mp hx
    rw [hx]
    have h2 : h * h = 1 := by simpa [pow_two] using hH.2 h hh
    have k2 : k * k = 1 := by simpa [pow_two] using hK.2 k hk
    have hkh : k * h = h * k := (hHK h hh k hk).symm
    calc (h * k) ^ 2 = h * (k * h * k⁻¹) * (k * k) := by rw [pow_two]; group
      _ = h * h * (k * k) := by rw [hkh]; group
      _ = 1 := by rw [h2, k2, one_mul]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
