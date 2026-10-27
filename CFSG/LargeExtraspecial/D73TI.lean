module

public import CFSG.LargeExtraspecial.DWTransQ
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.LargeExtraspecial.DW.D73

open Subgroup CFSG.GroupTheory.GLnTwoSplitting CFSG.CGT.Timmesfeld75
open scoped IsMulCommutative

theorem MaxEA.transitive_of_surjective {G : Type*} [Group G] [Finite G] {S : Setting G}
    {A : Subgroup G} [IsElementaryAbelian 2 A] (hA : MaxEA S A)
    (hsurj : Function.Surjective (CFSG.GroupTheory.GLnTwoSplitting.conjLinear (AN A))) :
    ∀ t ∈ A, t ≠ 1 → ∃ n ∈ normalizer (A : Set G), n * S.z * n⁻¹ = t := by
  intro t ht ht1
  have hz0 : hA.zVec ≠ 0 := fun h => S.z_ne_one (congrArg elt h)
  have ht0 : (vec ht : Additive (AN A)) ≠ 0 := fun h => ht1 (congrArg elt h)
  obtain ⟨f, d, hfd, hτ⟩ := exists_transvection_apply_eq hz0 ht0
  obtain ⟨n, hn⟩ := hsurj (LinearEquiv.transvection hfd)
  refine ⟨n, n.2, ?_⟩
  have h := congrArg elt (LinearEquiv.congr_fun hn hA.zVec)
  rw [elt_conjLinear, hτ] at h
  exact h

private theorem mem_conjSubgroup_inv {G : Type*} [Group G] {T : Subgroup G} {g x : G} :
    x ∈ conjSubgroup g⁻¹ T ↔ g * x * g⁻¹ ∈ T := by
  rw [mem_conjSubgroup, inv_inv]

private theorem conjSubgroup_inv_eq_of_mem_normalizer {G : Type*} [Group G] {T : Subgroup G}
    {g : G} (hg : g ∈ normalizer (T : Set G)) : conjSubgroup g⁻¹ T = T := by
  ext x
  rw [mem_conjSubgroup_inv]
  exact ((mem_normalizer_iff.mp hg) x).symm

theorem isTI_of_transitive {G : Type*} [Group G] {T : Subgroup G} {z : G}
    (hM : centralizer ({z} : Set G) ≤ normalizer (T : Set G))
    (htr : ∀ t ∈ T, t ≠ 1 → ∃ n ∈ normalizer (T : Set G), n * z * n⁻¹ = t) :
    ∀ g : G, T ⊓ conjSubgroup g⁻¹ T = ⊥ ∨ T ⊓ conjSubgroup g⁻¹ T = T := by
  intro g
  rcases (T ⊓ conjSubgroup g⁻¹ T).bot_or_exists_ne_one with h | ⟨t, ht, ht1⟩
  · exact Or.inl h
  right
  obtain ⟨htT, htg⟩ := mem_inf.mp ht
  rw [mem_conjSubgroup_inv] at htg
  have hgt1 : g * t * g⁻¹ ≠ 1 := fun h => ht1 (by
    simpa [mul_assoc] using congrArg (fun u => g⁻¹ * u * g) h)
  obtain ⟨n, hn, hnt⟩ := htr t htT ht1
  obtain ⟨n', hn', hnt'⟩ := htr _ htg hgt1
  have hc : n'⁻¹ * g * n ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : g * (n * z * n⁻¹) * g⁻¹ = n' * z * n'⁻¹ := by rw [hnt, hnt']
    calc n'⁻¹ * g * n * z = n'⁻¹ * (g * (n * z * n⁻¹) * g⁻¹) * (g * n) := by group
      _ = n'⁻¹ * (n' * z * n'⁻¹) * (g * n) := by rw [h1]
      _ = z * (n'⁻¹ * g * n) := by group
  have hg : g ∈ normalizer (T : Set G) := by
    have h2 : g = n' * (n'⁻¹ * g * n) * n⁻¹ := by group
    rw [h2]
    exact mul_mem (mul_mem hn' (hM hc)) (inv_mem hn)
  rw [conjSubgroup_inv_eq_of_mem_normalizer hg, inf_idem]

private theorem card_conjSubgroup {G : Type*} [Group G] (g : G) (T : Subgroup G) :
    Nat.card (conjSubgroup g T) = Nat.card T :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem conjSubgroup_inv_eq_of_conj_mem {G : Type*} [Group G] [Finite G]
    {T : Subgroup G}
    (hti : ∀ g : G, T ⊓ conjSubgroup g⁻¹ T = ⊥ ∨ T ⊓ conjSubgroup g⁻¹ T = T) {s h : G}
    (hs : s ∈ T) (hs1 : s ≠ 1) (hhs : h * s * h⁻¹ ∈ T) : conjSubgroup h⁻¹ T = T := by
  have hmem : s ∈ T ⊓ conjSubgroup h⁻¹ T := mem_inf.mpr ⟨hs, mem_conjSubgroup_inv.mpr hhs⟩
  rcases hti h with h0 | h0
  · rw [h0, mem_bot] at hmem
    exact absurd hmem hs1
  · exact (Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp h0)
      (card_conjSubgroup h⁻¹ T).le).symm

private theorem inv_eq_self_of_mem {G : Type*} [Group G] {T : Subgroup G}
    [IsElementaryAbelian 2 T] {u : G} (hu : u ∈ T) : u⁻¹ = u :=
  inv_eq_of_mul_eq_one_right (DW.MaxEA.mul_self_of_mem hu)

theorem weaklyClosed_of_isTI {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    [IsElementaryAbelian 2 T] (hC : centralizer (T : Set G) = T)
    (hti : ∀ g : G, T ⊓ conjSubgroup g⁻¹ T = ⊥ ∨ T ⊓ conjSubgroup g⁻¹ T = T) :
    ∀ g : G, conjSubgroup g⁻¹ T ≤ normalizer (T : Set G) → conjSubgroup g⁻¹ T = T := by
  intro g hXN
  have hcard := card_conjSubgroup g⁻¹ T
  rcases hti g with hTX | hTX
  swap
  · exact (Subgroup.eq_of_le_of_card_ge (inf_eq_left.mp hTX) hcard.le).symm
  by_contra hne
  have hcommT : ∀ t ∈ T, ∀ y ∈ conjSubgroup g⁻¹ T, t * y * t⁻¹ * y⁻¹ ∈ T := by
    intro t ht y hy
    have h1 : y * t⁻¹ * y⁻¹ ∈ T := (mem_normalizer_iff.mp (hXN hy) t⁻¹).mp (inv_mem ht)
    have h2 : t * y * t⁻¹ * y⁻¹ = t * (y * t⁻¹ * y⁻¹) := by group
    rw [h2]
    exact mul_mem ht h1
  have ha : ∀ t ∈ T, ∀ x ∈ conjSubgroup g⁻¹ T, x ≠ 1 → t * x = x * t →
      ∀ y ∈ conjSubgroup g⁻¹ T, t * y = y * t := by
    intro t ht x hx hx1 htx y hy
    have hs := mem_conjSubgroup_inv.mp hx
    have hs1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (by
      simpa [mul_assoc] using congrArg (fun u => g⁻¹ * u * g) h)
    have hhs : (g * t * g⁻¹) * (g * x * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * x * g⁻¹ := by
      calc (g * t * g⁻¹) * (g * x * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * x) * t⁻¹ * g⁻¹ := by
            group
        _ = g * x * g⁻¹ := by rw [htx]; group
    have hN := conjSubgroup_inv_eq_of_conj_mem hti hs hs1 (hhs.symm ▸ hs)
    have hty : t * y * t⁻¹ ∈ conjSubgroup g⁻¹ T := by
      rw [mem_conjSubgroup_inv]
      have h1 : g * y * g⁻¹ ∈ conjSubgroup (g * t * g⁻¹)⁻¹ T := by
        rw [hN]
        exact mem_conjSubgroup_inv.mp hy
      rw [mem_conjSubgroup_inv] at h1
      have h2 : g * (t * y * t⁻¹) * g⁻¹ =
          g * t * g⁻¹ * (g * y * g⁻¹) * (g * t * g⁻¹)⁻¹ := by group
      rw [h2]
      exact h1
    have hc : t * y * t⁻¹ * y⁻¹ ∈ T ⊓ conjSubgroup g⁻¹ T :=
      mem_inf.mpr ⟨hcommT t ht y hy, mul_mem hty (inv_mem hy)⟩
    rw [hTX, mem_bot] at hc
    calc t * y = t * y * t⁻¹ * y⁻¹ * (y * t) := by group
      _ = y * t := by rw [hc, one_mul]
  obtain ⟨t, htT, y₀, hy₀, hty₀⟩ : ∃ t ∈ T, ∃ y ∈ conjSubgroup g⁻¹ T, t * y ≠ y * t := by
    by_contra hall
    push Not at hall
    apply hne
    have hle : conjSubgroup g⁻¹ T ≤ T := by
      intro y hy
      rw [← hC]
      exact mem_centralizer_iff.mpr fun t ht => hall t ht y hy
    have hbot : conjSubgroup g⁻¹ T = ⊥ := by
      rw [eq_bot_iff, ← hTX]
      exact le_inf hle le_rfl
    have hT1 : Nat.card T = 1 := by rw [← hcard, hbot, card_bot]
    rw [hbot, Subgroup.card_eq_one.mp hT1]
  set X := conjSubgroup g⁻¹ T
  have hlt : T ⊓ centralizer (X : Set G) < T := by
    refine lt_of_le_of_ne inf_le_left fun h => hty₀ ?_
    have h1 : t ∈ T ⊓ centralizer (X : Set G) := h.symm ▸ htT
    exact ((mem_centralizer_iff.mp (mem_inf.mp h1).2) y₀ hy₀).symm
  have hmem : ∀ x : X, t * x * t⁻¹ * (x : G)⁻¹ ∈ T ⊓ centralizer (X : Set G) := by
    intro ⟨x, hx⟩
    refine mem_inf.mpr ⟨hcommT t htT x hx, mem_centralizer_iff.mpr fun y hy => ?_⟩
    by_cases hx1 : x = 1
    · subst hx1
      group
    have hxx : x * x = 1 := by
      have h1 := DW.MaxEA.mul_self_of_mem (mem_conjSubgroup_inv.mp hx)
      calc x * x = g⁻¹ * (g * x * g⁻¹ * (g * x * g⁻¹)) * g := by group
        _ = 1 := by rw [h1]; group
    have haT : x * t * x⁻¹ ∈ T := (mem_normalizer_iff.mp (hXN hx) t).mp htT
    set c := t * x * t⁻¹ * x⁻¹ with hc
    have e1 : x * c * x⁻¹ = (x * t * x⁻¹) * ((x * x) * t⁻¹ * (x * x)⁻¹) := by
      rw [hc]; group
    have e2 : c = t * (x * t * x⁻¹)⁻¹ := by rw [hc]; group
    rw [hxx, one_mul, inv_one, mul_one] at e1
    have hcx : x * c * x⁻¹ = c := by
      rw [e1, e2, inv_eq_self_of_mem htT, inv_eq_self_of_mem haT]
      exact (DW.MaxEA.comm_of_mem htT haT).symm
    have hcT : c ∈ T := hcommT t htT x hx
    have hcx' : c * x = x * c := by
      calc c * x = x * c * x⁻¹ * x := by rw [hcx]
        _ = x * c := by group
    exact (ha c hcT x hx hx1 hcx' y hy).symm
  let φ : X → ↥(T ⊓ centralizer (X : Set G)) := fun x => ⟨_, hmem x⟩
  have hinj : Function.Injective φ := by
    intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have h1 : t * x * t⁻¹ * x⁻¹ = t * y * t⁻¹ * y⁻¹ := congrArg Subtype.val hxy
    have h5 : y * t * y⁻¹ = x * t * x⁻¹ := by
      calc y * t * y⁻¹ = (t * y * t⁻¹ * y⁻¹)⁻¹ * t := by group
        _ = (t * x * t⁻¹ * x⁻¹)⁻¹ * t := by rw [h1]
        _ = x * t * x⁻¹ := by group
    have h3 : t * (y⁻¹ * x) = y⁻¹ * x * t := by
      calc t * (y⁻¹ * x) = y⁻¹ * (y * t * y⁻¹) * x := by group
        _ = y⁻¹ * (x * t * x⁻¹) * x := by rw [h5]
        _ = y⁻¹ * x * t := by group
    have hw : y⁻¹ * x ∈ X := mul_mem (inv_mem hy) hx
    by_cases hw1 : y⁻¹ * x = 1
    · exact Subtype.ext (inv_mul_eq_one.mp hw1).symm
    · exact absurd (ha t htT _ hw hw1 h3 y₀ hy₀) hty₀
  have h1 := Nat.card_le_card_of_injective φ hinj
  have h2 := Subgroup.card_lt_of_lt hlt
  rw [hcard] at h1
  omega

end CFSG.LargeExtraspecial.DW.D73
