module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAltCorePerm
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCoreInner
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitAut5Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.FooteLit.AltCore

open CFSG Subgroup Equiv Equiv.Perm

theorem commute_of_mem_oddCore {α : Type*} [DecidableEq α] [Finite α] {π : Perm α}
    (hπ : π * π = 1) :
    ∀ x y : ↥(pPrimeCore 2 ↥(centralizer ({π} : Set (Perm α)))), x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({π} : Set (Perm α)) with hC
  set O : Subgroup (Perm α) := (pPrimeCore 2 ↥C).map C.subtype with hOdef
  have hO : ∀ x ∈ O, x * π = π * x := by
    rintro _ ⟨u, -, rfl⟩
    exact mem_centralizer_singleton_iff.mp u.2
  have hodd : ∀ x ∈ O, Odd (orderOf x) := by
    rintro _ ⟨u, hu, rfl⟩
    have h1 : orderOf (C.subtype u) = orderOf (⟨u, hu⟩ : ↥(pPrimeCore 2 ↥C)) := by
      rw [Subgroup.orderOf_mk, coe_subtype, Subgroup.orderOf_coe]
    rw [h1]
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) (orderOf_dvd_natCard _)
  have hnorm : ∀ g : Perm α, g * π = π * g → ∀ x ∈ O, g * x * g⁻¹ ∈ O := by
    rintro g hg _ ⟨u, hu, rfl⟩
    have hgC : g ∈ C := mem_centralizer_singleton_iff.mpr hg
    exact ⟨⟨g, hgC⟩ * u * ⟨g, hgC⟩⁻¹,
      (pPrimeCore_normal (p := 2) (G := ↥C)).conj_mem u hu _, rfl⟩
  intro x y
  have key := commute_of_mem hπ hO hodd hnorm (x := ((x : C) : Perm α))
    (y := ((y : C) : Perm α)) ⟨x, x.2, rfl⟩ ⟨y, y.2, rfl⟩
  exact Subtype.ext (Subtype.ext key)

variable {S : Type} [Group S] {n : ℕ}

@[expose] noncomputable def autPermN (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : S ≃* alternatingGroup (Fin n)) : MulAut S ≃* Perm (Fin n) :=
  (MulAut.congr e).trans (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6)).symm

theorem commute_of_mem_oddCore_mulAut (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : S ≃* alternatingGroup (Fin n)) (i : MulAut S) (hi : i * i = 1) :
    ∀ x y : ↥(pPrimeCore 2 ↥(centralizer ({i} : Set (MulAut S)))), x * y = y * x := by
  set Φ := autPermN hn hn6 e with hΦ
  have hCC : (centralizer ({i} : Set (MulAut S))).map Φ.toMonoidHom =
      centralizer ({Φ i} : Set (Perm (Fin n))) := by
    ext g
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := congrArg Φ h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    · intro h
      apply Φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h
  let f : ↥(centralizer ({i} : Set (MulAut S))) ≃* ↥(centralizer ({Φ i} : Set (Perm (Fin n)))) :=
    (Φ.subgroupMap _).trans (MulEquiv.subgroupCongr hCC)
  have hmap := pPrimeCore_map_iso 2 f
  have hπ : Φ i * Φ i = 1 := by rw [← map_mul, hi, map_one]
  intro x y
  have hmem : ∀ u : ↥(pPrimeCore 2 ↥(centralizer ({i} : Set (MulAut S)))),
      f ↑u ∈ pPrimeCore 2 ↥(centralizer ({Φ i} : Set (Perm (Fin n)))) := fun u => by
    rw [← hmap]
    exact ⟨u, u.2, rfl⟩
  have key := commute_of_mem_oddCore hπ ⟨f x, hmem x⟩ ⟨f y, hmem y⟩
  have h1 : f (↑x * ↑y) = f (↑y * ↑x) := by
    rw [map_mul, map_mul]
    exact congrArg Subtype.val key
  exact Subtype.ext (f.injective h1)

theorem sign_eq_one_of_odd {α : Type*} [DecidableEq α] [Fintype α] {σ : Perm α}
    (h : Odd (orderOf σ)) : Perm.sign σ = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : Perm.sign σ ^ (2 * k + 1) = 1 := by
    rw [← map_pow, ← hk, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, pow_succ, pow_mul] at h1
    simp at h1

theorem oddOuterInner_alternating (hn : 5 ≤ n) (hn6 : n ≠ 6)
    (e : S ≃* alternatingGroup (Fin n)) : OddOuterInner S := by
  intro σ hσ
  set Φ := autPermN hn hn6 e with hΦ
  have hsign : Perm.sign (Φ σ) = 1 := sign_eq_one_of_odd (by rwa [MulEquiv.orderOf_eq])
  have hmem : Φ σ ∈ alternatingGroup (Fin n) := Perm.mem_alternatingGroup.mpr hsign
  refine ⟨e.symm ⟨Φ σ, hmem⟩, ?_⟩
  apply (MulAut.congr e).injective
  rw [Aut5.congr_conj, MulEquiv.apply_symm_apply]
  ext y
  have h1 : MulAut.congr e σ = MulAut.conjNormal (H := alternatingGroup (Fin n)) (Φ σ) := by
    rw [hΦ, autPermN]
    simp only [MulEquiv.trans_apply]
    rw [← MulEquiv.ofBijective_apply _
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6),
      MulEquiv.apply_symm_apply]
  rw [h1, MulAut.conjNormal_apply, MulAut.conj_apply]
  rfl

theorem five_le_of_simple [Finite S] [IsSimpleGroup S] (hna : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* alternatingGroup (Fin n)) : 5 ≤ n := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, b, hab⟩ := hna
  rcases (show n ≤ 3 ∨ n = 4 by omega) with h3 | rfl
  · have : IsMulCommutative (alternatingGroup (Fin n)) :=
      alternatingGroup.isMulCommutative_iff_card_le_three.mpr (by simpa using h3)
    apply hab
    apply e.injective
    rw [map_mul, map_mul]
    exact this.is_comm.comm (e a) (e b)
  · have h4 : Nat.card (Fin 4) = 4 := by simp
    have hnK := alternatingGroup.normal_kleinFour h4
    have hcK := alternatingGroup.kleinFour_card_of_card_eq_four h4
    set N := (alternatingGroup.kleinFour (Fin 4)).comap e.toMonoidHom with hN
    have hNn : N.Normal := hnK.comap _
    have hcN : Nat.card N = 4 := by
      have h1 : N.map e.toMonoidHom = alternatingGroup.kleinFour (Fin 4) :=
        map_comap_eq_self_of_surjective e.surjective _
      rw [← hcK, ← h1, card_map_of_injective (f := e.toMonoidHom) e.injective]
    have hcS : Nat.card S = 12 := by
      have h := two_mul_nat_card_alternatingGroup (α := Fin 4)
      rw [Nat.card_perm, h4, show Nat.factorial 4 = 24 by decide] at h
      rw [Nat.card_congr e.toEquiv]
      omega
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · rw [h, card_bot] at hcN
      omega
    · rw [h, card_top, hcS] at hcN
      omega

end CFSG.ComponentClassification.FooteLit.AltCore
