module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Cm
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbT17Prod
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

private lemma mem_zpowers_eq_one_or_eq {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

theorem comm_zpowers_inv {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {g : G}
    (hg2 : g * g = 1) (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) :
    (∀ n : G, n ∈ ⁅A, zpowers g⁆ ↔ ∃ a ∈ A, n = a * g * a⁻¹ * g⁻¹) ∧
      Nat.card A = Nat.card ↥(⁅A, zpowers g⁆) * Nat.card ↥(A ⊓ centralizer ({g} : Set G)) := by
  obtain ⟨N, _hNA, hmemN, hsurjN, hcardN⟩ := exists_comm_image hA hgA
  have hEq : ⁅A, zpowers g⁆ = N := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha k hk
      rcases mem_zpowers_eq_one_or_eq hg2 hk with rfl | rfl
      · rw [commutatorElement_def]; simp
      · rw [commutatorElement_def]; exact hmemN a ha
    · intro n hn
      obtain ⟨a, ha, rfl⟩ := hsurjN n hn
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator ha (Subgroup.mem_zpowers g)
  constructor
  · intro n
    rw [hEq]
    exact ⟨fun hn => hsurjN n hn, fun ⟨a, ha, h⟩ => h ▸ hmemN a ha⟩
  · rw [hEq]; exact hcardN

theorem card_sup_mul_card_inf {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  let f : ↥H × ↥K →* ↥(H ⊔ K) :=
    { toFun := fun p => ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
      map_one' := by ext <;> simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        have hc : (p.2 : G) * (q.1 : G) = (q.1 : G) * (p.2 : G) :=
          (hHK q.1 q.1.2 p.2 p.2.2).symm
        change (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
            = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
            = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [hc]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group }
  have hnorm : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H := by
    intro k hk h hh
    rw [← hHK h hh k hk, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hf_top : f.range = ⊤ := by
    refine le_antisymm le_top ?_
    intro x _
    obtain ⟨h, hh, k, hk, hxk⟩ := (mem_sup_iff_of_normalizes hnorm).mp x.2
    exact MonoidHom.mem_range.mpr ⟨(⟨h, hh⟩, ⟨k, hk⟩), Subtype.ext hxk.symm⟩
  let g : ↥(H ⊓ K) →* ↥H × ↥K :=
    { toFun := fun d => (⟨(d : G), d.2.1⟩, ⟨(d : G)⁻¹, K.inv_mem d.2.2⟩)
      map_one' := by ext <;> simp
      map_mul' := by
        intro d d'
        have hcomm : (d : G) * (d' : G) = (d' : G) * (d : G) := hHK d d.2.1 d' d'.2.2
        have hinv : ((d : G) * (d' : G))⁻¹ = (d : G)⁻¹ * (d' : G)⁻¹ := by
          have h := congrArg Inv.inv hcomm
          simpa [mul_inv_rev] using h
        ext
        · rfl
        · simpa using hinv }
  have hg_inj : Function.Injective g := by
    intro d d' h
    have h1 : (d : G) = (d' : G) := by
      have := congrArg (fun z : ↥H × ↥K => ((z.1 : ↥H) : G)) h
      simpa [g] using this
    exact Subtype.ext h1
  have hrange : g.range = f.ker := by
    apply le_antisymm
    · rintro y ⟨d, rfl⟩
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      simp [f, g]
    · intro y hy
      rw [MonoidHom.mem_ker] at hy
      have hyv : ((y.1 : ↥H) : G) * ((y.2 : ↥K) : G) = 1 := by
        have := congrArg (fun z : ↥(H ⊔ K) => (z : G)) hy
        simpa [f] using this
      refine MonoidHom.mem_range.mpr ⟨⟨((y.1 : ↥H) : G), ⟨y.1.2, ?_⟩⟩, ?_⟩
      · rw [eq_inv_of_mul_eq_one_left hyv]; exact K.inv_mem y.2.2
      · apply Prod.ext
        · exact Subtype.ext rfl
        · exact Subtype.ext (eq_inv_of_mul_eq_one_right hyv).symm
  have hcard_range : Nat.card g.range = Nat.card ↥(H ⊓ K) := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hg_inj, Subgroup.card_top]
  have hker : Nat.card f.ker = Nat.card ↥(H ⊓ K) := by
    rw [← hrange, hcard_range]
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hker, hf_top, Subgroup.card_top, Nat.card_prod] at hcard
  rw [mul_comm (Nat.card ↥(H ⊓ K)) (Nat.card ↥(H ⊔ K))] at hcard
  exact hcard

theorem exists_mul_of_sup {H K : Subgroup G} (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k = k * h) {x : G}
    (hx : x ∈ H ⊔ K) : ∃ h ∈ H, ∃ k ∈ K, x = h * k := by
  have hK : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H := by
    intro k hk h hh
    rw [← hHK h hh k hk, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  exact (mem_sup_iff_of_normalizes (H := H) (K := K) hK).mp hx

theorem two_mul_card_le_of_lt {A B : Subgroup G} (h : A < B) :
    2 * Nat.card A ≤ Nat.card B := by
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le h.le
  have hlt : Nat.card A < Nat.card B := Subgroup.card_lt_of_lt h
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hk; omega
    · simp at hk; omega
    · omega
  rw [hk, mul_comm 2 (Nat.card A)]
  exact Nat.mul_le_mul_left _ hk2

theorem isElemAbelian_zpowers {a : G} (ha : a * a = 1) :
    CFSG.Open.IsElemAbelian 2 (zpowers a) := by
  refine ⟨inferInstance, ?_⟩
  intro x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, ha]
  calc (a ^ n) ^ (2 : ℕ)
      = (a ^ n) ^ (2 : ℤ) := (zpow_natCast (a ^ n) 2).symm
    _ = a ^ (n * 2) := (zpow_mul a n 2).symm
    _ = a ^ (2 * n) := by rw [mul_comm]
    _ = (a ^ (2 : ℤ)) ^ n := zpow_mul a 2 n
    _ = 1 := by rw [h2, one_zpow]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
