module

public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Sylow
public import CFSG.Sporadic.HN.Local.ClassCount

public section

namespace CFSG.OddStandard.Seitz77.L34

open Subgroup CFSG.ComponentClassification

@[expose] def r₁S : PSL3Four.S := ⟨PSL3Four.r₁, PSL3Four.r₁_mem_S⟩

theorem card_isConj_r₁_S :
    Nat.card {s : PSL3Four.S // IsConj r₁S s} = 315 := by
  have h1 := CFSG.Sporadic.HN.Local.card_conj_mul_card_centralizer r₁S
  have hcent : Nat.card (centralizer ({r₁S} : Set PSL3Four.S)) = 64 := by
    rw [← PSL3Four.card_C₁]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨(x : PSL3Four.S).1, ?_, ?_⟩) ⟨?_, ?_⟩)
    · exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val
        (mem_centralizer_singleton_iff.1 x.2))
    · exact (x : PSL3Four.S).2
    · intro x y h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨y, hy1, hy2⟩
      exact ⟨⟨⟨y, hy2⟩, mem_centralizer_singleton_iff.2 (Subtype.ext
        (mem_centralizer_singleton_iff.1 hy1))⟩, rfl⟩
  rw [hcent, PSL3Four.card_S] at h1
  omega

theorem isConj_r₁S_of_orderOf_eq_two {x : PSL3Four.S}
    (hx : orderOf x = 2) : IsConj r₁S x := by
  let z : PSL3Four.R := Subgroup.inclusion PSL3Four.S_le_R x
  have hz : orderOf z = 2 := by
    rw [orderOf_injective _ (Subgroup.inclusion_injective PSL3Four.S_le_R) x]
    exact hx
  have hzS : (z : Equiv.Perm (Fin 42)) ∈ PSL3Four.S := x.2
  have hzr : IsConj z PSL3Four.r₁R := by
    rcases (PSL3Four.orderOf_eq_two_iff z).1 hz with h | h | h | h
    · exact h
    · exact absurd hzS (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₂)
    · exact absurd hzS (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₃)
    · exact absurd hzS (PSL3Four.not_mem_S_of_isConj h PSL3Four.not_mem_S_r₄)
  let f : {s : PSL3Four.S // IsConj r₁S s} → {w : PSL3Four.R // IsConj PSL3Four.r₁R w} :=
    fun s => ⟨Subgroup.inclusion PSL3Four.S_le_R s.1, by
      obtain ⟨c, hc⟩ := isConj_iff.1 s.2
      refine isConj_iff.2 ⟨Subgroup.inclusion PSL3Four.S_le_R c, Subtype.ext ?_⟩
      have h' := congrArg Subtype.val hc
      exact h'⟩
  have hcardR : Nat.card {w : PSL3Four.R // IsConj PSL3Four.r₁R w} = 315 := by
    rw [← (PSL3Four.involution_enumeration.2.2.2.2.2.2.2.1)]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun w => by
      rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_comm])
  have hbij : Function.Bijective f := by
    refine Function.Injective.bijective_of_nat_card_le ?_ (by rw [hcardR, card_isConj_r₁_S])
    intro s s' h
    exact Subtype.ext (Subtype.ext (congrArg (fun w => w.1.1) h))
  obtain ⟨s, hs⟩ := hbij.2 ⟨z, isConj_comm.1 hzr⟩
  have hsx : s.1 = x := Subtype.ext (congrArg (fun w => w.1.1) hs)
  rw [← hsx]
  exact s.2

end CFSG.OddStandard.Seitz77.L34

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.ComponentClassification

variable {A : Type*} [Group A]

theorem involutions_conj (hZ : Odd (Nat.card (center A)))
    (e : A ⧸ center A ≃* PSL3Four.S) {x y : A} (hx : orderOf x = 2) (hy : orderOf y = 2) :
    ∃ a : A, a * x * a⁻¹ = y := by
  let q : A →* PSL3Four.S := e.toMonoidHom.comp (QuotientGroup.mk' (center A))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ∀ k, q k = 1 → k ∈ center A := fun k hk => by
    simpa [q, QuotientGroup.eq_one_iff] using hk
  have hkodd : ∀ k ∈ center A, Odd (orderOf k) := fun k hk => by
    have := orderOf_dvd_natCard (⟨k, hk⟩ : center A)
    rw [Subgroup.orderOf_mk] at this
    exact hZ.of_dvd_nat this
  have hord : ∀ z : A, orderOf z = 2 → orderOf (q z) = 2 := by
    intro z hz
    have hz2 : z ^ 2 = 1 := by
      rw [← hz]
      exact pow_orderOf_eq_one z
    refine orderOf_eq_prime (by rw [← map_pow, hz2, map_one]) fun h1 => ?_
    have := hkodd z (hker z h1)
    rw [hz] at this
    exact (Nat.not_even_iff_odd.2 this) even_two
  have hconj : IsConj (q x) (q y) :=
    (isConj_comm.1 (L34.isConj_r₁S_of_orderOf_eq_two (hord x hx))).trans
      (L34.isConj_r₁S_of_orderOf_eq_two (hord y hy))
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  obtain ⟨a, rfl⟩ := hq c
  have hk : q ((a * x * a⁻¹)⁻¹ * y) = 1 := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, hc, inv_mul_cancel]
  have hkc := hker _ hk
  have hxa : orderOf (a * x * a⁻¹) = 2 := by
    rw [← (SemiconjBy.conj_mk a x).orderOf_eq]
    exact hx
  have h1 := L34.eq_one_of_two_power_of_odd (y := y) (v := a * x * a⁻¹)
    (k := (a * x * a⁻¹)⁻¹ * y) (by group) ⟨1, by rw [hxa, pow_one]⟩ ⟨1, by rw [hy, pow_one]⟩
    (Subgroup.mem_center_iff.mp hkc _) (hkodd _ hkc)
  exact ⟨a, inv_mul_eq_one.1 h1⟩


theorem involutions_conj_of_mem {G : Type*} [Group G]
    {A : Subgroup G} (hZ : Odd (Nat.card (center ↥A))) (e : ↥A ⧸ center ↥A ≃* PSL3Four.S)
    {x y : G} (hx : x ∈ A) (hy : y ∈ A) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) :
    ∃ a ∈ A, a * x * a⁻¹ = y := by
  obtain ⟨a, ha⟩ := involutions_conj hZ e (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)
    (by rwa [Subgroup.orderOf_mk]) (by rwa [Subgroup.orderOf_mk])
  exact ⟨a, a.2, congrArg Subtype.val ha⟩

end CFSG.OddStandard.Seitz77
