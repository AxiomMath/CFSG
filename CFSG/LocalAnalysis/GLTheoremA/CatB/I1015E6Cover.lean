module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015U6
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I1015FourU6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open
open CFSG.RankThree.PerfectCover (hopfMultiplier)
open CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier (exists_hom_of_cover)

namespace I1015

section Assembly

variable {U Q : Type} [Group U] [Finite U] [Group Q] [Finite Q]

theorem te6_assembly (hU : Group.IsPerfect U) (hQ : Group.IsPerfect Q)
    (hZ : IsPGroup 3 (Subgroup.center Q)) (e : Q ⧸ Subgroup.center Q ≃* U ⧸ Subgroup.center U)
    [Finite (hopfMultiplier (U ⧸ Subgroup.center U))]
    (hord : Nat.card (hopfMultiplier (U ⧸ Subgroup.center U)) ∣ 24) {Y : Subgroup U} {u z : U}
    (hY : IsElemAbelian 3 Y) (hYc : 3 ^ 4 ≤ Nat.card Y) (hu2 : u * u = 1)
    (hu : u ∉ Subgroup.center U) (hYu : ∀ y ∈ Y, y * u = u * y) (hz : z ∈ Subgroup.center U)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hzY : z ∉ Y) :
    ∃ Eb Wb : Subgroup Q, IsElemAbelian 3 Eb ∧
      Nat.card Eb = 3 ^ 4 * Nat.card (Subgroup.center Q) ∧ IsPGroup 2 Wb ∧ Wb ≠ ⊥ ∧
      Eb ≤ Subgroup.normalizer (Wb : Set Q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := U ⧸ Subgroup.center U with hX
  let β₀ : U →* X := QuotientGroup.mk' (Subgroup.center U)
  have hβ₀s : Function.Surjective β₀ := QuotientGroup.mk'_surjective _
  have hβ₀k : β₀.ker = Subgroup.center U := QuotientGroup.ker_mk' _
  obtain ⟨Q₂, hQ₂n, β₁, hQ₂3, hQ₂k, hβ₁mk, hβ₁s, hβ₁c, hβ₁p, hU₁perf⟩ :=
    exists_three_quotient hU β₀ hβ₀s hβ₀k
  set π₁ : U →* U ⧸ Q₂ := QuotientGroup.mk' Q₂ with hπ₁
  have hπ₁k : π₁.ker = Q₂ := QuotientGroup.ker_mk' Q₂
  have hπ₁β : ∀ g, β₁ (π₁ g) = β₀ g := hβ₁mk
  have hdvd : Nat.card β₁.ker ∣ 3 :=
    card_dvd_three_of_dvd hβ₁p hord (CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hU₁perf β₁ hβ₁s hβ₁c)
  have hz1' : π₁ z ≠ 1 := by
    intro h
    have hzQ : z ∈ Q₂ := by rw [← hπ₁k]; exact h
    have h3 : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have : orderOf z ∣ Nat.card Q₂ := by
      have := orderOf_dvd_natCard (⟨z, hzQ⟩ : Q₂)
      rwa [Subgroup.orderOf_mk] at this
    rw [h3] at this
    exact hQ₂3 this
  have hzb : π₁ z ∈ β₁.ker := by
    rw [MonoidHom.mem_ker, hπ₁β, ← MonoidHom.mem_ker, hβ₀k]
    exact hz
  have hzb3 : π₁ z ^ 3 = 1 := by rw [← map_pow, hz3, map_one]
  have hker3 : Nat.card β₁.ker = 3 := by
    refine Nat.dvd_antisymm hdvd ?_
    have h1 : orderOf (π₁ z) = 3 := orderOf_eq_prime hzb3 hz1'
    have := orderOf_dvd_natCard (⟨π₁ z, hzb⟩ : β₁.ker)
    rwa [Subgroup.orderOf_mk, h1] at this
  have hkerz : β₁.ker = Subgroup.zpowers (π₁ z) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzb) ?_
    rw [hker3, Nat.card_zpowers, orderOf_eq_prime hzb3 hz1']
  let γ : Q →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hγk : γ.ker = Subgroup.center Q := by
    rw [MonoidHom.ker_comp_of_injective _ e.toMonoidHom e.injective]
    exact QuotientGroup.ker_mk' _
  have hγs : Function.Surjective γ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hM : (Nat.card (hopfMultiplier X)).factorization 3 ≤ (Nat.card β₁.ker).factorization 3 := by
    rw [hker3, Nat.Prime.factorization_self Nat.prime_three]
    by_contra hlt
    push Not at hlt
    have h9 : 3 ^ 2 ∣ Nat.card (hopfMultiplier X) :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').2 hlt
    have := h9.trans hord
    omega
  obtain ⟨φ, hφs, hγφ⟩ := exists_hom_of_cover hU₁perf hQ β₁ hβ₁s hβ₁c γ hγs hγk.le Nat.prime_three
    (by rw [hγk]; exact hZ) hM
  obtain ⟨Eb₀, hEb₀Y, hEb₀e, hEb₀c⟩ := exists_sub_card_pow hY (k := 4) (by
    obtain ⟨n, hn⟩ := hY.isPGroup.exists_card_eq
    rw [hn] at hYc ⊢
    exact pow_dvd_pow 3 ((Nat.pow_le_pow_iff_right (by norm_num)).1 hYc))
  have hinj : Function.Injective (π₁.comp Eb₀.subtype) :=
    injective_comp_subtype Nat.prime_three π₁ (by rw [hπ₁k]; exact hQ₂3) hEb₀e.isPGroup
  have hE'card : Nat.card (Eb₀.map π₁) = 3 ^ 4 := by
    rw [← card_eq_of_injective_comp_subtype π₁ hinj, hEb₀c]
  have hED : Eb₀.map π₁ ⊓ β₁.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, ha, rfl⟩, hxD⟩
    have hac : a ∈ Subgroup.center U := by
      rw [← hβ₀k, MonoidHom.mem_ker, ← hπ₁β]
      exact hxD
    rw [hkerz] at hxD
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hxD
    have hw : a⁻¹ * z ^ m ∈ Q₂ := by
      rw [← hπ₁k, MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hm, inv_mul_cancel]
    have hw3 : (a⁻¹ * z ^ m) ^ 3 = 1 := by
      have hca0 : Commute a⁻¹ z := Subgroup.mem_center_iff.1 hz a⁻¹
      have hca : Commute a⁻¹ (z ^ m) := hca0.zpow_right m
      rw [hca.mul_pow, inv_pow, hEb₀e.2 a ha, inv_one, one_mul, ← zpow_natCast, ← zpow_mul,
        mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
    have hw1 : a⁻¹ * z ^ m = 1 := by
      by_contra hne
      have hq : orderOf (a⁻¹ * z ^ m) = 3 := orderOf_eq_prime hw3 hne
      have : orderOf (a⁻¹ * z ^ m) ∣ Nat.card Q₂ := by
        have := orderOf_dvd_natCard (⟨a⁻¹ * z ^ m, hw⟩ : Q₂)
        rwa [Subgroup.orderOf_mk] at this
      rw [hq] at this
      exact hQ₂3 this
    have haz : a = z ^ m := inv_mul_eq_one.1 hw1
    have h3m : (3 : ℤ) ∣ m := by
      by_contra h3m
      apply hzY
      have hzm : z = (z ^ m) ^ m := by
        have h3' : (3 : ℤ) ∣ m * m - 1 := by
          have : (3 : ℤ) ∣ m - 1 ∨ (3 : ℤ) ∣ m + 1 := by omega
          rcases this with h1 | h1
          · exact (h1.mul_right (m + 1)).trans (by rw [show (m - 1) * (m + 1) = m * m - 1 by ring])
          · exact (h1.mul_left (m - 1)).trans (by rw [show (m - 1) * (m + 1) = m * m - 1 by ring])
        obtain ⟨c, hc⟩ := h3'
        rw [← zpow_mul, show m * m = 1 + 3 * c by omega, zpow_add, zpow_one, zpow_mul,
          show ((3 : ℤ)) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hz3, one_zpow, mul_one]
      rw [hzm, ← haz]
      exact Subgroup.zpow_mem _ (hEb₀Y ha) m
    rw [haz, (by obtain ⟨c, hc⟩ := h3m; rw [hc, zpow_mul, zpow_ofNat, hz3, one_zpow] : z ^ m = 1), map_one]
    exact Subgroup.one_mem _
  have hDe : IsElemAbelian 3 β₁.ker := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · exact (Subgroup.mem_center_iff.1 (hβ₁c a.2) b).symm
    · have := pow_card_eq_one' (G := β₁.ker) (x := ⟨x, hx⟩)
      rw [hker3] at this
      exact congrArg Subtype.val this
  have hE : IsElemAbelian 3 (Eb₀.map π₁ ⊔ β₁.ker) :=
    (hEb₀e.map π₁).sup_of_commute hDe (fun a _ b hb => (Subgroup.mem_center_iff.1 (hβ₁c hb) a))
  have hs2 : π₁ u * π₁ u = 1 := by rw [← map_mul, hu2, map_one]
  have hsD : π₁ u ∉ β₁.ker := by
    intro h
    apply hu
    rw [← hβ₀k, MonoidHom.mem_ker, ← hπ₁β]
    exact h
  have hsc : ∀ x ∈ Eb₀.map π₁ ⊔ β₁.ker, x * π₁ u = π₁ u * x := by
    intro x hx
    have hle : Eb₀.map π₁ ⊔ β₁.ker ≤ Subgroup.centralizer ({π₁ u} : Set (U ⧸ Q₂)) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · obtain ⟨a, ha, rfl⟩ := hw
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hYu a (hEb₀Y ha)]
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.1 (hβ₁c hw) (π₁ u)).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  obtain ⟨Eb, s, hEbe, hEbc, hs2', hγs1, hEbs⟩ :=
    cover_assembly β₁ γ φ hφs hγφ rfl hE'card hED hE hs2 hsD hsc
  have hs1 : s ≠ 1 := fun h => hγs1 (by rw [h, map_one])
  refine ⟨Eb, Subgroup.zpowers s, hEbe, by rw [hEbc, hγk], isPGroup_zpowers_of_pow_eq_one hs2',
    by rwa [Ne, Subgroup.zpowers_eq_bot], fun x hx => mem_normalizer_zpowers_of_commute (hEbs x hx)⟩

end Assembly

end I1015

end CFSG.LocalAnalysis.GLTheoremA.CatB
