
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporLift

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem goodLocal_of_simple_quotient {X : Type*} [Group X] (Y : Subgroup X) (E : Subgroup X)
    (hEY : E ≤ Y) (hE2 : IsPGroup 2 ↥E) (hEn : (E.subgroupOf Y).Normal)
    (hC : ∀ y ∈ Y, (∀ e ∈ E, y * e = e * y) → y ∈ E)
    (hT : IsSimpleGroup (↥Y ⧸ E.subgroupOf Y)) (hT2 : ¬ IsPGroup 2 (↥Y ⧸ E.subgroupOf Y))
    (hord : ¬ Chi0Order (Nat.card (↥Y ⧸ E.subgroupOf Y))) : GoodLocal Y := by
  intro G _ _ K φ hφ hker
  have hE2' : IsPGroup 2 (E.subgroupOf Y) := hE2.of_equiv (Subgroup.subgroupOfEquivOfLe hEY).symm
  let q : ↥K →* (↥Y ⧸ E.subgroupOf Y) := (QuotientGroup.mk' (E.subgroupOf Y)).comp φ
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hφ
  have hqker : q.ker = (E.subgroupOf Y).comap φ := by
    ext k
    simp [q, MonoidHom.mem_ker]
  have hker2 : IsPGroup 2 q.ker := by
    rw [hqker]
    exact hE2'.comap_of_ker_isPGroup φ hker
  refine ⟨charTwo_of_quotient q hq hT hT2 hker2 ?_, not_hasChi0Block_of_quotient q hq hT hker2 hord⟩
  intro x hx
  have hmemker : ∀ k : ↥K, φ k ∈ E.subgroupOf Y → k ∈ q.ker := fun k hk => by
    rw [hqker]
    exact hk
  have hcomm : ∀ e ∈ E, ((φ x : ↥Y) : X) * e = e * ((φ x : ↥Y) : X) := by
    intro e he
    obtain ⟨k, hk⟩ := hφ ⟨e, hEY he⟩
    have hkE : φ k ∈ E.subgroupOf Y := by
      rw [hk]
      exact he
    have := hx k (hmemker k hkE)
    have h2 : φ x * φ k = φ k * φ x := by rw [← map_mul, ← map_mul, this]
    rw [hk] at h2
    exact congrArg Subtype.val h2
  have : ((φ x : ↥Y) : X) ∈ E := hC _ (φ x).2 hcomm
  rw [hqker]
  exact this

end CFSG.QuasithinUnique.Vol2Native.L239
