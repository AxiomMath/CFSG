module

public import CFSG.GroupTheory.PCore.PrimeCoreImages

public section

namespace CFSG

theorem pPrimeCore_eq_bot_of_pi_range_eq_bot {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {ι : Type*} {H : ι → Type*} [∀ i, Group (H i)] [∀ i, Finite (H i)]
    (φ : ∀ i, G →* H i) (hpi : Function.Injective (MonoidHom.pi φ))
    (hH : ∀ i, pPrimeCore p ↥(φ i).range = ⊥) : pPrimeCore p G = ⊥ := by
  classical
  rw [pPrimeCore_eq_bot_iff]
  intro K hK hKcop
  have hKker : ∀ i, K ≤ (φ i).ker := by
    intro i
    have hKle : K ≤ pPrimeCore p G := le_sSup ⟨hK, hKcop⟩
    have hmap : K.map ((φ i).rangeRestrict) ≤ pPrimeCore p ↥(φ i).range :=
      (Subgroup.map_mono hKle).trans
        (map_pPrimeCore_le ((φ i).rangeRestrict) (MonoidHom.rangeRestrict_surjective _))
    rw [hH i] at hmap
    have hbot : K.map ((φ i).rangeRestrict) = ⊥ := le_bot_iff.1 hmap
    intro x hx
    rw [MonoidHom.mem_ker]
    have hx1 : ((φ i).rangeRestrict x) ∈ K.map ((φ i).rangeRestrict) :=
      Subgroup.mem_map_of_mem _ hx
    rw [hbot] at hx1
    simpa using congrArg Subtype.val (Subgroup.mem_bot.1 hx1)
  have hKpi : K ≤ (MonoidHom.pi φ).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    funext i
    have hi : x ∈ (φ i).ker := hKker i hx
    rwa [MonoidHom.mem_ker] at hi
  have hbot : (MonoidHom.pi φ).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 hpi
  rw [hbot] at hKpi
  exact le_bot_iff.1 hKpi

end CFSG
