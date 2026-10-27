module

public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG

open CFSG.ABGLocalTools

theorem isSylowOf_map_of_not_dvd_card_ker {X Y : Type} [Group X] [Group Y] [Finite X]
    [Finite Y] (f : X →* Y) (hf : Function.Surjective f) {p : Nat} (hp : p.Prime)
    (hker : ¬ p ∣ Nat.card ↥(MonoidHom.ker f)) {S K : Subgroup X}
    (hSyl : IsSylowOf p S K) : IsSylowOf p (S.map f) (K.map f) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hSK : S ≤ K := hSyl.le
  rw [isSylowOf_iff] at hSyl ⊢
  obtain ⟨hle, hSp, hSidx⟩ := hSyl
  refine ⟨Subgroup.map_mono hle, hSp.map f, ?_⟩
  rw [Subgroup.relIndex_map_map]
  have hKrel : ¬ p ∣ K.relIndex (K ⊔ MonoidHom.ker f) := by
    rw [sup_comm, relIndex_sup_eq_relIndex_of_normal (MonoidHom.ker f) K]
    exact fun h => hker (h.trans (Subgroup.relIndex_dvd_card K (MonoidHom.ker f)))
  have hSsup : ¬ p ∣ S.relIndex (K ⊔ MonoidHom.ker f) := by
    rw [← Subgroup.relIndex_mul_relIndex (H := S) (K := K) (L := K ⊔ MonoidHom.ker f)
      hSK le_sup_left]
    intro h
    rcases hp.dvd_mul.mp h with h1 | h1
    · exact hSidx h1
    · exact hKrel h1
  have hrel : (S ⊔ MonoidHom.ker f).relIndex (K ⊔ MonoidHom.ker f)
      ∣ S.relIndex (K ⊔ MonoidHom.ker f) :=
    Subgroup.relIndex_dvd_of_le_left (H := S) (K := S ⊔ MonoidHom.ker f)
      (L := K ⊔ MonoidHom.ker f) le_sup_left
  exact fun h => hSsup (h.trans hrel)

end CFSG
