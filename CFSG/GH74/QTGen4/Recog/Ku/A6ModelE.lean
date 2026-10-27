module

public import CFSG.GH74.QTGen4.Recog.Ku.Defs
public import CFSG.GH74.QTGen4.Recog.Ku.A6ModelD

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku.A6

open CFSG.Quasithin.HSType CFSG.GH74.QTGen4.Ku

variable {G : Type} [Group G]

theorem nonempty_kuA6Model [Finite G] {T M H P : Subgroup G} {z : G}
    (hcardN : Nat.card ↥(Subgroup.normalizer (kuA P H : Set G)) = 5760)
    (hcardE : Nat.card ↥(kuA P H) = 16)
    {ω : G → G → ZMod 2} {Φ : SpV → G} (hΦ : CoordHyp (kuA P H) ω Φ)
    (he0 : Φ (spE 0) = z)
    (hpolar : ∀ v, Φ v ∈ kuW P H ↔ spForm (spE 0) v = 0)
    (hv2 : ∀ v, Φ v ∈ kuV2 T M ↔ InV2m v) :
    Nonempty (KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) := by
  obtain ⟨π, halt, hsurj, hker, hact⟩ := hΦ.exists_perm_model hcardN hcardE
  exact ⟨⟨Φ, π, hΦ.mem, hΦ.inj, hΦ.add, hΦ.surj, he0, hpolar, hv2, halt, hsurj, hker, hact⟩⟩

end CFSG.GH74.QTGen4.Ku.A6

end
