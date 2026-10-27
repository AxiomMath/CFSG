module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.QInvariant

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CentralImageOrder

open CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.Local

variable {G : Type} [Group G] [Finite G]

theorem Z_le_K (P T B : Subgroup G) : Z P T B ≤ K P T B := by
  rintro _ ⟨c, _, rfl⟩
  exact Subgroup.mem_sup_left c.2

theorem card_le_two {p : ℕ} {P T B : Subgroup G} {e : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : ExtraspecialBinaryActionCounterexample G p P T B e ρ) {H : Subgroup (MulAut ↥P)} (hH : H ≤ Z P T B)
    (hindex : H.relIndex (Z P T B) = 2) :
    haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
    haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
    haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
    Nat.card (((Z P T B).subgroupOf (K P T B)).map
      (beta p P T B H (QInvariant.invariant hc hH))) ≤ 2 := by
  haveI : Fact p.Prime := ⟨hc.oddPrimeClassTwoAction.setting.prime⟩
  haveI : Fact (⁅⁅P, P⁆, P⁆ = ⊥) := ⟨hc.oddPrimeClassTwoAction.setting.class_le_two⟩
  haveI : Fact (Monoid.exponent ↥P = p) := ⟨hc.oddPrimeClassTwoAction.setting.exponent⟩
  set hinv := QInvariant.invariant hc hH
  set β := beta p P T B H hinv
  set Z' := (Z P T B).subgroupOf (K P T B)
  have hZK := Z_le_K P T B
  have hrange : Z'.map β = (β.comp Z'.subtype).range := by
    ext x; simp [MonoidHom.mem_range, Subgroup.mem_map]
  have hle : (H.subgroupOf (K P T B)).subgroupOf Z' ≤ (β.comp Z'.subtype).ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hz' : (z : K P T B).1 ∈ H := hz
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, beta_apply_coe]
    have := (BinaryRepresentations.mem_fixedSpace_iff _ _ _).1 v.2.2 _ hz'
    exact this
  have hidx : ((H.subgroupOf (K P T B)).subgroupOf Z').index = 2 := by
    rw [← Subgroup.relIndex, Subgroup.relIndex_subgroupOf hZK]
    exact hindex
  have hd := Subgroup.index_dvd_of_le hle
  rw [hidx, Subgroup.index_ker] at hd
  rw [hrange]
  exact Nat.le_of_dvd (by norm_num) hd

end CFSG.LocalAnalysis.RankThreeUC.Section5.CentralImageOrder
