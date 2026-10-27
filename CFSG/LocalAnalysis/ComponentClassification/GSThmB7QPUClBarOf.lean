module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7QPUClBar
public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.ComponentClassification.GSThmB.QPUCl

open CFSG Subgroup
open scoped commutatorElement

theorem commutatorElement_mul_center {G : Type*} [Group G] (x y : G) {z w : G}
    (hz : z ∈ center G) (hw : w ∈ center G) : ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  have hz' := mem_center_iff.1 hz
  have hw' := mem_center_iff.1 hw
  have h1 : z * (y * w) * z⁻¹ = y * w := by rw [← hz' (y * w), mul_inv_cancel_right]
  have h2 : x * (y * w) * x⁻¹ = x * y * x⁻¹ * w := by
    calc x * (y * w) * x⁻¹ = x * y * (w * x⁻¹) := by group
      _ = x * y * (x⁻¹ * w) := by rw [hw' x⁻¹]
      _ = x * y * x⁻¹ * w := by group
  calc ⁅x * z, y * w⁆ = x * (z * (y * w) * z⁻¹) * x⁻¹ * (y * w)⁻¹ := by
        rw [commutatorElement_def]
        group
    _ = x * (y * w) * x⁻¹ * (y * w)⁻¹ := by rw [h1]
    _ = ⁅x, y⁆ := by
        rw [h2, commutatorElement_def]
        group

variable {M : Type} [Group M] [Finite M]

omit [Finite M] in
theorem isPerfect_of_isPComponent {H L : Subgroup M} (hLH : L ≤ H)
    (hL : IsPComponent 2 (L.subgroupOf H)) : Group.IsPerfect L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CatalogueBAlternating.pComponent_perfect hL
  exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hLH).toMonoidHom)
    (subgroupOfEquivOfLe hLH).surjective

omit [Finite M] in
theorem map_mk_ne_top [Group.IsPerfect M] {L : Subgroup M} (hL : L ≠ ⊤) :
    L.map (QuotientGroup.mk' (center M)) ≠ ⊤ := by
  intro htop
  apply hL
  have hcomm : commutator M ≤ L := by
    rw [commutator_def, commutator_le]
    intro a _ b _
    have ha : QuotientGroup.mk' (center M) a ∈ L.map (QuotientGroup.mk' (center M)) :=
      htop ▸ mem_top _
    have hb : QuotientGroup.mk' (center M) b ∈ L.map (QuotientGroup.mk' (center M)) :=
      htop ▸ mem_top _
    obtain ⟨la, hla, hla'⟩ := ha
    obtain ⟨lb, hlb, hlb'⟩ := hb
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hla' hlb'
    have hae : a = la * (la⁻¹ * a) := by group
    have hbe : b = lb * (lb⁻¹ * b) := by group
    rw [hae, hbe, commutatorElement_mul_center la lb hla' hlb']
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hla hlb) (inv_mem hla)) (inv_mem hlb)
  rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := M)]
  exact hcomm

theorem barConfig_of_central (hM : IsQuasisimple M) (hZ : IsPGroup 2 (center M))
    {p' f' p f : ℕ} {E : Subgroup (MulAut M)} {L : Subgroup M} {t : M} {J J₀ : Subgroup M}
    (hE : IsPGroup 2 E) (hLE : L ≤ fixedBy E) (hLc : IsPComponent 2 (L.subgroupOf (fixedBy E)))
    (hLtop : L ≠ ⊤) (hLm : Blueprint.LieModel (↥L ⧸ pPrimeCore 2 ↥L) .PSp 2 p' f')
    (htL : t ∈ L) (ht2 : t * t = 1) (htZ : t ∉ center M)
    (hJt : J ≤ centralizer {t}) (hJc : IsPComponent 2 (J.subgroupOf (centralizer {t})))
    (hJm : Blueprint.LieModel (↥J ⧸ pPrimeCore 2 ↥J) .PSL 2 p f)
    (hJ₀L : J₀ ≤ L) (hJ₀J : J₀ ≤ J) (hJ₀ : J₀ ⊔ (pPrimeCore 2 ↥J).map J.subtype = J) :
    BarConfig (M ⧸ center M) p' f' p f := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect M := hM.1
  have hLperf := isPerfect_of_isPComponent hLE hLc
  have hJperf := isPerfect_of_isPComponent hJt hJc
  have hLZ := inf_center_eq_bot hZ (center_eq_bot_of_lieModel (Or.inr rfl) hLm)
  have hJZ := inf_center_eq_bot hZ (center_eq_bot_of_lieModel (Or.inl rfl) hJm)
  set eL := equivMapMk hLZ with heL
  set eJ := equivMapMk hJZ with heJ
  obtain ⟨hLb, hLbc⟩ := isPComponent_map_fixedBy E hLE hLc
  obtain ⟨hJb, hJbc⟩ := isPComponent_map_centralizer t hJt hJc
  refine ⟨E.map (quotAut M), L.map (QuotientGroup.mk' (center M)),
    QuotientGroup.mk' (center M) t, J.map (QuotientGroup.mk' (center M)),
    J₀.map (QuotientGroup.mk' (center M)), hE.map _, hLb, hLbc, map_mk_ne_top hLtop,
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eL (pPrimeCore_map_iso 2 eL)) hLm,
    ⟨t, htL, rfl⟩, by rw [← map_mul, ht2, map_one], ?_, hJb, hJbc,
    LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr _ _ eJ (pPrimeCore_map_iso 2 eJ)) hJm,
    map_mono hJ₀L, map_mono hJ₀J, ?_⟩
  · rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact htZ
  · have hmapO : ((pPrimeCore 2 ↥J).map J.subtype).map (QuotientGroup.mk' (center M)) =
        (pPrimeCore 2 ↥(J.map (QuotientGroup.mk' (center M)))).map
          (J.map (QuotientGroup.mk' (center M))).subtype := by
      rw [← pPrimeCore_map_iso 2 eJ, Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [← hmapO, ← Subgroup.map_sup, hJ₀]

end CFSG.ComponentClassification.GSThmB.QPUCl
