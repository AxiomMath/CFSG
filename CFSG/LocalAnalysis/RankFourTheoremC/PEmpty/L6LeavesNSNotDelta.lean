module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L618
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622Basic
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Frattini
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Lines

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace L6LeavesNS

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G]

theorem centralizer_eq_map_conj_of_zpowers {x b g : G}
    (h : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers b) :
    centralizer ({b} : Set G) = (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by
  have hcz : ∀ w : G,
      centralizer ({w} : Set G) = centralizer ((zpowers w : Subgroup G) : Set G) := fun w => by
    rw [zpowers_eq_closure, centralizer_closure]
  calc centralizer ({b} : Set G)
      = centralizer ((zpowers b : Subgroup G) : Set G) := hcz _
    _ = centralizer (((zpowers x).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
      rw [h]
    _ = (centralizer ((zpowers x : Subgroup G) : Set G)).map (MulAut.conj g).toMonoidHom :=
      (centralizer_map_automorphism _ _).symm
    _ = (centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom := by rw [hcz x]

theorem hasNormalPComplement_inf_centralizer {p : ℕ} {x b g : G}
    (h : (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers b) (H : Subgroup G)
    (hx : CFSG.HasNormalPComplement p ↥(centralizer ({x} : Set G))) :
    CFSG.HasNormalPComplement p ↥(H ⊓ centralizer ({b} : Set G)) := by
  have hC := centralizer_eq_map_conj_of_zpowers h
  let e : ↥(centralizer ({x} : Set G)) ≃* ↥(centralizer ({b} : Set G)) :=
    ((centralizer ({x} : Set G)).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hC.symm)
  exact CFSG.hasNormalPComplement_of_le p inf_le_right (CFSG.hasNormalPComplement_of_equiv p e hx)

end L6LeavesNS

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

theorem stepNotDeltaOmega_of_kfact64ii (h : KFact64iiNPC) : StepNotDeltaOmega := by
  intro G _ _ p P M x z hS hx hz H S hopt hO hΩ hnpc
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hHtop : H ≠ ⊤ := isTwoLocal_ne_top hS hopt.ext.pair.isTwoLocal
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp
      (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.toGlobal.d1Global.kProper H hHtop)
  have hzo : orderOf z = p := orderOf_eq_prime hz.pow_eq_one hz.ne_one
  have hxz : x * z = z * x := mem_centralizer_iff.mp hz.centralizes x hx.mem
  have hxnz : x ∉ zpowers z := s622_x_not_mem_zpowers hS hx hz
  have hpl := plane_of_central hS hx hz
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hBH : zpowers x ⊔ zpowers z ≤ H := hopt.ext.pair.le
  have hB3' : IsPGroup p ↥((zpowers x ⊔ zpowers z).subgroupOf H) :=
    hB3.of_equiv (subgroupOfEquivOfLe hBH).symm
  obtain ⟨Q', hQ'⟩ := hB3'.exists_le_sylow
  set Q : Subgroup G := (Q' : Subgroup H).map H.subtype with hQ
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf p Q H := ⟨Q', rfl⟩
  have hBQ : zpowers x ⊔ zpowers z ≤ Q := by
    intro b hb
    have hbH : (⟨b, hBH hb⟩ : H) ∈ (zpowers x ⊔ zpowers z).subgroupOf H := hb
    exact ⟨⟨b, hBH hb⟩, hQ' hbH, rfl⟩
  have hQM : Q ≤ M := hopt.sylow_le Q hQsyl.isPGroup hQsyl.le hBQ
  have hΩQ := hΩ Q hQsyl.le hQsyl.isPGroup hBQ
  have hfr : x ∉ (frattini ↥Q).map Q.subtype := x_not_mem_frattini hS hx hQsyl.isPGroup
  have hwc : ∀ g ∈ H, g * z * g⁻¹ ∈ zpowers x ⊔ zpowers z → g * z * g⁻¹ ∈ zpowers z :=
    fun g _ hg => mem_zpowers_of_conj_mem_plane hS hx hz hg
  have hNZ : normalizer (zpowers z : Set G) ⊓ H ≤ M ⊓ H :=
    fun g hg => ⟨normalizer_zpowers_le hS hz hg.1, hg.2⟩
  have hcover : ¬ H ≤ (M ⊓ H) ⊔ rankThreePrimeCore p H := by
    intro hle
    exact hopt.ext.pair.not_le (hle.trans (sup_le inf_le_left hO))
  obtain ⟨b, hbB, hbZ, hbN⟩ := h G p H Q (M ⊓ H) x z hprime hS.p_ge hKH hx.order hzo hxz hxnz
    hQsyl hBQ hΩQ hfr hwc (le_inf hQM hQsyl.le) inf_le_right hNZ hcover
  obtain ⟨g, -, hgconj⟩ := exists_mem_normalizer_conj_zpowers hS hx hz hbB hbZ
  exact hbN (L6LeavesNS.hasNormalPComplement_inf_centralizer hgconj H hnpc)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
