module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Layer
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Defs
import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

theorem comp_le_centralizer_of_ne {C C' : ComponentIndex K} (h : C' ≠ C) :
    C'.1 ≤ centralizer (C.1 : Set K) :=
  commutator_eq_bot_iff_le_centralizer.1
    ((distinct_components_commute C'.2 C.2).resolve_left fun h' => h (Subtype.ext h'))

namespace Red

theorem eq_one_of_mem_of_mem_centralizer (R : Red n p K P z D) (C : ComponentIndex K) {x : K}
    (hx : x ∈ C.1) (hxc : x ∈ centralizer (C.1 : Set K)) : x = 1 := by
  have : (⟨x, hx⟩ : C.1) ∈ center C.1 :=
    mem_center_iff.2 fun g => Subtype.ext (mem_centralizer_iff.1 hxc g g.2)
  rw [R.hZ C, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem comm_D (R : Red n p K P z D) {a b : K} (ha : a ∈ D) (hb : b ∈ D) : a * b = b * a :=
  congrArg Subtype.val (R.conf.elem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem zc_centralizes (R : Red n p K P z D) {C : ComponentIndex K} {w : K} (hw : w ∈ D)
    (hwC : w • C = C) : w * R.zc C = R.zc C * w := by
  have h2 := π_conj (hZ := R.hZ) w C R.hzL
  have hwz : w * z * w⁻¹ = z := by
    rw [R.comm_D hw R.conf.mem]
    group
  have h3 : π R.hZ (cjComp w C) (w * z * w⁻¹) (conj_mem_layer w R.hzL) =
      π R.hZ (cjComp w C) z R.hzL := π_congr _ hwz _ _
  rw [h3] at h2
  have e : cjComp w C = C := hwC
  rw [e] at h2
  exact mul_inv_eq_iff_eq_mul.1 h2.symm

theorem zc_mem_of_normalizes (R : Red n p K P z D)
    (hD : ∀ w ∈ D, ∀ C : ComponentIndex K, w • C = C) (C : ComponentIndex K) : R.zc C ∈ D := by
  haveI := R.fact
  have hcen : R.zc C ∈ centralizer (D : Set K) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact R.zc_centralizes hw (hD w hw C)
  exact R.conf.mem_of_pElement_mem_centralizer R.prime hcen
    ⟨1, by rw [pow_one]; exact R.zc_pow C⟩

theorem subsingleton_of_normalizes (R : Red n p K P z D) (h3 : 3 ≤ p)
    (hD : ∀ w ∈ D, ∀ C : ComponentIndex K, w • C = C) : Subsingleton (ComponentIndex K) := by
  haveI := R.fact
  have hp := R.prime
  haveI := R.isPretransitive
  by_contra hns
  rw [not_subsingleton_iff_nontrivial] at hns
  obtain ⟨C₀⟩ := exists_comp R.core R.nc
  obtain ⟨k, hk⟩ := (P.isPGroup' : IsPGroup p (P : Subgroup K)).card_orbit C₀
  have hcard : Nat.card (ComponentIndex K) = p ^ k := by
    rw [← hk, MulAction.orbit_eq_univ (P : Subgroup K) C₀]
    exact (Nat.card_congr (Equiv.Set.univ _)).symm
  have hk0 : k ≠ 0 := by
    rintro rfl
    have : Nat.card (ComponentIndex K) = 1 := by rw [hcard]; rfl
    have h2 := (Nat.card_eq_one_iff_unique.1 this).1
    exact (not_subsingleton_iff_nontrivial.2 hns) h2
  have hge : 3 ≤ Nat.card (ComponentIndex K) := by
    rw [hcard]
    exact h3.trans (Nat.le_self_pow hk0 p)
  haveI := Fintype.ofFinite (ComponentIndex K)
  obtain ⟨a, b, c, hab, hac, hbc⟩ := (Fintype.two_lt_card_iff (α := ComponentIndex K)).1
    (by rw [Fintype.card_eq_nat_card]; omega)
  have hxa := R.zc_mem_of_normalizes hD a
  have hxb := R.zc_mem_of_normalizes hD b
  have hxc := R.zc_mem_of_normalizes hD c
  have hnot : R.zc b ∉ zpowers (R.zc a) := by
    intro hmem
    have h1 : R.zc b ∈ a.1 := (zpowers_le.2 (R.zc_mem a)) hmem
    exact R.zc_ne_one b (R.eq_one_of_mem_of_mem_centralizer a h1
      (comp_le_centralizer_of_ne (Ne.symm hab) (R.zc_mem b)))
  obtain ⟨s, t, hst⟩ := exists_pow_mul_pow_of_mem_plane R.conf.elem R.conf.card hxa
    (R.zc_ne_one a) hxb hnot hxc
  have hta : R.zc a ^ t = 1 := by
    have h1 : R.zc a ^ t = (R.zc b ^ s)⁻¹ * R.zc c := by
      rw [hst]
      group
    refine R.eq_one_of_mem_of_mem_centralizer a (pow_mem (R.zc_mem a) t) ?_
    rw [h1]
    exact mul_mem (inv_mem (pow_mem (comp_le_centralizer_of_ne (Ne.symm hab) (R.zc_mem b)) s))
      (comp_le_centralizer_of_ne (Ne.symm hac) (R.zc_mem c))
  have hsb : R.zc b ^ s = 1 := by
    have h1 : R.zc b ^ s = R.zc c * (R.zc a ^ t)⁻¹ := by
      rw [hst]
      group
    refine R.eq_one_of_mem_of_mem_centralizer b (pow_mem (R.zc_mem b) s) ?_
    rw [h1]
    exact mul_mem (comp_le_centralizer_of_ne (Ne.symm hbc) (R.zc_mem c))
      (inv_mem (pow_mem (comp_le_centralizer_of_ne hab (R.zc_mem a)) t))
  exact R.zc_ne_one c (by rw [hst, hsb, hta]; simp)

theorem layer_eq_of_subsingleton (hS : Subsingleton (ComponentIndex K)) (C₀ : ComponentIndex K) :
    layer K = C₀.1 := by
  apply le_antisymm
  · refine sSup_le fun C hC => ?_
    have : (⟨C, hC⟩ : ComponentIndex K) = C₀ := Subsingleton.elim _ _
    exact le_of_eq (congrArg Subtype.val this)
  · exact component_le_layer C₀.2

theorem centralizer_eq_bot (R : Red n p K P z D) (hS : Subsingleton (ComponentIndex K))
    (C₀ : ComponentIndex K) : centralizer (C₀.1 : Set K) = ⊥ := by
  haveI := R.fact
  have hF : fittingSubgroup K = ⊥ := by rw [Fitting_eq_pcore K p R.core, R.pc]
  have hgf : generalizedFitting K = C₀.1 := by
    rw [generalizedFitting.eq_sup, hF, bot_sup_eq]
    exact layer_eq_of_subsingleton hS C₀
  have hle := centralizer_generalizedFitting_le K
  rw [hgf] at hle
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact R.eq_one_of_mem_of_mem_centralizer C₀ (hle hx) hx

theorem isSimpleGroup_comp (R : Red n p K P z D) (C : ComponentIndex K) :
    IsSimpleGroup C.1 ∧ ∃ a b : C.1, a * b ≠ b * a := by
  obtain ⟨-, hsimple, a, b, hab⟩ := C.2.1
  let e : C.1 ⧸ center C.1 ≃* C.1 :=
    (QuotientGroup.quotientMulEquivOfEq (R.hZ C)).trans QuotientGroup.quotientBot
  refine ⟨MulEquiv.isSimpleGroup e.symm, e a, e b, fun h => hab ?_⟩
  exact e.injective (show e (a * b) = e (b * a) by rw [map_mul, map_mul]; exact h)

theorem caseA (hI : GL83I294Two) (R : Red n p K P z D) (h5 : 5 ≤ p) (hn : 3 ≤ n)
    (hcat : CFSG.AGLEmbedding.CatalogSimpleSections K) {g : K} (hg : IsPlaneDiagonal p D z g)
    (hlow : ∃ x ∈ D, x ≠ 1 ∧ CFSG.Open.pRank p (centralizer ({x} : Set K)) ≤ 2)
    (hD : ∀ w ∈ D, ∀ C : ComponentIndex K, w • C = C) :
    (∀ T : Subgroup K, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set K) → T = ⊥) ∨
      LinesTransitive D := by
  haveI := R.fact
  have hS := R.subsingleton_of_normalizes (by omega) hD
  obtain ⟨C₀⟩ := exists_comp R.core R.nc
  obtain ⟨hsimple, hnonab⟩ := R.isSimpleGroup_comp C₀
  haveI : C₀.1.Normal :=
    ⟨fun x hx g => by
      have h1 := mem_cjComp_of_mem g C₀ hx
      rwa [Subsingleton.elim (cjComp g C₀) C₀] at h1⟩
  have hcatL : IsCatalogGroup C₀.1 := hcat.simple_subgroup C₀.1 hsimple hnonab
  have hrank : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) :=
    hn.trans (R.conf.rank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p R.prime le_top))
  exact hI p R.prime h5 K C₀.1 hsimple hnonab hcatL (R.centralizer_eq_bot hS C₀) D R.conf.elem
    R.conf.card R.conf.sylow hrank z g R.conf.mem R.z_ne_one hg hlow

end Red

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
