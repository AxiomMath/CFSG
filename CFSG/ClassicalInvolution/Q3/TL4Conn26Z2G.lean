module

public import CFSG.RankThree.OddKernel.FixedPlaneKernel
public import CFSG.ClassicalInvolution.Q3.TL4LinkCases
public import CFSG.ClassicalInvolution.Q3.TL4Conn26Z2T

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T8
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance.Bootstrap (rankTwoSpan le_rankTwoSpan_of_le_centralizer)

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {J J₂ J₃ : Subgroup Y} {u v : Y}

namespace Z2FrameAt

theorem closure_le_centralizer (hL : TightLargeHypR r n Y R S t)
    (hF : Z2FrameAt R t J J₂ J₃ u v) :
    Subgroup.closure ({t, u, v} : Set Y) ≤ Subgroup.centralizer ({t} : Set Y) := by
  rw [Subgroup.closure_le]
  rintro w (rfl | rfl | rfl)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_tu hL).symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_tv hL).symm

theorem oddCoreOf_layerY_le_rankTwoSpan (hL : TightLargeHypR r n Y R S t)
    (hF : Z2FrameAt R t J J₂ J₃ u v) :
    oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) ≤
      rankTwoSpan (Subgroup.closure ({t, u, v} : Set Y)) := by
  have hΩ := hL.datum.hypOmegaGen
  have hA := hF.isElemAbelian hL
  have h8 := hF.natCard hL
  have hAt := hF.closure_le_centralizer hL
  have hnorm : Subgroup.closure ({t, u, v} : Set Y) ≤ Subgroup.normalizer
      (oddCoreOf (layerY (CoreAssembly.conjClass (tightCore R)) t) : Set Y) := by
    intro a ha
    rw [mem_normalizer_iff_conjSub_eq, ← Thompson.oddCoreOf_conjSub_eq,
      layerY_conjSub_eq hΩ.conjInvariant (hAt ha)]
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two _ _ hA (by rw [h8]; norm_num) hnorm
    (Nat.coprime_two_left.mpr (oddCoreOf_odd_natCard _))
  conv_lhs => rw [← hgen]
  exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right

theorem closure_pair_mem (hL : TightLargeHypR r n Y R S t) (hF : Z2FrameAt R t J J₂ J₃ u v)
    {a : Y} (haB : a ∈ Subgroup.closure ({t, u, v} : Set Y)) (ha1 : a ≠ 1) (hat : a ≠ t) :
    Subgroup.closure ({t, a} : Set Y) ∈
      CFSG.Open.signalizerFunctorEk 2 2 (Subgroup.closure ({t, u, v} : Set Y)) := by
  have ht := hL.datum.isUniqueInvolution_core
  have hB := hF.isElemAbelian hL
  have hm3 := mem_closure_three_left t u v
  have ha2 : a * a = 1 := (sq a).symm.trans (hB.2 a haB)
  have hta : t * a = a * t := by
    have h := hB.1.is_comm.comm ⟨t, hm3.1⟩ ⟨a, haB⟩
    exact congrArg Subtype.val h
  refine ⟨?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hm3.1
    · exact haB
  · rw [Balance.Bootstrap.card_closure_pair_eq_four ht.sq ha2 ht.ne_one ha1 hat.symm hta]
    norm_num

theorem linkLayer_le_rankTwoSpan (hL : TightLargeHypR r n Y R S t)
    (hF : Z2FrameAt R t J J₂ J₃ u v)
    (hgen : ∀ a a' : ↥(linkGrp R t), a * a = 1 → a ≠ 1 → a' * a' = 1 → a' ≠ 1 → a' ≠ a →
      a * a' = a' * a →
        Subgroup.centralizer ({a} : Set ↥(linkGrp R t)) ⊔
          Subgroup.centralizer ({a'} : Set ↥(linkGrp R t)) = ⊤) :
    linkLayer R t ≤ rankTwoSpan (Subgroup.closure ({t, u, v} : Set Y)) := by
  have hm3 := mem_closure_three_left t u v
  have hπs := linkLayerHom'_surjective hL
  have hker := ker_linkLayerHom hL
  have hodd2 : ¬ 2 ∣ Nat.card ↥(linkLayerHom' hL).ker := by
    rw [hker]
    exact Nat.not_even_iff_odd.mpr (CFSG.ComponentClassification.OddCore.odd_card _) ∘
      even_iff_two_dvd.mpr
  have hoddker : ∀ x : ↥(linkLayer R t), linkLayerHom' hL x = 1 → Odd (orderOf x) := by
    intro x hx
    have hxk : x ∈ classicalInvolutionOddCore ↥(linkLayer R t) := by
      rw [← hker]
      exact hx
    have hdvd := orderOf_dvd_natCard (⟨x, hxk⟩ : ↥(classicalInvolutionOddCore ↥(linkLayer R t)))
    rw [Subgroup.orderOf_mk] at hdvd
    exact (CFSG.ComponentClassification.OddCore.odd_card ↥(linkLayer R t)).of_dvd_nat hdvd
  set uL : ↥(linkLayer R t) := ⟨u, hF.u_mem_linkLayer hL⟩ with huL
  set vL : ↥(linkLayer R t) := ⟨v, hF.v_mem_linkLayer hL⟩ with hvL
  have hu2 : uL * uL = 1 := Subtype.ext hF.invJ.sq
  have hv2 : vL * vL = 1 := Subtype.ext hF.invJ₂.sq
  have huv : uL * vL = vL * uL := Subtype.ext hF.comm
  have hinv : ∀ x : ↥(linkLayer R t), x * x = 1 → x ≠ 1 → linkLayerHom' hL x ≠ 1 := by
    intro x hx2 hx1 h
    have h1 := hoddker x h
    rw [orderOf_eq_prime (by rw [sq]; exact hx2) hx1] at h1
    exact absurd h1 (by decide)
  have hu1 : uL ≠ 1 := fun h => hF.invJ.ne_one (congrArg Subtype.val h)
  have hv1 : vL ≠ 1 := fun h => hF.invJ₂.ne_one (congrArg Subtype.val h)
  have huvne : linkLayerHom' hL vL ≠ linkLayerHom' hL uL := by
    intro h
    have h1 : linkLayerHom' hL (vL * uL) = 1 := by
      rw [map_mul, h, ← map_mul, hu2, map_one]
    refine hinv (vL * uL) ?_ ?_ h1
    · calc vL * uL * (vL * uL) = vL * (uL * vL) * uL := by group
        _ = vL * vL * (uL * uL) := by rw [huv]; group
        _ = 1 := by rw [hu2, hv2, one_mul]
    · intro h2
      apply hF.ne
      have h3 : vL = uL⁻¹ := eq_inv_of_mul_eq_one_left h2
      rw [inv_eq_of_mul_eq_one_right hu2] at h3
      exact congrArg Subtype.val h3
  have htop := hgen (linkLayerHom' hL uL) (linkLayerHom' hL vL) (by rw [← map_mul, hu2, map_one])
    (hinv uL hu2 hu1) (by rw [← map_mul, hv2, map_one]) (hinv vL hv2 hv1) huvne
    (by rw [← map_mul, ← map_mul, huv])
  have hou : orderOf uL = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hov : orderOf vL = 2 := orderOf_eq_prime (by rw [sq]; exact hv2) hv1
  rw [← CFSG.RankThree.OddKernel.map_centralizer_eq_of_odd _ hπs hodd2 hou,
    ← CFSG.RankThree.OddKernel.map_centralizer_eq_of_odd _ hπs hodd2 hov, ← Subgroup.map_sup]
    at htop
  have hcov : ∀ x : ↥(linkLayer R t), x ∈ (Subgroup.centralizer ({uL} : Set ↥(linkLayer R t)) ⊔
      Subgroup.centralizer ({vL} : Set ↥(linkLayer R t))) ⊔ (linkLayerHom' hL).ker := by
    intro x
    rw [← Subgroup.comap_map_eq, htop]
    exact Subgroup.mem_top _
  have hCu : (Subgroup.centralizer ({uL} : Set ↥(linkLayer R t))).map (linkLayer R t).subtype ≤
      rankTwoSpan (Subgroup.closure ({t, u, v} : Set Y)) := by
    refine le_rankTwoSpan_of_le_centralizer (hF.closure_pair_mem hL hm3.2.1 hF.invJ.ne_one
      (hF.ne_tu hL).symm) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro s (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer x.2)).symm
    · have h := Subgroup.mem_centralizer_singleton_iff.mp hx
      exact (congrArg Subtype.val h).symm
  have hCv : (Subgroup.centralizer ({vL} : Set ↥(linkLayer R t))).map (linkLayer R t).subtype ≤
      rankTwoSpan (Subgroup.closure ({t, u, v} : Set Y)) := by
    refine le_rankTwoSpan_of_le_centralizer (hF.closure_pair_mem hL hm3.2.2 hF.invJ₂.ne_one
      (hF.ne_tv hL).symm) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro s (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (linkLayerAt_le_centralizer x.2)).symm
    · have h := Subgroup.mem_centralizer_singleton_iff.mp hx
      exact (congrArg Subtype.val h).symm
  have hO : (linkLayerHom' hL).ker.map (linkLayer R t).subtype ≤
      rankTwoSpan (Subgroup.closure ({t, u, v} : Set Y)) := by
    refine le_trans ?_ (hF.oddCoreOf_layerY_le_rankTwoSpan hL)
    rintro _ ⟨x, hx, rfl⟩
    have h1 : linkLayerHom hL x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    rw [linkLayerHom_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact mem_oddCoreOf_iff.mpr ⟨linkLayer_le_layerY hL x.2, h1⟩
  intro y hy
  have h1 := Subgroup.mem_map_of_mem (linkLayer R t).subtype (hcov ⟨y, hy⟩)
  rw [Subgroup.map_sup, Subgroup.map_sup] at h1
  exact (sup_le (sup_le hCu hCv) hO) h1

theorem exists_linkStep (hL : TightLargeHypR r n Y R S t) (htr : LinkTrans R t)
    (hgen : ∀ a a' : ↥(linkGrp R t), a * a = 1 → a ≠ 1 → a' * a' = 1 → a' ≠ 1 → a' ≠ a →
      a * a' = a' * a →
        Subgroup.centralizer ({a} : Set ↥(linkGrp R t)) ⊔
          Subgroup.centralizer ({a'} : Set ↥(linkGrp R t)) = ⊤)
    (hF : Z2FrameAt R t J J₂ J₃ u v) {J' : Subgroup Y}
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R)) :
    ∃ g ∈ Subgroup.centralizer ({t} : Set Y),
      g ∈ rankTwoSpan (Subgroup.closure ({t, u, v} : Set Y)) ∧ J' = conjSub g J := by
  have h := TightLargeHypR.typeRFam hL
  obtain ⟨gb, hgb⟩ := htr _ (subgroupOf_mem_linkRestrict (t := t) hF.memJ) _
    (subgroupOf_mem_linkRestrict (t := t) hJ')
  rw [Generic.conjSub_subgroupOf] at hgb
  have hle : conjSub (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t)
      (secImg (CoreAssembly.conjClass (tightCore R)) t J) ≤ linkGrp R t := by
    have h1 := conjSub_mono (n := (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t))
      (le_linkGrp (t := t) hF.memJ)
    rwa [conjSub_eq_self_of_mem gb.2] at h1
  have h1 := Subgroup.subgroupOf_inj.mp hgb
  rw [inf_of_le_left hle, inf_of_le_left (le_linkGrp (t := t) hJ')] at h1
  obtain ⟨g₁, hg₁⟩ := linkLayerHom'_surjective hL gb
  have hg₁Y := linkLayer_le_layerY hL g₁.2
  have hg₁C : (g₁ : Y) ∈ Subgroup.centralizer ({t} : Set Y) := linkLayerAt_le_centralizer g₁.2
  have h2 : secImg (CoreAssembly.conjClass (tightCore R)) t (conjSub (g₁ : Y) J) =
      secImg (CoreAssembly.conjClass (tightCore R)) t J' := by
    have e : QuotientGroup.mk' (classicalInvolutionOddCore
        ↥(layerY (CoreAssembly.conjClass (tightCore R)) t)) ⟨g₁, hg₁Y⟩ =
          (gb : SecQuot (CoreAssembly.conjClass (tightCore R)) t) := by
      rw [← hg₁]
      rfl
    have h3 := conjSub_secImg (Ω := CoreAssembly.conjClass (tightCore R)) (x := t)
      ⟨(g₁ : Y), hg₁Y⟩ J
    rw [e, h1] at h3
    exact h3.symm
  have hJg := conjSub_mem_omegaNbr_core hL hF.memJ hg₁C
  obtain ⟨ν, hν, hJeq⟩ := exists_conj_of_secImg_eq h (xMem_of_mem_omegaNbr_core hL hJg)
    (xMem_of_mem_omegaNbr_core hL hJ') h2
  refine ⟨(ν : Y) * g₁, Subgroup.mul_mem _ (layerY_le_centralizer ν.2) hg₁C,
    Subgroup.mul_mem _ (hF.oddCoreOf_layerY_le_rankTwoSpan hL ⟨ν, hν, rfl⟩)
      (hF.linkLayer_le_rankTwoSpan hL hgen g₁.2), ?_⟩
  rw [hJeq, ← conjSub_mul]

end Z2FrameAt

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
