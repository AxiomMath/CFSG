module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Fixed
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitTypeRank

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_eq_bot_of_perfect_of_le_centralizer {J H : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (h : ⁅J, H⁆ ≤ centralizer (J : Set G)) : ⁅J, H⁆ = ⊥ := by
  have h1 : ⁅⁅J, H⁆, J⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr h
  have h2 : ⁅⁅H, J⁆, J⁆ = ⊥ := by
    rw [commutator_comm H J]
    exact h1
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  rwa [hJ] at h3

private theorem mem_normalizer_of_map_conj_le {H : Subgroup G} {x : G}
    (h : H.map (MulAut.conj x).toMonoidHom ≤ H) : x ∈ normalizer (H : Set G) :=
  mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge h
    (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]))

theorem isStandardSubgroup_of_normal {L : Subgroup G} {a : G} (hq : IsQuasisimple L)
    (ha2 : orderOf a = 2) (hLa : L ≤ centralizer ({a} : Set G))
    (hnorm : ∀ t : G, orderOf t = 2 → L ≤ centralizer ({t} : Set G) →
      centralizer ({t} : Set G) ≤ normalizer (L : Set G))
    (hcomm : ∀ g : G, ⁅L, conjugate L g⁆ ≠ ⊥) : IsStandardSubgroup L := by
  have hperf : ⁅L, L⁆ = L := (Subgroup.isPerfect_iff (H := L)).mp hq.1
  have hkey : ∀ (g t : G), orderOf t = 2 → L ≤ centralizer ({t} : Set G) →
      conjugate L g ≤ centralizer ({t} : Set G) → conjugate L g = L := by
    intro g t ht htL htLg
    set Lg : Subgroup G := conjugate L g with hLg
    have hLN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) := hnorm t ht htL
    have hLgN : centralizer ({t} : Set G) ≤ normalizer (Lg : Set G) := by
      have ht' : orderOf (g * t * g⁻¹) = 2 := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ht]
      have hLt' : L ≤ centralizer ({g * t * g⁻¹} : Set G) := by
        intro l hl
        have hmem : g⁻¹ * l * g ∈ Lg := ⟨l, hl, by simp⟩
        have h1 := mem_centralizer_singleton_iff.mp (htLg hmem)
        rw [mem_centralizer_singleton_iff]
        calc l * (g * t * g⁻¹) = g * ((g⁻¹ * l * g) * t) * g⁻¹ := by group
          _ = g * (t * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
          _ = g * t * g⁻¹ * l := by group
      intro c hc
      have hc' : g * c * g⁻¹ ∈ centralizer ({g * t * g⁻¹} : Set G) := by
        rw [mem_centralizer_singleton_iff] at hc ⊢
        calc g * c * g⁻¹ * (g * t * g⁻¹) = g * (c * t) * g⁻¹ := by group
          _ = g * (t * c) * g⁻¹ := by rw [hc]
          _ = g * t * g⁻¹ * (g * c * g⁻¹) := by group
      have hcN := hnorm _ ht' hLt' hc'
      refine mem_normalizer_of_map_conj_le ?_
      rintro _ ⟨y, ⟨l, hl, rfl⟩, rfl⟩
      refine ⟨(g * c * g⁻¹) * l * (g * c * g⁻¹)⁻¹, (mem_normalizer_iff.mp hcN l).mp hl, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    by_contra hne
    have hc1 : ⁅L, Lg⁆ ≤ L := le_normalizer_iff_commutator_le_left.mp (htLg.trans hLN)
    have hc2 : ⁅L, Lg⁆ ≤ Lg := by
      rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_left.mp (htL.trans hLgN)
    have hn : ((L ⊓ Lg).subgroupOf L).Normal := by
      refine ⟨fun x hx l => ?_⟩
      rw [mem_subgroupOf] at hx ⊢
      obtain ⟨hxL, hxLg⟩ := mem_inf.mp hx
      exact mem_inf.mpr ⟨mul_mem (mul_mem l.2 hxL) (inv_mem l.2),
        (mem_normalizer_iff.mp (hLgN (htL l.2)) x).mp hxLg⟩
    rcases LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hn with h | h
    · apply hne
      refine (eq_of_le_of_card_ge (fun x hx => ?_) ?_).symm
      · have hx' : (⟨x, hx⟩ : L) ∈ (L ⊓ Lg).subgroupOf L := h ▸ mem_top _
        exact (mem_inf.mp (mem_subgroupOf.mp hx')).2
      · rw [hLg, conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective]
    · apply hcomm g
      refine commutator_eq_bot_of_perfect_of_le_centralizer hperf fun x hx => ?_
      have hx' : (⟨x, hc1 hx⟩ : L) ∈ (L ⊓ Lg).subgroupOf L :=
        mem_subgroupOf.mpr (mem_inf.mpr ⟨hc1 hx, hc2 hx⟩)
      have hz := mem_center_iff.mp (h hx')
      rw [mem_centralizer_iff]
      intro l hl
      exact congrArg Subtype.val (hz ⟨l, hl⟩)
  have hNLC : normalizer (L : Set G) ≤ normalizer (centralizer (L : Set G) : Set G) := by
    intro g hg
    refine mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_iff]
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (mem_normalizer_iff.mp (inv_mem hg) l).mp hl
      rwa [inv_inv] at this
    have h1 := (mem_centralizer_iff.mp hx) _ hl'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * l := by group
  have hfix : ∀ (g t : G), orderOf t = 2 → t ∈ centralizer (L : Set G) →
      t ∈ conjugate (centralizer (L : Set G)) g → g ∈ normalizer (L : Set G) := by
    intro g t ht htC htCg
    have htL : L ≤ centralizer ({t} : Set G) := fun l hl =>
      mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp htC) l hl)
    have htLg : conjugate L g ≤ centralizer ({t} : Set G) := by
      obtain ⟨c, hc, rfl⟩ := htCg
      rintro _ ⟨l, hl, rfl⟩
      have h1 := (mem_centralizer_iff.mp hc) l hl
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * l * g * (g⁻¹ * c * g) = g⁻¹ * (l * c) * g := by group
        _ = g⁻¹ * (c * l) * g := by rw [h1]
        _ = g⁻¹ * c * g * (g⁻¹ * l * g) := by group
    have heq := hkey g t ht htL htLg
    have h1 : g⁻¹ ∈ normalizer (L : Set G) := mem_normalizer_iff_map_conj_eq.mpr heq
    simpa using inv_mem h1
  have haC : a ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    (mem_centralizer_singleton_iff.mp (hLa hl))
  refine ⟨hq, ?_, ?_, ?_, hcomm⟩
  · have h1 : orderOf (⟨a, haC⟩ : centralizer (L : Set G)) = 2 := by
      rw [Subgroup.orderOf_mk, ha2]
    exact even_iff_two_dvd.mpr (h1 ▸ orderOf_dvd_natCard _)
  · intro g hg
    by_contra hodd
    have heven : 2 ∣ Nat.card ↥(centralizer (L : Set G) ⊓
        conjugate (centralizer (L : Set G)) g) :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 heven
    obtain ⟨hwC, hwCg⟩ := mem_inf.mp w.2
    exact hg (hNLC (hfix g w (by rw [← hw, Subgroup.orderOf_coe]) hwC hwCg))
  · refine le_antisymm (fun g hg => ?_) hNLC
    have hCg : conjugate (centralizer (L : Set G)) g = centralizer (L : Set G) :=
      mem_normalizer_iff_map_conj_eq.mp (inv_mem hg)
    exact hfix g a ha2 haC (by rw [hCg]; exact haC)

omit [Finite G] in
theorem fusionZStar_eq_center_of_le {J : Type*} [Group J] (hperf : commutator J = ⊤)
    (hO : pPrimeCore 2 J ≤ center J) : Open.fusionZStar J = center J := by
  apply le_antisymm
  · intro z hz
    have hc : ∀ m : J, ⁅z, m⁆ ∈ center J := fun m =>
      hO ((GSThmB.OddQuot.mem_fusionZStar_iff.mp hz) m)
    let φ : J →* J :=
      { toFun := fun m => ⁅z, m⁆
        map_one' := by simp
        map_mul' := fun m₁ m₂ => by
          have h2 : m₁ * ⁅z, m₂⁆ * m₁⁻¹ = ⁅z, m₂⁆ := by
            rw [(mem_center_iff.mp (hc m₂) m₁), mul_inv_cancel_right]
          show ⁅z, m₁ * m₂⁆ = ⁅z, m₁⁆ * ⁅z, m₂⁆
          rw [← h2]
          simp only [commutatorElement_def]
          group }
    have hrange : φ.range ≤ center J := by
      rintro _ ⟨m, rfl⟩
      exact hc m
    have h1 : (commutator J).map φ = ⊥ := by
      rw [map_commutator_eq, commutator_eq_bot_iff_le_centralizer]
      exact hrange.trans (center_le_centralizer _)
    rw [hperf, ← MonoidHom.range_eq_map] at h1
    rw [mem_center_iff]
    intro m
    have hm : φ m = 1 := by
      have : φ m ∈ φ.range := ⟨m, rfl⟩
      rw [h1] at this
      exact this
    have hm' : ⁅z, m⁆ = 1 := hm
    rw [commutatorElement_eq_one_iff_mul_comm] at hm'
    exact hm'.symm
  · intro z hz
    refine GSThmB.OddQuot.mem_fusionZStar_iff.mpr fun m => ?_
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp hz m).symm]
    exact one_mem _

theorem isQuasisimple_of_oddIn_le_center {C J : Subgroup G} (hJC : J ≤ C)
    (hJ : IsPComponent 2 (J.subgroupOf C)) (hO : oddIn J ≤ (center ↥J).map J.subtype) :
    IsQuasisimple J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 J C hJC).mp hJ
  have hperf : Group.IsPerfect J := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hJ
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hJC).toMonoidHom)
      (subgroupOfEquivOfLe hJC).surjective
  have hO' : pPrimeCore 2 ↥J ≤ center ↥J := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hO ⟨x, hx, rfl⟩
    rwa [← Subtype.ext hyx]
  have heq := fusionZStar_eq_center_of_le hperf.commutator_eq_top hO'
  obtain ⟨e₂⟩ := FooteLit.nonempty_fusionZStar_quotient_equiv ↥J
  let e : ↥J ⧸ center ↥J ≃* (↥J ⧸ pPrimeCore 2 ↥J) ⧸ center (↥J ⧸ pPrimeCore 2 ↥J) :=
    (QuotientGroup.quotientMulEquivOfEq heq.symm).trans e₂
  obtain ⟨-, hs, a, b, hab⟩ := hq
  have : IsSimpleGroup ((↥J ⧸ pPrimeCore 2 ↥J) ⧸ center (↥J ⧸ pPrimeCore 2 ↥J)) := hs
  refine ⟨hperf, e.isSimpleGroup, e.symm a, e.symm b, fun h => hab ?_⟩
  have := congrArg e h
  simpa using this

theorem centralizer_le_normalizer_of_isPComponent {J : Subgroup G} {t : G}
    (hT92 : ∀ g : G, ¬ ⁅J, conjugate J g⁆ ≤ oddIn J ⊓ oddIn (conjugate J g))
    (hJt : J ≤ centralizer ({t} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set G)))) :
    centralizer ({t} : Set G) ≤ normalizer (J : Set G) := by
  intro c hc
  apply mem_normalizer_of_conjugate_eq
  by_contra hne
  obtain ⟨hJct, hJcp⟩ := GSThmB.isPComponent_conjugate_centralizer_singleton hJt hJp hc
  exact hT92 c (commutator_le_inf_oddIn hJt hJct hJp hJcp fun h => hne h.symm)

theorem gsFixedLayer_eq_of_le {J : Subgroup G} {b t : G} (hJb : J ≤ centralizer ({b} : Set G))
    (hJp : IsPComponent 2 (J.subgroupOf (centralizer ({b} : Set G))))
    (hJt : J ≤ centralizer ({t} : Set G)) : gsFixedLayer J t = J := by
  have h := GSLit.gsFixedLayer_eq_self hJb hJp
  unfold gsFixedLayer at h ⊢
  rw [inf_eq_left.mpr hJb] at h
  rw [inf_eq_left.mpr hJt]
  exact h

theorem pumpUp_eq_of_oddIn_le_center {J : Subgroup G} {t : G}
    (hJt : J ≤ centralizer ({t} : Set G)) (hgs : gsFixedLayer J t = J)
    (hT91 : (⨆ (g : G) (_ : conjugate J g ≤ centralizer ({t} : Set G)), conjugate J g) ≤
      oddIn (centralizer ({t} : Set G)) ⊔ J)
    (hOP : oddIn (pumpUp J t) ≤ (center ↥J).map J.subtype) : pumpUp J t = J := by
  set C := centralizer ({t} : Set G) with hC
  set P := pumpUp J t with hP
  have hPC : P ≤ C := pumpUp_le_centralizer J t
  have hJP : J ≤ P := by
    refine le_iSup₂_of_le 1 (one_mem _) ?_
    rw [hgs]
    intro x hx
    exact ⟨x, hx, by simp⟩
  have hPO : P ≤ oddIn C ⊔ J := by
    refine iSup₂_le fun g hg => ?_
    rw [hgs]
    have hgC : g ∈ C := map_subtype_le _ hg
    have hJg : conjugate J g ≤ C := by
      rintro _ ⟨l, hl, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact mul_mem (mul_mem (inv_mem hgC) (hJt hl)) hgC
    exact (le_iSup₂_of_le g hJg le_rfl).trans hT91
  have hJN : J ≤ normalizer (oddIn C : Set G) := fun x hx =>
    normalizer_le_normalizer_oddIn C (le_normalizer (hJt hx))
  refine le_antisymm (fun p hp => ?_) hJP
  have hp' : p ∈ (oddIn C : Set G) * (J : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left (oddIn C) J hJN]
    exact hPO hp
  obtain ⟨o, ho, j, hj, rfl⟩ := hp'
  have hoP : o ∈ P := by
    have := mul_mem hp (inv_mem (hJP hj))
    rwa [mul_inv_cancel_right] at this
  have hoJ : o ∈ J := by
    have h1 := hOP (inf_oddIn_le_oddIn hPC (mem_inf.mpr ⟨ho, hoP⟩))
    exact map_subtype_le _ h1
  exact mul_mem hoJ hj

end CFSG.ComponentClassification.GrSLit.GrS5
