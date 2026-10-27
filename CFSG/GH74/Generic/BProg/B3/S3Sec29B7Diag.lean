module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29B7Cover
public import CFSG.GH74.Generic.BProg.B3.S3Sec29B7AbsD
public import CFSG.GH74.Generic.BProg.B3.S3Sec29B7Basic
public import CFSG.GH74.Generic.BProg.B3.S3Sec29BDiag
public import CFSG.GH74.Generic.BProg.B3.S3Boot293w
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29wFacts

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
  CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement MatrixGroups

theorem lemma296aw_sl2 {G : Type} [Group G] [Finite G] {x y b : G} {K A B Q D J : Subgroup G}
    (h : Ctx29w G x K A B Q y b D J)
    (hI : IsPCompIn 2 (K ⊓ centralizer ({b} : Set G)) (Ly29 K b))
    (hSL : HasSL2Model (↥(Ly29 K b) ⧸ pPrimeCore 2 ↥(Ly29 K b)) (fun q => Odd q ∧ 5 ≤ q))
    {r : ℕ} (hr : ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ r = p ^ f)
    (hJsl : HasSL2Model (↥J ⧸ pPrimeCore 2 ↥J) (fun q => q = r))
    (h295 : B ⊓ cSec K ⊓ cSec J = ⊥) : Ly29 K b ≤ cSec J := by
  classical
  by_contra hn
  obtain ⟨hb2, hJb, hbC⟩ := h.obs_data
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := h.circ.1.2.2.1.2.2
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hx2 : orderOf x = 2 := h.circ.1.1.1.1
  obtain ⟨hAB, hxB, hBCx, hBel, -, -, hBeq⟩ := h.ext
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  have hbx : b ∈ centralizer ({x} : Set G) := hBCx h.b_mem
  have hxb : x ∈ centralizer ({b} : Set G) := TwoThin.mem_centralizer_symm hbx
  set I : Subgroup G := Ly29 K b with hIdef
  have hIK : I ≤ K ⊓ centralizer ({b} : Set G) := hI.1
  have hIY : I ≤ centralizer ({b} : Set G) := hIK.trans inf_le_right
  have hIx : I ≤ centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G) :=
    hIK.trans (inf_le_inf_right _ hKC)
  have hID : IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G)) I := by
    have hsubK : (K.subgroupOf (centralizer ({x} : Set G))).IsSubnormal := by
      obtain ⟨Kb, -, hsub, -⟩ := hK.2
      exact hsub
    have hsub : ((K ⊓ centralizer ({b} : Set G)).subgroupOf
        (centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G))).IsSubnormal := by
      have h1 := TwoThin.isSubnormal_inf_subgroupOf hsubK
        (inf_le_left : centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G) ≤
          centralizer ({x} : Set G))
      have h2 : (K ⊓ centralizer ({b} : Set G)).subgroupOf
          (centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G)) =
          K.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({b} : Set G)) := by
        ext m
        simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        constructor
        · exact fun hm => hm.1
        · intro hm
          exact ⟨hm, (Subgroup.mem_inf.1 m.2).2⟩
      rwa [h2]
    exact B1.isPCompIn_of_isSubnormal 2 (inf_le_inf_right _ hKC) hsub hI
  have hso : orderOf (⟨x, hxb⟩ : ↥(centralizer ({b} : Set G))) = 2 :=
    TwoThin.orderOf_mk_centralizer hxb hx2
  have hΛC := TwoThin.le_centralizer_mk (Λ := I) hIx hxb
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hID hxb
  obtain ⟨-, -, L, hL, hcases, -, -, -⟩ := TwoThin.pumpupY_structure hso hΛC hΛ2
  have hJ' := TwoThin.isPCompIn_two_iff.1 hJb
  set barM : ↥(centralizer ({b} : Set G)) →* TwoThin.barQ ↥(centralizer ({b} : Set G)) :=
    TwoThin.barMk ↥(centralizer ({b} : Set G)) with hbarM
  set s : ↥(centralizer ({b} : Set G)) := ⟨x, hxb⟩ with hs
  set JY : Subgroup ↥(centralizer ({b} : Set G)) := J.subgroupOf (centralizer ({b} : Set G))
    with hJY
  have hM : IsComponent (JY.map barM) := TwoThin.isComponent_map_barMk hJ'.2
  set L' : Subgroup (TwoThin.barQ ↥(centralizer ({b} : Set G))) := conjSub (barM s)⁻¹ L
    with hL'
  have hL'c : IsComponent L' := isComponent_conjSub hL _
  by_cases hcase : JY.map barM = L ∨ JY.map barM = L'
  swap
  ·
    push Not at hcase
    obtain ⟨hc1', hc2'⟩ := hcase
    have hc1 : ⁅JY.map barM, L⁆ = ⊥ := (distinct_components_commute hM hL).resolve_left hc1'
    have hc2 : ⁅JY.map barM, L'⁆ = ⊥ := (distinct_components_commute hM hL'c).resolve_left hc2'
    apply hn
    intro q hq
    have hqC : q ∈ centralizer ({b} : Set G) := hIY hq
    have hqΛ : (⟨q, hqC⟩ : ↥(centralizer ({b} : Set G))) ∈
        I.subgroupOf (centralizer ({b} : Set G)) := Subgroup.mem_subgroupOf.2 hq
    refine TwoThin.mem_centralizerSection_of_map_eq hJ'.1 hJ'.2 hqC ?_
    intro m hm
    have hm' : barM m ∈ JY.map barM := ⟨m, hm, rfl⟩
    have hz : barM ⟨q, hqC⟩ ∈ (I.subgroupOf (centralizer ({b} : Set G))).map barM :=
      ⟨_, hqΛ, rfl⟩
    have hcL : ∀ c ∈ L, c * barM m = barM m * c := fun c hc =>
      Subgroup.mem_centralizer_iff.1 ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc1) hm')
        c hc
    have hcL' : ∀ c ∈ L', c * barM m = barM m * c := fun c hc =>
      Subgroup.mem_centralizer_iff.1 ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc2) hm')
        c hc
    have hcomm : barM ⟨q, hqC⟩ * barM m = barM m * barM ⟨q, hqC⟩ := by
      rcases hcases with ⟨-, hIL⟩ | ⟨-, hAB, hIsd⟩
      · exact hcL _ (hIL hz)
      · obtain ⟨l, hl⟩ := hIsd hz
        rw [← hl, swapDiag_apply]
        have h1 := hcL (l : TwoThin.barQ ↥(centralizer ({b} : Set G))) l.2
        have h2 := hcL' ((barM s)⁻¹ * (l : TwoThin.barQ ↥(centralizer ({b} : Set G))) * barM s)
          (conj_mem_conjSub l.2)
        calc ((l : TwoThin.barQ ↥(centralizer ({b} : Set G))) *
              ((barM s)⁻¹ * l * barM s)) * barM m
            = l * (((barM s)⁻¹ * l * barM s) * barM m) := by group
          _ = l * (barM m * ((barM s)⁻¹ * l * barM s)) := by rw [h2]
          _ = (l * barM m) * ((barM s)⁻¹ * l * barM s) := by group
          _ = (barM m * l) * ((barM s)⁻¹ * l * barM s) := by rw [h1]
          _ = barM m * (l * ((barM s)⁻¹ * l * barM s)) := by group
    rw [map_mul, map_mul, map_inv, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  ·
    have hsubJ : JY.IsSubnormal := by
      obtain ⟨Kb, -, hsub, -⟩ := hJb.2
      exact hsub
    obtain ⟨e1⟩ := TwoThin.hat_equiv_subgroupOf hJ'.1
    obtain ⟨e2⟩ := TwoThin.hat_equiv_map (M := JY) hsubJ
    let eJ : (↥J ⧸ pPrimeCore 2 ↥J) ≃* ↥(JY.map barM) := e1.trans e2
    have hMsl : HasSL2Model ↥(JY.map barM) (fun q => q = r) :=
      S3Boot293w.hasSL2Model_of_mulEquiv eJ hJsl
    have hxb2 : orderOf (barM s) = 2 := TwoThin.orderOf_barMk hso
    set Λ : Subgroup ↥(centralizer ({b} : Set G)) := I.subgroupOf (centralizer ({b} : Set G))
      with hΛdef
    set ρ : ↥I →* TwoThin.barQ ↥(centralizer ({b} : Set G)) :=
      barM.comp (Subgroup.inclusion hIY) with hρ
    have hρmem : ∀ i : ↥I, ρ i ∈ Λ.map barM := fun i =>
      ⟨⟨(i : G), hIY i.2⟩, Subgroup.mem_subgroupOf.2 i.2, rfl⟩
    have hρs : ∀ c ∈ Λ.map barM, ∃ i : ↥I, ρ i = c := by
      rintro _ ⟨z, hz, rfl⟩
      exact ⟨⟨(z : G), Subgroup.mem_subgroupOf.1 hz⟩, rfl⟩
    have hIsub : ((Λ.map barM).subgroupOf
        (centralizer ({barM s} : Set (TwoThin.barQ ↥(centralizer ({b} : Set G)))))).IsSubnormal :=
      CFSG.ComponentClassification.Components.mathlib_subnormal_of_chain
        (TwoThin.isTwoComponent_map_barMk hso hΛC hΛ2).1 Subgroup.IsSubnormal.top
    obtain ⟨E, hEK, hAE, -, hEel, hE4, -⟩ := h.exists_E
    obtain ⟨hxB0, -, -, hB0r⟩ := h.B_decomp ⟨hEK, hAE, hEel, hE4⟩
    set B₀ : Subgroup G := B ⊓ cSec K with hB₀
    have hB₀Y : B₀ ≤ centralizer ({b} : Set G) := fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.2 (hBc q (Subgroup.mem_inf.1 hq).1 b h.b_mem)
    have hB0el : CFSG.IsElementaryAbelian 2 ↥B₀ :=
      Th2Sig6.isElementaryAbelian_of_le hBel inf_le_left
    have hB0card : Nat.card ↥B₀ = 4 := by
      have h2 : Nat.card ↥B₀ = 2 ^ pRank 2 ↥B₀ := C3.Layer1.Back.card_eq_two_pow_pRank hB0el
      rw [h2, hB0r]
      norm_num
    have hinj : Function.Injective
        (barM.comp (B₀.subgroupOf (centralizer ({b} : Set G))).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
      intro z hz
      rw [MonoidHom.mem_ker] at hz
      have hq := Subgroup.mem_subgroupOf.1 z.2
      by_contra hz1
      have hq1 : ((z : ↥(centralizer ({b} : Set G))) : G) ≠ 1 := fun h1 => hz1 (by
        apply Subtype.ext
        apply Subtype.ext
        exact h1)
      have hsq : ((z : ↥(centralizer ({b} : Set G))) : G) ^ 2 = 1 := by
        rw [pow_two]
        exact hBsq _ (Subgroup.mem_inf.1 hq).1
      have hord : orderOf (z : ↥(centralizer ({b} : Set G))) = 2 := by
        apply orderOf_eq_prime
        · apply Subtype.ext
          simpa using hsq
        · intro h1
          exact hq1 (by rw [h1]; rfl)
      have h3 := TwoThin.orderOf_barMk hord
      have h4 : barM (z : ↥(centralizer ({b} : Set G))) = 1 := hz
      rw [h4, orderOf_one] at h3
      omega
    set D₀ : Subgroup (TwoThin.barQ ↥(centralizer ({b} : Set G))) :=
      (barM.comp (B₀.subgroupOf (centralizer ({b} : Set G))).subtype).range with hD₀
    have hD04 : Nat.card ↥D₀ = 4 := by
      rw [← S3Sec29BLayer.card_subgroupOf_of_le hB₀Y] at hB0card
      rw [← hB0card]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have hD₀mem : ∀ d ∈ D₀, ∃ (q : G) (hq : q ∈ B₀), d = barM ⟨q, hB₀Y hq⟩ := by
      rintro _ ⟨z, rfl⟩
      exact ⟨((z : ↥(centralizer ({b} : Set G))) : G), Subgroup.mem_subgroupOf.1 z.2, rfl⟩
    have hqI : ∀ q ∈ B₀, q ∈ cSec I := fun q hq =>
      S3Ctx29Layer.mem_cSec_pLayerOf (Subgroup.mem_inf.1 hq).2
        (hBc q (Subgroup.mem_inf.1 hq).1 b h.b_mem)
    refine S3Sec29B7AbsD.contra_main hxb2 hL hM hr hMsl hcase ρ (pPrimeCore 2 ↥I)
      (S3Sec29BDiag.ker_le_pPrimeCore hIY) (S3Sec29B7Cover.not_isSolvable_of_sl2 hSL)
      (Λ.map barM) hρmem hρs hcases hIsub D₀ hD04 ?_ ?_ ?_ ?_ ?_ ?_
    ·
      intro d hd
      obtain ⟨q, hq, rfl⟩ := hD₀mem d hd
      rw [← map_mul]
      have : (⟨q, hB₀Y hq⟩ : ↥(centralizer ({b} : Set G))) * ⟨q, hB₀Y hq⟩ = 1 :=
        Subtype.ext (hBsq q (Subgroup.mem_inf.1 hq).1)
      rw [this, map_one]
    ·
      exact ⟨⟨⟨x, hxb⟩, Subgroup.mem_subgroupOf.2 hxB0⟩, rfl⟩
    ·
      intro d hd i
      obtain ⟨q, hq, rfl⟩ := hD₀mem d hd
      have hmem : q * (i : G) * q⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 (hqI q hq).1 _).1 i.2
      refine ⟨⟨q * (i : G) * q⁻¹, hmem⟩, ?_⟩
      simp only [hρ, MonoidHom.comp_apply]
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    ·
      intro d hd n hn
      obtain ⟨q, hq, rfl⟩ := hD₀mem d hd
      have hnO : (n : G) ∈ pPrimeCoreOf 2 I := ⟨n, hn, rfl⟩
      have hmem : q * (n : G) * q⁻¹ ∈ pPrimeCoreOf 2 I :=
        (Subgroup.mem_normalizer_iff.1 (hqI q hq).2.1 _).1 hnO
      obtain ⟨n', hn', hn'eq⟩ := Subgroup.mem_map.1 hmem
      refine ⟨n', hn', ?_⟩
      simp only [hρ, MonoidHom.comp_apply]
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hn'eq.symm
    ·
      intro d hd i
      obtain ⟨q, hq, rfl⟩ := hD₀mem d hd
      by_cases hq1 : q = 1
      · subst hq1
        refine ⟨i, ?_, by simp⟩
        rw [show (⟨1, hB₀Y hq⟩ : ↥(centralizer ({b} : Set G))) = 1 from rfl, map_one, one_mul,
          mul_one]
      · have hq2 : orderOf q = 2 := by
          apply orderOf_eq_prime _ hq1
          rw [pow_two]
          exact hBsq q (Subgroup.mem_inf.1 hq).1
        obtain ⟨i', hi'c, hi'O⟩ := S3Sec29B7Cover.cover_of_mem_cSec (hqI q hq) hq2 i
        refine ⟨i', ?_, hi'O⟩
        simp only [hρ, MonoidHom.comp_apply]
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hi'c.symm
    ·
      intro d hd hdc
      obtain ⟨q, hq, rfl⟩ := hD₀mem d hd
      have hqC : q ∈ centralizer ({b} : Set G) := hB₀Y hq
      have hqJ : q ∈ cSec J := by
        refine TwoThin.mem_centralizerSection_of_map_eq hJ'.1 hJ'.2 hqC ?_
        intro m hm
        have hcm := hdc (barM m) ⟨m, hm, rfl⟩
        rw [map_mul, map_mul, map_inv, hcm, mul_assoc, mul_inv_cancel, mul_one]
      have hq1 : q ∈ B ⊓ cSec K ⊓ cSec J := Subgroup.mem_inf.2 ⟨hq, hqJ⟩
      rw [h295, Subgroup.mem_bot] at hq1
      subst hq1
      rw [show (⟨1, hB₀Y hq⟩ : ↥(centralizer ({b} : Set G))) = 1 from rfl, map_one]

end CFSG.GH74.Generic.BProg.B3
