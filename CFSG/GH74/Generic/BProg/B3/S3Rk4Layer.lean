module

public import CFSG.GH74.Generic.BProg.B3.S3Rk4Basic
public import CFSG.GH74.Generic.BProg.B3.S3Pump306bc
public import CFSG.GH74.Generic.BProg.B3.S3Obs32Conj
public import CFSG.GH74.Generic.S3.LyDiagA
public import CFSG.GH74.Generic.S1.SL2Facts

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S3Rk4Layer

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.S45 CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  Subgroup

variable {G : Type} [Group G] [Finite G] {x y : G} {K A : Subgroup G}

theorem x_mem_cSec (h : Setup30 G x K A y) {H : Subgroup G}
    (hH : IsPCompIn 2 (centralizer ({y} : Set G)) H)
    (hbar : barSub y H = barSub y (Ly K y)) : x ∈ centralizerSection H (pPrimeCoreOf 2 H) := by
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := S3L3Facts.pcomp h
  have hKC : K ≤ centralizer ({x} : Set G) := hK.1
  have hLK : Ly K y ≤ K := ((Setup30.layer h).1.1).trans inf_le_left
  have hyC : y ∈ centralizer ({x} : Set G) := hKC (S3L3Facts.y_mem_K h)
  have hxC : x ∈ centralizer ({y} : Set G) := TwoThin.mem_centralizer_symm hyC
  refine ObsPump.mem_cSec_of_bar_comm hH hxC (fun l hl => ?_)
  have hl' : l ∈ barSub y (Ly K y) := hbar ▸ hl
  obtain ⟨g, hg, hgL, rfl⟩ := mem_barSub.1 hl'
  have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.1 (hKC (hLK hgL))
  show proj y ⟨x, hxC⟩ * proj y ⟨g, hg⟩ = proj y ⟨g, hg⟩ * proj y ⟨x, hxC⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hgx.symm

theorem mem_normalizer_pumpUp (h : Setup30 G x K A y)
    (hH : IsPCompIn 2 (centralizer ({y} : Set G)) (pumpUp 2 (Ly K y) y))
    (hbar : barSub y (pumpUp 2 (Ly K y) y) = barSub y (Ly K y)) {t : G}
    (hty : t ∈ centralizer ({y} : Set G)) (htx : t * x = x * t) :
    t ∈ normalizer ((pumpUp 2 (Ly K y) y : Subgroup G) : Set G) := by
  set H : Subgroup G := pumpUp 2 (Ly K y) y
  have hxH : x ∈ centralizerSection H (pPrimeCoreOf 2 H) := x_mem_cSec h hH hbar
  have hH₁ : IsPCompIn 2 (centralizer ({y} : Set G)) (H.map (MulAut.conj t).toMonoidHom) :=
    FalseCtxS45Comp.isPCompIn_conj hH hty
  have hEq : H.map (MulAut.conj t).toMonoidHom = H := by
    by_contra hne
    have h1 : t * x * t⁻¹ ∈ centralizerSection (H.map (MulAut.conj t).toMonoidHom)
        (pPrimeCoreOf 2 (H.map (MulAut.conj t).toMonoidHom)) :=
      (S3Obs32Conj.mem_cSec_map_conj_iff t x H).2 hxH
    have h2 : t * x * t⁻¹ = x := by rw [htx]; group
    rw [h2] at h1
    exact (prop306bc h hH₁ hne).2.2.1 h1
  exact Subgroup.mem_normalizer_iff_map_conj_eq.2 hEq

theorem sl2_unique_invol {Lq : Type} [Group Lq] (hL : HasSL2Model Lq (fun q => Odd q ∧ 5 ≤ q))
    {u v : Lq} (hu : u * u = 1) (hv : v * v = 1) (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u = v := by
  obtain ⟨F, hF, hFin, hP, ⟨e⟩⟩ := hL
  have hV : HasSL2Model ↥(⊤ : Subgroup Lq) (fun q' => q' = Nat.card F) :=
    ⟨F, hF, hFin, rfl, ⟨Subgroup.topEquiv.trans e⟩⟩
  obtain ⟨t, -, -, huniq, -⟩ := S1.sl2_involution_facts (X := Lq) (V := ⊤) (q := Nat.card F) hP.1 hV
  rcases huniq u (Subgroup.mem_top u) hu with h1 | h1
  · exact absurd h1 hu1
  rcases huniq v (Subgroup.mem_top v) hv with h2 | h2
  · exact absurd h2 hv1
  exact h1.trans h2.symm

theorem pRank_barSub_le_one (h : Setup30 G x K A y) :
    CFSG.pRank 2 ↥(barSub y (Ly K y)) ≤ 1 := by
  classical
  by_contra hcon
  have h2 : 2 ≤ CFSG.pRank 2 ↥(barSub y (Ly K y)) := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL : IsPCompIn 2 (K ⊓ centralizer ({y} : Set G)) (Ly K y) := (Setup30.layer h).1
  have hLC : Ly K y ≤ centralizer ({y} : Set G) := hL.1.trans inf_le_right
  let φ : ↥(Ly K y) →* CentralizerBar y := (proj y).comp (Subgroup.inclusion hLC)
  have hφr : φ.range = barSub y (Ly K y) := by
    ext b
    constructor
    · rintro ⟨l, rfl⟩
      exact proj_mem_barSub (hLC l.2) l.2
    · intro hb
      obtain ⟨g, hg, hgL, rfl⟩ := mem_barSub.1 hb
      exact ⟨⟨g, hgL⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have hodd : Odd (Nat.card φ.ker) := by
      refine S45.odd_card_of_forall_odd_orderOf (Q := φ.ker) fun q hq => ?_
      have h1 := proj_odd y ⟨q.1, hLC q.2⟩ hq
      have hord : orderOf (Subgroup.inclusion hLC q) = orderOf q :=
        orderOf_injective _ (Subgroup.inclusion_injective _) q
      rw [← hord]
      exact h1
    exact Nat.not_even_iff_odd.2 hodd ∘ even_iff_two_dvd.2
  have e1 := S3Rk4Basic.pRank_range_eq φ hφk
  rw [hφr] at e1
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(Ly K y))) := CFSG.pPrimeCore_coprime_card
  have hN : ¬ 2 ∣ Nat.card (pPrimeCore 2 ↥(Ly K y)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop
  have e2 := CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two
    (pPrimeCore 2 ↥(Ly K y)) hN
  obtain ⟨u, v, hu, hv, hu1, hv1, huv, -⟩ :=
    S3Rk4Basic.exists_two_invol (P := ↥(Ly K y) ⧸ pPrimeCore 2 ↥(Ly K y)) (by omega)
  exact huv (sl2_unique_invol (Setup30.layer h).2.2 hu hv hu1 hv1)

theorem not_bar_le (h : Setup30 G x K A y) {H Λ : Subgroup G}
    (hbar : barSub y H = barSub y (Ly K y)) (hΛy : Λ ≤ centralizer ({y} : Set G)) {a b : G}
    (ha : a ∈ Λ) (hb : b ∈ Λ) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) (hcomm : a * b = b * a) : ¬ barSub y Λ ≤ barSub y H := by
  intro hle
  have haC : a ∈ centralizer ({y} : Set G) := hΛy ha
  have hbC : b ∈ centralizer ({y} : Set G) := hΛy hb
  set pa : CentralizerBar y := proj y ⟨a, haC⟩ with hpa
  set pb : CentralizerBar y := proj y ⟨b, hbC⟩ with hpb
  have hmem : ∀ {c : G} (hc : c ∈ centralizer ({y} : Set G)), c ∈ Λ →
      proj y ⟨c, hc⟩ ∈ barSub y (Ly K y) := fun {c} hc hcΛ =>
    hbar ▸ hle (proj_mem_barSub hc hcΛ)
  have hpa2 : pa * pa = 1 := by
    rw [hpa, ← map_mul]
    have : (⟨a, haC⟩ * ⟨a, haC⟩ : ↥(centralizer ({y} : Set G))) = 1 := Subtype.ext ha2
    rw [this, map_one]
  have hpb2 : pb * pb = 1 := by
    rw [hpb, ← map_mul]
    have : (⟨b, hbC⟩ * ⟨b, hbC⟩ : ↥(centralizer ({y} : Set G))) = 1 := Subtype.ext hb2
    rw [this, map_one]
  have hpa1 : pa ≠ 1 := fun e => ha1 (eq_one_of_proj_eq_one_of_sq haC e ha2)
  have hpb1 : pb ≠ 1 := fun e => hb1 (eq_one_of_proj_eq_one_of_sq hbC e hb2)
  have hcomm' : pa * pb = pb * pa := by
    rw [hpa, hpb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  have hne : pa ≠ pb := by
    intro e
    have hab2 : (a * b) * (a * b) = 1 := by
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hcomm]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha2, hb2, one_mul]
    have habC : a * b ∈ centralizer ({y} : Set G) := (centralizer ({y} : Set G)).mul_mem haC hbC
    have h1 : proj y ⟨a * b, habC⟩ = 1 := by
      have : (⟨a * b, habC⟩ : ↥(centralizer ({y} : Set G))) = ⟨a, haC⟩ * ⟨b, hbC⟩ := rfl
      rw [this, map_mul, ← hpa, ← hpb, ← e, hpa2]
    have hab1 : a * b = 1 := eq_one_of_proj_eq_one_of_sq habC h1 hab2
    exact hab (mul_left_cancel (hab1.trans ha2.symm)).symm
  have hPrank : 2 ≤ CFSG.pRank 2 ↥(barSub y (Ly K y)) :=
    S3OuterCore.two_le_pRank_of_invols (P := ↥(barSub y (Ly K y)))
      (a := ⟨pa, hmem haC ha⟩) (b := ⟨pb, hmem hbC hb⟩) (Subtype.ext hcomm')
      (Subtype.ext hpa2) (Subtype.ext hpb2) (fun e => hpa1 (congrArg Subtype.val e))
      (fun e => hpb1 (congrArg Subtype.val e)) (fun e => hne (congrArg Subtype.val e))
  have := pRank_barSub_le_one h
  omega

theorem le_cSec_of_stable (hG : Gen4 G) {t : G} (hty : t ∈ centralizer ({y} : Set G))
    (ht : orderOf t = 2) {H Λ : Subgroup G} (hH : IsPCompIn 2 (centralizer ({y} : Set G)) H)
    (htH : t ∈ normalizer (H : Set G))
    (hΛ : IsPCompIn 2 (centralizer ({t} : Set G) ⊓ centralizer ({y} : Set G)) Λ)
    (hnot : ¬ barSub y Λ ≤ barSub y H) : Λ ≤ centralizerSection H (pPrimeCoreOf 2 H) := by
  classical
  set Y' : Subgroup G := centralizer ({y} : Set G)
  have hso : orderOf (⟨t, hty⟩ : ↥Y') = 2 := TwoThin.orderOf_mk_centralizer hty ht
  have hΛC := TwoThin.le_centralizer_mk (isPCompIn_two_iff.mp hΛ).1 hty
  have hΛ2 := TwoThin.isTwoComponent_centralizer_mk hΛ hty
  obtain ⟨-, -, L, hL, hcases, -⟩ := TwoThin.pumpupY_structure hso hΛC hΛ2
  have hHb : CFSG.IsComponent (PumpCalc.bar y H) := PumpCalc.isComponent_bar hH
  have hstab := PumpCalc.map_conj_bar_of_normalizes (u := y) (X := H) hty htH
  have hs2 : orderOf (PumpCalc.sbar t hty) = 2 := PumpCalc.orderOf_sbar ht hty
  have hsinv : (barMk ↥Y' ⟨t, hty⟩)⁻¹ = barMk ↥Y' ⟨t, hty⟩ :=
    inv_eq_self_of_orderOf_eq_two hs2
  rcases hcases with ⟨-, hΛL⟩ | ⟨hne, -, -⟩
  ·
    rcases CFSG.LocalCores.distinct_components_commute hL hHb with hLH | hcomm
    · have hΛH : PumpCalc.bar y Λ ≤ PumpCalc.bar y H := hΛL.trans hLH.le
      exact absurd hΛH hnot
    · intro g hg
      have hgC : g ∈ Y' := (Subgroup.mem_inf.1 (hΛ.1 hg)).2
      refine ObsPump.mem_cSec_of_bar_comm hH hgC (fun l hl => ?_)
      have hgL : barMk ↥Y' ⟨g, hgC⟩ ∈ L :=
        hΛL ⟨⟨g, hgC⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
      exact S3Pump306.comm_of_commutator_eq_bot hcomm _ hgL l hl
  ·
    exfalso
    have hs := S3.eq_or_eq_conj_of_gen4 (gen4_barQ hG y) hL hne hHb
    have hHL : PumpCalc.bar y H = L := by
      rcases hs with h1 | h1
      · exact h1
      · rw [hsinv] at h1
        have h2 : conjSub (barMk ↥Y' ⟨t, hty⟩) (conjSub (barMk ↥Y' ⟨t, hty⟩) L) = L := by
          have := conjSub_conjSub_of_inv_eq hsinv L
          rwa [hsinv] at this
        have h3 : (conjSub (barMk ↥Y' ⟨t, hty⟩) L).map
            (MulAut.conj (PumpCalc.sbar t hty)).toMonoidHom = conjSub (barMk ↥Y' ⟨t, hty⟩) L := by
          rw [← h1]
          exact hstab
        exact (h1.trans (h3.symm.trans h2))
    apply hne
    rw [hsinv, ← hHL]
    exact hstab

end S3Rk4Layer

end CFSG.GH74.Generic.BProg.B3
