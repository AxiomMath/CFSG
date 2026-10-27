module

public import CFSG.GH74.Generic.S3.NbrR
public import CFSG.GH74.Generic.S3.L3Class
public import CFSG.GH74.Generic.BProg.B1.PilotS3Facts
public import CFSG.GH74.Generic.BProg.B1.Lift1

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_four_mem_of_nbrData {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}
    (h : S3.NbrData G t p f x y Iw Iv) :
    ∃ E : Subgroup G, E ≤ Iw ∧ y ∈ E ∧ CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIwq : IsQuasisimple ↥Iw := h.comp_w.1.isQuasisimple
  have hyIw : y ∈ Iw := h.Iv_le h.y_Iv
  have h2 := CFSG.LocalAnalysis.ComponentInitial.two_le_pRank_of_isQuasisimple_of_odd_center hIwq h.odd_w
  obtain ⟨A, hAab, hAcard⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_four_group_of_two_le_pRank h2
  have hAel : CFSG.IsElementaryAbelian 2 ↥A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 2 A).2 hAab
  have hAnt : Nontrivial ↥A := Finite.one_lt_card_iff_nontrivial.1 (by rw [hAcard]; norm_num)
  obtain ⟨a, ha1⟩ := exists_ne (1 : ↥A)
  have ha2 : (a : ↥Iw) ^ 2 = 1 := hAab.2 (a : ↥Iw) a.2
  have ha1' : ((a : ↥Iw) : G) ≠ 1 := fun hh => ha1 (Subtype.ext (Subtype.ext hh))
  have haa : ((a : ↥Iw) : G) * ((a : ↥Iw) : G) = 1 := by
    have := congrArg Subtype.val ha2
    simpa [pow_two] using this
  have hy2' : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [h.y_inv, pow_two] at this
  have hy1 : y ≠ 1 := by
    intro hh
    have := h.y_inv
    rw [hh, orderOf_one] at this
    omega
  obtain ⟨g, hgIw, hg⟩ := S3.b_L3_class G t p f h.tag h.prime.1 h.prime.2.1 h.prime.2.2 Iw hIwq
    h.odd_w h.model_w _ (a : ↥Iw).2 y hyIw haa ha1' hy2' hy1
  let φ : ↥Iw →* G := (MulAut.conj g).toMonoidHom.comp Iw.subtype
  have hφ : Function.Injective φ := (MulAut.conj g).injective.comp Subtype.val_injective
  have hφapp : ∀ z : ↥Iw, φ z = g * (z : G) * g⁻¹ := fun z => rfl
  refine ⟨A.map φ, ?_, ?_, CFSG.IsElementaryAbelian.map φ, ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    rw [hφapp]
    exact Iw.mul_mem (Iw.mul_mem hgIw z.2) (Iw.inv_mem hgIw)
  · exact ⟨(a : ↥Iw), a.2, by rw [hφapp]; exact hg⟩
  · rw [Subgroup.card_map_of_injective hφ, hAcard]

theorem imgBar_Iv_eq_split3 {F : Type} [Field F] [Finite F] {t : StatedLieTag} {p f : ℕ} {x y : G}
    {Iw Iv : Subgroup G} (h : S3.NbrData G t p f x y Iw Iv) {L : Subgroup (CentralizerBar x)}
    (_hLY : L ≤ S3.imgBar x Iw)
    (hL : B1.PilotS3.IsSplit3 F (bar x y) L
      (centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ S3.imgBar x Iw)) :
    S3.imgBar x Iv = L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIwC : Iw ≤ centralizer ({x} : Set G) := h.comp_w.1.1
  have hyIw : y ∈ Iw := h.Iv_le h.y_Iv
  have hyC : y ∈ centralizer ({x} : Set G) := hIwC hyIw
  have hbar : bar x y = proj x ⟨y, hyC⟩ := bar_of_mem hyC
  have hy2' : y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [h.y_inv, pow_two] at this
  have hy1 : y ≠ 1 := by
    intro hh
    have := h.y_inv
    rw [hh, orderOf_one] at this
    omega
  obtain ⟨F₀, hF₀f, hF₀fin, hF₀, ⟨e⟩⟩ := h.Iv_iso
  have hoddF₀ : Odd (Nat.card F₀) := by
    rw [hF₀]; exact (h.prime.1.odd_of_ne_two h.prime.2.1).pow
  have hIvc : ∀ i ∈ Iv, i * y = y * i :=
    S3.central_of_involution_of_equiv_sl2 hoddF₀ e h.y_Iv hy2' hy1
  have hIvq : IsQuasisimple ↥Iv :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e
      (CFSG.GH74.KGroups.L3Eps.isQuasisimple_sl2c (by rw [hF₀]; have := h.prime.2.2; omega))
  have hIvC : Iv ≤ centralizer ({x} : Set G) := h.Iv_le.trans hIwC
  have hNperf : ⁅S3.imgBar x Iv, S3.imgBar x Iv⁆ = S3.imgBar x Iv := by
    have hq' : IsQuasisimple ↥(Iv.subgroupOf (centralizer ({x} : Set G))) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hIvC).symm hIvq
    have hp' : ⁅Iv.subgroupOf (centralizer ({x} : Set G)), Iv.subgroupOf (centralizer ({x} : Set G))⁆ =
        Iv.subgroupOf (centralizer ({x} : Set G)) := Subgroup.isPerfect_iff.mp hq'.1
    unfold S3.imgBar
    rw [← Subgroup.map_commutator, hp']
  have hNcent : S3.imgBar x Iv ≤ centralizer ({bar x y} : Set (CentralizerBar x)) := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := S3.mem_imgBar.1 hn
    rw [Subgroup.mem_centralizer_singleton_iff, hbar, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hIvc _ hi)
  have hNH : S3.imgBar x Iv ≤ centralizer ({bar x y} : Set (CentralizerBar x)) ⊓ S3.imgBar x Iw :=
    le_inf hNcent (S3.imgBar_mono x h.Iv_le)
  have hNL : S3.imgBar x Iv ≤ L := hL.le_of_perfect' hNH hNperf
  have key : ∀ c : CentralizerBar x, c ∈ S3.imgBar x Iw → c * bar x y = bar x y * c →
      ∀ n ∈ S3.imgBar x Iv, c * n * c⁻¹ ∈ S3.imgBar x Iv := by
    intro c hc hcy n hn
    obtain ⟨g₀, hg₀, rfl⟩ := S3.mem_imgBar.1 hc
    have hNkodd : Odd (Nat.card (B1.projRes hIwC).ker) :=
      Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (B1.not_two_dvd_card_ker_projRes hIwC))
    let y' : ↥Iw := ⟨y, hyIw⟩
    have hy'2 : orderOf y' = 2 := by rw [Subgroup.orderOf_mk]; exact h.y_inv
    let g₀' : ↥Iw := ⟨(g₀ : G), hg₀⟩
    have hprojy : B1.projRes hIwC y' = bar x y := by
      rw [B1.projRes_apply, hbar]
    have hprojg : B1.projRes hIwC g₀' = proj x g₀ := rfl
    obtain ⟨g, hgc, hgy⟩ := B1.centralizer_quotient_of_pGroup (B1.projRes hIwC).ker hNkodd
      (A := zpowers y') (B1.isPGroup_two_zpowers_of_orderOf hy'2)
      (c := QuotientGroup.mk' (B1.projRes hIwC).ker g₀') (by
        intro a ha
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
        rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
          MonoidHom.mem_ker]
        simp only [map_mul, map_inv, map_zpow, hprojy, hprojg]
        rw [inv_mul_eq_one]
        exact (Commute.zpow_left (show Commute (bar x y) (proj x g₀) from hcy.symm) k).eq)
    have hgy' : (g : G) * y = y * (g : G) :=
      congrArg Subtype.val (hgy y' (Subgroup.mem_zpowers y')).symm
    have hgproj : proj x ⟨(g : G), hIwC g.2⟩ = proj x g₀ := by
      have h1 : g⁻¹ * g₀' ∈ (B1.projRes hIwC).ker := by
        have := hgc
        rwa [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
      rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h1
      exact h1.trans hprojg
    obtain ⟨i, hi, rfl⟩ := S3.mem_imgBar.1 hn
    have hnorm : (g : G) * (i : G) * (g : G)⁻¹ ∈ Iv := h.Iv_norm (g : G) g.2 hgy' (i : G) hi
    let gC : ↥(centralizer ({x} : Set G)) := ⟨(g : G), hIwC g.2⟩
    refine S3.mem_imgBar.2 ⟨gC * i * gC⁻¹, hnorm, ?_⟩
    have hgcproj : proj x gC = proj x g₀ := hgproj
    rw [map_mul, map_mul, map_inv, hgcproj]
  have hNn : ((S3.imgBar x Iv).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : CentralizerBar x) ∈ S3.imgBar x Iv := hn
    have hgH := hL.le_H g.2
    have hcy : (g : CentralizerBar x) * bar x y = bar x y * (g : CentralizerBar x) :=
      Subgroup.mem_centralizer_singleton_iff.1 hgH.1
    show (g : CentralizerBar x) * (n : CentralizerBar x) * (g : CentralizerBar x)⁻¹ ∈ S3.imgBar x Iv
    exact key g hgH.2 hcy n hn'
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hL.quasisimple hNn with
    htop | hcen
  · refine le_antisymm hNL fun l hl => ?_
    have : (⟨l, hl⟩ : ↥L) ∈ (S3.imgBar x Iv).subgroupOf L := by rw [htop]; trivial
    exact this
  · exfalso
    have hbot : ⁅S3.imgBar x Iv, S3.imgBar x Iv⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      have h1 := Subgroup.mem_center_iff.1
        (hcen (show (⟨a, hNL ha⟩ : ↥L) ∈ (S3.imgBar x Iv).subgroupOf L from ha)) ⟨b, hNL hb⟩
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 (congrArg Subtype.val h1.symm)
    have hyN : bar x y ∈ S3.imgBar x Iv := by
      rw [hbar]
      exact S3.mem_imgBar.2 ⟨⟨y, hyC⟩, h.y_Iv, rfl⟩
    rw [hNperf] at hbot
    rw [hbot, Subgroup.mem_bot] at hyN
    have hne : bar x y ≠ 1 := by
      intro hh
      have hodd := proj_odd x ⟨y, hyC⟩ (by rw [← hbar]; exact hh)
      rw [Subgroup.orderOf_mk, h.y_inv] at hodd
      exact absurd hodd (by decide)
    exact hne hyN

end CFSG.GH74.Generic.BProg.B3
