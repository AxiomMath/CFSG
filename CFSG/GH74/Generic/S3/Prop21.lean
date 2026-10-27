module

public import CFSG.GH74.Generic.S3.Prop21Leaves
public import CFSG.GH74.Generic.S3.Lem610
public import CFSG.GH74.Generic.S3.LeavesFine

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open scoped MatrixGroups


section Prop21Glue

variable {G : Type} [Group G] [Finite G]

theorem config22_of_leaves (h1 : B_S3_lemma22_v1) (h2 : B_L3_fourgroup) (hG : GlobalHyp G)
    {t : StatedLieTag} {p f : ℕ} {v w : G} {Iv Iw Ivw P : Subgroup G}
    (hc : Conf2A G t p f v w Iv Iw Ivw P) :
    ∃ (V : Subgroup G) (v₁ : G), Config22 G t p f v w Iv Iw Ivw P V v₁ ∧ v₁ ∈ P ∧ v₁ ∈ Iw ∧ v₁ ∈ Ivw := by
  obtain ⟨v₁, hv₁P, hv₁Iw, hv₁Ivw, hv₁2, hv₁1, hv₁v⟩ := h1 G hG t p f v w Iv Iw Ivw P hc
  have hv2 : v * v = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hc.v_inv, pow_two] at this
  have hw2 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hc.w_inv, pow_two] at this
  have hv1 : v ≠ 1 := fun h => by
    have := hc.v_inv
    rw [h, orderOf_one] at this
    omega
  have hw1 : w ≠ 1 := fun h => by
    have := hc.w_inv
    rw [h, orderOf_one] at this
    omega
  have hvv₁ : v * v₁ = v₁ * v := (hc.v_central v₁ hv₁P).symm
  have hvw : v * w = w * v := hc.comm
  have hIwC : ∀ i ∈ Iw, i * w = w * i := fun i hi =>
    mem_centralizer_singleton_iff.1 (hc.comp_w.1.1 hi)
  have hv₁w : v₁ * w = w * v₁ := hIwC v₁ hv₁Iw
  have hvIw : v ∈ Iw := hc.le_w hc.v_mem
  have hwIw : w ∉ Iw := fun hw =>
    not_central_involution_of_odd hc.odd_w hw hw2 hw1 hIwC
  have hvv₁Iw : v * v₁ ∈ Iw := Iw.mul_mem hvIw hv₁Iw
  obtain ⟨V, hs, hv, hv₁, hmem⟩ := exists_count23Setup hv2 hv₁2 hvv₁ hv1 hv₁1 hv₁v.symm hw2 hvw hv₁w
    ⟨hw1, fun h => hwIw (h ▸ hvIw), fun h => hwIw (h ▸ hv₁Iw), fun h => hwIw (h ▸ hvv₁Iw)⟩
  have hVIw : V ≤ Iw := by
    intro a ha
    rcases (hmem a).1 ha with h | h | h | h <;> rw [h]
    · exact Iw.one_mem
    · exact hvIw
    · exact hv₁Iw
    · exact hvv₁Iw
  have hvIvw : v ∈ Ivw := hc.le_vw hc.v_mem
  have hVIvw : V ≤ Ivw := by
    intro a ha
    rcases (hmem a).1 ha with h | h | h | h <;> rw [h]
    · exact Ivw.one_mem
    · exact hvIvw
    · exact hv₁Ivw
    · exact Ivw.mul_mem hvIvw hv₁Ivw
  obtain ⟨g, hgI, hg_v, hg_v₁⟩ := h2 G t p f hc.tag hc.prime.1 hc.prime.2.1 hc.prime.2.2 Ivw
    hc.comp_vw.1.isQuasisimple hc.odd_vw hc.model_vw v v₁ hvIvw hv₁Ivw hv2 hv₁2 hvv₁ hv1 hv₁1
    hv₁v.symm
  obtain ⟨h, hhI, hh_v, hh_v₁⟩ := h2 G t p f hc.tag hc.prime.1 hc.prime.2.1 hc.prime.2.2 Iw
    hc.comp_w.1.isQuasisimple hc.odd_w hc.model_w v v₁ hvIw hv₁Iw hv2 hv₁2 hvv₁ hv1 hv₁1
    hv₁v.symm
  have hg_wv : g * (w * v) = (w * v) * g := by
    have := mem_centralizer_singleton_iff.1 (hc.comp_vw.1.1 hgI)
    rw [← hvw]; exact this
  have hh_w : h * w = w * h := hIwC h hhI
  obtain ⟨hconj, -, -⟩ := lemma22_elem hs hv hv₁ hv₁v.symm hg_v hg_v₁ hg_wv hh_v hh_v₁ hh_w
    hc.notConj_w
  exact ⟨V, v₁, ⟨hc, hs, hv, hv₁, hv₁v.symm, hVIw, hVIvw, hconj⟩, hv₁P, hv₁Iw, hv₁Ivw⟩

end Prop21Glue

section Prop21Glue2

variable {G : Type} [Group G] [Finite G]

theorem a3core_of_leaves (h3 : B_S3_layers) (hG : GlobalHyp G) {t : StatedLieTag} {p f : ℕ}
    {v w : G} {Iv Iw Ivw P V : Subgroup G} {v₁ : G} (hcfg : Config22 G t p f v w Iv Iw Ivw P V v₁)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hIv : Nonempty (SL(2, F) ≃* Iv)) :
    ∃ J₀ J₁ J₂ : Subgroup G, IsSL2Comp F w v J₀ ∧ IsSL2Comp F w v₁ J₁ ∧ IsSL2Comp F (w * v₁) v J₂ ∧
      J₀ = Iv ∧ J₀ ≠ J₂ ∧ (∀ a ∈ J₀, ∀ b ∈ J₂, a * b = b * a) ∧
      GLS.LU.IsCentralInvolutionIn v J₀ ∧ GLS.LU.IsCentralInvolutionIn v₁ J₁ ∧
      GLS.LU.IsCentralInvolutionIn v J₂ ∧ A3Reflection w v₁ ![J₀, J₁, J₂] := by
  obtain ⟨huniq, hD, hcomp⟩ := h3 G hG t p f v w Iv Iw Ivw P V v₁ hcfg F inferInstance inferInstance hF
  obtain ⟨J₀, J₁, J₂, hP₀, hP₁, hP₂, hne, hcomm, hc₀, hc₁, hc₂, hrefl, hu₀, -, -⟩ :=
    lemma23_A3 hcfg.setup huniq hD hcomp hcfg.hv hcfg.hv₁ hcfg.hne
  have hIvw : Iv ≤ centralizer ({w} : Set G) := fun i hi => hcfg.conf.comp_w.1.1 (hcfg.conf.le_w hi)
  have hIvC : IsSL2Comp F w v Iv :=
    IsSL2Comp.of_isCompC hcfg.conf.comp_v hIvw hcfg.conf.v_mem hIv
  exact ⟨J₀, J₁, J₂, hP₀, hP₁, hP₂, (hu₀ Iv hIvC).symm, hne, hcomm, hc₀, hc₁, hc₂, hrefl⟩

end Prop21Glue2

section Prop21Glue3

variable {G : Type} [Group G] [Finite G]

theorem mod4_of_leaves (h5 : B_S3_lemma24_25) (h6 : B_SL2_outAbelian) (h7 : B_S3_lemma26_transfer)
    (hG : GlobalHyp G) {t : StatedLieTag} {p f : ℕ} {v w : G} {Iv Iw Ivw P V : Subgroup G} {v₁ : G}
    (hcfg : Config22 G t p f v w Iv Iw Ivw P V v₁) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p ^ f) {J₀ J₁ J₂ : Subgroup G} (hJ₀ : IsSL2Comp F w v J₀)
    (hJ₁ : IsSL2Comp F w v₁ J₁) (hJ₂ : IsSL2Comp F (w * v₁) v J₂) (hJ₀Iv : J₀ = Iv)
    (hne : J₀ ≠ J₂) (hcomm : ∀ a ∈ J₀, ∀ b ∈ J₂, a * b = b * a) :
    (t = .PSL → p ^ f % 4 = 1) ∧ (t = .PSU → p ^ f % 4 = 3) := by
  have hc := hcfg.conf
  have hodd : p ^ f % 2 = 1 := Nat.odd_iff.1 ((hc.prime.1.odd_of_ne_two hc.prime.2.1).pow)
  by_cases hbad : (t = .PSL ∧ p ^ f % 4 = 3) ∨ (t = .PSU ∧ p ^ f % 4 = 1)
  · exfalso
    have hw2 : w * w = 1 := by
      have := pow_orderOf_eq_one w
      rwa [hc.w_inv, pow_two] at this
    have hv2 : v * v = 1 := by
      have := pow_orderOf_eq_one v
      rwa [hc.v_inv, pow_two] at this
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have hIwC : ∀ i ∈ Iw, i * w = w * i := fun i hi =>
      mem_centralizer_singleton_iff.1 (hc.comp_w.1.1 hi)
    have hodd2 : Odd (Nat.card ↥(centralizer (Iw : Set G) ⊓ centralizer (Ivw : Set G))) := by
      have hv1 : v ≠ 1 := fun h => by
        have := hc.v_inv
        rw [h, orderOf_one] at this
        omega
      have hw1 : w ≠ 1 := fun h => by
        have := hc.w_inv
        rw [h, orderOf_one] at this
        omega
      have hwv : w * v = v * w := hc.comm.symm
      have hIvwC : ∀ i ∈ Ivw, i * (w * v) = (w * v) * i := fun i hi => by
        rw [hwv]; exact mem_centralizer_singleton_iff.1 (hc.comp_vw.1.1 hi)
      have hQ := sylow_inf_centralizer hc.sylow_w hc.comp_w.le_normalizer
      have hQ' := sylow_inf_centralizer hc.sylow_vw hc.comp_vw.le_normalizer
      have hrk : NoCommInv (centralizer ({w} : Set G) ⊓ centralizer (Iw : Set G)) :=
        noCommInv_of_sylow hQ (noCommInv_of_cyclic hc.Q_cyc)
      have hcyc' : IsCyclic ↥(P ⊓ centralizer (Ivw : Set G)) := hc.Q_iso.some.isCyclic.1 hc.Q_cyc
      have hrk' : NoCommInv (centralizer ({w * v} : Set G) ⊓ centralizer (Ivw : Set G)) := by
        rw [hwv]
        exact noCommInv_of_sylow hQ' (noCommInv_of_cyclic hcyc')
      exact odd_card_inf_centralizer hw2 hv2 hwv hw1 hv1 hc.ne.symm hIwC hIvwC
        (hc.le_w hc.v_mem) (hc.le_vw hc.v_mem) hrk hrk'
    obtain ⟨X₁, hX₁c, hX₁ne, hXall, hX₁iso, hwX₁, hout⟩ :=
      h5 G hG t p f v w Iv Iw Ivw P V v₁ hcfg F inferInstance inferInstance hF J₀ J₁ J₂ hJ₀ hJ₁ hJ₂
        hJ₀Iv hne hcomm hodd2
    have hout' := hout hbad
    set C : Subgroup G := centralizer ({v} : Set G) with hCdef
    have hwC : w ∈ C := mem_centralizer_singleton_iff.2 hc.comm.symm
    have hX₁C : X₁ ≤ C := hX₁c.1
    have hIvC : Iv ≤ C := hc.comp_v.1
    let X₁' : Subgroup ↥C := X₁.subgroupOf C
    let X₂' : Subgroup ↥C := Iv.subgroupOf C
    let xw : ↥C := ⟨w, hwC⟩
    have hF2 : Odd (Nat.card F) := by
      rw [hF]; exact (hc.prime.1.odd_of_ne_two hc.prime.2.1).pow
    have hiso' : Nonempty (SL(2, F) ≃* ↥X₁') := by
      obtain ⟨e⟩ := hX₁iso
      exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe hX₁C).symm⟩
    have hN : commutator (MulAut ↥X₁') ≤ (MulAut.conj : ↥X₁' →* MulAut ↥X₁').range :=
      h6 F inferInstance inferInstance hF2 ↥X₁' inferInstance hiso'
    have hmemX₁' : ∀ y : ↥C, y ∈ X₁' ↔ (y : G) ∈ X₁ := fun y => Iff.rfl
    have hmemX₂' : ∀ y : ↥C, y ∈ X₂' ↔ (y : G) ∈ Iv := fun y => Iff.rfl
    have hx1 : xw ∈ normalizer (X₁' : Set ↥C) := by
      apply mem_normalizer_of_conj
      · intro y hy
        rw [hmemX₁'] at hy ⊢
        exact hwX₁ _ hy
      · intro y hy
        rw [hmemX₁'] at hy ⊢
        have e : ((xw⁻¹ * y * xw : ↥C) : G) = w * (y : G) * w⁻¹ := by
          show (w⁻¹ * (y : G) * w) = w * (y : G) * w⁻¹
          rw [hwinv]
        rw [e]
        exact hwX₁ _ hy
    have hx₂ : ∀ y ∈ X₂', y * xw = xw * y := by
      intro y hy
      apply Subtype.ext
      exact hIwC _ (hc.le_w ((hmemX₂' y).1 hy))
    have hconj : ∀ c : ↥C, c ∈ normalizer (X₁' : Set ↥C) ∨ ∀ y ∈ X₁', c * y * c⁻¹ ∈ X₂' := by
      intro c
      have hcv : (c : G) * v = v * (c : G) := mem_centralizer_singleton_iff.1 c.2
      have hJ : IsCompC (X₁.map (MulAut.conj (c : G)).toMonoidHom) v := by
        have := hX₁c.map_conj (c : G)
        have e : (c : G) * v * (c : G)⁻¹ = v := by rw [hcv]; group
        rwa [e] at this
      have hmapmem : ∀ y ∈ X₁, (c : G) * y * (c : G)⁻¹ ∈ X₁.map (MulAut.conj (c : G)).toMonoidHom :=
        fun y hy => ⟨y, hy, by simp⟩
      rcases hXall _ hJ with hJIv | hJX₁
      · right
        intro y hy
        rw [hmemX₁'] at hy
        rw [hmemX₂']
        have := hmapmem _ hy
        rw [hJIv] at this
        exact this
      · left
        apply mem_normalizer_of_conj
        · intro y hy
          rw [hmemX₁'] at hy ⊢
          have := hmapmem _ hy
          rw [hJX₁] at this
          exact this
        · intro y hy
          rw [hmemX₁'] at hy ⊢
          rw [← hJX₁] at hy
          obtain ⟨j, hj, hjy⟩ := hy
          have hjy' : (c : G) * j * (c : G)⁻¹ = y := by simpa using hjy
          have e : ((c⁻¹ * y * c : ↥C) : G) = j := by
            show (c : G)⁻¹ * y * (c : G) = j
            rw [← hjy']; group
          rw [e]
          exact hj
    have hx₁ : X₁'.normalizerMonoidHom ⟨xw, hx1⟩ ∉ (MulAut.conj : ↥X₁' →* MulAut ↥X₁').range := by
      rintro ⟨x₀', hx₀'⟩
      apply hout'
      refine ⟨((x₀' : ↥C) : G), (hmemX₁' _).1 x₀'.2, fun y hy => ?_⟩
      let y' : ↥X₁' := ⟨⟨y, hX₁C hy⟩, hy⟩
      have h1 := congrArg (fun z : ↥X₁' => ((z : ↥C) : G)) (DFunLike.congr_fun hx₀' y')
      simpa using h1.symm
    have hmain : xw ∉ commutator ↥C :=
      not_mem_commutator_of_normalizer_or_conj_le X₁' X₂' _ hN xw hx1 hx₂ hconj hx₁
    obtain ⟨hw', hcomm'⟩ := h7 G hG t p f v w Iv Iw Ivw P hc
    exact hmain hcomm'
  · constructor
    · intro ht
      by_contra h
      apply hbad
      left
      exact ⟨ht, by omega⟩
    · intro ht
      by_contra h
      apply hbad
      right
      exact ⟨ht, by omega⟩

end Prop21Glue3

section Prop21Final

variable {G : Type} [Group G] [Finite G]

theorem b_S3_prop21_lin_of_leaves (h1 : B_S3_lemma22_v1) (h2 : B_L3_fourgroup) (h3 : B_S3_layers)
    (h4 : B_S3_sl3pair_lin) (h5 : B_S3_lemma24_25) (h6 : B_SL2_outAbelian)
    (h7 : B_S3_lemma26_transfer) : B_S3_prop21_lin := by
  intro G _ _ hG p f v w Iv Iw Ivw P hc
  obtain ⟨V, v₁, hcfg, -, -, -⟩ := config22_of_leaves h1 h2 hG hc
  obtain ⟨F, hFf, hFfin, hFc, hFiso⟩ := hc.iso_v
  obtain ⟨J₀, J₁, J₂, hP₀, hP₁, hP₂, hJ₀Iv, hne, hcomm, hc₀, hc₁, hc₂, hrefl⟩ :=
    a3core_of_leaves h3 hG hcfg hFc hFiso
  have hmod := mod4_of_leaves h5 h6 h7 hG hcfg hFc hP₀ hP₁ hP₂ hJ₀Iv hne hcomm
  obtain ⟨hJ₀J₁, hα₁, hα₂⟩ :=
    h4 G hG p f v w Iv Iw Ivw P V v₁ hcfg F hFf hFfin hFc J₀ J₁ J₂ hP₀ hP₁ hP₂
  have hvv₁ : v * v₁ = v₁ * v := hcfg.setup.V_comm v hcfg.hv.1 v₁ hcfg.hv₁.1
  refine ⟨F, hFf, hFfin, v, v₁, ![J₀, J₁, J₂], hFc, hmod.1 rfl, ?_, rfl, hJ₀Iv, hJ₀J₁, hrefl⟩
  refine ⟨fun i => ?_, hc₀, hc₂, hc₁, hcfg.hne, hvv₁, hcomm, hα₁, hα₂⟩
  fin_cases i
  · exact hP₀.iso
  · exact hP₁.iso
  · exact hP₂.iso

theorem b_S3_prop21_uni_of_leaves (h1 : B_S3_lemma22_v1) (h2 : B_L3_fourgroup) (h3 : B_S3_layers)
    (h4 : B_S3_sl3pair_uni) (h5 : B_S3_lemma24_25) (h6 : B_SL2_outAbelian)
    (h7 : B_S3_lemma26_transfer) : B_S3_prop21_uni := by
  intro G _ _ hG p f v w Iv Iw Ivw P hc
  obtain ⟨V, v₁, hcfg, -, -, -⟩ := config22_of_leaves h1 h2 hG hc
  obtain ⟨F, hFf, hFfin, hFc, hFiso⟩ := hc.iso_v
  obtain ⟨J₀, J₁, J₂, hP₀, hP₁, hP₂, hJ₀Iv, hne, hcomm, hc₀, hc₁, hc₂, hrefl⟩ :=
    a3core_of_leaves h3 hG hcfg hFc hFiso
  have hmod := mod4_of_leaves h5 h6 h7 hG hcfg hFc hP₀ hP₁ hP₂ hJ₀Iv hne hcomm
  obtain ⟨hJ₀J₁, F₂, hF₂f, hF₂fin, hF₂c, hα₁, hα₂⟩ :=
    h4 G hG p f v w Iv Iw Ivw P V v₁ hcfg F hFf hFfin hFc J₀ J₁ J₂ hP₀ hP₁ hP₂
  have hvv₁ : v * v₁ = v₁ * v := hcfg.setup.V_comm v hcfg.hv.1 v₁ hcfg.hv₁.1
  refine ⟨F₂, F, hF₂f, hF₂fin, hFf, hFfin, v, v₁, ![J₀, J₁, J₂], hF₂c, hFc, hmod.2 rfl, ?_, rfl,
    hJ₀Iv, hJ₀J₁, hrefl⟩
  refine ⟨fun i => ?_, hc₀, hc₂, hc₁, hcfg.hne, hvv₁, hcomm, hα₁, hα₂⟩
  fin_cases i
  · exact hP₀.iso
  · exact hP₁.iso
  · exact hP₂.iso

end Prop21Final

end CFSG.GH74.Generic.S3
