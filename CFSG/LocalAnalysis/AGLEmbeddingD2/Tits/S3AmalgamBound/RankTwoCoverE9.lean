module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2PairStrong3Irr
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.RankTwoCoverLift

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC
open scoped commutatorElement

theorem three_dvd_of_pow_mul_pow_eq_one {X : Type*} [Group X] {U V : X} (hU : orderOf U = 3)
    (hV : orderOf V = 3) (hnot : V ∉ Subgroup.zpowers U) {a b : ℕ} (h : U ^ a * V ^ b = 1) :
    3 ∣ a ∧ 3 ∣ b := by
  have hU3 : U ^ 3 = 1 := hU ▸ pow_orderOf_eq_one U
  have hV3 : V ^ 3 = 1 := hV ▸ pow_orderOf_eq_one V
  have hVb : V ^ b = (U ^ a)⁻¹ := eq_inv_of_mul_eq_one_right h
  have hb : 3 ∣ b := by
    by_contra hb
    have hb' : b % 3 = 1 ∨ b % 3 = 2 := by omega
    rcases hb' with h1 | h1
    · apply hnot
      have : V = (U ^ a)⁻¹ := by rw [← hVb, pow_eq_pow_mod b hV3, h1, pow_one]
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers U) a)
    · apply hnot
      have h2 : V ^ b = V⁻¹ := by
        rw [pow_eq_pow_mod b hV3, h1]
        exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hV3)
      have : V = U ^ a := by
        have := hVb ▸ h2
        simpa using congrArg (fun x => x⁻¹) this.symm
      rw [this]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers U) a
  have hVb1 : V ^ b = 1 := orderOf_dvd_iff_pow_eq_one.1 (hV ▸ hb)
  refine ⟨?_, hb⟩
  rw [hVb1, mul_one] at h
  exact hU ▸ orderOf_dvd_of_pow_eq_one h

theorem exists_aut_of_liftable_pair {W : Type} [Group W] [Finite W] {L A : Subgroup W}
    (hL : IsComponentOf L ⊤)
    (hA : ∀ E : Subgroup W, E ≤ A ⊓ L → IsElemAbelian 3 E → Nat.card E = 9 →
      TransitiveOnNonidentity (Subgroup.normalizer (E : Set W)) E)
    {ai bi aj bj : ↥L} (hai : (ai : W) ∈ A) (hbi : (bi : W) ∈ A) (haj : (aj : W) ∈ A)
    (hbj : (bj : W) ∈ A)
    (hai2 : (QuotientGroup.mk' (Subgroup.center ↥L) ai) ^ 2 = 1)
    (hbi2 : (QuotientGroup.mk' (Subgroup.center ↥L) bi) ^ 2 = 1)
    (haj2 : (QuotientGroup.mk' (Subgroup.center ↥L) aj) ^ 2 = 1)
    (hbj2 : (QuotientGroup.mk' (Subgroup.center ↥L) bj) ^ 2 = 1)
    (hui : orderOf (QuotientGroup.mk' (Subgroup.center ↥L) (ai * bi)) = 3)
    (huj : orderOf (QuotientGroup.mk' (Subgroup.center ↥L) (aj * bj)) = 3)
    (hcomm : Commute (QuotientGroup.mk' (Subgroup.center ↥L) (ai * bi))
      (QuotientGroup.mk' (Subgroup.center ↥L) (aj * bj)))
    (hbcomm : Commute (QuotientGroup.mk' (Subgroup.center ↥L) bj)
      (QuotientGroup.mk' (Subgroup.center ↥L) (ai * bi)))
    (hnot : QuotientGroup.mk' (Subgroup.center ↥L) (aj * bj) ∉
      Subgroup.zpowers (QuotientGroup.mk' (Subgroup.center ↥L) (ai * bi))) :
    ∃ ψ : (↥L ⧸ Subgroup.center ↥L) ≃* (↥L ⧸ Subgroup.center ↥L),
      ψ (QuotientGroup.mk' (Subgroup.center ↥L) (ai * bi)) =
        QuotientGroup.mk' (Subgroup.center ↥L) (ai * bi) *
          QuotientGroup.mk' (Subgroup.center ↥L) (aj * bj) := by
  set q : ↥L →* (↥L ⧸ Subgroup.center ↥L) := QuotientGroup.mk' (Subgroup.center ↥L) with hqdef
  have hq : q.ker ≤ Subgroup.center ↥L := by
    rw [hqdef, QuotientGroup.ker_mk']
  obtain ⟨vi, hvi_mem, hvi_q, hvi3, hvi_inv⟩ := exists_threeLift q hq hai2 hbi2 hui
  obtain ⟨vj, hvj_mem, hvj_q, hvj3, hvj_inv⟩ := exists_threeLift q hq haj2 hbj2 huj
  have hvij : vi * vj = vj * vi := by
    refine commute_of_inverted q hq hvj3 hvj_inv ?_ ?_
    · rw [map_mul, map_mul, hvi_q, hvj_q]; exact hcomm.eq
    · rw [map_mul, map_mul, hvi_q]; exact hbcomm.eq
  set x : W := (vi : W) with hx
  set y : W := (vj : W) with hy
  have hxy : x * y = y * x := congrArg Subtype.val hvij
  have hx3 : x ^ 3 = 1 := by
    have := congrArg Subtype.val hvi3
    simpa using this
  have hy3 : y ^ 3 = 1 := by
    have := congrArg Subtype.val hvj3
    simpa using this
  have hvi_A : x ∈ A := by
    have h : Subgroup.closure {ai, bi} ≤ A.comap L.subtype := by
      rw [Subgroup.closure_le]
      intro t ht
      rcases ht with rfl | rfl
      · exact hai
      · exact hbi
    exact h hvi_mem
  have hvj_A : y ∈ A := by
    have h : Subgroup.closure {aj, bj} ≤ A.comap L.subtype := by
      rw [Subgroup.closure_le]
      intro t ht
      rcases ht with rfl | rfl
      · exact haj
      · exact hbj
    exact h hvj_mem
  set E : Subgroup W := Subgroup.closure {x, y} with hE
  have hE_le : E ≤ A ⊓ L := by
    rw [hE, Subgroup.closure_le]
    intro t ht
    rcases ht with rfl | rfl
    · exact ⟨hvi_A, vi.2⟩
    · exact ⟨hvj_A, vj.2⟩
  obtain ⟨hEc, hE3⟩ := isElemAbelian_closure_pair hxy hx3 hy3
  have hinj : ∀ a b : ℕ, x ^ a * y ^ b = 1 → 3 ∣ a ∧ 3 ∣ b := by
    intro a b h
    have h' : vi ^ a * vj ^ b = 1 := Subtype.ext (by simpa using h)
    have h'' := congrArg q h'
    rw [map_mul, map_pow, map_pow, hvi_q, hvj_q, map_one] at h''
    exact three_dvd_of_pow_mul_pow_eq_one hui huj hnot h''
  have hEcard : Nat.card E = 9 := card_closure_pair hxy hx3 hy3 hinj
  have htrans := hA E hE_le ⟨hEc, hE3⟩ hEcard
  have hxE : x ∈ E := Subgroup.subset_closure (by simp)
  have hyE : y ∈ E := Subgroup.subset_closure (by simp)
  have hqvi_ne : q vi ≠ 1 := by
    rw [hvi_q]; intro h; rw [h, orderOf_one] at hui; omega
  have hxne : x ≠ 1 := by
    intro h; apply hqvi_ne
    have : vi = 1 := Subtype.ext (by rw [Subgroup.coe_one]; exact h)
    rw [this, map_one]
  have hxyne : x * y ≠ 1 := by
    intro h
    have h' : vi * vj = 1 := Subtype.ext (by simpa using h)
    have h'' := congrArg q h'
    rw [map_mul, hvi_q, hvj_q, map_one] at h''
    apply hnot
    have : q (aj * bj) = (q (ai * bi))⁻¹ := eq_inv_of_mul_eq_one_right h''
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  obtain ⟨g, hg, hgxy⟩ := htrans x hxE (x * y) (mul_mem hxE hyE) hxne hxyne
  have hLc : CFSG.IsComponent L := (CFSG.isComponent_iff_open L).2 hL
  have hL'c : CFSG.IsComponent (L.map (MulAut.conj g).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hLc
  have hnorm : L.map (MulAut.conj g).toMonoidHom = L := by
    rcases CFSG.LocalCores.distinct_components_commute hLc hL'c with h | h
    · exact h.symm
    · exfalso
      have hgE : ∀ e ∈ E, g⁻¹ * e * g ∈ E := by
        intro e he
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) e).1 he
        simpa using this
      have hxL' : x ∈ L.map (MulAut.conj g).toMonoidHom := by
        refine ⟨g⁻¹ * x * g, (hE_le (hgE x hxE)).2, ?_⟩
        simp [MulAut.conj_apply]
        group
      have hxc : vi ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro l
        have hc : ⁅(l : W), x⁆ ∈ ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ :=
          Subgroup.commutator_mem_commutator l.2 hxL'
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact Subtype.ext hc
      apply hqvi_ne
      rw [hqdef]
      exact (QuotientGroup.eq_one_iff _).2 hxc
  have hmapL : ∀ l : W, l ∈ L → g * l * g⁻¹ ∈ L := by
    intro l hl
    rw [← hnorm]
    exact ⟨l, hl, by simp [MulAut.conj_apply]⟩
  let φ : ↥L ≃* ↥L :=
    (MulEquiv.subgroupMap (MulAut.conj g) L).trans (MulEquiv.subgroupCongr hnorm)
  have hφ : ∀ l : ↥L, ((φ l : ↥L) : W) = g * l * g⁻¹ := fun l => rfl
  have hφc : (Subgroup.center ↥L).map (φ : ↥L →* ↥L) = Subgroup.center ↥L :=
    Subgroup.characteristic_iff_map_eq.1 inferInstance φ
  refine ⟨QuotientGroup.congr _ _ φ hφc, ?_⟩
  have hφvi : φ vi = vi * vj := Subtype.ext (by rw [hφ]; exact hgxy)
  have e1 : QuotientGroup.mk' (Subgroup.center ↥L) (ai * bi) = QuotientGroup.mk vi := by
    rw [← hvi_q]; rfl
  have e2 : QuotientGroup.mk' (Subgroup.center ↥L) (aj * bj) = QuotientGroup.mk vj := by
    rw [← hvj_q]; rfl
  rw [e1, e2, QuotientGroup.congr_mk, hφvi]
  rfl

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
