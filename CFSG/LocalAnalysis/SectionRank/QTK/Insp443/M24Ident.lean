module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CentConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24Lat
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.RefConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24ConclSextet

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M24

private theorem map_centralizer_of_bijective {f : G₀ →* G₀} (hf : Function.Bijective f)
    (X : Subgroup G₀) :
    (Subgroup.centralizer (X : Set G₀)).map f =
      Subgroup.centralizer ((X.map f : Subgroup G₀) : Set G₀) := by
  rw [CFSG.Quasithin.KGC31.map_centralizer_eq f hf.injective,
    MonoidHom.range_eq_top.mpr hf.surjective, top_inf_eq]

namespace M24

theorem refData_o :
    RefData (eSub basis_o) Mo where
  cent := cent_o.le
  comm := fun a ha b hb => eSub_comm basis_o a b ha hb
  le := o_le_Mo
  norm := Mo_le
  perf := perf_of_card Mo_le (by
    change Nat.card (eNorm basis_o) ≤ 2 * Nat.card Mo
    rw [eNorm_o, card_Mo]
    norm_num)
  simple := by
    have hO : Mo ⊓ Subgroup.centralizer (eSub basis_o : Set G₀) = eSub basis_o := by
      rw [cent_o, inf_eq_right.mpr o_le_Mo]
    have hker : (E16.eNHom basis_o Mo_le).ker = (eSub basis_o).subgroupOf Mo :=
      ker_eNHom basis_o Mo_le hO
    have hsurj : Function.Surjective (E16.eNHom basis_o Mo_le) := by
      have h1 := card_range_eq o_le_Mo (E16.eNHom basis_o Mo_le) hker
      rw [card_eSub, card_Mo] at h1
      have h2 : Nat.card (E16.eNHom basis_o Mo_le).range =
          Nat.card ↥(StatedSL 4 (ZMod 2)) := by
        rw [E16.card_statedSL4]
        omega
      rw [← MonoidHom.range_eq_top]
      exact Subgroup.eq_top_of_card_eq _ h2
    haveI : IsSimpleGroup ↥(StatedSL 4 (ZMod 2)) := E16.isSimpleGroup_statedSL4
    exact simple_of_surj _ hsurj hker

end M24

variable {L V MK : Subgroup G₀}

theorem KConfig.m24_eq_of_o
    (h : KConfig G₀ L V MK) {c : G₀}
    (hU : (eSub basis_o).map (MulAut.conj c).toMonoidHom ≤ V) :
    V = (eSub basis_o).map (MulAut.conj c).toMonoidHom ∧
      L = Mo.map (MulAut.conj c).toMonoidHom :=
  h.eq_of_refData_of_le
    (RefData.map_mulEquiv (M24.refData_o) (MulAut.conj c)) hU

theorem KConfig.m24_eq_sextet
    (h : KConfig G₀ L V MK) {e : G₀}
    (hC : Subgroup.centralizer (V : Set G₀) =
      (eSub basis_s).map (MulAut.conj e).toMonoidHom)
    {y : G₀} (hy : y ∈ L) (hyk : ∃ k, y ^ 5 ^ k = 1) (hy1 : y ≠ 1) :
    V = (eSub basis_s).map (MulAut.conj e).toMonoidHom ∧
      L = Ls.map (MulAut.conj e).toMonoidHom := by
  let f : G₀ →* G₀ := (MulAut.conj e).toMonoidHom
  have hfb : Function.Bijective f := (MulAut.conj e).bijective
  have hf : Function.Injective f := hfb.injective
  have hC' : Subgroup.centralizer (V : Set G₀) = (eSub basis_s).map f := hC
  have h2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set G₀)) := by
    rw [hC']
    exact IsPGroup.of_card (n := 6) (by
      rw [Subgroup.card_map_of_injective (f := f) hf, card_eSub])
  have hNs : Subgroup.normalizer (eSub basis_s : Set G₀) = Ns := M24.eNorm_s
  have hN : Subgroup.normalizer (Subgroup.centralizer (V : Set G₀) : Set G₀) = Ns.map f := by
    rw [hC', ← Subgroup.map_normalizer_eq_of_bijective (eSub basis_s) hfb, hNs]
  have hLN : L ≤ Ns.map f := by
    rw [← hN]
    exact h.le_normalizer_centralizer
  have hNL : Ns.map f ≤ Subgroup.normalizer (L : Set G₀) := by
    rw [← hN]
    exact h.normalizer_centralizer_le h2
  have hi : (Ls.map f).relIndex (Ns.map f) ≤ 4 := by
    rw [Subgroup.relIndex_map_map_of_injective Ls Ns hf, M24.relIndex_Ls_Ns]
    norm_num
  have hL_le : L ≤ Ls.map f :=
    le_of_perfect_of_relIndex_le (K := L) (H := Ls.map f) (N := Ns.map f) hLN h.perfect hi
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hy5 : f y5 ∈ L := by
    refine mem_of_sylow (p := 5) (N := Ns.map f) (M₀ := L) (x := f y5) (y := y)
      ?_ ?_ ?_ hLN hNL hy hyk hy1
    · exact Subgroup.mem_map_of_mem f (by rw [← M24.eNorm_s]; exact y5_mem)
    · rw [orderOf_injective f hf y5, orderOf_y5]
    · rw [Subgroup.card_map_of_injective (f := f) hf, card_Ns]
      norm_num
  have hH_le : Ls.map f ≤ L := by
    rw [Subgroup.map_le_iff_le_comap]
    refine conjGenOf_le (ws := njW) (y := y5W) fun w hw => ?_
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    change f (elt w) * f y5 * (f (elt w))⁻¹ ∈ L
    have hwN : f (elt w) ∈ Ns.map f :=
      Subgroup.mem_map_of_mem f (by rw [← M24.eNorm_s]; exact nj_mem w hw)
    exact (Subgroup.mem_normalizer_iff.mp (hNL hwN) (f y5)).mp hy5
  have hLeq : L = Ls.map f := le_antisymm hL_le hH_le
  have hperf : ⁅Ls, Ls⁆ = Ls := by
    apply Subgroup.map_injective (f := f) hf
    rw [Subgroup.map_commutator, ← hLeq, h.perfect]
  have hVC : V ≤ (eSub basis_s).map f := by
    rw [← hC']
    exact h.le_centralizer
  let W : Subgroup G₀ := V.comap f
  have hmapV : W.map f = V := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr hfb.surjective, top_inf_eq]
  have hWR : W ≤ eSub basis_s := by
    intro x hx
    have hx' : f x ∈ V := hx
    obtain ⟨r, hr, hfr⟩ := hVC hx'
    have hrx : r = x := hf hfr
    rw [← hrx]
    exact hr
  have hLW : Ls ≤ Subgroup.normalizer (W : Set G₀) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp
      (h.le_normalizer (hH_le (Subgroup.mem_map_of_mem f hz))) (f x))
  have hVeq : V = (eSub basis_s).map f := by
    rcases M24.irr_Ls hperf hWR hLW with hW | hW
    · exfalso
      apply h.ne_bot
      rw [← hmapV, hW, Subgroup.map_bot]
    · rw [← hmapV, hW]
  exact ⟨hVeq, hLeq⟩

theorem KConfig.m24_eq_of_s32
    (h : KConfig G₀ L V MK) {c : G₀}
    (hU : (eSub basis_s32).map (MulAut.conj c).toMonoidHom ≤ V)
    {y : G₀} (hy : y ∈ L) (hyk : ∃ k, y ^ 5 ^ k = 1) (hy1 : y ≠ 1) :
    V = (eSub basis_s).map (MulAut.conj c).toMonoidHom ∧
      L = Ls.map (MulAut.conj c).toMonoidHom := by
  let f : G₀ →* G₀ := (MulAut.conj c).toMonoidHom
  have hfb : Function.Bijective f := (MulAut.conj c).bijective
  have hC32 : Subgroup.centralizer ((eSub basis_s32).map f : Set G₀) =
      (eSub basis_s).map f := by
    rw [← map_centralizer_of_bijective hfb (eSub basis_s32), cent_s32]
  have hab : ∀ a ∈ Subgroup.centralizer ((eSub basis_s32).map f : Set G₀),
      ∀ b ∈ Subgroup.centralizer ((eSub basis_s32).map f : Set G₀), a * b = b * a := by
    intro a ha b hb
    rw [hC32] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul, eSub_comm basis_s a' b' ha' hb']
  have hC : Subgroup.centralizer (V : Set G₀) = (eSub basis_s).map f := by
    rw [h.centralizer_eq_of_le hU hab]
    exact hC32
  exact h.m24_eq_sextet hC hy hyk hy1

theorem KConfig.m24_eq_of_s16
    (h : KConfig G₀ L V MK) {c : G₀}
    (hU : (eSub basis_s16).map (MulAut.conj c).toMonoidHom ≤ V)
    {y : G₀} (hy : y ∈ L) (hyk : ∃ k, y ^ 5 ^ k = 1) (hy1 : y ≠ 1) :
    V = (eSub basis_s).map (MulAut.conj c).toMonoidHom ∧
      L = Ls.map (MulAut.conj c).toMonoidHom := by
  let f : G₀ →* G₀ := (MulAut.conj c).toMonoidHom
  have hfb : Function.Bijective f := (MulAut.conj c).bijective
  have hC16 : Subgroup.centralizer ((eSub basis_s16).map f : Set G₀) =
      (eSub basis_s).map f := by
    rw [← map_centralizer_of_bijective hfb (eSub basis_s16), cent_s16]
  have hab : ∀ a ∈ Subgroup.centralizer ((eSub basis_s16).map f : Set G₀),
      ∀ b ∈ Subgroup.centralizer ((eSub basis_s16).map f : Set G₀), a * b = b * a := by
    intro a ha b hb
    rw [hC16] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul, eSub_comm basis_s a' b' ha' hb']
  have hC : Subgroup.centralizer (V : Set G₀) = (eSub basis_s).map f := by
    rw [h.centralizer_eq_of_le hU hab]
    exact hC16
  exact h.m24_eq_sextet hC hy hyk hy1

theorem KConfig.m24_eq_u5
    (h : KConfig G₀ L V MK) {c : G₀}
    (hV : V = (eSub basis_u5).map (MulAut.conj c).toMonoidHom)
    {y : G₀} (hy : y ∈ L) (hyk : ∃ k, y ^ 7 ^ k = 1) (hy1 : y ≠ 1) :
    L = Lq.map (MulAut.conj c).toMonoidHom := by
  let f : G₀ →* G₀ := (MulAut.conj c).toMonoidHom
  have hfb : Function.Bijective f := (MulAut.conj c).bijective
  have hf : Function.Injective f := hfb.injective
  have hV' : V = (eSub basis_u5).map f := hV
  have hNu : Subgroup.normalizer (eSub basis_u5 : Set G₀) = Nq := M24.eNorm_u5
  have hN : Subgroup.normalizer (V : Set G₀) = Nq.map f := by
    rw [hV', ← Subgroup.map_normalizer_eq_of_bijective (eSub basis_u5) hfb, hNu]
  have hLN : L ≤ Nq.map f := hN ▸ h.le_normalizer
  have hNL : Nq.map f ≤ Subgroup.normalizer (L : Set G₀) :=
    hN ▸ (h.normalizer_le_MK.trans h.MK_le_normalizer)
  have hi : (Lq.map f).relIndex (Nq.map f) ≤ 4 := by
    rw [Subgroup.relIndex_map_map_of_injective Lq Nq hf, M24.relIndex_Lq_Nq]
    norm_num
  have hL_le : L ≤ Lq.map f :=
    le_of_perfect_of_relIndex_le (K := L) (H := Lq.map f) (N := Nq.map f) hLN h.perfect hi
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hy7 : f y7 ∈ L := by
    refine mem_of_sylow (p := 7) (N := Nq.map f) (M₀ := L) (x := f y7) (y := y)
      ?_ ?_ ?_ hLN hNL hy hyk hy1
    · exact Subgroup.mem_map_of_mem f (by rw [← M24.eNorm_u5]; exact y7_mem)
    · rw [orderOf_injective f hf y7, orderOf_y7]
    · rw [Subgroup.card_map_of_injective (f := f) hf, card_Nq]
      norm_num
  have hH_le : Lq.map f ≤ L := by
    rw [Subgroup.map_le_iff_le_comap]
    refine conjGenOf_le (ws := mjW) (y := y7W) fun w hw => ?_
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    change f (elt w) * f y7 * (f (elt w))⁻¹ ∈ L
    have hwN : f (elt w) ∈ Nq.map f :=
      Subgroup.mem_map_of_mem f (by rw [← M24.eNorm_u5]; exact mj_mem w hw)
    exact (Subgroup.mem_normalizer_iff.mp (hNL hwN) (f y7)).mp hy7
  exact le_antisymm hL_le hH_le

end CFSG.SectionRank.QTK.Insp443

end
