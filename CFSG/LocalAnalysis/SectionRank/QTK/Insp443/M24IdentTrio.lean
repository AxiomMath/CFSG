module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CentConfig
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24Lat
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.M24Facts
public import CFSG.Quasithin.Vol2.KGFactC31M24Q

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.M24
  CFSG.SectionRank.QTK.Insp443.M24

variable {L V MK : Subgroup G₀}

private theorem conj_comp (a b : G₀) :
    (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
      (MulAut.conj (a * b)).toMonoidHom := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.comp_apply,
    show (MulAut.conj a).toMonoidHom ((MulAut.conj b).toMonoidHom x) =
      MulAut.conj a (MulAut.conj b x) from rfl,
    show (MulAut.conj (a * b)).toMonoidHom x = MulAut.conj (a * b) x from rfl,
    MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply]
  group

private theorem KConfig.normal_step (h : KConfig G₀ L V MK) {e : G₀} {X : Subgroup G₀}
    (hC : Subgroup.centralizer (V : Set G₀) = Subgroup.map (MulAut.conj e).toMonoidHom X)
    (h2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set G₀))) :
    L ≤ Subgroup.map (MulAut.conj e).toMonoidHom (Subgroup.normalizer (X : Set G₀)) ∧
      Subgroup.map (MulAut.conj e).toMonoidHom (Subgroup.normalizer (X : Set G₀)) ≤
        Subgroup.normalizer (L : Set G₀) := by
  have hN : Subgroup.normalizer (Subgroup.centralizer (V : Set G₀) : Set G₀) =
      Subgroup.map (MulAut.conj e).toMonoidHom (Subgroup.normalizer (X : Set G₀)) := by
    rw [hC]
    exact (Subgroup.map_normalizer_eq_of_bijective X (MulAut.conj e).bijective).symm
  exact ⟨hN ▸ h.le_normalizer_centralizer, hN ▸ h.normalizer_centralizer_le h2⟩

theorem KConfig.m24_not_r2
    (h : KConfig G₀ L V MK) {e : G₀}
    (hC : Subgroup.centralizer (V : Set G₀) = (eSub basis_r2).map (MulAut.conj e).toMonoidHom)
    {y : G₀} (hy : y ∈ L) (hyk : ∃ k, y ^ 7 ^ k = 1) (hy1 : y ≠ 1) : False := by
  have h2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set G₀)) := by
    rw [hC]
    refine IsPGroup.of_card (n := 4) ?_
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj e).toMonoidHom)
      (MulAut.conj e).injective, card_eSub]
  obtain ⟨hLN, hNL⟩ := KConfig.normal_step (X := eSub basis_r2) h hC h2
  have hNr : Subgroup.normalizer (eSub basis_r2 : Set G₀) = CB0 := eNorm_r2
  rw [hNr] at hLN hNL
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hx : MulAut.conj e xE ∈ L := by
    refine mem_of_sylow (p := 7) (N := CB0.map (MulAut.conj e).toMonoidHom)
      (M₀ := L) (x := MulAut.conj e xE) (y := y) ?_ ?_ ?_ hLN hNL hy hyk hy1
    · exact Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom xE_mem_CB0
    · change orderOf ((MulAut.conj e).toMonoidHom xE) = 7
      rw [orderOf_injective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective xE,
        orderOf_xE]
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj e).toMonoidHom)
        (MulAut.conj e).injective, card_CB0]
      norm_num
  have hCB : CB0.map (MulAut.conj e).toMonoidHom ≤ L := by
    rw [Subgroup.map_le_iff_le_comap, ← conjGenOf_cj]
    refine conjGenOf_le (ws := cjW) (y := xW) fun w hw => ?_
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hwN : MulAut.conj e (elt w) ∈ CB0.map (MulAut.conj e).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom (cj_mem_CB0 w hw)
    exact (Subgroup.mem_normalizer_iff.mp (hNL hwN) (MulAut.conj e xE)).mp hx
  have hL : L = CB0.map (MulAut.conj e).toMonoidHom := le_antisymm hLN hCB
  have hO2 : Nat.card ↥(pCoreOf 2 L) = 128 := by
    rw [hL, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj e) CB0,
      Subgroup.card_map_of_injective (f := (MulAut.conj e).toMonoidHom)
        (MulAut.conj e).injective, card_pCoreOf_CB0]
  have h16 : Nat.card ↥(Subgroup.centralizer (V : Set G₀)) = 16 := by
    rw [hC, Subgroup.card_map_of_injective (f := (MulAut.conj e).toMonoidHom)
      (MulAut.conj e).injective, card_eSub]
    norm_num
  have hle := Subgroup.card_le_of_le h.pCoreOf_le
  rw [hO2, h16] at hle
  omega

theorem KConfig.m24_not_of_r2
    (h : KConfig G₀ L V MK) {c : G₀}
    (hU : (eSub basis_r2).map (MulAut.conj c).toMonoidHom ≤ V)
    {y : G₀} (hy : y ∈ L) (hyk : ∃ k, y ^ 7 ^ k = 1) (hy1 : y ≠ 1) : False := by
  have hCU : Subgroup.centralizer
      (((eSub basis_r2).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀) =
      (eSub basis_r2).map (MulAut.conj c).toMonoidHom := by
    rw [centralizer_map_conj, cent_r2]
  have hab : ∀ a ∈ Subgroup.centralizer
        (((eSub basis_r2).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀),
      ∀ b ∈ Subgroup.centralizer
        (((eSub basis_r2).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀),
        a * b = b * a := by
    intro a ha b hb
    rw [hCU] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul, eSub_comm basis_r2 a' b' ha' hb']
  have hC : Subgroup.centralizer (V : Set G₀) =
      (eSub basis_r2).map (MulAut.conj c).toMonoidHom := by
    rw [h.centralizer_eq_of_le hU hab]
    exact hCU
  exact h.m24_not_r2 hC hy hyk hy1

theorem KConfig.m24_not_of_u4
    (h : KConfig G₀ L V MK) {c : G₀}
    (hU : (eSub basis_u4).map (MulAut.conj c).toMonoidHom ≤ V)
    {y : G₀} (hy : y ∈ L) (hyk : ∃ k, y ^ 7 ^ k = 1) (hy1 : y ≠ 1) : False := by
  have hCU : Subgroup.centralizer
      (((eSub basis_u4).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀) =
      (eSub basis_r2).map (MulAut.conj (c * d4)).toMonoidHom := by
    rw [centralizer_map_conj, cent_u4, Subgroup.map_map, conj_comp]
  have hab : ∀ a ∈ Subgroup.centralizer
        (((eSub basis_u4).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀),
      ∀ b ∈ Subgroup.centralizer
        (((eSub basis_u4).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀),
        a * b = b * a := by
    intro a ha b hb
    rw [hCU] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul, eSub_comm basis_r2 a' b' ha' hb']
  have hC : Subgroup.centralizer (V : Set G₀) =
      (eSub basis_r2).map (MulAut.conj (c * d4)).toMonoidHom := by
    rw [h.centralizer_eq_of_le hU hab]
    exact hCU
  exact h.m24_not_r2 hC hy hyk hy1

theorem KConfig.m24_eq_trio
    (h : KConfig G₀ L V MK) {e : G₀}
    (hC : Subgroup.centralizer (V : Set G₀) = (eSub basis_et).map (MulAut.conj e).toMonoidHom)
    {y : G₀} (hy : y ∈ L) (hyk : ∃ k, y ^ 7 ^ k = 1) (hy1 : y ≠ 1) :
    L = Lq.map (MulAut.conj e).toMonoidHom := by
  have h2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set G₀)) := by
    rw [hC]
    refine IsPGroup.of_card (n := 6) ?_
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj e).toMonoidHom)
      (MulAut.conj e).injective, card_eSub]
  obtain ⟨hLN, hNL⟩ := KConfig.normal_step (X := eSub basis_et) h hC h2
  have hi3 : (Nq.map (MulAut.conj e).toMonoidHom).relIndex
      ((eNorm basis_et).map (MulAut.conj e).toMonoidHom) ≤ 4 := by
    rw [Subgroup.relIndex_map_map_of_injective Nq (eNorm basis_et)
      (MulAut.conj e).injective, relIndex_Nq_eNorm_et]
    norm_num
  have hL1 : L ≤ Nq.map (MulAut.conj e).toMonoidHom :=
    le_of_perfect_of_relIndex_le hLN h.perfect hi3
  have hi2 : (Lq.map (MulAut.conj e).toMonoidHom).relIndex
      (Nq.map (MulAut.conj e).toMonoidHom) ≤ 4 := by
    rw [Subgroup.relIndex_map_map_of_injective Lq Nq (MulAut.conj e).injective,
      relIndex_Lq_Nq]
    norm_num
  have hL2 : L ≤ Lq.map (MulAut.conj e).toMonoidHom :=
    le_of_perfect_of_relIndex_le hL1 h.perfect hi2
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hy7 : MulAut.conj e y7 ∈ L := by
    refine mem_of_sylow (p := 7) (N := (eNorm basis_et).map (MulAut.conj e).toMonoidHom)
      (M₀ := L) (x := MulAut.conj e y7) (y := y) ?_ ?_ ?_ hLN hNL hy hyk hy1
    · exact Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom y7_mem_eNorm_et
    · change orderOf ((MulAut.conj e).toMonoidHom y7) = 7
      rw [orderOf_injective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective y7,
        orderOf_y7]
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj e).toMonoidHom)
        (MulAut.conj e).injective, card_eNorm_et]
      norm_num
  have hH_le : Lq.map (MulAut.conj e).toMonoidHom ≤ L := by
    rw [Subgroup.map_le_iff_le_comap]
    refine conjGenOf_le (ws := mjW) (y := y7W) fun w hw => ?_
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    have hwN : MulAut.conj e (elt w) ∈ (eNorm basis_et).map (MulAut.conj e).toMonoidHom :=
      Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom (mj_mem_eNorm_et w hw)
    exact (Subgroup.mem_normalizer_iff.mp (hNL hwN) (MulAut.conj e y7)).mp hy7
  exact le_antisymm hL2 hH_le

theorem KConfig.m24_eq_of_u6
    (h : KConfig G₀ L V MK) {c : G₀}
    (hU : (eSub basis_u6).map (MulAut.conj c).toMonoidHom ≤ V)
    {y : G₀} (hy : y ∈ L) (hyk : ∃ k, y ^ 7 ^ k = 1) (hy1 : y ≠ 1) :
    V = (eSub basis_et).map (MulAut.conj (c * zE⁻¹)).toMonoidHom ∧
      L = Lq.map (MulAut.conj (c * zE⁻¹)).toMonoidHom := by
  set e : G₀ := c * zE⁻¹ with he
  set W : Subgroup G₀ := (eSub basis_u6).map (MulAut.conj zE).toMonoidHom with hW
  set W' : Subgroup G₀ := (eSub basis_u6).map (MulAut.conj (lE * zE)).toMonoidHom with hW'
  have hec : e * zE = c := by
    rw [he]
    group
  have hU6 : (eSub basis_u6).map (MulAut.conj c).toMonoidHom =
      W.map (MulAut.conj e).toMonoidHom := by
    rw [hW]
    simp only [Subgroup.map_map, conj_comp, hec]
  have hCU : Subgroup.centralizer
      (((eSub basis_u6).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀) =
      (eSub basis_et).map (MulAut.conj e).toMonoidHom := by
    rw [hU6, centralizer_map_conj, cent_conj_zE_u6]
  have hab : ∀ a ∈ Subgroup.centralizer
        (((eSub basis_u6).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀),
      ∀ b ∈ Subgroup.centralizer
        (((eSub basis_u6).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀),
        a * b = b * a := by
    intro a ha b hb
    rw [hCU] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    rw [← map_mul, ← map_mul, eSub_comm basis_et a' b' ha' hb']
  have hC : Subgroup.centralizer (V : Set G₀) =
      (eSub basis_et).map (MulAut.conj e).toMonoidHom := by
    rw [h.centralizer_eq_of_le hU hab]
    exact hCU
  have hL : L = Lq.map (MulAut.conj e).toMonoidHom := h.m24_eq_trio hC hy hyk hy1
  have hV1 : W.map (MulAut.conj e).toMonoidHom ≤ V := by
    rw [← hU6]
    exact hU
  have hV2 : W'.map (MulAut.conj e).toMonoidHom ≤ V := by
    have hl : MulAut.conj e lE ∈ L := by
      rw [hL]
      exact Subgroup.mem_map_of_mem (MulAut.conj e).toMonoidHom lE_mem
    have hnorm : MulAut.conj e lE ∈ Subgroup.normalizer (V : Set G₀) := h.le_normalizer hl
    have hWW' : W' = W.map (MulAut.conj lE).toMonoidHom := by
      rw [hW', hW]
      simp only [Subgroup.map_map, conj_comp]
    have heq : e * lE = MulAut.conj e lE * e := by
      change e * lE = (e * lE * e⁻¹) * e
      group
    have hconj : (W.map (MulAut.conj lE).toMonoidHom).map (MulAut.conj e).toMonoidHom =
        (W.map (MulAut.conj e).toMonoidHom).map
          (MulAut.conj (MulAut.conj e lE)).toMonoidHom := by
      simp only [Subgroup.map_map, conj_comp, heq]
    rw [hWW', hconj]
    exact (Subgroup.map_mono (f := (MulAut.conj (MulAut.conj e lE)).toMonoidHom) hV1).trans
      (le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp hnorm))
  have hVsup : (eSub basis_et).map (MulAut.conj e).toMonoidHom ≤ V := by
    rw [← sup_six_eq_et, Subgroup.map_sup]
    exact sup_le hV1 hV2
  have hVle : V ≤ (eSub basis_et).map (MulAut.conj e).toMonoidHom := by
    have hv := h.le_centralizer
    rwa [hC] at hv
  exact ⟨le_antisymm hVle hVsup, hL⟩

theorem KConfig.m24_eq_of_t
    (h : KConfig G₀ L V MK) {c : G₀}
    (hU : (eSub basis_t).map (MulAut.conj c).toMonoidHom ≤ V)
    {y : G₀} (hy : y ∈ L) (hyk : ∃ k, y ^ 7 ^ k = 1) (hy1 : y ≠ 1) :
    V = (eSub basis_et).map (MulAut.conj (c * gE⁻¹)).toMonoidHom ∧
      L = Lq.map (MulAut.conj (c * gE⁻¹)).toMonoidHom := by
  set e : G₀ := c * gE⁻¹ with he
  have hCU : Subgroup.centralizer
      (((eSub basis_t).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀) =
      (eSub basis_t).map (MulAut.conj c).toMonoidHom := by
    rw [centralizer_map_conj, cent_t]
  have hVle : V ≤ (eSub basis_t).map (MulAut.conj c).toMonoidHom :=
    h.le_centralizer.trans ((Subgroup.centralizer_le hU).trans hCU.le)
  have hVU : V = (eSub basis_t).map (MulAut.conj c).toMonoidHom := le_antisymm hVle hU
  have hEt : (eSub basis_et).map (MulAut.conj gE⁻¹).toMonoidHom = eSub basis_t := by
    have h := congrArg (Subgroup.map (MulAut.conj gE⁻¹).toMonoidHom) conj_gE_t
    rw [Subgroup.map_map] at h
    have hcomp : (MulAut.conj gE⁻¹).toMonoidHom.comp (MulAut.conj gE).toMonoidHom =
        MonoidHom.id G₀ := by
      refine MonoidHom.ext fun x => ?_
      rw [MonoidHom.comp_apply,
        show (MulAut.conj gE⁻¹).toMonoidHom ((MulAut.conj gE).toMonoidHom x) =
          MulAut.conj gE⁻¹ (MulAut.conj gE x) from rfl,
        show (MonoidHom.id G₀) x = x from rfl,
        MulAut.conj_apply, MulAut.conj_apply]
      group
    rw [hcomp, Subgroup.map_id] at h
    exact h.symm
  have hmap : (eSub basis_et).map (MulAut.conj e).toMonoidHom =
      (eSub basis_t).map (MulAut.conj c).toMonoidHom := by
    have hcomp2 : (MulAut.conj c).toMonoidHom.comp (MulAut.conj gE⁻¹).toMonoidHom =
        (MulAut.conj e).toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      rw [MonoidHom.comp_apply,
        show (MulAut.conj c).toMonoidHom ((MulAut.conj gE⁻¹).toMonoidHom x) =
          MulAut.conj c (MulAut.conj gE⁻¹ x) from rfl,
        show (MulAut.conj e).toMonoidHom x = MulAut.conj e x from rfl,
        MulAut.conj_apply, MulAut.conj_apply, MulAut.conj_apply, he]
      group
    rw [← hcomp2, ← Subgroup.map_map, hEt]
  have hVeq : V = (eSub basis_et).map (MulAut.conj e).toMonoidHom := by
    rw [hVU, hmap]
  have hC : Subgroup.centralizer (V : Set G₀) =
      (eSub basis_et).map (MulAut.conj e).toMonoidHom := by
    rw [hVeq, centralizer_map_conj, cent_et]
  exact ⟨hVeq, h.m24_eq_trio hC hy hyk hy1⟩

end CFSG.SectionRank.QTK.Insp443

end

