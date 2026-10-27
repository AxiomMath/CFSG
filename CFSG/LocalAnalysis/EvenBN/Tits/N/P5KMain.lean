module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Gen
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KSet
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5K618
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5Syl

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N

variable {Γ : Type*} [Group Γ]

namespace KSet

variable {Hs C U K W0 W : Subgroup Γ} {x y t : Γ} (h : KSet Hs C U K W0 W x y t)

include h



theorem exists_twist [Finite Γ] :
    ∀ u ∈ W, t * u * t⁻¹ = u → ∃ w ∈ W, u = w * (t * w * t⁻¹) := by
  intro u hu htu
  have htn := h.t_mem_normalizer_W
  set j : MulAut ↥W := actFun W t with hj
  have hc : ∀ a b : ↥W, a * b = b * a := fun a b => h.W_ab.1.is_comm.comm a b
  have h2 : ∀ w : ↥W, w * w = 1 := fun w => by
    have := h.W_ab.2 w w.2
    apply Subtype.ext
    simpa [pow_two] using this
  have hjj : j * j = 1 := by
    rw [hj, ← actFun_mul W htn htn, h.t_sq, actFun_one]
  have hfix : ∀ w : ↥W, w ∈ fixSub j ↔ (w : Γ) ∈ U := by
    intro w
    rw [mem_fixSub, Subtype.ext_iff, hj, actFun_apply_coe W htn w]
    exact h.W_cent_t w w.2
  have hfeq : fixSub j = U.subgroupOf W := by
    ext w
    rw [hfix, Subgroup.mem_subgroupOf]
  have hcard16 : Nat.card (fixSub j) = 16 := by
    rw [hfeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.U_le_W).toEquiv, h.U_card]
  have hmul := card_fixSub_mul_card_commImg hc h2 j
  have hW256 : Nat.card ↥W = 256 := by rw [h.W_card]; norm_num
  rw [hcard16, hW256] at hmul
  have hcomm16 : Nat.card (commImg j) = 16 := by omega
  have hle := commImg_le_fixSub hc h2 hjj
  have heq : commImg j = fixSub j :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard16, hcomm16])
  have hmem : (⟨u, hu⟩ : ↥W) ∈ fixSub j := by
    rw [hfix]
    exact (h.W_cent_t u hu).1 htu
  rw [← heq, commImg_eq_range_twistHom hc h2 j] at hmem
  obtain ⟨w, hw⟩ := hmem
  refine ⟨w, w.2, ?_⟩
  have := congrArg Subtype.val hw
  rw [twistHom_apply] at this
  simp only [Subgroup.coe_mul] at this
  rw [hj, actFun_apply_coe W htn w] at this
  exact this.symm

theorem maxElemAbelian2_K [Finite Γ] : maxElemAbelian2 K = {W} := by
  have h256 : Nat.card W = 256 := by rw [h.W_card]; norm_num
  have hU16 : Nat.card U = 16 := h.U_card
  exact maxElemAbelian2_eq_of_structure h.frob h.t_sq h.t_x h.t_y h.W0_K h.F_le_K
    h.K_le_normalizer_W h.K_W0 h.W_ab h256 h.W_le_W0 (h.zpowers_t_le_W0 (mem_zpowers t))
    h.t_not_mem_W h.W0_eq h.K_dec_F h.F_inf_W0 h.fpf h.W_cent_t hU16

theorem maxElemAbelian2_W_sup [Finite Γ] {T' : Subgroup Γ} (hT : fusionIsSylowIn 2 T' C) :
    maxElemAbelian2 (W ⊔ T') = {W} := by
  have hmax := h.maxElemAbelian2_K
  have hWK : W ≤ K := h.W_le_W0.trans h.W0_K
  have hT'K : T' ≤ K := hT.1.trans h.C_le_K
  have hle : W ⊔ T' ≤ K := sup_le hWK hT'K
  have hWmem : W ∈ maxElemAbelian2 K := by rw [hmax]; rfl
  ext E
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hEle, hEab, hEmax⟩
    have h1 : Nat.card W ≤ Nat.card E := hEmax W le_sup_left h.W_ab
    have hE : E ∈ maxElemAbelian2 K :=
      ⟨hEle.trans hle, hEab, fun D hD hDab => (hWmem.2.2 D hD hDab).trans h1⟩
    rw [hmax] at hE
    exact hE
  · rintro rfl
    exact ⟨le_sup_left, h.W_ab, fun D hD hDab => hWmem.2.2 D (hD.trans hle) hDab⟩

theorem W_inf_centralizer_t : W ⊓ centralizer ({t} : Set Γ) = U := by
  ext w
  constructor
  · rintro ⟨hw, hc⟩
    refine (h.W_cent_t w hw).1 ?_
    have : w * t = t * w := mem_centralizer_singleton_iff.1 hc
    calc t * w * t⁻¹ = (w * t) * t⁻¹ := by rw [this]
      _ = w := by group
  · intro hu
    exact ⟨h.U_le_W hu, mem_centralizer_singleton_iff.2 (h.t_comm_U hu).symm⟩

theorem sylow_W [Finite Γ] : fusionIsSylowIn 2 W (centralizer (W : Set Γ) ⊓ Hs) := by
  refine fusionIsSylowIn_centralizer_of_trans h.W_le_Hs h.W_ab (h.C_le_Hs h.t_mem_C) h.t_sq
    h.t_mem_normalizer_W h.hcent ?_
  intro q hqHs _ ⟨w, hwW, hq⟩
  have hw2 : w * w = 1 := by
    have := h.W_ab.2 w hwW
    simpa [pow_two] using this
  have hqt2 : (q * t * q⁻¹) * (q * t * q⁻¹) = 1 := by
    calc (q * t * q⁻¹) * (q * t * q⁻¹) = q * (t * t) * q⁻¹ := by group
      _ = 1 := by rw [h.t_sq]; group
  rw [hq] at hqt2
  have hwt : t * w * t⁻¹ = w := by
    have h1 : t * w * t = w⁻¹ := by
      have : w * (t * w * t) = 1 := by
        calc w * (t * w * t) = (w * t) * (w * t) := by group
          _ = 1 := hqt2
      exact eq_inv_of_mul_eq_one_right this
    have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_sq
    rw [htinv, h1, hwinv]
  have hwU : w ∈ U := (h.W_cent_t w hwW).1 hwt
  have hmem : q * t * q⁻¹ ∈ (U ⊔ zpowers t : Subgroup Γ) := by
    rw [hq]
    exact mul_mem (mem_sup_left hwU) (mem_sup_right (mem_zpowers t))
  obtain ⟨w2, hw2W0, hw2eq⟩ := h.trans q hqHs hmem
  obtain ⟨v, hv, e, rfl⟩ := h.W0_eq w2 hw2W0
  refine ⟨v, hv, ?_⟩
  rw [← hw2eq]
  have hte : t ^ e * t = t * t ^ e := by rw [← pow_succ, ← pow_succ']
  calc v * t * v⁻¹ = v * (t ^ e * t * (t ^ e)⁻¹) * v⁻¹ := by rw [hte]; group
    _ = v * t ^ e * t * (v * t ^ e)⁻¹ := by group



theorem imgIn_C_eq [Finite Γ] :
    imgIn W C = centralizer ({actFun W t} : Set (MulAut ↥W)) ⊓ imgIn W (normalizer (W : Set Γ) ⊓ Hs) := by
  have htn := h.t_mem_normalizer_W
  apply le_antisymm
  · refine le_inf ?_ (imgIn_mono W h.C_le_NHs)
    intro a ha
    obtain ⟨c, hcC, hcN, rfl⟩ := (mem_imgIn_iff W C).1 ha
    have hc1 : c ∈ centralizer ({t} : Set Γ) := by
      rw [h.C_cent] at hcC
      exact hcC.1
    exact mem_centralizer_singleton_iff.2 (actFun_comm_of_comm W (mem_centralizer_singleton_iff.1 hc1))
  · rintro a ⟨haC, haI⟩
    obtain ⟨k, hkI, hkN, rfl⟩ := (mem_imgIn_iff W _).1 haI
    have hkHs : k ∈ Hs := hkI.2
    have hcomm : actFun W k * actFun W t = actFun W t * actFun W k :=
      mem_centralizer_singleton_iff.1 haC
    rw [← actFun_mul W hkN htn, ← actFun_mul W htn hkN,
      actFun_eq_iff W (mul_mem hkN htn) (mul_mem htn hkN)] at hcomm
    have hkt : k * t * k⁻¹ * t⁻¹ ∈ centralizer (W : Set Γ) ⊓ Hs := by
      refine ⟨?_, mul_mem (mul_mem (mul_mem hkHs (h.C_le_Hs h.t_mem_C)) (Subgroup.inv_mem _ hkHs))
        (Subgroup.inv_mem _ (h.C_le_Hs h.t_mem_C))⟩
      have h1 := h.conj_mem_centralizer (mul_mem hkN htn) (Subgroup.inv_mem _ hcomm)
      have e : k * t * k⁻¹ * t⁻¹ = (k * t) * ((k * t)⁻¹ * (t * k))⁻¹ * (k * t)⁻¹ := by group
      rw [e]
      exact h1
    obtain ⟨m, hmC, hm⟩ := exists_mul_centralizer_of_commutator_mem h.W_ab h.t_sq h.sylow_W
      h.exists_twist hkt
    have hmN : m ∈ normalizer (W : Set Γ) := Subgroup.centralizer_le_normalizer _ hmC.1
    have hk'C : m⁻¹ * k ∈ C := by
      rw [h.C_cent]
      exact ⟨mem_centralizer_singleton_iff.2 hm, mul_mem (Subgroup.inv_mem _ hmC.2) hkHs⟩
    have hk'N : m⁻¹ * k ∈ normalizer (W : Set Γ) := mul_mem (Subgroup.inv_mem _ hmN) hkN
    refine (mem_imgIn_iff W C).2 ⟨m⁻¹ * k, hk'C, hk'N, ?_⟩
    rw [actFun_mul W (Subgroup.inv_mem _ hmN) hkN, actFun_inv W hmN,
      (actFun_eq_one_iff W hmN).2 hmC.1, inv_one, one_mul]




theorem centralizer_alpha_eq [Finite Γ] :
    centralizer ({actFun W t} : Set (MulAut ↥W)) ⊓ imgIn W (normalizer (W : Set Γ) ⊓ Hs) =
      zpowers (actFun W t) ⊔ (imgIn W (zpowers x) ⊔ zpowers (actFun W y)) := by
  have htn := h.t_mem_normalizer_W
  rw [← h.imgIn_C_eq]
  have hKN := h.K_le_normalizer_W
  have hxK : zpowers x ≤ K := (le_sup_left : zpowers x ≤ F20 x y).trans h.F_le_K
  have hyK : zpowers y ≤ K := (le_sup_right : zpowers y ≤ F20 x y).trans h.F_le_K
  have hUK : U ≤ K := h.U_le_C.trans h.C_le_K
  have htK : zpowers t ≤ K := zpowers_le.2 h.t_mem_K
  rw [h.C_def, imgIn_sup_of_le W (htK.trans hKN)
      (sup_le (sup_le (hUK.trans hKN) (hxK.trans hKN)) (hyK.trans hKN)),
    imgIn_sup_of_le W (sup_le (hUK.trans hKN) (hxK.trans hKN)) (hyK.trans hKN),
    imgIn_sup_of_le W (hUK.trans hKN) (hxK.trans hKN),
    imgIn_eq_bot_of_le_centralizer W (h.U_le_W.trans h.W_le_centralizer),
    imgIn_zpowers W htn, imgIn_zpowers W h.y_mem_normalizer_W, bot_sup_eq]

theorem inf_alpha_bot [Finite Γ] :
    zpowers (actFun W t) ⊓ (imgIn W (zpowers x) ⊔ zpowers (actFun W y)) = ⊥ := by
  have htn := h.t_mem_normalizer_W
  have hsq : actFun W t * actFun W t = 1 := by
    rw [← actFun_mul W htn htn, h.t_sq, actFun_one]
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨hbt, hbF⟩ := hb
  rcases mem_zpowers_sq_one hsq hbt with h1 | h1
  · rw [h1]; exact one_mem _
  · exfalso
    have hF : actFun W t ∈ imgIn W (F20 x y) := by
      rw [F20, imgIn_sup_of_le W (zpowers_le.2 h.x_mem_normalizer_W) (zpowers_le.2 h.y_mem_normalizer_W),
        imgIn_zpowers W h.y_mem_normalizer_W]
      rw [h1] at hbF
      exact hbF
    obtain ⟨f, hf, hfN, hfeq⟩ := (mem_imgIn_iff W _).1 hF
    have hc : f⁻¹ * t ∈ centralizer (W : Set Γ) := (actFun_eq_iff W hfN htn).1 hfeq
    have hfC : f ∈ C := h.F_le_C hf
    have hft : t * f⁻¹ = f⁻¹ * t := (Commute.inv_right (show Commute t f from h.t_comm_F hf)).eq
    have hmem : f⁻¹ * t ∈ W := by
      refine h.hcent _ (mul_mem (Subgroup.inv_mem _ (h.C_le_Hs hfC)) (h.C_le_Hs h.t_mem_C)) hc ?_
      calc f⁻¹ * t * t = (t * f⁻¹) * t := by rw [hft]
        _ = t * (f⁻¹ * t) := by group
    have hfW0 : f ∈ W0 := by
      have h2 : t * (f⁻¹ * t)⁻¹ ∈ W0 :=
        mul_mem (h.zpowers_t_le_W0 (mem_zpowers t))
          (Subgroup.inv_mem _ (h.W_le_W0 hmem))
      have e : t * (f⁻¹ * t)⁻¹ = f := by group
      rwa [e] at h2
    have hf1 : f ∈ F20 x y ⊓ W0 := ⟨hf, hfW0⟩
    rw [h.F_inf_W0] at hf1
    have : f = 1 := mem_bot.1 hf1
    rw [this] at hmem
    simp only [inv_one, one_mul] at hmem
    exact h.t_not_mem_W hmem

theorem comm_alpha :
    ∀ a ∈ (imgIn W (zpowers x) ⊔ zpowers (actFun W y) : Subgroup (MulAut ↥W)),
      actFun W t * a = a * actFun W t := by
  have hle : imgIn W (zpowers x) ⊔ zpowers (actFun W y) ≤
      centralizer ({actFun W t} : Set (MulAut ↥W)) := by
    refine sup_le ?_ ?_
    · intro a ha
      obtain ⟨g, hg, hgN, rfl⟩ := (mem_imgIn_iff W _).1 ha
      obtain ⟨n, rfl⟩ := hg
      refine mem_centralizer_singleton_iff.2 (actFun_comm_of_comm W ?_)
      exact (Commute.zpow_left (show Commute x t from h.t_x.symm) n).eq
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 (actFun_comm_of_comm W h.t_y.symm))
  intro a ha
  exact (mem_centralizer_singleton_iff.1 (hle ha)).symm

end KSet

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5
