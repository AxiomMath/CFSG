module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Comps
public import CFSG.GH74.GLS.Stage2.Final.ModelLUSyl
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2011CFId

public section

namespace CFSG.GH74.Ivk411

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.L5U5
open CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT (Data411)
open scoped commutatorElement

variable {F : Type} [Field F]

theorem yP_mem_C0 (M : ModelData F) : yP M ∈ C0 M :=
  ⟨M.yK, mem_Dsub.2 rfl, rfl⟩

theorem bs_le_Cg [Finite F] {M : ModelData F} (hG : GoodModel M) : BSsub M ≤ Cg M := by
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Ivk413.bs_comm_C0 hG hc (yP_mem_C0 M)

theorem cent_E_eq_BS [Finite F] {M : ModelData F} (hG : GoodModel M) :
    Cg M ⊓ Subgroup.centralizer ((K1 M ⊔ K2 M : Subgroup (PG M)) : Set (PG M)) = BSsub M := by
  apply le_antisymm
  · rintro c ⟨hc, hcE⟩
    obtain ⟨p, hp⟩ := blockScalar_of_cent_E hG hc (fun e he => by
      have := Subgroup.mem_centralizer_iff.1 hcE e he
      exact this.symm)
    exact ⟨p, hp⟩
  · intro c hc
    refine ⟨bs_le_Cg hG hc, ?_⟩
    show c ∈ Subgroup.centralizer ((K1 M ⊔ K2 M : Subgroup (PG M)) : Set (PG M))
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hle : K1 M ⊔ K2 M ≤ Subgroup.centralizer {c} :=
      sup_le (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
          (Ivk413.bs_comm_C0 hG hc (K1_le_C0 M hx)).symm)
        (fun x hx => Subgroup.mem_centralizer_singleton_iff.2
          (Ivk413.bs_comm_C0 hG hc (K2_le_C0 M hx)).symm)
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle he))

theorem inf_K1_K2 [Finite F] {M : ModelData F} (hG : GoodModel M) (q : ℕ)
    (hSL : HasSL2Model ↥M.H2 (fun r => r = q)) :
    K1 M ⊓ K2 M = Subgroup.zpowers (yP M) := by
  have hc := luComps_PG hG q hSL
  apply le_antisymm
  · rintro x ⟨hx1, hx2⟩
    have : x ∈ (Subgroup.center ↥(K1 M)).map (K1 M).subtype := by
      refine ⟨⟨x, hx1⟩, ?_, rfl⟩
      show (⟨x, hx1⟩ : ↥(K1 M)) ∈ Subgroup.center ↥(K1 M)
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (K1_K2_comm M g.2 hx2)
    rw [hc.cen₁] at this
    exact this
  · rw [Subgroup.zpowers_le]
    exact ⟨⟨_, iota1_negOne M⟩, ⟨_, iota2_negOne M⟩⟩

theorem mkP_diag_mem_EBS [Finite F] {M : ModelData F} {n : ℕ}
    (hU2 : ∀ l : Fˣ, sc2 l ∈ M.U2 ↔ l ^ n = 1)
    {u v : GL (Fin 2) F} (hu : u ∈ M.U2) (hv : v ∈ M.U2) (hK : diagGL u v ∈ M.K4)
    {l : Fˣ} (hl : l ^ n = 1)
    (hdu : Matrix.GeneralLinearGroup.det u = l ^ 2) :
    mkP M ⟨diagGL u v, hK⟩ ∈ K1 M ⊔ K2 M ⊔ BSsub M := by
  have hdet := (M.diagGL_mem_K4_iff.1 hK).2.2
  have hdu' : (u : Matrix (Fin 2) (Fin 2) F).det = (l : F) ^ 2 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdu]; simp
  have hlne : (l : F) ≠ 0 := l.ne_zero
  have hdv : (v : Matrix (Fin 2) (Fin 2) F).det = ((l : F) ^ 2)⁻¹ := by
    rw [hdu'] at hdet
    exact eq_inv_of_mul_eq_one_right hdet
  have hli : sc2 l⁻¹ ∈ M.U2 := (hU2 l⁻¹).2 (by rw [inv_pow, hl, inv_one])
  have hl' : sc2 l ∈ M.U2 := (hU2 l).2 hl
  have hH : sc2 l⁻¹ * u ∈ M.H2 := by
    refine (M.mem_H2 _).2 ⟨M.U2.mul_mem hli hu, ?_⟩
    rw [Units.val_mul, Matrix.det_mul, det_sc2, hdu', Units.val_inv_eq_inv_val,
      inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hlne)]
  have hH' : sc2 l * v ∈ M.H2 := by
    refine (M.mem_H2 _).2 ⟨M.U2.mul_mem hl' hv, ?_⟩
    rw [Units.val_mul, Matrix.det_mul, det_sc2, hdv, mul_inv_cancel₀ (pow_ne_zero 2 hlne)]
  have hbs : diagGL (sc2 l) (sc2 l⁻¹) ∈ M.K4 := by
    refine diag_sc2_mem_K4 M hl' hli ?_
    rw [Units.val_inv_eq_inv_val, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hlne)]
  have hhh : diagGL (sc2 l⁻¹ * u) (sc2 l * v) ∈ M.K4 := diagGL_mem_K4_of_H2 M ⟨_, hH⟩ ⟨_, hH'⟩
  have heq : (⟨diagGL u v, hK⟩ : ↥M.K4) =
      ⟨diagGL (sc2 l) (sc2 l⁻¹), hbs⟩ * ⟨diagGL (sc2 l⁻¹ * u) (sc2 l * v), hhh⟩ := by
    apply Subtype.ext
    show diagGL u v = diagGL (sc2 l) (sc2 l⁻¹) * diagGL (sc2 l⁻¹ * u) (sc2 l * v)
    rw [diagGL_mul, ← mul_assoc, ← mul_assoc, sc2_mul, sc2_mul, mul_inv_cancel, inv_mul_cancel,
      sc2_one, one_mul, one_mul]
  have h1 : mkP M ⟨diagGL (sc2 l⁻¹ * u) (sc2 l * v), hhh⟩ =
      iota1 M ⟨_, hH⟩ * iota2 M ⟨_, hH'⟩ :=
    (iota_mul_eq_mkP_diag M ⟨_, hH⟩ ⟨_, hH'⟩ hhh).symm
  rw [heq, map_mul, h1]
  have hmem : mkP M ⟨diagGL (sc2 l) (sc2 l⁻¹), hbs⟩ ∈ BSsub M :=
    ⟨⟨(l, l⁻¹), hbs⟩, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmem)
    (Subgroup.mem_sup_left (Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩))


theorem comm_tP_mem [Finite F] {M : ModelData F} (hG : GoodModel M) {n : ℕ}
    (hU2 : ∀ l : Fˣ, sc2 l ∈ M.U2 ↔ l ^ n = 1)
    (hdetn : ∀ a ∈ M.U2, ((a : Matrix (Fin 2) (Fin 2) F).det) ^ n = 1)
    {c : PG M} (hc : c ∈ C0 M) : ⁅tP M, c⁆ ∈ K1 M ⊔ K2 M ⊔ BSsub M := by
  have h2 := hG.two_ne_zero
  obtain ⟨d, hd, rfl⟩ := hc
  obtain ⟨a, b, hab, haU, hbU, hdet⟩ :=
    M.exists_diagGL_of_comm h2 d.2 (congrArg Subtype.val (mem_Dsub.1 hd))
  have hcomm : ((⁅M.wK, d⁆ : ↥M.K4) : GL (Fin 4) F) = diagGL (b * a⁻¹) (a * b⁻¹) := by
    have e1 : ((⁅M.wK, d⁆ : ↥M.K4) : GL (Fin 4) F) =
        (M.wK : GL (Fin 4) F) * (d : GL (Fin 4) F) * (M.wK : GL (Fin 4) F)⁻¹ *
          (d : GL (Fin 4) F)⁻¹ := rfl
    rw [e1, hab, coe_wK, swapGL_inv, swapGL_mul_diagGL_mul_swapGL, diagGL_inv, diagGL_mul]
  have hK : diagGL (b * a⁻¹) (a * b⁻¹) ∈ M.K4 := hcomm ▸ (⁅M.wK, d⁆ : ↥M.K4).2
  set da : Fˣ := Matrix.GeneralLinearGroup.det a with hda
  set db : Fˣ := Matrix.GeneralLinearGroup.det b with hdb
  have hdadb : da * db = 1 := by
    apply Units.ext
    rw [Units.val_mul, hda, hdb, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.GeneralLinearGroup.val_det_apply]
    exact hdet
  have hdbeq : db = da⁻¹ := eq_inv_of_mul_eq_one_right hdadb
  have hdan : da ^ n = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hda, Matrix.GeneralLinearGroup.val_det_apply]
    exact hdetn a haU
  have hl : (da⁻¹) ^ n = 1 := by rw [inv_pow, hdan, inv_one]
  have hu : b * a⁻¹ ∈ M.U2 := M.U2.mul_mem hbU (M.U2.inv_mem haU)
  have hv : a * b⁻¹ ∈ M.U2 := M.U2.mul_mem haU (M.U2.inv_mem hbU)
  have hdu : Matrix.GeneralLinearGroup.det (b * a⁻¹) = (da⁻¹) ^ 2 := by
    rw [map_mul, map_inv, ← hda, ← hdb, hdbeq, sq]
  have key := mkP_diag_mem_EBS hU2 hu hv hK hl hdu
  have hrew : (⁅M.wK, d⁆ : ↥M.K4) = ⟨diagGL (b * a⁻¹) (a * b⁻¹), hK⟩ := Subtype.ext hcomm
  have hcP : ⁅tP M, mkP M d⁆ = mkP M ⁅M.wK, d⁆ := by
    rw [map_commutatorElement]; rfl
  rw [hcP, hrew]
  exact key


theorem comm_mem_of_index_two {G : Type*} [Group G] {C C0 A : Subgroup G} {W : G}
    (hW : W ∈ C) (hW2 : W * W = 1) (hC : ∀ g ∈ C, g ∈ C0 ∨ W * g ∈ C0)
    (hAn : ∀ g ∈ C, ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (h00 : ∀ x ∈ C0, ∀ y ∈ C0, ⁅x, y⁆ ∈ A) (hW0 : ∀ y ∈ C0, ⁅W, y⁆ ∈ A) :
    ∀ x ∈ C, ∀ y ∈ C, ⁅x, y⁆ ∈ A := by
  have step1 : ∀ c ∈ C0, ∀ y ∈ C0, ⁅W * c, y⁆ ∈ A := by
    intro c hc y hy
    have e : ⁅W * c, y⁆ = (W * ⁅c, y⁆ * W⁻¹) * ⁅W, y⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact A.mul_mem (hAn W hW _ (h00 c hc y hy)) (hW0 y hy)
  have step2 : ∀ x ∈ C, ∀ y ∈ C0, ⁅x, y⁆ ∈ A := by
    intro x hx y hy
    rcases hC x hx with h | h
    · exact h00 x h y hy
    · have hxe : x = W * (W * x) := by rw [← mul_assoc, hW2, one_mul]
      rw [hxe]
      exact step1 _ h y hy
  have step3 : ∀ x ∈ C, ⁅W, x⁆ ∈ A := by
    intro x hx
    rcases hC x hx with h | h
    · exact hW0 x h
    · have hxe : x = W * (W * x) := by rw [← mul_assoc, hW2, one_mul]
      have e : ⁅W, W * (W * x)⁆ = W * ⁅W, W * x⁆ * W⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [hxe, e]
      exact hAn W hW _ (hW0 _ h)
  intro x hx y hy
  rcases hC y hy with h | h
  · exact step2 x hx y h
  · have hye : y = W * (W * y) := by rw [← mul_assoc, hW2, one_mul]
    have e : ⁅x, W * (W * y)⁆ = ⁅x, W⁆ * (W * ⁅x, W * y⁆ * W⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [hye, e]
    refine A.mul_mem ?_ (hAn W hW _ (step2 x hx _ h))
    rw [← commutatorElement_inv]
    exact A.inv_mem (step3 x hx)

theorem E_conj [Finite F] {M : ModelData F} (hG : GoodModel M) {g e : PG M} (hg : g ∈ Cg M)
    (he : e ∈ K1 M ⊔ K2 M) : g * e * g⁻¹ ∈ K1 M ⊔ K2 M := by
  have hn := layer_normal_Cg M hG.two_ne_zero hG.qs
  have hEC : K1 M ⊔ K2 M ≤ Cg M := sup_le (K1_le_Cg M) (K2_le_Cg M)
  have h1 : (⟨e, hEC he⟩ : ↥(Cg M)) ∈ (K1 M ⊔ K2 M).subgroupOf (Cg M) := he
  exact hn.conj_mem _ h1 ⟨g, hg⟩

theorem BS_conj [Finite F] {M : ModelData F} (hG : GoodModel M) {g c : PG M} (hg : g ∈ Cg M)
    (hc : c ∈ BSsub M) : g * c * g⁻¹ ∈ BSsub M := by
  rw [← cent_E_eq_BS hG] at hc ⊢
  obtain ⟨hcC, hcE⟩ := hc
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hcC) (Subgroup.inv_mem _ hg), ?_⟩
  show _ ∈ Subgroup.centralizer ((K1 M ⊔ K2 M : Subgroup (PG M)) : Set (PG M))
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  have h1 := E_conj hG (Subgroup.inv_mem _ hg) he
  rw [inv_inv] at h1
  have h2 := Subgroup.mem_centralizer_iff.1 hcE _ h1
  calc e * (g * c * g⁻¹) = g * ((g⁻¹ * e * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * e * g)) * g⁻¹ := by rw [h2]
    _ = (g * c * g⁻¹) * e := by group

theorem A_conj [Finite F] {M : ModelData F} (hG : GoodModel M) {g a : PG M} (hg : g ∈ Cg M)
    (ha : a ∈ K1 M ⊔ K2 M ⊔ BSsub M) : g * a * g⁻¹ ∈ K1 M ⊔ K2 M ⊔ BSsub M := by
  have hle : K1 M ⊔ K2 M ⊔ BSsub M ≤
      (K1 M ⊔ K2 M ⊔ BSsub M).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun e he => Subgroup.mem_sup_left (E_conj hG hg he))
      (fun c hc => Subgroup.mem_sup_right (BS_conj hG hg hc))
  simpa [MulAut.conj_apply] using hle ha

theorem comm_Cg_mem [Finite F] {M : ModelData F} (hG : GoodModel M) {n : ℕ}
    (hU2 : ∀ l : Fˣ, sc2 l ∈ M.U2 ↔ l ^ n = 1)
    (hdetn : ∀ a ∈ M.U2, ((a : Matrix (Fin 2) (Fin 2) F).det) ^ n = 1) :
    ∀ x ∈ Cg M, ∀ y ∈ Cg M, ⁅x, y⁆ ∈ K1 M ⊔ K2 M ⊔ BSsub M := by
  have h2 := hG.two_ne_zero
  refine comm_mem_of_index_two (W := tP M) (tP_mem_Cg M) ?_ ?_
    (fun g hg a ha => A_conj hG hg ha) ?_ (fun y hy => comm_tP_mem hG hU2 hdetn hy)
  · show mkP M M.wK * mkP M M.wK = 1
    rw [← map_mul, wK_mul_self, map_one]
  · intro g hg
    have hg' : g ∈ (Nsub M).map (mkP M) := by rw [← centralizer_yP]; exact hg
    obtain ⟨n, hn, rfl⟩ := hg'
    rcases (mem_Nsub_iff_D M).1 hn with h | h
    · exact Or.inl ⟨n, h, rfl⟩
    · refine Or.inr ⟨M.wK * n, h, ?_⟩
      show mkP M (M.wK * n) = mkP M M.wK * mkP M n
      rw [map_mul]
  · intro x hx y hy
    exact Subgroup.mem_sup_left (comm_mem_E M h2 hx hy)


theorem bs_mul_comm [Finite F] (M : ModelData F) {a b : PG M} (ha : a ∈ BSsub M)
    (hb : b ∈ BSsub M) : a * b = b * a := by
  have hcyc : IsCyclic ↥(BSsub M) := isCyclic_BSsub M
  let _inst : CommGroup ↥(BSsub M) := IsCyclic.commGroup
  have := mul_comm (⟨a, ha⟩ : ↥(BSsub M)) ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem fitting_map_eq [Finite F] {M : ModelData F} (hG : GoodModel M) :
    (fittingSubgroup ↥(Cg M)).map (Cg M).subtype = BSsub M := by
  rw [← cent_E_eq_BS hG]
  have hEz : (layer ↥(Cg M)).map (Cg M).subtype = K1 M ⊔ K2 M :=
    layer_map_eq M hG.two_ne_zero hG.qs
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    refine ⟨f.2, ?_⟩
    show (f : PG M) ∈ Subgroup.centralizer ((K1 M ⊔ K2 M : Subgroup (PG M)) : Set (PG M))
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    rw [← hEz] at he
    obtain ⟨l, hl, rfl⟩ := he
    have hc := Subgroup.commutator_mem_commutator hf hl
    rw [CFSG.LocalCores.fitting_layer_commute, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at hc
    exact (congrArg Subtype.val hc).symm
  · rintro z ⟨hzC, hzE⟩
    have hzB : z ∈ BSsub M := by rw [← cent_E_eq_BS hG]; exact ⟨hzC, hzE⟩
    let N : Subgroup ↥(Cg M) := (BSsub M).subgroupOf (Cg M)
    have hNn : N.Normal := ⟨fun n hn g => by
      show ((g * n * g⁻¹ : ↥(Cg M)) : PG M) ∈ BSsub M
      exact BS_conj hG g.2 hn⟩
    have hNc : IsMulCommutative ↥N := ⟨⟨fun a b => Subtype.ext (Subtype.ext
      (bs_mul_comm M a.2 b.2))⟩⟩
    have hNnil : Group.IsNilpotent ↥N := CommGroup.isNilpotent
    have hle : N ≤ fittingSubgroup ↥(Cg M) := le_sSup ⟨hNn, hNnil⟩
    exact ⟨⟨z, hzC⟩, hle hzB, rfl⟩

theorem generalizedFitting_map_eq [Finite F] {M : ModelData F} (hG : GoodModel M) :
    (generalizedFitting ↥(Cg M)).map (Cg M).subtype = K1 M ⊔ K2 M ⊔ BSsub M := by
  have hEz : (layer ↥(Cg M)).map (Cg M).subtype = K1 M ⊔ K2 M :=
    layer_map_eq M hG.two_ne_zero hG.qs
  simp only [CFSG.generalizedFitting.eq_sup]
  rw [Subgroup.map_sup, fitting_map_eq hG, hEz, sup_comm]

theorem data411_PG [Finite F] {M : ModelData F} (hG : GoodModel M) {q n : ℕ}
    (hSL : HasSL2Model ↥M.H2 (fun r => r = q))
    (hU2 : ∀ l : Fˣ, sc2 l ∈ M.U2 ↔ l ^ n = 1)
    (hdetn : ∀ a ∈ M.U2, ((a : Matrix (Fin 2) (Fin 2) F).det) ^ n = 1) :
    Stage2.Final.Thm6.L2011.CFT.Data411 (yP M) q (K1 M) (K2 M) := by
  have hc := luComps_PG hG q hSL
  have hEz : IVK.Ez (yP M) = K1 M ⊔ K2 M := layer_map_eq M hG.two_ne_zero hG.qs
  have hFs : (generalizedFitting ↥(Subgroup.centralizer ({yP M} : Set (PG M)))).map
      (Subgroup.centralizer ({yP M} : Set (PG M))).subtype = K1 M ⊔ K2 M ⊔ BSsub M :=
    generalizedFitting_map_eq hG
  refine ⟨hEz, hc.sl₁, hc.sl₂, fun a ha b hb => K1_K2_comm M ha hb, inf_K1_K2 hG q hSL,
    ?_, ?_, ?_⟩
  · intro a ha b hb
    rw [hFs]
    exact comm_Cg_mem hG hU2 hdetn a ha b hb
  · rw [hFs, hEz]
    have := cent_E_eq_BS hG
    rw [this]
  · intro a ha b hb
    rw [hEz, cent_E_eq_BS hG] at ha hb
    exact bs_mul_comm M ha hb


open CFSG.GH74.GLS.Stage2.Final.Thm6.L2011.CFT (Data411)

end CFSG.GH74.Ivk411
