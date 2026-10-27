module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3WTwo

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open scoped commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

omit [Finite G] in
theorem η_commutator_mem_Zp_iff (d : Data G h) {u a : hypSU h 2 1}
    (hu : u ∈ hypUnitriangular h 2 1) (ha : a ∈ hypUnitriangular h 2 1) :
    ⁅d.η u, d.η a⁆ ∈ d.Zp ↔ ⁅u, a⁆ ∈ ZPsub h := by
  rw [← map_commutatorElement]
  refine d.η_mem_pull_iff ZPsub_le_U ?_
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hu ha) (inv_mem hu)) (inv_mem ha)

omit [Finite G] in
theorem mem_A₃_of_commutator_A₁ (d : Data G h) {p : G} (hp : p ∈ d.P)
    (hc : ∀ a ∈ d.A₁, ⁅p, a⁆ ∈ d.Zp) : p ∈ d.A₃ := by
  obtain ⟨u, hu, rfl⟩ := hp
  refine ⟨u, mem_Ssub_of_commutator_Vsub hu fun a ha => ?_, rfl⟩
  exact (d.η_commutator_mem_Zp_iff hu (Vsub_le_Ssub.trans Ssub_le_Usub ha)).1
    (hc _ ⟨a, ha, rfl⟩)

omit [Finite G] in
theorem mem_A₁_of_commutator_A₃ (d : Data G h) {p : G} (hp : p ∈ d.A₃)
    (hc : ∀ a ∈ d.A₃, ⁅p, a⁆ ∈ d.Zp) : p ∈ d.A₁ := by
  obtain ⟨u, hu, rfl⟩ := hp
  refine ⟨u, mem_Vsub_of_commutator_Ssub hu fun a ha => ?_, rfl⟩
  exact (d.η_commutator_mem_Zp_iff (Ssub_le_Usub hu) (Ssub_le_Usub ha)).1 (hc _ ⟨a, ha, rfl⟩)

theorem Hyp.V_inf_P (hd : d.Hyp) : d.V ⊓ d.P = d.Zp := by
  refine le_antisymm (fun x hx => ?_) (le_inf hd.Zp_le_V d.Zp_le_P)
  rw [← hd.V_inf_centralizer_t]
  exact ⟨hx.1, hd.L_le_centralizer (d.P_le_L hx.2)⟩

theorem Hyp.FP_le_centralizer_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊔ d.P ≤ centralizer (d.V : Set G) := by
  have hFc := hd.F_comm hGMS
  have hVP : d.V ≤ centralizer (d.P : Set G) := hd.V_le_CB₄I₃.trans hd.CB₄I₃_le_centralizer_P
  exact sup_le (fun a ha => mem_centralizer_iff.2 fun w hw => hFc w (d.V_le_F hw) a ha)
    (fun p hp => mem_centralizer_iff.2 fun w hw => (mem_centralizer_iff.1 (hVP hw) p hp).symm)

theorem Hyp.commutator_mem_F_FP (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x y : G} (hx : x ∈ d.F) (hy : y ∈ d.F ⊔ d.P) : ⁅x, y⁆ ∈ d.F := by
  have hyN : y ∈ normalizer (d.F : Set G) :=
    sup_le (le_normalizer : d.F ≤ normalizer (d.F : Set G)) (hd.P_le_normalizer_F hGMS) hy
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  refine mul_mem hx ?_
  rw [← mul_assoc]
  exact (mem_normalizer_iff.1 hyN _).1 (inv_mem hx)

theorem Hyp.cr_commutator (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {x y : G}
    (hx : x ∈ d.F) (hy : y ∈ d.P) :
    ⁅x, y⁆⁻¹ * d.t * ⁅x, y⁆ * d.t = ⁅x⁻¹ * d.t * x * d.t, y⁆ := by
  have hyC : y ∈ centralizer ({d.t} : Set G) := hd.L_le_centralizer (d.P_le_L hy)
  have hyx : y * x⁻¹ * y⁻¹ ∈ d.F :=
    (mem_normalizer_iff.1 (hd.P_le_normalizer_F hGMS hy) _).1 (inv_mem hx)
  have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
  rw [e, hd.cr_F_mul hx hyx, d.cr_conj hyC, hd.cr_F_inv hx, commutatorElement_def]
  group

theorem Hyp.commutator_F_I₄_mem (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {c y : G} (hc : c ∈ d.F ⊓ centralizer (d.I₄ : Set G)) (hy : y ∈ d.P) :
    ∃ v ∈ d.V, v⁻¹ * ⁅c, y⁆ ∈ d.A₁ := by
  have hcr := hd.cr_F_I₄_mem hc
  have hZ₂ : c⁻¹ * d.t * c * d.t ∈ d.Z₂p := by
    rw [hd.Z₂p_eq.1]
    exact mem_sup_right hcr
  have hmem : ⁅c, y⁆⁻¹ * d.t * ⁅c, y⁆ * d.t ∈ d.Zp := by
    rw [hd.cr_commutator hGMS hc.1 hy]
    exact (d.mem_Z₂p_iff hcr.1).1 hZ₂ y hy
  obtain ⟨v, hv, hvt⟩ := hd.exists_V_cr_eq hmem
  exact ⟨v, hv, hd.inv_mul_mem_A₁_of_cr_eq hGMS (d.V_le_F hv)
    (hd.commutator_mem_F_FP hGMS hc.1 (mem_sup_right hy)) hvt⟩

theorem Hyp.card_V_sup_A₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card (d.V ⊔ d.A₂ : Subgroup G) = (2 ^ f) ^ 8 := by
  have hN : d.A₂ ≤ normalizer (d.V : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ ((hd.FP_le_centralizer_V hGMS)
      (mem_sup_right (d.A₂_le_P ha)))
  have hinf : d.V ⊓ d.A₂ = d.Zp := le_antisymm
    ((inf_le_inf_left _ d.A₂_le_P).trans hd.V_inf_P.le) (le_inf hd.Zp_le_V d.Zp_le_A₂)
  have h1 := Common.card_sup_mul_card_inf_eq hN
  rw [hinf, hd.card_V, d.card_A₂, d.card_Zp] at h1
  have hq : 0 < 2 ^ f := by positivity
  have : (2 ^ f) ^ 8 * 2 ^ f = (2 ^ f) ^ 2 * (2 ^ f) ^ 7 := by ring
  exact Nat.eq_of_mul_eq_mul_right hq (h1.trans this.symm)

theorem Hyp.eq_V_sup_A₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {E : Subgroup G} (hVE : d.V ≤ E) (hEP : E ≤ d.V ⊔ d.P) (hE : ElemAbMod d.V E)
    (hcard : Nat.card E = (2 ^ f) ^ 8) : E = d.V ⊔ d.A₂ := by
  have hVc := hd.FP_le_centralizer_V hGMS
  have hPV : d.P ≤ normalizer (d.V : Set G) := fun p hp =>
    Subgroup.centralizer_le_normalizer _ (hVc (mem_sup_right hp))
  have hEeq : E = d.V ⊔ (E ⊓ d.P) := by
    refine le_antisymm (fun x hx => ?_) (sup_le hVE inf_le_left)
    obtain ⟨v, hv, p, hp, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hPV (hEP hx)
    refine mul_mem (mem_sup_left hv) (mem_sup_right ⟨?_, hp⟩)
    have := mul_mem (inv_mem (hVE hv)) hx
    rwa [inv_mul_cancel_left] at this
  have hEP' : ElemAbMod d.Zp (E ⊓ d.P) := by
    rw [← hd.V_inf_P]
    refine ⟨fun x hx => Subgroup.mem_inf.2 ⟨hE.1 x hx.1, mul_mem hx.2 hx.2⟩,
      fun x hx y hy => Subgroup.mem_inf.2 ⟨hE.2 x hx.1 y hy.1, ?_⟩⟩
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx.2 hy.2) (inv_mem hx.2)) (inv_mem hy.2)
  have hN : E ⊓ d.P ≤ normalizer (d.V : Set G) := inf_le_right.trans hPV
  have h1 := Common.card_sup_mul_card_inf_eq hN
  have hinf : d.V ⊓ (E ⊓ d.P) = d.Zp := by
    rw [← inf_assoc, inf_eq_left.2 hVE, hd.V_inf_P]
  rw [← hEeq, hinf, hcard, hd.card_V, d.card_Zp] at h1
  have h7 : Nat.card (E ⊓ d.P : Subgroup G) = (2 ^ f) ^ 7 := by
    have hq : 0 < (2 ^ f) ^ 2 := by positivity
    refine Nat.eq_of_mul_eq_mul_left hq ?_
    rw [← h1]
    ring
  have hA := (d.sec2_2_modZp inf_le_right hEP').2.2 h7.ge
  rw [hEeq, hA]

theorem Hyp.elemAbMod_V_sup_A₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ElemAbMod d.V (d.V ⊔ d.A₂) := by
  have hle : d.V ⊔ d.A₂ ≤ d.F ⊔ d.P :=
    sup_le (d.V_le_F.trans le_sup_left) (d.A₂_le_P.trans le_sup_right)
  have hcen : ∀ v ∈ d.V, ∀ y ∈ d.V ⊔ d.A₂, v * y = y * v := fun v hv y hy =>
    mem_centralizer_iff.1 (hd.FP_le_centralizer_V hGMS (hle hy)) v hv
  have hAN : d.A₂ ≤ normalizer (d.V : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (hd.FP_le_centralizer_V hGMS (hle (mem_sup_right ha)))
  have hcomm : ∀ v ∈ d.V, ∀ x y : G, x ∈ d.V ⊔ d.A₂ → y ∈ d.V ⊔ d.A₂ →
      ⁅v * x, y⁆ = ⁅x, y⁆ := by
    intro v hv x y hx hy
    have h1 : v * (x * y * x⁻¹) = (x * y * x⁻¹) * v :=
      hcen v hv _ (mul_mem (mul_mem hx hy) (inv_mem hx))
    rw [commutatorElement_def, commutatorElement_def]
    calc v * x * y * (v * x)⁻¹ * y⁻¹ = v * (x * y * x⁻¹) * v⁻¹ * y⁻¹ := by group
      _ = (x * y * x⁻¹) * v * v⁻¹ * y⁻¹ := by rw [h1]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨v, hv, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hAN hx
    have e : v * a * (v * a) = (v * v) * (a * a) := by
      rw [show v * a * (v * a) = v * (a * v) * a by group, ← hcen v hv a (mem_sup_right ha)]
      group
    rw [e, hd.mul_self_eq_one_of_mem_V hGMS hv, one_mul]
    exact hd.Zp_le_V (d.elemAbMod_Zp_A₂.1 a ha)
  · obtain ⟨v, hv, a, ha, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hAN hx
    obtain ⟨w, hw, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hAN hy
    rw [hcomm v hv a (w * b) (mem_sup_right ha) hy, ← commutatorElement_inv,
      hcomm w hw b a (mem_sup_right hb) (mem_sup_right ha), commutatorElement_inv]
    exact hd.Zp_le_V (d.elemAbMod_Zp_A₂.2 a ha b hb)

theorem Hyp.commutator_F_I₄_A₂_mem (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {c a : G} (hc : c ∈ d.F ⊓ centralizer (d.I₄ : Set G)) (ha : a ∈ d.A₂) :
    ∃ v ∈ d.V, ∃ z ∈ d.P ⊓ centralizer (d.I₄ : Set G), ⁅c, a⁆ = v * z := by
  have hVc := hd.FP_le_centralizer_V hGMS
  have hcV : ∀ v ∈ d.V, c * v * c⁻¹ = v := fun v hv => by
    rw [← mem_centralizer_iff.1 (hVc (mem_sup_left hc.1)) v hv, mul_inv_cancel_right]
  have hPV : d.P ≤ normalizer (d.V : Set G) := fun p hp =>
    Subgroup.centralizer_le_normalizer _ (hVc (mem_sup_right hp))
  set φ : G →* G := (MulAut.conj c).toMonoidHom with hφ
  have hφV : d.V.map φ = d.V := by
    refine le_antisymm ?_ fun v hv => ⟨v, hv, hcV v hv⟩
    rintro _ ⟨v, hv, rfl⟩
    change c * v * c⁻¹ ∈ d.V
    rw [hcV v hv]
    exact hv
  have hφVP : ∀ x ∈ d.V ⊔ d.P, c * x * c⁻¹ ∈ d.V ⊔ d.P := by
    intro x hx
    obtain ⟨v, hv, p, hp, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hPV hx
    obtain ⟨w, hw, hwa⟩ := hd.commutator_F_I₄_mem hGMS hc hp
    have e : c * (v * p) * c⁻¹ = v * w * (w⁻¹ * ⁅c, p⁆) * p := by
      rw [show c * (v * p) * c⁻¹ = (c * v * c⁻¹) * ⁅c, p⁆ * p by
        rw [commutatorElement_def]; group, hcV v hv]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (mem_sup_left hv) (mem_sup_left hw))
      (mem_sup_right (d.A₁_le_P hwa))) (mem_sup_right hp)
  have h1 : d.V ≤ (d.V ⊔ d.A₂).map φ := by
    calc d.V = d.V.map φ := hφV.symm
      _ ≤ (d.V ⊔ d.A₂).map φ := map_mono le_sup_left
  have h2 : (d.V ⊔ d.A₂).map φ ≤ d.V ⊔ d.P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hφVP x (sup_le_sup_left d.A₂_le_P _ hx)
  have h3 : ElemAbMod d.V ((d.V ⊔ d.A₂).map φ) := by
    have := (hd.elemAbMod_V_sup_A₂ hGMS).map φ
    rwa [hφV] at this
  have h4 : Nat.card ((d.V ⊔ d.A₂).map φ) = (2 ^ f) ^ 8 := by
    rw [card_map_of_injective (MulAut.conj c).injective, hd.card_V_sup_A₂ hGMS]
  have hE := hd.eq_V_sup_A₂ hGMS h1 h2 h3 h4
  have hca : c * a * c⁻¹ ∈ d.V ⊔ d.A₂ := by
    rw [← hE]
    exact ⟨a, mem_sup_right ha, rfl⟩
  have hmem : ⁅c, a⁆ ∈ d.V ⊔ d.A₂ := by
    rw [commutatorElement_def]
    exact mul_mem hca (inv_mem (mem_sup_right ha))
  have hAN : d.A₂ ≤ normalizer (d.V : Set G) := fun a' ha' => hPV (d.A₂_le_P ha')
  obtain ⟨v, hv, a', ha', hva⟩ := exists_mul_of_mem_sup_of_le_normalizer hAN hmem
  have ha'F : a' ∈ d.F := by
    have := mul_mem (inv_mem (d.V_le_F hv)) (hd.commutator_mem_F_FP hGMS hc.1
      (mem_sup_right (d.A₂_le_P ha)))
    rwa [hva, inv_mul_cancel_left] at this
  have ha'Z : a' ∈ d.Z₂p := by
    rw [d.Z₂p_eq, ← hd.F_inf_P hGMS]
    exact ⟨⟨ha'F, d.A₂_le_P ha'⟩, ha'⟩
  rw [hd.Z₂p_eq.1] at ha'Z
  obtain ⟨z₀, hz₀, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer d.C₄_le_normalizer_Zp ha'Z
  exact ⟨v * z₀, mul_mem hv (hd.Zp_le_V hz₀), z, hz, by rw [hva, mul_assoc]⟩

theorem Hyp.commutator_F_I₄_C₁_mem (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {c y : G} (hc : c ∈ d.F ⊓ centralizer (d.I₄ : Set G))
    (hy : y ∈ d.P ⊓ centralizer (d.I₁ : Set G)) : ⁅c, y⁆ ∈ d.V := by
  have hVc := hd.FP_le_centralizer_V hGMS
  obtain ⟨i, hi, -, hgen⟩ := d.exists_I₄_generic hd.two_le
  obtain ⟨y', hy', rfl⟩ := hgen y hy
  have hy'A : y' ∈ d.A₂ := (d.sec2_1_two hd.two_le).2.2.2.2.1.1 ▸ mem_sup_right hy'
  obtain ⟨v, hv, z, hz, hvz⟩ := hd.commutator_F_I₄_A₂_mem hGMS hc hy'A
  have hgP : i * y' * i⁻¹ * y'⁻¹ ∈ d.P :=
    mul_mem ((mem_normalizer_iff.1 (d.I_le_normalizer_P (d.I₄_le_I hi)) y').1 hy'.1)
      (inv_mem hy'.1)
  have hvg : v * (i * y' * i⁻¹ * y'⁻¹) = (i * y' * i⁻¹ * y'⁻¹) * v :=
    mem_centralizer_iff.1 (hVc (mem_sup_right hgP)) v hv
  rw [commutator_conj_comm (mem_centralizer_iff.1 hc.2 i hi) (mem_centralizer_iff.1 hz.2 i hi)
    hvz hvg]
  have hZ₂ : z ∈ d.Z₂p := by
    rw [hd.Z₂p_eq.1]
    exact mem_sup_right hz
  refine mul_mem (mul_mem ((mem_normalizer_iff.1 (hd.I_le_normalizer_V (d.I₄_le_I hi)) v).1 hv)
    (hd.Zp_le_V ((d.mem_Z₂p_iff hz.1).1 hZ₂ _ hgP))) (inv_mem hv)

theorem Hyp.commutator_F_I₄_mem_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {c y : G} (hc : c ∈ d.F ⊓ centralizer (d.I₄ : Set G)) (hy : y ∈ d.F ⊔ d.P) :
    ⁅c, y⁆ ∈ d.V := by
  have hVc := hd.FP_le_centralizer_V hGMS
  have hFc := hd.F_comm hGMS
  have hN : ∀ y ∈ d.F ⊔ d.P, y ∈ normalizer (d.V : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (hVc hy)
  have hcomm : ∀ y : G, y * c = c * y → ⁅c, y⁆ ∈ d.V := fun y hyc => by
    rw [commutatorElement_def, ← hyc, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hF : d.F ≤ commNormSub d.V c := fun y hy =>
    ⟨hN y (mem_sup_left hy), hcomm y (hFc y hy c hc.1)⟩
  have hA₃ : d.A₃ ≤ commNormSub d.V c := fun y hy =>
    ⟨hN y (mem_sup_right (d.A₃_le_P hy)), hcomm y (mem_centralizer_iff.1
      (hd.F_le_centralizer_A₃ hc.1) y hy)⟩
  have hC₁ : d.P ⊓ centralizer (d.I₁ : Set G) ≤ commNormSub d.V c := fun y hy =>
    ⟨hN y (mem_sup_right hy.1), hd.commutator_F_I₄_C₁_mem hGMS hc hy⟩
  have hP : d.P ≤ commNormSub d.V c := by
    rw [((d.sec2_1_two hd.two_le).2.2.2.2.2.2.2.2.2.2.2).1]
    exact sup_le hA₃ hC₁
  exact ((sup_le hF hP) hy).2

theorem Hyp.mem_Z₂_FP_iff (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {x : G} :
    x ∈ (Subgroup.upperCentralSeries ↥(d.F ⊔ d.P) 2).map (d.F ⊔ d.P).subtype ↔
      x ∈ d.F ⊔ d.P ∧ ∀ y ∈ d.F ⊔ d.P, ⁅x, y⁆ ∈ d.V := by
  rw [mem_map_upperCentralSeries_two, hd.centerIn_FP hGMS]

theorem Hyp.W_le_Z₂_FP (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.W ≤ (Subgroup.upperCentralSeries ↥(d.F ⊔ d.P) 2).map (d.F ⊔ d.P).subtype := by
  have hVc := hd.FP_le_centralizer_V hGMS
  rw [hd.W_eq hGMS]
  refine sup_le (fun v hv => (hd.mem_Z₂_FP_iff hGMS).2 ⟨d.V_le_FP hv, fun y hy => ?_⟩)
    fun c hc => (hd.mem_Z₂_FP_iff hGMS).2 ⟨mem_sup_left hc.1,
      fun y hy => hd.commutator_F_I₄_mem_V hGMS hc hy⟩
  rw [commutatorElement_def, mem_centralizer_iff.1 (hVc hy) v hv, mul_inv_cancel_right,
    mul_inv_cancel]
  exact one_mem _

theorem Hyp.Z₂_FP_le_W (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    (Subgroup.upperCentralSeries ↥(d.F ⊔ d.P) 2).map (d.F ⊔ d.P).subtype ≤ d.W := by
  have hFc := hd.F_comm hGMS
  have hPA₁ : d.P ≤ normalizer (d.A₁ : Set G) := fun p hp =>
    hd.normalizer_B₁_le_normalizer_A₁ (hd.T_le_normalizer_B₁ (hd.P_le hp))
  have hPA₃ : d.P ≤ normalizer (d.A₃ : Set G) := fun p hp =>
    hd.normalizer_B₁_le_normalizer_A₃ (hd.T_le_normalizer_B₁ (hd.P_le hp))
  intro x hx
  obtain ⟨hxFP, hxc⟩ := (hd.mem_Z₂_FP_iff hGMS).1 hx
  obtain ⟨a, ha, p, hp, rfl⟩ := hd.exists_mul_of_mem_FP hGMS hxFP
  have hpA₃ : p ∈ d.A₃ := by
    refine d.mem_A₃_of_commutator_A₁ hp fun b hb => ?_
    obtain ⟨g, hg, hgb⟩ := hd.exists_F_cr_eq hb
    have hpg : p * g * p⁻¹ ∈ d.F := (mem_normalizer_iff.1 (hd.P_le_normalizer_F hGMS hp) g).1 hg
    have e1 : ⁅a * p, g⁆ = ⁅p, g⁆ := by
      have h1 : a * (p * g * p⁻¹) = (p * g * p⁻¹) * a := hFc a ha _ hpg
      rw [commutatorElement_def, commutatorElement_def]
      calc a * p * g * (a * p)⁻¹ * g⁻¹ = a * (p * g * p⁻¹) * a⁻¹ * g⁻¹ := by group
        _ = p * g * p⁻¹ * g⁻¹ := by rw [h1]; group
    have hV : ⁅p, g⁆ ∈ d.V := e1 ▸ hxc g (mem_sup_left hg)
    have hcr := hd.cr_mem ((hd.V_le_CB₄I₃.trans d.CB₄I₃_le) hV)
    have hpC : p ∈ centralizer ({d.t} : Set G) := hd.L_le_centralizer (d.P_le_L hp)
    have e2 : ⁅p, g⁆⁻¹ * d.t * ⁅p, g⁆ * d.t = ⁅p, b⁆ := by
      have e : ⁅p, g⁆ = (p * g * p⁻¹) * g⁻¹ := by rw [commutatorElement_def]
      rw [e, hd.cr_F_mul hpg (inv_mem hg), d.cr_conj hpC, hd.cr_F_inv hg, hgb,
        commutatorElement_def]
    rwa [e2] at hcr
  have hpA₁ : p ∈ d.A₁ := by
    refine d.mem_A₁_of_commutator_A₃ hpA₃ fun a' ha' => ?_
    have hpa : p * a' * p⁻¹ ∈ d.A₃ := (mem_normalizer_iff.1 (hPA₃ hp) a').1 ha'
    have e1 : ⁅a * p, a'⁆ = ⁅p, a'⁆ := by
      have h1 : (p * a' * p⁻¹) * a = a * (p * a' * p⁻¹) :=
        mem_centralizer_iff.1 (hd.F_le_centralizer_A₃ ha) _ hpa
      rw [commutatorElement_def, commutatorElement_def]
      calc a * p * a' * (a * p)⁻¹ * a'⁻¹ = a * (p * a' * p⁻¹) * a⁻¹ * a'⁻¹ := by group
        _ = p * a' * p⁻¹ * a'⁻¹ := by rw [← h1]; group
    rw [← hd.V_inf_P]
    refine Subgroup.mem_inf.2 ⟨e1 ▸ hxc a' (mem_sup_right (d.A₃_le_P ha')), ?_⟩
    rw [commutatorElement_def]
    have ha'P := d.A₃_le_P ha'
    exact mul_mem (mul_mem (mul_mem hp ha'P) (inv_mem hp)) (inv_mem ha'P)
  have hxF : a * p ∈ d.F := mul_mem ha (hd.A₁_le_F hpA₁)
  have hcrZ : (a * p)⁻¹ * d.t * (a * p) * d.t ∈ d.Z₂p := by
    refine (d.mem_Z₂p_iff (d.A₁_le_P (hd.cr_F_mem hxF))).2 fun y hy => ?_
    rw [← hd.cr_commutator hGMS hxF hy]
    exact hd.cr_mem ((hd.V_le_CB₄I₃.trans d.CB₄I₃_le) (hxc y (mem_sup_right hy)))
  rw [hd.Z₂p_eq.1] at hcrZ
  obtain ⟨z₀, hz₀, z, hz, hz₀z⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer d.C₄_le_normalizer_Zp hcrZ
  obtain ⟨v, hv, hvz⟩ := hd.exists_V_cr_eq hz₀
  obtain ⟨c, hc, hcz⟩ := hd.exists_F_I₄_cr_eq hGMS hz
  have hwW : v * c ∈ d.W := by
    rw [hd.W_eq hGMS]
    exact mul_mem (mem_sup_left hv) (mem_sup_right hc)
  have hwF : v * c ∈ d.F := mul_mem (d.V_le_F hv) hc.1
  have hb : (v * c)⁻¹ * (a * p) ∈ d.A₁ := hd.inv_mul_mem_A₁_of_cr_eq hGMS hwF hxF (by
    rw [hd.cr_F_mul (d.V_le_F hv) hc.1, hvz, hcz, hz₀z])
  have hbZ := mul_mem (inv_mem (hd.W_le_Z₂_FP hGMS hwW)) hx
  obtain ⟨-, hbc⟩ := (hd.mem_Z₂_FP_iff hGMS).1 hbZ
  have hbP := d.A₁_le_P hb
  have hbZ₂ : (v * c)⁻¹ * (a * p) ∈ d.Z₂p := by
    refine (d.mem_Z₂p_iff hbP).2 fun y hy => ?_
    rw [← hd.V_inf_P]
    refine Subgroup.mem_inf.2 ⟨hbc y (mem_sup_right hy), ?_⟩
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hbP hy) (inv_mem hbP)) (inv_mem hy)
  have hZ₂W : d.Z₂p ≤ d.W := by
    rw [hd.Z₂p_eq.1, hd.W_eq hGMS]
    exact sup_le_sup hd.Zp_le_V (le_inf (hd.C₄_le_A₁.trans hd.A₁_le_F) inf_le_right)
  have := mul_mem hwW (hZ₂W hbZ₂)
  rwa [mul_inv_cancel_left] at this

theorem Hyp.sec3_5_one (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    CFSG.centerIn (d.F ⊔ d.P) = d.V ∧
      (Subgroup.upperCentralSeries ↥(d.F ⊔ d.P) 2).map (d.F ⊔ d.P).subtype = d.W ∧
      (d.F ⊔ d.P) ⊓ centralizer (d.I₄ : Set G) = d.F ⊓ centralizer (d.I₄ : Set G) ∧
      Nat.card (d.F ⊓ centralizer (d.I₄ : Set G) : Subgroup G) = (2 ^ f) ^ 4 ∧
      d.V ⊓ (d.F ⊓ centralizer (d.I₄ : Set G)) = ⊥ ∧ d.W ≤ d.F ∧
      Nat.card d.W = (2 ^ f) ^ 6 :=
  ⟨hd.centerIn_FP hGMS, le_antisymm (hd.Z₂_FP_le_W hGMS) (hd.W_le_Z₂_FP hGMS),
    hd.FP_inf_centralizer_I₄ hGMS, hd.card_F_I₄ hGMS, hd.V_inf_F_I₄, hd.W_le_F hGMS,
    hd.card_W hGMS⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
