module

public import CFSG.Quasithin.H13.L32AC38e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NModule

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecF.C10E4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

namespace Ctx38

variable {b c : G} (C : Ctx38 T L V H b c)
include C

theorem false_of_ψ_eq_one_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) {x : G}
    (hxL : x ∈ L₁Of L (fsuV1 T V)) (hx3 : x ^ 3 = 1)
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V)
    (hxH : x ∈ H) (hψ : C.ψ ⟨x, hxH⟩ = 1) : False := by
  have h91 := C.hF.toHypF91
  have hMod := stmtL32NModule_of_inputs_F4 h1332 h1334
  obtain ⟨-, -, hLTV, -⟩ := hMod G T L V C.S.hyp.hyp C.S.hyp.fsu
  have hL1 : L₁Of L (fsuV1 T V) ≤ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := oTwoRes_le _
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hUe := h91.isElemAbelian_tilde
  set N := Subgroup.normalizer (fsuV1 T V : Set G) with hNdef
  set Ut := tildeOf (fsuV1 T V) (conjClosure V H) with hUt
  set Vt := tildeOf (fsuV1 T V) V with hVt
  have hHU : tildeOf (fsuV1 T V) H ≤ Subgroup.normalizer (Ut : Set (SecQuot N (fsuV1 T V))) :=
    HypF91.tilde_le_normalizer le_rfl
  let ρ : ↥H →* MulAut (IntMod Ut hUe) :=
    (convI hUe).comp (((secMk N (fsuV1 T V)).comp (Subgroup.inclusion C.HN)).codRestrict _
      fun h => hHU (secMk_mem_secImg h.2))
  have hρ : ∀ (h : ↥H) (e : IntMod Ut hUe),
      (ρ h e).val = secMk N (fsuV1 T V) ⟨h, C.HN h.2⟩ * e.val *
        (secMk N (fsuV1 T V) ⟨h, C.HN h.2⟩)⁻¹ := fun h e => convI_apply_val hUe _ e

  have hρQ : ∀ (q : ↥H), (q : G) ∈ pCoreOf 2 H → ρ q = 1 := by
    intro q hq
    have hc : secMk N (fsuV1 T V) ⟨q, C.HN q.2⟩ ∈
        Subgroup.centralizer (Ut : Set (SecQuot N (fsuV1 T V))) := by
      have h1 : secMk N (fsuV1 T V) ⟨q, C.HN q.2⟩ ∈ tildeOf (fsuV1 T V) (H ⊓ pCoreOf 2 H) :=
        secMk_mem_secImg ⟨q.2, hq⟩
      rw [← h91.tilde_inf_centralizer_pCoreOf (le_refl H)] at h1
      exact h1.2
    exact (convI_eq_one_iff hUe _).mpr hc

  have hcomm : ∀ (h : ↥H), (h : G) ∈ H1 H b → ρ ⟨x, hxH⟩ * ρ h = ρ h * ρ ⟨x, hxH⟩ := by
    intro h hh
    have hm : (x⁻¹ * h * x * (h : G)⁻¹) ∈ H1 H b := by
      have h1 : x⁻¹ * h * x ∈ H1 H b := by
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ H (inv_mem hxH))
          h).mp hh
        simpa using this
      exact mul_mem h1 (inv_mem hh)
    have hmH : (x⁻¹ * h * x * (h : G)⁻¹) ∈ H := C.H1_le hm
    have hψm : C.ψ ⟨_, hmH⟩ = 1 := by
      have e : (⟨x⁻¹ * h * x * (h : G)⁻¹, hmH⟩ : ↥H) = ⟨x, hxH⟩⁻¹ * h * ⟨x, hxH⟩ * h⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hψ, inv_one, one_mul, mul_one,
        mul_inv_cancel]
    have hq := C.mem_pCoreOf_of_mem_H1 hm hψm
    have h1 := hρQ ⟨_, hmH⟩ hq
    have e : (⟨x⁻¹ * h * x * (h : G)⁻¹, hmH⟩ : ↥H) = ⟨x, hxH⟩⁻¹ * h * ⟨x, hxH⟩ * h⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h2 : ρ h * ρ ⟨x, hxH⟩ = ρ ⟨x, hxH⟩ * ρ h := by
      calc ρ h * ρ ⟨x, hxH⟩
          = ρ ⟨x, hxH⟩ * ((ρ ⟨x, hxH⟩)⁻¹ * ρ h * ρ ⟨x, hxH⟩ * (ρ h)⁻¹) * ρ h := by group
        _ = ρ ⟨x, hxH⟩ * ρ h := by rw [h1, mul_one]
    exact h2.symm

  let valH : IntMod Ut hUe →* SecQuot N (fsuV1 T V) :=
    MonoidHom.mk' IntMod.val (fun a b => IntMod.val_mul a b)
  let A : Subgroup (IntMod Ut hUe) := Vt.comap valH
  let Wm : Subgroup (IntMod Ut hUe) := C.Wt.comap valH
  have hxN : x ∈ N := (hL1 hxL).2
  have hσA : ∀ a ∈ A, ρ ⟨x, hxH⟩ a ∈ A := by
    intro a ha
    show (ρ ⟨x, hxH⟩ a).val ∈ Vt
    rw [hρ]
    exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_tildeV hxN (hLV (hL1 hxL).1)) _).mp ha
  have hfpfA : ∀ a ∈ A, ρ ⟨x, hxH⟩ a = a → a = 1 := by
    intro a ha hfix
    apply IntMod.val_injective
    rw [IntMod.val_one]
    refine fix_eq_one hxN hfpf ha ?_
    have := congrArg IntMod.val hfix
    rw [hρ] at this
    exact this

  have hxW : secMk N (fsuV1 T V) ⟨x, hxN⟩ ∈
      Subgroup.centralizer (C.Wt : Set (SecQuot N (fsuV1 T V))) :=
    (convI_eq_one_iff C.hUe _).mp hψ
  have hσW : ∀ w ∈ Wm, ρ ⟨x, hxH⟩ w = w := by
    intro w hw
    apply IntMod.val_injective
    rw [hρ]
    have h1 := Subgroup.mem_centralizer_iff.mp hxW w.val hw
    rw [← h1, mul_inv_cancel_right]

  have h3 : ∀ e, ρ ⟨x, hxH⟩ (ρ ⟨x, hxH⟩ (ρ ⟨x, hxH⟩ e)) = e := by
    intro e
    have hx3' : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    have : ρ ⟨x, hxH⟩ ^ 3 = 1 := by rw [← map_pow, hx3', map_one]
    have h' := congrArg (fun f : MulAut (IntMod Ut hUe) => f e) this
    simpa [pow_succ, MulAut.mul_apply] using h'
  have hE : ∀ e : IntMod Ut hUe, e * e = 1 := fun e => by
    rw [← pow_two]
    exact IntMod.sq_eq_one e

  have hcentV : ∀ h (hh : h ∈ H1 H b) (v : G) (hv : v ∈ V),
      secMk N (fsuV1 T V) ⟨h, C.HN (C.H1_le hh)⟩ * secMk N (fsuV1 T V) ⟨v, C.VN hv⟩ *
        (secMk N (fsuV1 T V) ⟨h, C.HN (C.H1_le hh)⟩)⁻¹ = secMk N (fsuV1 T V) ⟨v, C.VN hv⟩ := by
    intro h hh v hv
    have hhH := C.H1_le hh
    have hτ : ∀ e, ρ ⟨h, hhH⟩ e / e ∈ Wm := by
      intro e
      show (ρ ⟨h, hhH⟩ e / e).val ∈ C.Wt
      rw [div_eq_mul_inv, IntMod.val_mul, IntMod.val_inv, hρ]
      exact (C.mem_cmod (Subgroup.mem_sup_left hh) (C.HN hhH)).2.2 _ e.val_mem
    have hvU : secMk N (fsuV1 T V) ⟨v, C.VN hv⟩ ∈ Ut := secMk_mem_secImg (le_conjClosure V H hv)
    have hvA : (IntMod.mk hUe ⟨_, hvU⟩ : IntMod Ut hUe) ∈ A := secMk_mem_secImg hv
    have hstar := fix_of_coprime_38 hE (ρ ⟨x, hxH⟩) (ρ ⟨h, hhH⟩) h3
      (fun e => by
        have := congrArg (fun f : MulAut (IntMod Ut hUe) => f e) (hcomm ⟨h, hhH⟩ hh)
        simpa [MulAut.mul_apply] using this)
      hσA hfpfA hσW hτ hvA
    have := congrArg IntMod.val hstar
    rw [hρ] at this
    exact this

  have hbN := C.bN
  set bt := secMk N (fsuV1 T V) ⟨b, hbN⟩ with hbt
  have hle : conjClosure V H ≤ ((Subgroup.centralizer ({bt} : Set (SecQuot N (fsuV1 T V)))).comap
      (secMk N (fsuV1 T V))).map N.subtype := by
    refine conjClosure_le fun g hg v hv => ?_
    have hgN := C.HN hg
    have hvN := C.VN hv
    have hm : g * v * g⁻¹ ∈ N := mul_mem (mul_mem hgN hvN) (inv_mem hgN)
    refine ⟨⟨_, hm⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
    have hgb : g⁻¹ * b * g ∈ H1 H b := by
      have := mem_conjClosure (Z := Subgroup.zpowers b) (inv_mem hg) (Subgroup.mem_zpowers b)
      simpa using this
    have h1 := hcentV _ hgb v hv
    have e1 : (⟨g⁻¹ * b * g, C.HN (C.H1_le hgb)⟩ : ↥N) = ⟨g, hgN⟩⁻¹ * ⟨b, hbN⟩ * ⟨g, hgN⟩ := rfl
    have e2 : (⟨g * v * g⁻¹, hm⟩ : ↥N) = ⟨g, hgN⟩ * ⟨v, hvN⟩ * ⟨g, hgN⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv] at h1
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rw [e2, map_mul, map_mul, map_inv]
    set gt := secMk N (fsuV1 T V) ⟨g, hgN⟩
    set vt := secMk N (fsuV1 T V) ⟨v, hvN⟩
    calc bt * (gt * vt * gt⁻¹) = gt * ((gt⁻¹ * bt * gt) * vt * (gt⁻¹ * bt * gt)⁻¹) * gt⁻¹ * bt := by
          group
      _ = gt * vt * gt⁻¹ * bt := by rw [h1]
  have hbU : bt ∈ Subgroup.centralizer (Ut : Set (SecQuot N (fsuV1 T V))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨u, hu, rfl⟩ := mem_secImg.mp hy
    obtain ⟨u', hu', hu'u⟩ := hle hu
    have e : u = u' := Subtype.ext hu'u.symm
    rw [e]
    exact (Subgroup.mem_centralizer_iff.mp hu' bt rfl).symm
  have hV1 : fsuV1 T V ≤ H ⊓ pCoreOf 2 H :=
    le_inf (h91.V₁_le_pCoreOf.trans (pCoreOf_le 2 H)) h91.V₁_le_pCoreOf
  have h2 : bt ∈ tildeOf (fsuV1 T V) (H ⊓ pCoreOf 2 H) := by
    rw [← h91.tilde_inf_centralizer_pCoreOf (le_refl H)]
    exact ⟨secMk_mem_secImg C.bH, hbU⟩
  exact C.bQ ((secMk_mem_secImg_iff hV1).mp h2).2

end Ctx38

end CFSG.Quasithin.H13.L32A.C
