module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightA
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ProofEightC1

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups
open scoped commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec38e1_A2E (hp : d.CaseHyp) {a : G} (ha : a ∈ d.A₂)
    (h : ∀ e ∈ d.E, ⁅a, e⁆ ∈ d.Zp) : a ∈ d.Zp := by
  have hGMS := hp.gms
  have hd := hp.hyp
  refine hd.sec38a1_mem_Zp hGMS ha fun e he => ?_
  have hz := h e he
  have hzV : ⁅a, e⁆ ∈ d.V := hd.Zp_le_V hz
  have hzt : ⁅a, e⁆ * d.t = d.t * ⁅a, e⁆ := hd.comm_t (d.Zp_le_L hz)
  refine ⟨mem_sup_left (d.V_le_E hzV), mem_centralizer_iff.2 fun y hy => ?_⟩
  rcases hd.sec38a1_mem_sup hGMS hy with hyE | ⟨e', he', rfl⟩
  · exact hd.sec38a1_V_comm hGMS hzV hyE
  · calc e' * d.t * ⁅a, e⁆ = e' * (d.t * ⁅a, e⁆) := by group
      _ = e' * (⁅a, e⁆ * d.t) := by rw [hzt]
      _ = (e' * ⁅a, e⁆) * d.t := by group
      _ = (⁅a, e⁆ * e') * d.t := by rw [hd.sec38a1_V_comm hGMS hzV he']
      _ = ⁅a, e⁆ * (e' * d.t) := by group

theorem Hyp.sec38e1_T_mem_normalizer_ZtP (hd : d.Hyp) {x : G} (hx : x ∈ d.T) :
    x ∈ normalizer (d.ZtP : Set G) :=
  d.normalizer_tP_le_normalizer_ZtP (hd.normalizer_T_le (le_normalizer hx))

theorem Hyp.sec38e1_T_mem_normalizer_B₂ (hd : d.Hyp) {x : G} (hx : x ∈ d.T) :
    x ∈ normalizer (d.B₂ : Set G) :=
  hd.normalizer_tP_le (hd.normalizer_T_le (le_normalizer hx))

theorem Hyp.sec38e1_T_mem_normalizer_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {x : G} (hx : x ∈ d.T) : x ∈ normalizer (d.V : Set G) :=
  hd.normalizer_ZtP_le_normalizer_V hGMS (hd.sec38e1_T_mem_normalizer_ZtP hx)

theorem Hyp.sec38e1_conj_A₂ (hd : d.Hyp) {x : G} (hx : x ∈ d.T) {a : G} (ha : a ∈ d.A₂) :
    x * a * x⁻¹ ∈ d.A₂ :=
  hd.conj_mem_A₂ (hd.sec38e1_T_mem_normalizer_ZtP hx) (hd.T_le_centralizer hx) ha

theorem Hyp.sec38e1_conj_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : G} (hx : x ∈ d.T) {v : G} (hv : v ∈ d.V) : x * v * x⁻¹ ∈ d.V :=
  (mem_normalizer_iff.1 (hd.sec38e1_T_mem_normalizer_V hGMS hx) v).1 hv

theorem Hyp.sec38e1_conj_Zp (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : G} (hx : x ∈ d.T) {z : G} (hz : z ∈ d.Zp) : x * z * x⁻¹ ∈ d.Zp := by
  rw [← hd.V_inf_A₂] at hz ⊢
  exact ⟨hd.sec38e1_conj_V hGMS hx hz.1, hd.sec38e1_conj_A₂ hx hz.2⟩

theorem sec38e1_Zp_comm_P (d : Data G h) {z p : G} (hz : z ∈ d.Zp) (hp : p ∈ d.P) :
    p * z = z * p := by
  have h1 : z ∈ CFSG.centerIn d.P := by rw [d.sec2_2_three.2.2.2.2]; exact hz
  exact mem_centralizer_iff.1 h1.2 p hp

theorem sec38e1_conj_Zp_P (d : Data G h) {z p : G} (hz : z ∈ d.Zp) (hp : p ∈ d.P) :
    p * z * p⁻¹ = z := by
  rw [sec38e1_Zp_comm_P d hz hp, mul_inv_cancel_right]

@[expose] def sec38e1_C1 (d : Data G h) (x : G) : Subgroup G where
  carrier := {a | a ∈ d.A₂ ∧ ⁅a, x⁆ ∈ d.Zp}
  mul_mem' := by
    rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e : ⁅a * b, x⁆ = (a * ⁅b, x⁆ * a⁻¹) * ⁅a, x⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, sec38e1_conj_Zp_P d hbx (d.A₂_le_P ha)]
    exact mul_mem hbx hax
  one_mem' := ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
  inv_mem' := by
    rintro a ⟨ha, hax⟩
    refine ⟨inv_mem ha, ?_⟩
    have e : ⁅a⁻¹, x⁆ = a⁻¹ * ⁅a, x⁆⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, sec38e1_conj_Zp_P d (inv_mem hax) (d.A₂_le_P (inv_mem ha))]
    exact inv_mem hax

theorem sec38e1_C1_le_A₂ (d : Data G h) (x : G) : sec38e1_C1 d x ≤ d.A₂ := fun _ ha => ha.1

theorem Hyp.sec38e1_psi_fixed (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : G} (hx : x ∈ d.T) (ψ : d.E →* d.A₂ ⧸ d.Zp.subgroupOf d.A₂)
    (hker : ψ.ker = (d.V ⊔ d.A₂).subgroupOf d.E)
    (hequiv : ∀ c ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G), ∀ (e : d.E) (a : d.A₂)
        (he : c * e * c⁻¹ ∈ d.E) (ha : c * a * c⁻¹ ∈ d.A₂),
        ψ e = QuotientGroup.mk a → ψ ⟨c * e * c⁻¹, he⟩ = QuotientGroup.mk ⟨c * a * c⁻¹, ha⟩)
    {e : G} (he : e ∈ d.E) (hex : ⁅e, x⁆ ∈ d.V) {a : d.A₂}
    (hψ : ψ ⟨e, he⟩ = QuotientGroup.mk a) : ⁅(a : G), x⁆ ∈ d.Zp := by
  have hxi : x⁻¹ ∈ d.T := inv_mem hx
  have hxN := hd.T_le_normalizer_E hGMS hxi
  have hcmem : x⁻¹ ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G) :=
    ⟨hd.sec38e1_T_mem_normalizer_B₂ hxi, hd.T_le_centralizer hxi⟩
  have he' : x⁻¹ * e * x⁻¹⁻¹ ∈ d.E := (mem_normalizer_iff.1 hxN e).1 he
  have ha' : x⁻¹ * (a : G) * x⁻¹⁻¹ ∈ d.A₂ := hd.sec38e1_conj_A₂ hxi a.2
  have h1 := hequiv _ hcmem ⟨e, he⟩ a he' ha' hψ
  have hv0 : x⁻¹ * e * x⁻¹⁻¹ * e⁻¹ ∈ d.V := by
    have := hd.sec38e1_conj_V hGMS hxi hex
    have e1 : x⁻¹ * e * x⁻¹⁻¹ * e⁻¹ = x⁻¹ * ⁅e, x⁆ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1]
    exact this
  have hv0E : x⁻¹ * e * x⁻¹⁻¹ * e⁻¹ ∈ d.E := d.V_le_E hv0
  have hk : (⟨x⁻¹ * e * x⁻¹⁻¹ * e⁻¹, hv0E⟩ : d.E) ∈ ψ.ker := by
    rw [hker, mem_subgroupOf]
    exact mem_sup_left hv0
  have h2 : ψ ⟨x⁻¹ * e * x⁻¹⁻¹, he'⟩ = ψ ⟨e, he⟩ := by
    have : (⟨x⁻¹ * e * x⁻¹⁻¹, he'⟩ : d.E) = ⟨x⁻¹ * e * x⁻¹⁻¹ * e⁻¹, hv0E⟩ * ⟨e, he⟩ := by
      apply Subtype.ext
      simp
    rw [this, map_mul, MonoidHom.mem_ker.1 hk, one_mul]
  have h3 : (QuotientGroup.mk a : d.A₂ ⧸ d.Zp.subgroupOf d.A₂) =
      QuotientGroup.mk ⟨x⁻¹ * (a : G) * x⁻¹⁻¹, ha'⟩ := by
    rw [← hψ, ← h1, h2]
  rw [QuotientGroup.eq, mem_subgroupOf] at h3
  have h4 : (a : G)⁻¹ * (x⁻¹ * (a : G) * x) ∈ d.Zp := by
    simpa using h3
  have e1 : ⁅(a : G), x⁆ = x * ((a : G) * ((a : G)⁻¹ * (x⁻¹ * (a : G) * x)) * (a : G)⁻¹) * x⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e1, sec38e1_conj_Zp_P d h4 (d.A₂_le_P a.2)]
  exact hd.sec38e1_conj_Zp hGMS hx h4

theorem sec38e1_card_eq_ker_range {X Y : Type*} [Group X] [Group Y] (f : X →* Y) :
    Nat.card X = Nat.card f.ker * Nat.card f.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]

theorem Hyp.sec38e1_Zp_le_C1 (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : G} (hx : x ∈ d.T) : d.Zp ≤ sec38e1_C1 d x := fun z hz => by
  refine ⟨d.Zp_le_A₂ hz, ?_⟩
  have e : ⁅z, x⁆ = z * (x * z⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
  rw [e]
  exact mul_mem hz (hd.sec38e1_conj_Zp hGMS hx (inv_mem hz))

theorem Hyp.sec38e1_card_V_sup_C1 (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : G} (hx : x ∈ d.T) :
    Nat.card (d.V ⊔ sec38e1_C1 d x : Subgroup G) = 2 ^ f * Nat.card (sec38e1_C1 d x) := by
  have hN : sec38e1_C1 d x ≤ normalizer (d.V : Set G) := fun a ha =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun _ hv => hd.V_comm_A₂ hv ha.1)
  have h1 := Common.card_sup_mul_card_inf_eq hN
  have hinf : d.V ⊓ sec38e1_C1 d x = d.Zp := by
    refine le_antisymm (fun a ha => ?_) (le_inf hd.Zp_le_V (hd.sec38e1_Zp_le_C1 hGMS hx))
    rw [← hd.V_inf_A₂]
    exact ⟨ha.1, ha.2.1⟩
  rw [hinf, d.card_Zp, hd.card_V] at h1
  have hq : 0 < 2 ^ f := by positivity
  refine Nat.eq_of_mul_eq_mul_right hq ?_
  rw [h1]
  ring

theorem Hyp.sec38e1_card_le_C1_sq (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x : G} (hx : x ∈ d.T) {X : Subgroup G} (hXE : X ≤ d.E) (hX : ∀ e ∈ X, ⁅e, x⁆ ∈ d.V) :
    Nat.card X ≤ Nat.card (sec38e1_C1 d x) ^ 2 := by
  obtain ⟨ψ, -, hker, -, hequiv⟩ := hd.exists_E_hom hGMS
  set Cx := sec38e1_C1 d x with hCx
  set Zq : Subgroup d.A₂ := d.Zp.subgroupOf d.A₂ with hZq
  let ψ' : X →* d.A₂ ⧸ Zq := ψ.comp (Subgroup.inclusion hXE)
  let θ : Cx →* d.A₂ ⧸ Zq :=
    (QuotientGroup.mk' Zq).comp (Subgroup.inclusion (sec38e1_C1_le_A₂ d x))
  have hXcard := sec38e1_card_eq_ker_range ψ'
  have hCcard := sec38e1_card_eq_ker_range θ
  have hrange : ψ'.range ≤ θ.range := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (ψ ⟨y, hXE y.2⟩)
    have hax := hd.sec38e1_psi_fixed hGMS hx ψ hker hequiv (hXE y.2) (hX y y.2) ha.symm
    exact ⟨⟨a, a.2, hax⟩, ha⟩
  have hker_θ : 2 ^ f ≤ Nat.card θ.ker := by
    rw [← d.card_Zp]
    refine Nat.card_le_card_of_injective
      (fun z : d.Zp => (⟨⟨z, hd.sec38e1_Zp_le_C1 hGMS hx z.2⟩, ?_⟩ : θ.ker)) ?_
    · rw [MonoidHom.mem_ker]
      change (QuotientGroup.mk (⟨(z : G), d.Zp_le_A₂ z.2⟩ : d.A₂) : d.A₂ ⧸ Zq) = 1
      rw [QuotientGroup.eq_one_iff, hZq, mem_subgroupOf]
      exact z.2
    · intro z z' hzz
      exact Subtype.ext (congrArg (fun w : θ.ker => ((w : Cx) : G)) hzz)
  have hmem : ∀ y : X, ψ' y = 1 → (y : G) ∈ d.V ⊔ Cx := by
    intro y hy
    have hk : (⟨y, hXE y.2⟩ : d.E) ∈ ψ.ker := MonoidHom.mem_ker.2 hy
    rw [hker, mem_subgroupOf] at hk
    obtain ⟨v, hv, a, ha, hya⟩ := hd.exists_mul_of_mem_VA hk
    have hyx : ⁅(y : G), x⁆ ∈ d.V := hX y y.2
    have hvx : ⁅v, x⁆ ∈ d.V := by
      have e : ⁅v, x⁆ = v * (x * v⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem hv (hd.sec38e1_conj_V hGMS hx (inv_mem hv))
    have hax : ⁅a, x⁆ ∈ d.V := by
      have e : ⁅a, x⁆ = v⁻¹ * (⁅v * a, x⁆ * ⁅v, x⁆⁻¹) * v := by
        simp only [commutatorElement_def]; group
      rw [e, ← hya]
      exact mul_mem (mul_mem (inv_mem hv) (mul_mem hyx (inv_mem hvx))) hv
    have haA : ⁅a, x⁆ ∈ d.A₂ := by
      have e : ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact mul_mem ha (hd.sec38e1_conj_A₂ hx (inv_mem ha))
    have haZ : ⁅a, x⁆ ∈ d.Zp := by
      rw [← hd.V_inf_A₂]
      exact ⟨hax, haA⟩
    rw [hya]
    exact mul_mem_sup hv (show a ∈ Cx from ⟨ha, haZ⟩)
  have hker_ψ : Nat.card ψ'.ker ≤ 2 ^ f * Nat.card Cx := by
    rw [← hd.sec38e1_card_V_sup_C1 hGMS hx]
    exact Nat.card_le_card_of_injective
      (fun y : ψ'.ker => (⟨((y : X) : G), hmem y (MonoidHom.mem_ker.1 y.2)⟩ : (d.V ⊔ Cx : Subgroup G)))
      (fun y y' hyy => by
        have := congrArg (fun w : (d.V ⊔ Cx : Subgroup G) => (w : G)) hyy
        exact Subtype.ext (Subtype.ext this))
  calc Nat.card X = Nat.card ψ'.ker * Nat.card ψ'.range := hXcard
    _ ≤ (2 ^ f * Nat.card Cx) * Nat.card θ.range :=
        Nat.mul_le_mul hker_ψ (Subgroup.card_le_of_le hrange)
    _ = Nat.card Cx * (2 ^ f * Nat.card θ.range) := by ring
    _ ≤ Nat.card Cx * (Nat.card θ.ker * Nat.card θ.range) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hker_θ)
    _ = Nat.card Cx ^ 2 := by rw [← hCcard]; ring

theorem sec38e1_CTE (hp : d.CaseHyp) {x : G} (hx : x ∈ d.T)
    (h : ∀ e ∈ d.E, ⁅e, x⁆ ∈ d.V) : x ∈ d.A₂ := by
  have hGMS := hp.gms
  have hd := hp.hyp
  have hB : x ∈ d.B₂ := by
    by_contra hxB
    have h1 := hd.sec38e1_card_le_C1_sq hGMS hx (le_refl d.E) h
    rw [hd.card_E hGMS] at h1
    have h2 : Nat.card (sec38e1_C1 d x) ≤ (2 ^ f) ^ 5 := by
      by_cases htP : x ∈ d.tP
      · exact hd.sec38c1_card_le_in htP hxB (sec38e1_C1_le_A₂ d x) (fun a ha => ha.2)
      · exact (hd.sec38c1_card_le_out hx htP (sec38e1_C1_le_A₂ d x) (fun a ha => ha.2)).trans
          (Nat.pow_le_pow_right (by positivity) (by norm_num))
    have h3 : Nat.card (sec38e1_C1 d x) ^ 2 ≤ ((2 ^ f) ^ 5) ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : (2 ^ f) ^ 10 < (2 ^ f) ^ 14 :=
      Nat.pow_lt_pow_right (by have := hd.four_le; omega) (by norm_num)
    have h5 : ((2 ^ f) ^ 5) ^ 2 = (2 ^ f) ^ 10 := by ring
    omega
  obtain ⟨a, ha, hxa | hxa⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hB
  · rw [hxa]
    exact ha
  · exfalso
    obtain ⟨e, he, hne⟩ := hd.sec38a1_exists_cr_not_mem_V hGMS
    refine hne ?_
    have hE := hd.elemAbMod_V_E hGMS
    have hxe := h e⁻¹ (inv_mem he)
    rw [hxa] at hxe
    have hea : ⁅e⁻¹, a⁆ ∈ d.V := hE.2 _ (inv_mem he) a (hd.A₂_le_E hGMS ha)
    have hta := hd.sec38e1_conj_V hGMS hd.t_mem_T hea
    have e1 : e⁻¹ * d.t * e * d.t⁻¹ = ⁅e⁻¹, d.t * a⁆ * (d.t * ⁅e⁻¹, a⁆ * d.t⁻¹)⁻¹ := by
      simp only [commutatorElement_def]; group
    have h5 : e⁻¹ * d.t * e * d.t⁻¹ ∈ d.V := by
      rw [e1]
      exact mul_mem hxe (inv_mem hta)
    rwa [hd.sec38a1_inv_t] at h5

end Data

end CFSG.LocalAnalysis.EvenBN.U5
