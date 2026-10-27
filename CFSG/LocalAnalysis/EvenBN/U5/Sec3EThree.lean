module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3ETwo

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common
open scoped commutatorElement

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

omit [Finite G] in
instance normal_Zp_subgroupOf_A₂ (d : Data G h) : (d.Zp.subgroupOf d.A₂).Normal := by
  have hZA : CFSG.centerIn d.A₂ = d.Zp := d.sec2_2_three.2.2.2.1
  refine ⟨fun x hx g => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  rw [← hZA] at hx ⊢
  have hc : (g : G) * x = x * g := (mem_centralizer_iff.1 hx.2 g g.2)
  simp only [coe_mul, coe_inv, hc, mul_inv_cancel_right]
  exact hx

theorem Hyp.cr_mem_V_of_mem_VA (hd : d.Hyp) {x : G} (hx : x ∈ d.V ⊔ d.A₂) :
    x⁻¹ * d.t * x * d.t ∈ d.V := by
  obtain ⟨v, hv, a, ha, rfl⟩ := hd.exists_mul_of_mem_VA hx
  have hz := hd.cr_mem (hd.V_le_B₄ hv)
  have hza : (v⁻¹ * d.t * v * d.t) * a = a * (v⁻¹ * d.t * v * d.t) :=
    (hd.V_comm_A₂ (hd.Zp_le_V hz) ha)
  have e : (v * a)⁻¹ * d.t * (v * a) * d.t = a⁻¹ * (v⁻¹ * d.t * v * d.t) * a := by
    calc (v * a)⁻¹ * d.t * (v * a) * d.t = a⁻¹ * v⁻¹ * d.t * v * (a * d.t) := by group
      _ = a⁻¹ * v⁻¹ * d.t * v * (d.t * a) := by rw [← hd.t_comm_A₂ ha]
      _ = a⁻¹ * (v⁻¹ * d.t * v * d.t) * a := by group
  rw [e, mul_assoc, hza, ← mul_assoc, inv_mul_cancel, one_mul]
  exact hd.Zp_le_V hz

theorem Hyp.exists_E_hom (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ∃ ψ : d.E →* d.A₂ ⧸ d.Zp.subgroupOf d.A₂, Function.Surjective ψ ∧
      ψ.ker = (d.V ⊔ d.A₂).subgroupOf d.E ∧
      (∀ (e : d.E) (a : d.A₂), ∀ v ∈ d.V, (e : G)⁻¹ * d.t * e * d.t = v * a →
        ψ e = QuotientGroup.mk a) ∧
      ∀ c ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G), ∀ (e : d.E) (a : d.A₂)
        (he : c * e * c⁻¹ ∈ d.E) (ha : c * a * c⁻¹ ∈ d.A₂),
        ψ e = QuotientGroup.mk a → ψ ⟨c * e * c⁻¹, he⟩ = QuotientGroup.mk ⟨c * a * c⁻¹, ha⟩ := by
  have hEC := hd.E_le_C₀ hGMS
  have hcen : ∀ {x v : G}, x ∈ d.V ⊔ d.A₂ → v ∈ d.V → x * v = v * x := fun hx hv =>
    hd.comm_V_of_mem_VA hGMS hx hv
  have hcr : ∀ e ∈ d.E, e⁻¹ * d.t * e * d.t ∈ d.V ⊔ d.A₂ := fun e he =>
    hd.cr_mem_VA hGMS (d.C₀_le_normalizer_B₄ (hEC he))
  set VA := d.V ⊔ d.A₂ with hVA
  set V' := d.V.subgroupOf VA with hV'
  have : V'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hV', mem_subgroupOf] at hx ⊢
    have := hcen g.2 hx
    simp only [coe_mul, coe_inv, this, mul_inv_cancel_right]
    exact hx
  have hmkeq : ∀ x y : VA, (QuotientGroup.mk x : VA ⧸ V') = QuotientGroup.mk y ↔
      (x : G)⁻¹ * y ∈ d.V := fun x y => by
    rw [QuotientGroup.eq, hV', mem_subgroupOf, coe_mul, coe_inv]
  have key : ∀ {c v₀ : G}, c ∈ VA → v₀ ∈ d.V → (v₀ * c)⁻¹ * c ∈ d.V := fun hc hv₀ => by
    have k := hcen hc (inv_mem hv₀)
    rw [mul_inv_rev, mul_assoc, ← k, inv_mul_cancel_left]
    exact inv_mem hv₀
  let ψ₁ : d.E →* VA ⧸ V' :=
    MonoidHom.mk' (fun e => QuotientGroup.mk (⟨(e : G)⁻¹ * d.t * e * d.t, hcr e e.2⟩ : VA))
      fun x y => by
        rw [← QuotientGroup.mk_mul, hmkeq]
        obtain ⟨v₀, hv₀, h12⟩ := hd.cr_mul_mod hGMS (hEC x.2) (hEC y.2)
        change (((x : G) * (y : G))⁻¹ * d.t * ((x : G) * (y : G)) * d.t)⁻¹ *
          (((x : G)⁻¹ * d.t * x * d.t) * ((y : G)⁻¹ * d.t * y * d.t)) ∈ d.V
        rw [h12]
        exact key (mul_mem (hcr x x.2) (hcr y y.2)) hv₀
  have hψ₁ : ∀ e : d.E, ψ₁ e = QuotientGroup.mk
      (⟨(e : G)⁻¹ * d.t * e * d.t, hcr e e.2⟩ : VA) := fun _ => rfl
  let ι : d.A₂ →* VA ⧸ V' := (QuotientGroup.mk' V').comp (inclusion le_sup_right)
  have hι : ∀ a : d.A₂, ι a = QuotientGroup.mk (⟨a, mem_sup_right a.2⟩ : VA) := fun _ => rfl
  have hιsurj : Function.Surjective ι := by
    intro q
    induction q using QuotientGroup.induction_on with | H w => ?_
    obtain ⟨v, hv, a, ha, hw⟩ := hd.exists_mul_of_mem_VA w.2
    refine ⟨⟨a, ha⟩, ?_⟩
    rw [hι, hmkeq]
    change a⁻¹ * (w : G) ∈ d.V
    rw [hw, hd.V_comm_A₂ hv ha, inv_mul_cancel_left]
    exact hv
  have hιker : ι.ker = d.Zp.subgroupOf d.A₂ := by
    ext a
    rw [MonoidHom.mem_ker, hι, QuotientGroup.eq_one_iff, hV', mem_subgroupOf, mem_subgroupOf]
    change (a : G) ∈ d.V ↔ (a : G) ∈ d.Zp
    rw [← hd.V_inf_A₂]
    exact ⟨fun h1 => ⟨h1, a.2⟩, fun h1 => h1.1⟩
  let e₂ : d.A₂ ⧸ d.Zp.subgroupOf d.A₂ ≃* VA ⧸ V' :=
    (QuotientGroup.quotientMulEquivOfEq hιker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ι hιsurj)
  have he₂ : ∀ a : d.A₂, e₂ (QuotientGroup.mk a) = ι a := fun _ => rfl
  let ψ : d.E →* d.A₂ ⧸ d.Zp.subgroupOf d.A₂ := e₂.symm.toMonoidHom.comp ψ₁
  have hψ : ∀ e : d.E, ψ e = e₂.symm (ψ₁ e) := fun _ => rfl
  have hchar : ∀ (e : d.E) (a : d.A₂), ∀ v ∈ d.V, (e : G)⁻¹ * d.t * e * d.t = v * a →
      ψ e = QuotientGroup.mk a := by
    intro e a v hv hea
    rw [hψ, MulEquiv.symm_apply_eq, he₂, hψ₁, hι, hmkeq]
    change ((e : G)⁻¹ * d.t * e * d.t)⁻¹ * a ∈ d.V
    rw [hea, mul_inv_rev, mul_assoc, hd.V_comm_A₂ (inv_mem hv) a.2, inv_mul_cancel_left]
    exact inv_mem hv
  refine ⟨ψ, ?_, ?_, hchar, ?_⟩
  ·
    intro q
    obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (e₂ q)
    obtain ⟨e, he, hew⟩ := hd.exists_E_cr hGMS w.2
    refine ⟨⟨e, he⟩, ?_⟩
    rw [hψ, MulEquiv.symm_apply_eq, ← hw, hψ₁, hmkeq]
    exact hew
  ·
    ext e
    rw [MonoidHom.mem_ker, hψ, map_eq_one_iff _ e₂.symm.injective, hψ₁,
      QuotientGroup.eq_one_iff, hV', mem_subgroupOf, mem_subgroupOf]
    change (e : G)⁻¹ * d.t * e * d.t ∈ d.V ↔ (e : G) ∈ VA
    constructor
    · intro h1
      exact (hd.E_inf_B₄ hGMS).le ⟨e.2, hd.mem_B₄_of_mem_C₀ hGMS (hEC e.2) h1⟩
    · exact hd.cr_mem_V_of_mem_VA
  ·
    intro c hc e a he ha hea
    have hcN : c ∈ normalizer (d.B₄ : Set G) := (hd.normalizer_B₄_inf_C.ge hc).1
    have hcZ : c ∈ normalizer (d.ZtP : Set G) := by
      rw [← hd.centerIn_B₂]
      exact mem_normalizer_centerIn hc.1
    have hcV := hd.normalizer_B₄_le_normalizer_V hGMS hcN
    have hcZp : c ∈ normalizer (d.Zp : Set G) := by
      rw [← hd.centerIn_B₄]
      exact mem_normalizer_centerIn hcN
    obtain ⟨v', hv', a', ha', hcre⟩ := hd.exists_mul_of_mem_VA (hcr e e.2)
    have h1 := hchar e ⟨a', ha'⟩ v' hv' hcre
    rw [h1, QuotientGroup.eq, mem_subgroupOf] at hea
    have hca' : c * a' * c⁻¹ ∈ d.A₂ := hd.conj_mem_A₂ hcZ hc.2 ha'
    have hcr' : (c * e * c⁻¹)⁻¹ * d.t * (c * e * c⁻¹) * d.t =
        (c * v' * c⁻¹) * (c * a' * c⁻¹) := by
      calc (c * e * c⁻¹)⁻¹ * d.t * (c * e * c⁻¹) * d.t =
          c * ((e : G)⁻¹ * d.t * e * d.t) * c⁻¹ := d.cr_conj hc.2
        _ = c * (v' * a') * c⁻¹ := by rw [hcre]
        _ = (c * v' * c⁻¹) * (c * a' * c⁻¹) := by group
    have h2 := hchar ⟨c * e * c⁻¹, he⟩ ⟨c * a' * c⁻¹, hca'⟩ (c * v' * c⁻¹)
      ((mem_normalizer_iff.1 hcV v').1 hv') hcr'
    rw [h2, QuotientGroup.eq, mem_subgroupOf]
    change (c * a' * c⁻¹)⁻¹ * (c * a * c⁻¹) ∈ d.Zp
    rw [show (c * a' * c⁻¹)⁻¹ * (c * a * c⁻¹) = c * (a'⁻¹ * a) * c⁻¹ by group]
    exact (mem_normalizer_iff.1 hcZp _).1 hea

theorem Hyp.centerIn_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    CFSG.centerIn d.E = d.V := by
  have hZA : CFSG.centerIn d.A₂ = d.Zp := d.sec2_2_three.2.2.2.1
  have key : ∀ x ∈ d.V ⊔ d.A₂, (∀ a ∈ d.A₂, a * x = x * a) → x ∈ d.V := by
    intro x hx hxa
    obtain ⟨v, hv, b, hb, rfl⟩ := hd.exists_mul_of_mem_VA hx
    refine mul_mem hv (hd.Zp_le_V ?_)
    rw [← hZA]
    refine ⟨hb, mem_centralizer_iff.2 fun a ha => ?_⟩
    have e := hxa a ha
    have hva := hd.V_comm_A₂ hv ha
    have e1 : v * (a * b) = v * (b * a) := by
      calc v * (a * b) = (v * a) * b := by group
        _ = (a * v) * b := by rw [hva]
        _ = v * b * a := by rw [mul_assoc, e]
        _ = v * (b * a) := by group
    exact mul_left_cancel e1
  apply le_antisymm
  · rintro z ⟨hzE, hzc⟩
    have hza : ∀ a ∈ d.A₂, a * z = z * a := fun a ha =>
      mem_centralizer_iff.1 hzc a (hd.A₂_le_E hGMS ha)
    have hcrV : z⁻¹ * d.t * z * d.t ∈ d.V := by
      refine key _ (hd.cr_mem_VA hGMS (d.C₀_le_normalizer_B₄ (hd.E_le_C₀ hGMS hzE))) fun a ha => ?_
      have h1 := hza a ha
      have h2 := hd.t_comm_A₂ ha
      have h3 : a * z⁻¹ = z⁻¹ * a := by
        calc a * z⁻¹ = z⁻¹ * (z * a) * z⁻¹ := by group
          _ = z⁻¹ * (a * z) * z⁻¹ := by rw [h1]
          _ = z⁻¹ * a := by group
      calc a * (z⁻¹ * d.t * z * d.t) = (a * z⁻¹) * d.t * z * d.t := by group
        _ = z⁻¹ * (a * d.t) * z * d.t := by rw [h3]; group
        _ = z⁻¹ * (d.t * a) * z * d.t := by rw [h2]
        _ = z⁻¹ * d.t * (a * z) * d.t := by group
        _ = z⁻¹ * d.t * (z * a) * d.t := by rw [h1]
        _ = z⁻¹ * d.t * z * (a * d.t) := by group
        _ = z⁻¹ * d.t * z * (d.t * a) := by rw [h2]
        _ = (z⁻¹ * d.t * z * d.t) * a := by group
    have hzVA : z ∈ d.V ⊔ d.A₂ := by
      rw [← hd.E_inf_B₄ hGMS]
      exact ⟨hzE, hd.mem_B₄_of_mem_C₀ hGMS (hd.E_le_C₀ hGMS hzE) hcrV⟩
    exact key z hzVA hza
  · intro v hv
    refine ⟨d.V_le_E hv, mem_centralizer_iff.2 fun e he => ?_⟩
    exact (mem_centralizer_iff.1 (hd.E_le_centralizer_V hGMS he) v hv).symm

theorem Hyp.elemAbMod_V_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    ElemAbMod d.V d.E := by
  have hZA : CFSG.centerIn d.A₂ = d.Zp := d.sec2_2_three.2.2.2.1
  have hEC := hd.E_le_C₀ hGMS
  have hsq : ∀ e ∈ d.E, e * e ∈ d.V := by
    intro e he
    obtain ⟨v₀, hv₀, h0⟩ := hd.cr_mul_mod hGMS (hEC he) (hEC he)
    have hcr := hd.cr_mem_VA hGMS (d.C₀_le_normalizer_B₄ (hEC he))
    have hsqV : (e⁻¹ * d.t * e * d.t) * (e⁻¹ * d.t * e * d.t) ∈ d.V :=
      (hd.elemAbMod_V_sup_A₂ hGMS).1 _ hcr
    have hcrV : (e * e)⁻¹ * d.t * (e * e) * d.t ∈ d.V := by
      rw [h0]
      exact mul_mem hv₀ hsqV
    have hVA : e * e ∈ d.V ⊔ d.A₂ := by
      rw [← hd.E_inf_B₄ hGMS]
      exact ⟨mul_mem he he, hd.mem_B₄_of_mem_C₀ hGMS (hEC (mul_mem he he)) hcrV⟩
    have hcomm : ∀ a ∈ d.A₂, a * (e * e) = (e * e) * a := by
      intro a ha
      set w := e * a * e⁻¹ * a⁻¹ with hw
      have hwV : w ∈ d.V := d.commutator_mem_V_of_mem_C₀ (hEC he) (mem_sup_right ha)
      have hew : e * w * e⁻¹ = w := by
        rw [← mem_centralizer_iff.1 (hd.E_le_centralizer_V hGMS he) w hwV,
          mul_inv_cancel_right]
      have hww : w * w = 1 := hd.mul_self_eq_one_of_mem_V hGMS hwV
      have hea : e * a * e⁻¹ = w * a := by rw [hw]; group
      have : (e * e) * a * (e * e)⁻¹ = a := by
        calc (e * e) * a * (e * e)⁻¹ = e * (e * a * e⁻¹) * e⁻¹ := by group
          _ = e * (w * a) * e⁻¹ := by rw [hea]
          _ = (e * w * e⁻¹) * (e * a * e⁻¹) := by group
          _ = w * (w * a) := by rw [hew, hea]
          _ = a := by rw [← mul_assoc, hww, one_mul]
      calc a * (e * e) = (e * e) * a * (e * e)⁻¹ * (e * e) := by rw [this]
        _ = (e * e) * a := by group
    obtain ⟨v, hv, b, hb, hvb⟩ := hd.exists_mul_of_mem_VA hVA
    rw [hvb]
    refine mul_mem hv (hd.Zp_le_V ?_)
    rw [← hZA]
    refine ⟨hb, mem_centralizer_iff.2 fun a ha => ?_⟩
    have e := hcomm a ha
    rw [hvb] at e
    have hva := hd.V_comm_A₂ hv ha
    have e1 : v * (a * b) = v * (b * a) := by
      calc v * (a * b) = (v * a) * b := by group
        _ = (a * v) * b := by rw [hva]
        _ = v * b * a := by rw [mul_assoc, e]
        _ = v * (b * a) := by group
    exact mul_left_cancel e1
  refine ⟨hsq, fun x hx y hy => ?_⟩
  have hcen : ∀ v ∈ d.V, ∀ g ∈ d.E, v * g = g * v := fun v hv g hg =>
    (mem_centralizer_iff.1 (hd.E_le_centralizer_V hGMS hg) v hv)
  have hx2 := hsq x hx
  have hy2 := hsq y hy
  have hxy2 := hsq _ (mul_mem hx hy)
  have e : ⁅x, y⁆ = (x * y) * (x * y) * (x * x)⁻¹ * (y * y)⁻¹ := by
    have k : y⁻¹ * (x * x)⁻¹ = (x * x)⁻¹ * y⁻¹ := (hcen _ (inv_mem hx2) _ (inv_mem hy)).symm
    rw [commutatorElement_def]
    calc x * y * x⁻¹ * y⁻¹ = (x * y) * (x * y) * (y⁻¹ * (x * x)⁻¹) * y⁻¹ := by group
      _ = (x * y) * (x * y) * ((x * x)⁻¹ * y⁻¹) * y⁻¹ := by rw [k]
      _ = (x * y) * (x * y) * (x * x)⁻¹ * (y * y)⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem hxy2 (inv_mem hx2)) (inv_mem hy2)

theorem Hyp.card_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    Nat.card d.E = (2 ^ f) ^ 14 := by
  obtain ⟨ψ, hψ, hker, -, -⟩ := hd.exists_E_hom hGMS
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hψ, Subgroup.card_top, hker,
    Nat.card_congr (subgroupOfEquivOfLe (hd.VA_le_E hGMS)).toEquiv,
    hd.card_V_sup_A₂ hGMS] at h1
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (d.Zp.subgroupOf d.A₂)
  rw [d.card_A₂, Nat.card_congr (subgroupOfEquivOfLe d.Zp_le_A₂).toEquiv, d.card_Zp] at h2
  have hq : Nat.card (d.A₂ ⧸ d.Zp.subgroupOf d.A₂) = (2 ^ f) ^ 6 := by
    have : (2 ^ f) ^ 6 * 2 ^ f = Nat.card (d.A₂ ⧸ d.Zp.subgroupOf d.A₂) * 2 ^ f := by
      rw [← h2]
      ring
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) this).symm
  rw [← h1, hq]
  ring

theorem Hyp.sec3_6 (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    (∀ g ∈ normalizer ((d.V ⊔ d.B₂ : Subgroup G) : Set G), ∃ e ∈ d.E,
        ∃ c ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G), g = e * c) ∧
      d.E ⊔ (normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G)) ≤
        normalizer ((d.V ⊔ d.B₂ : Subgroup G) : Set G) ∧
      normalizer ((d.V ⊔ d.B₂ : Subgroup G) : Set G) ≤ normalizer (d.E : Set G) ∧
      d.E ⊓ d.B₂ = d.A₂ ∧
      (∃ ψ : d.E →* d.A₂ ⧸ d.Zp.subgroupOf d.A₂, Function.Surjective ψ ∧
        ψ.ker = (d.V ⊔ d.A₂).subgroupOf d.E ∧
        (∀ (e : d.E) (a : d.A₂), ∀ v ∈ d.V, (e : G)⁻¹ * d.t * e * d.t = v * a →
          ψ e = QuotientGroup.mk a) ∧
        ∀ c ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G), ∀ (e : d.E) (a : d.A₂)
          (he : c * e * c⁻¹ ∈ d.E) (ha : c * a * c⁻¹ ∈ d.A₂),
          ψ e = QuotientGroup.mk a →
            ψ ⟨c * e * c⁻¹, he⟩ = QuotientGroup.mk ⟨c * a * c⁻¹, ha⟩) ∧
      CFSG.centerIn d.E = d.V ∧ ElemAbMod d.V d.E ∧ Nat.card d.E = (2 ^ f) ^ 14 := by
  rw [← hd.B₄_eq_V_sup_B₂]
  refine ⟨fun g hg => hd.exists_E_mul_of_mem_normalizer hGMS hg,
    sup_le (fun e he => d.C₀_le_normalizer_B₄ (hd.E_le_C₀ hGMS he))
      (fun c hc => (hd.normalizer_B₄_inf_C.ge hc).1),
    hd.normalizer_B₄_le_normalizer_E hGMS, hd.E_inf_B₂ hGMS, hd.exists_E_hom hGMS,
    hd.centerIn_E hGMS, hd.elemAbMod_V_E hGMS, hd.card_E hGMS⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
