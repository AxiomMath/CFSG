module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3E

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.Common

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

@[expose] def E (d : Data G h) : Subgroup G :=
  closure {x | ∃ n ∈ d.N₂, ∃ w ∈ d.W, x = n * w * n⁻¹}

omit [Finite G] in
theorem conj_mem_E {n w : G} (hn : n ∈ d.N₂) (hw : w ∈ d.W) : n * w * n⁻¹ ∈ d.E :=
  subset_closure ⟨n, hn, w, hw, rfl⟩

omit [Finite G] in
theorem W_le_E (d : Data G h) : d.W ≤ d.E := fun w hw => by
  have := d.conj_mem_E (one_mem _) hw
  rwa [one_mul, inv_one, mul_one] at this

omit [Finite G] in
theorem V_le_E (d : Data G h) : d.V ≤ d.E := (le_sup_left : d.V ≤ d.W).trans d.W_le_E

omit [Finite G] in
theorem E_le {X : Subgroup G} (hX : ∀ n ∈ d.N₂, ∀ w ∈ d.W, n * w * n⁻¹ ∈ X) : d.E ≤ X :=
  (closure_le _).2 fun _ ⟨n, hn, w, hw, hx⟩ => hx ▸ hX n hn w hw

theorem N₂_le_normalizer_E (d : Data G h) : d.N₂ ≤ normalizer (d.E : Set G) := fun g hg =>
  mem_normalizer_of_conj_le fun x hx => by
    have hle : d.E ≤ d.E.comap (MulAut.conj g).toMonoidHom := E_le fun n hn w hw => by
      change g * (n * w * n⁻¹) * g⁻¹ ∈ d.E
      rw [show g * (n * w * n⁻¹) * g⁻¹ = (g * n) * w * (g * n)⁻¹ by group]
      exact conj_mem_E (mul_mem hg hn) hw
    exact hle hx

theorem Hyp.N₂_le_K₀ (hd : d.Hyp) :
    d.N₂ ≤ normalizer (d.ZtP : Set G) ⊓ centralizer (d.Zp : Set G) ⊓
      centralizer ({d.t} : Set G) := by
  rintro _ ⟨n, hn, rfl⟩
  refine hd.mem_K₀_of_mem_L (d.η_mem n) fun z hz => ?_
  obtain ⟨z', hz', rfl⟩ := hz
  rw [← map_mul, ← map_mul, N₂sub_comm_ZPsub hn hz']

theorem Hyp.N₂_le_normalizer_B₄ (hd : d.Hyp) : d.N₂ ≤ normalizer (d.B₄ : Set G) :=
  fun _ hn => d.le_normalizer_B₄ (hd.N₂_le_K₀ hn).1.1

theorem Hyp.N₂_le_C (hd : d.Hyp) : d.N₂ ≤ centralizer ({d.t} : Set G) :=
  fun _ hn => (hd.N₂_le_K₀ hn).2

theorem Hyp.F_I₄_le_C₀ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.F ⊓ centralizer (d.I₄ : Set G) ≤ d.C₀ := by
  have hVc := hd.FP_le_centralizer_V hGMS
  have hcomm : ∀ {c y : G}, c ∈ d.F ⊓ centralizer (d.I₄ : Set G) → y ∈ d.F ⊔ d.P →
      c * y * c⁻¹ * y⁻¹ ∈ d.V := fun hc hy => by
    have := hd.commutator_F_I₄_mem_V hGMS hc hy
    rwa [commutatorElement_def] at this
  have hVA : d.V ⊔ d.A₂ ≤ d.F ⊔ d.P :=
    sup_le (d.V_le_F.trans le_sup_left) (d.A₂_le_P.trans le_sup_right)
  have hconj : ∀ {c : G}, c ∈ d.F ⊓ centralizer (d.I₄ : Set G) → ∀ x ∈ d.B₄,
      c * x * c⁻¹ ∈ d.B₄ := by
    intro c hc x hx
    have hcv : ∀ v ∈ d.V, c * v * c⁻¹ = v := fun v hv => by
      rw [← mem_centralizer_iff.1 (hVc (mem_sup_left hc.1)) v hv, mul_inv_cancel_right]
    have hca : ∀ a ∈ d.A₂, c * a * c⁻¹ ∈ d.B₄ := fun a ha => by
      rw [show c * a * c⁻¹ = (c * a * c⁻¹ * a⁻¹) * a by group]
      exact mul_mem (hd.V_le_B₄ (hcomm hc (mem_sup_right (d.A₂_le_P ha)))) (hd.A₂_le_B₄ ha)
    have hct : c * d.t * c⁻¹ ∈ d.B₄ := by
      have hc' : c⁻¹ ∈ d.F ⊓ centralizer (d.I₄ : Set G) := inv_mem hc
      have h1 := hd.cr_F_I₄_mem hc'
      rw [inv_inv] at h1
      have hA : c * d.t * c⁻¹ * d.t ∈ d.A₂ :=
        d.Z₂p_le_A₂ (hd.Z₂p_eq.1 ▸ (le_sup_right : d.P ⊓ centralizer (d.I₄ : Set G) ≤
          d.Zp ⊔ (d.P ⊓ centralizer (d.I₄ : Set G))) h1)
      rw [show c * d.t * c⁻¹ = (c * d.t * c⁻¹ * d.t) * d.t by
        rw [mul_assoc _ d.t d.t, hd.t_mul_t, mul_one]]
      exact mul_mem (hd.A₂_le_B₄ hA) hd.t_mem_B₄
    obtain ⟨v, hv, a, ha, rfl | rfl⟩ := hd.exists_of_mem_B₄ hx
    · rw [show c * (v * a) * c⁻¹ = (c * v * c⁻¹) * (c * a * c⁻¹) by group, hcv v hv]
      exact mul_mem (hd.V_le_B₄ hv) (hca a ha)
    · rw [show c * (d.t * (v * a)) * c⁻¹ = (c * d.t * c⁻¹) * (c * v * c⁻¹) * (c * a * c⁻¹) by
        group, hcv v hv]
      exact mul_mem (mul_mem hct (hd.V_le_B₄ hv)) (hca a ha)
  intro c hc
  refine (hd.mem_C₀_iff hGMS).2 ⟨mem_normalizer_fintype fun x hx => hconj hc x hx,
    fun y hy => hcomm hc (hVA hy)⟩

theorem Hyp.W_le_C₀ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.W ≤ d.C₀ := by
  rw [hd.W_eq hGMS]
  exact sup_le (hd.V_le_B₄.trans (hd.B₄_le_C₀ hGMS)) (hd.F_I₄_le_C₀ hGMS)

theorem Hyp.W_le_centralizer_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.W ≤ centralizer (d.V : Set G) :=
  (hd.W_le_F hGMS).trans (le_sup_left.trans (hd.FP_le_centralizer_V hGMS))

theorem Hyp.E_le_C₀ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.E ≤ d.C₀ := E_le fun _ hn w hw =>
  (mem_normalizer_iff.1 (hd.normalizer_B₄_le_normalizer_C₀ hGMS (hd.N₂_le_normalizer_B₄ hn))
    w).1 (hd.W_le_C₀ hGMS hw)

theorem Hyp.E_le_centralizer_V (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.E ≤ centralizer (d.V : Set G) := E_le fun _ hn w hw =>
  (mem_normalizer_iff.1 (Prelim.normalizer_le_normalizer_centralizer d.V
    (hd.normalizer_B₄_le_normalizer_V hGMS (hd.N₂_le_normalizer_B₄ hn))) w).1
    (hd.W_le_centralizer_V hGMS hw)

theorem Hyp.Z₂p_le_W (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.Z₂p ≤ d.W := by
  rw [hd.Z₂p_eq.1, hd.W_eq hGMS]
  exact sup_le_sup hd.Zp_le_V (le_inf (hd.C₄_le_A₁.trans hd.A₁_le_F) inf_le_right)

theorem Hyp.A₂_le_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.A₂ ≤ d.E := by
  have hle : (A₂sub h).map d.η ≤
      (closure {y | ∃ n ∈ N₂sub h, ∃ w ∈ Z₂Psub h, y = n * w * n⁻¹}).map d.η :=
    map_mono A₂sub_le_closure_conj_Z₂Psub
  rw [MonoidHom.map_closure] at hle
  refine hle.trans ((closure_le _).2 ?_)
  rintro _ ⟨y, ⟨n, hn, w, hw, rfl⟩, rfl⟩
  rw [map_mul, map_mul, map_inv]
  exact d.conj_mem_E ⟨n, hn, rfl⟩ (hd.Z₂p_le_W hGMS ⟨w, hw, rfl⟩)

theorem Hyp.VA_le_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.V ⊔ d.A₂ ≤ d.E :=
  sup_le d.V_le_E (hd.A₂_le_E hGMS)

theorem Hyp.exists_E_cr (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) {w : G}
    (hw : w ∈ d.V ⊔ d.A₂) : ∃ e ∈ d.E, (e⁻¹ * d.t * e * d.t)⁻¹ * w ∈ d.V := by
  have hEC := hd.E_le_C₀ hGMS
  have hcen : ∀ {x v : G}, x ∈ d.V ⊔ d.A₂ → v ∈ d.V → x * v = v * x := fun hx hv =>
    hd.comm_V_of_mem_VA hGMS hx hv
  have hcr : ∀ e ∈ d.E, e⁻¹ * d.t * e * d.t ∈ d.V ⊔ d.A₂ := fun e he =>
    hd.cr_mem_VA hGMS (d.C₀_le_normalizer_B₄ (hEC he))
  let X : Subgroup G :=
    { carrier := {w | w ∈ d.V ⊔ d.A₂ ∧ ∃ e ∈ d.E, (e⁻¹ * d.t * e * d.t)⁻¹ * w ∈ d.V}
      mul_mem' := by
        rintro w₁ w₂ ⟨hw₁, e₁, he₁, hp₁⟩ ⟨hw₂, e₂, he₂, hp₂⟩
        refine ⟨mul_mem hw₁ hw₂, e₁ * e₂, mul_mem he₁ he₂, ?_⟩
        obtain ⟨v₀, hv₀, h12⟩ := hd.cr_mul_mod hGMS (hEC he₁) (hEC he₂)
        rw [h12]
        set c₁ := e₁⁻¹ * d.t * e₁ * d.t
        set c₂ := e₂⁻¹ * d.t * e₂ * d.t
        have k1 : c₁⁻¹ * v₀⁻¹ = v₀⁻¹ * c₁⁻¹ := hcen (inv_mem (hcr e₁ he₁)) (inv_mem hv₀)
        have k2 : c₂⁻¹ * v₀⁻¹ = v₀⁻¹ * c₂⁻¹ := hcen (inv_mem (hcr e₂ he₂)) (inv_mem hv₀)
        have k3 : c₂⁻¹ * (c₁⁻¹ * w₁) = (c₁⁻¹ * w₁) * c₂⁻¹ := hcen (inv_mem (hcr e₂ he₂)) hp₁
        have e : (v₀ * (c₁ * c₂))⁻¹ * (w₁ * w₂) = v₀⁻¹ * (c₁⁻¹ * w₁) * (c₂⁻¹ * w₂) := by
          calc (v₀ * (c₁ * c₂))⁻¹ * (w₁ * w₂) = c₂⁻¹ * (c₁⁻¹ * v₀⁻¹) * w₁ * w₂ := by group
            _ = c₂⁻¹ * (v₀⁻¹ * c₁⁻¹) * w₁ * w₂ := by rw [k1]
            _ = (c₂⁻¹ * v₀⁻¹) * (c₁⁻¹ * w₁) * w₂ := by group
            _ = (v₀⁻¹ * c₂⁻¹) * (c₁⁻¹ * w₁) * w₂ := by rw [k2]
            _ = v₀⁻¹ * (c₂⁻¹ * (c₁⁻¹ * w₁)) * w₂ := by group
            _ = v₀⁻¹ * ((c₁⁻¹ * w₁) * c₂⁻¹) * w₂ := by rw [k3]
            _ = v₀⁻¹ * (c₁⁻¹ * w₁) * (c₂⁻¹ * w₂) := by group
        rw [e]
        exact mul_mem (mul_mem (inv_mem hv₀) hp₁) hp₂
      one_mem' := ⟨one_mem _, 1, one_mem _, by simp [hd.t_mul_t]⟩
      inv_mem' := by
        rintro w ⟨hw, e, he, hp⟩
        refine ⟨inv_mem hw, e⁻¹, inv_mem he, ?_⟩
        obtain ⟨v₀, hv₀, h0⟩ := hd.cr_mul_mod hGMS (hEC he) (hEC (inv_mem he))
        set c := e⁻¹ * d.t * e * d.t
        set c' := e⁻¹⁻¹ * d.t * e⁻¹ * d.t
        rw [mul_inv_cancel, inv_one, one_mul, mul_one, hd.t_mul_t] at h0
        have hc' : c' = c⁻¹ * v₀⁻¹ := by
          calc c' = c⁻¹ * (v₀⁻¹ * (v₀ * (c * c'))) := by group
            _ = c⁻¹ * (v₀⁻¹ * 1) := by rw [← h0]
            _ = c⁻¹ * v₀⁻¹ := by group
        have k : c * (c⁻¹ * w)⁻¹ = (c⁻¹ * w)⁻¹ * c := hcen (hcr e he) (inv_mem hp)
        rw [hc']
        have e1 : (c⁻¹ * v₀⁻¹)⁻¹ * w⁻¹ = v₀ * (c⁻¹ * w)⁻¹ := by
          calc (c⁻¹ * v₀⁻¹)⁻¹ * w⁻¹ = v₀ * (c * (c⁻¹ * w)⁻¹ * c⁻¹) := by group
            _ = v₀ * ((c⁻¹ * w)⁻¹ * c * c⁻¹) := by rw [k]
            _ = v₀ * (c⁻¹ * w)⁻¹ := by group
        rw [e1]
        exact mul_mem hv₀ (inv_mem hp) }
  have hXV : d.V ≤ X := fun v hv => ⟨mem_sup_left hv, 1, one_mem _, by simpa [hd.t_mul_t] using hv⟩
  have hXC₄ : d.P ⊓ centralizer (d.I₄ : Set G) ≤ X := by
    intro a ha
    have haA : a ∈ d.A₂ :=
      d.Z₂p_le_A₂ (hd.Z₂p_eq.1 ▸ (le_sup_right : d.P ⊓ centralizer (d.I₄ : Set G) ≤
        d.Zp ⊔ (d.P ⊓ centralizer (d.I₄ : Set G))) ha)
    obtain ⟨c, hc, hca⟩ := hd.exists_F_I₄_cr_eq hGMS ha
    have hcW : c ∈ d.W := by
      rw [hd.W_eq hGMS]
      exact mem_sup_right hc
    refine ⟨mem_sup_right haA, c, d.W_le_E hcW, ?_⟩
    rw [hca, inv_mul_cancel]
    exact one_mem _
  have hXZ₂ : d.Z₂p ≤ X := by
    rw [hd.Z₂p_eq.1]
    exact sup_le (hd.Zp_le_V.trans hXV) hXC₄
  have hXN : ∀ n ∈ d.N₂, ∀ w ∈ X, n * w * n⁻¹ ∈ X := by
    rintro n hn w ⟨hw, e, he, hp⟩
    have hnB := hd.N₂_le_normalizer_B₄ hn
    refine ⟨(mem_normalizer_iff.1 (hd.normalizer_B₄_le_normalizer_VA hGMS hnB) w).1 hw,
      n * e * n⁻¹, (mem_normalizer_iff.1 (d.N₂_le_normalizer_E hn) e).1 he, ?_⟩
    rw [d.cr_conj (hd.N₂_le_C hn), show (n * (e⁻¹ * d.t * e * d.t) * n⁻¹)⁻¹ * (n * w * n⁻¹) =
      n * ((e⁻¹ * d.t * e * d.t)⁻¹ * w) * n⁻¹ by group]
    exact (mem_normalizer_iff.1 (hd.normalizer_B₄_le_normalizer_V hGMS hnB) _).1 hp
  have hA₂X : d.A₂ ≤ X := by
    have hle : (A₂sub h).map d.η ≤
        (closure {y | ∃ n ∈ N₂sub h, ∃ w ∈ Z₂Psub h, y = n * w * n⁻¹}).map d.η :=
      map_mono A₂sub_le_closure_conj_Z₂Psub
    rw [MonoidHom.map_closure] at hle
    refine hle.trans ((closure_le _).2 ?_)
    rintro _ ⟨y, ⟨n, hn, w, hw, rfl⟩, rfl⟩
    rw [map_mul, map_mul, map_inv]
    exact hXN _ ⟨n, hn, rfl⟩ _ (hXZ₂ ⟨w, hw, rfl⟩)
  exact ((sup_le hXV hA₂X) hw).2

theorem Hyp.inv_mul_mem_B₄ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {x y : G} (hx : x ∈ d.C₀) (hy : y ∈ d.C₀)
    (hxy : (x⁻¹ * d.t * x * d.t)⁻¹ * (y⁻¹ * d.t * y * d.t) ∈ d.V) : x⁻¹ * y ∈ d.B₄ := by
  refine hd.mem_B₄_of_mem_C₀ hGMS (mul_mem (inv_mem hx) hy) ?_
  obtain ⟨v₀, hv₀, h0⟩ := hd.cr_mul_mod hGMS hx (inv_mem hx)
  obtain ⟨v₁, hv₁, h1⟩ := hd.cr_mul_mod hGMS (inv_mem hx) hy
  set cx := x⁻¹ * d.t * x * d.t
  set cy := y⁻¹ * d.t * y * d.t
  set cx' := x⁻¹⁻¹ * d.t * x⁻¹ * d.t
  rw [mul_inv_cancel, inv_one, one_mul, mul_one, hd.t_mul_t] at h0
  have hcx' : cx' = cx⁻¹ * v₀⁻¹ := by
    calc cx' = cx⁻¹ * (v₀⁻¹ * (v₀ * (cx * cx'))) := by group
      _ = cx⁻¹ * (v₀⁻¹ * 1) := by rw [← h0]
      _ = cx⁻¹ * v₀⁻¹ := by group
  have hk : cx⁻¹ * v₀⁻¹ = v₀⁻¹ * cx⁻¹ :=
    hd.comm_V_of_mem_VA hGMS (inv_mem (hd.cr_mem_VA hGMS (d.C₀_le_normalizer_B₄ hx)))
      (inv_mem hv₀)
  rw [h1, hcx', hk, show v₁ * (v₀⁻¹ * cx⁻¹ * cy) = v₁ * v₀⁻¹ * (cx⁻¹ * cy) by group]
  exact mul_mem (mul_mem hv₁ (inv_mem hv₀)) hxy

theorem Hyp.exists_E_mul_of_mem_C₀ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp)
    {g : G} (hg : g ∈ d.C₀) : ∃ e ∈ d.E, ∃ b ∈ d.B₄, g = e * b := by
  obtain ⟨e, he, hep⟩ := hd.exists_E_cr hGMS (hd.cr_mem_VA hGMS (d.C₀_le_normalizer_B₄ hg))
  exact ⟨e, he, e⁻¹ * g, hd.inv_mul_mem_B₄ hGMS (hd.E_le_C₀ hGMS he) hg hep, by group⟩

theorem Hyp.E_eq (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.E = d.C₀ ⊓ centralizer (d.V : Set G) := by
  refine le_antisymm (le_inf (hd.E_le_C₀ hGMS) (hd.E_le_centralizer_V hGMS)) fun g hg => ?_
  obtain ⟨e, he, b, hb, rfl⟩ := hd.exists_E_mul_of_mem_C₀ hGMS hg.1
  have hbV : b ∈ centralizer (d.V : Set G) := by
    have := mul_mem (inv_mem (hd.E_le_centralizer_V hGMS he)) hg.2
    rwa [inv_mul_cancel_left] at this
  have hbVA : b ∈ d.V ⊔ d.A₂ :=
    hd.mem_VA_of_comm hGMS hb fun v hv => (mem_centralizer_iff.1 hbV v hv).symm
  exact mul_mem he (hd.VA_le_E hGMS hbVA)

theorem Hyp.normalizer_B₄_le_normalizer_E (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) : normalizer (d.B₄ : Set G) ≤ normalizer (d.E : Set G) := by
  intro n hn
  rw [hd.E_eq hGMS]
  exact Common.mem_normalizer_inf (hd.normalizer_B₄_le_normalizer_C₀ hGMS hn)
    (Prelim.normalizer_le_normalizer_centralizer d.V (hd.normalizer_B₄_le_normalizer_V hGMS hn))

theorem Hyp.exists_E_mul_of_mem_normalizer (hGMS : GMSK.GMSUnitarySharpKRankOneStatement)
    (hd : d.Hyp) {g : G} (hg : g ∈ normalizer (d.B₄ : Set G)) :
    ∃ e ∈ d.E, ∃ c ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G), g = e * c := by
  obtain ⟨e, he, hp⟩ := hd.exists_E_cr hGMS (hd.cr_mem_VA hGMS hg)
  set p := (e⁻¹ * d.t * e * d.t)⁻¹ * (g⁻¹ * d.t * g * d.t) with hpdef
  have heN : e ∈ normalizer (d.B₄ : Set G) := d.C₀_le_normalizer_B₄ (hd.E_le_C₀ hGMS he)
  have hk : g * e⁻¹ ∈ normalizer (d.B₄ : Set G) := mul_mem hg (inv_mem heN)
  have hcr : (g * e⁻¹)⁻¹ * d.t * (g * e⁻¹) * d.t =
      d.t * (e * (d.t * p * d.t) * e⁻¹) * d.t := by
    have e1 : g⁻¹ * d.t * g = (e⁻¹ * d.t * e * d.t) * p * d.t := by
      rw [hpdef, mul_inv_cancel_left, mul_assoc _ d.t d.t, hd.t_mul_t, mul_one]
    calc (g * e⁻¹)⁻¹ * d.t * (g * e⁻¹) * d.t = e * (g⁻¹ * d.t * g) * e⁻¹ * d.t := by group
      _ = e * ((e⁻¹ * d.t * e * d.t) * p * d.t) * e⁻¹ * d.t := by rw [e1]
      _ = d.t * (e * (d.t * p * d.t) * e⁻¹) * d.t := by group
  have hV : (g * e⁻¹)⁻¹ * d.t * (g * e⁻¹) * d.t ∈ d.V := by
    rw [hcr]
    exact hd.t_conj_mem_V ((mem_normalizer_iff.1 (hd.normalizer_B₄_le_normalizer_V hGMS heN)
      _).1 (hd.t_conj_mem_V hp))
  obtain ⟨c, hc, w, hw, hcw⟩ := hd.exists_mul_of_cr_mem_V hGMS hk hV
  have hc' : c ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G) :=
    hd.normalizer_B₄_inf_C.le hc
  have hwe : w * e ∈ d.E := mul_mem (d.V_le_E hw) he
  refine ⟨c * (w * e) * c⁻¹,
    (mem_normalizer_iff.1 (hd.normalizer_B₄_le_normalizer_E hGMS hc.1) _).1 hwe, c, hc', ?_⟩
  calc g = (g * e⁻¹) * e := by group
    _ = c * w * e := by rw [hcw]
    _ = c * (w * e) * c⁻¹ * c := by group

theorem Hyp.E_inf_B₄ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.E ⊓ d.B₄ = d.V ⊔ d.A₂ :=
  le_antisymm (fun _ hx => hd.mem_VA_of_comm hGMS hx.2 fun v hv =>
      (mem_centralizer_iff.1 (hd.E_le_centralizer_V hGMS hx.1) v hv).symm)
    (le_inf (hd.VA_le_E hGMS) hd.VA_le_B₄)

theorem Hyp.E_inf_B₂ (hGMS : GMSK.GMSUnitarySharpKRankOneStatement) (hd : d.Hyp) :
    d.E ⊓ d.B₂ = d.A₂ := by
  refine le_antisymm (fun x hx => ?_) (le_inf (hd.A₂_le_E hGMS) le_sup_right)
  have hxVA : x ∈ d.V ⊔ d.A₂ := (hd.E_inf_B₄ hGMS).le ⟨hx.1, hd.B₂_le_B₄ hx.2⟩
  obtain ⟨a, ha, e | e⟩ := hd.exists_of_mem_zpowers_sup d.A₂_le_L hx.2 <;> subst x
  · exact ha
  · exfalso
    apply hd.t_not_mem_VA hGMS
    have := mul_mem hxVA (inv_mem (mem_sup_right ha : a ∈ d.V ⊔ d.A₂))
    rwa [mul_inv_cancel_right] at this

end Data

end CFSG.LocalAnalysis.EvenBN.U5
