module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A76S2h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2d

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Q511 CFSG.Quasithin.H13.L32A.M76 CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H Y : Subgroup G} {γ γ' : F8.Geom T L H}
  {g : ↥((L ⊔ T) ⊔ H)}

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.S2.Ctx_F4

@[expose] noncomputable def Ne_F4 (C : Ctx_F4 G T L V H Y)
    (e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) : Subgroup G :=
  ((Subgroup.normalizer (Subgroup.zpowers e : Set _)).comap (FixR.rho C.h91_F4)).map H.subtype

variable (C : Ctx_F4 G T L V H Y)
include C

theorem mem_Ne_F4 {e : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} {x : G} :
    x ∈ C.Ne_F4 e ↔ ∃ hx : x ∈ H,
      FixR.rho C.h91_F4 ⟨x, hx⟩ * e * (FixR.rho C.h91_F4 ⟨x, hx⟩)⁻¹ ∈ Subgroup.zpowers e := by
  have : Finite (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :=
    Finite.of_injective _ MulEquiv.toEquiv_injective
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have hy' : FixR.rho C.h91_F4 y ∈ Subgroup.normalizer (Subgroup.zpowers e : Set _) := hy
    exact (Subgroup.mem_normalizer_iff.mp hy' e).mp (Subgroup.mem_zpowers e)
  · rintro ⟨hx, h⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    show FixR.rho C.h91_F4 ⟨x, hx⟩ ∈ Subgroup.normalizer (Subgroup.zpowers e : Set _)
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h j

theorem exists_S_F4 (s : F8Setup T V L H γ γ' g) :
    ∃ S : Subgroup G, S ≤ H ∧ quasithinIsSylowTwo S ∧ F8.Uγ V H (g : G) ≤ S := by
  obtain ⟨c, hcH, hc⟩ := S1549C.exists_alpha C.h98 s
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  rw [hl1eq] at hc
  have hT := C.S.hyp.fsu.sylow
  refine ⟨Quasithin.conjSub c⁻¹ T, ?_, ⟨hT.1.map _, ?_⟩, ?_⟩
  · intro x hx
    rw [Quasithin.mem_conjSub, inv_inv] at hx
    have hx' := Setting147.TH' C.S hx
    have e : x = c⁻¹ * (c * x * c⁻¹) * c := by group
    rw [e]
    exact H.mul_mem (H.mul_mem (H.inv_mem hcH) hx') hcH
  · unfold Quasithin.conjSub
    rw [show (MulAut.conj c⁻¹).toMonoidHom = ((MulAut.conj c⁻¹ : G ≃* G) : G →* G) from rfl,
      Subgroup.index_map_equiv]
    exact hT.2
  · intro u hu
    rw [Quasithin.mem_conjSub, inv_inv]
    exact Setting147.R1_le_T C.S (hc (Quasithin.mul_mem_conjSub hu))

theorem card_le_two_mul_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {e₁ e₂ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} (hL : Lines e₁ e₂)
    (hEp : ∀ e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)),
      Lines.InE e₁ e₂ e)
    (he₁ : e₁ ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)))
    {S : Subgroup G} (hSH : S ≤ H) : Nat.card S ≤ 2 * Nat.card ↥(S ⊓ C.Ne_F4 e₁) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :=
    Finite.of_injective _ MulEquiv.toEquiv_injective

  have hout : ∀ x : ↥H, (x : G) ∉ C.Ne_F4 e₁ →
      FixR.rho C.h91_F4 x * e₁ * (FixR.rho C.h91_F4 x)⁻¹ ∈ Subgroup.zpowers e₂ := by
    intro x hx
    rcases hL.conj_mem_lines (hEp _ (C.conj_mem_E_F4 (C.rho_mem_X_F4 x) he₁)) with h | h
    · exact absurd ((C.mem_Ne_F4).mpr ⟨x.2, h⟩) hx
    · exact h
  have hprod : ∀ x y : ↥H, (x : G) ∉ C.Ne_F4 e₁ → (y : G) ∉ C.Ne_F4 e₁ →
      ((x⁻¹ * y : ↥H) : G) ∈ C.Ne_F4 e₁ := by
    intro x y hx hy
    refine (C.mem_Ne_F4).mpr ⟨(x⁻¹ * y).2, ?_⟩
    have h := conj_mem_zpowers_of_swap
      (by rw [orderOf_eq_prime hL.h5₁ hL.ne_one₁, orderOf_eq_prime hL.h5₂ hL.symm.ne_one₁])
      (hout x hx) (hout y hy)
    rw [map_mul, map_inv]
    exact h

  by_cases hall : S ≤ C.Ne_F4 e₁
  · have : S ⊓ C.Ne_F4 e₁ = S := inf_eq_left.mpr hall
    rw [this]
    omega
  obtain ⟨s₀, hs₀S, hs₀N⟩ : ∃ s₀ ∈ S, s₀ ∉ C.Ne_F4 e₁ := by
    by_contra h
    push Not at h
    exact hall h
  let f : ↥S → ↥(S ⊓ C.Ne_F4 e₁) × Bool := fun s =>
    if hs : (s : G) ∈ C.Ne_F4 e₁ then (⟨s, s.2, hs⟩, false)
    else (⟨s₀⁻¹ * s, S.mul_mem (S.inv_mem hs₀S) s.2, by
      have := hprod ⟨s₀, hSH hs₀S⟩ ⟨s, hSH s.2⟩ hs₀N hs
      simpa using this⟩, true)
  have hf : Function.Injective f := by
    intro s s' hss'
    simp only [f] at hss'
    by_cases hs : (s : G) ∈ C.Ne_F4 e₁ <;> by_cases hs' : (s' : G) ∈ C.Ne_F4 e₁ <;>
      simp only [hs, hs', dite_true, dite_false, Prod.mk.injEq] at hss'
    · exact Subtype.ext (congrArg (fun z : ↥(S ⊓ C.Ne_F4 e₁) => (z : G)) hss'.1)
    · exact absurd hss'.2 (by decide)
    · exact absurd hss'.2 (by decide)
    · apply Subtype.ext
      have := congrArg Subtype.val hss'.1
      simpa using this
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

theorem Ne_le_Ne_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {e₁ e₂ : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))} (hL : Lines e₁ e₂)
    (hEp : ∀ e ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H)),
      Lines.InE e₁ e₂ e)
    (he₂ : e₂ ∈ autOn (tildeOf (fsuV1 T V) Y) (tildeOf (fsuV1 T V) (conjClosure V H))) :
    C.Ne_F4 e₁ ≤ C.Ne_F4 e₂ := by
  have : Finite (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :=
    Finite.of_injective _ MulEquiv.toEquiv_injective
  intro x hx
  obtain ⟨hxH, h1⟩ := (C.mem_Ne_F4).mp hx
  refine (C.mem_Ne_F4).mpr ⟨hxH, ?_⟩
  rcases hL.symm.conj_mem_lines (hL.inE_swap (hEp _ (C.conj_mem_E_F4 (C.rho_mem_X_F4 _) he₂))) with
    h | h
  · exact h
  · exfalso
    have hmem : e₂ ∈ Subgroup.zpowers e₁ ⊓ Subgroup.zpowers e₂ :=
      ⟨mem_zpowers_of_conj h1 h, Subgroup.mem_zpowers e₂⟩
    rw [hL.zpowers_inf_eq_bot, Subgroup.mem_bot] at hmem
    exact hL.symm.ne_one₁ hmem

theorem rho_mem_cw_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (D : Good_F4 C γ γ' g e₁ e₂ b) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hUS : F8.Uγ V H (g : G) ≤ S) (t : ↥H) (ht : (t : G) ∈ S ⊓ C.Ne_F4 e₁) :
    ∀ w ∈ cw b, FixR.rho C.h91_F4 t w ∈ cw b := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Finite (MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))) :=
    Finite.of_injective _ MulEquiv.toEquiv_injective
  have hL := D.lines
  have hV := C.sq_eq_one_F4
  have hb2 : b ^ 2 = 1 := by
    have := D.Bz ▸ D.bB
    have hB := (C.unpack_F4 D.s (by rw [D.mγ]; norm_num) (by rw [D.mγ, D.mH])).2.2.1
    exact hB.2 b D.bB
  obtain ⟨u₀, hu₀, hbu⟩ := (FixR.mem_autOn_tilde_iff C.h91_F4 (C.h98.Uγ_le_H D.s)).mp D.bB

  have hcwb : (cw e₁).map (commHom b) = cw b :=
    eq_of_le_of_rk_le hV (Subgroup.map_mono le_top) (by rw [(hL.rk_inv hb2 D.inv).1, D.rk_cw])
  obtain ⟨t, htH⟩ := t
  obtain ⟨htS, htN⟩ := ht
  obtain ⟨htH2, hte⟩ := (C.mem_Ne_F4).mp htN
  set a := FixR.rho C.h91_F4 ⟨t, htH⟩ with ha
  replace hte : a * e₁ * a⁻¹ ∈ Subgroup.zpowers e₁ := hte
  clear htH2

  have hae₁ : ∀ w ∈ cw e₁, a w ∈ cw e₁ := by
    intro w hw
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hte
    have hmap : (cw e₁).map (a : _ →* _) = cw (a * e₁ * a⁻¹) := (cw_conj a e₁).symm
    have h1 : cw (a * e₁ * a⁻¹) = cw e₁ := by
      classical
      have hte' := hte
      rw [mem_zpowers_iff_mem_range_orderOf, orderOf_eq_prime hL.h5₁ hL.ne_one₁,
        Finset.mem_image] at hte'
      obtain ⟨k, hk5, hk⟩ := hte'
      rw [Finset.mem_range] at hk5
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · exfalso
          rw [h0, pow_zero] at hk
          exact hL.ne_one₁ (by
            have := congrArg (fun z => a⁻¹ * z * a) hk
            simpa [mul_assoc] using this.symm)
        · exact h0
      rw [← hk]
      exact hL.cw_pow₁ hk0 hk5
    rw [← h1, ← hmap]
    exact ⟨w, hw, rfl⟩

  have hb' : ∀ w ∈ cw e₁, (a * b * a⁻¹) w = b w := by
    set x := b * (a * b * a⁻¹) with hx
    have hx2 : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
      have hm : (u₀ : G) * (t * u₀ * t⁻¹) ∈ S :=
        S.mul_mem (hUS hu₀) (S.mul_mem (S.mul_mem htS (hUS hu₀)) (S.inv_mem htS))
      obtain ⟨k, hk⟩ := hS2 ⟨_, hm⟩
      refine ⟨k, ?_⟩
      have e : x = FixR.rho C.h91_F4 (u₀ * (⟨t, htH⟩ * u₀ * (⟨t, htH⟩ : ↥H)⁻¹)) := by
        rw [hx, map_mul, map_mul, map_mul, map_inv, hbu, ha]
      rw [e, ← map_pow]
      have : (u₀ * (⟨t, htH⟩ * u₀ * (⟨t, htH⟩ : ↥H)⁻¹)) ^ 2 ^ k = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]

    have hinv' : (a * b * a⁻¹) * e₁ * (a * b * a⁻¹)⁻¹ = e₁⁻¹ := by
      have h2 := conj_inv_mem_zpowers hte
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h2
      have hbi : b * e₁ ^ i * b⁻¹ = (e₁ ^ i)⁻¹ := by
        rw [← conj_zpow, D.inv, inv_zpow]
      calc (a * b * a⁻¹) * e₁ * (a * b * a⁻¹)⁻¹ = a * (b * (a⁻¹ * e₁ * a) * b⁻¹) * a⁻¹ := by
            group
        _ = a * (e₁ ^ i)⁻¹ * a⁻¹ := by rw [← hi, hbi]
        _ = (a * e₁ ^ i * a⁻¹)⁻¹ := by group
        _ = e₁⁻¹ := by rw [hi]; group
    have hxe : x * e₁ = e₁ * x := by
      have h1 : x * e₁ * x⁻¹ = e₁ := by
        calc x * e₁ * x⁻¹ = b * ((a * b * a⁻¹) * e₁ * (a * b * a⁻¹)⁻¹) * b⁻¹ := by
              rw [hx]; group
          _ = e₁ := by
            rw [hinv']
            calc b * e₁⁻¹ * b⁻¹ = (b * e₁ * b⁻¹)⁻¹ := by group
              _ = e₁ := by rw [D.inv, inv_inv]
      calc x * e₁ = x * e₁ * x⁻¹ * x := by group
        _ = e₁ * x := by rw [h1]
    have htriv := trivial_of_comm hV hx2 hxe hL.h5₁ (fun u hu => mem_map_commHom_of_comm hxe hu)
      (map_commHom_invariant rfl (fun _ _ => Subgroup.mem_top _)) hL.fpf₁
      (rk_cond_five hL.rk₁)
    intro w hw
    have h1 := htriv w hw
    rw [hx, MulAut.mul_apply] at h1
    have hbb : b (b ((a * b * a⁻¹) w)) = (a * b * a⁻¹) w := by
      rw [← MulAut.mul_apply, ← pow_two, hb2, MulAut.one_apply]
    rw [← hbb, h1]

  intro w hw
  rw [← hcwb] at hw ⊢
  obtain ⟨w₁, hw₁, rfl⟩ := hw
  refine ⟨a w₁, hae₁ w₁ hw₁, ?_⟩
  rw [commHom_apply, commHom_apply, map_mul, map_inv, ← hb' _ (hae₁ w₁ hw₁)]
  simp [MulAut.mul_apply]

theorem S₁_le_normalizer_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (D : Good_F4 C γ γ' g e₁ e₂ b) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hUS : F8.Uγ V H (g : G) ≤ S) :
    S ⊓ C.Ne_F4 e₁ ≤
      Subgroup.normalizer ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G) := by
  intro t ht
  have htH : t ∈ H := (C.mem_Ne_F4).mp ht.2 |>.1
  have hacw := C.rho_mem_cw_F4 D hS2 hUS ⟨t, htH⟩ ht
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  rw [D.A_eq] at hy ⊢
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨⟨t * z * t⁻¹, conj_mem_UH htH z.2⟩, Subgroup.mem_comap.mpr ?_, rfl⟩
  rw [C.piU_conj_F4 ⟨t, htH⟩ z]
  exact hacw _ hz

end Ctx_F4

end CFSG.Quasithin.H13.L32A.S2

end
