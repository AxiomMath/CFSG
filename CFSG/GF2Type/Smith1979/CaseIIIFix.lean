module

public import CFSG.LargeExtraspecial.S10SixA
public import CFSG.LargeExtraspecial.S10Dec
public import CFSG.LargeExtraspecial.S10Two

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

theorem exists_pair_of_finrank_eq_add_two {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {U W : Submodule (ZMod 2) V} (hUW : U ≤ W)
    (hdim : finrank (ZMod 2) W = finrank (ZMod 2) U + 2) :
    ∃ u₁ ∈ W, ∃ u₂ ∈ W, ∀ B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2,
      (∀ u ∈ U, ∀ v ∈ W, B u v = 0) → (∀ u ∈ W, ∀ v ∈ U, B u v = 0) →
      (∀ w ∈ W, B w w = 0) → B u₁ u₂ = 0 → ∀ u ∈ W, ∀ v ∈ W, B u v = 0 := by
  obtain ⟨C₀, hC₀⟩ := Submodule.exists_isCompl U
  set C := C₀ ⊓ W with hC
  have hCW : C ≤ W := inf_le_right
  have hsup : U ⊔ C = W := by
    have := sup_inf_assoc_of_le C₀ hUW
    rw [hC₀.sup_eq_top, top_inf_eq] at this
    exact this.symm
  have hinf : U ⊓ C = ⊥ := by
    rw [hC, ← inf_assoc, hC₀.inf_eq_bot, bot_inf_eq]
  have hCdim : finrank (ZMod 2) C = 2 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq U C
    rw [hsup, hinf, finrank_bot] at this
    omega
  let e := Module.finBasisOfFinrankEq (ZMod 2) C hCdim
  have h0 : (e 0 : V) ∈ W := hCW (e 0).2
  have h1 : (e 1 : V) ∈ W := hCW (e 1).2
  refine ⟨e 0, h0, e 1, h1, fun B hl hr halt hB u hu v hv => ?_⟩
  have hCC : ∀ c ∈ C, ∀ c' ∈ C, B c c' = 0 := by
    have hext : B.compl₁₂ C.subtype C.subtype = 0 := by
      refine LinearMap.ext_basis e e fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact halt _ h0
      · exact hB
      · have h := halt ((e 0 : V) + (e 1 : V)) (add_mem h0 h1)
        simp only [map_add, LinearMap.add_apply, halt _ h0, halt _ h1, hB, zero_add,
          add_zero] at h
        exact h
      · exact halt _ h1
    intro c hc c' hc'
    have := LinearMap.congr_fun₂ hext ⟨c, hc⟩ ⟨c', hc'⟩
    simpa using this
  rw [← hsup] at hu hv
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨a', ha', c', hc', rfl⟩ := Submodule.mem_sup.mp hv
  simp only [map_add, LinearMap.add_apply]
  rw [hl a ha a' (hUW ha'), hl a ha c' (hCW hc'), hr c (hCW hc) a' ha', hCC c hc c' hc']
  simp

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

variable (S g t) in
@[expose] noncomputable def Pcap : Submodule (ZMod 2) S.Qt :=
  S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t

variable (S g t) in
@[expose] noncomputable def Ulag : Submodule (ZMod 2) S.Qt := Pcap S g t ⊔ Vt S g t

theorem Ulag_le_Wt (X : Hyp10 S g t) : Ulag S g t ≤ Wt S g t :=
  sup_le inf_le_right (Vt_le_Wt X.H X.ht1)

theorem polar_Ulag (X : Hyp10 S g t) {x y : S.Qt} (hx : x ∈ Ulag S g t) (hy : y ∈ Ulag S g t) :
    polar S.q x y = 0 := by
  obtain ⟨p, hp, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨p', hp', v', hv', rfl⟩ := Submodule.mem_sup.mp hy
  have h1 : polar S.q p p' = 0 := polar_eq_zero_of_mem_clSub X.H.conj_ne hp.1 hp'.1
  have h2 : polar S.q p v' = 0 := by rw [polar_comm]; exact mem_Wt.mp hp.2 v' hv'
  have h3 : polar S.q v p' = 0 := mem_Wt.mp hp'.2 v hv
  have h4 : polar S.q v v' = 0 := polar_eq_zero_of_mem_Vt X.H X.ht1 hv hv'
  simp only [polar_add_left, polar_add_right, h1, h2, h3, h4, add_zero]

theorem q_Ulag (X : Hyp10 S g t) {x : S.Qt} (hx : x ∈ Ulag S g t) : S.q x = 0 := by
  obtain ⟨p, hp, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  have h1 : S.q p = 0 := S.q_eq_zero_of_mem_clSub_QG_inf_Qa X.H.conj_ne hp.1
  have h2 : S.q v = 0 := q_eq_zero_of_mem_Vt X.H X.ht1 hv
  have h3 : polar S.q p v = 0 := by rw [polar_comm]; exact mem_Wt.mp hp.2 v hv
  rw [QuadraticMap.map_add S.q p v, h1, h2, h3, add_zero, add_zero]

theorem finrank_Pcap (X : Hyp10 S g t) : finrank (ZMod 2) (Pcap S g t) + 1 = S.width :=
  finrank_clSub_inf_Wt X.H X.C X.ht X.ht1 X.hVQ

theorem finrank_Ulag (X : Hyp10 S g t) : finrank (ZMod 2) (Ulag S g t) = S.width := by
  have h1 := finrank_Pcap X
  have h2 := finrank_clSub_inf_Vt X.H X.C X.ht X.ht1 X.hVQ
  rw [X.h4] at h2
  have hinf : Pcap S g t ⊓ Vt S g t = S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := by
    rw [Pcap, inf_assoc, inf_eq_right.mpr (Vt_le_Wt X.H X.ht1)]
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq (Pcap S g t) (Vt S g t)
  rw [hinf, X.h4] at h3
  unfold Ulag
  omega

theorem orthogonal_Ulag (X : Hyp10 S g t) :
    LinearMap.BilinForm.orthogonal S.q.polarBilin (Ulag S g t) = Ulag S g t := by
  have hle : Ulag S g t ≤ LinearMap.BilinForm.orthogonal S.q.polarBilin (Ulag S g t) :=
    fun v hv u hu => by
      rw [polarBilin_apply_apply]
      exact polar_Ulag X hu hv
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  rw [LinearMap.BilinForm.finrank_orthogonal S.q_nondegenerate, finrank_Ulag X,
    S.finrank_Qt_eq_two_mul_width]
  omega

theorem finrank_Wt_eq_add_two (X : Hyp10 S g t) (h6 : S.width = 6) :
    finrank (ZMod 2) (Wt S g t) = finrank (ZMod 2) (Ulag S g t) + 2 := by
  have h1 := finrank_Wt (S := S) (g := g) (t := t)
  rw [X.h4, S.finrank_Qt_eq_two_mul_width] at h1
  rw [finrank_Ulag X]
  omega

theorem Lbar_sub_mem_Vt (X : Hyp10 S g t) {s : S.O} (hs : s ∈ S.Lbar g) {x : S.Qt}
    (hx : x ∈ Ulag S g t) : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x ∈ Vt S g t := by
  obtain ⟨p, hp, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  have h1 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ Vt S g t :=
    ((Submodule.span_singleton_le_iff_mem _ _).mpr (cl_a_mem_Vt X.ht))
      (Lbar_apply_sub_mem_span' X.haQ hp.1 hs)
  have h2 : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ Vt S g t :=
    sub_mem (apply_mem_Vt_of_mem_Rbar X.haQ (Lbar_le_Rbar X.ht hs) hv) hv
  have e : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (p + v) - (p + v) =
      ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p) + ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) := by
    rw [map_add]
    abel
  rw [e]
  exact add_mem h1 h2

theorem polar_sub_inv_apply (s : S.O) (x y : S.Qt) :
    polar S.q x ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) y - y) =
      polar S.q (((s⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x - x) y := by
  rw [polar_sub_right, polar_sub_left,
    ← TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (s⁻¹).2 x
      ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) y), inv_apply_apply_O]

theorem Lbar_sub_mem_Ulag (X : Hyp10 S g t) {s : S.O} (hs : s ∈ S.Lbar g) {w : S.Qt}
    (hw : w ∈ Wt S g t) : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Ulag S g t := by
  rw [← orthogonal_Ulag X, LinearMap.BilinForm.mem_orthogonal_iff]
  intro x hx
  simp only [polarBilin_apply_apply]
  rw [polar_sub_inv_apply]
  exact mem_Wt.mp hw _ (Lbar_sub_mem_Vt X (inv_mem hs) hx)

@[expose] noncomputable def fixForm (s : S.O) : S.Qt →ₗ[ZMod 2] S.Qt →ₗ[ZMod 2] ZMod 2 :=
  S.q.polarBilin.compl₂
    (((s : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - LinearMap.id)

theorem fixForm_apply (s : S.O) (u v : S.Qt) :
    fixForm s u v = polar S.q u ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) := by
  simp [fixForm, polarBilin_apply_apply]

theorem fixForm_one (u v : S.Qt) : fixForm (1 : S.O) u v = 0 := by
  rw [fixForm_apply]
  simp

theorem fixForm_left_eq_zero (X : Hyp10 S g t) {s : S.O} (hs : s ∈ S.Lbar g) {u v : S.Qt}
    (hu : u ∈ Ulag S g t) (hv : v ∈ Wt S g t) : fixForm s u v = 0 := by
  rw [fixForm_apply, polar_sub_inv_apply]
  exact mem_Wt.mp hv _ (Lbar_sub_mem_Vt X (inv_mem hs) hu)

theorem fixForm_right_eq_zero (X : Hyp10 S g t) {s : S.O} (hs : s ∈ S.Lbar g) {u v : S.Qt}
    (hu : u ∈ Wt S g t) (hv : v ∈ Ulag S g t) : fixForm s u v = 0 := by
  rw [fixForm_apply, polar_comm]
  exact mem_Wt.mp hu _ (Lbar_sub_mem_Vt X hs hv)

theorem fixForm_self (X : Hyp10 S g t) {s : S.O} (hs : s ∈ S.Lbar g) {w : S.Qt}
    (hw : w ∈ Wt S g t) : fixForm s w w = 0 := by
  have hq := q_Ulag X (Lbar_sub_mem_Ulag X hs hw)
  rw [sub_eq_add_vec (ZMod 2), QuadraticMap.map_add S.q,
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup s.2 w, CharTwo.add_self_eq_zero,
    zero_add] at hq
  rw [fixForm_apply, polar_sub_right, polar_self_eq_zero S.q w, sub_zero, polar_comm]
  exact hq

theorem fixForm_mul (X : Hyp10 S g t) {s₁ s₂ : S.O} (h₁ : s₁ ∈ S.Lbar g) (h₂ : s₂ ∈ S.Lbar g)
    {u v : S.Qt} (hu : u ∈ Wt S g t) (hv : v ∈ Wt S g t) :
    fixForm (s₁ * s₂) u v = fixForm s₁ u v + fixForm s₂ u v := by
  have hV := Lbar_sub_mem_Vt X h₁ (Lbar_sub_mem_Ulag X h₂ hv)
  have e : ((s₁ * s₂ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v =
      ((s₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) + ((s₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) +
        ((s₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) -
          ((s₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v)) := by
    rw [coe_mul_apply, map_sub]
    abel
  have h0 : polar S.q u ((s₁ : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v) -
      ((s₂ : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v)) = 0 := by
    rw [polar_comm]
    exact mem_Wt.mp hu _ hV
  rw [fixForm_apply, fixForm_apply, fixForm_apply, e, polar_add_right, polar_add_right, h0,
    add_zero, add_comm]

theorem exists_mem_fixWstar_of_width_six (X : Hyp10 S g t) (h6 : S.width = 6) :
    ∃ x ∈ S.Lbar g, x ∉ Nbar S g t ∧ x ∈ fixWstar X := by
  obtain ⟨u₁, hu₁, u₂, hu₂, key⟩ :=
    exists_pair_of_finrank_eq_add_two (Ulag_le_Wt X) (finrank_Wt_eq_add_two X h6)
  let φ : ↥(S.Lbar g) →* Multiplicative (ZMod 2) :=
    { toFun := fun s => Multiplicative.ofAdd (fixForm (s : S.O) u₁ u₂)
      map_one' := by
        change Multiplicative.ofAdd (fixForm ((1 : S.Lbar g) : S.O) u₁ u₂) = 1
        rw [Subgroup.coe_one, fixForm_one]
        rfl
      map_mul' := fun s₁ s₂ => by
        change Multiplicative.ofAdd (fixForm ((s₁ * s₂ : S.Lbar g) : S.O) u₁ u₂) = _
        rw [Subgroup.coe_mul, fixForm_mul X s₁.2 s₂.2 hu₁ hu₂]
        rfl }
  have hker : ∀ s : ↥(S.Lbar g), s ∈ φ.ker → (s : S.O) ∈ fixWstar X := by
    intro s hs
    have h0 : fixForm (s : S.O) u₁ u₂ = 0 := by
      have h := MonoidHom.mem_ker.mp hs
      change Multiplicative.ofAdd (fixForm (s : S.O) u₁ u₂) = 1 at h
      exact h
    have hall := key (fixForm (s : S.O)) (fun u hu v hv => fixForm_left_eq_zero X s.2 hu hv)
      (fun u hu v hv => fixForm_right_eq_zero X s.2 hu hv)
      (fun w hw => fixForm_self X s.2 hw) h0
    refine ⟨Lbar_le_Rbar X.ht s.2, fun w hw => ?_⟩
    rw [← orthogonal_Wt (S := S) (g := g) t, LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    simp only [polarBilin_apply_apply]
    rw [← fixForm_apply]
    exact hall u hu w hw
  by_contra hcon
  have hle : Nat.card φ.ker ≤ 2 ^ (S.width - 3) := by
    rw [← X.card_Abar]
    let f : φ.ker → ↥(S.Lbar g ⊓ Nbar S g t) := fun s =>
      ⟨(s.1 : S.O), s.1.2, by
        by_contra hN
        exact hcon ⟨(s.1 : S.O), s.1.2, hN, hker s.1 s.2⟩⟩
    refine Nat.card_le_card_of_injective f fun a b hab => ?_
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  have hrange : Nat.card φ.range ≤ 2 := by
    have h1 := Subgroup.card_le_card_group φ.range
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    omega
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [X.C.card_Lbar, h6] at hmul
  rw [h6] at hle
  have := Nat.mul_le_mul hle hrange
  omega

theorem exists_dirDec_of_width_six (hCE : CentralExtInput.{u}) (X : Hyp10 S g t)
    (h6 : S.width = 6) :
    ∃ Xb Yb : Subgroup S.O, DirDec S g t Xb Yb ∧ Nbar S g t ≤ Xb ∧
      (∀ r ∈ Xb, ∀ w ∈ Wt S g t, (r : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Vt S g t) ∧
      ∃ y ∈ Yb, y ∈ S.Lbar g ∧ y ∉ Nbar S g t := by
  obtain ⟨x, hxL, hxN, hxW⟩ := exists_mem_fixWstar_of_width_six X h6
  obtain ⟨Y, -, hiso, hsup, hinf, hcomm, hW, y, hyY, hyL, hyN⟩ :=
    timmesfeld_10_2 hCE X hxL hxN hxW.2
  exact ⟨R0 S g t x, Y, ⟨hsup, hinf, hcomm, hiso⟩, le_sup_left, hW, y, hyY, hyL, hyN⟩

end CFSG.GF2Type.Smith1979
