module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Red
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67RedAut
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.ComponentClassification.PerfectAutomorphisms
open scoped commutatorElement

section Lift

variable {Q : Type} [Group Q]

theorem commutator_mul_central_p67 {a b wa wb : Q} (hwa : wa ∈ Subgroup.center Q)
    (hwb : wb ∈ Subgroup.center Q) : ⁅a * wa, b * wb⁆ = ⁅a, b⁆ := by
  have h1 := Subgroup.mem_center_iff.mp hwa
  have h2 := Subgroup.mem_center_iff.mp hwb
  simp only [commutatorElement_def, mul_inv_rev]
  have e1 : a * wa * (b * wb) * (wa⁻¹ * a⁻¹) * (wb⁻¹ * b⁻¹) =
      a * (wa * b) * wb * wa⁻¹ * a⁻¹ * wb⁻¹ * b⁻¹ := by group
  rw [e1, ← h1 b]
  have e2 : a * (b * wa) * wb * wa⁻¹ * a⁻¹ * wb⁻¹ * b⁻¹ =
      a * b * (wa * wb * wa⁻¹) * a⁻¹ * wb⁻¹ * b⁻¹ := by group
  rw [e2]
  have h3 : wa * wb * wa⁻¹ = wb := by
    rw [h2 wa]; group
  rw [h3]
  have e3 : a * b * wb * a⁻¹ * wb⁻¹ * b⁻¹ = a * b * (wb * a⁻¹) * wb⁻¹ * b⁻¹ := by group
  rw [e3, ← h2 a⁻¹]
  group

theorem mem_fixSub_onCenterQuotient {α : MulAut Q} {a : Q} :
    QuotientGroup.mk' (Subgroup.center Q) a ∈ fixSub (onCenterQuotient α) ↔
      a⁻¹ * α a ∈ Subgroup.center Q := by
  rw [mem_fixSub, onCenterQuotient_apply_mk, eq_comm]
  exact QuotientGroup.eq

theorem commutator_fixSub_le_map (α : MulAut Q) :
    ⁅fixSub (onCenterQuotient α), fixSub (onCenterQuotient α)⁆ ≤
      (fixSub α).map (QuotientGroup.mk' (Subgroup.center Q)) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) y
  have ha := mem_fixSub_onCenterQuotient.mp hx
  have hb := mem_fixSub_onCenterQuotient.mp hy
  refine ⟨⁅a, b⁆, ?_, by simp [commutatorElement_def]⟩
  rw [SetLike.mem_coe, mem_fixSub]
  have hαa : α a = a * (a⁻¹ * α a) := by group
  have hαb : α b = b * (b⁻¹ * α b) := by group
  have : α ⁅a, b⁆ = ⁅α a, α b⁆ := by simp [commutatorElement_def]
  rw [this, hαa, hαb]
  exact commutator_mul_central_p67 ha hb

theorem fixSub_onCenterQuotient_le_map [Finite Q] (α : MulAut Q) {r : ℕ} (hr : r.Prime)
    (hαr : α ^ r = 1) (hcop : ¬ r ∣ Nat.card (Subgroup.center Q)) :
    fixSub (onCenterQuotient α) ≤ (fixSub α).map (QuotientGroup.mk' (Subgroup.center Q)) := by
  classical
  intro x hx
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Q) x
  have ha := mem_fixSub_onCenterQuotient.mp hx
  have : Fact r.Prime := ⟨hr⟩
  let S : Type := {y : Q // a⁻¹ * y ∈ Subgroup.center Q}
  have hmap : ∀ y : S, a⁻¹ * α y.1 ∈ Subgroup.center Q := by
    intro y
    have hy := y.2
    have hz : α (a⁻¹ * y.1) ∈ Subgroup.center Q := by
      have hchar := (Subgroup.characteristic_iff_map_eq.mp
        (inferInstance : (Subgroup.center Q).Characteristic)) α
      have hm := Subgroup.mem_map_of_mem α.toMonoidHom hy
      rw [hchar] at hm
      exact hm
    have e : a⁻¹ * α y.1 = (a⁻¹ * α a) * α (a⁻¹ * y.1) := by
      simp [map_mul, mul_assoc]
    rw [e]
    exact Subgroup.mul_mem _ ha hz
  let f : Function.End S := fun y => ⟨α y.1, hmap y⟩
  have hfpow : ∀ n : ℕ, ∀ y : S, ((f ^ n) y).1 = (α ^ n) y.1 := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', pow_succ']
      show (α ((f ^ n) y).1 : Q) = _
      rw [ih]
      rfl
  have hf1 : f ^ r ^ 1 = 1 := by
    funext y
    apply Subtype.ext
    rw [pow_one, hfpow, hαr]
    rfl
  have : Fintype S := Fintype.ofFinite S
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := r) (n := 1) hf1
  have hS : Nat.card S = Nat.card (Subgroup.center Q) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨a⁻¹ * y.1, y.2⟩
        invFun := fun z => ⟨a * z.1, by simp⟩
        left_inv := fun y => by apply Subtype.ext; simp
        right_inv := fun z => by apply Subtype.ext; simp }
  have hcard : Fintype.card S = Nat.card (Subgroup.center Q) := by
    rw [← hS, Nat.card_eq_fintype_card]
  by_cases hfix : Nonempty (Function.fixedPoints f)
  · obtain ⟨⟨y, hyf⟩⟩ := hfix
    refine ⟨y.1, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_fixSub]
      exact congrArg Subtype.val hyf
    · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      have := Subgroup.inv_mem _ y.2
      simp at this ⊢
      exact this
  · exfalso
    have h0 : Fintype.card (Function.fixedPoints f) = 0 := by
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun z => hfix ⟨z⟩⟩
    rw [h0, hcard] at hmod
    apply hcop
    exact (Nat.modEq_zero_iff_dvd).mp hmod

end Lift

section Bridge

@[expose] def N3Full (Y : Type) [Group Y] (V Z : Subgroup (MulAut Y)) : Prop :=
  ∀ v ∈ V, v ≠ 1 → ∀ c ∈ fixSub v, MulAut.conj c ∈ normalizer (Z : Set (MulAut Y))

@[expose] def N3Deriv (Y : Type) [Group Y] (V Z : Subgroup (MulAut Y)) : Prop :=
  ∀ v ∈ V, v ≠ 1 → ∀ c ∈ ⁅fixSub v, fixSub v⁆, MulAut.conj c ∈ normalizer (Z : Set (MulAut Y))

theorem N3Full.deriv {Y : Type} [Group Y] {V Z : Subgroup (MulAut Y)} (h : N3Full Y V Z) :
    N3Deriv Y V Z := fun v hv hne c hc => by
  refine h v hv hne c ?_
  have hle : ⁅fixSub v, fixSub v⁆ ≤ fixSub v := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact (fixSub v).mul_mem ((fixSub v).mul_mem ((fixSub v).mul_mem hx hy) ((fixSub v).inv_mem hx))
      ((fixSub v).inv_mem hy)
  exact hle hc

@[expose] def CF67CoreFull (Y : Type) [Group Y] [Finite Y] : Prop :=
  IsSimpleGroup Y → (∃ a b : Y, a * b ≠ b * a) →
    ∀ (r : ℕ) (V Z : Subgroup (MulAut Y)), N2Cfg Y r V Z → N3Full Y V Z → False

@[expose] def CF67CoreDeriv (Y : Type) [Group Y] [Finite Y] (r : ℕ) : Prop :=
  IsSimpleGroup Y → (∃ a b : Y, a * b ≠ b * a) →
    ∀ (V Z : Subgroup (MulAut Y)), N2Cfg Y r V Z → N3Deriv Y V Z → False

theorem conj_mem_normalizer_map {N : Type} [Group N] (J Z : Subgroup N)
    {c : N} (hcJ : c ∈ J) (hcZ : c ∈ normalizer (Z : Set N)) :
    MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) ⟨c, hcJ⟩) ∈
      normalizer ((((Z.subgroupOf (normalizer (J : Set N))).map (actCenterQuot J) :
        Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J)))) : Set (MulAut (↥J ⧸ Subgroup.center ↥J))) := by
  have hcH : c ∈ normalizer (J : Set N) := Subgroup.le_normalizer hcJ
  set cH : ↥(normalizer (J : Set N)) := ⟨c, hcH⟩ with hcHdef
  have hψ : actCenterQuot J cH = MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) ⟨c, hcJ⟩) := by
    ext x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center ↥J) x
    change onCenterQuotient (J.normalizerMonoidHom cH) (QuotientGroup.mk' (Subgroup.center ↥J) d) = _
    rw [onCenterQuotient_apply_mk]
    simp only [MulAut.conj_apply, ← map_mul, ← map_inv]
    congr 1
  rw [← hψ, Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨zH, hzH, rfl⟩
    refine ⟨cH * zH * cH⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hzH' : zH ∈ Z.subgroupOf (normalizer (J : Set N)) := hzH
    rw [Subgroup.mem_subgroupOf] at hzH'
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.mp hcZ _).mp hzH'
    simpa [cH] using this
  · rintro ⟨wH, hwH, hw⟩
    refine ⟨cH⁻¹ * wH * cH, ?_, ?_⟩
    · have hwH' : wH ∈ Z.subgroupOf (normalizer (J : Set N)) := hwH
      rw [Subgroup.mem_subgroupOf] at hwH'
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have := (Subgroup.mem_normalizer_iff.mp hcZ ((c⁻¹ * (wH : N) * c))).mpr
        (by simpa [mul_assoc] using hwH')
      simpa [cH, mul_assoc] using this
    · have h1 : actCenterQuot J wH = actCenterQuot J cH * g * (actCenterQuot J cH)⁻¹ := hw
      simp only [map_mul, map_inv, h1]
      group

end Bridge

section Data

theorem cf67_Ydata (N : Type) [Group N] [Finite N] (J : Subgroup N) (hJ : IsComponent J)
    (r : ℕ) (hr : r.Prime) (hr2 : Odd r) (V Z : Subgroup N)
    (hVe : IsElementaryAbelian r ↥V) (hVc : Nat.card ↥V = r ^ 2)
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZodd : Odd (Nat.card ↥Z))
    (hZcop : Nat.Coprime (Nat.card ↥Z) r) (hcomm : ∀ v ∈ V, ∀ w ∈ Z, v * w = w * v)
    (hVn : V ≤ normalizer (J : Set N)) (hZn : Z ≤ normalizer (J : Set N))
    (hfaith : ∀ v ∈ V, v ≠ 1 → ¬ J ≤ centralizer ({v} : Set N))
    (hZnt : ¬ J ≤ centralizer (Z : Set N))
    (hP3 : ∀ v ∈ V, v ≠ 1 → ∀ c ∈ J, c ∈ centralizer ({v} : Set N) → c ∈ normalizer (Z : Set N)) :
    ∃ (V' Z' : Subgroup (MulAut (↥J ⧸ Subgroup.center ↥J))),
      N2Cfg (↥J ⧸ Subgroup.center ↥J) r V' Z' ∧ N3Deriv (↥J ⧸ Subgroup.center ↥J) V' Z' ∧
        (¬ r ∣ Nat.card ↥(Subgroup.center ↥J) → N3Full (↥J ⧸ Subgroup.center ↥J) V' Z') := by
  have : Group.IsPerfect ↥J := hJ.1.1
  have : Fact r.Prime := ⟨hr⟩
  have := hVe
  set H : Subgroup N := normalizer (J : Set N) with hH
  set ψ : ↥H →* MulAut (↥J ⧸ Subgroup.center ↥J) := actCenterQuot J with hψ
  have hker : ∀ h : ↥H, ψ h = 1 → ∀ c ∈ J, (h : N) * c = c * h :=
    commute_of_actCenterQuot_eq_one J
  have hVinj : Function.Injective (ψ.domRestrict (V.subgroupOf H)) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨v, hv⟩ hv1
    have hcen := hker v hv1
    have hv' : (v : N) ∈ V := mem_subgroupOf.mp hv
    by_contra hne
    have hne' : (v : N) ≠ 1 := fun h => hne (Subtype.ext (Subtype.ext h))
    refine hfaith _ hv' hne' ?_
    intro c hc
    rw [mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hcen c hc
  have hVcard : Nat.card ↥(V.subgroupOf H) = Nat.card ↥V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVn).toEquiv
  have hZcard : Nat.card ↥(Z.subgroupOf H) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZn).toEquiv
  have hZdvd : Nat.card ↥((Z.subgroupOf H).map ψ) ∣ Nat.card ↥Z :=
    (Subgroup.card_map_dvd _ ψ).trans (dvd_of_eq hZcard)
  have hN2 : N2Cfg (↥J ⧸ Subgroup.center ↥J) r ((V.subgroupOf H).map ψ) ((Z.subgroupOf H).map ψ) := by
    refine ⟨hr, hr2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have : IsElementaryAbelian r ↥(V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVn
      exact IsElementaryAbelian.map ψ
    · rw [← MonoidHom.domRestrict_range, ← Nat.card_congr (MonoidHom.ofInjective hVinj).toEquiv,
        hVcard, hVc]
    · rintro a ha b hb
      obtain ⟨x, hx, rfl⟩ := mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hZab _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy))
    · exact Odd.of_dvd_nat hZodd hZdvd
    · exact Nat.Coprime.coprime_dvd_left hZdvd hZcop
    · intro hbot
      apply hZnt
      intro c hc
      rw [mem_centralizer_iff]
      intro z hz
      have hz' : (⟨z, hZn hz⟩ : ↥H) ∈ Z.subgroupOf H := mem_subgroupOf.mpr hz
      have h1 : ψ ⟨z, hZn hz⟩ ∈ (Z.subgroupOf H).map ψ := mem_map_of_mem ψ hz'
      rw [hbot, mem_bot] at h1
      exact hker _ h1 c hc
    · rintro a ha b hb
      obtain ⟨x, hx, rfl⟩ := mem_map.mp ha
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hb
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm _ (mem_subgroupOf.mp hx) _ (mem_subgroupOf.mp hy))
  have hkey : ∀ vH : ↥H, vH ∈ V.subgroupOf H → ψ vH ≠ 1 →
      ∀ c ∈ fixSub (J.normalizerMonoidHom vH),
        MulAut.conj (QuotientGroup.mk' (Subgroup.center ↥J) c) ∈
          normalizer (((Z.subgroupOf H).map ψ : Subgroup _) : Set _) := by
    intro vH hvH hne c hc
    have hvV : (vH : N) ∈ V := mem_subgroupOf.mp hvH
    have hv1 : (vH : N) ≠ 1 := by
      intro h
      apply hne
      have : vH = 1 := Subtype.ext h
      rw [this, map_one]
    have hcent : (c : N) ∈ centralizer ({(vH : N)} : Set N) := by
      rw [mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      have h1 : J.normalizerMonoidHom vH c = c := hc
      have h2 := congrArg (fun w : ↥J => (w : N)) h1
      simp only [Subgroup.normalizerMonoidHom_apply_apply_coe] at h2
      exact mul_inv_eq_iff_eq_mul.mp h2
    have hcZ := hP3 _ hvV hv1 _ c.2 hcent
    have := conj_mem_normalizer_map J Z (c := (c : N)) c.2 hcZ
    simpa using this
  refine ⟨_, _, hN2, ?_, ?_⟩
  · rintro v' hv' hne c hc
    obtain ⟨vH, hvH, rfl⟩ := mem_map.mp hv'
    have hc' := commutator_fixSub_le_map (J.normalizerMonoidHom vH) hc
    obtain ⟨c0, hc0, rfl⟩ := hc'
    exact hkey vH hvH hne c0 hc0
  · intro hcop v' hv' hne c hc
    obtain ⟨vH, hvH, rfl⟩ := mem_map.mp hv'
    have hvpow : (J.normalizerMonoidHom vH) ^ r = 1 := by
      rw [← map_pow]
      have : vH ^ r = 1 := by
        apply Subtype.ext
        have := elemPow_eq_one_of_isElementaryAbelian (p := r) (A := V) (vH : N)
          (mem_subgroupOf.mp hvH)
        simpa using this
      rw [this, map_one]
    have hc' := fixSub_onCenterQuotient_le_map (J.normalizerMonoidHom vH) hr hvpow hcop hc
    obtain ⟨c0, hc0, rfl⟩ := hc'
    exact hkey vH hvH hne c0 hc0

end Data

section Core

theorem false_of_inn_normalizes {Y : Type} [Group Y] (hY : IsSimpleGroup Y)
    (hn : ∃ a b : Y, a * b ≠ b * a) {Z : Subgroup (MulAut Y)} (hZ : Z ≠ ⊥)
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (hS : ∀ c : Y, MulAut.conj c ∈ normalizer (Z : Set (MulAut Y))) : False := by
  obtain ⟨a₀, b₀, hab₀⟩ := hn
  have hcen : Subgroup.center Y = ⊥ := by
    rcases hY.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · exact h
    · exfalso
      apply hab₀
      have ha : a₀ ∈ Subgroup.center Y := h ▸ Subgroup.mem_top a₀
      exact (Subgroup.mem_center_iff.mp ha b₀).symm
  have hinj := mulAut_conj_injective_of_center_bot hcen
  let D : Subgroup Y := Z.comap (MulAut.conj : Y →* MulAut Y)
  have hDn : D.Normal := by
    refine ⟨fun d hd g => ?_⟩
    have hd' : MulAut.conj d ∈ Z := hd
    have h1 := (Subgroup.mem_normalizer_iff.mp (hS g) (MulAut.conj d)).mp hd'
    show MulAut.conj (g * d * g⁻¹) ∈ Z
    simpa [map_mul, map_inv] using h1
  rcases hY.eq_bot_or_eq_top_of_normal D with hD | hD
  · apply hZ
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hconj : ∀ (φ : MulAut Y) (a : Y), φ * MulAut.conj a * φ⁻¹ = MulAut.conj (φ a) := by
      intro φ a; ext y; simp [MulAut.conj_apply]
    ext c
    have h1 := (Subgroup.mem_normalizer_iff.mp (hS c) z).mp hz
    have h2 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ ∈ Z :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hz)
    have h3 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (c * z c⁻¹) := by
      have : z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (z c⁻¹) := by
        have := hconj z c⁻¹
        simpa [map_inv] using this
      calc MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹
          = MulAut.conj c * (z * (MulAut.conj c)⁻¹ * z⁻¹) := by group
        _ = MulAut.conj (c * z c⁻¹) := by rw [this, map_mul]
    rw [h3] at h2
    have h4 : c * z c⁻¹ ∈ D := h2
    rw [hD, Subgroup.mem_bot] at h4
    have : z c⁻¹ = c⁻¹ := by
      have := congrArg (fun t => c⁻¹ * t) h4
      simpa using this
    have h5 := this
    simp only [MulAut.one_apply]
    have := congrArg (fun t => t⁻¹) h5
    simpa using this
  · apply hab₀
    have ha : a₀ ∈ D := hD ▸ Subgroup.mem_top a₀
    have hb : b₀ ∈ D := hD ▸ Subgroup.mem_top b₀
    have h := hZab _ ha _ hb
    apply hinj
    simpa [map_mul] using h

theorem false_of_generation {Y : Type} [Group Y] (hY : IsSimpleGroup Y)
    (hn : ∃ a b : Y, a * b ≠ b * a) {r : ℕ} {V Z : Subgroup (MulAut Y)} (h2 : N2Cfg Y r V Z)
    (h3 : N3Full Y V Z)
    (hgen : (⨆ v ∈ V, ⨆ (_ : v ≠ 1), fixSub v) = ⊤) : False := by
  obtain ⟨-, -, -, -, hZab, -, -, hZbot, -⟩ := h2
  refine false_of_inn_normalizes hY hn hZbot hZab fun c => ?_
  let S : Subgroup Y := (normalizer (Z : Set (MulAut Y))).comap (MulAut.conj : Y →* MulAut Y)
  have hle : (⨆ v ∈ V, ⨆ (_ : v ≠ 1), fixSub v) ≤ S :=
    iSup₂_le fun v hv => iSup_le fun hne => fun c hc => h3 v hv hne c hc
  rw [hgen] at hle
  exact hle (Subgroup.mem_top c)

theorem false_of_generation_deriv {Y : Type} [Group Y] (hY : IsSimpleGroup Y)
    (hn : ∃ a b : Y, a * b ≠ b * a) {r : ℕ} {V Z : Subgroup (MulAut Y)} (h2 : N2Cfg Y r V Z)
    (h3 : N3Deriv Y V Z)
    (hgen : (⨆ v ∈ V, ⨆ (_ : v ≠ 1), ⁅fixSub v, fixSub v⁆) = ⊤) : False := by
  obtain ⟨-, -, -, -, hZab, -, -, hZbot, -⟩ := h2
  refine false_of_inn_normalizes hY hn hZbot hZab fun c => ?_
  let S : Subgroup Y := (normalizer (Z : Set (MulAut Y))).comap (MulAut.conj : Y →* MulAut Y)
  have hle : (⨆ v ∈ V, ⨆ (_ : v ≠ 1), ⁅fixSub v, fixSub v⁆) ≤ S :=
    iSup₂_le fun v hv => iSup_le fun hne => fun c hc => h3 v hv hne c hc
  rw [hgen] at hle
  exact hle (Subgroup.mem_top c)

theorem cf67Fam_of_core {F : (Y : Type) → [Group Y] → Prop}
    (hFull : ∀ (Y : Type) [Group Y] [Finite Y], F Y → CF67CoreFull Y)
    (hcov : ∀ (J : Type) [Group J] [Finite J], IsQuasisimple J → F (J ⧸ Subgroup.center J) →
      ∀ r : ℕ, r.Prime → Odd r → r ∣ Nat.card (Subgroup.center J) →
        CF67CoreDeriv (J ⧸ Subgroup.center J) r) : CF67Fam F := by
  intro N _ _ J hJ hF r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  obtain ⟨V', Z', hN2, hD, hFullN3⟩ :=
    cf67_Ydata N J hJ r hr hr2 V Z hVe hVc hZab hZodd hZcop hcomm hVn hZn hfaith hZnt hP3
  have hsimple : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ.1.2.1
  have hnab : ∃ a b : ↥J ⧸ Subgroup.center ↥J, a * b ≠ b * a := hJ.1.2.2
  by_cases hdvd : r ∣ Nat.card (Subgroup.center ↥J)
  · exact hcov ↥J hJ.1 hF r hr hr2 hdvd hsimple hnab V' Z' hN2 hD
  · exact hFull (↥J ⧸ Subgroup.center ↥J) hF hsimple hnab r V' Z' hN2 (hFullN3 hdvd)

end Core

end CFSG.GH74.GLS.Stage2.Bender.Thm1
