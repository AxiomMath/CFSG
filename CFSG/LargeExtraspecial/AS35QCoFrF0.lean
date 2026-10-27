module

public import CFSG.LargeExtraspecial.AS35QCoFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QCo

open Module CFSG.RankThree.OrthogonalInvolutions

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

namespace Frame

variable [FiniteDimensional (ZMod 2) V] {q : QuadraticForm (ZMod 2) V} (F : Frame q)

abbrev F₀ : Submodule (ZMod 2) V := fixSpace F.Y₁ ⊓ fixSpace F.Y₂ ⊓ fixSpace F.Y₃

omit [FiniteDimensional (ZMod 2) V] in
theorem le_sup_F₀ :
    (⊤ : Submodule (ZMod 2) V) ≤
      F.F₀ ⊔ commSpace F.Y₃ ⊔ commSpace F.Y₂ ⊔ commSpace F.Y₁ := by
  have s1 := le_sup_fix_comm F.y₁ (U := ⊤) fun u _ => Submodule.mem_top
  rw [top_inf_eq, top_inf_eq] at s1
  have s2 := le_sup_fix_comm F.y₂ (U := fixSpace F.Y₁)
    fun u hu => apply_mem_fixSpace F.y₁₂.symm hu
  have s3 := le_sup_fix_comm F.y₃ (U := fixSpace F.Y₁ ⊓ fixSpace F.Y₂)
    fun u hu => Submodule.mem_inf.mpr ⟨apply_mem_fixSpace F.y₁₃.symm (Submodule.mem_inf.mp hu).1,
      apply_mem_fixSpace F.y₂₃.symm (Submodule.mem_inf.mp hu).2⟩
  refine s1.trans (sup_le ?_ le_sup_right)
  refine s2.trans (sup_le ?_ ((inf_le_right).trans (le_sup_right.trans le_sup_left)))
  refine s3.trans (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) ?_)
  exact inf_le_right.trans (le_sup_right.trans (le_sup_left.trans le_sup_left))


theorem trivial_on_commSpace {Y S : V ≃ₗ[ZMod 2] V} (hY : Y ^ 3 = 1)
    (hdim : finrank (ZMod 2) (commSpace Y) = 2) (hSY : S * Y = Y * S) (hS : S * S = 1) :
    ∀ v ∈ commSpace Y, S v = v := by
  have hfix : ∀ v, S (S v - v) = S v - v := fun v => by
    rw [map_sub, ← LinearEquiv.mul_apply, hS, one_apply', ← neg_sub, neg_eq_self']
  have hne : commSpace Y ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hdim
    exact absurd hdim (by norm_num)
  have hK : commSpace Y ⊓ fixSpace S ≠ ⊥ := by
    intro hK
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    by_cases hSu : S u = u
    · have : u ∈ commSpace Y ⊓ fixSpace S := Submodule.mem_inf.mpr ⟨hu, mem_fixSpace.mpr hSu⟩
      rw [hK, Submodule.mem_bot] at this
      exact hu0 this
    · have : S u - u ∈ commSpace Y ⊓ fixSpace S :=
        Submodule.mem_inf.mpr ⟨(commSpace Y).sub_mem (apply_mem_commSpace hSY hu) hu,
          mem_fixSpace.mpr (hfix u)⟩
      rw [hK, Submodule.mem_bot, sub_eq_zero] at this
      exact hSu this
  have heven := even_finrank_of_free hY (W := commSpace Y ⊓ fixSpace S)
    (fun u hu => Submodule.mem_inf.mpr ⟨apply_mem_commSpace rfl (Submodule.mem_inf.mp hu).1,
      apply_mem_fixSpace hSY.symm (Submodule.mem_inf.mp hu).2⟩)
    (inf_fixSpace_of_le_commSpace hY inf_le_left)
  have hle : finrank (ZMod 2) ↥(commSpace Y ⊓ fixSpace S) ≤ 2 := by
    have := Submodule.finrank_mono (inf_le_left : commSpace Y ⊓ fixSpace S ≤ commSpace Y)
    omega
  have hpos : finrank (ZMod 2) ↥(commSpace Y ⊓ fixSpace S) ≠ 0 :=
    fun h => hK (Submodule.finrank_eq_zero.mp h)
  have heq : commSpace Y ⊓ fixSpace S = commSpace Y := by
    apply Submodule.eq_of_le_of_finrank_eq inf_le_left
    obtain ⟨k, hk⟩ := heven
    omega
  intro v hv
  rw [← heq] at hv
  exact mem_fixSpace.mp (Submodule.mem_inf.mp hv).2

omit [FiniteDimensional (ZMod 2) V] in
theorem exists_ne_on_commSpace {Y S : V ≃ₗ[ZMod 2] V} (hY : Y ^ 3 = 1)
    (hne : commSpace Y ≠ ⊥) (hsy : S * Y * S = Y * Y) : ∃ v ∈ commSpace Y, S v ≠ v := by
  by_contra hcon
  push Not at hcon
  apply hne
  rw [eq_bot_iff]
  intro v hv
  have e1 : S (Y (S v)) = Y (Y v) := by
    rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hsy, LinearEquiv.mul_apply]
  rw [hcon v hv, hcon _ (apply_mem_commSpace rfl hv)] at e1
  have e2 : v = Y v := Y.injective e1
  have : v ∈ commSpace Y ⊓ fixSpace Y := Submodule.mem_inf.mpr ⟨hv, mem_fixSpace.mpr e2.symm⟩
  rwa [commSpace_inf_fixSpace hY] at this

abbrev sub1 (S : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V := (S : V →ₗ[ZMod 2] V) - 1

omit [FiniteDimensional (ZMod 2) V] in
theorem sub1_apply (S : V ≃ₗ[ZMod 2] V) (v : V) : sub1 S v = S v - v := rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem range_sub1 (S : V ≃ₗ[ZMod 2] V) : LinearMap.range (sub1 S) = commSpace S := rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem sub1_mem_fixSpace {S : V ≃ₗ[ZMod 2] V} (hS : S * S = 1) (v : V) :
    sub1 S v ∈ fixSpace S := by
  rw [mem_fixSpace, sub1_apply, map_sub, ← LinearEquiv.mul_apply, hS, one_apply', ← neg_sub,
    neg_eq_self']

theorem finrank_map_sub1_lt {S : V ≃ₗ[ZMod 2] V} (hS : S * S = 1) {U : Submodule (ZMod 2) V}
    (hU : ∀ u ∈ U, S u ∈ U) (hne : ∃ v ∈ U, S v ≠ v) :
    finrank (ZMod 2) ↥(U.map (sub1 S)) < finrank (ZMod 2) U := by
  have hle : U.map (sub1 S) ≤ U ⊓ fixSpace S := by
    rintro _ ⟨u, hu, rfl⟩
    exact Submodule.mem_inf.mpr ⟨U.sub_mem (hU u hu) hu, sub1_mem_fixSpace hS u⟩
  have hlt : U ⊓ fixSpace S < U := by
    refine lt_of_le_of_ne inf_le_left fun h => ?_
    obtain ⟨v, hv, hSv⟩ := hne
    rw [← h] at hv
    exact hSv (mem_fixSpace.mp (Submodule.mem_inf.mp hv).2)
  exact (Submodule.finrank_mono hle).trans_lt (Submodule.finrank_lt_finrank_of_lt hlt)


omit [FiniteDimensional (ZMod 2) V] in
theorem sup_inf_V₃ (h2 : commSpace F.Y₂ ≤ fixSpace F.Y₁ ⊓ fixSpace F.Y₃)
    (h3 : commSpace F.Y₃ ≤ fixSpace F.Y₁ ⊓ fixSpace F.Y₂) :
    (commSpace F.Y₁ ⊔ commSpace F.Y₂) ⊓ commSpace F.Y₃ = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hv12, hv3⟩ := Submodule.mem_inf.mp hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv12
  have hb1 : b ∈ fixSpace F.Y₁ := (Submodule.mem_inf.mp (h2 hb)).1
  have hv1 : a + b ∈ fixSpace F.Y₁ := (Submodule.mem_inf.mp (h3 hv3)).1
  have ha1 : a ∈ fixSpace F.Y₁ := by
    have := (fixSpace F.Y₁).sub_mem hv1 hb1
    rwa [add_sub_cancel_right] at this
  have ha0 : a = 0 := by
    have : a ∈ commSpace F.Y₁ ⊓ fixSpace F.Y₁ := Submodule.mem_inf.mpr ⟨ha, ha1⟩
    rwa [commSpace_inf_fixSpace F.y₁, Submodule.mem_bot] at this
  rw [ha0, zero_add] at hv3 ⊢
  have : b ∈ commSpace F.Y₂ ⊓ fixSpace F.Y₂ :=
    Submodule.mem_inf.mpr ⟨hb, (Submodule.mem_inf.mp (h3 hv3)).2⟩
  rwa [commSpace_inf_fixSpace F.y₂, Submodule.mem_bot] at this

omit [FiniteDimensional (ZMod 2) V] in
theorem F₀_inf_sum (h2 : commSpace F.Y₂ ≤ fixSpace F.Y₁ ⊓ fixSpace F.Y₃)
    (h3 : commSpace F.Y₃ ≤ fixSpace F.Y₁ ⊓ fixSpace F.Y₂) :
    F.F₀ ⊓ (commSpace F.Y₁ ⊔ commSpace F.Y₂ ⊔ commSpace F.Y₃) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvF, hvs⟩ := Submodule.mem_inf.mp hv
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := And.intro (Submodule.mem_inf.mp (Submodule.mem_inf.mp hvF).1)
    (Submodule.mem_inf.mp hvF).2
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp hvs
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
  have hc12 := Submodule.mem_inf.mp (h3 hc)
  have hb13 := Submodule.mem_inf.mp (h2 hb)
  have ha1 : a ∈ fixSpace F.Y₁ := by
    have := (fixSpace F.Y₁).sub_mem ((fixSpace F.Y₁).sub_mem hv1 hc12.1) hb13.1
    rwa [add_sub_cancel_right, add_sub_cancel_right] at this
  have ha0 : a = 0 := by
    have : a ∈ commSpace F.Y₁ ⊓ fixSpace F.Y₁ := Submodule.mem_inf.mpr ⟨ha, ha1⟩
    rwa [commSpace_inf_fixSpace F.y₁, Submodule.mem_bot] at this
  subst ha0
  rw [zero_add] at hv1 hv2 hv3 ⊢
  have hb2 : b ∈ fixSpace F.Y₂ := by
    have := (fixSpace F.Y₂).sub_mem hv2 hc12.2
    rwa [add_sub_cancel_right] at this
  have hb0 : b = 0 := by
    have : b ∈ commSpace F.Y₂ ⊓ fixSpace F.Y₂ := Submodule.mem_inf.mpr ⟨hb, hb2⟩
    rwa [commSpace_inf_fixSpace F.y₂, Submodule.mem_bot] at this
  subst hb0
  rw [zero_add] at hv3 ⊢
  have : c ∈ commSpace F.Y₃ ⊓ fixSpace F.Y₃ := Submodule.mem_inf.mpr ⟨hc, hv3⟩
  rwa [commSpace_inf_fixSpace F.y₃] at this


@[expose] def FixedByFrame (f₀ : V) : Prop :=
  F.Y₁ f₀ = f₀ ∧ F.Y₂ f₀ = f₀ ∧ F.Y₃ f₀ = f₀ ∧ F.S₁ f₀ = f₀ ∧ F.S₂ f₀ = f₀ ∧ F.S₃ f₀ = f₀ ∧
    F.P₁₂ f₀ = f₀ ∧ F.P₂₃ f₀ = f₀ ∧ F.X f₀ = f₀

omit [FiniteDimensional (ZMod 2) V] in
theorem F₀_preserved {P : V ≃ₗ[ZMod 2] V} (h1 : ∀ v ∈ fixSpace F.Y₁, P v ∈ fixSpace F.Y₁)
    (h2 : ∀ v ∈ fixSpace F.Y₂, P v ∈ fixSpace F.Y₂)
    (h3 : ∀ v ∈ fixSpace F.Y₃, P v ∈ fixSpace F.Y₃) : ∀ v ∈ F.F₀, P v ∈ F.F₀ := by
  intro v hv
  obtain ⟨hv12, hv3⟩ := Submodule.mem_inf.mp hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv12
  exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨h1 v hv1, h2 v hv2⟩, h3 v hv3⟩

theorem exists_f₀ (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    (hY : F.Y₁ ≠ 1) (hX : F.X ≠ 1) (hfix : fixSpace F.X ≠ ⊥)
    (hS : Even (finrank (ZMod 2) (commSpace F.S₁))) :
    ∃ f₀ : V, f₀ ≠ 0 ∧ q f₀ = 1 ∧ F.FixedByFrame f₀ := by
  obtain ⟨hc, hW⟩ := F.natural hq hV hY hX hfix
  obtain ⟨h1, h2, h3⟩ := F.le_fixSpace_of_W₁₂ hW
  have hc2 : finrank (ZMod 2) (commSpace F.Y₂) = 2 := by rw [F.finrank_commSpace_Y₂, hc]
  have hc3 : finrank (ZMod 2) (commSpace F.Y₃) = 2 := by rw [F.finrank_commSpace_Y₃, hc]
  have hsum : finrank (ZMod 2) ↥(commSpace F.Y₁ ⊔ commSpace F.Y₂ ⊔ commSpace F.Y₃) = 6 := by
    rw [finrank_sup_of_inf_eq_bot (F.sup_inf_V₃ h2 h3), finrank_sup_of_inf_eq_bot hW, hc, hc2,
      hc3]
  have hF₀le : finrank (ZMod 2) F.F₀ ≤ 2 := by
    have := finrank_sup_of_inf_eq_bot (F.F₀_inf_sum h2 h3)
    have hle : finrank (ZMod 2)
        ↥(F.F₀ ⊔ (commSpace F.Y₁ ⊔ commSpace F.Y₂ ⊔ commSpace F.Y₃)) ≤ 8 :=
      hV ▸ Submodule.finrank_le _
    omega
  have hS1V2 := trivial_on_commSpace F.y₂ hc2 F.s₁y₂ F.s₁
  have hS1V3 := trivial_on_commSpace F.y₃ hc3 F.s₁y₃ F.s₁
  have hS1F : ∀ v ∈ F.F₀, F.S₁ v ∈ F.F₀ := F.F₀_preserved
    (fun v hv => apply_mem_fixSpace_of_inv F.y₁ (s_mul_y F.s₁ F.sy₁) hv)
    (fun v hv => apply_mem_fixSpace F.s₁y₂ hv) (fun v hv => apply_mem_fixSpace F.s₁y₃ hv)
  have hS1V1 : ∀ v ∈ commSpace F.Y₁, F.S₁ v ∈ commSpace F.Y₁ :=
    fun v hv => apply_mem_commSpace_of_inv F.y₁ (s_mul_y F.s₁ F.sy₁) hv
  have hcomm : commSpace F.S₁ = F.F₀.map (sub1 F.S₁) ⊔ (commSpace F.Y₁).map (sub1 F.S₁) := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      have hv := F.le_sup_F₀ (Submodule.mem_top (x := v))
      obtain ⟨w, hw, a, ha, rfl⟩ := Submodule.mem_sup.mp hv
      obtain ⟨w', hw', b, hb, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨c, hc', d, hd, rfl⟩ := Submodule.mem_sup.mp hw'
      have e : sub1 F.S₁ (c + d + b + a) = sub1 F.S₁ c + sub1 F.S₁ a := by
        rw [map_add, map_add, map_add, sub1_apply F.S₁ d, sub1_apply F.S₁ b, hS1V3 d hd,
          hS1V2 b hb, sub_self, sub_self, add_zero, add_zero]
      change sub1 F.S₁ (c + d + b + a) ∈ _
      rw [e]
      exact Submodule.add_mem_sup ⟨c, hc', rfl⟩ ⟨a, ha, rfl⟩
    · rw [← range_sub1]
      exact sup_le LinearMap.map_le_range LinearMap.map_le_range
  have hinf : F.F₀.map (sub1 F.S₁) ⊓ (commSpace F.Y₁).map (sub1 F.S₁) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨a, ha, rfl⟩, ⟨b, hb, e⟩⟩
    have h1' : sub1 F.S₁ a ∈ fixSpace F.Y₁ :=
      (Submodule.mem_inf.mp (Submodule.mem_inf.mp (F.F₀.sub_mem (hS1F a ha) ha)).1).1
    have h2' : sub1 F.S₁ a ∈ commSpace F.Y₁ := e ▸ (commSpace F.Y₁).sub_mem (hS1V1 b hb) hb
    have : sub1 F.S₁ a ∈ commSpace F.Y₁ ⊓ fixSpace F.Y₁ := Submodule.mem_inf.mpr ⟨h2', h1'⟩
    rwa [commSpace_inf_fixSpace F.y₁] at this
  have hV1 : finrank (ZMod 2) ↥((commSpace F.Y₁).map (sub1 F.S₁)) = 1 := by
    have hne := exists_ne_on_commSpace F.y₁ (fun h => by rw [h, finrank_bot] at hc; omega) F.sy₁
    have hlt := finrank_map_sub1_lt F.s₁ hS1V1 hne
    have hpos : (commSpace F.Y₁).map (sub1 F.S₁) ≠ ⊥ := by
      obtain ⟨v, hv, hSv⟩ := hne
      intro h
      have : sub1 F.S₁ v ∈ (commSpace F.Y₁).map (sub1 F.S₁) := ⟨v, hv, rfl⟩
      rw [h, Submodule.mem_bot, sub1_apply, sub_eq_zero] at this
      exact hSv this
    have := Submodule.finrank_eq_zero.not.mpr hpos
    omega
  have hF1 : finrank (ZMod 2) ↥(F.F₀.map (sub1 F.S₁)) = 1 := by
    have hsplit := finrank_sup_of_inf_eq_bot hinf
    rw [← hcomm, hV1] at hsplit
    obtain ⟨k, hk⟩ := hS
    have hodd : finrank (ZMod 2) ↥(F.F₀.map (sub1 F.S₁)) ≠ 0 := by omega
    have hne : ∃ v ∈ F.F₀, F.S₁ v ≠ v := by
      by_contra hcon
      push Not at hcon
      apply hodd
      rw [Submodule.finrank_eq_zero, eq_bot_iff]
      rintro _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_bot, sub1_apply, hcon v hv, sub_self]
    have hlt := finrank_map_sub1_lt F.s₁ hS1F hne
    omega
  have hne0 : F.F₀.map (sub1 F.S₁) ≠ ⊥ := fun h => by rw [h, finrank_bot] at hF1; omega
  obtain ⟨f₀, hf₀mem, hf₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne0
  obtain ⟨u, hu, hufo⟩ := hf₀mem
  have hf₀F : f₀ ∈ F.F₀ := hufo ▸ F.F₀.sub_mem (hS1F u hu) hu
  have hf₀S1 : F.S₁ f₀ = f₀ := hufo ▸ mem_fixSpace.mp (sub1_mem_fixSpace F.s₁ u)
  have huniq : ∀ w ∈ F.F₀.map (sub1 F.S₁), w ≠ 0 → w = f₀ := fun w hw hw0 =>
    eq_of_finrank_eq_one hF1 hw ⟨u, hu, hufo⟩ hw0 hf₀0
  have hline : ∀ {P : V ≃ₗ[ZMod 2] V}, P * F.S₁ = F.S₁ * P → (∀ v ∈ F.F₀, P v ∈ F.F₀) →
      P f₀ = f₀ := by
    intro P hPS hPF
    apply huniq
    · refine ⟨P u, hPF u hu, ?_⟩
      rw [← hufo, sub1_apply, sub1_apply, map_sub, ← LinearEquiv.mul_apply P F.S₁, hPS,
        LinearEquiv.mul_apply]
    · intro h
      exact hf₀0 (P.injective (h.trans (map_zero P).symm))
  have hf₀Y : ∀ {Y : V ≃ₗ[ZMod 2] V}, (∀ v ∈ F.F₀, Y v = v) → Y f₀ = f₀ := fun h => h f₀ hf₀F
  have hY1 : F.Y₁ f₀ = f₀ :=
    mem_fixSpace.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf₀F).1).1
  have hY2 : F.Y₂ f₀ = f₀ :=
    mem_fixSpace.mp (Submodule.mem_inf.mp (Submodule.mem_inf.mp hf₀F).1).2
  have hY3 : F.Y₃ f₀ = f₀ := mem_fixSpace.mp (Submodule.mem_inf.mp hf₀F).2
  have hS2 : F.S₂ f₀ = f₀ := hline F.s₁₂.symm (F.F₀_preserved
    (fun v hv => apply_mem_fixSpace F.s₂y₁ hv)
    (fun v hv => apply_mem_fixSpace_of_inv F.y₂ (s_mul_y F.s₂ F.sy₂) hv)
    (fun v hv => apply_mem_fixSpace F.s₂y₃ hv))
  have hS3 : F.S₃ f₀ = f₀ := hline F.s₁₃.symm (F.F₀_preserved
    (fun v hv => apply_mem_fixSpace F.s₃y₁ hv) (fun v hv => apply_mem_fixSpace F.s₃y₂ hv)
    (fun v hv => apply_mem_fixSpace_of_inv F.y₃ (s_mul_y F.s₃ F.sy₃) hv))
  have hP23 : F.P₂₃ f₀ = f₀ := by
    refine hline F.p₂₃s₁ fun v hv => ?_
    obtain ⟨hv12, hv3⟩ := Submodule.mem_inf.mp hv
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv12
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨apply_mem_fixSpace_conj F.p₂₃y₁ hv1,
      apply_mem_fixSpace_conj F.p₂₃y₃ hv3⟩, apply_mem_fixSpace_conj F.p₂₃y₂ hv2⟩
  have hX' : F.X f₀ = f₀ := by
    have : f₀ ∈ commSpace F.S₁ := by
      rw [← hufo, ← range_sub1]
      exact ⟨u, rfl⟩
    exact mem_fixSpace.mp ((F.commSpace_le_fixSpace_X hq hV hX hfix).2 this)
  have hP12 : F.P₁₂ f₀ = f₀ := by
    have hPF : ∀ v ∈ F.F₀, F.P₁₂ v ∈ F.F₀ := fun v hv => by
      obtain ⟨hv12, hv3⟩ := Submodule.mem_inf.mp hv
      obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv12
      exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨apply_mem_fixSpace_conj F.p₁₂y₂ hv2,
        apply_mem_fixSpace_conj F.p₁₂y₁ hv1⟩, apply_mem_fixSpace_conj F.p₁₂y₃ hv3⟩
    have hPf : F.P₁₂ f₀ = F.S₂ (F.P₁₂ u) - F.P₁₂ u := by
      rw [← hufo, sub1_apply, map_sub, ← LinearEquiv.mul_apply F.P₁₂ F.S₁, F.p₁₂s₁,
        LinearEquiv.mul_apply]
    have hS2F : ∀ v ∈ F.F₀, F.S₂ v ∈ F.F₀ := F.F₀_preserved
      (fun v hv => apply_mem_fixSpace F.s₂y₁ hv)
      (fun v hv => apply_mem_fixSpace_of_inv F.y₂ (s_mul_y F.s₂ F.sy₂) hv)
      (fun v hv => apply_mem_fixSpace F.s₂y₃ hv)
    have hPf0 : F.P₁₂ f₀ ≠ 0 := fun h => hf₀0 (F.P₁₂.injective (h.trans (map_zero _).symm))
    have hne2 : ∃ v ∈ F.F₀, F.S₂ v ≠ v := ⟨F.P₁₂ u, hPF u hu, fun h => hPf0 (by
      rw [hPf, h, sub_self])⟩
    have hlt := finrank_map_sub1_lt F.s₂ hS2F hne2
    have hlt2 : F.F₀ ⊓ fixSpace F.S₂ < F.F₀ := by
      refine lt_of_le_of_ne inf_le_left fun h => ?_
      obtain ⟨v, hv, hSv⟩ := hne2
      rw [← h] at hv
      exact hSv (mem_fixSpace.mp (Submodule.mem_inf.mp hv).2)
    have hdim := Submodule.finrank_lt_finrank_of_lt hlt2
    have hmem1 : F.P₁₂ f₀ ∈ F.F₀ ⊓ fixSpace F.S₂ := Submodule.mem_inf.mpr ⟨hPF f₀ hf₀F, by
      rw [hPf]; exact sub1_mem_fixSpace F.s₂ (F.P₁₂ u)⟩
    have hmem2 : f₀ ∈ F.F₀ ⊓ fixSpace F.S₂ := Submodule.mem_inf.mpr ⟨hf₀F, mem_fixSpace.mpr hS2⟩
    have hpos : finrank (ZMod 2) ↥(F.F₀ ⊓ fixSpace F.S₂) ≠ 0 := fun h => hf₀0 (by
      rw [Submodule.finrank_eq_zero] at h
      rw [h] at hmem2
      exact hmem2)
    exact eq_of_finrank_eq_one (by omega) hmem1 hmem2 hPf0 hf₀0
  have hperp : ∀ {Y : V ≃ₗ[ZMod 2] V}, IsIsom q Y → Y f₀ = f₀ → ∀ w ∈ commSpace Y,
      QuadraticMap.polar q f₀ w = 0 := by
    intro Y hYi hYf w hw
    have hmem : f₀ ∈ fixSpace Y := mem_fixSpace.mpr hYf
    rw [fixSpace_eq_orthogonal hq hYi, LinearMap.BilinForm.mem_orthogonal_iff] at hmem
    have h' : QuadraticMap.polar q w f₀ = 0 := hmem w hw
    rw [QuadraticMap.polar_comm]
    exact h'
  obtain ⟨v, hv, hpol⟩ : ∃ v ∈ F.F₀, QuadraticMap.polar q f₀ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hf₀0
    refine hq.1 _ fun w => ?_
    rw [QuadraticMap.polarBilin_apply_apply]
    have hw := F.le_sup_F₀ (Submodule.mem_top (x := w))
    obtain ⟨w1, hw1, a, ha, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨w2, hw2, b, hb, rfl⟩ := Submodule.mem_sup.mp hw1
    obtain ⟨c, hc', d, hd, rfl⟩ := Submodule.mem_sup.mp hw2
    rw [QuadraticMap.polar_add_right, QuadraticMap.polar_add_right, QuadraticMap.polar_add_right,
      hcon c hc', hperp F.iY₃ hY3 d hd, hperp F.iY₂ hY2 b hb, hperp F.iY₁ hY1 a ha]
    simp
  have hpol1 : QuadraticMap.polar q f₀ v = 1 := by
    have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases h01 (QuadraticMap.polar q f₀ v) with h | h
    · exact absurd h hpol
    · exact h
  have hiso : ∀ x y, QuadraticMap.polar q (F.S₁ x) (F.S₁ y) = QuadraticMap.polar q x y := by
    intro x y
    simp only [QuadraticMap.polar, ← map_add, F.iS₁ _]
  have hSv : F.S₁ v = v + f₀ := by
    have hmem : sub1 F.S₁ v ∈ F.F₀.map (sub1 F.S₁) := ⟨v, hv, rfl⟩
    by_cases h0 : sub1 F.S₁ v = 0
    · exfalso
      rw [sub1_apply, sub_eq_zero] at h0
      apply hpol
      rw [← hufo, sub1_apply, QuadraticMap.polar_sub_left]
      nth_rewrite 1 [← h0]
      rw [hiso, sub_self]
    · have := huniq _ hmem h0
      rw [sub1_apply] at this
      rw [← this]
      abel
  have hq1 : q f₀ = 1 := by
    have e := F.iS₁ v
    rw [hSv, map_add_eq, QuadraticMap.polar_comm, hpol1] at e
    have h2 : q f₀ + 1 = 0 := by linear_combination e
    have h01 : ∀ c : ZMod 2, c + 1 = 0 → c = 1 := by decide
    exact h01 _ h2
  exact ⟨f₀, hf₀0, hq1, hY1, hY2, hY3, hf₀S1, hS2, hS3, hP12, hP23, hX'⟩

theorem fpf_or_fixed (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    (hY : F.Y₁ ≠ 1) (hX : F.X ≠ 1) (hS : Even (finrank (ZMod 2) (commSpace F.S₁))) :
    fixSpace F.X = ⊥ ∨ ∃ f₀ : V, f₀ ≠ 0 ∧ q f₀ = 1 ∧ F.FixedByFrame f₀ := by
  by_cases hfix : fixSpace F.X = ⊥
  · exact Or.inl hfix
  · exact Or.inr (F.exists_f₀ hq hV hY hX hfix hS)

end Frame

end CFSG.LargeExtraspecial.AS35QCo
