module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemL
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7N7
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfMembers
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7L

section Count

theorem exists_mul_center {A Q H : Type} [Group A] [Group Q] [Group H] [Finite A] [Finite H]
    (ρ : A →* Q) (σ : A →* H) (ψ : Q →* H) (hψ : ψ.ker ≤ Subgroup.center Q)
    (hrange : ψ.range ≤ σ.range)
    (hcen : ∀ x, (∀ x', σ x * σ x' = σ x' * σ x) → σ x = 1)
    (hker : ∀ x, ρ x ∈ Subgroup.center Q → ∀ x', σ (x * x' * x⁻¹ * x'⁻¹) = 1) (q : Q) :
    ∃ x, (ρ x)⁻¹ * q ∈ Subgroup.center Q := by
  have hK : (ψ.comp ρ).ker ≤ σ.ker := by
    intro x hx
    have hxc : ρ x ∈ Subgroup.center Q := hψ hx
    rw [MonoidHom.mem_ker]
    refine hcen x fun x' => ?_
    have h := hker x hxc x'
    simp only [map_mul, map_inv] at h
    calc σ x * σ x' = (σ x * σ x' * (σ x)⁻¹ * (σ x')⁻¹) * (σ x' * σ x) := by group
      _ = σ x' * σ x := by rw [h, one_mul]
  have hcard : Nat.card σ.range ≤ Nat.card (ψ.comp ρ).range := by
    rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, ← Subgroup.relIndex_ker,
      ← Subgroup.relIndex_ker]
    exact Subgroup.relIndex_le_of_le_left hK (relIndex_ne_zero' _ _)
  have heq : (ψ.comp ρ).range = σ.range :=
    Subgroup.eq_of_le_of_card_ge
      ((by rintro _ ⟨x, rfl⟩; exact ⟨ρ x, rfl⟩ : (ψ.comp ρ).range ≤ ψ.range).trans hrange) hcard
  have hq : ψ q ∈ (ψ.comp ρ).range := heq ▸ hrange ⟨q, rfl⟩
  obtain ⟨x, hx⟩ := hq
  refine ⟨x, hψ ?_⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.comp_apply, hx, inv_mul_cancel]

end Count

section Sec

variable {G : Type} [Group G] [Finite G]

theorem exists_secImage_mul_center {X Y : Subgroup G} (hXY : X ≤ Y)
    {PX : Set (Subgroup (SecQuot X))} {PY : Set (Subgroup (SecQuot Y))}
    (hspanX : TC.Thin.pSpan PX = ⊤) (IX : TC.Thin.AEIdentOn PX 7 AE.e64Sets AE.e64Sub)
    (hspanY : TC.Thin.pSpan PY = ⊤) (IY : TC.Thin.AEIdentOn PY 7 AE.e64Sets AE.e64Sub)
    (q : SecQuot Y) :
    ∃ x : G, ∃ hxX : x ∈ X, (F7I.piC Y ⟨x, hXY hxX⟩)⁻¹ * q ∈ Subgroup.center (SecQuot Y) := by
  have hmX : ∀ q : SecQuot X, q ∈ TC.Thin.pSpan PX := fun q => hspanX ▸ Subgroup.mem_top q
  have hmY : ∀ q : SecQuot Y, q ∈ TC.Thin.pSpan PY := fun q => hspanY ▸ Subgroup.mem_top q
  set ιX := (MonoidHom.id (SecQuot X)).codRestrict _ hmX with hιX
  set ιY := (MonoidHom.id (SecQuot Y)).codRestrict _ hmY with hιY
  set ρ : ↥X →* SecQuot Y :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)).comp (Subgroup.inclusion hXY) with hρ
  set β : ↥X →* SecQuot X := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hβ
  set σ := IX.φ.comp (ιX.comp β) with hσ
  set ψ := IY.φ.comp ιY with hψ
  have hσr : σ.range = AE.e64Sub := by
    rw [← IX.range_eq]
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rintro _ ⟨y, rfl⟩
      obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥X) (y : SecQuot X)
      refine ⟨x, ?_⟩
      have : ιX (β x) = y := Subtype.ext hx
      simp only [hσ, MonoidHom.comp_apply, this]
  have hψr : ψ.range ≤ σ.range := by
    rw [hσr, ← IY.range_eq]
    rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  have hker : ∀ x : ↥X, ρ x = 1 → β x = 1 := by
    intro x hx
    rw [hρ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
    have h1 : (x : G) ∈ oddCoreOf Y := ⟨_, hx, rfl⟩
    have h2 : (x : G) ∈ oddCoreOf X := F7M.oddCoreOf_inf_le hXY ⟨h1, x.2⟩
    obtain ⟨x', hx', hxx⟩ := h2
    have : x' = x := Subtype.ext hxx
    rw [hβ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← this]
    exact hx'
  obtain ⟨x, hx⟩ := exists_mul_center ρ σ ψ
    (by
      intro y hy
      have hc := IY.ker_le hy
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro q'
      exact congrArg Subtype.val (hc (ιY q')))
    hψr
    (by
      intro x hx
      have hmem : σ x ∈ σ.range := ⟨x, rfl⟩
      rw [hσr] at hmem
      have hc : (⟨σ x, hmem⟩ : ↥AE.e64Sub) ∈ Subgroup.center ↥AE.e64Sub := by
        rw [Subgroup.mem_center_iff]
        rintro ⟨h, hh⟩
        rw [← hσr] at hh
        obtain ⟨x', rfl⟩ := hh
        exact Subtype.ext (hx x').symm
      rw [TwinThinPf.center_e64_eq_bot, Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc)
    (by
      intro x hx x'
      have h1 : ρ (x * x' * x⁻¹ * x'⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [← Subgroup.mem_center_iff.mp hx (ρ x')]
        group
      simp only [hσ, MonoidHom.comp_apply, hker _ h1, map_one])
    q
  exact ⟨x, x.2, hx⟩

theorem rLayerSub_mono {Ω : Set (Subgroup G)} {U V : Subgroup G} (hVU : V ≤ U) :
    rLayerSub Ω U ≤ rLayerSub Ω V := by
  unfold rLayerSub
  exact iSup₂_le fun R hR => iSup_le fun h =>
    F7C.le_rLayerSub hR (h.trans (Subgroup.centralizer_le hVU))

theorem mem_normalizer_rLayerSub {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {V : Subgroup G}
    {a : G} (ha : a ∈ Subgroup.centralizer (V : Set G)) :
    a ∈ Subgroup.normalizer ((rLayerSub Ω V : Subgroup G) : Set G) := by
  have key : ∀ b ∈ Subgroup.centralizer (V : Set G), ∀ y ∈ rLayerSub Ω V,
      b * y * b⁻¹ ∈ rLayerSub Ω V := by
    intro b hb
    have hle : rLayerSub Ω V ≤ (rLayerSub Ω V).comap (MulAut.conj b).toMonoidHom := by
      unfold rLayerSub
      refine iSup₂_le fun R hR => iSup_le fun hRV => ?_
      intro y hy
      rw [Subgroup.mem_comap]
      show b * y * b⁻¹ ∈ _
      have hR' : conjSub b R ∈ RSet Ω := Q3CL.Thompson.conjSub_mem_RSet hΩ hR b
      have hR'V : conjSub b R ≤ Subgroup.centralizer (V : Set G) := by
        rintro _ ⟨x, hx, rfl⟩
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have h1 := (Subgroup.mem_centralizer_iff.mp hb) w hw
        have h2 := (Subgroup.mem_centralizer_iff.mp (hRV hx)) w hw
        show w * (b * x * b⁻¹) = (b * x * b⁻¹) * w
        have h3 : b⁻¹ * w = w * b⁻¹ := by
          calc b⁻¹ * w = b⁻¹ * (w * b) * b⁻¹ := by group
            _ = b⁻¹ * (b * w) * b⁻¹ := by rw [h1]
            _ = w * b⁻¹ := by group
        calc w * (b * x * b⁻¹) = (w * b) * x * b⁻¹ := by group
          _ = b * (w * x) * b⁻¹ := by rw [h1]; group
          _ = b * (x * w) * b⁻¹ := by rw [h2]
          _ = b * x * (w * b⁻¹) := by group
          _ = b * x * (b⁻¹ * w) := by rw [h3]
          _ = (b * x * b⁻¹) * w := by group
      exact F7C.le_rLayerSub hR' hR'V (conj_mem_conjSub hy)
    intro y hy
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key a ha y, fun hy => ?_⟩
  have := key a⁻¹ (Subgroup.inv_mem _ ha) _ hy
  have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
  rwa [e] at this

theorem central_conj {Y : Subgroup G} {a : G} (haN : a ∈ Subgroup.normalizer ((Y : Subgroup G) : Set G))
    {y : G} (hy : y ∈ Y) (hya : a * y * a⁻¹ ∈ Y)
    (hc : F7I.piC Y ⟨y, hy⟩ ∈ Subgroup.center (SecQuot Y)) :
    F7I.piC Y ⟨a * y * a⁻¹, hya⟩ ∈ Subgroup.center (SecQuot Y) := by
  have hON : a ∈ Subgroup.normalizer ((oddCoreOf Y : Subgroup G) : Set G) :=
    mem_normalizer_oddCoreOf_of_mem_normalizer haN
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro q
  obtain ⟨q₀, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥Y) q
  have hq' : a⁻¹ * (q₀ : G) * a ∈ Y := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) q₀).mp q₀.2
    simpa using this
  have h1 := hc (F7I.piC Y ⟨_, hq'⟩)
  change F7I.piC Y _ * F7I.piC Y _ = F7I.piC Y _ * F7I.piC Y _ at h1
  rw [← map_mul, ← map_mul, F7I.piC_eq_iff] at h1
  change F7I.piC Y q₀ * F7I.piC Y _ = F7I.piC Y _ * F7I.piC Y q₀
  rw [← map_mul, ← map_mul, F7I.piC_eq_iff]
  have h2 := (Subgroup.mem_normalizer_iff.mp hON _).mp h1
  have e : a * ((((⟨_, hq'⟩ : ↥Y) * ⟨y, hy⟩)⁻¹ * (⟨y, hy⟩ * ⟨_, hq'⟩) : ↥Y) : G) * a⁻¹ =
      ((((q₀ * ⟨a * y * a⁻¹, hya⟩ : ↥Y))⁻¹ * (⟨a * y * a⁻¹, hya⟩ * q₀) : ↥Y) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rwa [e] at h2

theorem le_oddCoreOf_of_cover {E H N : Subgroup G} (hHE : H ≤ E) (hcov : E ≤ oddCoreOf E ⊔ H)
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hodd : Odd (Nat.card N)) :
    N ≤ oddCoreOf E := by
  set π := F7I.piC E
  set P : Subgroup (SecQuot E) := (N.subgroupOf E).map π with hPdef
  have hPodd : Odd (Nat.card P) := by
    have h1 : Nat.card P ∣ Nat.card (N.subgroupOf E) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card (N.subgroupOf E) = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hNH.trans hHE)).toEquiv
    rw [h2] at h1
    exact Odd.of_dvd_nat hodd h1
  have hHNE : E ≤ Subgroup.normalizer ((oddCoreOf E : Subgroup G) : Set G) :=
    Sec7.le_normalizer_oddCoreOf E
  have hPn : (⊤ : Subgroup (SecQuot E)) ≤ Subgroup.normalizer (P : Set (SecQuot E)) := by
    intro q _
    obtain ⟨q₀, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥E) q
    have hq : (q₀ : G) ∈ ((oddCoreOf E ⊔ H : Subgroup G) : Set G) := hcov q₀.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hHE.trans hHNE)] at hq
    obtain ⟨o, ho, h, hh, hoh⟩ := hq
    have hq₀ : π q₀ = π ⟨h, hHE hh⟩ := by
      rw [F7I.piC_eq_iff]
      have e : (((q₀⁻¹ * ⟨h, hHE hh⟩ : ↥E)) : G) = h⁻¹ * o⁻¹ * h := by
        show (q₀ : G)⁻¹ * h = _
        rw [← hoh]
        group
      rw [e]
      have := (Subgroup.mem_normalizer_iff.mp (hHNE (E.inv_mem (hHE hh))) o⁻¹).mp
        ((oddCoreOf E).inv_mem ho)
      simpa using this
    change π q₀ ∈ _
    rw [hq₀, Subgroup.mem_normalizer_iff]
    intro p
    have hNnorm : ∀ m ∈ N, h * m * h⁻¹ ∈ N := fun m hm =>
      (Subgroup.mem_normalizer_iff.mp (hHN hh) m).mp hm
    have hNnorm' : ∀ m ∈ N, h⁻¹ * m * h ∈ N := fun m hm => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hHN hh)) m).mp hm
      simpa using this
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hm' : (m : G) ∈ N := Subgroup.mem_subgroupOf.mp hm
      refine ⟨⟨h, hHE hh⟩ * m * (⟨h, hHE hh⟩ : ↥E)⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · exact hNnorm _ hm'
      · simp only [map_mul, map_inv]
    · rintro ⟨m, hm, hmp⟩
      have hm' : (m : G) ∈ N := Subgroup.mem_subgroupOf.mp hm
      refine ⟨(⟨h, hHE hh⟩ : ↥E)⁻¹ * m * ⟨h, hHE hh⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · exact hNnorm' _ hm'
      · simp only [map_mul, map_inv, hmp]
        group
  intro x hx
  have hxE : x ∈ E := hHE (hNH hx)
  have h1 := F7I.eq_one_of_odd_normalized (F7I.quot_odd_normal_eq_bot E) Subgroup.normal_top hPodd hPn
    (d := π ⟨x, hxE⟩) ⟨⟨x, hxE⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩ (Subgroup.mem_top _)
  exact (F7I.piC_eq_one_iff _).mp h1

end Sec

end F7L

section Steps


variable {n : ℕ}

theorem p23E7LL2_of_lemLId (hL : P23E7LemLId n) : P23E7LL2 n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ Z hZd f₁ hf₁ hf₁e U hU hU1 f hf hUf
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have heO : e ∈ p23Orb Z t e := ⟨1, Subgroup.one_mem _, by group⟩
  have hUZ : U ≤ Z := hU.trans (inf_le_left.trans (aSub_le R Z e))
  have hZf : Z ≤ Subgroup.centralizer ({f} : Set Y) := hZd.le_cent (hZd.orb_le hf)
  obtain ⟨⟨v, hvUA⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hUf
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvU : v ∈ U := (Subgroup.mem_inf.mp hvUA).1
  have hvAf : v ∈ aSub R Z f := (Subgroup.mem_inf.mp hvUA).2
  set V := Subgroup.zpowers v with hVdef
  have hVU : V ≤ U := Subgroup.zpowers_le.mpr hvU
  have hVZ : V ≤ Z := hVU.trans hUZ
  have hV1 : V ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hv1'
  have hVe : V ≤ aSub R Z e := hVU.trans (hU.trans inf_le_left)
  have hVf₁ : V ≤ aSub R Z f₁ := hVU.trans (hU.trans inf_le_right)
  have hVf : V ≤ aSub R Z f := Subgroup.zpowers_le.mpr hvAf
  obtain ⟨hspanV, ⟨IV⟩, hEV⟩ :=
    hL hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd V hVZ hV1 e heO f₁ hf₁ (Ne.symm hf₁e) hVe hVf₁
  obtain ⟨hspanU, ⟨IU⟩, -⟩ :=
    hL hcit hP Y R S t K' W u e g hc hno hE hZ Z hZd U hUZ hU1 e heO f₁ hf₁ (Ne.symm hf₁e)
      (hU.trans inf_le_left) (hU.trans inf_le_right)
  set YV := rLayerSub (Om R) V with hYVdef
  set X := rLayerSub (Om R) U with hXdef
  set E := rLayer (Om R) f with hEdef
  have hXY : X ≤ YV := F7L.rLayerSub_mono hVU
  have hcov : E ≤ oddCoreOf E ⊔ (E ⊓ YV) := by
    refine F7C.rLayer_le_cover hΩ (hZd.isPGroup.to_le hVZ) (hVZ.trans hZf) ?_
    intro w hw
    exact ((mem_aSub_iff hZf).mp (hVf hw)).2
  have hEN : E ≤ Subgroup.normalizer ((oddCoreOf E : Subgroup Y) : Set Y) := Sec7.le_normalizer_oddCoreOf E
  have hN : oddCoreOf YV ⊓ (E ⊓ YV) ≤ oddCoreOf E := by
    refine F7L.le_oddCoreOf_of_cover inf_le_left hcov inf_le_right ?_
      (Odd.of_dvd_nat (oddCoreOf_odd_natCard YV) (Subgroup.card_dvd_of_le inf_le_left))
    intro x hx
    have h1 : x ∈ Subgroup.normalizer ((oddCoreOf YV : Subgroup Y) : Set Y) :=
      Sec7.le_normalizer_oddCoreOf YV hx.2
    have h2 : x ∈ Subgroup.normalizer ((E ⊓ YV : Subgroup Y) : Set Y) := Subgroup.le_normalizer hx
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro y
    simp only [Subgroup.mem_inf]
    exact and_congr (h1 y) (h2 y)
  have hcent : ∀ a ∈ U, CentModE R f a := by
    intro a ha
    have haZ := hUZ ha
    have hav : v * a = a * v := (hZd.comm a haZ v (hUZ hvU)).symm
    have haV : a ∈ Subgroup.centralizer (V : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (hav : Commute v a) k).eq
    have haN : a ∈ Subgroup.normalizer ((YV : Subgroup Y) : Set Y) :=
      F7L.mem_normalizer_rLayerSub hΩ haV
    have haE : a ∈ Subgroup.normalizer ((E : Subgroup Y) : Set Y) :=
      F7C.mem_normalizer_rLayer hΩ (hZf haZ)
    have haX : ∀ x ∈ X, a * x = x * a := fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (F7C.rLayerSub_le_centralizer U hx)) a ha
    have hkey : ∀ h ∈ E ⊓ YV, a * h * a⁻¹ * h⁻¹ ∈ oddCoreOf E := by
      intro h hh
      obtain ⟨hhE, hhY⟩ := hh
      have hahY : a * h * a⁻¹ ∈ YV := (Subgroup.mem_normalizer_iff.mp haN h).mp hhY
      have hahE : a * h * a⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp haE h).mp hhE
      obtain ⟨x₀, hx₀X, hx₀c⟩ :=
        F7L.exists_secImage_mul_center hXY hspanU IU hspanV IV (F7I.piC YV ⟨h, hhY⟩)
      set x' : ↥YV := ⟨x₀, hXY hx₀X⟩ with hx'def
      have hx'X' : (x' : Y) ∈ X := hx₀X
      set y₂ : ↥YV := x'⁻¹ * ⟨h, hhY⟩ with hy₂
      have hy₂c : F7I.piC YV y₂ ∈ Subgroup.center (SecQuot YV) := by
        rw [hy₂, map_mul, map_inv]
        exact hx₀c
      have hay₂ : a * (y₂ : Y) * a⁻¹ ∈ YV := (Subgroup.mem_normalizer_iff.mp haN _).mp y₂.2
      have hc₁ := F7L.central_conj haN y₂.2 hay₂ hy₂c
      have hkY : a * h * a⁻¹ * h⁻¹ ∈ YV := YV.mul_mem hahY (YV.inv_mem hhY)
      have hxa : a * (x' : Y)⁻¹ = (x' : Y)⁻¹ * a := by
        have h1 := haX _ hx'X'
        calc a * (x' : Y)⁻¹ = (x' : Y)⁻¹ * ((x' : Y) * a) * (x' : Y)⁻¹ := by group
          _ = (x' : Y)⁻¹ * (a * (x' : Y)) * (x' : Y)⁻¹ := by rw [h1]
          _ = (x' : Y)⁻¹ * a := by group
      have hkeq : (⟨a * h * a⁻¹ * h⁻¹, hkY⟩ : ↥YV) =
          x' * ⟨a * (y₂ : Y) * a⁻¹, hay₂⟩ * y₂⁻¹ * x'⁻¹ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hy₂]
        calc a * h * a⁻¹ * h⁻¹ = (x' : Y) * (x' : Y)⁻¹ * a * h * a⁻¹ * h⁻¹ := by group
          _ = (x' : Y) * (a * (x' : Y)⁻¹) * h * a⁻¹ * h⁻¹ := by rw [hxa]; group
          _ = (x' : Y) * (a * ((x' : Y)⁻¹ * h) * a⁻¹) * ((x' : Y)⁻¹ * h)⁻¹ * (x' : Y)⁻¹ := by
              group
      have hkc : F7I.piC YV ⟨_, hkY⟩ ∈ Subgroup.center (SecQuot YV) := by
        rw [hkeq, map_mul, map_mul, map_mul, map_inv, map_inv]
        have hc : F7I.piC YV ⟨a * (y₂ : Y) * a⁻¹, hay₂⟩ * (F7I.piC YV y₂)⁻¹ ∈
            Subgroup.center (SecQuot YV) :=
          Subgroup.mul_mem _ hc₁ (Subgroup.inv_mem _ hy₂c)
        have e1 : F7I.piC YV x' * F7I.piC YV ⟨a * (y₂ : Y) * a⁻¹, hay₂⟩ * (F7I.piC YV y₂)⁻¹ *
            (F7I.piC YV x')⁻¹ = F7I.piC YV ⟨a * (y₂ : Y) * a⁻¹, hay₂⟩ * (F7I.piC YV y₂)⁻¹ := by
          rw [show F7I.piC YV x' * F7I.piC YV ⟨a * (y₂ : Y) * a⁻¹, hay₂⟩ * (F7I.piC YV y₂)⁻¹ *
              (F7I.piC YV x')⁻¹ = (F7I.piC YV x' * (F7I.piC YV ⟨a * (y₂ : Y) * a⁻¹, hay₂⟩ *
              (F7I.piC YV y₂)⁻¹)) * (F7I.piC YV x')⁻¹ by group,
            Subgroup.mem_center_iff.mp hc (F7I.piC YV x'), mul_inv_cancel_right]
        rw [e1]
        exact hc
      have hkH : F7I.piC YV ⟨_, hkY⟩ ∈ secImage YV (E ⊓ YV) :=
        ⟨⟨_, hkY⟩, Subgroup.mem_subgroupOf.mpr ⟨E.mul_mem hahE (E.inv_mem hhE), hkY⟩, rfl⟩
      have hk1 : F7I.piC YV ⟨_, hkY⟩ = 1 := by
        have := hEV f hf hVf
        have hmem : F7I.piC YV ⟨_, hkY⟩ ∈ secImage YV (E ⊓ YV) ⊓ Subgroup.center (SecQuot YV) :=
          ⟨hkH, hkc⟩
        rw [this] at hmem
        exact hmem
      have hkO : a * h * a⁻¹ * h⁻¹ ∈ oddCoreOf YV := (F7I.piC_eq_one_iff _).mp hk1
      exact hN ⟨hkO, E.mul_mem hahE (E.inv_mem hhE), hkY⟩
    intro b hb
    have hb' : b ∈ ((oddCoreOf E ⊔ (E ⊓ YV) : Subgroup Y) : Set Y) := hcov hb
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (inf_le_left.trans hEN)] at hb'
    obtain ⟨o, ho, h, hh, rfl⟩ := hb'
    have hao : a * o * a⁻¹ ∈ oddCoreOf E :=
      (Subgroup.mem_normalizer_iff.mp (mem_normalizer_oddCoreOf_of_mem_normalizer haE) o).mp ho
    have e1 : a * (o * h) * a⁻¹ * (o * h)⁻¹ = (a * o * a⁻¹) * (a * h * a⁻¹ * h⁻¹) * o⁻¹ := by group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hao (hkey h hh)) (Subgroup.inv_mem _ ho)
  intro a ha
  exact Subgroup.subset_closure ⟨hUZ ha, hcent a ha⟩

theorem p23E7LL2_of_lemL (hL : P23E7LemL n) : P23E7LL2 n :=
  p23E7LL2_of_lemLId (p23E7LemLId_of_lemL hL)

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
