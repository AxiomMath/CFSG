module

public import CFSG.CGT.Foote82.SetupLayer
import CFSG.GroupTheory.LocalCores.Layer
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdComp
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.Quasithin.Background.G11Basic
import CFSG.Quasithin.Background.VolII31
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

namespace Lemma63

private instance instFiniteGLV (V' : Type) [AddCommGroup V'] [Module (ZMod 2) V'] [Finite V'] :
    Finite (GLV V') :=
  Finite.of_injective (fun f : GLV V' => (f : V' → V')) fun _ _ h => LinearEquiv.ext (congrFun h)

private instance instFiniteSect (W₀ W₁ : Submodule (ZMod 2) V) : Finite (Sect W₀ W₁) :=
  Module.finite_of_finite (ZMod 2)

section Sections

variable {H : Subgroup (GLV V)} {W₀ W₁ : Submodule (ZMod 2) V}

private theorem mk_eq_mk_iff {v v' : V} (hv : v ∈ W₁) (hv' : v' ∈ W₁) :
    (Submodule.Quotient.mk ⟨v, hv⟩ : Sect W₀ W₁) = Submodule.Quotient.mk ⟨v', hv'⟩ ↔
      v - v' ∈ W₀ := by
  rw [Submodule.Quotient.eq]
  rfl

private def pull (W₀ W₁ : Submodule (ZMod 2) V) (J : Submodule (ZMod 2) (Sect W₀ W₁)) :
    Submodule (ZMod 2) V :=
  (J.comap (W₀.comap W₁.subtype).mkQ).map W₁.subtype

private theorem mem_pull {J : Submodule (ZMod 2) (Sect W₀ W₁)} {v : V} :
    v ∈ pull W₀ W₁ J ↔ ∃ hv : v ∈ W₁, (Submodule.Quotient.mk ⟨v, hv⟩ : Sect W₀ W₁) ∈ J := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, hx⟩
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, h, rfl⟩

private theorem pull_le (J : Submodule (ZMod 2) (Sect W₀ W₁)) : pull W₀ W₁ J ≤ W₁ :=
  fun _ hv => (mem_pull.1 hv).1

private theorem pull_bot (h : W₀ ≤ W₁) : pull W₀ W₁ ⊥ = W₀ := by
  ext v
  rw [mem_pull]
  constructor
  · rintro ⟨hv, h0⟩
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at h0
    exact h0
  · intro hv
    refine ⟨h hv, ?_⟩
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hv

private theorem pull_top : pull W₀ W₁ ⊤ = W₁ := by
  ext v
  rw [mem_pull]
  exact ⟨fun h => h.1, fun hv => ⟨hv, Submodule.mem_top⟩⟩

private theorem pull_le_pull_iff {J J' : Submodule (ZMod 2) (Sect W₀ W₁)} :
    pull W₀ W₁ J ≤ pull W₀ W₁ J' ↔ J ≤ J' := by
  constructor
  · intro h q hq
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have : (w : V) ∈ pull W₀ W₁ J := mem_pull.2 ⟨w.2, hq⟩
    obtain ⟨hv, hq'⟩ := mem_pull.1 (h this)
    exact hq'
  · intro h v hv
    obtain ⟨hv, hq⟩ := mem_pull.1 hv
    exact mem_pull.2 ⟨hv, h hq⟩

private theorem pull_injective :
    Function.Injective (pull W₀ W₁) := fun J J' h =>
  le_antisymm (pull_le_pull_iff.1 h.le) (pull_le_pull_iff.1 h.ge)

private theorem sectHom_eq_one_iff (h₀ : Invariant H W₀) (h₁ : Invariant H W₁) (y : ↥H) :
    sectHom H h₀ h₁ y = 1 ↔ ∀ w ∈ W₁, (y : GLV V) w - w ∈ W₀ := by
  constructor
  · intro h w hw
    have h' := congrArg (fun f : GLV (Sect W₀ W₁) => f (Submodule.Quotient.mk ⟨w, hw⟩)) h
    simp only [sectHom_mk] at h'
    exact (mk_eq_mk_iff (h₁ y y.2 w hw) hw).1 h'
  · intro h
    ext q
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    simp only [sectHom_mk]
    exact (mk_eq_mk_iff (h₁ y y.2 w w.2) w.2).2 (h w w.2)

private theorem invariant_pull (h₀ : Invariant H W₀) (h₁ : Invariant H W₁)
    {J : Submodule (ZMod 2) (Sect W₀ W₁)} (hJ : Invariant (sectHom H h₀ h₁).range J) :
    Invariant H (pull W₀ W₁ J) := by
  intro x hx v hv
  obtain ⟨hv₁, hvJ⟩ := mem_pull.1 hv
  refine mem_pull.2 ⟨h₁ x hx v hv₁, ?_⟩
  have := hJ (sectHom H h₀ h₁ ⟨x, hx⟩) ⟨⟨x, hx⟩, rfl⟩ _ hvJ
  rwa [sectHom_mk] at this

theorem isIrr_range_sectHom (h₀ : Invariant H W₀) (h₁ : Invariant H W₁)
    (hirr : IrrSec H W₀ W₁) : IsIrr (sectHom H h₀ h₁).range ⊤ := by
  refine ⟨invariant_top _, ?_, ?_⟩
  · obtain ⟨w, hw₁, hw₀⟩ := SetLike.exists_of_lt hirr.1
    refine lt_of_le_of_ne bot_le fun h => hw₀ ?_
    have hmem : (Submodule.Quotient.mk ⟨w, hw₁⟩ : Sect W₀ W₁) ∈
        (⊥ : Submodule (ZMod 2) (Sect W₀ W₁)) := by
      rw [h]
      exact Submodule.mem_top
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmem
    exact hmem
  · intro J hJ _ _
    have hP := invariant_pull h₀ h₁ hJ
    have hle : W₀ ≤ pull W₀ W₁ J :=
      (pull_bot hirr.1.le).symm.le.trans (pull_le_pull_iff.2 bot_le)
    rcases hirr.2 (pull W₀ W₁ J) hP hle (pull_le J) with h | h
    · left
      exact pull_injective (h.trans (pull_bot hirr.1.le).symm)
    · right
      exact pull_injective (h.trans pull_top.symm)

private theorem false_of_isPGroup (h₀ : Invariant H W₀) (h₁ : Invariant H W₁)
    (hirr : IrrSec H W₀ W₁) (hnt : ¬ ∀ x ∈ H, ∀ w ∈ W₁, x w - w ∈ W₀)
    {T : Subgroup ↥H} (hT : IsPGroup 2 T)
    (hTr : ∀ y : ↥H, ∃ t ∈ T, sectHom H h₀ h₁ y = sectHom H h₀ h₁ t) : False := by
  set φ := sectHom H h₀ h₁ with hφ
  haveI : Nontrivial (Sect W₀ W₁) := by
    obtain ⟨w, hw₁, hw₀⟩ := SetLike.exists_of_lt hirr.1
    refine ⟨⟨Submodule.Quotient.mk ⟨w, hw₁⟩, 0, fun h => hw₀ ?_⟩⟩
    have h' : (Submodule.Quotient.mk ⟨w, hw₁⟩ : Sect W₀ W₁) = 0 := h
    rwa [Submodule.Quotient.mk_eq_zero] at h'
  obtain ⟨v, hv0, hv⟩ := CFSG.RankThree.OddKernel.exists_ne_zero_fixed (p := 2) hT
    (CFSG.RankThree.OddKernel.toRep (φ.comp T.subtype))
  have hvT : ∀ t ∈ T, φ t v = v := fun t ht => hv ⟨t, ht⟩
  have hvH : ∀ y : ↥H, φ y v = v := by
    intro y
    obtain ⟨t, ht, hyt⟩ := hTr y
    rw [hyt]
    exact hvT t ht
  have hFinv : Invariant φ.range (fixedSpace φ.range) :=
    invariant_fixedSpace fun k' hk' k hk =>
      φ.range.mul_mem (φ.range.mul_mem hk' hk) (φ.range.inv_mem hk')
  have hP := invariant_pull h₀ h₁ hFinv
  have hle : W₀ ≤ pull W₀ W₁ (fixedSpace φ.range) :=
    (pull_bot hirr.1.le).symm.le.trans (pull_le_pull_iff.2 bot_le)
  have hvF : v ∈ fixedSpace φ.range := by
    rintro _ ⟨y, rfl⟩
    exact hvH y
  rcases hirr.2 _ hP hle (pull_le _) with h | h
  · have hF : fixedSpace φ.range = ⊥ := pull_injective (h.trans (pull_bot hirr.1.le).symm)
    rw [hF, Submodule.mem_bot] at hvF
    exact hv0 hvF
  · have hF : fixedSpace φ.range = ⊤ := pull_injective (h.trans pull_top.symm)
    refine hnt fun x hx w hw => ?_
    have hfix : φ ⟨x, hx⟩ (Submodule.Quotient.mk ⟨w, hw⟩) = Submodule.Quotient.mk ⟨w, hw⟩ := by
      have : (Submodule.Quotient.mk ⟨w, hw⟩ : Sect W₀ W₁) ∈ fixedSpace φ.range := by
        rw [hF]; exact Submodule.mem_top
      exact this _ ⟨⟨x, hx⟩, rfl⟩
    rw [hφ, sectHom_mk] at hfix
    exact (mk_eq_mk_iff (h₁ x hx w hw) hw).1 hfix

private theorem mem_map_subgroupOf_sectHom (h₀ : Invariant H W₀) (h₁ : Invariant H W₁)
    {L : Subgroup (GLV V)} (hLH : L ≤ H) {x : GLV (Sect W₀ W₁)} :
    x ∈ (L.subgroupOf H).map (sectHom H h₀ h₁) ↔
      ∃ (l : GLV V) (hl : l ∈ L), sectHom H h₀ h₁ ⟨l, hLH hl⟩ = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hLH hl⟩, hl, rfl⟩

private theorem commSpace_sectHom (h₀ : Invariant H W₀) (h₁ : Invariant H W₁)
    {L : Subgroup (GLV V)} (hLH : L ≤ H) :
    commSpace ((L.subgroupOf H).map (sectHom H h₀ h₁)) ⊤ =
      ((commSpace L W₁).comap W₁.subtype).map (W₀.comap W₁.subtype).mkQ := by
  set φ := sectHom H h₀ h₁ with hφ
  refine le_antisymm (commSpace_le_iff.2 fun k hk u _ => ?_) ?_
  · obtain ⟨l, hl, rfl⟩ := (mem_map_subgroupOf_sectHom h₀ h₁ hLH).1 hk
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    refine ⟨⟨l w - w, W₁.sub_mem (h₁ l (hLH hl) w w.2) w.2⟩, ?_, ?_⟩
    · exact sub_mem_commSpace hl w.2
    · show Submodule.Quotient.mk (⟨(l : GLV V) (w : V), h₁ l (hLH hl) w w.2⟩ - w) = _
      rw [Submodule.Quotient.mk_sub]
      rfl
  · rintro _ ⟨y, hy, rfl⟩
    have hlw : ∀ l ∈ L, ∀ w ∈ W₁, (l : GLV V) w ∈ W₁ := fun l hl w hw => h₁ l (hLH hl) w hw
    have hle : commSpace L W₁ ≤
        ((commSpace ((L.subgroupOf H).map φ) ⊤).comap (W₀.comap W₁.subtype).mkQ).map
          W₁.subtype := by
      refine commSpace_le_iff.2 fun l hl w hw =>
        ⟨⟨l w - w, W₁.sub_mem (hlw l hl w hw) hw⟩, ?_, rfl⟩
      have h1 : φ ⟨l, hLH hl⟩ ∈ (L.subgroupOf H).map φ :=
        (mem_map_subgroupOf_sectHom h₀ h₁ hLH).2 ⟨l, hl, rfl⟩
      have h2 := sub_mem_commSpace h1
        (Submodule.mem_top : (Submodule.Quotient.mk ⟨w, hw⟩ : Sect W₀ W₁) ∈
          (⊤ : Submodule (ZMod 2) (Sect W₀ W₁)))
      rw [hφ, sectHom_mk] at h2
      rw [SetLike.mem_coe, Submodule.mem_comap]
      have : (W₀.comap W₁.subtype).mkQ ⟨l w - w, W₁.sub_mem (hlw l hl w hw) hw⟩ =
          Submodule.Quotient.mk ⟨(l : GLV V) w, hlw l hl w hw⟩ -
            Submodule.Quotient.mk ⟨w, hw⟩ := by
        rw [← Submodule.Quotient.mk_sub]
        rfl
      rw [this]
      exact h2
    obtain ⟨z, hz, hzy⟩ := hle hy
    have : z = y := Subtype.ext hzy
    rw [← this]
    exact hz

private theorem commutator_subgroupOf_self {H L : Subgroup (GLV V)} (hLH : L ≤ H)
    (hL : ⁅L, L⁆ = L) : ⁅L.subgroupOf H, L.subgroupOf H⁆ = L.subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLH, hL]

private theorem subgroupOf_ne_bot {H L : Subgroup (GLV V)} (hLH : L ≤ H) (hL : L ≠ ⊥) :
    L.subgroupOf H ≠ ⊥ := by
  intro h'
  apply hL
  have := congrArg (Subgroup.map H.subtype) h'
  rwa [Subgroup.map_subgroupOf_eq_of_le hLH, Subgroup.map_bot] at this

theorem hasIrrTildeV_sectHom (h₀ : Invariant H W₀) (h₁ : Invariant H W₁)
    {L : Subgroup (GLV V)} (hLH : L ≤ H) (hperf : ⁅L, L⁆ = L) (hirr : HasIrrTildeV L)
    (hnt : ∃ l ∈ L, ∃ w ∈ W₁, l w - w ∉ W₀) :
    HasIrrTildeV ((L.subgroupOf H).map (sectHom H h₀ h₁)) := by
  set φ := sectHom H h₀ h₁ with hφ
  set Lb := (L.subgroupOf H).map φ with hLb
  have hmem := fun x : GLV (Sect W₀ W₁) => mem_map_subgroupOf_sectHom h₀ h₁ hLH (x := x)
  have hLbperf : ⁅Lb, Lb⁆ = Lb := by
    rw [hLb, ← Subgroup.map_commutator, commutator_subgroupOf_self hLH hperf]
  have hX₁ : Invariant L W₁ := h₁.mono hLH
  have hconj : ∀ k' ∈ L, ∀ k ∈ L, k' * k * k'⁻¹ ∈ L := fun k' hk' k hk =>
    L.mul_mem (L.mul_mem hk' hk) (L.inv_mem hk')
  have hXinv : Invariant L (commSpace L W₁) := invariant_commSpace hconj hX₁
  have hXU : commSpace L W₁ ≤ commSpace L ⊤ := commSpace_mono le_rfl le_top
  have hŪ := commSpace_sectHom h₀ h₁ hLH
  obtain ⟨-, hmin⟩ : IrrSec L (fixedSpace L ⊓ commSpace L ⊤) (commSpace L ⊤) := hirr
  show IrrSec Lb (fixedSpace Lb ⊓ commSpace Lb ⊤) (commSpace Lb ⊤)
  refine ⟨?_, ?_⟩
  ·
    refine lt_of_le_of_ne inf_le_right fun h => ?_
    have hfix : ∀ k ∈ Lb, ∀ u ∈ commSpace Lb ⊤, k u = u := fun k hk u hu => by
      have : u ∈ fixedSpace Lb ⊓ commSpace Lb ⊤ := by rw [h]; exact hu
      exact this.1 k hk
    have h0 : commSpace Lb (commSpace Lb ⊤) = ⊥ := commSpace_eq_bot_iff.2 hfix
    rw [commSpace_commSpace_top_of_perfect hLbperf] at h0
    obtain ⟨l, hl, w, hw, hlw⟩ := hnt
    have := commSpace_eq_bot_iff.1 h0 (φ ⟨l, hLH hl⟩) ((hmem _).2 ⟨l, hl, rfl⟩)
      (Submodule.Quotient.mk ⟨w, hw⟩) Submodule.mem_top
    rw [hφ, sectHom_mk] at this
    exact hlw ((mk_eq_mk_iff (h₁ l (hLH hl) w hw) hw).1 this)
  · intro J hJ hCJ hJU
    have hPjinv : Invariant L (pull W₀ W₁ J) := by
      intro l hl v hv
      obtain ⟨hv₁, hvJ⟩ := mem_pull.1 hv
      refine mem_pull.2 ⟨h₁ l (hLH hl) v hv₁, ?_⟩
      have := hJ (φ ⟨l, hLH hl⟩) ((hmem _).2 ⟨l, hl, rfl⟩) _ hvJ
      rwa [hφ, sectHom_mk] at this
    have hYinv : Invariant L (commSpace L W₁ ⊓ pull W₀ W₁ J) := hXinv.inf hPjinv
    have hYU : commSpace L W₁ ⊓ pull W₀ W₁ J ≤ commSpace L ⊤ := inf_le_left.trans hXU
    have hCinv : Invariant L (fixedSpace L ⊓ commSpace L ⊤) := fun l hl u hu => by
      rw [hu.1 l hl]
      exact hu
    have hYC : Invariant L (commSpace L W₁ ⊓ pull W₀ W₁ J ⊔ (fixedSpace L ⊓ commSpace L ⊤)) :=
      hYinv.sup hCinv
    rcases hmin _ hYC le_sup_right (sup_le hYU inf_le_right) with h | h
    ·
      left
      have hYC' : commSpace L W₁ ⊓ pull W₀ W₁ J ≤ fixedSpace L ⊓ commSpace L ⊤ :=
        le_sup_left.trans h.le
      refine le_antisymm (fun q hq => ?_) hCJ
      have hq' : q ∈ commSpace Lb ⊤ := hJU hq
      rw [hŪ] at hq'
      obtain ⟨y, hyX, rfl⟩ := hq'
      have hyPj : (y : V) ∈ pull W₀ W₁ J := mem_pull.2 ⟨y.2, hq⟩
      have hyC := hYC' (show (y : V) ∈ commSpace L W₁ ⊓ pull W₀ W₁ J from ⟨hyX, hyPj⟩)
      refine ⟨fun k hk => ?_, ?_⟩
      · obtain ⟨l, hl, rfl⟩ := (hmem k).1 hk
        have hly : (l : GLV V) (y : V) = y := hyC.1 l hl
        show φ ⟨l, hLH hl⟩ (Submodule.Quotient.mk y) = Submodule.Quotient.mk y
        rw [hφ, sectHom_mk]
        exact congrArg Submodule.Quotient.mk (Subtype.ext hly)
      · rw [hŪ]
        exact ⟨y, hyX, rfl⟩
    ·
      right
      have hUY : commSpace L ⊤ ≤ commSpace L W₁ ⊓ pull W₀ W₁ J := by
        calc commSpace L ⊤ = commSpace L (commSpace L ⊤) :=
              (commSpace_commSpace_top_of_perfect hperf).symm
          _ = commSpace L (commSpace L W₁ ⊓ pull W₀ W₁ J ⊔ (fixedSpace L ⊓ commSpace L ⊤)) := by
              rw [h]
          _ ≤ commSpace L W₁ ⊓ pull W₀ W₁ J := by
              refine commSpace_le_iff.2 fun l hl u hu => ?_
              obtain ⟨y, hy, c, hc, rfl⟩ := Submodule.mem_sup.1 hu
              have hcfix : (l : GLV V) c = c := hc.1 l hl
              have e : (l : GLV V) (y + c) - (y + c) = l y - y := by
                rw [map_add, hcfix]
                abel
              rw [e]
              exact Submodule.sub_mem _ (hYinv l hl y hy) hy
      refine le_antisymm hJU ?_
      rw [hŪ]
      rintro _ ⟨y, hyX, rfl⟩
      have hyY : (y : V) ∈ commSpace L W₁ ⊓ pull W₀ W₁ J := hUY (hXU hyX)
      exact (mem_pull.1 hyY.2).2

end Sections

section Orbit

variable {Y : Type*} [Group Y] [Finite Y]

instance instNormalLayer (Y : Type*) [Group Y] : (CFSG.layer Y).Normal :=
  haveI := CFSG.LocalCores.layer_characteristic (G := Y)
  inferInstance

private theorem mem_conjugate_iff {K : Subgroup Y} {g x : Y} :
    x ∈ CFSG.conjugate K g ↔ g * x * g⁻¹ ∈ K := by
  unfold CFSG.conjugate
  constructor
  · rintro ⟨k, hk, rfl⟩
    show g * (g⁻¹ * k * g⁻¹⁻¹) * g⁻¹ ∈ K
    rw [show g * (g⁻¹ * k * g⁻¹⁻¹) * g⁻¹ = k by group]
    exact hk
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

private theorem isComponent_conjugate {K : Subgroup Y} (hK : CFSG.IsComponent K) (g : Y) :
    CFSG.IsComponent (CFSG.conjugate K g) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g⁻¹) hK

private theorem conjugate_le_of_normal {K N : Subgroup Y} [N.Normal] (hK : K ≤ N) (g : Y) :
    CFSG.conjugate K g ≤ N := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have h2 := Subgroup.Normal.conj_mem ‹N.Normal› _ (hK hx) g⁻¹
  simpa [mul_assoc] using h2

private theorem le_of_conjugate_le {K N : Subgroup Y} [N.Normal] {g : Y}
    (h : CFSG.conjugate K g ≤ N) : K ≤ N := by
  intro k hk
  have hk' : g⁻¹ * k * g ∈ CFSG.conjugate K g := by
    rw [mem_conjugate_iff, show g * (g⁻¹ * k * g) * g⁻¹ = k by group]
    exact hk
  have h2 := Subgroup.Normal.conj_mem ‹N.Normal› _ (h hk') g
  simpa [mul_assoc] using h2

private theorem perfect_le_of_solvable_quotient {P N : Subgroup Y} [N.Normal]
    (hP : ⁅P, P⁆ = P) (hN : Group.IsSolvable (Y ⧸ N)) : P ≤ N := by
  by_contra hPN
  set Q := P.map (QuotientGroup.mk' N) with hQ
  have hQperf : ⁅Q, Q⁆ = Q := by rw [hQ, ← Subgroup.map_commutator, hP]
  have hQne : Q ≠ ⊥ := by
    intro h
    apply hPN
    rw [hQ, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  haveI : Group.IsSolvable ↥Q := inferInstance
  haveI : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQne
  haveI : Group.IsPerfect ↥Q := Subgroup.isPerfect_iff.2 hQperf
  exact Group.IsPerfect.not_isSolvable ↥Q inferInstance

structure OrbitData (A S K : Subgroup Y) : Prop where
  normal : A.Normal
  isPGroup : IsPGroup 2 S
  sup_eq : A ⊔ S = ⊤
  comp : CFSG.IsComponent K
  K_le : K ≤ A
  A_le : A ≤ ⨆ s ∈ S, CFSG.conjugate K s

variable {A S K : Subgroup Y} (hO : OrbitData A S K)

include hO in
theorem OrbitData.A_le_layer : A ≤ CFSG.layer Y := by
  refine hO.A_le.trans (iSup₂_le fun s _ => ?_)
  exact CFSG.LocalCores.component_le_layer (isComponent_conjugate hO.comp s)

include hO in
theorem OrbitData.isSolvable_quotient {N : Subgroup Y} [N.Normal] (hAN : A ≤ N) :
    Group.IsSolvable (Y ⧸ N) := by
  haveI := hO.normal
  have hsurj : Function.Surjective ((QuotientGroup.mk' N).comp S.subtype) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : y ∈ A ⊔ S := hO.sup_eq ▸ Subgroup.mem_top y
    obtain ⟨a, ha, s, hs, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy
    refine ⟨⟨s, hs⟩, ?_⟩
    change QuotientGroup.mk s = QuotientGroup.mk (a * s)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).2 (hAN ha), one_mul]
  haveI := (hO.isPGroup.of_surjective _ hsurj).isNilpotent
  infer_instance

include hO in
theorem OrbitData.layer_eq : CFSG.layer Y = A := by
  haveI := hO.normal
  refine le_antisymm (sSup_le fun J hJ => ?_) hO.A_le_layer
  exact perfect_le_of_solvable_quotient (Subgroup.isPerfect_iff.1 hJ.1.1)
    (hO.isSolvable_quotient le_rfl)

include hO in
theorem OrbitData.exists_conjugate_eq {J : Subgroup Y} (hJ : CFSG.IsComponent J) :
    ∃ s ∈ S, J = CFSG.conjugate K s := by
  by_contra hne
  push Not at hne
  have hJA : J ≤ A := hO.layer_eq ▸ CFSG.LocalCores.component_le_layer hJ
  have hcomm : ∀ s ∈ S, ⁅J, CFSG.conjugate K s⁆ = ⊥ := fun s hs =>
    (CFSG.LocalCores.distinct_components_commute hJ
      (isComponent_conjugate hO.comp s)).resolve_left (hne s hs)
  have hAc : A ≤ Subgroup.centralizer (J : Set Y) := by
    refine hO.A_le.trans (iSup₂_le fun s hs => ?_)
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm s hs
  have hJJ : ⁅J, J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hJA.trans hAc)
  have hperf := Subgroup.isPerfect_iff.1 hJ.1.1
  rw [hJJ] at hperf
  haveI := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  exact (Subgroup.nontrivial_iff_ne_bot J).1 inferInstance hperf.symm

include hO in
theorem OrbitData.dichotomy {N : Subgroup Y} [N.Normal] :
    A ≤ N ∨ N ⊓ CFSG.layer Y ≤ Subgroup.centralizer (CFSG.layer Y : Set Y) := by
  by_cases hex : ∃ J : Subgroup Y, CFSG.IsComponent J ∧ J ≤ N
  · left
    obtain ⟨J, hJ, hJN⟩ := hex
    obtain ⟨s, -, rfl⟩ := hO.exists_conjugate_eq hJ
    have hK : K ≤ N := le_of_conjugate_le hJN
    exact hO.A_le.trans (iSup₂_le fun t _ => conjugate_le_of_normal hK t)
  · right
    push Not at hex
    have hle : CFSG.layer Y ≤ Subgroup.centralizer (N : Set Y) :=
      sSup_le fun J hJ => Subgroup.commutator_eq_bot_iff_le_centralizer.1
        ((CFSG.LocalCores.component_normal_subgroup hJ ‹N.Normal›).resolve_left (hex J hJ))
    rintro x ⟨hxN, -⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.1 (hle hy)) x hxN).symm

include hO in
theorem OrbitData.le_of_normal {L : Subgroup Y} (hLperf : ⁅L, L⁆ = L) (hL : L ≠ ⊥) (hLA : L ≤ A)
    {N : Subgroup Y} [N.Normal] (hLN : L ≤ N) : A ≤ N := by
  rcases hO.dichotomy (N := N) with h | h
  · exact h
  · exfalso
    have hLE : L ≤ CFSG.layer Y := hO.layer_eq ▸ hLA
    have hLc : L ≤ Subgroup.centralizer (L : Set Y) :=
      fun x hx => Subgroup.centralizer_le hLE (h ⟨hLN hx, hLE hx⟩)
    have hLL : ⁅L, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hLc
    rw [hLL] at hLperf
    exact hL hLperf.symm

include hO in
theorem OrbitData.commutator_ker_eq_bot {Y' : Type*} [Group Y'] {L : Subgroup Y}
    (hLperf : ⁅L, L⁆ = L) (hLA : L ≤ A) (φ : Y →* Y') (hnA : ¬ A ≤ φ.ker) :
    ⁅L, φ.ker⁆ = ⊥ := by
  haveI := hO.normal
  have hcen := (hO.dichotomy (N := φ.ker)).resolve_left hnA
  refine CFSG.LocalAnalysis.ComponentInitial.perfect_double_commutator hLperf ?_
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 fun x hx => ?_
  have hx1 : x ∈ A ⊓ φ.ker :=
    Subgroup.commutator_le_inf _ _ (Subgroup.commutator_mono hLA le_rfl hx)
  have hx2 : x ∈ Subgroup.centralizer (CFSG.layer Y : Set Y) :=
    hcen ⟨hx1.2, hO.layer_eq ▸ hx1.1⟩
  exact Subgroup.centralizer_le (hO.layer_eq ▸ hLA) hx2

theorem map_layer_eq {Y' : Type*} [Group Y'] [Finite Y'] (f : Y →* Y')
    (hf : Function.Surjective f) (hsolv : Group.IsSolvable (Y ⧸ CFSG.layer Y)) :
    (CFSG.layer Y).map f = CFSG.layer Y' := by
  haveI hM : ((CFSG.layer Y).map f).Normal := Subgroup.Normal.map inferInstance f hf
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 (sSup_le fun K hK => ?_))
    (sSup_le fun J hJ => ?_)
  · refine Subgroup.map_le_iff_le_comap.1 ?_
    by_cases hKf : K ≤ f.ker
    · rw [(Subgroup.map_eq_bot_iff K).2 hKf]
      exact bot_le
    · exact CFSG.LocalCores.component_le_layer
        ⟨CFSG.LocalCores.isQuasisimple_map hK.1 f hKf, hK.2.map hf⟩
  · refine perfect_le_of_solvable_quotient (Subgroup.isPerfect_iff.1 hJ.1.1) ?_
    let g : Y ⧸ CFSG.layer Y →* Y' ⧸ (CFSG.layer Y).map f :=
      QuotientGroup.map _ _ f (Subgroup.le_comap_map f _)
    have hg : Function.Surjective g := by
      intro q
      obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨y, rfl⟩ := hf y'
      exact ⟨QuotientGroup.mk y, rfl⟩
    exact Group.isSolvable_of_surjective hg

end Orbit

section Ambient

private theorem mem_layerIn_iff {H : Subgroup (GLV V)} {x : GLV V} :
    x ∈ layerIn H ↔ ∃ hx : x ∈ H, (⟨x, hx⟩ : ↥H) ∈ CFSG.layer ↥H := by
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨x'.2, hx'⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨⟨x, hx⟩, hx', rfl⟩

private theorem layerIn_le (H : Subgroup (GLV V)) : layerIn H ≤ H := Subgroup.map_subtype_le _

private theorem conj_mem_layerIn {H : Subgroup (GLV V)} {g x : GLV V} (hg : g ∈ H)
    (hx : x ∈ layerIn H) : g * x * g⁻¹ ∈ layerIn H := by
  obtain ⟨hxH, hx'⟩ := mem_layerIn_iff.1 hx
  refine mem_layerIn_iff.2 ⟨H.mul_mem (H.mul_mem hg hxH) (H.inv_mem hg), ?_⟩
  exact (instNormalLayer ↥H).conj_mem _ hx' ⟨g, hg⟩

private theorem layerIn_le_normalizer {H K : Subgroup (GLV V)} (hKH : K ≤ H)
    (hK : CFSG.IsComponent (K.subgroupOf H)) :
    layerIn H ≤ Subgroup.normalizer (K : Set (GLV V)) := by
  intro x hx
  obtain ⟨hxH, hx'⟩ := mem_layerIn_iff.1 hx
  have hn := CFSG.LocalCores.layer_le_normalizer hK hx'
  rw [Subgroup.mem_normalizer_iff] at hn ⊢
  intro h
  constructor
  · intro hh
    exact (hn ⟨h, hKH hh⟩).1 hh
  · intro hh
    have hhH : h ∈ H := by
      have := H.mul_mem (H.mul_mem (H.inv_mem hxH) (hKH hh)) hxH
      rwa [show x⁻¹ * (x * h * x⁻¹) * x = h by group] at this
    exact (hn ⟨h, hhH⟩).2 hh

private theorem conjugate_le_of_mem {H K : Subgroup (GLV V)} (hKH : K ≤ H) {p : GLV V}
    (hp : p ∈ H) : CFSG.conjugate K p ≤ H := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have := H.mul_mem (H.mul_mem (H.inv_mem hp) (hKH hx)) hp
  rwa [show p⁻¹ * (p * x * p⁻¹) * p = x by group] at this

private theorem isComponent_conjugate_subgroupOf {H K : Subgroup (GLV V)}
    (hK : CFSG.IsComponent (K.subgroupOf H)) {p : GLV V} (hp : p ∈ H) :
    CFSG.IsComponent ((CFSG.conjugate K p).subgroupOf H) := by
  have h := isComponent_conjugate hK ⟨p, hp⟩
  convert h using 1
  ext x
  simp only [Subgroup.mem_subgroupOf, mem_conjugate_iff]
  rfl

private theorem le_normalizer_map_subtype {H : Subgroup (GLV V)} (N : Subgroup ↥H) [N.Normal] :
    H ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup (GLV V)) : Set (GLV V)) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, Subgroup.Normal.conj_mem inferInstance k hk ⟨h, hh⟩, rfl⟩
  · rintro ⟨k, hk, hkg⟩
    refine ⟨⟨h, hh⟩⁻¹ * k * ⟨h, hh⟩, ?_, ?_⟩
    · have := Subgroup.Normal.conj_mem (inferInstance : N.Normal) k hk ⟨h, hh⟩⁻¹
      simpa using this
    · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hkg ⊢
      rw [hkg]
      group

private theorem odd_card_oddCoreIn (H : Subgroup (GLV V)) :
    Odd (Nat.card (CFSG.QuasithinUnique.oddCoreIn H)) := by
  rw [CFSG.QuasithinUnique.oddCoreIn, Subgroup.card_map_of_injective H.subtype_injective]
  exact CFSG.ComponentClassification.OddCore.odd_card H

private theorem nontrivial_of_isQuasisimple_open {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : Nontrivial Q := by
  have hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  obtain ⟨x, y, hxy⟩ := hsimple.exists_pair_ne
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨a, b, fun hab => hxy (by rw [hab])⟩

private theorem perfect_ne_bot_of_isQuasisimple {L : Subgroup (GLV V)}
    (hq : CFSG.Open.IsQuasisimple ↥L) : ⁅L, L⁆ = L ∧ L ≠ ⊥ := by
  haveI : Nontrivial ↥L := nontrivial_of_isQuasisimple_open hq
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.2 hq.1
  exact ⟨Subgroup.isPerfect_iff.1 inferInstance, (Subgroup.nontrivial_iff_ne_bot L).1 inferInstance⟩

private theorem conj_mem_normalClosure_of_centralizes {E L : Subgroup (GLV V)} {s : GLV V}
    (hs : ∀ x ∈ E, s * x * s⁻¹ ∈ E) (hsL : ∀ l ∈ L, s * l * s⁻¹ = l) {a : GLV V}
    (ha : a ∈ normalClosure E L) : s * a * s⁻¹ ∈ normalClosure E L := by
  induction ha using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, hx, l, hl, rfl⟩ := hy
    apply Subgroup.subset_closure
    refine ⟨s * x * s⁻¹, hs x hx, l, hl, ?_⟩
    have e : s * (x * l * x⁻¹) * s⁻¹ = (s * x * s⁻¹) * (s * l * s⁻¹) * (s * x * s⁻¹)⁻¹ := by
      group
    rw [e, hsL l hl]
  | one => simpa using (normalClosure E L).one_mem
  | mul y z _ _ hy hz =>
    have := (normalClosure E L).mul_mem hy hz
    convert this using 1
    group
  | inv y _ hy =>
    have := (normalClosure E L).inv_mem hy
    convert this using 1
    group

theorem exists_orbit_aux {S L H₀ : Subgroup (GLV V)} (h0 : Setup6 H₀ S L) :
    ∃ K : Subgroup (GLV V), K ≤ H₀ ∧ CFSG.IsComponent (K.subgroupOf H₀) ∧
      K ≤ normalClosure (layerIn H₀) L ∧
      normalClosure (layerIn H₀) L ≤ ⨆ p ∈ S, CFSG.conjugate K p := by
  have hSH₀ : S ≤ H₀ := h0.S_le
  have hLX : L ≤ H₀ ⊓ Subgroup.centralizer (S : Set (GLV V)) := h0.component.1
  have hLH₀ : L ≤ H₀ := hLX.trans inf_le_left
  have hLcS : ∀ s ∈ S, ∀ l ∈ L, s * l = l * s := fun s hs l hl =>
    (Subgroup.mem_centralizer_iff.1 (hLX hl).2) s hs
  have hq : CFSG.Open.IsQuasisimple ↥L := h0.component.2.2
  obtain ⟨hLperf, hLne⟩ := perfect_ne_bot_of_isQuasisimple hq
  have heven : 2 ∣ Nat.card L := by
    by_contra h2
    haveI : Nontrivial ↥L := nontrivial_of_isQuasisimple_open hq
    haveI : Group.IsPerfect ↥L := Group.isPerfect_def.2 hq.1
    exact Group.IsPerfect.not_isSolvable ↥L
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h2)))
  have hLcomp : CFSG.QuasithinUnique.IsComponentIn L
      (H₀ ⊓ Subgroup.centralizer (S : Set (GLV V))) :=
    ⟨hLX, (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLX).1
      (CFSG.Assembly.isComponentOf_iff_open.2 h0.component)⟩
  have hL2 := CFSG.QuasithinUnique.Id2519.isTwoComponentIn_of_isComponentIn hLcomp heven
  have hLO : L ≤ Subgroup.centralizer
      (CFSG.QuasithinUnique.oddCoreIn H₀ : Set (GLV V)) := by
    have hnorm : H₀ ≤ Subgroup.normalizer
        (CFSG.QuasithinUnique.oddCoreIn H₀ : Set (GLV V)) :=
      le_normalizer_map_subtype (fusionOddCore ↥H₀)
    have := lemma62 h0 (Subgroup.map_subtype_le _) (odd_card_oddCoreIn H₀) (hSH₀.trans hnorm)
      (hLH₀.trans hnorm)
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1
      ((Subgroup.commutator_comm _ _).trans this)
  obtain ⟨K, ⟨hKH₀, hKc⟩, hLK⟩ :=
    CFSG.Quasithin.VolI.I31.as_I_3_1_one_two hSH₀ h0.isPGroup hL2 hLO
  have hconjc : ∀ p ∈ S, CFSG.IsComponent ((CFSG.conjugate K p).subgroupOf H₀) := fun p hp =>
    isComponent_conjugate_subgroupOf hKc (hSH₀ hp)
  have hconjH : ∀ p ∈ S, CFSG.conjugate K p ≤ H₀ := fun p hp =>
    conjugate_le_of_mem hKH₀ (hSH₀ hp)
  have hDE : (⨆ p ∈ S, CFSG.conjugate K p) ≤ layerIn H₀ := by
    refine iSup₂_le fun p hp x hx => ?_
    have hxH := hconjH p hp hx
    exact mem_layerIn_iff.2 ⟨hxH, CFSG.LocalCores.component_le_layer (hconjc p hp)
      (show (⟨x, hxH⟩ : ↥H₀) ∈ (CFSG.conjugate K p).subgroupOf H₀ from hx)⟩
  have hLE : L ≤ layerIn H₀ := hLK.trans hDE
  have hE₀D : ∀ x ∈ layerIn H₀, x ∈ Subgroup.normalizer
      ((⨆ p ∈ S, CFSG.conjugate K p : Subgroup (GLV V)) : Set (GLV V)) := by
    intro x hx
    refine CFSG.Quasithin.VolI.I31.mem_normalizer_iSup fun p =>
      CFSG.Quasithin.VolI.I31.mem_normalizer_iSup fun hp => ?_
    exact layerIn_le_normalizer (hconjH p hp) (hconjc p hp) hx
  have hAD : normalClosure (layerIn H₀) L ≤ ⨆ p ∈ S, CFSG.conjugate K p := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hE₀D x hx) l).1 (hLK hl)
  have hSA : ∀ s ∈ S, ∀ a ∈ normalClosure (layerIn H₀) L,
      s * a * s⁻¹ ∈ normalClosure (layerIn H₀) L := fun s hs a ha =>
    conj_mem_normalClosure_of_centralizes (fun x hx => conj_mem_layerIn (hSH₀ hs) hx)
      (fun l hl => by rw [hLcS s hs l hl]; group) ha
  have hAle : normalClosure (layerIn H₀) L ≤ layerIn H₀ := normalClosure_le hLE
  refine ⟨K, hKH₀, hKc, ?_, hAD⟩
  have hA₀le : (normalClosure (layerIn H₀) L).subgroupOf H₀ ≤ CFSG.layer ↥H₀ := by
    intro y hy
    exact (mem_layerIn_iff.1 (hAle hy)).2
  have hA₀norm : (((normalClosure (layerIn H₀) L).subgroupOf H₀).subgroupOf
      (CFSG.layer ↥H₀)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hA₀le]
    intro h g hh hg
    exact normalClosure_conj (mem_layerIn_iff.2 ⟨g.2, hg⟩) hh
  have hA₀sub : ((normalClosure (layerIn H₀) L).subgroupOf H₀).IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ hA₀le (Subgroup.Normal.isSubnormal inferInstance) hA₀norm
  rcases CFSG.LocalCores.component_subnormal_subgroup hKc hA₀sub with h1 | h1
  · intro k hk
    exact h1 (show (⟨k, hKH₀ hk⟩ : ↥H₀) ∈ K.subgroupOf H₀ from hk)
  · exfalso
    have hKcomm : ∀ k ∈ K, ∀ a ∈ normalClosure (layerIn H₀) L, k * a = a * k := by
      intro k hk a ha
      have h2 := Subgroup.mem_centralizer_iff.1
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1)
          (show (⟨k, hKH₀ hk⟩ : ↥H₀) ∈ K.subgroupOf H₀ from hk))
        ⟨a, (hAle.trans (layerIn_le H₀)) ha⟩ ha
      exact (congrArg Subtype.val h2).symm
    have hDc : (⨆ p ∈ S, CFSG.conjugate K p) ≤
        Subgroup.centralizer ((normalClosure (layerIn H₀) L : Subgroup (GLV V)) : Set (GLV V)) := by
      refine iSup₂_le fun p hp x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hx' : p * x * p⁻¹ ∈ K := (mem_conjugate_iff).1 hx
      have h3 := hKcomm _ hx' _ (hSA p hp a ha)
      have e1 : p * x * p⁻¹ * (p * a * p⁻¹) = p * (x * a) * p⁻¹ := by group
      have e2 : p * a * p⁻¹ * (p * x * p⁻¹) = p * (a * x) * p⁻¹ := by group
      rw [e1, e2] at h3
      have := mul_left_cancel (mul_right_cancel h3)
      exact this.symm
    have hLc : L ≤ Subgroup.centralizer (L : Set (GLV V)) := fun l hl =>
      Subgroup.centralizer_le (le_normalClosure (layerIn H₀) L) (hDc (hLK hl))
    have hLL : ⁅L, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hLc
    rw [hLL] at hLperf
    exact hLne hLperf.symm

private theorem conj_mem_normalClosure_layerIn {S L H₀ : Subgroup (GLV V)} (h0 : Setup6 H₀ S L)
    {s : GLV V} (hs : s ∈ S) {a : GLV V} (ha : a ∈ normalClosure (layerIn H₀) L) :
    s * a * s⁻¹ ∈ normalClosure (layerIn H₀) L := by
  have hLX : L ≤ H₀ ⊓ Subgroup.centralizer (S : Set (GLV V)) := h0.component.1
  refine conj_mem_normalClosure_of_centralizes (fun x hx => conj_mem_layerIn (h0.S_le hs) hx)
    (fun l hl => ?_) ha
  have := (Subgroup.mem_centralizer_iff.1 (hLX hl).2) s hs
  rw [this]
  group

private theorem normalClosure_layerIn_le {L H₀ : Subgroup (GLV V)} (hL : L ≤ H₀) :
    normalClosure (layerIn H₀) L ≤ H₀ := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, l, hl, rfl⟩
  exact H₀.mul_mem (H₀.mul_mem (layerIn_le _ hx) (hL hl)) (H₀.inv_mem (layerIn_le _ hx))

theorem orbitData_subgroupOf {H A S K : Subgroup (GLV V)} (hAH : A ≤ H) (hSH : S ≤ H)
    (hAn : H ≤ Subgroup.normalizer (A : Set (GLV V))) (hS : IsPGroup 2 S) (hsup : A ⊔ S = H)
    (hKc : CFSG.IsComponent (K.subgroupOf H)) (hKA : K ≤ A)
    (hAD : A ≤ ⨆ p ∈ S, CFSG.conjugate K p) :
    OrbitData (A.subgroupOf H) (S.subgroupOf H) (K.subgroupOf H) where
  normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAH).2 hAn
  isPGroup := hS.comap_of_injective H.subtype H.subtype_injective
  sup_eq := by rw [← Subgroup.subgroupOf_sup hAH hSH, hsup, Subgroup.subgroupOf_self]
  comp := hKc
  K_le := Subgroup.comap_mono hKA
  A_le := by
    rw [← Subgroup.map_le_map_iff_of_injective H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hAH]
    refine hAD.trans (iSup₂_le fun p hp => ?_)
    have hp' : p ∈ H := hSH hp
    refine le_trans ?_ (Subgroup.map_mono (le_iSup₂_of_le (⟨p, hp'⟩ : ↥H)
      (show (⟨p, hp'⟩ : ↥H) ∈ S.subgroupOf H from hp) le_rfl))
    intro x hx
    have hxH : x ∈ H := conjugate_le_of_mem (hKA.trans hAH) hp' hx
    rw [mem_conjugate_iff] at hx
    exact ⟨⟨x, hxH⟩, (mem_conjugate_iff).2 hx, rfl⟩


theorem setup6_of_le {G S L H₀ : Subgroup (GLV V)} (h : Setup6 G S L) (hH₀ : H₀ ≤ G)
    (hLS : L ⊔ S ≤ H₀) : Setup6 H₀ S L := by
  have hLX : L ≤ G ⊓ Subgroup.centralizer (S : Set (GLV V)) := h.component.1
  exact
    { S_le := le_sup_right.trans hLS
      isPGroup := h.isPGroup
      component := CFSG.Assembly.isComponentOf_iff_open.1
        ((CFSG.Assembly.isComponentOf_iff_open.2 h.component).of_le_of_le
          (le_inf (le_sup_left.trans hLS) (hLX.trans inf_le_right)) (inf_le_inf_right _ hH₀))
      irrTilde := h.irrTilde }

theorem exists_orbitData {S L H₀ H : Subgroup (GLV V)} (h0 : Setup6 H₀ S L)
    (hH : H = normalClosure (layerIn H₀) L ⊔ S) :
    ∃ K : Subgroup (GLV V), OrbitData ((normalClosure (layerIn H₀) L).subgroupOf H)
      (S.subgroupOf H) (K.subgroupOf H) := by
  have hSH₀ : S ≤ H₀ := h0.S_le
  have hLH₀ : L ≤ H₀ := h0.component.1.trans inf_le_left
  obtain ⟨K, hKH₀, hKc₀, hKA, hAD⟩ := exists_orbit_aux h0
  have hAH : normalClosure (layerIn H₀) L ≤ H := by rw [hH]; exact le_sup_left
  have hSH : S ≤ H := by rw [hH]; exact le_sup_right
  have hHH₀ : H ≤ H₀ := by
    rw [hH]
    exact sup_le (normalClosure_layerIn_le hLH₀) hSH₀
  have hAn : H ≤ Subgroup.normalizer (normalClosure (layerIn H₀) L : Set (GLV V)) := by
    rw [hH]
    exact sup_le Subgroup.le_normalizer fun s hs => by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      refine ⟨fun ha => conj_mem_normalClosure_layerIn h0 hs ha, fun ha => ?_⟩
      have := conj_mem_normalClosure_layerIn h0 (S.inv_mem hs) ha
      rwa [show s⁻¹ * (s * a * s⁻¹) * s⁻¹⁻¹ = a by group] at this
  have hKH : K ≤ H := hKA.trans hAH
  have hKc : CFSG.IsComponent (K.subgroupOf H) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKH).1
      (CFSG.Assembly.IsComponentOf.of_le_of_le
        ((CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hKH₀).2
          hKc₀) hKH hHH₀)
  exact ⟨K, orbitData_subgroupOf hAH hSH hAn h0.isPGroup hH.symm hKc hKA hAD⟩

end Ambient

section Images

variable {V' : Type} [AddCommGroup V'] [Module (ZMod 2) V']

private theorem isQuasisimple_native {Q : Type*} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q :=
  ⟨⟨h.1⟩, h.2, CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Q h⟩

private theorem isQuasisimple_open {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    CFSG.Open.IsQuasisimple Q :=
  ⟨h.1.commutator_eq_top, h.2.1⟩

private theorem map_mem_normalClosure {H L : Subgroup (GLV V)} (hLH : L ≤ H)
    (φ : ↥H →* GLV V') :
    ∀ g : GLV V, g ∈ normalClosure H L → ∀ hg : g ∈ H,
      φ ⟨g, hg⟩ ∈ normalClosure φ.range ((L.subgroupOf H).map φ) := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, hx, l, hl, rfl⟩ := hy
    intro hg
    apply Subgroup.subset_closure
    refine ⟨φ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, φ ⟨l, hLH hl⟩, ⟨⟨l, hLH hl⟩, hl, rfl⟩, ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  | one =>
    intro hg
    have h1 : φ ⟨1, hg⟩ = 1 := map_one φ
    rw [h1]
    exact (normalClosure φ.range ((L.subgroupOf H).map φ)).one_mem
  | mul y z hy hz ihy ihz =>
    intro hg
    have hyH : y ∈ H := normalClosure_le hLH hy
    have hzH : z ∈ H := normalClosure_le hLH hz
    have := (normalClosure φ.range ((L.subgroupOf H).map φ)).mul_mem (ihy hyH) (ihz hzH)
    rw [← map_mul] at this
    exact this
  | inv y hy ihy =>
    intro hg
    have hyH : y ∈ H := normalClosure_le hLH hy
    have := (normalClosure φ.range ((L.subgroupOf H).map φ)).inv_mem (ihy hyH)
    rw [← map_inv] at this
    exact this

theorem not_le_ker {H : Subgroup (GLV V)} {W₀ W₁ : Submodule (ZMod 2) V}
    (h₀ : Invariant H W₀) (h₁ : Invariant H W₁) (hirr : IrrSec H W₀ W₁)
    (hnt : ¬ ∀ x ∈ H, ∀ w ∈ W₁, x w - w ∈ W₀) {A S K : Subgroup ↥H} (hO : OrbitData A S K) :
    ¬ A ≤ (sectHom H h₀ h₁).ker := by
  intro hA
  haveI := hO.normal
  refine false_of_isPGroup h₀ h₁ hirr hnt hO.isPGroup fun y => ?_
  have hy : y ∈ A ⊔ S := by
    rw [hO.sup_eq]
    exact Subgroup.mem_top y
  obtain ⟨a, ha, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hy
  exact ⟨t, ht, by rw [map_mul, MonoidHom.mem_ker.1 (hA ha), one_mul]⟩

theorem mem_centralizer_of_ker {H : Subgroup (GLV V)} {A S K : Subgroup ↥H}
    (hO : OrbitData A S K) (φ : ↥H →* GLV V') (hA : ¬ A ≤ φ.ker) {x : ↥H}
    (hx : (x : GLV V) ∈ layerIn H) (hφ : φ x = 1) :
    (x : GLV V) ∈ Subgroup.centralizer (layerIn H : Set (GLV V)) := by
  have hcen := (hO.dichotomy (N := φ.ker)).resolve_left hA
  have hxc := hcen ⟨MonoidHom.mem_ker.2 hφ, (mem_layerIn_iff.1 hx).2⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨hgH, hg'⟩ := mem_layerIn_iff.1 hg
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hxc ⟨g, hgH⟩ hg')

theorem map_layerIn_eq [Finite V'] {H : Subgroup (GLV V)} {A S K : Subgroup ↥H}
    (hO : OrbitData A S K) (φ : ↥H →* GLV V') :
    ((layerIn H).subgroupOf H).map φ = layerIn φ.range := by
  haveI : Finite ↥φ.range := inferInstance
  have h1 : (layerIn H).subgroupOf H = CFSG.layer ↥H :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have h2 := map_layer_eq φ.rangeRestrict φ.rangeRestrict_surjective
    (hO.isSolvable_quotient (N := CFSG.layer ↥H) hO.A_le_layer)
  rw [h1]
  calc (CFSG.layer ↥H).map φ = ((CFSG.layer ↥H).map φ.rangeRestrict).map φ.range.subtype := by
        rw [Subgroup.map_map]
        rfl
    _ = layerIn φ.range := by rw [h2]

theorem gen_map {H : Subgroup (GLV V)} {A S K : Subgroup ↥H} (hO : OrbitData A S K)
    {L : Subgroup (GLV V)} (hLH : L ≤ H) (hLperf : ⁅L, L⁆ = L) (hLne : L ≠ ⊥)
    (hLA : L.subgroupOf H ≤ A) (φ : ↥H →* GLV V') :
    φ.range = normalClosure φ.range ((L.subgroupOf H).map φ) ⊔ S.map φ := by
  refine le_antisymm ?_ (sup_le (normalClosure_le (Subgroup.map_le_range φ _))
    (Subgroup.map_le_range φ _))
  have hrange : φ.range = A.map φ ⊔ S.map φ := by
    rw [MonoidHom.range_eq_map, ← hO.sup_eq, Subgroup.map_sup]
  refine hrange.le.trans (sup_le_sup_right ?_ _)
  haveI hMn : ((normalClosure H L).subgroupOf H).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (normalClosure_le hLH)).2 fun g hg => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro a
    refine ⟨fun ha => normalClosure_conj hg ha, fun ha => ?_⟩
    have := normalClosure_conj (H.inv_mem hg) ha
    rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at this
  have hAM : A ≤ (normalClosure H L).subgroupOf H :=
    hO.le_of_normal (commutator_subgroupOf_self hLH hLperf) (subgroupOf_ne_bot hLH hLne) hLA
      (Subgroup.comap_mono (le_normalClosure H L))
  rintro _ ⟨a, ha, rfl⟩
  exact map_mem_normalClosure hLH φ a (hAM ha) a.2

theorem component_map {H S L : Subgroup (GLV V)} (hSH : S ≤ H)
    (hcomp : IsComponentOf L (H ⊓ Subgroup.centralizer (S : Set (GLV V))))
    (φ : ↥H →* GLV V') (hLN : ¬ L.subgroupOf H ≤ φ.ker)
    (hNL : ⁅L.subgroupOf H, φ.ker⁆ = ⊥) :
    IsComponentOf ((L.subgroupOf H).map φ) (φ.range ⊓ Subgroup.centralizer
      (((S.subgroupOf H).map φ : Subgroup (GLV V')) : Set (GLV V'))) := by
  have hLX : L ≤ H ⊓ Subgroup.centralizer (S : Set (GLV V)) := hcomp.1
  have hLH : L ≤ H := hLX.trans inf_le_left
  have hLcS : ∀ s ∈ S, ∀ l ∈ L, s * l = l * s := fun s hs l hl =>
    (Subgroup.mem_centralizer_iff.1 (hLX hl).2) s hs
  have hLsub : CFSG.Open.IsSubnormal (L.subgroupOf H)
      ((H ⊓ Subgroup.centralizer (S : Set (GLV V))).subgroupOf H) := hcomp.2.1.comap H.subtype
  haveI hKerN : (φ.ker).Normal := MonoidHom.normal_ker φ
  let N : Subgroup ↥H := φ.ker
  let Y₂ : Subgroup ↥H := Subgroup.centralizer ((S.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊓
    Subgroup.centralizer (N : Set ↥H)
  let Y₁ : Subgroup ↥H := (Subgroup.centralizer
    (((S.subgroupOf H).map φ : Subgroup (GLV V')) : Set (GLV V'))).comap φ
  have hY₂Y₁ : Y₂ ≤ Y₁ := by
    intro y hy
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hy.1 s hs
    rw [← map_mul, ← map_mul, this]
  have hY₁conj : ∀ g ∈ Y₁, ∀ y ∈ Y₂, g * y * g⁻¹ ∈ Y₂ := by
    intro g hg y hy
    refine ⟨Subgroup.mem_centralizer_iff.2 fun s hs => ?_,
      Subgroup.mem_centralizer_iff.2 fun n hn => ?_⟩
    · have hs' : φ s * φ g = φ g * φ s :=
        Subgroup.mem_centralizer_iff.1 (Subgroup.mem_comap.1 hg) (φ s) ⟨s, hs, rfl⟩
      have ht : s⁻¹ * g⁻¹ * s * g ∈ N := by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_inv]
        calc (φ s)⁻¹ * (φ g)⁻¹ * φ s * φ g = (φ g * φ s)⁻¹ * (φ s * φ g) := by group
          _ = 1 := by rw [hs']; group
      have h1 : s * y = y * s := Subgroup.mem_centralizer_iff.1 hy.1 s hs
      have h2 : (s⁻¹ * g⁻¹ * s * g) * y = y * (s⁻¹ * g⁻¹ * s * g) :=
        Subgroup.mem_centralizer_iff.1 hy.2 _ ht
      have h3 : (g⁻¹ * s * g) * y = y * (g⁻¹ * s * g) := by
        have e : g⁻¹ * s * g = s * (s⁻¹ * g⁻¹ * s * g) := by group
        rw [e, mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
      calc s * (g * y * g⁻¹) = g * ((g⁻¹ * s * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * s * g)) * g⁻¹ := by rw [h3]
        _ = g * y * g⁻¹ * s := by group
    · have hc := Subgroup.mem_centralizer_iff.1 hy.2 (g⁻¹ * n * g⁻¹⁻¹) (hKerN.conj_mem n hn g⁻¹)
      calc n * (g * y * g⁻¹) = g * (g⁻¹ * n * g⁻¹⁻¹ * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * n * g⁻¹⁻¹)) * g⁻¹ := by rw [hc]
        _ = g * y * g⁻¹ * n := by group
  have hY₂norm : Y₁ ≤ Subgroup.normalizer (Y₂ : Set ↥H) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hY₁conj g hg y hy, fun hy => ?_⟩
    have := hY₁conj g⁻¹ (Y₁.inv_mem hg) _ hy
    rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at this
  have hLyY₂ : L.subgroupOf H ≤ Y₂ := by
    intro x hx
    refine ⟨Subgroup.mem_centralizer_iff.2 fun s hs => ?_,
      Subgroup.mem_centralizer_iff.2 fun n hn => ?_⟩
    · exact Subtype.ext (hLcS s hs x hx)
    · exact Subgroup.mem_centralizer_iff.1
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hNL) hx) n hn
  have hY₂c : Y₂ ≤ (H ⊓ Subgroup.centralizer (S : Set (GLV V))).subgroupOf H := by
    intro y hy
    refine ⟨y.2, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hy.1 ⟨s, hSH hs⟩ hs)
  have hsub₂ : CFSG.Open.IsSubnormal (L.subgroupOf H) Y₂ := by
    have := hLsub.inf_of_le hY₂c
    rwa [inf_eq_left.2 hLyY₂] at this
  have hsub₁ : CFSG.Open.IsSubnormal (L.subgroupOf H) Y₁ :=
    hsub₂.trans (.step hY₂Y₁ ((Subgroup.normal_subgroupOf_iff_le_normalizer hY₂Y₁).2 hY₂norm)
      (.refl Y₁))
  have hmapY₁ : Y₁.map φ = φ.range ⊓ Subgroup.centralizer
      (((S.subgroupOf H).map φ : Subgroup (GLV V')) : Set (GLV V')) :=
    Subgroup.map_comap_eq φ _
  refine ⟨?_, ?_, ?_⟩
  · refine le_inf (Subgroup.map_le_range φ _) ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hLcS s hs x hx))
  · have := hsub₁.map φ
    rwa [hmapY₁] at this
  · have hLyq : CFSG.IsQuasisimple ↥(L.subgroupOf H) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH).symm
        (isQuasisimple_native hcomp.2.2)
    exact isQuasisimple_open (CFSG.LocalCores.isQuasisimple_map hLyq φ hLN)

end Images

end Lemma63

open Lemma63 in
theorem lemma63 {G S L H₀ H : Subgroup (GLV V)} (h : Setup6 G S L) (hH₀ : H₀ ≤ G)
    (hLS : L ⊔ S ≤ H₀) (hH : H = normalClosure (layerIn H₀) L ⊔ S)
    {W₀ W₁ : Submodule (ZMod 2) V} (h₀ : Invariant H W₀) (h₁ : Invariant H W₁)
    (hirr : IrrSec H W₀ W₁) (hnt : ¬ ∀ x ∈ H, ∀ w ∈ W₁, x w - w ∈ W₀) :
    Setup6Irr (sectHom H h₀ h₁).range ((S.subgroupOf H).map (sectHom H h₀ h₁))
        ((L.subgroupOf H).map (sectHom H h₀ h₁)) ∧
      ((layerIn H).subgroupOf H).map (sectHom H h₀ h₁) = layerIn (sectHom H h₀ h₁).range ∧
      ∀ x : ↥H, (x : GLV V) ∈ layerIn H → sectHom H h₀ h₁ x = 1 →
        (x : GLV V) ∈ Subgroup.centralizer (layerIn H : Set (GLV V)) := by
  have h0 : Setup6 H₀ S L := setup6_of_le h hH₀ hLS
  obtain ⟨K, hO⟩ := exists_orbitData h0 hH
  have hAH : normalClosure (layerIn H₀) L ≤ H := by rw [hH]; exact le_sup_left
  have hSH : S ≤ H := by rw [hH]; exact le_sup_right
  have hLA : L ≤ normalClosure (layerIn H₀) L := le_normalClosure _ _
  have hLH : L ≤ H := hLA.trans hAH
  have hHH₀ : H ≤ H₀ := by
    rw [hH]
    exact sup_le (normalClosure_layerIn_le (hLS.trans' le_sup_left)) h0.S_le
  have hH' : Setup6 H S L := setup6_of_le h (hHH₀.trans hH₀) (sup_le hLH hSH)
  set φ := sectHom H h₀ h₁ with hφ
  obtain ⟨hLperf, hLne⟩ := perfect_ne_bot_of_isQuasisimple h.component.2.2
  have hLyA : L.subgroupOf H ≤ (normalClosure (layerIn H₀) L).subgroupOf H :=
    Subgroup.comap_mono hLA
  have hLyperf := commutator_subgroupOf_self hLH hLperf
  have hLyne := subgroupOf_ne_bot hLH hLne
  have hnA := not_le_ker h₀ h₁ hirr hnt hO
  have hLyN : ¬ L.subgroupOf H ≤ φ.ker := fun hle =>
    hnA (hO.le_of_normal hLyperf hLyne hLyA hle)
  have hNL := hO.commutator_ker_eq_bot hLyperf hLyA φ hnA
  have hnt' : ∃ l ∈ L, ∃ w ∈ W₁, l w - w ∉ W₀ := by
    obtain ⟨y, hyL, hy⟩ := SetLike.not_le_iff_exists.1 hLyN
    refine ⟨y, hyL, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hy (MonoidHom.mem_ker.2 ((sectHom_eq_one_iff h₀ h₁ y).2 hcon))
  refine ⟨?_, map_layerIn_eq hO φ, fun x hx hφx => mem_centralizer_of_ker hO φ hnA hx hφx⟩
  exact
    { S_le := Subgroup.map_le_range φ _
      isPGroup := hO.isPGroup.map φ
      component := component_map hSH hH'.component φ hLyN hNL
      irrTilde := hasIrrTildeV_sectHom h₀ h₁ hLH hLperf h.irrTilde hnt'
      irr := isIrr_range_sectHom h₀ h₁ hirr
      gen := gen_map hO hLH hLperf hLne hLyA φ }

end CFSG.CGT.Foote82
