module

public import CFSG.LocalAnalysis.AGLEmbedding.ChevTwoSurvivorBlocks
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Inner

variable {G : Type} [Group G] [Finite G]

theorem conj_conj_apply_of_mem_centralizer {Y : Type*} [Group Y] {Lb : Subgroup Y} {c s : Y}
    (hc : c ∈ Subgroup.centralizer (Lb : Set Y)) (hs : s ∈ Subgroup.normalizer (Lb : Set Y))
    {w : Y} (hw : w ∈ Lb) : (c * s * c⁻¹) * w * (c * s * c⁻¹)⁻¹ = s * w * s⁻¹ := by
  have hcw : c⁻¹ * w * c = w := by
    have := Subgroup.mem_centralizer_iff.mp hc w hw
    rw [mul_assoc, this, inv_mul_cancel_left]
  have hsw : s * w * s⁻¹ ∈ Lb := (Subgroup.mem_normalizer_iff.mp hs w).mp hw
  have hc2 : c * (s * w * s⁻¹) * c⁻¹ = s * w * s⁻¹ := by
    have := Subgroup.mem_centralizer_iff.mp hc _ hsw
    rw [← this, mul_inv_cancel_right]
  calc (c * s * c⁻¹) * w * (c * s * c⁻¹)⁻¹ = c * (s * (c⁻¹ * w * c) * s⁻¹) * c⁻¹ := by group
    _ = c * (s * w * s⁻¹) * c⁻¹ := by rw [hcw]
    _ = s * w * s⁻¹ := hc2

omit [Finite G] in
theorem mem_normalizer_barM_of_mem_barM_normalizer {M S : Subgroup G}
    {x : ↥M ⧸ CFSG.pCore 2 ↥M} (hx : x ∈ barM M (Subgroup.normalizer (S : Set G))) :
    x ∈ Subgroup.normalizer (barM M S : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  obtain ⟨m, hm, rfl⟩ := hx
  exact mem_normalizer_barM m.2 (Subgroup.mem_subgroupOf.mp hm)

theorem D1PhaseThree.exists_mem_blockParabolic {p : ℕ} {P : Sylow p G} {M H R L : Subgroup G}
    (h : D1PhaseThree p P M H R) (h84 : Asc81bEightFour) (h86 : Asc81bEightSix)
    (hD2 : D1NoXBlock) (hb : StmtBlockInnerNormalizer) (hL : IsWeakSBlock M (pCoreOf 2 H) L)
    {x : ↥M ⧸ CFSG.pCore 2 ↥M}
    (hxK : x ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G)))
    (hxLC : x ∈ barM M L ⊔ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))) :
    ∃ l ∈ blockParabolic M (pCoreOf 2 H) L,
      x * l⁻¹ ∈ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
  set Lb := barM M L with hLb
  set Cb := Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hCb
  have hLC : Lb ≤ Subgroup.normalizer (Cb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  have hSL : barM M (pCoreOf 2 H) ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
    h86 G M (pCoreOf 2 H) h.isKGroup.1 h.asc81bHyp _ hL.component
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right Lb Cb hLC] at hxLC
  obtain ⟨l, hl, c, hc, rfl⟩ := hxLC
  have hxS := mem_normalizer_barM_of_mem_barM_normalizer hxK
  refine ⟨l, hb h h84 h86 hD2 hL l hl fun s hs => ⟨l * c * s * (l * c)⁻¹, ?_, fun w hw => ?_⟩, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hxS s).mp hs
  · have hw' : l⁻¹ * w * l ∈ Lb := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hl) hw) hl
    have key := conj_conj_apply_of_mem_centralizer hc (hSL hs) hw'
    calc (l * s * l⁻¹) * w * (l * s * l⁻¹)⁻¹ = l * (s * (l⁻¹ * w * l) * s⁻¹) * l⁻¹ := by group
      _ = l * ((c * s * c⁻¹) * (l⁻¹ * w * l) * (c * s * c⁻¹)⁻¹) * l⁻¹ := by rw [key]
      _ = (l * c * s * (l * c)⁻¹) * w * (l * c * s * (l * c)⁻¹)⁻¹ := by group
  · have : l * c * l⁻¹ ∈ Cb := (Subgroup.mem_normalizer_iff.mp (hLC hl) c).mp hc
    simpa [mul_assoc] using this

theorem card_dvd_of_faithful_inner {Y : Type*} [Group Y] [Finite Y] {Lb I J : Subgroup Y}
    (hI : I ≤ Subgroup.normalizer (Lb : Set Y)) (hJ : J ≤ Subgroup.normalizer (Lb : Set Y))
    (hIC : I ⊓ Subgroup.centralizer (Lb : Set Y) = ⊥)
    (hIJ : ∀ x ∈ I, ∃ l ∈ J, x * l⁻¹ ∈ Subgroup.centralizer (Lb : Set Y)) :
    Nat.card I ∣ Nat.card J := by
  set Nn := Subgroup.normalizer (Lb : Set Y) with hNn
  set ρ : Nn →* MulAut Lb := Lb.normalizerMonoidHom with hρ
  have hker : ∀ g : Nn, ρ g = 1 ↔ (g : Y) ∈ Subgroup.centralizer (Lb : Set Y) := by
    intro g
    constructor
    · intro h1
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have h2 := congrArg (fun f : MulAut Lb => ((f ⟨w, hw⟩ : Lb) : Y)) h1
      simp only [hρ, MulAut.one_apply] at h2
      change (g : Y) * w * (g : Y)⁻¹ = w at h2
      rw [mul_inv_eq_iff_eq_mul] at h2
      exact h2.symm
    · intro hg
      ext ⟨w, hw⟩
      change (g : Y) * w * (g : Y)⁻¹ = w
      rw [mul_inv_eq_iff_eq_mul]
      exact (Subgroup.mem_centralizer_iff.mp hg w hw).symm
  set f : I →* MulAut Lb := ρ.comp (Subgroup.inclusion hI) with hf
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxC := (hker (Subgroup.inclusion hI x)).mp hx
    have hmem : (x : Y) ∈ I ⊓ Subgroup.centralizer (Lb : Set Y) := ⟨x.2, hxC⟩
    rw [hIC, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hrange : f.range ≤ (J.subgroupOf Nn).map ρ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨l, hl, hxl⟩ := hIJ x x.2
    refine ⟨⟨l, hJ hl⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
    have h1 : ρ (Subgroup.inclusion hI x * (⟨l, hJ hl⟩ : Nn)⁻¹) = 1 := (hker _).mpr hxl
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1.symm
  calc Nat.card I = Nat.card f.range := (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv)
    _ ∣ Nat.card ((J.subgroupOf Nn).map ρ) := Subgroup.card_dvd_of_le hrange
    _ ∣ Nat.card (J.subgroupOf Nn) := Subgroup.card_map_dvd _ _
    _ = Nat.card J := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ).toEquiv

end Inner

end CFSG.AGLEmbedding
