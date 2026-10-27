module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zMSylow
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem k631b_isSubnormal_inf {J X Z : Subgroup G} (hJ : IsSubnormal J X) (hZX : Z ≤ X) :
    IsSubnormal (J ⊓ Z) Z := by
  have h1 := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_comap' Z.subtype hJ
  have h2 : X.comap Z.subtype = ⊤ := eq_top_iff.2 fun z _ => hZX z.2
  rw [h2] at h1
  have h3 := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_map' Z.subtype h1
  have h4 : (J.comap Z.subtype).map Z.subtype = J ⊓ Z := Subgroup.subgroupOf_map_subtype J Z
  rwa [h4, Subgroup.map_top, Subgroup.range_subtype] at h3

theorem k631b_centralizer_zpowers (u : G) :
    centralizer ((zpowers u : Subgroup G) : Set G) = centralizer ({u} : Set G) := by
  ext g
  rw [mem_centralizer_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact (h u (mem_zpowers u)).symm
  · intro h y hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute u g from h.symm) n).eq

variable [Finite G]

theorem k631b_lift_J1 {f : ℕ} (hf : f.Prime) {O J₁ : Subgroup G} {a : G}
    (haf : IsPGroup f (zpowers a)) (ha : a ∈ k631Triv O J₁) (hO : ¬ f ∣ Nat.card O) :
    ∀ j ∈ J₁, ∃ c ∈ J₁ ⊓ centralizer ({a} : Set G), c⁻¹ * j ∈ O := by
  have : Fact f.Prime := ⟨hf⟩
  intro j hj
  obtain ⟨c, hc, hcj⟩ := k631m_lift haf (zpowers_le.mpr ha) hO j hj
  rw [k631b_centralizer_zpowers] at hc
  exact ⟨c, hc, hcj.1⟩

private noncomputable def k631b_barXHom (p : ℕ) {X J : Subgroup G} (hJX : J ≤ X) :
    ↥J →* ↥(CFSG.LocalAnalysis.GLTheoremB.barX p X J) :=
  ((QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (Subgroup.inclusion hJX)).codRestrict
    (CFSG.LocalAnalysis.GLTheoremB.barX p X J)
    (fun x => ⟨⟨x, hJX x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩)

omit [Finite G] in
private theorem k631b_barXHom_surjective (p : ℕ) {X J : Subgroup G} (hJX : J ≤ X) :
    Function.Surjective (k631b_barXHom p hJX) := by
  rintro ⟨_, ⟨⟨l, hlX⟩, hl, rfl⟩⟩
  exact ⟨⟨l, Subgroup.mem_subgroupOf.1 hl⟩, rfl⟩

omit [Finite G] in
private theorem k631b_barXHom_ker {p : ℕ} {X J : Subgroup G} (hJX : J ≤ X)
    (hcore : J ⊓ GLAPPrimeCoreOf p X = GLAPPrimeCoreOf p J) :
    (k631b_barXHom p hJX).ker =
      GLAPPrimeCore p ↥J := by
  ext x
  rw [MonoidHom.mem_ker]
  have h1 : k631b_barXHom p hJX x = 1 ↔
      (⟨(x : G), hJX x.2⟩ : ↥X) ∈ GLAPPrimeCore p ↥X := by
    rw [← QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  rw [h1]
  have h2 : (⟨(x : G), hJX x.2⟩ : ↥X) ∈ GLAPPrimeCore p ↥X ↔ (x : G) ∈ GLAPPrimeCoreOf p X := by
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff]
    exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h⟩
  rw [h2]
  have h3 : (x : G) ∈ GLAPPrimeCoreOf p X ↔ (x : G) ∈ GLAPPrimeCoreOf p J := by
    rw [← hcore]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  rw [h3, CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

private theorem k631b_isQuasisimple_barX {f : ℕ} (hf : f.Prime) {X Z J₁ J₂ : Subgroup G}
    (hJ₁ : GLAPComponent f X J₁) (hJ₂Z : IsSubnormal J₂ Z) (hJ₂X : J₂ ≤ X)
    (hbar : CFSG.LocalAnalysis.GLTheoremB.barX f X J₂ =
      CFSG.LocalAnalysis.GLTheoremB.barX f X J₁) :
    CFSG.Open.IsQuasisimple ↥(CFSG.LocalAnalysis.GLTheoremB.barX f Z J₂) := by
  have hq1 : CFSG.Open.IsQuasisimple ↥(CFSG.LocalAnalysis.GLTheoremB.barX f X J₁) :=
    hJ₁.2.2.1.2.2
  have hq2 : CFSG.Open.IsQuasisimple ↥(CFSG.LocalAnalysis.GLTheoremB.barX f X J₂) := by
    rw [hbar]
    exact hq1
  have hbot : GLAPPrimeCore f ↥(CFSG.LocalAnalysis.GLTheoremB.barX f X J₂) = ⊥ := by
    rw [hbar]
    exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.glaPPrimeCore_eq_bot_of_isSubnormal
      (CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCore_quotient_eq_bot hf)
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_isSubnormal_top f hJ₁.2.1)
  have hcore := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.gLAPPrimeCoreOf_eq_inf hf
    hJ₂X hbot
  have hker := k631b_barXHom_ker hJ₂X hcore.symm
  let e : CFSG.HardMathSupport.Solomon.LocalBalance.barOf f J₂ ≃*
      ↥(CFSG.LocalAnalysis.GLTheoremB.barX f X J₂) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        (k631b_barXHom_surjective f hJ₂X))
  exact (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isQuasisimple_barX_iff hf
    hJ₂Z).2 (CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e.symm hq2)

private theorem k631b_exists_min_component {f : ℕ} {Z J₂ : Subgroup G} (hJ₂Z : IsSubnormal J₂ Z)
    (hcomp : IsComponentOf (CFSG.LocalAnalysis.GLTheoremB.barX f Z J₂) ⊤) :
    ∃ J₀ : Subgroup G, GLAPComponent f Z J₀ ∧ J₀ ≤ J₂ ∧
      CFSG.LocalAnalysis.GLTheoremB.barX f Z J₀ = CFSG.LocalAnalysis.GLTheoremB.barX f Z J₂ := by
  classical
  obtain ⟨L, ⟨hLJ, hsn, hbar⟩, hmin⟩ := (wellFounded_lt (α := Subgroup G)).has_min
    {J : Subgroup G | J ≤ J₂ ∧ IsSubnormal J Z ∧
      CFSG.LocalAnalysis.GLTheoremB.barX f Z J = CFSG.LocalAnalysis.GLTheoremB.barX f Z J₂}
    ⟨J₂, le_rfl, hJ₂Z, rfl⟩
  refine ⟨L, ⟨hLJ.trans (CFSG.LocalAnalysis.GLTheoremB.isSubnormal_le' hJ₂Z), hsn, ?_, ?_⟩,
    hLJ, hbar⟩
  · change IsComponentOf (CFSG.LocalAnalysis.GLTheoremB.barX f Z L) ⊤
    rw [hbar]
    exact hcomp
  · intro J hJ hJsn heq
    exact hmin J ⟨hJ.le.trans hLJ, hJsn, heq.trans hbar⟩ hJ

private theorem k631b_mem_of_pElement {f : ℕ} (hf : f.Prime) {Z J₂ J₀ : Subgroup G}
    (hJ₀ : GLAPComponent f Z J₀) (hJ₂Z : IsSubnormal J₂ Z) (hJ₀J₂ : J₀ ≤ J₂)
    (hbar : CFSG.LocalAnalysis.GLTheoremB.barX f Z J₀ =
      CFSG.LocalAnalysis.GLTheoremB.barX f Z J₂) {x : G} (hx : x ∈ J₂)
    (hxf : IsPGroup f (zpowers x)) : x ∈ J₀ := by
  have hcov := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_eq_iff_cov hf hJ₂Z
    hJ₀J₂).1 hbar
  have hKJ₂ : GLAPPrimeCoreOf f J₂ ≤ J₂ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.gLAPPrimeCoreOf_le f J₂
  have hJ₂n : J₂ ≤ normalizer (GLAPPrimeCoreOf f J₂ : Set G) :=
    CFSG.LocalAnalysis.GLTheoremB.le_normalizer_glaPPrimeCoreOf f J₂
  have hdvd : J₀.relIndex J₂ ∣ Nat.card ↥(GLAPPrimeCoreOf f J₂) :=
    k631m_relIndex_dvd hJ₀J₂ hKJ₂ hJ₂n hcov
  have hKN : GLAPPrimeCoreOf f J₂ ≤ normalizer (J₀ : Set G) := by
    refine le_trans ?_ (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPPrimeCoreOf_le_normalizer
      hJ₀)
    rw [← CFSG.LocalAnalysis.GLTheoremB.glaPPrimeCoreOf_inf_eq_of_isSubnormal hf hJ₂Z]
    exact inf_le_right
  have hJ₂N : J₂ ≤ normalizer (J₀ : Set G) := by
    intro j hj
    obtain ⟨c, hc, hck⟩ := hcov j hj
    have hjc : j = c * (c⁻¹ * j) := by group
    rw [hjc]
    exact mul_mem (le_normalizer hc) (hKN hck)
  have hnorm : (J₀.subgroupOf J₂).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₀J₂).2 hJ₂N
  have hpow : x ^ J₀.relIndex J₂ ∈ J₀ := by
    have h1 := Subgroup.pow_index_mem (J₀.subgroupOf J₂) (⟨x, hx⟩ : J₂)
    simpa [Subgroup.mem_subgroupOf, Subgroup.relIndex] using h1
  obtain ⟨n, hn⟩ := k631a_exists_pow_eq_one hxf (mem_zpowers x)
  have hcop : Nat.Coprime f (Nat.card ↥(GLAPPrimeCoreOf f J₂)) :=
    (Nat.Prime.coprime_iff_not_dvd hf).2
      (CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf hf J₂)
  have hcop' : Nat.Coprime (J₀.relIndex J₂) (f ^ n) :=
    Nat.Coprime.pow_right n (Nat.Coprime.coprime_dvd_right hdvd hcop).symm
  exact k631a_mem_of_pow_mem hcop' hpow (by rw [hn]; exact J₀.one_mem)

theorem k631b_exists_J0 {f : ℕ} (hf : f.Prime) {u a : G} (haf : IsPGroup f (zpowers a))
    {J₁ : Subgroup G} (hJ₁ : GLAPComponent f (centralizer ({u} : Set G)) J₁)
    (ha : a ∈ k631Triv (GLAPPrimeCoreOf f (centralizer ({u} : Set G))) J₁) :
    ∃ J₀ : Subgroup G,
      GLAPComponent f (centralizer ({a} : Set G) ⊓ centralizer ((zpowers u : Subgroup G) : Set G))
        J₀ ∧ J₀ ≤ J₁ ∧ ∀ x ∈ J₁, a * x = x * a → IsPGroup f (zpowers x) → x ∈ J₀ := by
  rw [k631b_centralizer_zpowers]
  have hJ₁X : J₁ ≤ centralizer ({u} : Set G) := hJ₁.1
  have hZX : centralizer ({a} : Set G) ⊓ centralizer ({u} : Set G) ≤ centralizer ({u} : Set G) :=
    inf_le_right
  have hJ₂eq : J₁ ⊓ (centralizer ({a} : Set G) ⊓ centralizer ({u} : Set G)) =
      J₁ ⊓ centralizer ({a} : Set G) :=
    le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
      (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hJ₁X)))
  have hJ₂Zsn : IsSubnormal (J₁ ⊓ centralizer ({a} : Set G))
      (centralizer ({a} : Set G) ⊓ centralizer ({u} : Set G)) := by
    have h := k631b_isSubnormal_inf hJ₁.2.1 hZX
    rwa [hJ₂eq] at h
  have hJ₂X : J₁ ⊓ centralizer ({a} : Set G) ≤ centralizer ({u} : Set G) :=
    inf_le_left.trans hJ₁X
  have hlift := k631b_lift_J1 hf haf ha
    (CFSG.LocalAnalysis.GLTheoremB.not_dvd_card_glaPPrimeCoreOf hf _)
  have hbar : CFSG.LocalAnalysis.GLTheoremB.barX f (centralizer ({u} : Set G))
      (J₁ ⊓ centralizer ({a} : Set G)) =
      CFSG.LocalAnalysis.GLTheoremB.barX f (centralizer ({u} : Set G)) J₁ :=
    le_antisymm (CFSG.LocalAnalysis.GLTheoremB.barX_mono f inf_le_left)
      (CFSG.LocalAnalysis.GLTheoremB.barX_le_of_forall hJ₂X hlift)
  have hqs := k631b_isQuasisimple_barX hf hJ₁ hJ₂Zsn hJ₂X hbar
  obtain ⟨J₀, hJ₀, hJ₀J₂, hJ₀bar⟩ := k631b_exists_min_component (f := f) hJ₂Zsn
    ⟨le_top, CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.barX_isSubnormal_top f hJ₂Zsn,
      hqs⟩
  refine ⟨J₀, hJ₀, hJ₀J₂.trans inf_le_left, fun x hx hax hxf => ?_⟩
  exact k631b_mem_of_pElement hf hJ₀ hJ₂Zsn hJ₀J₂ hJ₀bar
    ⟨hx, mem_centralizer_singleton_iff.mpr hax.symm⟩ hxf

end CFSG.LocalAnalysis.RankThreeTheoremC
