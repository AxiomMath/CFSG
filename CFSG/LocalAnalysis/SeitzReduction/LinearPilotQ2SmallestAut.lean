module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallResidual
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift centralizerPerfectCore)

section Generic

variable {K : Type*} [Group K]

@[expose] def FixingAutDichotomy (D : Subgroup K) (τ : MulAut K) : Prop :=
  ∀ α : MulAut K, (∀ d ∈ D, α d = d) → α = 1 ∨ α = τ

end Generic

section Conj

variable {G : Type} [Group G]

theorem mem_normalizer_centralizer_of_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ normalizer (X : Set G)) : g ∈ normalizer (centralizer (X : Set G) : Set G) := by
  have hX : ∀ x : G, x ∈ X ↔ g * x * g⁻¹ ∈ X := mem_normalizer_iff.1 hg
  rw [mem_normalizer_iff]
  intro h
  simp only [mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hh x hx
    have hx' : g⁻¹ * x * g ∈ X := by
      have := (hX (g⁻¹ * x * g)).2 (by simpa [mul_assoc] using hx)
      exact this
    have h1 := hh _ hx'
    calc x * (g * h * g⁻¹) = g * ((g⁻¹ * x * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
      _ = g * h * g⁻¹ * x := by group
  · intro hh x hx
    have h1 := hh _ ((hX x).1 hx)
    calc x * h = g⁻¹ * ((g * x * g⁻¹) * (g * h * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * h * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
      _ = h * x := by group

@[expose] noncomputable def neighbourCentralizerConj (X : Subgroup G) {g : G}
    (hg : g ∈ normalizer (X : Set G)) : MulAut (centralizer (X : Set G)) :=
  ((MulAut.conj g).subgroupMap (centralizer (X : Set G))).trans
    (MulEquiv.subgroupCongr
      (mem_normalizer_iff_map_conj_eq.1 (mem_normalizer_centralizer_of_normalizer hg)))

@[simp] theorem coe_neighbourCentralizerConj_apply (X : Subgroup G) {g : G}
    (hg : g ∈ normalizer (X : Set G)) (x : centralizer (X : Set G)) :
    ((neighbourCentralizerConj X hg x : centralizer (X : Set G)) : G) = g * (x : G) * g⁻¹ :=
  rfl

theorem map_oddCore_neighbourCentralizerConj (X : Subgroup G) {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    (oddCore (centralizer (X : Set G))).map (neighbourCentralizerConj X hg).toMonoidHom =
      oddCore (centralizer (X : Set G)) := by
  have := OddNormalCore.oddCore_characteristic (centralizer (X : Set G))
  exact Subgroup.characteristic_iff_map_eq.1 this _

@[expose] noncomputable def neighbourQuotConj (X : Subgroup G) {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    MulAut (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) :=
  QuotientGroup.congr _ _ (neighbourCentralizerConj X hg)
    (map_oddCore_neighbourCentralizerConj X hg)

theorem neighbourQuotConj_mk (X : Subgroup G) {g : G} (hg : g ∈ normalizer (X : Set G))
    (x : centralizer (X : Set G)) :
    neighbourQuotConj X hg (QuotientGroup.mk x) =
      QuotientGroup.mk (neighbourCentralizerConj X hg x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem map_perfectCore_top_mulAut {Y : Type*} [Group Y] [Finite Y] (φ : MulAut Y) :
    (perfectCore (⊤ : Subgroup Y)).map φ.toMonoidHom = perfectCore (⊤ : Subgroup Y) := by
  rw [CFSG.Quasithin.map_perfectCore, map_top_of_surjective _ φ.surjective]

@[expose] noncomputable def neighbourCoreConj [Finite G] (X : Subgroup G) {g : G}
    (hg : g ∈ normalizer (X : Set G)) :
    MulAut (perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G))))) :=
  ((neighbourQuotConj X hg).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_perfectCore_top_mulAut (neighbourQuotConj X hg)))

theorem coe_neighbourCoreConj_apply [Finite G] (X : Subgroup G) {g : G}
    (hg : g ∈ normalizer (X : Set G))
    (k : perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G))))) :
    ((neighbourCoreConj X hg k : perfectCore _) : centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G))) = neighbourQuotConj X hg k :=
  rfl

theorem hAut_of_fixingAutDichotomy [Finite G] {X : Subgroup G} {t j : G}
    (htN : t ∈ normalizer (X : Set G)) (hjN : j ∈ normalizer (X : Set G))
    {Dc : Subgroup (perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸
      oddCore (centralizer (X : Set G)))))}
    (hDc : ∀ d ∈ Dc, ∃ c : centralizer (X : Set G),
      (c : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
        (d : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) ∧
        j * (c : G) = (c : G) * j)
    (hdich : FixingAutDichotomy Dc (neighbourCoreConj X htN)) :
    (∀ x ∈ centralizerPerfectCore X, j * x * j⁻¹ * (t * x * t⁻¹)⁻¹ ∈
        (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype) ∨
      ∀ x ∈ centralizerPerfectCore X, j * x * j⁻¹ * x⁻¹ ∈
        (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype := by
  have hfix : ∀ d ∈ Dc, neighbourCoreConj X hjN d = d := by
    intro d hd
    obtain ⟨c, hcd, hjc⟩ := hDc d hd
    apply Subtype.ext
    rw [coe_neighbourCoreConj_apply, ← hcd, neighbourQuotConj_mk]
    congr 1
    apply Subtype.ext
    rw [coe_neighbourCentralizerConj_apply, hjc, mul_assoc, mul_inv_cancel, mul_one]
  have hmem : ∀ x ∈ centralizerPerfectCore X, ∃ hx : x ∈ centralizer (X : Set G),
      ((⟨x, hx⟩ : centralizer (X : Set G)) :
        centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) ∈
          perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸
            oddCore (centralizer (X : Set G)))) := by
    intro x hx
    have hxC : x ∈ centralizer (X : Set G) := F4Pilot.centralizerPerfectCore_le_centralizer X hx
    refine ⟨hxC, ?_⟩
    have hE := centralizerPerfectCore_eq_map_perfectCore_top X
    have hx' : x ∈ (perfectCore (⊤ : Subgroup (centralizer (X : Set G)))).map
        (centralizer (X : Set G)).subtype := hE ▸ hx
    obtain ⟨z, hz, hzx⟩ := hx'
    have hz' : z = ⟨x, hxC⟩ := Subtype.ext hzx
    rw [← hz']
    have hπ : (perfectCore (⊤ : Subgroup (centralizer (X : Set G)))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) = perfectCore ⊤ := by
      rw [CFSG.Quasithin.map_perfectCore, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    rw [← hπ]
    exact mem_map_of_mem _ hz
  have htrans : ∀ a b : centralizer (X : Set G),
      (a : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
        (b : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) →
      (a : G) * (b : G)⁻¹ ∈
        (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype := by
    intro a b hab
    have h1 := (QuotientGroup.eq_iff_div_mem).1 hab
    exact ⟨a / b, h1, by simp [div_eq_mul_inv]⟩
  rcases hdich (neighbourCoreConj X hjN) hfix with h | h
  · right
    intro x hx
    obtain ⟨hxC, hxK⟩ := hmem x hx
    have h1 : neighbourCoreConj X hjN ⟨_, hxK⟩ = ⟨_, hxK⟩ := by rw [h]; rfl
    have h2 := congrArg Subtype.val h1
    rw [coe_neighbourCoreConj_apply, neighbourQuotConj_mk] at h2
    simpa using htrans _ _ h2
  · left
    intro x hx
    obtain ⟨hxC, hxK⟩ := hmem x hx
    have h1 : neighbourCoreConj X hjN ⟨_, hxK⟩ = neighbourCoreConj X htN ⟨_, hxK⟩ := by rw [h]
    have h2 := congrArg Subtype.val h1
    rw [coe_neighbourCoreConj_apply, coe_neighbourCoreConj_apply, neighbourQuotConj_mk,
      neighbourQuotConj_mk] at h2
    simpa using htrans _ _ h2

end Conj

section Setting

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem xab_commute_of_mem_blockSL_compl {n : ℕ} {K : Type} [Field K]
    (e : L ≃* LinearFlag.projectiveSL n K) {a b : Fin n} (hab : a ≠ b) {d : G}
    (hd : d ∈ ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype) :
    ((e.symm (xab hab 1) : L) : G) * d = d * ((e.symm (xab hab 1) : L) : G) := by
  obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hd
  have hc := commute_blockSL_of_disjoint (K := K) (I := {a, b}) (J := ({a, b} : Finset (Fin n))ᶜ)
    disjoint_compl_right (xab hab 1) (xab_mem_rootSL2 hab 1) y hy
  have h1 : e.symm (xab hab 1) * e.symm y = e.symm y * e.symm (xab hab 1) := by
    rw [← map_mul, ← map_mul, hc.eq]
  exact congrArg Subtype.val h1

theorem rootSL2_le_centralizer_or_card_dvd_of_fixingAutDichotomy (hset : SeitzSetting G L)
    {n : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL n K)
    (hn : 5 ≤ n) {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n}
    (hab : a ≠ b) {X₀ : Subgroup (LinearFlag.projectiveSL n K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    (hB : ∀ x ∈ centralizerPerfectCore X,
      x ∈ (oddCore (centralizer (X : Set G))).map (centralizer (X : Set G)).subtype →
      ∀ y ∈ centralizerPerfectCore X, x * y = y * x)
    (hdich : FixingAutDichotomy
      ((((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf
          (perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸
            oddCore (centralizer (X : Set G)))))))
      (neighbourCoreConj X (Subgroup.centralizer_le_normalizer (X : Set G) htX))) :
    (∃ g : G, (centralizerPerfectCore X).map (MulAut.conj g).toMonoidHom ≤ L ∧
        Nat.card (centralizerPerfectCore X) ∣ Nat.card L) ∨
      ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype ≤
        centralizer (centralizerPerfectCore X : Set G) := by
  have hjN : ((e.symm (xab hab 1) : L) : G) ∈ normalizer (X : Set G) := by
    rw [hX]
    exact map_symm_mem_normalizer e (mem_normalizer_of_mem_rootSL2_two hK (by omega) hab hX₀
      hX₀c (xab_mem_rootSL2 hab 1))
  have hDc : ∀ d ∈ (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).subgroupOf
          (perfectCore (⊤ : Subgroup (centralizer (X : Set G) ⧸
            oddCore (centralizer (X : Set G)))))),
      ∃ c : centralizer (X : Set G),
        (c : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) =
          (d : centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))) ∧
          ((e.symm (xab hab 1) : L) : G) * (c : G) = (c : G) * ((e.symm (xab hab 1) : L) : G) := by
    intro d hd
    obtain ⟨c, hc, hcd⟩ := mem_subgroupOf.1 hd
    refine ⟨c, hcd, ?_⟩
    have hcD : (c : G) ∈ D := mem_subgroupOf.1 hc
    rw [hDe] at hcD
    exact xab_commute_of_mem_blockSL_compl e hab hcD
  have hAut := hAut_of_fixingAutDichotomy (Subgroup.centralizer_le_normalizer (X : Set G) htX) hjN
    hDc hdich
  exact rootSL2_le_centralizer_or_card_dvd_linear_two hset hK e hn htC ht hab hX₀ hX₀c hX hB hAut

end Setting

end CFSG.SeitzReduction.LinearPilot
