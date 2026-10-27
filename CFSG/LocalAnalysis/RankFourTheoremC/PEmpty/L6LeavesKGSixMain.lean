module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGSixMod
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGMain
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGSixJ

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGSix

open CFSG.Open CFSG.HardMathSupport.Solomon.UniquenessMaximal Subgroup

theorem transvection_of_data
    {G : Type} [Group G] [Finite G] {p : ℕ} {H D S B L M : Subgroup G} {z : G}
    [hDn : (D.subgroupOf H).Normal] (d3 : KGC.KGData3 p H D S B L M z)
    [IsCyclic ↥(KGC.img H D S)] :
    ∃ (V : Type) (_ : CommGroup V) (_ : Finite V) (_ : IsElemAbelianTwo V)
      (ρ : KGC.QA H D →* MulAut V), ¬ KGC.img H D L ≤ ρ.ker ∧
      ∃ a ∈ KGC.img H D S, a ≠ 1 ∧ a ^ 2 = 1 ∧ IsTransvection (ρ a) := by
  have d := d3.toData
  have c := d.cfg
  have hDS : D ≤ S := d.D_lt_S.le
  have hHD : H ≤ normalizer (D : Set G) := d.H_le_D
  have hS1 : S ≠ ⊥ := (bot_le.trans_lt d.D_lt_S).ne'
  set V : Subgroup G := omegaCenter D with hVdef
  have hVD : V ≤ D := omegaCenter_le D
  have hHV : H ≤ normalizer (V : Set G) := fun h hh => mem_normalizer_omegaCenter (hHD hh)
  let ρ₀ : ↥H →* MulAut ↥V := repH hHV
  have hρ₀ : ∀ (h : ↥H) (v : ↥V), ((ρ₀ h v : ↥V) : G) = (h : G) * v * (h : G)⁻¹ :=
    fun h v => repH_apply hHV h v
  have hker : D.subgroupOf H ≤ ρ₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    ext v
    rw [hρ₀, MulAut.one_apply]
    have := v.2.2.2 x hx
    rw [this]
    group
  let ρ : KGC.QA H D →* MulAut ↥V := QuotientGroup.lift (D.subgroupOf H) ρ₀ hker
  have hρ : ∀ h : ↥H, ρ (KGC.qmk H D h) = ρ₀ h := fun h => rfl
  haveI : IsMulCommutative ↥V := (isElemAbelian_omegaCenter D).1
  letI : CommGroup ↥V := { (inferInstance : Group ↥V) with mul_comm := fun a b => mul_comm' a b }
  have hVel : IsElemAbelianTwo ↥V := fun v => Subtype.ext (by simpa [pow_two] using v.2.2.1)
  have hchar : ∀ S₀ : Subgroup G, S₀ ≤ S → S₀ ≠ ⊥ → (S₀.subgroupOf S).Characteristic →
      normalizer (S₀ : Set G) ≤ M := d3.char_le
  have hV₁V : omegaCenter S ≤ V := by
    intro v hv
    obtain ⟨hvS, hv2, hvc⟩ := hv
    have hvD : v ∈ D :=
      d3.charTwo ⟨d.S_le_H hvS, mem_centralizer_iff.mpr fun x hx => hvc x (hDS hx)⟩
    exact ⟨hvD, hv2, fun x hx => hvc x (hDS hx)⟩
  have hV₁M : normalizer (omegaCenter S : Set G) ≤ M :=
    hchar _ (omegaCenter_le S) (omegaCenter_ne_bot d.S_two hS1) (omegaCenter_char S)
  have hρK : ¬ KGC.img H D L ≤ ρ.ker := by
    intro hle
    apply d.L_not_le
    intro l hl
    apply hV₁M
    refine KGB.mem_normalizer_of_commute fun t ht => ?_
    have hlH : l ∈ H := d.L_le_H hl
    have hq : KGC.qmk H D ⟨l, hlH⟩ ∈ KGC.img H D L := KGC.mem_img.mpr ⟨⟨l, hlH⟩, hl, rfl⟩
    have h2 : ρ₀ ⟨l, hlH⟩ = 1 := hle hq
    have h3 := congrArg (fun f : MulAut ↥V => ((f ⟨t, hV₁V ht⟩ : ↥V) : G)) h2
    simp only [hρ₀, MulAut.one_apply] at h3
    rwa [mul_inv_eq_iff_eq_mul] at h3
  obtain ⟨A₀, hA, hA₀D⟩ := exists_isEmax_not_le hDS hHD d.L_le_H d.S_two hS1 hchar d.L_not_le
  obtain ⟨a₀, ha₀A, ha₀D⟩ := Set.not_subset.mp hA₀D
  have ha₀S : a₀ ∈ S := hA.1 ha₀A
  have ha₀H : a₀ ∈ H := d.S_le_H ha₀S
  have ha₀2 : a₀ ^ 2 = 1 := hA.2.1.2 a₀ ha₀A
  set a : KGC.QA H D := KGC.qmk H D ⟨a₀, ha₀H⟩ with ha_def
  have haS : a ∈ KGC.img H D S := KGC.mem_img.mpr ⟨⟨a₀, ha₀H⟩, ha₀S, rfl⟩
  have ha1 : a ≠ 1 := fun h => ha₀D (KGC.qmk_eq_one_iff.mp h)
  have ha2 : a ^ 2 = 1 := by
    rw [ha_def, ← map_pow]
    have : (⟨a₀, ha₀H⟩ : ↥H) ^ 2 = 1 := Subtype.ext ha₀2
    rw [this, map_one]
  have hρa : ρ a ≠ 1 := fun h =>
    ha1 (eq_one_of_map_eq_one c ρ hρK (Subgroup.mem_sup_right haS) h)
  have hidx : Nat.card A₀ ≤ 2 * Nat.card ↥(A₀ ⊓ centralizer (V : Set G)) := by
    let φ : ↥A₀ →* KGC.QA H D :=
      (KGC.qmk H D).comp (Subgroup.inclusion (hA.1.trans d.S_le_H))
    have hφS : ∀ x : ↥A₀, φ x ∈ KGC.img H D S := fun x =>
      KGC.mem_img.mpr ⟨⟨x, d.S_le_H (hA.1 x.2)⟩, hA.1 x.2, rfl⟩
    let φ' : ↥A₀ →* ↥(KGC.img H D S) := φ.codRestrict _ hφS
    have hprod : Nat.card φ'.ker * Nat.card φ'.range = Nat.card ↥A₀ := by
      rw [← Subgroup.index_ker]
      exact Subgroup.card_mul_index _
    have hR : Nat.card φ'.range ≤ 2 := by
      refine card_le_two_of_sq _ ?_
      rintro _ ⟨x, rfl⟩
      rw [← map_pow]
      have : x ^ 2 = 1 := Subtype.ext (hA.2.1.2 x x.2)
      rw [this, map_one]
    have hK : Nat.card φ'.ker ≤ Nat.card ↥(A₀ ⊓ centralizer (V : Set G)) := by
      have hle : φ'.ker.map A₀.subtype ≤ A₀ ⊓ centralizer (V : Set G) := by
        rintro _ ⟨y, hy, rfl⟩
        have hyD : (y : G) ∈ D := by
          have h1 : KGC.qmk H D ⟨(y : G), d.S_le_H (hA.1 y.2)⟩ = 1 :=
            congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
          exact (KGC.qmk_eq_one_iff (H := H) (D := D)).mp h1
        refine ⟨y.2, mem_centralizer_iff.mpr fun v hv => ?_⟩
        exact (hv.2.2 y hyD).symm
      rw [← Subgroup.card_map_of_injective (K := φ'.ker) A₀.subtype_injective]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hle)
    calc Nat.card A₀ = Nat.card φ'.ker * Nat.card φ'.range := hprod.symm
      _ ≤ Nat.card ↥(A₀ ⊓ centralizer (V : Set G)) * 2 := Nat.mul_le_mul hK hR
      _ = 2 * Nat.card ↥(A₀ ⊓ centralizer (V : Set G)) := mul_comm _ _
  have hcard := card_le_two_mul hA (isElemAbelian_omegaCenter D) (hVD.trans hDS) hidx ha₀A
  have hρa_app : ∀ w : ↥V, ((ρ a w : ↥V) : G) = a₀ * (w : G) * a₀⁻¹ := fun w => by
    rw [ha_def, hρ]
    exact hρ₀ ⟨a₀, ha₀H⟩ w
  have hfix : Nat.card ↥(fixedSub (ρ a)) = Nat.card ↥(V ⊓ centralizer ({a₀} : Set G)) := by
    have hmap : (fixedSub (ρ a)).map V.subtype = V ⊓ centralizer ({a₀} : Set G) := by
      ext x
      constructor
      · rintro ⟨w, hw, rfl⟩
        refine ⟨w.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        have h1 : (a₀ * (w : G) * a₀⁻¹) = w := by
          rw [← hρa_app w]
          exact congrArg Subtype.val (show ρ a w = w from hw)
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
      · rintro ⟨hxV, hxc⟩
        refine ⟨⟨x, hxV⟩, ?_, rfl⟩
        show ρ a ⟨x, hxV⟩ = ⟨x, hxV⟩
        refine Subtype.ext ?_
        have h1 : x * a₀ = a₀ * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
        rw [hρa_app ⟨x, hxV⟩, mul_inv_eq_iff_eq_mul]
        exact h1.symm
    rw [← hmap, Subgroup.card_map_of_injective V.subtype_injective]
  have htv : IsTransvection (ρ a) :=
    isTransvection_of_card_le hρa (by rw [hfix]; exact hcard)
  exact ⟨↥V, inferInstance, inferInstance, hVel, ρ, hρK, a, haS, ha1, ha2, htv⟩

theorem false_of_data (hT : KGTransvCent) (h241 : KFact2401ThreeOmega)
    {G : Type} [Group G] [Finite G] {p : ℕ} {H D S B L M : Subgroup G} {z : G}
    [hDn : (D.subgroupOf H).Normal] (d3 : KGC.KGData3 p H D S B L M z)
    (hG : KGC.KGStrongEmb p M z)
    (hc : KGStep4Concl (KGC.QA H D) (KGC.img H D L) (KGC.img H D S))
    (hbot : KGC.img H D S ⊓ KGC.img H D L = ⊥) [IsCyclic ↥(KGC.img H D S)] : False := by
  obtain ⟨V, _, _, hV, ρ, hρK, a, haS, ha1, ha2, htv⟩ := transvection_of_data d3
  exact false_of_transv hT h241 d3.toData.cfg (d3.toData.strong_img hG) hc hbot hV ρ hρK haS ha1
    ha2 htv

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KGSix

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

theorem kgStep6Cyc_of_inputs (hT : KGTransvCent) (h241 : KFact2401ThreeOmega) : KGStep6Cyc := by
  intro G _ _ p P M x z hS hx hz H S hopt hO hΩ hnpc h2 L _ d3 hG hc hcase
  obtain ⟨hbot, hcyc⟩ := hcase
  haveI := hcyc
  exact KGSix.false_of_data hT h241 d3 hG hc hbot

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
