module

public import CFSG.LocalAnalysis.ComponentClassification.Foote47Conf
public import CFSG.LocalAnalysis.ComponentClassification.Foote47P3Gen
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm46

public section

namespace CFSG.ComponentClassification.Foote47

open CFSG Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.FooteLit
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_of_mem_centralizer {X : Subgroup G} {g : G}
    (hg : g ∈ centralizer (X : Set G)) : g ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro w
  have hc : ∀ g ∈ centralizer (X : Set G), ∀ w ∈ X, g * w * g⁻¹ = w := fun g hg w hw => by
    rw [← mem_centralizer_iff.mp hg w hw, mul_inv_cancel_right]
  constructor
  · intro hw
    rw [hc g hg w hw]
    exact hw
  · intro hw
    have h1 := hc g⁻¹ (inv_mem hg) _ hw
    rw [show g⁻¹ * (g * w * g⁻¹) * g⁻¹⁻¹ = w by group] at h1
    rw [h1]
    exact hw

namespace Conf

variable {M T S P : Subgroup G} {t z : G}

omit [Finite G] in
theorem le_normalizer_T (c : Conf L M T S P t z) : S ≤ normalizer (T : Set G) := fun s hs => by
  rw [c.hT]
  exact mem_normalizer_inf' (le_normalizer hs) (mem_normalizer_coreActionKernel (c.hSN.le hs))

omit [Finite G] in
theorem exists_not_comm (c : Conf L M T S P t z) : ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x := by
  obtain ⟨Q₀, hd⟩ := c.hd
  by_contra hall
  push Not at hall
  exact hd.t_ne_z (hd.hzZ t c.htT c.hv.ht fun y hy => hall t c.htT y hy)

theorem inf_conjugate_eq_bot (c : Conf L M T S P t z) {g : G}
    (hgS : g ∈ normalizer (S : Set G)) (hgz : g ∉ centralizer ({z} : Set G)) :
    T ⊓ conjugate T g = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀, hd⟩ := c.hd
  have hTS : T ≤ S := c.hT ▸ inf_le_left
  have hSg : conjugate S g = S := conjugate_eq_of_mem_normalizer hgS
  have hT'S : conjugate T g ≤ S := hSg ▸ map_mono hTS
  have hSN := c.le_normalizer_T
  have hSN' : S ≤ normalizer ((conjugate T g : Subgroup G) : Set G) := by
    intro s hs
    have hs' : g * s * g⁻¹ ∈ S := (mem_normalizer_iff.mp hgS s).mp hs
    rw [mem_normalizer_iff]
    intro x
    rw [mem_conjugate_iff, mem_conjugate_iff,
      show g * (s * x * s⁻¹) * g⁻¹ = (g * s * g⁻¹) * (g * x * g⁻¹) * (g * s * g⁻¹)⁻¹ by group]
    exact mem_normalizer_iff.mp (hSN hs') _
  by_contra hne
  set N₀ := T ⊓ conjugate T g with hN₀
  have hN₀S : N₀ ≤ S := inf_le_left.trans hTS
  have hSp : IsPGroup 2 S := c.hSz.isPGroup
  have : Group.IsNilpotent S := hSp.isNilpotent
  have hn : (N₀.subgroupOf S).Normal := by
    rw [normal_subgroupOf_iff_le_normalizer hN₀S]
    exact fun s hs => mem_normalizer_inf' (hSN hs) (hSN' hs)
  have hne' : N₀.subgroupOf S ≠ ⊥ := by
    intro hb
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hN₀S hx⟩ : S) ∈ N₀.subgroupOf S := hx
    rw [hb, mem_bot] at h1
    exact (mem_bot).mpr (congrArg Subtype.val h1)
  have hne2 := Group.IsNilpotent.inf_center_ne_bot_of_normal hne'
  obtain ⟨⟨⟨y, hyS⟩, hy⟩, hy1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne2
  have hy1 : (⟨y, hyS⟩ : S) ≠ 1 := fun h => hy1' (Subtype.ext h)
  obtain ⟨hyN, hyZ⟩ := mem_inf.mp hy
  set Y := N₀ ⊓ centralizer (S : Set G) with hY
  have hyY : (y : G) ∈ Y := by
    refine mem_inf.mpr ⟨hyN, mem_centralizer_iff.mpr fun s hs => ?_⟩
    exact (congrArg Subtype.val (mem_center_iff.mp hyZ ⟨s, hs⟩))
  have hYp : IsPGroup 2 Y := hSp.to_le (inf_le_left.trans hN₀S)
  have hY1 : Y ≠ ⊥ := fun hb => by
    rw [hb, mem_bot] at hyY
    exact hy1 (Subtype.ext hyY)
  obtain ⟨n, hn0, hn2⟩ := hYp.nontrivial_iff_card.mp ((nontrivial_iff_ne_bot Y).mpr hY1)
  obtain ⟨⟨x₀, hx₀Y⟩, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := Y) 2
    (hn2 ▸ dvd_pow_self 2 (by omega))
  have hx₀o : orderOf x₀ = 2 := by rw [← hx₀, Subgroup.orderOf_mk]
  obtain ⟨⟨hx₀T, hx₀T'⟩, hx₀Z⟩ := hx₀Y
  have hx₀c : ∀ s ∈ S, x₀ * s = s * x₀ := fun s hs => (mem_centralizer_iff.mp hx₀Z s hs).symm
  have h1 : x₀ = z := hd.hzZ x₀ hx₀T hx₀o fun y hy => hx₀c y (hTS hy)
  have h2 : g * x₀ * g⁻¹ = z := by
    refine hd.hzZ _ (mem_conjugate_iff.mp hx₀T') ?_ fun y hy => ?_
    · rw [show g * x₀ * g⁻¹ = MulAut.conj g x₀ from rfl, MulEquiv.orderOf_eq, hx₀o]
    · have hy' : g⁻¹ * y * g ∈ S := hT'S (by
        rw [mem_conjugate_iff, show g * (g⁻¹ * y * g) * g⁻¹ = y by group]
        exact hy)
      have h3 := hx₀c _ hy'
      calc g * x₀ * g⁻¹ * y = g * (x₀ * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * x₀) * g⁻¹ := by rw [h3]
        _ = y * (g * x₀ * g⁻¹) := by group
  apply hgz
  rw [h1] at h2
  rw [mem_centralizer_singleton_iff]
  calc g * z = g * z * g⁻¹ * g := by group
    _ = z * g := by rw [h2]

theorem le_normalizer_conjugate (h : FooteSec4 G L) (hFG : Foote47FourgroupGeneration)
    (c : Conf L M T S P t z) {g : G} (hgS : g ∈ normalizer (S : Set G))
    (hgz : g ∉ centralizer ({z} : Set G)) :
    M ≤ normalizer ((conjugate M g : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTS : T ≤ S := c.hT ▸ inf_le_left
  have hSg : conjugate S g = S := conjugate_eq_of_mem_normalizer hgS
  have hT'S : conjugate T g ≤ S := hSg ▸ map_mono hTS
  have hbot := c.inf_conjugate_eq_bot hgS hgz
  have hT'N : conjugate T g ≤ normalizer (M : Set G) := hT'S.trans c.hSN.le
  have hT'p : IsPGroup 2 (conjugate T g) := c.hTsyl.isPGroup.map _
  have hT'C : ∀ x ∈ conjugate T g, x ∈ coreActionKernel M → x = 1 := by
    intro x hx hxC
    have hxT : x ∈ T := by rw [c.hT]; exact mem_inf.mpr ⟨hT'S hx, hxC⟩
    have h1 : x ∈ T ⊓ conjugate T g := mem_inf.mpr ⟨hxT, hx⟩
    rw [hbot, mem_bot] at h1
    exact h1
  obtain ⟨E, hET, hE2, hE8⟩ := exists_card_eight_le_of_isSylowOf h c.hv.hM c.hTsyl
  have hE'T : conjugate E g ≤ conjugate T g := map_mono hET
  have hnab : ∃ x ∈ conjugate T g, ∃ y ∈ conjugate T g, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := c.exists_not_comm
    refine ⟨g⁻¹ * x * g, conj_mem_conjugate hx g, g⁻¹ * y * g, conj_mem_conjugate hy g,
      fun h1 => hxy ?_⟩
    have h2 : g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ =
        g * (g⁻¹ * y * g * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
    simpa [mul_assoc] using h2
  have hM' : IsFooteM L (conjugate M g) := isFooteM_conjugate h c.hv.hM g
  have hT'C' : conjugate T g ≤ coreActionKernel (conjugate M g) := by
    rw [coreActionKernel_conjugate]
    exact map_mono c.hTsyl.le
  refine le_of_forall_fourgroup_le h hFG c.hv.hM hT'N hT'p hT'C hE'T
    (sq_eq_one_of_mem_conjugate hE2 g) (by rw [card_conjugate_eq_card, hE8]) hnab
    fun W F hW hWF hFT hF2 hF8 => ?_
  refine inf_le_right.trans fun x hx => ?_
  exact foote_lemma_4_5_iii_four h hM' hW hF2 hF8 (hFT.trans hT'C') hWF
    (mem_normalizer_of_mem_centralizer hx)

theorem normalizer_le_centralizer_of_conf (h : FooteSec4 G L)
    (hA5 : GSThmB.AschbacherTheorem5Input) (hE8 : FooteL2FourgroupE8)
    (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts) (hcalc : FooteSmallCentralizers)
    (hFG : Foote47FourgroupGeneration) (c : Conf L M T S P t z) :
    normalizer (S : Set G) ≤ centralizer ({z} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hgS
  by_contra hgz
  have hTS : T ≤ S := c.hT ▸ inf_le_left
  have hSg : conjugate S g = S := conjugate_eq_of_mem_normalizer hgS
  have hgz' : g⁻¹ ∉ centralizer ({z} : Set G) := fun h1 => hgz (by simpa using inv_mem h1)
  have h1 := c.le_normalizer_conjugate h hFG hgS hgz
  have h2 := c.le_normalizer_conjugate h hFG (inv_mem hgS) hgz'
  have h3 : conjugate M g ≤ normalizer (M : Set G) := by
    have h4 : conjugate M g ≤ conjugate (normalizer ((conjugate M g⁻¹ : Subgroup G) : Set G)) g :=
      map_mono h2
    rwa [GSThmB.conjugate_normalizer, conjugate_conjugate, inv_mul_cancel, conjugate_one] at h4
  obtain ⟨E, hET, hE2, hE8'⟩ := exists_card_eight_le_of_isSylowOf h c.hv.hM c.hTsyl
  have hM' : IsFooteM L (conjugate M g) := isFooteM_conjugate h c.hv.hM g
  have hT'S : conjugate T g ≤ S := hSg ▸ map_mono hTS
  have hT'C' : conjugate T g ≤ coreActionKernel (conjugate M g) := by
    rw [coreActionKernel_conjugate]
    exact map_mono c.hTsyl.le
  have hSN' : S ≤ normalizer ((conjugate M g : Subgroup G) : Set G) := by
    rw [← hSg, ← GSThmB.conjugate_normalizer]
    exact map_mono c.hSN.le
  have heq := foote_theorem_4_6 h hA5 hE8 hK hcalc c.hv.hM hM'
    (commutator_le_inf_of_le_normalizer h1 h3) hE2 hE8'
    (le_inf (hET.trans c.hTsyl.le) (hET.trans (hTS.trans hSN')))
    (sq_eq_one_of_mem_conjugate hE2 g) (by rw [card_conjugate_eq_card, hE8'])
    (le_inf ((map_mono hET).trans hT'C') ((map_mono hET).trans (hT'S.trans c.hSN.le)))
  have hbot := c.inf_conjugate_eq_bot hgS hgz
  have hT'T : conjugate T g ≤ T := by
    intro x hx
    rw [c.hT]
    exact mem_inf.mpr ⟨hT'S hx, heq ▸ hT'C' hx⟩
  have hE'bot : conjugate E g ≤ ⊥ := by
    rw [← hbot]
    exact le_inf ((map_mono hET).trans hT'T) (map_mono hET)
  have h5 := card_conjugate_eq_card E g
  rw [le_bot_iff.mp hE'bot, card_bot, hE8'] at h5
  omega

end Conf

end CFSG.ComponentClassification.Foote47
