module

public import CFSG.LocalAnalysis.RankFourTheoremC.P5.Case2Comp
import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.GL83PartI.I_7_13

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.P5

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding
  CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

open scoped Pointwise

variable {p : ℕ} [hp : Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {x : Y} {K : Subgroup Y}

namespace Case2HypP

theorem exists_component_not_centralized (h : Case2HypP p Y x) {Z : Subgroup Y}
    (hZp : IsPGroup p Z) (hZ : ¬ Z ≤ CFSG.pCore p Y) :
    ∃ K : Subgroup Y, IsComponentOf K ⊤ ∧ ¬ Z ≤ centralizer (K : Set Y) := by
  by_contra hall
  push Not at hall
  apply hZ
  have hlay : CFSG.layer Y ≤ centralizer (Z : Set Y) := by
    show sSup {K : Subgroup Y | CFSG.IsComponent K} ≤ _
    exact sSup_le fun K hK =>
      le_centralizer_iff.mp (hall K ((CFSG.isComponent_iff_open K).mp hK))
  obtain ⟨R, hZR⟩ := hZp.exists_le_sylow
  have hpR : CFSG.pCore p Y ≤ (R : Subgroup Y) := CFSG.pCore_isPGroup.le_sylow_of_normal R
  have := h.abelian R
  have hpC : CFSG.pCore p Y ≤ centralizer (Z : Set Y) := fun a ha =>
    mem_centralizer_iff.mpr fun z hz => setLike_mul_comm (hZR hz) (hpR ha)
  have hF : CFSG.fittingSubgroup Y = CFSG.pCore p Y := CFSG.Fitting_eq_pcore Y p h.core_eq_bot
  have hFs : CFSG.generalizedFitting Y ≤ centralizer (Z : Set Y) := by
    rw [CFSG.generalizedFitting, hF]
    exact sup_le hpC hlay
  have hZF : Z ≤ CFSG.generalizedFitting Y :=
    (le_centralizer_iff.mp hFs).trans (CFSG.centralizer_generalizedFitting_le Y)
  intro z hz
  have hzF := hZF hz
  rw [CFSG.generalizedFitting, hF] at hzF
  have : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨a, ha, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hzF
  have haC : a ∈ centralizer (CFSG.layer Y : Set Y) := by
    have := commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.LocalCores.fitting_layer_commute (G := Y)) (hF ▸ ha)
    exact this
  have hzC : a * e ∈ centralizer (CFSG.layer Y : Set Y) := le_centralizer_iff.mp hlay hz
  have hec : e ∈ centralizer (CFSG.layer Y : Set Y) := by
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ haC) hzC
    simpa using this
  have hcenter : (center (CFSG.layer Y)).map (CFSG.layer Y).subtype = ⊥ := by
    rw [(CFSG.LocalCores.layer_center (G := Y)).1]
    refine le_bot_iff.mp (iSup_le fun K => ?_)
    rw [h.center_eq_bot ((CFSG.isComponent_iff_open K.1).mp K.2), Subgroup.map_bot]
  have he1 : e = 1 := by
    have : e ∈ (center (CFSG.layer Y)).map (CFSG.layer Y).subtype :=
      (CFSG.LocalCores.mem_map_center_iff (CFSG.layer Y)).mpr ⟨he, hec⟩
    rw [hcenter] at this
    exact mem_bot.mp this
  rw [he1, mul_one]
  exact ha

theorem exists_order_p (h : Case2HypP p Y x) (hK : IsComponentOf K ⊤) :
    ∃ t ∈ K, orderOf t = p ∧ t ∉ centralizer (K : Set Y) := by
  obtain ⟨R⟩ := (Sylow.nonempty : Nonempty (Sylow p Y))
  obtain ⟨t, htRK, hto, htC⟩ :=
    exists_mem_sylow_inf_component hp.out h.ne_two h.core_eq_bot R hK
  exact ⟨t, htRK.2, hto, htC⟩

theorem centralizes_of_le_centralizer (h : Case2HypP p Y x) {Z O : Subgroup Y}
    (hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (hZN : ∀ z ∈ Z, z ∈ normalizer (K : Set Y))
    (hO : ¬ p ∣ Nat.card O) (hZC : Z ≤ centralizer ({x} : Set Y))
    (hCO : centralizer ({x} : Set Y) ≤ normalizer (O : Set Y))
    (hCZO : centralizer ({x} : Set Y) ≤ normalizer ((Z ⊔ O : Subgroup Y) : Set Y))
    (hK : IsComponentOf K ⊤) (hKC : K ≤ centralizer ({x} : Set Y)) :
    Z ≤ centralizer (K : Set Y) := by
  set L : Subgroup Y := Z ⊔ O with hL
  have hZO : Z ≤ normalizer (O : Set Y) := fun z hz => hCO (hZC hz)
  have hLset : (L : Set Y) = (Z : Set Y) * (O : Set Y) :=
    coe_mul_of_left_le_normalizer_right Z O hZO
  have hZ := h.center_eq_bot hK
  obtain ⟨hsimple, hnonab⟩ := isSimpleGroup_of_isComponentOf_of_center_eq_bot hK hZ
  obtain ⟨t, htK, hto, -⟩ := h.exists_order_p hK
  have hpK : p ∣ Nat.card K := by
    have := orderOf_dvd_natCard (⟨t, htK⟩ : K)
    rwa [Subgroup.orderOf_mk, hto] at this
  have hcomm : ∀ a ∈ L, ∀ b ∈ L, a * b * a⁻¹ * b⁻¹ ∈ O := by
    intro a ha b hb
    rw [← SetLike.mem_coe, hLset] at ha hb
    obtain ⟨z₁, hz₁, o₁, ho₁, rfl⟩ := ha
    obtain ⟨z₂, hz₂, o₂, ho₂, rfl⟩ := hb
    have hzz : z₁ * z₂ = z₂ * z₁ := hZab z₁ hz₁ z₂ hz₂
    have ho₁' : z₂⁻¹ * o₁ * z₂ ∈ O := by
      have := (mem_normalizer_iff.mp (hZO (Z.inv_mem hz₂)) o₁).mp ho₁
      simpa using this
    have ho₂' : z₁⁻¹ * o₂ * z₁ ∈ O := by
      have := (mem_normalizer_iff.mp (hZO (Z.inv_mem hz₁)) o₂).mp ho₂
      simpa using this
    have e1 : (z₁ * o₁) * (z₂ * o₂) = (z₁ * z₂) * ((z₂⁻¹ * o₁ * z₂) * o₂) := by group
    have e2 : (z₂ * o₂) * (z₁ * o₁) = (z₁ * z₂) * ((z₁⁻¹ * o₂ * z₁) * o₁) := by
      calc (z₂ * o₂) * (z₁ * o₁) = (z₂ * z₁) * ((z₁⁻¹ * o₂ * z₁) * o₁) := by group
        _ = (z₁ * z₂) * ((z₁⁻¹ * o₂ * z₁) * o₁) := by rw [hzz]
    have e3 : z₁ * o₁ * (z₂ * o₂) * (z₁ * o₁)⁻¹ * (z₂ * o₂)⁻¹ =
        ((z₁ * o₁) * (z₂ * o₂)) * ((z₂ * o₂) * (z₁ * o₁))⁻¹ := by group
    have e4 : (z₁ * z₂) * ((z₂⁻¹ * o₁ * z₂) * o₂) * ((z₁ * z₂) * ((z₁⁻¹ * o₂ * z₁) * o₁))⁻¹ =
        (z₁ * z₂) * (((z₂⁻¹ * o₁ * z₂) * o₂) * ((z₁⁻¹ * o₂ * z₁) * o₁)⁻¹) * (z₁ * z₂)⁻¹ := by
      group
    rw [e3, e1, e2, e4]
    exact (mem_normalizer_iff.mp (hZO (Z.mul_mem hz₁ hz₂)) _).mp
      (O.mul_mem (O.mul_mem ho₁' ho₂) (O.inv_mem (O.mul_mem ho₂' ho₁)))
  have hKL : ¬ K ≤ L := by
    intro hKL
    have hperf : (⊤ : Subgroup K) ≤ O.subgroupOf K := by
      rw [← hK.2.2.1]
      show ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ _
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [mem_subgroupOf, commutatorElement_def]
      exact hcomm _ (hKL g₁.2) _ (hKL g₂.2)
    have hKO : K ≤ O := fun k hk => hperf (mem_top (⟨k, hk⟩ : K))
    exact hO (hpK.trans (Subgroup.card_dvd_of_le hKO))
  have hnorm : ((K ⊓ L).subgroupOf K).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    refine ⟨K.mul_mem (K.mul_mem g.2 hn.1) (K.inv_mem g.2), ?_⟩
    exact (mem_normalizer_iff.mp (hCZO (hKC g.2)) n).mp hn.2⟩
  have hbot : (K ⊓ L).subgroupOf K = ⊥ := by
    have := hsimple
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ L).subgroupOf K) with h1 | h1
    · exact h1
    · exfalso
      apply hKL
      intro k hk
      have : (⟨k, hk⟩ : K) ∈ (K ⊓ L).subgroupOf K := by
        rw [h1]
        exact mem_top _
      exact (mem_subgroupOf.mp this).2
  intro z hz
  rw [mem_centralizer_iff]
  intro k hk
  have hcK : z * k * z⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem ((mem_normalizer_iff.mp (hZN z hz) k).mp hk) (K.inv_mem hk)
  have hcL : z * k * z⁻¹ * k⁻¹ ∈ L := by
    have h1 := (mem_normalizer_iff.mp (hCZO (hKC hk)) z⁻¹).mp (mem_sup_left (Z.inv_mem hz))
    have h2 : z * k * z⁻¹ * k⁻¹ = z * (k * z⁻¹ * k⁻¹) := by group
    rw [h2]
    exact L.mul_mem (mem_sup_left hz) h1
  have h3 : (⟨z * k * z⁻¹ * k⁻¹, hcK⟩ : K) ∈ (K ⊓ L).subgroupOf K :=
    mem_subgroupOf.mpr ⟨hcK, hcL⟩
  rw [hbot, mem_bot] at h3
  have h4 : z * k * z⁻¹ * k⁻¹ = 1 := congrArg Subtype.val h3
  exact ((commutatorElement_eq_one_iff_mul_comm (g₁ := z) (g₂ := k)).mp h4).symm

end Case2HypP

structure Case2DataP (p : ℕ) [Fact p.Prime] (Y : Type) [Group Y] [Finite Y] (x : Y)
    (Z : Subgroup Y) (S : Set Y) (O : Subgroup Y) : Prop where
  base : Case2HypP p Y x
  isElemAbelian : IsElemAbelian p Z
  card_eq : ∃ n : ℕ, 3 ≤ n ∧ Nat.card Z = p ^ n
  le_centralizer : Z ≤ centralizer ({x} : Set Y)
  centralizes : ∀ s ∈ S, s * x * s⁻¹ = x
  normalizes : ∀ s ∈ S, ∀ z ∈ Z, s * z * s⁻¹ ∈ Z
  irreducible : ∀ D : Subgroup Y, D ≤ Z → (∀ s ∈ S, ∀ d ∈ D, s * d * s⁻¹ ∈ D) → D = ⊥ ∨ D = Z
  coprime : ¬ p ∣ Nat.card O
  normalizes_O : centralizer ({x} : Set Y) ≤ normalizer (O : Set Y)
  normalizes_ZO : centralizer ({x} : Set Y) ≤ normalizer ((Z ⊔ O : Subgroup Y) : Set Y)

theorem Case2DataP.le_pCore {Z : Subgroup Y} {S : Set Y} {O : Subgroup Y}
    (hd : Case2DataP p Y x Z S O) (hInn : KFactInnerAction) (hWC : KFactWeakClosure)
    (h713 : GL83.I_7_13_1) : Z ≤ CFSG.pCore p Y := by
  by_contra hZ
  have hZcomm : IsMulCommutative Z := hd.isElemAbelian.1
  have hZab : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb => setLike_mul_comm ha hb
  have hZp : IsPGroup p Z := elementary_isPGroup p Z hd.isElemAbelian
  obtain ⟨K, hK, hZK⟩ := hd.base.exists_component_not_centralized hZp hZ
  have hZN : ∀ z ∈ Z, z ∈ normalizer (K : Set Y) := fun z hz =>
    hd.base.mem_normalizer_of_pow_p hK (hd.isElemAbelian.2 z hz)
  have hxN : x ∈ normalizer (K : Set Y) :=
    hd.base.mem_normalizer_of_pow_p hK hd.base.pow_eq_one
  have hxC : x ∉ centralizer (K : Set Y) := by
    intro hxC
    refine hZK (hd.base.centralizes_of_le_centralizer hZab hZN hd.coprime hd.le_centralizer
      hd.normalizes_O hd.normalizes_ZO hK fun k hk => ?_)
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxC k hk)
  obtain ⟨hxK, hrank⟩ := hd.base.mem_and_pRank_le_one hInn hWC hK hxN hxC
  have hSN : ∀ s ∈ S, s ∈ normalizer (K : Set Y) := fun s hs =>
    hd.base.mem_normalizer_of_mem hK hxK (hd.centralizes s hs)
  obtain ⟨hsimple, hnonab⟩ :=
    isSimpleGroup_of_isComponentOf_of_center_eq_bot hK (hd.base.center_eq_bot hK)
  have hcat := hd.base.catalog.simple_subgroup K hsimple hnonab
  have hinv : ∀ s ∈ S, ∀ d ∈ Z ⊓ centralizer (K : Set Y),
      s * d * s⁻¹ ∈ Z ⊓ centralizer (K : Set Y) := by
    intro s hs d hdd
    refine ⟨hd.normalizes s hs d hdd.1, mem_centralizer_iff.mpr fun k hk => ?_⟩
    have hk' : s⁻¹ * k * s ∈ K := by
      have := (mem_normalizer_iff.mp (Subgroup.inv_mem _ (hSN s hs)) k).mp hk
      simpa using this
    have h1 := mem_centralizer_iff.mp hdd.2 _ hk'
    calc k * (s * d * s⁻¹) = s * ((s⁻¹ * k * s) * d) * s⁻¹ := by group
      _ = s * (d * (s⁻¹ * k * s)) * s⁻¹ := by rw [h1]
      _ = s * d * s⁻¹ * k := by group
  rcases hd.irreducible (Z ⊓ centralizer (K : Set Y)) inf_le_left hinv with hD | hD
  swap
  · exact hZK (inf_eq_left.mp hD)
  let α : Z →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion fun z hz => hZN z hz)
  have hinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have hu' : (u : Y) ∈ Z ⊓ centralizer (K : Set Y) := ⟨u.2, mem_centralizer_iff.mpr fun k hk => by
      have h1 := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : Y)) (MonoidHom.mem_ker.mp hu)
      change (u : Y) * k * (u : Y)⁻¹ = k at h1
      calc k * (u : Y) = (u : Y) * k * (u : Y)⁻¹ * (u : Y) := by rw [h1]
        _ = (u : Y) * k := by group⟩
    rw [hD, mem_bot] at hu'
    exact mem_bot.mpr (Subtype.ext hu')
  obtain ⟨n, hn3, hcardZ⟩ := hd.card_eq
  have hE : IsElemAbelian p α.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨a', ha'⟩ := a.2
      obtain ⟨b', hb'⟩ := b.2
      apply Subtype.ext
      show (a : MulAut K) * b = b * a
      rw [← ha', ← hb', ← map_mul, ← map_mul]
      exact congrArg α (Subtype.ext (hZab _ a'.2 _ b'.2))
    · rintro _ ⟨a', rfl⟩
      rw [← map_pow]
      have : a' ^ p = 1 := Subtype.ext (by simpa using hd.isElemAbelian.2 a' a'.2)
      rw [this, map_one]
  have hcard : Nat.card α.range = p ^ n :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hcardZ
  have hge : n ≤ CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) :=
    le_csSup (CFSG.PreuniquenessRankFour.Helpers.pRank_bddAbove p hp.out _)
      ⟨α.range, le_top, hE, hcard⟩
  have hle := (h713 p hp.out hd.base.ne_two K hsimple hnonab hcat hrank).2
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.P5
