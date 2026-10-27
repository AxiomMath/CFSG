module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28ClosedBase
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x k : Y} {K₁ K₂ : Subgroup Y}

structure TwoData (P K₁ K₂ : Subgroup Y) : Prop where
  hs : CompSetting P
  c₁ : IsComponentOf K₁ ⊤
  c₂ : IsComponentOf K₂ ⊤
  ne : K₁ ≠ K₂
  all : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = K₁ ∨ K = K₂

theorem CompSetting.three_dvd (hs : CompSetting P) {K : Subgroup Y} (hK : IsComponentOf K ⊤) :
    3 ∣ Nat.card K := by
  obtain ⟨t, ht, hto, -⟩ := hs.exists_t hK
  have hord : orderOf (⟨t, ht.2⟩ : K) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hto
  exact hord ▸ _root_.orderOf_dvd_natCard _

theorem mem_sup_prod {A B : Subgroup Y} (hAB : A ≤ normalizer (B : Set Y)) {w : Y}
    (hw : w ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = w := by
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right A B hAB
  have : w ∈ (A : Set Y) * (B : Set Y) := by
    rw [← hset]
    exact hw
  obtain ⟨a, ha, b, hb, hab⟩ := this
  exact ⟨a, ha, b, hb, hab⟩

namespace TwoData

variable (htw : TwoData P K₁ K₂)

include htw

theorem symm : TwoData P K₂ K₁ :=
  ⟨htw.hs, htw.c₂, htw.c₁, htw.ne.symm, fun K hK => (htw.all K hK).symm⟩

theorem le_cent : K₁ ≤ centralizer (K₂ : Set Y) :=
  CompSetting.comp_le_centralizer htw.c₁ htw.c₂ htw.ne

theorem inf_bot : K₁ ⊓ K₂ = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hZ : (⟨y, hy.1⟩ : K₁) ∈ center K₁ := Subgroup.mem_center_iff.mpr fun g =>
    Subtype.ext (mem_centralizer_iff.mp (htw.symm.le_cent hy.2) g g.2)
  rw [htw.hs.center_bot htw.c₁, mem_bot] at hZ
  exact mem_bot.mpr (congrArg Subtype.val hZ)

theorem prod_unique {a c b d : Y} (ha : a ∈ K₁) (hc : c ∈ K₁) (hb : b ∈ K₂) (hd : d ∈ K₂)
    (h : a * b = c * d) : a = c ∧ b = d := by
  have h1 : c⁻¹ * a = d * b⁻¹ :=
    calc c⁻¹ * a = c⁻¹ * (a * b) * b⁻¹ := by group
      _ = c⁻¹ * (c * d) * b⁻¹ := by rw [h]
      _ = d * b⁻¹ := by group
  have hmem : c⁻¹ * a ∈ K₁ ⊓ K₂ :=
    ⟨K₁.mul_mem (K₁.inv_mem hc) ha, h1 ▸ K₂.mul_mem hd (K₂.inv_mem hb)⟩
  rw [htw.inf_bot, mem_bot] at hmem
  have hac : a = c := (inv_mul_eq_one.mp hmem).symm
  exact ⟨hac, mul_left_cancel (a := a) (by rw [h, hac])⟩

theorem conj_comp (g : Y) :
    K₁.map (MulAut.conj g).toMonoidHom = K₁ ∨ K₁.map (MulAut.conj g).toMonoidHom = K₂ :=
  htw.all _ ((CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) K₁).mpr
    htw.c₁)

theorem swap_of_ne {g : Y} (hg : K₁.map (MulAut.conj g).toMonoidHom ≠ K₁) :
    K₁.map (MulAut.conj g).toMonoidHom = K₂ ∧ K₂.map (MulAut.conj g).toMonoidHom = K₁ := by
  have h1 : K₁.map (MulAut.conj g).toMonoidHom = K₂ := (htw.conj_comp g).resolve_left hg
  refine ⟨h1, ?_⟩
  rcases htw.symm.conj_comp g with h2 | h2
  · exact absurd (map_injective (MulAut.conj g).injective (h1.trans h2.symm)) htw.ne
  · exact h2

theorem map_conj_of_mem {g : Y} (hg : K₁.map (MulAut.conj g).toMonoidHom = K₁) :
    K₂.map (MulAut.conj g).toMonoidHom = K₂ := by
  rcases htw.symm.conj_comp g with h2 | h2
  · exact h2
  · exact absurd (map_injective (MulAut.conj g).injective (hg.trans h2.symm)) htw.ne

theorem normal_normalizer : (normalizer (K₁ : Set Y)).Normal := by
  refine ⟨fun y hy g => ?_⟩
  have hy' : K₁.map (MulAut.conj y).toMonoidHom = K₁ := mem_normalizer_iff_map_conj_eq.mp hy
  have hy2 := htw.map_conj_of_mem hy'
  refine mem_normalizer_iff_map_conj_eq.mpr ?_
  show K₁.map (MulAut.conj (g * y * g⁻¹)).toMonoidHom = K₁
  have hK : ∀ K, IsComponentOf K ⊤ → K.map (MulAut.conj y).toMonoidHom = K := fun K hK =>
    (htw.all K hK).elim (fun h => h ▸ hy') (fun h => h ▸ hy2)
  have hc : IsComponentOf (K₁.map (MulAut.conj g⁻¹).toMonoidHom) ⊤ :=
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g⁻¹) K₁).mpr htw.c₁
  rw [CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul,
    CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, hK _ hc, Subgroup.map_map]
  have : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id Y := by
    ext z
    simp [MulAut.conj_apply]
    group
  rw [this, Subgroup.map_id]

theorem exists_normalizer_swap {ι : Y} (hι : K₁.map (MulAut.conj ι).toMonoidHom = K₂) :
    ∃ t ∈ normalizer (P : Set Y), K₁.map (MulAut.conj t).toMonoidHom = K₂ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := htw.normal_normalizer
  set D : Subgroup Y := normalizer (K₁ : Set Y) with hD
  have hPD : P ≤ D := htw.hs.normalizes htw.c₁
  set P' : Subgroup Y := P.map (MulAut.conj ι).toMonoidHom with hP'
  have hP'D : P' ≤ D := by
    rintro _ ⟨g, hg, rfl⟩
    exact (inferInstance : D.Normal).conj_mem g (hPD hg) ι
  have hSyl : IsSylowOf 3 P' ⊤ := by
    obtain ⟨-, hp, hidx⟩ := isSylowOf_iff.mp htw.hs.sylow
    refine isSylowOf_iff.mpr ⟨le_top, hp.map _, ?_⟩
    rw [Subgroup.relIndex_top_right] at hidx ⊢
    have hi : (P.map ((MulAut.conj ι : MulAut Y) : Y →* Y)).index = P.index :=
      Subgroup.index_map_equiv P (MulAut.conj ι)
    exact fun h3 => hidx (hi ▸ h3)
  obtain ⟨d, hdD, hd⟩ := IsSylowOf.exists_mem_conj (htw.hs.sylow.of_le hPD le_top)
    (hSyl.of_le hP'D le_top)
  have hdm : ∀ y : Y, y ∈ P' ↔ ι⁻¹ * y * ι ∈ P := fun y => by
    rw [hP', Subgroup.mem_map_equiv]
    simp [MulAut.conj_apply]
  refine ⟨d⁻¹ * ι, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    have h1 := hd (ι * y * ι⁻¹)
    rw [hdm] at h1
    have e1 : ι⁻¹ * (ι * y * ι⁻¹) * ι = y := by group
    have e2 : d⁻¹ * (ι * y * ι⁻¹) * d = d⁻¹ * ι * y * (d⁻¹ * ι)⁻¹ := by group
    rw [e1, e2] at h1
    exact h1
  · rw [CFSG.RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, hι]
    exact htw.map_conj_of_mem (mem_normalizer_iff_map_conj_eq.mp (D.inv_mem hdD))

end TwoData

theorem zpowers_comm {a b : Y} (h : a * b = b * a) :
    ∀ u ∈ zpowers a, ∀ v ∈ zpowers b, u * v = v * u := by
  intro u hu v hv
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hv
  exact (Commute.zpow_zpow (show Commute a b from h) i j).eq

theorem mem_of_map_eq {K : Subgroup Y} {g : Y} (h : K.map (MulAut.conj g).toMonoidHom = K)
    {y : Y} (hy : y ∈ K) : g * y * g⁻¹ ∈ K := by
  rw [← h]
  exact ⟨y, hy, rfl⟩

namespace TwoData

variable (htw : TwoData P K₁ K₂)

include htw

theorem exists_Z (hz : Nat.card (L28Z P) = 3 ^ 2) :
    ∃ z₁ z₂ : Y, z₁ ∈ P ⊓ K₁ ∧ z₂ ∈ P ⊓ K₂ ∧ z₁ ≠ 1 ∧ z₂ ≠ 1 ∧ z₁ ^ 3 = 1 ∧ z₂ ^ 3 = 1 ∧
      L28Z P = zpowers z₁ ⊔ zpowers z₂ := by
  obtain ⟨z₁, hz₁, hz₁1, hz₁3, hz₁c, -⟩ := htw.hs.exists_central htw.c₁
  obtain ⟨z₂, hz₂, hz₂1, hz₂3, hz₂c, -⟩ := htw.hs.exists_central htw.c₂
  refine ⟨z₁, z₂, hz₁, hz₂, hz₁1, hz₂1, hz₁3, hz₂3, ?_⟩
  have hz₂n : z₂ ∉ zpowers z₁ := by
    intro h
    have : z₂ ∈ K₁ ⊓ K₂ := ⟨(zpowers_le.mpr hz₁.2) h, hz₂.2⟩
    rw [htw.inf_bot, mem_bot] at this
    exact hz₂1 this
  have hcomm : z₁ * z₂ = z₂ * z₁ := (hz₁c z₂ hz₂.1).symm
  have hle : zpowers z₁ ⊔ zpowers z₂ ≤ L28Z P := sup_le
    (zpowers_le.mpr (GL83P3L28Aux.mem_L28Z_iff.mpr ⟨hz₁.1, hz₁c⟩))
    (zpowers_le.mpr (GL83P3L28Aux.mem_L28Z_iff.mpr ⟨hz₂.1, hz₂c⟩))
  have hcard : Nat.card (zpowers z₁ ⊔ zpowers z₂ : Subgroup Y) = 3 ^ 2 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three (zpowers z₁) hz₂3 hz₂n
      (fun e he => zpowers_comm hcomm e he z₂ (mem_zpowers z₂)), Nat.card_zpowers,
      orderOf_eq_prime hz₁3 hz₁1]
    norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hz, hcard])).symm

end TwoData

namespace ClosedData

variable (hd : ClosedData P x k) (htw : TwoData P K₁ K₂)

include hd htw

theorem x_not_mem_left : x ∉ K₁ := by
  intro hx
  refine hd.solv K₂ (htw.hs.simple htw.c₂).1 (htw.hs.simple htw.c₂).2
    (htw.hs.three_dvd htw.c₂) ?_
  intro y hy
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp (htw.symm.le_cent hy) x hx).symm

theorem x_not_mem_right : x ∉ K₂ := hd.x_not_mem_left htw.symm

theorem iota_swaps {ι : Y} (hιx : ι * x * ι⁻¹ = x) (hικ : ι * k ^ 3 * ι⁻¹ = (k ^ 3)⁻¹) :
    K₁.map (MulAut.conj ι).toMonoidHom = K₂ := by
  by_contra hne
  have h1 := (htw.conj_comp ι).resolve_right hne
  have h2 := htw.map_conj_of_mem h1
  have hm1 : ∀ y ∈ K₁, ι * y * ι⁻¹ ∈ K₁ := fun y hy => mem_of_map_eq h1 hy
  have hm2 : ∀ y ∈ K₂, ι * y * ι⁻¹ ∈ K₂ := fun y hy => mem_of_map_eq h2 hy
  obtain ⟨z₁, z₂, hz₁, hz₂, hz₁1, hz₂1, hz₁3, hz₂3, hV⟩ := htw.exists_Z hd.z_card
  have hcomm : z₁ * z₂ = z₂ * z₁ := by
    have hc := htw.le_cent hz₁.2
    exact (mem_centralizer_iff.mp hc z₂ hz₂.2).symm
  have hn : zpowers z₁ ≤ normalizer (zpowers z₂ : Set Y) :=
    GL83P3L28Aux.le_normalizer_of_comm (zpowers_comm hcomm)
  have hz1K : zpowers z₁ ≤ K₁ := zpowers_le.mpr hz₁.2
  have hz2K : zpowers z₂ ≤ K₂ := zpowers_le.mpr hz₂.2
  obtain ⟨w₁, hw₁, w₂, hw₂, hxw⟩ := mem_sup_prod hn (hV ▸ hd.x_mem)
  have hfix : ι * w₁ * ι⁻¹ = w₁ ∧ ι * w₂ * ι⁻¹ = w₂ := by
    refine htw.prod_unique (hm1 w₁ (hz1K hw₁)) (hz1K hw₁) (hm2 w₂ (hz2K hw₂)) (hz2K hw₂) ?_
    calc ι * w₁ * ι⁻¹ * (ι * w₂ * ι⁻¹) = ι * (w₁ * w₂) * ι⁻¹ := by group
      _ = ι * x * ι⁻¹ := by rw [hxw]
      _ = x := hιx
      _ = w₁ * w₂ := hxw.symm
  have hw₁1 : w₁ ≠ 1 := by
    intro h
    rw [h, one_mul] at hxw
    exact hd.x_not_mem_right htw (hxw ▸ hz2K hw₂)
  have hw₂1 : w₂ ≠ 1 := by
    intro h
    rw [h, mul_one] at hxw
    exact hd.x_not_mem_left htw (hxw ▸ hz1K hw₁)
  have hzfix1 : ι * z₁ * ι⁻¹ = z₁ := by
    rcases GL83P3L28Aux.zpowers_three_cases hz₁3 hz₁1 hw₁ hw₁1 with h | h
    · rw [← h]; exact hfix.1
    · have := hfix.1
      rw [h] at this
      have h' : ι * z₁⁻¹ * ι⁻¹ = z₁⁻¹ := this
      have e : (ι * z₁ * ι⁻¹)⁻¹ = ι * z₁⁻¹ * ι⁻¹ := by group
      exact inv_injective (e.trans h')
  have hzfix2 : ι * z₂ * ι⁻¹ = z₂ := by
    rcases GL83P3L28Aux.zpowers_three_cases hz₂3 hz₂1 hw₂ hw₂1 with h | h
    · rw [← h]; exact hfix.2
    · have := hfix.2
      rw [h] at this
      have h' : ι * z₂⁻¹ * ι⁻¹ = z₂⁻¹ := this
      have e : (ι * z₂ * ι⁻¹)⁻¹ = ι * z₂⁻¹ * ι⁻¹ := by group
      exact inv_injective (e.trans h')
  have hfixpow : ∀ (z : Y), ι * z * ι⁻¹ = z → ∀ u ∈ zpowers z, ι * u * ι⁻¹ = u := by
    intro z hz u hu
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
    rw [← conj_zpow, hz]
  obtain ⟨u₁, hu₁, u₂, hu₂, hκ⟩ := mem_sup_prod hn (hV ▸ hd.k_cube)
  have hκfix : ι * k ^ 3 * ι⁻¹ = k ^ 3 := by
    rw [← hκ]
    calc ι * (u₁ * u₂) * ι⁻¹ = (ι * u₁ * ι⁻¹) * (ι * u₂ * ι⁻¹) := by group
      _ = u₁ * u₂ := by rw [hfixpow z₁ hzfix1 u₁ hu₁, hfixpow z₂ hzfix2 u₂ hu₂]
  rw [hικ] at hκfix
  have hk3 : k ^ 3 ≠ 1 := fun h => by
    have := orderOf_le_of_pow_eq_one (by norm_num) h
    rw [hd.k_order] at this
    omega
  have hsq : (k ^ 3) ^ 2 = 1 := by
    have : (k ^ 3)⁻¹ = k ^ 3 := hκfix
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr this.symm
  have hcube : (k ^ 3) ^ 3 = 1 := by
    rw [← pow_mul]
    have : k ^ 9 = 1 := hd.k_order ▸ pow_orderOf_eq_one k
    exact this
  apply hk3
  calc k ^ 3 = (k ^ 3) ^ 3 * ((k ^ 3) ^ 2)⁻¹ := by group
    _ = 1 := by rw [hcube, hsq]; group

end ClosedData

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3L28Cl
