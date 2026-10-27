module

public import CFSG.CGT.Timmesfeld75.Config
public import CFSG.CGT.Timmesfeld75.StrongClosure
public import CFSG.CGT.Timmesfeld75.NormalClosure
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G] {T T₁ : Subgroup G}

private theorem isElemAbelian_map {H : Type*} [Group H] {S : Subgroup G}
    (hS : IsElemAbelian 2 S) (f : G →* H) : IsElemAbelian 2 (S.map f) :=
  CFSG.Open.IsElemAbelian.map hS _

private theorem Cfg.not_mem_cfgM_of_not_mem_normIn (c : Cfg T T₁) {a : G} (ha : a ∈ T)
    (haL : a ∉ normIn T T₁) : a ∉ cfgM T T₁ := fun h =>
  haL (by rw [← c.inf_cfgM]; exact ⟨ha, h⟩)

theorem Cfg.of_conj [Finite G] (hT : IsWC T) {g : G} (hne : conjSubgroup g T ≠ T)
    (hL : normIn T (conjSubgroup g T) ≠ ⊥) : Cfg T (conjSubgroup g T) := by
  have hwc₁ : IsWC (conjSubgroup g T) := hT.conj g
  refine ⟨hT, hwc₁, hT.inf_conj_eq_bot hne, hL, ?_⟩
  obtain ⟨⟨x, hxL⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hL
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  obtain ⟨hxT, hxN⟩ := mem_normIn.1 hxL
  have hnc : ¬ conjSubgroup g T ≤ Subgroup.centralizer ({x} : Set G) := fun hle =>
    hne ((hT.2 x hxT hx1').2 g hle)
  obtain ⟨y, hyT₁, hy⟩ := IsConcreteLE.not_le_iff_exists.1 hnc
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  have hxi : x⁻¹ = x := elemAbelian_inv hT.1 hxT
  have hyi : y⁻¹ = y := elemAbelian_inv hwc₁.1 hyT₁
  have hwT₁ : ⁅x, y⁆ ∈ conjSubgroup g T := comm_mem_of_mem_normalizer hxN hyT₁
  have hw2 : ⁅x, y⁆ * ⁅x, y⁆ = 1 := elemAbelian_mul_self hwc₁.1 hwT₁
  have hxw : x * ⁅x, y⁆ = ⁅x, y⁆ * x := (comm_commute_of_sq hxi hyi hw2).2
  have hw1 : ⁅x, y⁆ ≠ 1 := fun h => hy (commutatorElement_eq_one_iff_mul_comm.1 h).symm
  have hwN : ⁅x, y⁆ ∈ Subgroup.normalizer (T : Set G) :=
    hT.centralizer_le_normalizer hxT hx1'
      (Subgroup.mem_centralizer_singleton_iff.2 hxw.symm)
  exact Subgroup.ne_bot_iff_exists_ne_one.2
    ⟨⟨⁅x, y⁆, mem_normIn.2 ⟨hwT₁, hwN⟩⟩, fun h => hw1 (congrArg Subtype.val h)⟩

theorem Cfg.normal_cfgM (c : Cfg T T₁) (hX : T ⊔ T₁ = ⊤) : (cfgM T T₁).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  have h := c.le_normalizer_cfgM
  rwa [hX] at h

theorem Cfg.normIn_lt [Finite G] (c : Cfg T T₁) (hconj : ∃ x : G, T₁ = conjSubgroup x T) :
    normIn T T₁ < T := by
  refine lt_of_le_of_ne (normIn_le T T₁) fun hLT => ?_
  obtain ⟨x, hx⟩ := hconj
  obtain ⟨⟨y, hyL⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 c.ne₁
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  obtain ⟨hyT₁, hyN⟩ := mem_normIn.1 hyL
  have hTC : T ≤ Subgroup.centralizer ({y} : Set G) := by
    intro t ht
    have htL : t ∈ normIn T T₁ := by rw [hLT]; exact ht
    have htN : t ∈ Subgroup.normalizer (T₁ : Set G) := (mem_normIn.1 htL).2
    have h1 : ⁅t, y⁆ ∈ T₁ := comm_mem_of_mem_normalizer htN hyT₁
    have h2 : ⁅t, y⁆ ∈ T := by
      rw [← commutatorElement_inv]
      exact T.inv_mem (comm_mem_of_mem_normalizer hyN ht)
    have h3 : ⁅t, y⁆ ∈ T ⊓ T₁ := ⟨h2, h1⟩
    rw [c.inf, Subgroup.mem_bot] at h3
    exact Subgroup.mem_centralizer_singleton_iff.2 (commutatorElement_eq_one_iff_mul_comm.1 h3)
  have hT₁ : conjSubgroup x⁻¹ T₁ = T := by
    rw [hx, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hTT₁ : T = T₁ := by
    have := (c.wc₁.2 y hyT₁ hy1').2 x⁻¹ (by rw [hT₁]; exact hTC)
    rwa [hT₁] at this
  have hbot : T = ⊥ := by
    have h := c.inf
    rwa [← hTT₁, inf_idem] at h
  exact c.ne (le_bot_iff.1 ((normIn_le T T₁).trans hbot.le))

theorem Cfg.odd_orderOf_mul [Finite G] (c : Cfg T T₁) (hX : T ⊔ T₁ = ⊤)
    (hconj : ∃ x : G, T₁ = conjSubgroup x T) {a b : G} (ha : a ∈ T)
    (haL : a ∉ normIn T T₁) (hb : b ∈ T₁) (hbL : b ∉ normIn T₁ T) :
    Odd (orderOf (a * b)) := by
  rcases Nat.even_or_odd (orderOf (a * b)) with ⟨m, hm⟩ | hodd
  swap
  · exact hodd
  exfalso
  have hmemX : ∀ h : G, h ∈ T ⊔ T₁ := fun h => by rw [hX]; exact Subgroup.mem_top h
  have haa : a * a = 1 := elemAbelian_mul_self c.wc.1 ha
  have hbb : b * b = 1 := elemAbelian_mul_self c.wc₁.1 hb
  have hm0 : 0 < m := by
    have := orderOf_pos (a * b)
    omega
  have hord : orderOf (b * a) = 2 * m := by
    have h1 : b * a = (a * b)⁻¹ := by
      rw [mul_inv_rev, elemAbelian_inv c.wc.1 ha, elemAbelian_inv c.wc₁.1 hb]
    rw [h1, orderOf_inv]
    omega
  obtain ⟨z, -, hz1, hbz, haz, hconjz⟩ := dihedral_central_of_even_order hbb haa hm0 hord
  have haM : a ∉ cfgM T T₁ := c.not_mem_cfgM_of_not_mem_normIn ha haL
  have hstar : ∀ t ∈ T, t ∉ normIn T T₁ → ∀ h : G, a * z = h⁻¹ * t * h → a * z ∈ T := by
    intro t ht htL h hh
    have hc : a * z * a = a * (a * z) :=
      calc a * z * a = a * (z * a) := mul_assoc _ _ _
        _ = a * (a * z) := by rw [haz]
    have hcomm : ⁅h⁻¹ * t * h, a⁆ ∈ cfgM T T₁ := by
      rw [← hh, commutatorElement_eq_one_iff_mul_comm.2 hc]
      exact (cfgM T T₁).one_mem
    have := c.strongly_closed_star ha haM (hmemX h) ht htL hcomm
    rwa [← hh] at this
  have hazT : a * z ∈ T := by
    rcases hconjz with ⟨g, hg⟩ | ⟨g, hg⟩
    · obtain ⟨x, hx⟩ := hconj
      have hb' : b ∈ conjSubgroup x T := by rw [← hx]; exact hb
      have hbT : x⁻¹ * b * x ∈ T := mem_conjSubgroup.1 hb'
      have htL : x⁻¹ * b * x ∉ normIn T T₁ := by
        intro hL
        have hM : x⁻¹ * b * x ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_left T T₁ hL
        have hM' := c.conj_mem_cfgM (hmemX x) hM
        have e : x * (x⁻¹ * b * x) * x⁻¹ = b := by group
        rw [e] at hM'
        exact hbL (by rw [← c.inf_cfgM_right]; exact ⟨hb, hM'⟩)
      exact hstar (x⁻¹ * b * x) hbT htL (x⁻¹ * g) (by rw [hg]; group)
    · exact hstar a ha haL g hg
  have hzT : z ∈ T := by
    have := T.mul_mem ha hazT
    rwa [← mul_assoc, haa, one_mul] at this
  have hbN : b ∈ Subgroup.normalizer (T : Set G) :=
    c.wc.centralizer_le_normalizer hzT hz1 (Subgroup.mem_centralizer_singleton_iff.2 hbz)
  exact hbL (mem_normIn.2 ⟨hb, hbN⟩)

theorem Cfg.strongWC_map [Finite G] (c : Cfg T T₁) (hX : T ⊔ T₁ = ⊤)
    [(cfgM T T₁).Normal] : StrongWC (T.map (QuotientGroup.mk' (cfgM T T₁))) := by
  refine ⟨isElemAbelian_map c.wc.1 _, ?_⟩
  intro t' ht' ht'1 a' ha' g' hg'
  obtain ⟨t, ht, rfl⟩ := ht'
  obtain ⟨a, ha, rfl⟩ := ha'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g'
  have e : (↑g : G ⧸ cfgM T T₁)⁻¹ * QuotientGroup.mk' (cfgM T T₁) a * ↑g =
      QuotientGroup.mk' (cfgM T T₁) (g⁻¹ * a * g) := by
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [e] at hg' ⊢
  rw [Subgroup.mem_centralizer_singleton_iff] at hg'
  have htM : t ∉ cfgM T T₁ := fun h => ht'1 ((QuotientGroup.eq_one_iff t).2 h)
  by_cases haM : a ∈ cfgM T T₁
  · have h1 : QuotientGroup.mk' (cfgM T T₁) (g⁻¹ * a * g) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.Normal.conj_mem' inferInstance a haM g)
    rw [h1]
    exact Subgroup.one_mem _
  · have haL : a ∉ normIn T T₁ := fun h => haM (Cfg.normIn_le_cfgM_left T T₁ h)
    have hcomm : ⁅g⁻¹ * a * g, t⁆ ∈ cfgM T T₁ := by
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' (cfgM T T₁) ⁅g⁻¹ * a * g, t⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 hg'
    have hyT : g⁻¹ * a * g ∈ T :=
      c.strongly_closed_star ht htM (by rw [hX]; exact Subgroup.mem_top g) ha haL hcomm
    exact Subgroup.mem_map.2 ⟨g⁻¹ * a * g, hyT, rfl⟩

theorem Cfg.normalClosure_map [Finite G] (_c : Cfg T T₁) (hX : T ⊔ T₁ = ⊤)
    (hconj : ∃ x : G, T₁ = conjSubgroup x T) [(cfgM T T₁).Normal] :
    Subgroup.normalClosure
      ((T.map (QuotientGroup.mk' (cfgM T T₁)) : Subgroup (G ⧸ cfgM T T₁)) :
        Set (G ⧸ cfgM T T₁)) = ⊤ := by
  obtain ⟨x, hx⟩ := hconj
  have hcl : Subgroup.normalClosure (T : Set G) = ⊤ := by
    rw [eq_top_iff, ← hX]
    refine sup_le Subgroup.le_normalClosure ?_
    rw [hx]
    exact conjSubgroup_le_normalClosure T x
  rw [Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), hcl,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

theorem Cfg.map_ne_bot [Finite G] (c : Cfg T T₁) (hconj : ∃ x : G, T₁ = conjSubgroup x T)
    [(cfgM T T₁).Normal] : T.map (QuotientGroup.mk' (cfgM T T₁)) ≠ ⊥ := by
  intro h
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  have hle : T ≤ normIn T T₁ := by
    rw [← c.inf_cfgM]
    exact le_inf le_rfl h
  exact (c.normIn_lt hconj).not_ge hle

end CFSG.CGT.Timmesfeld75
