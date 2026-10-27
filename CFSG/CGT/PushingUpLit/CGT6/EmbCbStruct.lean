module

public import CFSG.CGT.PushingUpLit.CGT6.EmbCbLift
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbVec
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbSwap
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbApi
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbComp

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv
open CFSG.EvenSmallLie.OddTranspAlt (cls)

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
private theorem cbs_ne_bot {Y : Subgroup (MulAut V)} {m : ℕ} (hm : 7 ≤ m) (hY : YAlt Y m) :
    Y ≠ ⊥ := by
  obtain ⟨ε⟩ := hY
  have : Nontrivial (alternatingGroup (Fin m)) :=
    alternatingGroup.nontrivial_of_three_le_card (by simp; omega)
  have : Nontrivial ↥Y := ε.toEquiv.nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot Y).mp this

omit [Finite V] in
private theorem cbs_isSimple {X : Subgroup (MulAut V)} {k : ℕ} (hk : 5 ≤ k)
    (θ : ↥X ≃* alternatingGroup (Fin k)) : IsSimpleGroup ↥X := by
  have : IsSimpleGroup (alternatingGroup (Fin k)) :=
    alternatingGroup.isSimpleGroup (by simpa using hk)
  exact (MulEquiv.isSimpleGroup_congr θ).mpr this

omit [Finite V] in
private theorem cbs_subnormal_restrict {K X H : Subgroup (MulAut V)} (hXH : X ≤ H)
    (h : (K.subgroupOf H).IsSubnormal) : (K.subgroupOf X).IsSubnormal := by
  have := h.comap (Subgroup.inclusion hXH)
  rwa [Subgroup.comap_inclusion_subgroupOf] at this

omit [Finite V] in
private theorem cbs_eq_of_subnormal {X Y : Subgroup (MulAut V)} {k : ℕ} (hk : 5 ≤ k)
    (θ : ↥X ≃* alternatingGroup (Fin k)) (hYX : Y ≤ X) (hY : Y ≠ ⊥)
    (hsub : (Y.subgroupOf X).IsSubnormal) : Y = X := by
  have : IsSimpleGroup ↥X := cbs_isSimple hk θ
  rcases hsub.eq_bot_or_top_of_isSimpleGroup inferInstance with h0 | h1
  · exfalso
    refine hY (eq_bot_iff.mpr fun y hy => ?_)
    have hy' : (⟨y, hYX hy⟩ : ↥X) ∈ Y.subgroupOf X := hy
    rw [h0, Subgroup.mem_bot] at hy'
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hy')
  · exact le_antisymm hYX (Subgroup.subgroupOf_eq_top.mp h1)

omit [Finite V] in
private theorem cbs_card_sup_of_inf_eq_bot {A B : Subgroup V} (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  rw [← Nat.card_prod]
  refine (Nat.card_congr (Equiv.ofBijective
    (fun p : ↥A × ↥B => (⟨(p.1 : V) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(A ⊔ B)))
    ⟨?_, ?_⟩)).symm
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ hab
    simp only [Subtype.mk.injEq] at hab
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [hab]
        _ = b' * b⁻¹ := by group
    have h2 : a'⁻¹ * a ∈ A ⊓ B :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hb' (inv_mem hb)⟩
    rw [h, Subgroup.mem_bot] at h2
    have h3 : a = a' := (inv_mul_eq_one.mp h2).symm
    have h4 : b' = b := mul_inv_eq_one.mp (by rw [← h1, h2])
    subst h3
    subst h4
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

private theorem cbs_normalizes {G T Y : Subgroup (MulAut V)} (h2 : Alt2Rank1)
    (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m)
    (hY : YAlt Y m) {H : Subgroup (MulAut V)} (hHG : H ≤ G) (hYH : Y ≤ H)
    (hsub : (Y.subgroupOf H).IsSubnormal) : ∀ x ∈ H, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := by
  intro x hx y hy
  obtain ⟨ε⟩ := hY
  let e : ↥Y ≃* ↥(Y.map (MulAut.conj x).toMonoidHom) :=
    Subgroup.equivMapOfInjective Y (MulAut.conj x).toMonoidHom (MulAut.conj x).injective
  have hY'H : Y.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨y', hy', rfl⟩
    exact H.mul_mem (H.mul_mem hx (hYH hy')) (H.inv_mem hx)
  have hsub' := cbc_map_conj_subnormal hx hsub
  rcases cbc_le_or_commute hYH hY'H hsub hsub' (k := m) (by omega) ε with hle | hcomm
  · have heq : Y = Y.map (MulAut.conj x).toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hle (Nat.card_congr e.toEquiv).ge
    have hmem : x * y * x⁻¹ ∈ Y.map (MulAut.conj x).toMonoidHom :=
      ⟨y, hy, by simp [MulAut.conj_apply]⟩
    rwa [← heq] at hmem
  · exfalso
    refine h.not_alt_le_centralizer h2 hV hm hodd ⟨ε⟩ (k := m) (by omega) (e.symm.trans ε)
      (hY'H.trans hHG) fun z hz y' hy' => ?_
    have hle : Y ≤ Subgroup.centralizer (Y.map (MulAut.conj x).toMonoidHom : Set (MulAut V)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact Subgroup.mem_centralizer_iff.mp (hle hy') z hz

theorem EndCfg4.cbLift_of_lift {G T Y : Subgroup (MulAut V)} (h2 : Alt2Rank1)
    (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m)
    (hY : YAlt Y m) {t : MulAut V} (htG : t ∈ G) (htT : t ∈ T) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1)
    {u : V} (hu : u ∈ commV (Subgroup.zpowers t)) (hu1 : u ≠ 1) {X : Subgroup (MulAut V)}
    (hX : Lift4 (vecStab G u) Y X) (hXY : X ≠ Y) : IsCbLift G Y t m X := by
  classical
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have hHG : vecStab G u ≤ G := fun g hg => (mem_vecStab.mp hg).1
  obtain ⟨hYX, hXH, hsubX, hcase⟩ := h.lift_alt h2 hV hm hodd hY hHG hX
  obtain ⟨θ, a, b, hab, hstab, hnat⟩ := hcase.resolve_left hXY
  have hXG : X ≤ G := hXH.trans hHG
  have hYbot : Y ≠ ⊥ := cbs_ne_bot hm hY
  have hty : ∀ y ∈ Y, t * y = y * t := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (h.adm.hYC hy).2 t htT
  have htY : t ∈ Subgroup.centralizer (Y : Set (MulAut V)) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hty y hy).symm
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hut : t u = u :=
    mem_fixV.mp (cb_commV_zpowers_le_fixV_self hV ht2 hu) t (Subgroup.mem_zpowers t)
  have htH : t ∈ vecStab G u := mem_vecStab.mpr ⟨htG, hut⟩
  have hufix : u ∈ fixV X := mem_fixV.mpr fun x hx => (mem_vecStab.mp (hXH hx)).2
  have hn : ∀ x ∈ X, t * x * t⁻¹ ∈ X := by
    have hsubXt := cbc_map_conj_subnormal htH hsubX
    have hYXt : Y ≤ X.map (MulAut.conj t).toMonoidHom := by
      intro y hy
      refine Subgroup.mem_map.mpr ⟨y, hYX hy, ?_⟩
      change t * y * t⁻¹ = y
      rw [hty y hy, mul_assoc, mul_inv_cancel, mul_one]
    have hle := cbc_le_of_subnormal_meet hXH hsubXt (by omega : 5 ≤ m + 2) θ hYX hYXt hYbot
    intro x hx
    obtain ⟨x', hx', hxx'⟩ := Subgroup.mem_map.mp (hle hx)
    have h1 : t * x' * t⁻¹ = x := hxx'
    have h2' : t * x * t⁻¹ = x' := by
      rw [← h1, htinv]
      calc t * (t * x' * t) * t = (t * t) * x' * (t * t) := by group
        _ = x' := by rw [htt]; group
    rw [h2']
    exact hx'
  have hsplit := cb_swap_or_one hm θ hab hstab hn hty
  rcases hsplit with hone | hswap
  swap
  · refine
      { Y_le := hYX
        alt := ⟨θ, a, b, hn, hab, hstab, hnat, hswap⟩
        le_G := hXG
        nontrivial := ?_
        subnormal := ?_ }
    · intro hbot
      have : u ∈ fixV X ⊓ commV (Subgroup.zpowers t) := ⟨hufix, hu⟩
      rw [hbot] at this
      exact hu1 (Subgroup.mem_bot.mp this)
    · intro u' hu' hu'1
      have hXu' : X ≤ vecStab G u' := fun x hx =>
        mem_vecStab.mpr ⟨hXG hx, mem_fixV.mp hu'.1 x hx⟩
      have hH'G : vecStab G u' ≤ G := fun g hg => (mem_vecStab.mp hg).1
      obtain ⟨X', hX'⟩ := h.exists_lift_vecStab hV hm hodd hY htG htT ht2 ht1 hu'.2 hu'1
      obtain ⟨hYX', hX'H', hsubX', hcase'⟩ := h.lift_alt h2 hV hm hodd hY hH'G hX'
      by_cases hX'Y : X' = Y
      · exfalso
        rw [hX'Y] at hsubX'
        exact hXY (cbs_eq_of_subnormal (by omega : 5 ≤ m + 2) θ hYX hYbot
          (cbs_subnormal_restrict hXu' hsubX')).symm
      · obtain ⟨θ', a', b', hab', hstab', hnat'⟩ := hcase'.resolve_left hX'Y
        have hle := cbc_le_of_subnormal_meet hXu' hsubX' (by omega : 5 ≤ m + 2) θ hYX hYX' hYbot
        have heq : X = X' := by
          refine Subgroup.eq_of_le_of_card_ge hle ?_
          rw [Nat.card_congr θ.toEquiv, Nat.card_congr θ'.toEquiv]
        rw [heq]
        exact hsubX'
  · exfalso
    have htX : ∀ x ∈ X, t * x = x * t := by
      intro x hx
      have h2' : (⟨t * x * t⁻¹, hn x hx⟩ : ↥X) = ⟨x, hx⟩ := θ.injective (Subtype.ext (hone x hx))
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h2')
    have hcent := h.cent t ⟨htG, htY⟩ ht1 ht2
    have hXC : X ≤ G ⊓ Subgroup.centralizer ({t} : Set (MulAut V)) := fun x hx =>
      ⟨hXG hx, Subgroup.mem_centralizer_iff.mpr fun s hs => by
        rw [Set.mem_singleton_iff.mp hs]
        exact htX x hx⟩
    exact hXY (cbs_eq_of_subnormal (by omega : 5 ≤ m + 2) θ hYX hYbot
      (cbs_subnormal_restrict hXC hcent)).symm

theorem EndCfg4.exists_cbLift {G T Y : Subgroup (MulAut V)} (h2 : Alt2Rank1)
    (h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m)
    (hY : YAlt Y m) {t : ↥G} (ht : orderOf t = 2) (htT : (t : MulAut V) ∈ T) {c : ↥G}
    (hc : c ∈ cls t) (hct : c ≠ t) (hcomm : t * c = c * t)
    (hbad : commV (Subgroup.zpowers (t : MulAut V)) ⊓
      commV (Subgroup.zpowers (c : MulAut V)) ≠ ⊥) :
    ∃ X : Subgroup (MulAut V), IsCbLift G Y (t : MulAut V) m X := by
  classical
  have hYG : Y ≤ G := fun y hy => (h.adm.hYC hy).1
  have ht2 : (t : MulAut V) ^ 2 = 1 := by
    have h1 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
  have ht1 : (t : MulAut V) ≠ 1 := by
    intro h1
    have : t = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ht
    omega
  obtain ⟨g, hg⟩ := hc
  have hcg : (c : MulAut V) = (g : MulAut V) * (t : MulAut V) * (g : MulAut V)⁻¹ := by
    rw [hg]; rfl
  have hc2 : (c : MulAut V) ^ 2 = 1 := by
    rw [hcg, conj_pow, ht2]; group
  have hc1 : (c : MulAut V) ≠ 1 := by
    intro h1
    apply ht1
    have h3 : (g : MulAut V) * (t : MulAut V) * (g : MulAut V)⁻¹ = 1 := by rw [← hcg]; exact h1
    calc (t : MulAut V) = (g : MulAut V)⁻¹ * ((g : MulAut V) * (t : MulAut V) *
          (g : MulAut V)⁻¹) * (g : MulAut V) := by group
      _ = 1 := by rw [h3]; group
  obtain ⟨u', hu1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbad
  have hu : (u' : V) ∈ commV (Subgroup.zpowers (t : MulAut V)) ⊓
      commV (Subgroup.zpowers (c : MulAut V)) := u'.2
  have hu1 : (u' : V) ≠ 1 := fun e => hu1' (Subtype.ext e)
  obtain ⟨X, hX⟩ := h.exists_lift_vecStab hV hm hodd hY t.2 htT ht2 ht1 hu.1 hu1
  by_cases hXY : X = Y
  swap
  · exact ⟨X, h.cbLift_of_lift h2 hV hm hodd hY t.2 htT ht2 ht1 hu.1 hu1 hX hXY⟩
  exfalso
  rw [hXY] at hX
  have hHG : vecStab G (u' : V) ≤ G := fun x hx => (mem_vecStab.mp hx).1
  have hnorm := cbs_normalizes h2 h hV hm hodd hY hHG hX.2.1 hX.2.2.1
  have hty : ∀ y ∈ Y, (t : MulAut V) * y = y * t := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (h.adm.hYC hy).2 t htT
  obtain ⟨ε⟩ := hY
  let e : ↥Y ≃* ↥(Y.map (MulAut.conj (g : MulAut V)).toMonoidHom) :=
    Subgroup.equivMapOfInjective Y (MulAut.conj (g : MulAut V)).toMonoidHom
      (MulAut.conj (g : MulAut V)).injective
  have hZH : Y.map (MulAut.conj (g : MulAut V)).toMonoidHom ≤ vecStab G (u' : V) := by
    rintro _ ⟨y, hy, rfl⟩
    refine mem_vecStab.mpr ⟨G.mul_mem (G.mul_mem g.2 (hYG hy)) (G.inv_mem g.2), ?_⟩
    have hmem : (u' : V) ∈ commV (Subgroup.zpowers
        ((g : MulAut V) * (t : MulAut V) * (g : MulAut V)⁻¹)) := by
      rw [← hcg]
      exact hu.2
    rw [cb_commV_zpowers_conj] at hmem
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.mp hmem
    have hwY : w ∈ fixV Y := h.commV_zpowers_le_fixV hV hm hodd ⟨ε⟩ htT ht2 hw
    have hyw : y w = w := mem_fixV.mp hwY y hy
    have key : (g : MulAut V)⁻¹ (u' : V) = w := by
      have h4 : (g : MulAut V)⁻¹ ((g : MulAut V) w) = w := MulAut.inv_apply_self V _ _
      rw [← hwu]
      exact h4
    have h3 : (MulAut.conj (g : MulAut V)).toMonoidHom y =
        (g : MulAut V) * y * (g : MulAut V)⁻¹ := rfl
    rw [h3, MulAut.mul_apply, MulAut.mul_apply, key, hyw]
    exact hwu
  have hZY := h.eq_of_alt_le_normalizer h2 hV hm hodd ⟨ε⟩ ⟨e.symm.trans ε⟩ (hZH.trans hHG)
    (fun z hz y hy => hnorm z (hZH hz) y hy)
  have hcY : ∀ y ∈ Y, (c : MulAut V) * y = y * (c : MulAut V) := by
    intro y hy
    have hyZ : y ∈ Y.map (MulAut.conj (g : MulAut V)).toMonoidHom := by rw [hZY]; exact hy
    obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.mp hyZ
    have h1 : (t : MulAut V) * y' = y' * t := hty y' hy'
    have h3 : (g : MulAut V) * y' * (g : MulAut V)⁻¹ = y := hyy'
    rw [hcg, ← h3]
    calc (g : MulAut V) * t * (g : MulAut V)⁻¹ * ((g : MulAut V) * y' * (g : MulAut V)⁻¹)
        = (g : MulAut V) * (t * y') * (g : MulAut V)⁻¹ := by group
      _ = (g : MulAut V) * (y' * t) * (g : MulAut V)⁻¹ := by rw [h1]
      _ = ((g : MulAut V) * y' * (g : MulAut V)⁻¹) * ((g : MulAut V) * t * (g : MulAut V)⁻¹) := by
        group
  have htC : (t : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hty y hy).symm
  have hcC : (c : MulAut V) ∈ Subgroup.centralizer (Y : Set (MulAut V)) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hcY y hy).symm
  refine h2 V hV G T Y h m hm hodd ⟨ε⟩ t c t.2 c.2 htC hcC ht2 hc2 ht1 hc1
    (fun e' => hct (Subtype.ext e'.symm)) ?_
  have := congrArg Subtype.val hcomm
  simpa using this

omit [Finite V] in
theorem IsCbLift.eq_of_common_vec {G Y : Subgroup (MulAut V)} {m : ℕ} (hm : 7 ≤ m)
    (hY : YAlt Y m) {t : MulAut V} {X X' : Subgroup (MulAut V)} (hX : IsCbLift G Y t m X)
    (hX' : IsCbLift G Y t m X') {u : V} (hu : u ∈ fixV X ⊓ commV (Subgroup.zpowers t))
    (hu' : u ∈ fixV X') (hu1 : u ≠ 1) : X = X' := by
  have hYbot : Y ≠ ⊥ := cbs_ne_bot hm hY
  obtain ⟨θ, -⟩ := hX.alt
  obtain ⟨θ', -⟩ := hX'.alt
  have hXu : X ≤ vecStab G u := fun x hx =>
    mem_vecStab.mpr ⟨hX.le_G hx, mem_fixV.mp hu.1 x hx⟩
  have hXu' : X' ≤ vecStab G u := fun x hx =>
    mem_vecStab.mpr ⟨hX'.le_G hx, mem_fixV.mp hu' x hx⟩
  have hsub := hX.subnormal u hu hu1
  have hsub' := hX'.subnormal u ⟨hu', hu.2⟩ hu1
  exact le_antisymm
    (cbc_le_of_subnormal_meet hXu hsub' (by omega : 5 ≤ m + 2) θ hX.Y_le hX'.Y_le hYbot)
    (cbc_le_of_subnormal_meet hXu' hsub (by omega : 5 ≤ m + 2) θ' hX'.Y_le hX.Y_le hYbot)

omit [Finite V] in
theorem IsCbLift.le_conjClosure {G Y : Subgroup (MulAut V)} {m : ℕ} (hm : 7 ≤ m)
    (hY : YAlt Y m) {t : MulAut V} {X : Subgroup (MulAut V)} (hX : IsCbLift G Y t m X) :
    X ≤ conjClosure Y G := by
  obtain ⟨θ, -⟩ := hX.alt
  refine cbc_le_of_normalizes (by omega : 5 ≤ m + 2) θ hX.Y_le
    CFSG.CGT.PushingUpLit.CGT6.le_conjClosure (cbs_ne_bot hm hY) ?_
  intro x hx z hz
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure (hX.le_G hx)) z).mp hz

theorem EndCfg4.card_commV_of_two_lifts {G T Y : Subgroup (MulAut V)} (_h2 : Alt2Rank1)
    (_h : EndCfg4 G T Y) (hV : ∀ v : V, v ^ 2 = 1) {m : ℕ} (hm : 7 ≤ m) (hodd : Odd m)
    (hY : YAlt Y m) {t : MulAut V} (_htG : t ∈ G) (_htT : t ∈ T) (ht2 : t ^ 2 = 1)
    (_ht1 : t ≠ 1) {X₁ X₂ : Subgroup (MulAut V)} (h₁ : IsCbLift G Y t m X₁)
    (h₂ : IsCbLift G Y t m X₂)
    (hne : X₁ ≠ X₂) :
    Nat.card ↥(commV (Subgroup.zpowers t)) = 4 ∧
      Nat.card ↥(fixV X₁ ⊓ commV (Subgroup.zpowers t)) = 2 ∧
      Nat.card ↥(fixV X₂ ⊓ commV (Subgroup.zpowers t)) = 2 ∧
      (fixV X₁ ⊓ commV (Subgroup.zpowers t)) ⊓ (fixV X₂ ⊓ commV (Subgroup.zpowers t)) = ⊥ := by
  classical
  have hdisj : (fixV X₁ ⊓ commV (Subgroup.zpowers t)) ⊓ (fixV X₂ ⊓ commV (Subgroup.zpowers t)) =
      ⊥ := by
    refine eq_bot_iff.mpr fun u hu => ?_
    by_contra hu1
    exact hne (IsCbLift.eq_of_common_vec hm hY h₁ h₂ hu.1 hu.2.1
      fun e => hu1 (Subgroup.mem_bot.mpr e))
  obtain ⟨D₁⟩ := h₁.toCbAlg.nonempty_data hm hodd
  obtain ⟨D₂⟩ := h₂.toCbAlg.nonempty_data hm hodd
  have e₁ : Nat.card ↥(commV (Subgroup.zpowers t)) =
      2 * Nat.card ↥(fixV X₁ ⊓ commV (Subgroup.zpowers t)) := by
    have := D₁.card_commV_zpowers hV hm hodd ht2
    rwa [inf_comm] at this
  have e₂ : Nat.card ↥(commV (Subgroup.zpowers t)) =
      2 * Nat.card ↥(fixV X₂ ⊓ commV (Subgroup.zpowers t)) := by
    have := D₂.card_commV_zpowers hV hm hodd ht2
    rwa [inf_comm] at this
  have hsup := cbs_card_sup_of_inf_eq_bot hdisj
  have hle : Nat.card ↥((fixV X₁ ⊓ commV (Subgroup.zpowers t)) ⊔
      (fixV X₂ ⊓ commV (Subgroup.zpowers t))) ≤ Nat.card ↥(commV (Subgroup.zpowers t)) :=
    Subgroup.card_le_of_le (sup_le inf_le_right inf_le_right)
  have hpos₁ : 0 < Nat.card ↥(fixV X₁ ⊓ commV (Subgroup.zpowers t)) := Nat.card_pos
  have hpos₂ : 0 < Nat.card ↥(fixV X₂ ⊓ commV (Subgroup.zpowers t)) := Nat.card_pos
  have hge₂ : 2 ≤ Nat.card ↥(fixV X₂ ⊓ commV (Subgroup.zpowers t)) := by
    have h1 : Nat.card ↥(fixV X₂ ⊓ commV (Subgroup.zpowers t)) ≠ 1 := fun e =>
      h₂.nontrivial (Subgroup.card_eq_one.mp e)
    omega
  have hge₁ : 2 ≤ Nat.card ↥(fixV X₁ ⊓ commV (Subgroup.zpowers t)) := by
    have h1 : Nat.card ↥(fixV X₁ ⊓ commV (Subgroup.zpowers t)) ≠ 1 := fun e =>
      h₁.nontrivial (Subgroup.card_eq_one.mp e)
    omega
  rw [hsup, e₁] at hle
  have h22 : Nat.card ↥(fixV X₂ ⊓ commV (Subgroup.zpowers t)) ≤ 2 := by
    have : Nat.card ↥(fixV X₁ ⊓ commV (Subgroup.zpowers t)) *
        Nat.card ↥(fixV X₂ ⊓ commV (Subgroup.zpowers t)) ≤
        Nat.card ↥(fixV X₁ ⊓ commV (Subgroup.zpowers t)) * 2 := by
      rw [mul_comm (Nat.card ↥(fixV X₁ ⊓ commV (Subgroup.zpowers t))) 2]
      exact hle
    exact Nat.le_of_mul_le_mul_left this hpos₁
  refine ⟨by omega, ?_, by omega, hdisj⟩
  have h22' : Nat.card ↥(fixV X₂ ⊓ commV (Subgroup.zpowers t)) = 2 := le_antisymm h22 hge₂
  omega

end CFSG.CGT.PushingUpLit.CGT6
