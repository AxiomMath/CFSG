module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryStartFusion

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.Blueprint CFSG.GH74.Uniqueness.Bender
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

theorem isSolvable_outer_unitary {K : Type*} [Group K] {n e : ℕ} (h : BenderType K n 3 e) :
    Group.IsSolvable (Outer K) := by
  obtain ⟨Dd, hDn, hDcyc, -, hqcyc, -⟩ := h.outer_unitary
  exact Group.isSolvable_of_ker_le_range Dd.subtype (QuotientGroup.mk' Dd) fun x hx =>
    ⟨⟨x, (QuotientGroup.eq_one_iff x).mp hx⟩, rfl⟩

theorem map_eq_bot_of_perfect {G H : Type*} [Group G] [Group H] [Group.IsSolvable H]
    (φ : G →* H) {P : Subgroup G} (hP : ⁅(P : Subgroup G), (P : Subgroup G)⁆ = P) :
    P.map φ = ⊥ := by
  by_contra hne
  have h1 := Group.IsSolvable.commutator_lt_of_ne_bot hne
  rw [← map_commutator, hP] at h1
  exact lt_irrefl _ h1

theorem commutator_eq_self_of_simple {G : Type*} [Group G] {P : Subgroup G}
    (hs : IsSimpleGroup P) (hnab : ∃ a b : P, a * b ≠ b * a) :
    ⁅(P : Subgroup G), (P : Subgroup G)⁆ = P := by
  have htop : commutator P = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator P) with h1 | h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have h2 : ⁅a, b⁆ ∈ commutator P := commutator_mem_commutator (mem_top a) (mem_top b)
      rw [h1, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
      exact hab h2
    · exact h1
  rw [← map_subtype_commutator, htop, ← MonoidHom.range_eq_map, range_subtype]

namespace U3Start

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}

theorem commutator_sup_zpowers_le (h : U3Start G L f t T) :
    ⁅L ⊔ zpowers t, L ⊔ zpowers t⁆ ≤ L := by
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨l, hl, z, hz, rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem ha
  obtain ⟨l', hl', z', hz', rfl⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem hb
  have hzl' : l' * z = z * l' := commute_of_mem_zpowers hz (mem_centralizer_iff.mp h.mem l' hl')
  have hzz' : z' * z = z * z' := commute_of_mem_zpowers hz (commute_of_mem_zpowers hz' rfl).symm
  have hz'l : l⁻¹ * z' = z' * l⁻¹ :=
    commute_of_mem_zpowers hz' (mem_centralizer_iff.mp h.mem _ (inv_mem hl))
  have e : ⁅l * z, l' * z'⁆ = l * l' * l⁻¹ * l'⁻¹ := by
    rw [commutatorElement_def]
    calc l * z * (l' * z') * (l * z)⁻¹ * (l' * z')⁻¹ =
        l * (l' * z) * z' * z⁻¹ * l⁻¹ * z'⁻¹ * l'⁻¹ := by rw [hzl']; group
      _ = l * l' * (z * z') * z⁻¹ * l⁻¹ * z'⁻¹ * l'⁻¹ := by group
      _ = l * l' * (z' * z) * z⁻¹ * l⁻¹ * z'⁻¹ * l'⁻¹ := by rw [hzz']
      _ = l * l' * (z' * l⁻¹) * z'⁻¹ * l'⁻¹ := by group
      _ = l * l' * l⁻¹ * l'⁻¹ := by rw [← hz'l]; group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hl hl') (inv_mem hl)) (inv_mem hl')

theorem le_of_perfect_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {M : Subgroup G}
    (hM : M ≤ centralizer ({t} : Set G)) (hMp : ⁅M, M⁆ = M) : M ≤ L := by
  have hst := h.setting.standardSetting
  have hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hst.standard
      h.mem h.inv).1
  have hCH : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
    inf_centralizer_eq_zpowers_of_card_sylow_eq_two hst.standard hS2 h.mem h.inv (hst.core t h.inv)
  obtain ⟨e, hB⟩ := exists_benderType_of_lieModel_psu3 h.two_le h.model
  have := isSolvable_outer_unitary hB
  set C := centralizer ({t} : Set G) with hC
  set ψ : C →* Outer L := (QuotientGroup.mk' (inner L)).comp
    (L.normalizerMonoidHom.comp (inclusion hHN)) with hψ
  set M' := M.subgroupOf C with hM'
  have hMM : M'.map C.subtype = M := by rw [hM', subgroupOf_map_subtype, inf_of_le_left hM]
  have hM'p : ⁅M', M'⁆ = M' := by
    apply map_injective C.subtype_injective
    rw [map_commutator, hMM, hMp]
  have hbot := map_eq_bot_of_perfect ψ hM'p
  have hle : M ≤ L ⊔ zpowers t := by
    intro m hm
    have hψm : ψ ⟨m, hM hm⟩ = 1 := by
      have hmM' : (⟨m, hM hm⟩ : C) ∈ M' := by rw [hM', mem_subgroupOf]; exact hm
      have : ψ ⟨m, hM hm⟩ ∈ M'.map ψ := ⟨⟨m, hM hm⟩, hmM', rfl⟩
      rwa [hbot, mem_bot] at this
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hψm
    obtain ⟨g, hg⟩ := hψm
    have hgm : ∀ y ∈ L, m * y * m⁻¹ = (g : G) * y * (g : G)⁻¹ := by
      intro y hy
      have := congrArg (fun σ : MulAut L => ((σ ⟨y, hy⟩ : L) : G)) hg
      simp only [MulAut.conj_apply, coe_mul, coe_inv, MonoidHom.comp_apply,
        normalizerMonoidHom_apply_apply_coe, coe_inclusion] at this
      exact this.symm
    have hgt : (g : G) ∈ C := mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp h.mem g g.2)
    have hk : (g : G)⁻¹ * m ∈ zpowers t := by
      rw [← hCH]
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y hy => ?_, mul_mem (inv_mem hgt) (hM hm)⟩
      calc y * ((g : G)⁻¹ * m) = (g : G)⁻¹ * (g * y * (g : G)⁻¹) * m := by group
        _ = (g : G)⁻¹ * (m * y * m⁻¹) * m := by rw [hgm y hy]
        _ = (g : G)⁻¹ * m * y := by group
    have e1 : m = g * ((g : G)⁻¹ * m) := by group
    rw [e1]
    exact mul_mem (mem_sup_left g.2) (mem_sup_right hk)
  calc M = ⁅M, M⁆ := hMp.symm
    _ ≤ ⁅L ⊔ zpowers t, L ⊔ zpowers t⁆ := commutator_mono hle hle
    _ ≤ L := h.commutator_sup_zpowers_le

theorem exists_conj_eq_mul_of_outer (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {g : G}
    (hxT : g⁻¹ * t * g ∈ T) (hxS : g⁻¹ * t * g ∉ szT₁ L T ⊔ zpowers t) {a : G}
    (ha : a ∈ szA₁ (szT₁ L T)) : ∃ g' : G, g'⁻¹ * t * g' = a * t := by
  classical
  have hst := h.setting.standardSetting
  have hHN : centralizer ({t} : Set G) ≤ normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hst.standard
      h.mem h.inv).1
  have hCH : centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t :=
    inf_centralizer_eq_zpowers_of_card_sylow_eq_two hst.standard hS2 h.mem h.inv (hst.core t h.inv)
  obtain ⟨e, hB⟩ := exists_benderType_of_lieModel_psu3 h.two_le h.model
  obtain ⟨-, hA₁card, -, -, -, hA₁sq, -⟩ := h.facts_of_card_sylow hS2
  set x := g⁻¹ * t * g with hx
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hx2 : x ^ 2 = 1 := by
    calc x ^ 2 = g⁻¹ * (t * t) * g := by rw [hx, sq]; group
      _ = 1 := by rw [ht2]; group
  have hx1 : x ≠ 1 := fun h1 => hxS (h1 ▸ one_mem _)
  have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
  obtain ⟨hxout, hxA₁, -, -⟩ := h.outer_facts_of_card_sylow hS2 hxT hx2 hxS
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (h.le hxT)
  obtain ⟨-, hLs, hLnab, -, -⟩ := u3Star_fixed h.two_le h.model hxo (h.le_normalizer hxT) hxout
  set Lx := L ⊓ centralizer ({x} : Set G) with hLx
  have hA₁Lx : szA₁ (szT₁ L T) ≤ Lx := fun b hb => mem_inf.mpr
    ⟨szT₁_le_right L T (szA₁_le _ hb), mem_centralizer_singleton_iff.mpr (hxA₁ b hb).symm⟩
  set s := g * t * g⁻¹ with hs
  have hgx : g * x * g⁻¹ = t := by rw [hx]; group
  have hst' : s * t = t * s := by
    calc s * t = g * (t * x) * g⁻¹ := by rw [hs, ← hgx]; group
      _ = g * (x * t) * g⁻¹ := by rw [hxt]
      _ = t * s := by rw [hs, ← hgx]; group
  have hsC : s ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr hst'
  have hs2 : s * s = 1 := by
    calc s * s = g * (t * t) * g⁻¹ := by rw [hs]; group
      _ = 1 := by rw [ht2]; group
  have hst1 : s ≠ t := by
    intro h1
    apply hxS
    have : x = t := by
      calc x = g⁻¹ * s * g := by rw [hx, h1]
        _ = t := by rw [hs]; group
    rw [this]
    exact mem_sup_right (mem_zpowers t)
  set M := Lx.map (MulAut.conj g).toMonoidHom with hM
  have hmemM : ∀ y ∈ Lx, g * y * g⁻¹ ∈ M := fun y hy => ⟨y, hy, rfl⟩
  have hMt : M ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyx : y * x = x * y := mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_centralizer_singleton_iff]
    calc g * y * g⁻¹ * t = g * (y * x) * g⁻¹ := by rw [← hgx]; group
      _ = g * (x * y) * g⁻¹ := by rw [hyx]
      _ = t * (g * y * g⁻¹) := by rw [← hgx]; group
  have hMs : M ≤ centralizer ({s} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyt : y * t = t * y := mem_centralizer_iff.mp h.mem y (mem_inf.mp hy).1
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_centralizer_singleton_iff, hs]
    calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
      _ = g * (t * y) * g⁻¹ := by rw [hyt]
      _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
  have hMp : ⁅M, M⁆ = M := by
    rw [hM, ← map_commutator, commutator_eq_self_of_simple hLs hLnab]
  have hML : M ≤ L := h.le_of_perfect_of_card_sylow hS2 hMt hMp
  set A₁' := (szA₁ (szT₁ L T)).map (MulAut.conj g).toMonoidHom with hA₁'
  have hA₁'M : A₁' ≤ M := map_mono hA₁Lx
  have hA₁'L : A₁' ≤ L := hA₁'M.trans hML
  have hA₁'sq : ∀ y ∈ A₁', y * y = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hb2 : b * b = 1 := by rw [← sq, hA₁sq b hb]
    calc g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  set Bq := A₁'.subgroupOf L with hBq
  have hBcard : Nat.card Bq = 2 ^ f := by
    rw [hBq, Nat.card_congr (subgroupOfEquivOfLe hA₁'L).toEquiv, hA₁',
      card_map_of_injective (MulAut.conj g).injective, hA₁card]
  have hBp : IsPGroup 2 Bq := IsPGroup.of_card hBcard
  obtain ⟨Q', hQ'⟩ := hBp.exists_le_sylow
  obtain ⟨t₀, hc⟩ := hB.exists_benderCore Q'
  have hBZ : Bq ≤ rootCenter (Q' : Subgroup L) := fun y hy =>
    hc.mem_rootCenter_of_mul_self (hQ' hy) (Subtype.ext (hA₁'sq y (mem_subgroupOf.mp hy)))
  have hBeq : Bq = rootCenter (Q' : Subgroup L) :=
    eq_of_le_of_card_ge hBZ (by rw [hc.card_center, hBcard])
  have hmemZ : ∀ y : L, y ∈ rootCenter (Q' : Subgroup L) ↔ (y : G) ∈ A₁' := fun y => by
    rw [← hBeq, hBq, mem_subgroupOf]
  have hsN : s ∈ normalizer (L : Set G) := hHN hsC
  set σ := L.normalizerMonoidHom ⟨s, hsN⟩ with hσdef
  have hσ : ∀ y : L, ((σ y : L) : G) = s * y * s⁻¹ := fun y =>
    normalizerMonoidHom_apply_apply_coe L _ y
  have hσσ : σ * σ = 1 := by
    rw [hσdef, ← map_mul]
    have : (⟨s, hsN⟩ : normalizer (L : Set G)) * ⟨s, hsN⟩ = 1 := Subtype.ext hs2
    rw [this, map_one]
  have hσZ : ∀ z ∈ rootCenter (Q' : Subgroup L), σ z = z := by
    intro z hz
    apply Subtype.ext
    rw [hσ]
    have hzs := mem_centralizer_singleton_iff.mp (hMs (hA₁'M ((hmemZ z).mp hz)))
    rw [← hzs, mul_inv_cancel_right]
  have hσout : ¬ ∃ l : L, ∀ y : L, σ y = l * y * l⁻¹ := by
    rintro ⟨l, hl⟩
    have hly : ∀ y ∈ L, s * y * s⁻¹ = l * y * (l : G)⁻¹ := by
      intro y hy
      have := congrArg Subtype.val (hl ⟨y, hy⟩)
      rw [hσ] at this
      simpa using this
    have hlt : (l : G) ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp h.mem l l.2)
    have hk : (l : G)⁻¹ * s ∈ zpowers t := by
      rw [← hCH]
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun y hy => ?_, mul_mem (inv_mem hlt) hsC⟩
      calc y * ((l : G)⁻¹ * s) = (l : G)⁻¹ * (l * y * (l : G)⁻¹) * s := by group
        _ = (l : G)⁻¹ * (s * y * s⁻¹) * s := by rw [hly y hy]
        _ = (l : G)⁻¹ * s * y := by group
    have hlM : ∀ y ∈ M, (l : G) * y = y * l := by
      intro y hy
      have hys := mem_centralizer_singleton_iff.mp (hMs hy)
      have hyt := mem_centralizer_singleton_iff.mp (hMt hy)
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hk with h1 | h1
      · have hls : (l : G) = s := by
          calc (l : G) = l * ((l : G)⁻¹ * s) := by rw [h1, mul_one]
            _ = s := by group
        rw [hls, hys]
      · have hls : (l : G) = s * t := by
          calc (l : G) = l * ((l : G)⁻¹ * s) * t := by rw [h1, mul_assoc, ht2, mul_one]
            _ = s * t := by group
        rw [hls]
        calc s * t * y = s * (t * y) := by group
          _ = s * (y * t) := by rw [hyt]
          _ = (s * y) * t := by group
          _ = (y * s) * t := by rw [hys]
          _ = y * (s * t) := by group
    have hl2 : (l : G) * l = 1 := by
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hk with h1 | h1
      · have hls : (l : G) = s := by
          calc (l : G) = l * ((l : G)⁻¹ * s) := by rw [h1, mul_one]
            _ = s := by group
        rw [hls, hs2]
      · have hls : (l : G) = s * t := by
          calc (l : G) = l * ((l : G)⁻¹ * s) * t := by rw [h1, mul_assoc, ht2, mul_one]
            _ = s * t := by group
        rw [hls]
        calc s * t * (s * t) = s * (t * s) * t := by group
          _ = s * (s * t) * t := by rw [hst']
          _ = (s * s) * (t * t) := by group
          _ = 1 := by rw [hs2, ht2, mul_one]
    have hl1 : (l : G) ≠ 1 := by
      intro h1
      rw [h1, inv_one, one_mul] at hk
      rcases mem_zpowers_involution_eq_one_or_eq h.sq_eq_one hk with h2 | h2
      · have h3 : t = 1 := by
          calc t = g⁻¹ * s * g := by rw [hs]; group
            _ = 1 := by rw [h2]; group
        have h4 := h.inv
        rw [h3, orderOf_one] at h4
        exact absurd h4 (by norm_num)
      · exact hst1 h2
    have hlZ : l ∈ centralizer (rootCenter (Q' : Subgroup L) : Set L) :=
      mem_centralizer_iff.mpr fun z hz => Subtype.ext
        (hlM z (hA₁'M ((hmemZ z).mp hz))).symm
    rw [hc.centralizer_rootCenter_eq] at hlZ
    have hlB : l ∈ borel (Q' : Subgroup L) := sup_le (le_borel _)
      ((fixCartan_le_cartan _ _).trans (cartan_le_borel _ _)) hlZ
    have hlo : orderOf l = 2 := orderOf_eq_prime (by
      rw [sq]; exact Subtype.ext hl2) (fun h1 => hl1 (congrArg Subtype.val h1))
    have hlA : (l : G) ∈ A₁' := (hmemZ l).mp (hc.center_of_involution l hlB hlo)
    obtain ⟨b, hb, hbl⟩ := hlA
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hbl
    have hbLx := hA₁Lx hb
    have hbZ : (⟨b, hbLx⟩ : Lx) ∈ center Lx := mem_center_iff.mpr fun y => Subtype.ext (by
      have e1 := hlM _ (hmemM y y.2)
      rw [← hbl] at e1
      have e2 : g * (y * b) * g⁻¹ = g * (b * y) * g⁻¹ := by
        calc g * (y * b) * g⁻¹ = g * y * g⁻¹ * (g * b * g⁻¹) := by group
          _ = g * b * g⁻¹ * (g * y * g⁻¹) := e1.symm
          _ = g * (b * y) * g⁻¹ := by group
      simpa using e2)
    rw [center_eq_bot_of_simple_nonabelian hLs hLnab, mem_bot] at hbZ
    have hb1 : b = 1 := congrArg Subtype.val hbZ
    apply hl1
    rw [← hbl, hb1]
    group
  have hσQ := hB.mem_of_centralizes_rootCenter Q' σ hσZ
  obtain ⟨hWQ, -, -, -, hWinv, -, -, hWsq, -⟩ := hB.lemma_3_4_d5_unitary Q' σ hσσ hσout hσQ
  have haL : g * a * g⁻¹ ∈ L := hA₁'L ⟨a, ha, rfl⟩
  obtain ⟨w, hwW, hww⟩ := hWsq ⟨g * a * g⁻¹, haL⟩ ((hmemZ _).mpr ⟨a, ha, rfl⟩)
  have hσw : s * w * s⁻¹ = (w : G)⁻¹ := by
    have := congrArg Subtype.val (hWinv w hwW)
    rw [hσ] at this
    simpa using this
  have hww' : (w : G) * w = g * a * g⁻¹ := congrArg Subtype.val hww
  refine ⟨g⁻¹ * (w : G)⁻¹ * g, ?_⟩
  have hsw : (w : G) * s * (w : G)⁻¹ = g * (a * t) * g⁻¹ := by
    calc (w : G) * s * (w : G)⁻¹ = w * (s * (w : G)⁻¹ * s⁻¹) * s := by group
      _ = w * (s * w * s⁻¹)⁻¹ * s := by group
      _ = w * w * s := by rw [hσw, inv_inv]
      _ = g * (a * t) * g⁻¹ := by rw [hww', hs]; group
  calc (g⁻¹ * (w : G)⁻¹ * g)⁻¹ * t * (g⁻¹ * (w : G)⁻¹ * g) =
      g⁻¹ * ((w : G) * (g * t * g⁻¹) * (w : G)⁻¹) * g := by group
    _ = a * t := by rw [← hs, hsw]; group

theorem exists_conj_eq_mul_ne_one_of_card_sylow
    (h : U3Start G L f t T) (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) :
    ∃ a ∈ szA₁ (szT₁ L T), a ≠ 1 ∧ ∃ g : G, g⁻¹ * t * g = a * t := by
  have hst := h.setting.standardSetting
  have := hst.simple
  obtain ⟨P, hP⟩ := h.sylow
  have hPT : (P : Subgroup (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype = T := by
    rw [hP, subgroupOf_map_subtype, inf_of_le_left h.le]
  obtain ⟨g, -, hgT, hgt⟩ :=
    exists_conj_ne_mem_sylow_centralizer hst.nonab hst.standard hst.cyclic h.mem h.inv
      (hst.core t h.inv) P
  rw [hPT] at hgT
  have ht2 : t * t = 1 := by rw [← sq, h.sq_eq_one]
  have hx2 : (g⁻¹ * t * g) ^ 2 = 1 := by
    calc (g⁻¹ * t * g) ^ 2 = g⁻¹ * (t * t) * g := by rw [sq]; group
      _ = 1 := by rw [ht2]; group
  obtain ⟨-, -, -, -, -, -, hinvA⟩ := h.facts_of_card_sylow hS2
  by_cases hxS : g⁻¹ * t * g ∈ szT₁ L T ⊔ zpowers t
  · obtain ⟨⟨b, hb, hxb⟩, -⟩ := h.exists_normalizer_conj_of_card_sylow hS2 (hinvA _ hxS hx2)
    refine ⟨b, hb, fun hb1 => hgt ?_, g, hxb⟩
    rw [hxb, hb1, one_mul]
  · obtain ⟨a, ha, -, ha1⟩ := h.exists_mem_szA₁_inf_center_of_card_sylow hS2
    exact ⟨a, ha, ha1, h.exists_conj_eq_mul_of_outer hS2 hgT hxS ha⟩

theorem exists_conj_eq_mul_of_card_sylow (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {a : G}
    (ha : a ∈ szA₁ (szT₁ L T)) : ∃ g : G, g⁻¹ * t * g = a * t := by
  by_cases ha1 : a = 1
  · exact ⟨1, by rw [ha1]; group⟩
  obtain ⟨a₀, ha₀, ha₀1, g₀, hg₀⟩ := h.exists_conj_eq_mul_ne_one_of_card_sylow hS2
  obtain ⟨d, -, hda, hdt, -, -⟩ := h.exists_cartan_conj_of_card_sylow hS2 ha₀ ha₀1 ha ha1
  refine ⟨g₀ * d, ?_⟩
  calc (g₀ * d)⁻¹ * t * (g₀ * d) = d⁻¹ * (g₀⁻¹ * t * g₀) * d := by group
    _ = d⁻¹ * a₀ * d * (d⁻¹ * (t * d)) := by rw [hg₀]; group
    _ = a * t := by rw [← hda, ← hdt]; group

end U3Start

end CFSG.SeitzReduction.RankOne
