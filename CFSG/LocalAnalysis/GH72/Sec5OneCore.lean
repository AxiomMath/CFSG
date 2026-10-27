module

public import CFSG.LocalAnalysis.GH72.Sec5OneTools
public import CFSG.LocalAnalysis.GH72.OuterFacts
public import CFSG.LocalAnalysis.GH72.Sec4A
public import CFSG.LocalAnalysis.GH72.Sec4Balance
public import CFSG.LocalAnalysis.GH72.Sec4Bar

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools

namespace G5one

section Generic

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem mem_oddCore_iff {H : Subgroup G} (h : H) : h ∈ CFSG.oddCore H ↔ (h : G) ∈ O H := by
  constructor
  · intro hh
    exact ⟨h, hh, rfl⟩
  · rintro ⟨y, hy, hyh⟩
    rwa [← Subtype.ext hyh]

omit [Finite G] in
theorem exists_map_eq_of_covers {H K₀ OK : Subgroup G} {L : Type*} [Group L] (f : K₀ →* L)
    (hker : f.ker = OK.subgroupOf K₀) (hOKn : K₀ ≤ normalizer (OK : Set G))
    (hcov : Covers H K₀ OK) (k : K₀) : ∃ h : K₀, (h : G) ∈ H ∧ f h = f k := by
  obtain ⟨h, hh, o, ho, hho⟩ :=
    G5d.mem_sup_of_le_normalizer' (inf_le_right.trans hOKn) (hcov k.2)
  have hoK : o ∈ K₀ := by
    have e : o = h⁻¹ * k := by
      rw [← hho]
      group
    rw [e]
    exact mul_mem (inv_mem (mem_inf.mp hh).2) k.2
  refine ⟨⟨h, (mem_inf.mp hh).2⟩, (mem_inf.mp hh).1, ?_⟩
  have ho' : f ⟨o, hoK⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker, mem_subgroupOf]
    exact ho
  have e : k = ⟨h, (mem_inf.mp hh).2⟩ * ⟨o, hoK⟩ := Subtype.ext hho.symm
  rw [e, map_mul, ho', mul_one]

omit [Finite G] in
theorem map_normal_of_covers {H K₀ OK D : Subgroup G} {L : Type*} [Group L] (f : K₀ →* L)
    (hf : Function.Surjective f) (hker : f.ker = OK.subgroupOf K₀)
    (hOKn : K₀ ≤ normalizer (OK : Set G)) (hcov : Covers H K₀ OK)
    (hD : H ⊓ K₀ ≤ normalizer (D : Set G)) : ((D.subgroupOf K₀).map f).Normal := by
  refine ⟨fun n hn l => ?_⟩
  obtain ⟨d, hd, rfl⟩ := hn
  obtain ⟨k, rfl⟩ := hf l
  obtain ⟨h, hhH, hhk⟩ := exists_map_eq_of_covers f hker hOKn hcov k
  rw [← hhk]
  have hd' : (d : G) ∈ D := hd
  refine ⟨h * d * h⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  exact (mem_normalizer_iff.mp (hD (mem_inf.mpr ⟨hhH, h.2⟩)) d).mp hd'

theorem O_inf_le_of_covers {H K₀ OK : Subgroup G} {L : Type*} [Group L] (f : K₀ →* L)
    (hf : Function.Surjective f) (hker : f.ker = OK.subgroupOf K₀)
    (hOKn : K₀ ≤ normalizer (OK : Set G))
    (hLodd : ∀ N : Subgroup L, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hcov : Covers H K₀ OK) : O H ⊓ K₀ ≤ OK := by
  have hD : H ⊓ K₀ ≤ normalizer ((O H ⊓ K₀ : Subgroup G) : Set G) := fun h hh =>
    inf_normalizer_le_normalizer_inf ⟨G4c.le_normalizer_O H (mem_inf.mp hh).1,
      le_normalizer (mem_inf.mp hh).2⟩
  have hNodd : Odd (Nat.card (((O H ⊓ K₀).subgroupOf K₀).map f)) :=
    (G4c.odd_card_O H).of_dvd_nat ((card_map_dvd _ _).trans
      ((G4c.card_subgroupOf_dvd K₀ _).trans (card_dvd_of_le inf_le_left)))
  have hN1 := hLodd _ (map_normal_of_covers f hf hker hOKn hcov hD) hNodd
  intro x hx
  have hxK : x ∈ K₀ := (mem_inf.mp hx).2
  have hker' : (⟨x, hxK⟩ : K₀) ∈ f.ker := by
    rw [MonoidHom.mem_ker, ← mem_bot, ← hN1]
    exact ⟨⟨x, hxK⟩, hx, rfl⟩
  rw [hker, mem_subgroupOf] at hker'
  exact hker'

theorem eq_bot_of_normal_of_odd {L : Type*} [Group L] [Finite L] [IsSimpleGroup L]
    {P : Subgroup L} (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥) (N : Subgroup L) (hN : N.Normal)
    (hNodd : Odd (Nat.card N)) : N = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · have h1 := G4c.inf_eq_bot_of_odd_of_isPGroup hNodd hP
    rw [h, top_inf_eq] at h1
    exact absurd h1 hP1

omit [Finite G] in
theorem map_ne_bot_of_isPGroup [Finite G] {K₀ OK T : Subgroup G} {L : Type*} [Group L]
    (f : K₀ →* L) (hker : f.ker = OK.subgroupOf K₀) (hOKodd : Odd (Nat.card OK))
    (hTK : T ≤ K₀) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) : (T.subgroupOf K₀).map f ≠ ⊥ := by
  intro h
  apply hT1
  have hTO : T ≤ OK := by
    intro x hx
    have hx' : (⟨x, hTK hx⟩ : K₀) ∈ f.ker := by
      rw [MonoidHom.mem_ker, ← mem_bot, ← h]
      exact ⟨⟨x, hTK hx⟩, hx, rfl⟩
    rw [hker, mem_subgroupOf] at hx'
    exact hx'
  have h1 := G4c.inf_eq_bot_of_odd_of_isPGroup hOKodd hT
  rwa [inf_eq_right.mpr hTO] at h1

theorem map_eq_top_of_isSimpleGroup {H K₀ OK W T : Subgroup G} {L : Type*} [Group L]
    [IsSimpleGroup L] (f : K₀ →* L) (hf : Function.Surjective f)
    (hker : f.ker = OK.subgroupOf K₀) (hOKodd : Odd (Nat.card OK))
    (hOKn : K₀ ≤ normalizer (OK : Set G)) (hcov : Covers H K₀ OK) (hWK : W ≤ K₀)
    (hWn : H ⊓ K₀ ≤ normalizer (W : Set G)) (hTW : T ≤ W) (hT : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    (W.subgroupOf K₀).map f = ⊤ := by
  have hn := map_normal_of_covers f hf hker hOKn hcov hWn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((W.subgroupOf K₀).map f) with h | h
  · exfalso
    refine map_ne_bot_of_isPGroup f hker hOKodd (hTW.trans hWK) hT hT1 (eq_bot_iff.mpr ?_)
    rw [← h]
    exact map_mono (fun x hx => hTW hx)
  · exact h

omit [Finite G] in
theorem sup_O_subgroupOf_eq_comap {H W : Subgroup G} (hWH : W ≤ H) :
    (W ⊔ O H).subgroupOf H = (bar H W).comap (QuotientGroup.mk' (CFSG.oddCore H)) := by
  ext x
  rw [mem_subgroupOf, mem_comap]
  constructor
  · intro hx
    obtain ⟨w, hw, o, ho, hwo⟩ :=
      G5d.mem_sup_of_le_normalizer' (hWH.trans (G4c.le_normalizer_O H)) hx
    refine ⟨⟨w, hWH hw⟩, hw, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_oddCore_iff]
    have e : ((⟨w, hWH hw⟩ : H)⁻¹ * x : H) = o := by
      rw [coe_mul, coe_inv, Subtype.coe_mk, ← hwo]
      group
    rw [e]
    exact ho
  · rintro ⟨y, hy, hyx⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_oddCore_iff] at hyx
    have e : (x : G) = y * ((y⁻¹ * x : H) : G) := by
      rw [coe_mul, coe_inv]
      group
    rw [e]
    exact mul_mem_sup hy hyx

theorem O_eq_bot_of_normal {H : Subgroup G} {B : Subgroup (Bar H)} (hB : B.Normal) : O B = ⊥ := by
  refine G4c.eq_bot_of_normal_of_odd_bar ?_ (G4c.odd_card_O B)
  refine G4c.normal_of_top_le_normalizer fun u _ => G4c.mem_normalizer_of_map_cj_eq ?_
  have hu : u ∈ normalizer (B : Set (Bar H)) := mem_normalizer_iff.mpr fun h =>
    ⟨fun hh => hB.conj_mem h hh u, fun hh => by simpa [mul_assoc] using hB.conj_mem _ hh u⁻¹⟩
  rw [G4c.map_cj_O, G4c.map_cj_eq_of_mem_normalizer hu]

theorem core {H K₀ OK W : Subgroup G} {L : Type*} [Group L] (f : K₀ →* L)
    (hker : f.ker = OK.subgroupOf K₀) (hOKn : K₀ ≤ normalizer (OK : Set G))
    (hOKodd : Odd (Nat.card OK))
    (hLodd : ∀ N : Subgroup L, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hWH : W ≤ H) (hWK : W ≤ K₀) (hWn : (bar H W).Normal)
    (hWf : (W.subgroupOf K₀).map f = ⊤) :
    Covers W K₀ OK ∧ H ⊓ K₀ ≤ W ⊔ (H ⊓ OK) ∧ ((W ⊔ O H).subgroupOf H).Normal ∧
      O H ⊓ W = W ⊓ OK ∧ Nonempty (bar H W ≃* L) ∧
      bar H (H ⊓ OK) ≤ centralizer (bar H W : Set (Bar H)) := by
  have hrep : ∀ k ∈ K₀, ∃ w ∈ W, w⁻¹ * k ∈ OK := by
    intro k hk
    have hk' : f ⟨k, hk⟩ ∈ (W.subgroupOf K₀).map f := hWf ▸ mem_top _
    obtain ⟨w, hw, hwk⟩ := hk'
    refine ⟨w, hw, ?_⟩
    have h1 : w⁻¹ * ⟨k, hk⟩ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hwk, inv_mul_cancel]
    rw [hker, mem_subgroupOf] at h1
    exact h1
  have hcovW : Covers W K₀ OK := by
    intro k hk
    obtain ⟨w, hw, hwk⟩ := hrep k hk
    have e : k = w * (w⁻¹ * k) := by group
    rw [e]
    exact mul_mem_sup (mem_inf.mpr ⟨hw, hWK hw⟩) hwk
  have hfac : H ⊓ K₀ ≤ W ⊔ (H ⊓ OK) := by
    intro k hk
    obtain ⟨w, hw, hwk⟩ := hrep k (mem_inf.mp hk).2
    have e : k = w * (w⁻¹ * k) := by group
    rw [e]
    exact mul_mem_sup hw (mem_inf.mpr ⟨mul_mem (inv_mem (hWH hw)) (mem_inf.mp hk).1, hwk⟩)
  have hOHW : O H ⊓ W ≤ OK := by
    have hn : (((O H ⊓ W).subgroupOf K₀).map f).Normal := by
      refine ⟨fun n hn l => ?_⟩
      obtain ⟨d, hd, rfl⟩ := hn
      have hl : l ∈ (W.subgroupOf K₀).map f := hWf ▸ mem_top l
      obtain ⟨w, hw, rfl⟩ := hl
      have hd' : (d : G) ∈ O H ⊓ W := hd
      have hw' : (w : G) ∈ W := hw
      refine ⟨w * d * w⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact mem_inf.mpr ⟨G4c.conj_mem_O (hWH hw') (mem_inf.mp hd').1,
        mul_mem (mul_mem hw' (mem_inf.mp hd').2) (inv_mem hw')⟩
    have hodd : Odd (Nat.card (((O H ⊓ W).subgroupOf K₀).map f)) :=
      (G4c.odd_card_O H).of_dvd_nat ((card_map_dvd _ _).trans
        ((G4c.card_subgroupOf_dvd K₀ _).trans (card_dvd_of_le inf_le_left)))
    have h1 := hLodd _ hn hodd
    intro x hx
    have hxK : x ∈ K₀ := hWK (mem_inf.mp hx).2
    have hx' : (⟨x, hxK⟩ : K₀) ∈ f.ker := by
      rw [MonoidHom.mem_ker, ← mem_bot, ← h1]
      exact ⟨⟨x, hxK⟩, hx, rfl⟩
    rw [hker, mem_subgroupOf] at hx'
    exact hx'
  have hOB : O (bar H W) = ⊥ := O_eq_bot_of_normal hWn
  have hWOK : W ⊓ OK ≤ O H := by
    have hle : bar H (W ⊓ OK) ≤ O (bar H W) := by
      refine G5d.le_O_of_le_normalizer (G4c.bar_mono inf_le_left) (G4c.bar_le_normalizer ?_)
        (G4c.odd_card_bar (G4c.odd_card_of_le inf_le_right hOKodd))
      intro w hw
      exact inf_normalizer_le_normalizer_inf ⟨le_normalizer hw, hOKn (hWK hw)⟩
    rw [hOB] at hle
    exact (G4c.bar_eq_bot_iff (inf_le_left.trans hWH)).mp (le_bot_iff.mp hle)
  have hkereq : O H ⊓ W = W ⊓ OK :=
    le_antisymm (le_inf inf_le_right hOHW) (le_inf hWOK inf_le_left)
  refine ⟨hcovW, hfac, ?_, hkereq, ?_, ?_⟩
  · rw [sup_O_subgroupOf_eq_comap hWH]
    exact hWn.comap _
  ·
    let π : W →* Bar H := (QuotientGroup.mk' (CFSG.oddCore H)).comp (inclusion hWH)
    let g : W →* L := f.comp (inclusion hWK)
    have hg : Function.Surjective g := by
      intro l
      have hl : l ∈ (W.subgroupOf K₀).map f := hWf ▸ mem_top l
      obtain ⟨w, hw, rfl⟩ := hl
      exact ⟨⟨w, hw⟩, rfl⟩
    have hπ : π.range = bar H W := by
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
      rfl
    have hkk : π.ker = g.ker := by
      ext w
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, mem_oddCore_iff, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
        hker, mem_subgroupOf]
      change (w : G) ∈ O H ↔ (w : G) ∈ OK
      constructor
      · intro h
        exact hOHW ⟨h, w.2⟩
      · intro h
        exact hWOK ⟨w.2, h⟩
    exact ⟨(MulEquiv.subgroupCongr hπ).symm.trans
      ((QuotientGroup.quotientKerEquivRange π).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hkk).trans
          (QuotientGroup.quotientKerEquivOfSurjective g hg)))⟩
  ·
    set D : Subgroup (Bar H) := bar H W ⊓ bar H (H ⊓ OK) with hDdef
    have hWD : bar H W ≤ normalizer ((bar H (H ⊓ OK) : Subgroup (Bar H)) : Set (Bar H)) := by
      refine G4c.bar_le_normalizer fun w hw => ?_
      exact inf_normalizer_le_normalizer_inf ⟨le_normalizer (hWH hw), hOKn (hWK hw)⟩
    have hDle : D ≤ O (bar H W) := by
      refine G5d.le_O_of_le_normalizer inf_le_left ?_
        (G4c.odd_card_of_le inf_le_right
          (G4c.odd_card_bar (G4c.odd_card_of_le inf_le_right hOKodd)))
      intro w hw
      exact inf_normalizer_le_normalizer_inf ⟨le_normalizer hw, hWD hw⟩
    rw [hOB] at hDle
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ D := by
      refine mem_inf.mpr ⟨mul_mem (hWn.conj_mem b hb a) (inv_mem hb), ?_⟩
      have h1 : b * a⁻¹ * b⁻¹ ∈ bar H (H ⊓ OK) :=
        (mem_normalizer_iff.mp (hWD hb) a⁻¹).mp (inv_mem ha)
      have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [e]
      exact mul_mem ha h1
    have h1 : a * b * a⁻¹ * b⁻¹ = 1 := (mem_bot.mp (hDle hc))
    calc b * a = a * b * a⁻¹ * b⁻¹ * (b * a) := by rw [h1, one_mul]
      _ = a * b := by group

theorem bar_inf_le_centralizer_of_sup {H OK W Z Z' A : Subgroup G} (hAZ : A = Z ⊔ Z')
    (hZW : Z ≤ W) (hZH : Z ≤ H) (hZ'H : Z' ≤ H) (hOKZ' : OK ≤ centralizer (Z' : Set G))
    (hWc : bar H (H ⊓ OK) ≤ centralizer (bar H W : Set (Bar H))) :
    bar H (H ⊓ OK) ≤ centralizer (bar H A : Set (Bar H)) := by
  rw [hAZ, G4c.bar_sup hZH hZ'H, le_centralizer_iff]
  refine sup_le ?_ ?_
  · rw [← le_centralizer_iff]
    exact hWc.trans (centralizer_le (G4c.bar_mono hZW))
  · rw [← le_centralizer_iff]
    exact bar_le_centralizer (inf_le_right.trans hOKZ')

omit [Finite G] in
theorem map_eq_top_of_isPGroup [Finite G] {K₀ T : Subgroup G} {L : Type*} [Group L]
    (f : K₀ →* L) (hf : Function.Surjective f) (hL : IsPGroup 2 L) (hT : IsSylowOf 2 T K₀) :
    (T.subgroupOf K₀).map f = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := hT.exists_sylow_eq_subgroupOf
  set Q' := Sylow.mapSurjective hf Q
  have h1 : ((⊤ : Subgroup L)) = Q' :=
    Q'.3 (hL.of_equiv Subgroup.topEquiv.symm) le_top
  rw [← hQ, ← Sylow.coe_mapSurjective hf Q, ← h1]

theorem center_eq_bot_of_isSimpleGroup {L : Type*} [Group L] [Finite L] [IsSimpleGroup L]
    {P : Subgroup L} (hP : IsPGroup 2 P) (hP4 : 4 ≤ Nat.card P) : Subgroup.center L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
  · exact h
  · exfalso
    have hc : ∀ a b : L, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.mp (h ▸ mem_top b) a)
    have hn : ∀ N : Subgroup L, N.Normal := fun N =>
      ⟨fun n hn g => by rw [hc g n, mul_inv_cancel_right]; exact hn⟩
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hk2 : 2 ≤ k := by
      by_contra hk2
      interval_cases k <;> rw [hk] at hP4 <;> norm_num at hP4
    have h2 : 2 ∣ Nat.card L :=
      (dvd_pow_self 2 (by omega)).trans (hk ▸ Subgroup.card_subgroup_dvd_card P)
    have : Fintype L := Fintype.ofFinite L
    rw [Nat.card_eq_fintype_card] at h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 h2
    have := hn (zpowers x)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers x) with h3 | h3
    · have : x = 1 := by
        rw [← mem_bot, ← h3]
        exact mem_zpowers x
      rw [this, orderOf_one] at hx
      exact absurd hx (by norm_num)
    · have h4 := Subgroup.card_le_card_group P
      rw [← card_top (G := L), ← h3, Nat.card_zpowers, hx] at h4
      omega

end Generic

section Isolated

variable {G : Type} [Group G] [Finite G]

theorem exists_mk_eq_of_isIsolatedIn {H : Subgroup G} {t : G} (ht : IsIsolatedIn H t)
    (u : Bar H) : ∃ c : H, (c : G) ∈ C t ∧ QuotientGroup.mk' (CFSG.oddCore H) c = u := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.oddCore H) u
  obtain ⟨c, hc, hch⟩ := ht.exists_mem_C h.2
  refine ⟨⟨c, (mem_inf.mp hc).1⟩, (mem_inf.mp hc).2, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_oddCore_iff]
  exact hch

theorem inf_O_C_le_O {H : Subgroup G} {t : G} (ht : IsIsolatedIn H t) :
    (H ⊓ C t) ⊓ O (C t) ≤ O H := by
  have hn : (bar H ((H ⊓ C t) ⊓ O (C t))).Normal := by
    refine G4c.normal_of_top_le_normalizer fun u _ => ?_
    obtain ⟨c, hc, rfl⟩ := exists_mk_eq_of_isIsolatedIn ht u
    refine G4c.bar_le_normalizer (K := (H ⊓ C t) ⊓ O (C t)) (L := H ⊓ C t) ?_ ⟨c, ⟨c.2, hc⟩, rfl⟩
    intro g hg
    exact inf_normalizer_le_normalizer_inf ⟨le_normalizer hg,
      G4c.le_normalizer_O (C t) (mem_inf.mp hg).2⟩
  have h1 := G4c.eq_bot_of_normal_of_odd_bar hn
    (G4c.odd_card_bar (G4c.odd_card_of_le inf_le_right (G4c.odd_card_O _)))
  exact (G4c.bar_eq_bot_iff (inf_le_left.trans inf_le_left)).mp h1

theorem bar_normal_of_isIsolatedIn {H : Subgroup G} {t : G} (ht : IsIsolatedIn H t)
    {K : Subgroup G} (hK : K ≤ H ⊓ C t)
    (hKn : H ⊓ C t ≤ normalizer ((K ⊔ O (C t) : Subgroup G) : Set G)) : (bar H K).Normal := by
  have hO := inf_O_C_le_O ht
  refine ⟨fun n hn u => ?_⟩
  obtain ⟨⟨k, hkH⟩, hk, rfl⟩ := hn
  obtain ⟨c, hc, rfl⟩ := exists_mk_eq_of_isIsolatedIn ht u
  have hcQ : (c : G) ∈ H ⊓ C t := ⟨c.2, hc⟩
  have hkK : k ∈ K := hk
  have h1 : (c : G) * k * (c : G)⁻¹ ∈ K ⊔ O (C t) :=
    (mem_normalizer_iff.mp (hKn hcQ) k).mp (mem_sup_left hkK)
  obtain ⟨k', hk', o, ho, hko⟩ :=
    G5d.mem_sup_of_le_normalizer' ((hK.trans inf_le_right).trans (G4c.le_normalizer_O (C t))) h1
  have hoQ : o ∈ H ⊓ C t := by
    have e : o = k'⁻¹ * ((c : G) * k * (c : G)⁻¹) := by
      rw [← hko]
      group
    rw [e]
    exact mul_mem (inv_mem (hK hk')) (mul_mem (mul_mem hcQ (hK hkK)) (inv_mem hcQ))
  have hoH : o ∈ O H := hO ⟨hoQ, ho⟩
  refine ⟨⟨k', (mem_inf.mp (hK hk')).1⟩, hk', ?_⟩
  rw [QuotientGroup.mk'_apply, ← map_mul, ← map_inv, ← map_mul, QuotientGroup.mk'_apply,
    QuotientGroup.eq, mem_oddCore_iff]
  have e : (((⟨k', (mem_inf.mp (hK hk')).1⟩ : H)⁻¹ * (c * ⟨k, hkH⟩ * c⁻¹) : H) : G) = o := by
    rw [coe_mul, coe_inv, coe_mul, coe_mul, coe_inv, Subtype.coe_mk, Subtype.coe_mk, ← hko]
    group
  rw [e]
  exact hoH

theorem exists_injective_of_isIsolatedIn {H : Subgroup G} {t : G} (ht : IsIsolatedIn H t)
    (hOt : O H ⊓ C t ≤ O (C t)) :
    ∃ φ : Bar H →* Bar (C t), Function.Injective φ ∧
      ∀ K : Subgroup G, K ≤ H ⊓ C t → (bar H K).map φ = bar (C t) K := by
  set Q := H ⊓ C t with hQ
  let σ : Q →* Bar H := (QuotientGroup.mk' (CFSG.oddCore H)).comp (inclusion inf_le_left)
  let ρ : Q →* Bar (C t) := (QuotientGroup.mk' (CFSG.oddCore (C t))).comp (inclusion inf_le_right)
  have hσ : Function.Surjective σ := by
    intro u
    obtain ⟨c, hc, rfl⟩ := exists_mk_eq_of_isIsolatedIn ht u
    exact ⟨⟨c, c.2, hc⟩, rfl⟩
  have hker : σ.ker = ρ.ker := by
    ext q
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      QuotientGroup.eq_one_iff, mem_oddCore_iff, mem_oddCore_iff]
    change (q : G) ∈ O H ↔ (q : G) ∈ O (C t)
    constructor
    · intro h
      exact hOt ⟨h, (mem_inf.mp q.2).2⟩
    · intro h
      exact inf_O_C_le_O ht ⟨q.2, h⟩
  let e₁ : Q ⧸ σ.ker ≃* Bar H := QuotientGroup.quotientKerEquivOfSurjective σ hσ
  let e₂ : Q ⧸ σ.ker ≃* Q ⧸ ρ.ker := QuotientGroup.quotientMulEquivOfEq hker
  let φ : Bar H →* Bar (C t) :=
    (QuotientGroup.kerLift ρ).comp (e₂.toMonoidHom.comp e₁.symm.toMonoidHom)
  have hφσ : ∀ q : Q, φ (σ q) = ρ q := by
    intro q
    have h1 : e₁.symm (σ q) = (q : Q ⧸ σ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.kerLift ρ (e₂ (e₁.symm (σ q))) = ρ q
    rw [h1, QuotientGroup.quotientMulEquivOfEq_mk, QuotientGroup.kerLift_mk]
  refine ⟨φ, (QuotientGroup.kerLift_injective ρ).comp
    (e₂.injective.comp e₁.symm.injective), fun K hK => ?_⟩
  apply le_antisymm
  · rintro _ ⟨_, ⟨⟨k, hkH⟩, hk, rfl⟩, rfl⟩
    have hkK : k ∈ K := hk
    have e : QuotientGroup.mk' (CFSG.oddCore H) ⟨k, hkH⟩ = σ ⟨k, hK hkK⟩ := rfl
    rw [e, hφσ]
    exact ⟨⟨k, (mem_inf.mp (hK hkK)).2⟩, hkK, rfl⟩
  · rintro _ ⟨⟨k, hkC⟩, hk, rfl⟩
    have hkK : k ∈ K := hk
    refine ⟨σ ⟨k, hK hkK⟩, ⟨⟨k, (mem_inf.mp (hK hkK)).1⟩, hkK, rfl⟩, ?_⟩
    rw [hφσ]
    rfl

theorem exists_isPGroup_card_eq {K₀ OK T : Subgroup G} {L : Type*} [Group L] (f : K₀ →* L)
    (hker : f.ker = OK.subgroupOf K₀) (hOKodd : Odd (Nat.card OK)) (hTK : T ≤ K₀)
    (hT : IsPGroup 2 T) : ∃ P : Subgroup L, IsPGroup 2 P ∧ Nat.card P = Nat.card T := by
  let φ : T →* L := f.comp (inclusion hTK)
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx' : inclusion hTK x ∈ f.ker := hx
    rw [hker, mem_subgroupOf] at hx'
    have h1 := G4c.inf_eq_bot_of_odd_of_isPGroup hOKodd hT
    have h2 : (x : G) ∈ OK ⊓ T := mem_inf.mpr ⟨hx', x.2⟩
    rw [h1, mem_bot] at h2
    exact mem_bot.mpr (Subtype.ext h2)
  let e := MonoidHom.ofInjective hinj
  exact ⟨φ.range, hT.of_equiv e, (Nat.card_congr e.toEquiv).symm⟩

theorem false_of_isIsolatedIn_mem {H K₀ OK T : Subgroup G} {L : Type*} [Group L]
    [IsSimpleGroup L] (f : K₀ →* L) (hf : Function.Surjective f)
    (hker : f.ker = OK.subgroupOf K₀) (hOKodd : Odd (Nat.card OK))
    (hOKn : K₀ ≤ normalizer (OK : Set G)) (hcov : Covers H K₀ OK) (hTK : T ≤ K₀)
    (hT : IsPGroup 2 T) (hT4 : 4 ≤ Nat.card T) {t : G} (ht : IsIsolatedIn H t)
    (htK : t ∈ K₀) : False := by
  have : Finite L := Finite.of_surjective f hf
  obtain ⟨P, hP, hPc⟩ := exists_isPGroup_card_eq f hker hOKodd hTK hT
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hPc
    omega
  have hLodd := eq_bot_of_normal_of_odd hP hP1
  have hF2 := O_inf_le_of_covers f hf hker hOKn hLodd hcov
  have hcen : f ⟨t, htK⟩ ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro l
    obtain ⟨m, rfl⟩ := hf l
    obtain ⟨k, hkH, hkm⟩ := exists_map_eq_of_covers f hker hOKn hcov m
    rw [← hkm]
    have h1 : (k : G) * t * (k : G)⁻¹ * t⁻¹ ∈ OK :=
      hF2 (mem_inf.mpr ⟨ht.conj_mul_inv_mem_O hkH, mul_mem (mul_mem (mul_mem k.2 htK)
        (inv_mem k.2)) (inv_mem htK)⟩)
    have h2 : k * ⟨t, htK⟩ * k⁻¹ * ⟨t, htK⟩⁻¹ ∈ f.ker := by
      rw [hker, mem_subgroupOf]
      exact h1
    rw [MonoidHom.mem_ker] at h2
    simp only [map_mul, map_inv] at h2
    calc f k * f ⟨t, htK⟩ = f k * f ⟨t, htK⟩ * (f k)⁻¹ * (f ⟨t, htK⟩)⁻¹ * (f ⟨t, htK⟩ * f k) := by
          group
      _ = f ⟨t, htK⟩ * f k := by rw [h2, one_mul]
  have ht1 : f ⟨t, htK⟩ ≠ 1 := by
    intro h
    have h1 : (⟨t, htK⟩ : K₀) ∈ f.ker := h
    rw [hker, mem_subgroupOf] at h1
    have h1' : t ∈ OK := h1
    have htt : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht.2.1, pow_two] at this
    have h3 := ht.2.1
    rw [eq_one_of_mul_self_of_odd hOKodd h1' htt, orderOf_one] at h3
    exact absurd h3 (by norm_num)
  rw [center_eq_bot_of_isSimpleGroup hP (hPc ▸ hT4), mem_bot] at hcen
  exact ht1 hcen

theorem false_of_isPGroup_bar {H K₀ OK T : Subgroup G} {L : Type*} [Group L]
    [IsSimpleGroup L] (f : K₀ →* L) (hf : Function.Surjective f)
    (hker : f.ker = OK.subgroupOf K₀) (hOKodd : Odd (Nat.card OK))
    (hOKn : K₀ ≤ normalizer (OK : Set G)) (hcov : Covers H K₀ OK) (hTK : T ≤ K₀)
    (hT : IsPGroup 2 T) (hT4 : 4 ≤ Nat.card T) (hH : IsPGroup 2 (Bar H)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite L := Finite.of_surjective f hf
  obtain ⟨P, hP, hPc⟩ := exists_isPGroup_card_eq f hker hOKodd hTK hT
  have hP1 : P ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hPc
    omega
  have hF2 := O_inf_le_of_covers f hf hker hOKn (eq_bot_of_normal_of_odd hP hP1) hcov
  have hL : IsPGroup 2 L := by
    intro l
    obtain ⟨m, rfl⟩ := hf l
    obtain ⟨k, hkH, hkm⟩ := exists_map_eq_of_covers f hker hOKn hcov m
    obtain ⟨a, ha⟩ := hH (QuotientGroup.mk' (CFSG.oddCore H) ⟨k, hkH⟩)
    refine ⟨a, ?_⟩
    rw [← hkm, ← map_pow]
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_oddCore_iff] at ha
    have h1 : ((k ^ 2 ^ a : K₀) : G) ∈ OK := hF2 (mem_inf.mpr ⟨ha, (k ^ 2 ^ a).2⟩)
    have h2 : k ^ 2 ^ a ∈ f.ker := by
      rw [hker, mem_subgroupOf]
      exact h1
    exact h2
  have : Nontrivial L := IsSimpleGroup.toNontrivial
  have hc := hL.center_nontrivial
  rw [center_eq_bot_of_isSimpleGroup hP (hPc ▸ hT4)] at hc
  exact (not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton (⊥ : Subgroup L))) hc

theorem le_normalizer_sup_O_of_conj {t z g : G} (hg : g * t * g⁻¹ = z) {V : Subgroup G}
    (hV : V ≤ C t) (hVn : (bar (C z) (V.map (G4c.cj g))).Normal) :
    C t ≤ normalizer ((V ⊔ O (C t) : Subgroup G) : Set G) := by
  have hCz : (C t).map (G4c.cj g) = C z := by rw [G4c.map_cj_C, hg]
  have hV' : V.map (G4c.cj g) ≤ C z := hCz ▸ map_mono hV
  have h1 : C z ≤ normalizer ((V.map (G4c.cj g) ⊔ O (C z) : Subgroup G) : Set G) := by
    rw [← normal_subgroupOf_iff_le_normalizer (sup_le hV' (G4c.O_le _)),
      sup_O_subgroupOf_eq_comap hV']
    exact hVn.comap _
  have h2 := map_mono (f := G4c.cj g⁻¹) h1
  rw [G4c.map_cj_normalizer, G4c.map_cj_sup, G4c.map_cj_O, ← hCz, G4c.map_cj_cj_inv,
    G4c.map_cj_cj_inv] at h2
  exact h2

end Isolated

section Generic'

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem exists_bar_mulEquiv (H : Subgroup G) (n : G) :
    ∃ ψ : Bar H ≃* Bar (H.map (G4c.cj n)), ∀ K : Subgroup G,
      (bar H K).map ψ.toMonoidHom = bar (H.map (G4c.cj n)) (K.map (G4c.cj n)) := by
  let e : H ≃* H.map (G4c.cj n) := H.equivMapOfInjective (G4c.cj n) (G4c.cj_injective n)
  have he : (CFSG.oddCore H).map (e : H →* H.map (G4c.cj n)) = CFSG.oddCore (H.map (G4c.cj n)) :=
    G4b.map_oddCore e
  refine ⟨QuotientGroup.congr _ _ e he, fun K => ?_⟩
  apply le_antisymm
  · rintro _ ⟨_, ⟨⟨k, hkH⟩, hk, rfl⟩, rfl⟩
    refine ⟨e ⟨k, hkH⟩, ⟨k, hk, rfl⟩, ?_⟩
    change _ = QuotientGroup.congr _ _ e he (⟨k, hkH⟩ : H)
    rw [QuotientGroup.congr_mk]
    rfl
  · rintro _ ⟨⟨x, hxH'⟩, hx, rfl⟩
    obtain ⟨k, hk, hkx⟩ := hx
    obtain ⟨k', hk'H, hk'x⟩ := hxH'
    have hkk' : k = k' := G4c.cj_injective n (hkx.trans hk'x.symm)
    subst hkk'
    refine ⟨QuotientGroup.mk' _ ⟨k, hk'H⟩, ⟨⟨k, hk'H⟩, hk, rfl⟩, ?_⟩
    change QuotientGroup.congr _ _ e he (⟨k, hk'H⟩ : H) = _
    rw [QuotientGroup.congr_mk]
    congr 1
    exact Subtype.ext hkx

omit [Finite G] in
theorem exists_bar_mulEquiv_of_eq {H K' : Subgroup G} {n : G} (h : H.map (G4c.cj n) = K') :
    ∃ ψ : Bar H ≃* Bar K', ∀ K : Subgroup G,
      (bar H K).map ψ.toMonoidHom = bar K' (K.map (G4c.cj n)) := by
  subst h
  exact exists_bar_mulEquiv H n

theorem isSylowOf_bar_of_sup {H R T : Subgroup G} {F : Subgroup (Bar H)} (S : Sylow 2 G)
    (hSRT : (S : Subgroup G) = R ⊔ T) (hSH : (S : Subgroup G) ≤ H) (hRF : bar H R ⊓ F = ⊥)
    (hRF' : bar H R ⊔ F = ⊤) (hFR : F ≤ centralizer (bar H R : Set (Bar H)))
    (hTF : bar H T ≤ F) : IsSylowOf 2 (bar H T) F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFn := G4c.normal_of_sup hRF' hFR
  have hRH : R ≤ H := le_sup_left.trans (hSRT ▸ hSH)
  have hTH : T ≤ H := le_sup_right.trans (hSRT ▸ hSH)
  have hSb : IsSylowOf 2 (bar H S) ⊤ := by
    have h := isSylowOf_bar (H := H) le_rfl (G4b.isSylowOf_of_sylow_le S hSH)
    rwa [bar_self] at h
  have h1 := hSb.inf_of_le_normalizer le_top (fun x _ => by
    rw [normalizer_eq_top_iff.mpr hFn]
    exact mem_top x)
  have heq : bar H S ⊓ F = bar H T := by
    rw [hSRT, G4c.bar_sup hRH hTH]
    exact le_antisymm (G4c.bar_sup_inf_le hRF hRF' hFR hTF) (le_inf le_sup_right hTF)
  rwa [heq] at h1

omit [Finite G] in
theorem isL2PGL2OrA7OrV4_of_mulEquiv {L M : Type*} [Group L] [Group M] (e : L ≃* M)
    (h : IsL2PGL2OrA7OrV4 M) : IsL2PGL2OrA7OrV4 L := by
  rcases h with h | ⟨p, k, hp, hp2, h3, ⟨f⟩⟩ | h
  · exact Or.inl (isL2OrA7_of_mulEquiv e h)
  · exact Or.inr (Or.inl ⟨p, k, hp, hp2, h3, ⟨e.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨by rw [Nat.card_congr e.toEquiv]; exact h.card_four,
      by rw [Monoid.exponent_eq_of_mulEquiv e]; exact h.exponent_two⟩)

omit [Finite G] in
theorem nonempty_bar_mulEquiv_of_transport {H H' W : Subgroup G} {m : G} (ψ : Bar H' ≃* Bar H)
    (hψ : ∀ K : Subgroup G, (bar H' K).map ψ.toMonoidHom = bar H (K.map (G4c.cj m))) :
    Nonempty (bar H (W.map (G4c.cj m)) ≃* bar H' W) := by
  rw [← hψ W]
  exact ⟨((bar H' W).equivMapOfInjective ψ.toMonoidHom ψ.injective).symm⟩

theorem transport_W {H H' K₀ OK Z A W' : Subgroup G} {m : G} (hH : H'.map (G4c.cj m) = H)
    (hK₀ : K₀.map (G4c.cj m) = K₀) (hOK : OK.map (G4c.cj m) = OK) (hZ : Z.map (G4c.cj m) = Z)
    (hA : A.map (G4c.cj m) = A)
    (h : W' ≤ H' ⊓ K₀ ∧ Z ≤ W' ∧ Covers W' K₀ OK ∧ H' ⊓ K₀ ≤ W' ⊔ (H' ⊓ OK) ∧
      ((W' ⊔ O H').subgroupOf H').Normal ∧ O H' ⊓ W' = W' ⊓ OK ∧
      bar H' (H' ⊓ OK) ≤ centralizer (bar H' W' : Set (Bar H')) ∧
      bar H' (H' ⊓ OK) ≤ centralizer (bar H' A : Set (Bar H'))) :
    ∃ ψ : Bar H' ≃* Bar H, (∀ K : Subgroup G,
        (bar H' K).map ψ.toMonoidHom = bar H (K.map (G4c.cj m))) ∧
      W'.map (G4c.cj m) ≤ H ⊓ K₀ ∧ Z ≤ W'.map (G4c.cj m) ∧ Covers (W'.map (G4c.cj m)) K₀ OK ∧
      H ⊓ K₀ ≤ W'.map (G4c.cj m) ⊔ (H ⊓ OK) ∧
      ((W'.map (G4c.cj m) ⊔ O H).subgroupOf H).Normal ∧
      O H ⊓ W'.map (G4c.cj m) = W'.map (G4c.cj m) ⊓ OK ∧
      bar H (H ⊓ OK) ≤ centralizer (bar H (W'.map (G4c.cj m)) : Set (Bar H)) ∧
      bar H (H ⊓ OK) ≤ centralizer (bar H A : Set (Bar H)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  obtain ⟨ψ, hψ⟩ := exists_bar_mulEquiv_of_eq hH
  have hOH : (O H').map (G4c.cj m) = O H := by rw [G4c.map_cj_O, hH]
  have hHOK : (H' ⊓ OK).map (G4c.cj m) = H ⊓ OK := by rw [G4c.map_cj_inf, hH, hOK]
  refine ⟨ψ, hψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := map_mono (f := G4c.cj m) h1
    rwa [G4c.map_cj_inf, hH, hK₀] at this
  · have := map_mono (f := G4c.cj m) h2
    rwa [hZ] at this
  · have := G5d.covers_map_conj h3 m
    rwa [hK₀, hOK] at this
  · have := map_mono (f := G4c.cj m) h4
    rwa [G4c.map_cj_inf, hH, hK₀, G4c.map_cj_sup, hHOK] at this
  · have hle : W' ⊔ O H' ≤ H' := sup_le (h1.trans inf_le_left) (G4c.O_le H')
    have hle' : W'.map (G4c.cj m) ⊔ O H ≤ H := by
      rw [← hOH, ← G4c.map_cj_sup, ← hH]
      exact map_mono hle
    rw [normal_subgroupOf_iff_le_normalizer hle'] at ⊢
    rw [normal_subgroupOf_iff_le_normalizer hle] at h5
    have := map_mono (f := G4c.cj m) h5
    rwa [G4c.map_cj_normalizer, G4c.map_cj_sup, hOH, hH] at this
  · have := congrArg (Subgroup.map (G4c.cj m)) h6
    rwa [G4c.map_cj_inf, G4c.map_cj_inf, hOH, hOK] at this
  · have := map_mono (f := ψ.toMonoidHom) h7
    rwa [G4b.map_centralizer, hψ, hψ, hHOK] at this
  · have := map_mono (f := ψ.toMonoidHom) h8
    rwa [G4b.map_centralizer, hψ, hψ, hHOK, hA] at this

omit [Finite G] in
theorem transport_L {H H' W V A : Subgroup G} {m : G} (ψ : Bar H' ≃* Bar H)
    (hψ : ∀ K : Subgroup G, (bar H' K).map ψ.toMonoidHom = bar H (K.map (G4c.cj m)))
    (hV : V.map (G4c.cj m) = V) (hA : A.map (G4c.cj m) = A) {L' : Subgroup (Bar H')}
    (h : L'.Normal ∧ bar H' V ≤ L' ∧ L' ⊓ bar H' W = ⊥ ∧
      L' ≤ centralizer (bar H' W : Set (Bar H')) ∧ (IsL2PGL2OrA7OrV4 L' ∨ IsPGroup 2 L') ∧
      L' ⊔ bar H' W ⊔ normalizer (bar H' A : Set (Bar H')) = ⊤) :
    ∃ L : Subgroup (Bar H), L.Normal ∧ bar H V ≤ L ∧ L ⊓ bar H (W.map (G4c.cj m)) = ⊥ ∧
      L ≤ centralizer (bar H (W.map (G4c.cj m)) : Set (Bar H)) ∧
      (IsL2PGL2OrA7OrV4 L ∨ IsPGroup 2 L) ∧
      L ⊔ bar H (W.map (G4c.cj m)) ⊔ normalizer (bar H A : Set (Bar H)) = ⊤ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨L'.map ψ.toMonoidHom, h1.map _ ψ.surjective, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hV, ← hψ V]
    exact map_mono h2
  · rw [← hψ W, ← map_inf_eq _ _ _ ψ.injective, h3, Subgroup.map_bot]
  · rw [← hψ W, ← G4b.map_centralizer]
    exact map_mono h4
  · rcases h5 with h5 | h5
    · exact Or.inl (isL2PGL2OrA7OrV4_of_mulEquiv
        (L'.equivMapOfInjective ψ.toMonoidHom ψ.injective).symm h5)
    · exact Or.inr (h5.map _)
  · have := congrArg (Subgroup.map ψ.toMonoidHom) h6
    rwa [Subgroup.map_sup, Subgroup.map_sup, map_equiv_normalizer_eq, hψ, hψ, hA,
      Subgroup.map_top_of_surjective _ ψ.surjective] at this

theorem le_normalizer_commutator_sup_O (K : Subgroup G) :
    K ≤ normalizer ((⁅O2 K, O2 K⁆ ⊔ O K : Subgroup G) : Set G) := by
  intro g hg
  apply G4c.mem_normalizer_of_map_cj_eq
  rw [G4c.map_cj_sup, G4c.map_cj_commutator,
    G4c.map_cj_eq_of_mem_normalizer (G4c.le_normalizer_O2 K hg),
    G4c.map_cj_eq_of_mem_normalizer (G4c.le_normalizer_O K hg)]

theorem inf_sup_O_eq {H K Ct : Subgroup G} (hKC : K ≤ Ct) (hOK : O K ≤ O Ct)
    (h5 : ⁅O2 Ct, O2 Ct⁆ ⊔ O Ct = ((⁅O2 K, O2 K⁆ ⊔ O K) ⊓ ⁅O2 Ct, O2 Ct⁆) ⊔ O Ct)
    (hcov : Covers H (⁅O2 K, O2 K⁆ ⊔ O K) (O K)) :
    (H ⊓ (⁅O2 K, O2 K⁆ ⊔ O K)) ⊔ O Ct = ⁅O2 Ct, O2 Ct⁆ ⊔ O Ct := by
  have hK₀ : ⁅O2 K, O2 K⁆ ⊔ O K ≤ ⁅O2 Ct, O2 Ct⁆ ⊔ O Ct :=
    sup_le_sup (commutator_mono (G4c.O2_mono hKC) (G4c.O2_mono hKC)) hOK
  apply le_antisymm
  · exact sup_le (inf_le_right.trans hK₀) le_sup_right
  · rw [h5]
    refine sup_le ?_ le_sup_right
    refine inf_le_left.trans (hcov.trans (sup_le le_sup_left ?_))
    exact hOK.trans le_sup_right

theorem bar_map_inf_eq {H K : Subgroup G} {t z g : G} (hg : g * t * g⁻¹ = z) (hKC : K ≤ C t)
    (hOK : O K ≤ O (C t))
    (h5 : ⁅O2 (C t), O2 (C t)⁆ ⊔ O (C t) =
      ((⁅O2 K, O2 K⁆ ⊔ O K) ⊓ ⁅O2 (C t), O2 (C t)⁆) ⊔ O (C t))
    (hcov : Covers H (⁅O2 K, O2 K⁆ ⊔ O K) (O K)) :
    bar (C z) ((H ⊓ (⁅O2 K, O2 K⁆ ⊔ O K)).map (G4c.cj g)) = bar (C z) ⁅O2 (C z), O2 (C z)⁆ := by
  have h := inf_sup_O_eq hKC hOK h5 hcov
  have hCz : (C t).map (G4c.cj g) = C z := by rw [G4c.map_cj_C, hg]
  have h' := congrArg (Subgroup.map (G4c.cj g)) h
  rw [G4c.map_cj_sup, G4c.map_cj_sup, G4c.map_cj_O, G4c.map_cj_commutator, G4c.map_cj_O2,
    hCz] at h'
  have hK₀ : ⁅O2 K, O2 K⁆ ⊔ O K ≤ C t :=
    sup_le ((G4c.commutator_le_of_le (G4c.O2_le K) (G4c.O2_le K)).trans hKC)
      ((G4c.O_le K).trans hKC)
  have hle1 : (H ⊓ (⁅O2 K, O2 K⁆ ⊔ O K)).map (G4c.cj g) ≤ C z := by
    rw [← hCz]
    exact map_mono (inf_le_right.trans hK₀)
  have hle2 : ⁅O2 (C z), O2 (C z)⁆ ≤ C z := G4c.commutator_le_of_le (G4c.O2_le _) (G4c.O2_le _)
  rw [← G4c.bar_sup_O hle1, h', G4c.bar_sup_O hle2]

end Generic'

section Decomposition

variable {B : Type*} [Group B] [Finite B]

omit [Finite B] in
theorem mem_normalizer_of_odd [Finite B] {T V A' K : Subgroup B} {k : ℕ}
    (e : T ≃* DihedralGroup (2 ^ k)) (hk : 2 ≤ k) (hA' : A' ≤ V ⊔ T)
    (hKV : K ≤ centralizer (V : Set B)) :
    ∀ x ∈ K ⊓ normalizer (T : Set B), Odd (orderOf x) → x ∈ normalizer (A' : Set B) := by
  intro x hx hodd
  have hxT := mem_centralizer_of_odd_of_mem_normalizer e hk (mem_inf.mp hx).2 hodd
  have hxV := hKV (mem_inf.mp hx).1
  have hle : V ⊔ T ≤ centralizer ({x} : Set B) := by
    refine sup_le (fun v hv => ?_) (fun t ht => ?_)
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hxV v hv
    · rw [mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.mp hxT t ht
  refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun a ha => ?_)
  exact mem_centralizer_singleton_iff.mp (hle (hA' ha))

theorem le_sup_sup_normalizer {R K F T P A' : Subgroup B}
    (hRK : R ⊓ K = ⊥) (hRK' : R ⊔ K = ⊤) (hKR : K ≤ centralizer (R : Set B))
    (hR : IsPGroup 2 R) (hFK : F ≤ K) (hFP : F ≤ P) (hFn : P ≤ normalizer (F : Set B))
    (hTF : T ≤ F) (hTK : IsSylowOf 2 T K)
    (hodd : ∀ x ∈ K ⊓ normalizer (T : Set B), Odd (orderOf x) → x ∈ normalizer (A' : Set B)) :
    P ≤ (P ⊓ R) ⊔ F ⊔ (P ⊓ normalizer (A' : Set B)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKRn : K ≤ normalizer (R : Set B) := fun k hk => centralizer_le_normalizer _ (hKR hk)
  have hRT : R ≤ centralizer (T : Set B) :=
    le_centralizer_iff.mp ((hTF.trans hFK).trans hKR)
  have hdec : ∀ b : B, ∃ r ∈ R, ∃ k ∈ K, r * k = b := fun b =>
    G5d.mem_sup_of_le_normalizer hKRn (hRK' ▸ mem_top b)
  have hcomm : ∀ r ∈ R, ∀ k ∈ K, r * k = k * r := fun r hr k hk =>
    mem_centralizer_iff.mp (hKR hk) r hr
  have hsplit : ∀ r ∈ R, ∀ k ∈ K, ∀ m : ℕ, (r * k) ^ m = 1 → r ^ m = 1 ∧ k ^ m = 1 := by
    intro r hr k hk m h
    rw [(Commute.mul_pow (hcomm r hr k hk) m)] at h
    have hrm : r ^ m ∈ R ⊓ K := mem_inf.mpr ⟨pow_mem hr m, by
      rw [eq_inv_of_mul_eq_one_left h]
      exact inv_mem (pow_mem hk m)⟩
    rw [hRK, mem_bot] at hrm
    rw [hrm, one_mul] at h
    exact ⟨hrm, h⟩
  have hTFs : IsSylowOf 2 T F := hTK.of_le hTF hFK
  refine (G5d.eq_sup_inf_normalizer_of_isSylowOf hFP hFn hTFs).le.trans (sup_le
    (le_sup_right.trans le_sup_left) fun n hn => ?_)
  have hzp : zpowers n ≤ P ⊓ normalizer (T : Set B) := zpowers_le.mpr hn
  have hq : TauCeti.pPart 2 n ∈ P ⊓ normalizer (T : Set B) := hzp (TauCeti.pPart_mem_zpowers 2 n)
  have hm : TauCeti.pFreePart 2 n ∈ P ⊓ normalizer (T : Set B) :=
    hzp (TauCeti.pFreePart_mem_zpowers 2 n)
  rw [← TauCeti.pPart_mul_pFreePart 2 n]
  refine mul_mem_sup ?_ ?_
  ·
    set q := TauCeti.pPart 2 n
    obtain ⟨r, hr, k, hk, hrk⟩ := hdec q
    obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_zpowers_pPart n)) ⟨q, mem_zpowers q⟩
    have hqa : q ^ 2 ^ a = 1 := by
      have := pow_orderOf_eq_one (⟨q, mem_zpowers q⟩ : zpowers q)
      rw [ha] at this
      exact congrArg Subtype.val this
    rw [← hrk] at hqa
    have hka := (hsplit r hr k hk _ hqa).2
    have hkT : k ∈ normalizer (T : Set B) := by
      have e : k = r⁻¹ * q := by rw [← hrk]; group
      rw [e]
      exact mul_mem (centralizer_le_normalizer _ (hRT (inv_mem hr))) (mem_inf.mp hq).2
    have hk2 : IsPGroup 2 (zpowers k) := by
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hka)
      exact IsPGroup.of_card (n := b) (by rw [Nat.card_zpowers, hb])
    have hkT' : k ∈ T := mem_of_isSylowOf_of_le_normalizer
      (hTK.of_le (le_inf (hTF.trans hFK) le_normalizer) inf_le_left) inf_le_right
      (mem_inf.mpr ⟨hk, hkT⟩) hk2
    have hrP : r ∈ P := by
      have e : r = q * k⁻¹ := by rw [← hrk]; group
      rw [e]
      exact mul_mem (mem_inf.mp hq).1 (inv_mem (hFP (hTF hkT')))
    rw [← hrk]
    exact mul_mem_sup (mem_inf.mpr ⟨hrP, hr⟩) (hTF hkT')
  ·
    set m := TauCeti.pFreePart 2 n
    obtain ⟨r, hr, k, hk, hrk⟩ := hdec m
    have hmo : (r * k) ^ orderOf m = 1 := by
      rw [hrk]
      exact pow_orderOf_eq_one m
    have hr1 : r = 1 := by
      have hro := orderOf_dvd_of_pow_eq_one (hsplit r hr k hk _ hmo).1
      obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp hR) ⟨r, hr⟩
      rw [← Subgroup.orderOf_mk r hr, hb] at hro
      have hb0 : b = 0 := by
        by_contra hb0
        exact (Nat.not_even_iff_odd.mpr (odd_orderOf_pFreePart n))
          (even_iff_two_dvd.mpr ((dvd_pow_self 2 hb0).trans hro))
      rw [hb0, pow_zero, orderOf_eq_one_iff] at hb
      exact congrArg Subtype.val hb
    have hmK : m ∈ K := by rw [← hrk, hr1, one_mul]; exact hk
    exact mem_inf.mpr ⟨(mem_inf.mp hm).1,
      hodd m (mem_inf.mpr ⟨hmK, (mem_inf.mp hm).2⟩) (odd_orderOf_pFreePart n)⟩

end Decomposition

section IsolatedL

variable {G : Type} [Group G] [Finite G]

theorem exists_L_of_isIsolatedIn {H K₀ A V : Subgroup G} {t z g : G} (ht : IsIsolatedIn H t)
    (hOt : O H ⊓ C t ≤ O (C t)) (hg : g * t * g⁻¹ = z)
    {R K T : Subgroup (Bar (C z))} (hRK : R ⊓ K = ⊥) (hRK' : R ⊔ K = ⊤)
    (hKR : K ≤ centralizer (R : Set (Bar (C z)))) (hR : IsPGroup 2 R)
    (hTF : T ≤ ⁅K, K⁆) (hTK : IsSylowOf 2 T K)
    (hK₀ : K₀ ≤ C t) (hWF : bar (C z) ((H ⊓ K₀).map (G4c.cj g)) = ⁅K, K⁆)
    (hAt : A ≤ H ⊓ C t) (hVA : V ≤ A) (hVR : bar (C z) (V.map (G4c.cj g)) ≤ R)
    (hodd : ∀ x ∈ K ⊓ normalizer (T : Set (Bar (C z))), Odd (orderOf x) →
      x ∈ normalizer (bar (C z) (A.map (G4c.cj g)) : Set (Bar (C z)))) :
    ∃ L : Subgroup (Bar H), L.Normal ∧ bar H V ≤ L ∧ L ⊓ bar H (H ⊓ K₀) = ⊥ ∧
      L ≤ centralizer (bar H (H ⊓ K₀) : Set (Bar H)) ∧ IsPGroup 2 L ∧
      L ⊔ bar H (H ⊓ K₀) ⊔ normalizer (bar H A : Set (Bar H)) = ⊤ ∧
      (bar (C z) (V.map (G4c.cj g)) = R → L = bar H V) := by
  obtain ⟨φ₀, hφ₀, hφ₀K⟩ := exists_injective_of_isIsolatedIn ht hOt
  obtain ⟨ψ, hψ⟩ := exists_bar_mulEquiv_of_eq (n := g)
    (show (C t).map (G4c.cj g) = C z by rw [G4c.map_cj_C, hg])
  set Φ : Bar H →* Bar (C z) := ψ.toMonoidHom.comp φ₀ with hΦdef
  have hΦ : Function.Injective Φ := ψ.injective.comp hφ₀
  have hΦK : ∀ K' : Subgroup G, K' ≤ H ⊓ C t →
      (bar H K').map Φ = bar (C z) (K'.map (G4c.cj g)) := by
    intro K' hK'
    rw [hΦdef, ← map_map, hφ₀K K' hK', hψ]
  have hW : H ⊓ K₀ ≤ H ⊓ C t := inf_le_inf_left _ hK₀
  have hWΦ : (bar H (H ⊓ K₀)).map Φ = ⁅K, K⁆ := (hΦK _ hW).trans hWF
  have hFK : ⁅K, K⁆ ≤ K := G4c.commutator_le_of_le le_rfl le_rfl
  have hRKc : R ≤ centralizer (K : Set (Bar (C z))) := le_centralizer_iff.mp hKR
  have hKn : K.Normal := by
    refine G4c.normal_of_top_le_normalizer ?_
    rw [← hRK']
    exact sup_le (hRKc.trans (centralizer_le_normalizer _)) le_normalizer
  have hRn : R.Normal := by
    refine G4c.normal_of_top_le_normalizer ?_
    rw [← hRK']
    exact sup_le le_normalizer (hKR.trans (centralizer_le_normalizer _))
  have hFn : (⁅K, K⁆ : Subgroup (Bar (C z))).Normal := commutator_normal K K
  have hFr : ⁅K, K⁆ ≤ Φ.range := hWΦ ▸ map_le_range Φ _
  refine ⟨R.comap Φ, hRn.comap Φ, ?_, ?_, ?_, hR.comap_of_injective Φ hΦ, ?_, fun hVR' => ?_⟩
  · intro x hx
    rw [mem_comap]
    have h1 : Φ x ∈ (bar H V).map Φ := mem_map_of_mem Φ hx
    rw [hΦK V (hVA.trans hAt)] at h1
    exact hVR h1
  · rw [eq_bot_iff]
    rintro x ⟨hxL, hxW⟩
    have h1 : Φ x ∈ R := hxL
    have h2 : Φ x ∈ ⁅K, K⁆ := hWΦ ▸ mem_map_of_mem Φ hxW
    have h3 : Φ x ∈ R ⊓ K := mem_inf.mpr ⟨h1, hFK h2⟩
    rw [hRK, mem_bot] at h3
    exact mem_bot.mpr (hΦ (h3.trans (map_one Φ).symm))
  · intro x hxL
    rw [mem_centralizer_iff]
    intro y hyW
    apply hΦ
    rw [map_mul, map_mul]
    have h2 : Φ y ∈ K := hFK (hWΦ ▸ mem_map_of_mem Φ hyW)
    exact (mem_centralizer_iff.mp (hKR h2) (Φ x) hxL).symm
  · set A' := bar (C z) (A.map (G4c.cj g)) with hA'
    have hdec : Φ.range ≤ (Φ.range ⊓ R) ⊔ ⁅K, K⁆ ⊔ (Φ.range ⊓ normalizer (A' : Set (Bar (C z)))) :=
      le_sup_sup_normalizer hRK hRK' hKR hR hFK hFr (fun x _ => by
        rw [normalizer_eq_top_iff.mpr hFn]
        exact mem_top x) hTF hTK hodd
    have h1 : (⊤ : Subgroup (Bar H)) ≤
        ((Φ.range ⊓ R) ⊔ ⁅K, K⁆ ⊔ (Φ.range ⊓ normalizer (A' : Set (Bar (C z))))).comap Φ :=
      fun x _ => hdec ⟨x, rfl⟩
    rw [← comap_sup_eq_of_le_range Φ (sup_le inf_le_left hFr) inf_le_left,
      ← comap_sup_eq_of_le_range Φ inf_le_left hFr] at h1
    refine le_antisymm le_top (h1.trans (sup_le (sup_le ?_ ?_) ?_))
    · exact (comap_mono inf_le_right).trans (le_sup_left.trans le_sup_left)
    · rw [← hWΦ, comap_map_eq_self_of_injective hΦ]
      exact le_sup_right.trans le_sup_left
    · refine (comap_mono inf_le_right).trans (le_trans ?_ le_sup_right)
      have hAΦ : A' = (bar H A).map Φ := (hΦK A hAt).symm
      have h2 := le_normalizer_comap (H := (bar H A).map Φ) Φ
      rw [comap_map_eq_self_of_injective hΦ] at h2
      rw [hAΦ]
      exact h2
  · rw [← hVR', ← hΦK V (hVA.trans hAt), comap_map_eq_self_of_injective hΦ]

end IsolatedL

section NonIsolated

variable {G : Type*} [Group G] [Finite G]

theorem nonisolated {H K₀ T V A : Subgroup G} {Lw Lc : Subgroup (Bar H)}
    (hTK : T ≤ H ⊓ K₀) (hT : IsSylowOf 2 T (H ⊓ K₀)) (hVH : V ≤ H) (hV : IsPGroup 2 V)
    (hK₀ : centralizer (V : Set G) ≤ normalizer (K₀ : Set G))
    (hLw : Lw.Normal) (hinf : Lc ⊓ Lw = ⊥) (hcent : Lw ≤ centralizer (Lc : Set (Bar H)))
    (htop : ⊤ = (Lc ⊔ Lw) ⊔ normalizer (bar H A : Set (Bar H)))
    (hTL : IsSylowOf 2 (bar H T) Lw) (hVL : bar H V ≤ Lc)
    (hodd : ∀ x ∈ Lw ⊓ normalizer (bar H T : Set (Bar H)), Odd (orderOf x) →
      x ∈ normalizer (bar H A : Set (Bar H))) :
    bar H (genW H K₀ T) ≤ Lw ∧ (bar H (genW H K₀ T)).Normal ∧
      Lc ⊓ bar H (genW H K₀ T) = ⊥ ∧ Lc ≤ centralizer (bar H (genW H K₀ T) : Set (Bar H)) ∧
      Lc ⊔ bar H (genW H K₀ T) ⊔ normalizer (bar H A : Set (Bar H)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV : Lw ≤ centralizer (bar H V : Set (Bar H)) := hcent.trans (centralizer_le hVL)
  have h1 := bar_genW_le (K₀ := K₀) hTK hLw hTL
  have h2 := bar_genW_normal hTK hT hVH hV hK₀ hLw hTL hLV
  set W := bar H (genW H K₀ T) with hW
  refine ⟨h1, h2, le_bot_iff.mp ((inf_le_inf_left _ h1).trans hinf.le),
    (le_centralizer_iff.mp hcent).trans (centralizer_le h1), le_antisymm le_top ?_⟩
  have hTW : bar H T ≤ W := G4c.bar_mono le_genW
  have hLwW : Lw ≤ normalizer (W : Set (Bar H)) := fun x _ =>
    G4c.mem_normalizer_of_map_cj_eq (by
      refine le_antisymm ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        exact h2.conj_mem w hw x
      · intro w hw
        refine ⟨x⁻¹ * w * x⁻¹⁻¹, h2.conj_mem w hw x⁻¹, ?_⟩
        rw [G4c.cj_apply]
        group)
  have hfr := G5d.eq_sup_inf_normalizer_of_isSylowOf h1 hLwW (hTL.of_le hTW h1)
  have hN : Lw ⊓ normalizer (bar H T : Set (Bar H)) ≤
      bar H T ⊔ normalizer (bar H A : Set (Bar H)) := by
    intro n hn
    have hzp : zpowers n ≤ Lw ⊓ normalizer (bar H T : Set (Bar H)) := zpowers_le.mpr hn
    rw [← TauCeti.pPart_mul_pFreePart 2 n]
    refine mul_mem_sup ?_ (hodd _ (hzp (TauCeti.pFreePart_mem_zpowers 2 n))
      (odd_orderOf_pFreePart n))
    exact mem_of_isSylowOf_of_le_normalizer
      (hTL.of_le (le_inf hTL.le le_normalizer) inf_le_left) inf_le_right
      (hzp (TauCeti.pPart_mem_zpowers 2 n)) (isPGroup_zpowers_pPart n)
  have hLw : Lw ≤ W ⊔ normalizer (bar H A : Set (Bar H)) := by
    rw [hfr]
    exact sup_le le_sup_left (hN.trans (sup_le (hTW.trans le_sup_left) le_sup_right))
  rw [htop]
  refine sup_le (sup_le (le_sup_left.trans le_sup_left) (hLw.trans ?_)) le_sup_right
  exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

end NonIsolated

section Setting

variable {G : Type} [Group G] [Finite G] (𝔖 : Sec4Setting G) {A : Subgroup G}

theorem exists_conj_isSylowOf (hAS : A ≤ 𝔖.S) (hA : IsE16 A) {H : Subgroup G} (hAH : A ≤ H) :
    ∃ n ∈ normalizer (A : Set G),
      IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H.map (G4c.cj n)) (H.map (G4c.cj n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA2 : IsPGroup 2 A := G5d.isPGroup_of_isE16 hA
  obtain ⟨Q, hQ⟩ := (hA2.comap_subtype (K := H)).exists_le_sylow
  set P : Subgroup G := (Q : Subgroup H).map H.subtype with hPdef
  have hPH : IsSylowOf 2 P H := ⟨Q, rfl⟩
  have hAP : A ≤ P := fun a ha => ⟨⟨a, hAH ha⟩, hQ ha, rfl⟩
  obtain ⟨c, -, hc⟩ := G4c.exists_mem_map_cj_le 𝔖.S le_top (le_top : P ≤ ⊤) hPH.isPGroup
  have hAc : A.map (G4c.cj c) ≤ 𝔖.S := (map_mono hAP).trans hc
  obtain ⟨s, hs, hsA⟩ := Sec3Setting.lemma_3_1 𝔖.toSec3Setting A (A.map (G4c.cj c)) hAS hAc hA
    (G4b.IsE16.map hA (MulAut.conj c)) c rfl
  have hSs : (𝔖.S : Subgroup G).map (G4c.cj s⁻¹) = 𝔖.S :=
    G4c.map_cj_eq_of_mem_normalizer (le_normalizer (inv_mem hs))
  refine ⟨s⁻¹ * c, ?_, ?_⟩
  · apply G4c.mem_normalizer_of_map_cj_eq
    have hsA' : A.map (G4c.cj s) = A.map (G4c.cj c) := hsA
    rw [← G4c.map_cj_map_cj, ← hsA', G4c.map_cj_map_cj, inv_mul_cancel]
    exact G4b.map_conj_one A
  · have hP' : IsSylowOf 2 (P.map (G4c.cj (s⁻¹ * c))) (H.map (G4c.cj (s⁻¹ * c))) :=
      isSylowOf_map_hom hPH _
    have hP'S : P.map (G4c.cj (s⁻¹ * c)) ≤ 𝔖.S := by
      rw [← G4c.map_cj_map_cj, ← hSs]
      exact map_mono hc
    have hS2 : IsPGroup 2 ↥((𝔖.S : Subgroup G) ⊓ H.map (G4c.cj (s⁻¹ * c))) :=
      𝔖.S.isPGroup'.to_le (inf_le_left : (𝔖.S : Subgroup G) ⊓ H.map (G4c.cj (s⁻¹ * c)) ≤ 𝔖.S)
    rw [hP'.eq_of_le (le_inf hP'S hP'.le) inf_le_right hS2]
    exact hP'

omit [Finite G] in
theorem map_cj_le_of_involutions {D : Subgroup G} (hD : IsDih D) {g : G}
    (h : ∀ d ∈ D, orderOf d = 2 → g * d * g⁻¹ ∈ D) : D.map (G4c.cj g) ≤ D := by
  obtain ⟨a, -, ⟨e⟩⟩ := hD
  have hinv : ∀ i : ZMod (2 ^ a), orderOf ((e.symm (DihedralGroup.sr i) : D) : G) = 2 := by
    intro i
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  rintro _ ⟨x, hx, rfl⟩
  rw [G4c.cj_apply]
  have hx' : (⟨x, hx⟩ : D) = e.symm (e ⟨x, hx⟩) := (e.symm_apply_apply _).symm
  rcases he : e ⟨x, hx⟩ with i | i
  · have hxi : x = ((e.symm (DihedralGroup.sr 0) : D) : G) *
        ((e.symm (DihedralGroup.sr i) : D) : G) := by
      rw [← coe_mul, ← map_mul, DihedralGroup.sr_mul_sr, sub_zero, ← he, e.symm_apply_apply]
    rw [hxi, show ∀ u v : G, g * (u * v) * g⁻¹ = (g * u * g⁻¹) * (g * v * g⁻¹) by
      intro u v; group]
    exact mul_mem (h _ (e.symm _).2 (hinv 0)) (h _ (e.symm _).2 (hinv i))
  · have hxi : x = ((e.symm (DihedralGroup.sr i) : D) : G) := by
      rw [← he, e.symm_apply_apply]
    rw [hxi]
    exact h _ (e.symm _).2 (hinv i)

theorem le_of_covers {H K₀ OK R : Subgroup G} (hR : R = 𝔖.S₁ ∨ R = 𝔖.S₂)
    (hRK : IsSylowOf 2 R K₀) (hOKodd : Odd (Nat.card OK))
    (hOKn : K₀ ≤ normalizer (OK : Set G)) (hcov : Covers H K₀ OK)
    (hsyl : IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H) : R ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd ((H ⊓ K₀).relIndex K₀) := by
    set U : Subgroup K₀ := (H ⊓ K₀).subgroupOf K₀
    set N : Subgroup K₀ := OK.subgroupOf K₀
    have : N.Normal := normal_subgroupOf_of_le_normalizer hOKn
    have htop : N ⊔ U = ⊤ := by
      refine eq_top_iff.mpr fun k _ => ?_
      obtain ⟨h, hh, o, ho, hho⟩ :=
        G5d.mem_sup_of_le_normalizer' (inf_le_right.trans hOKn) (hcov k.2)
      have hoK : o ∈ K₀ := by
        have e : o = h⁻¹ * k := by rw [← hho]; group
        rw [e]
        exact mul_mem (inv_mem (mem_inf.mp hh).2) k.2
      have e : k = ⟨h, (mem_inf.mp hh).2⟩ * ⟨o, hoK⟩ := Subtype.ext hho.symm
      rw [e, sup_comm]
      exact mul_mem_sup (show (⟨h, (mem_inf.mp hh).2⟩ : K₀) ∈ U from hh)
        (show (⟨o, hoK⟩ : K₀) ∈ N from ho)
    have h1 : U.relIndex ⊤ = U.relIndex N := by
      rw [← htop, relIndex_sup_eq_relIndex_of_normal N U]
    have h2 : U.relIndex N ∣ Nat.card OK :=
      (relIndex_dvd_card U N).trans (G4c.card_subgroupOf_dvd K₀ OK)
    change Odd U.index
    rw [← relIndex_top_right, h1]
    exact hOKodd.of_dvd_nat h2
  obtain ⟨P, hP⟩ := exists_isSylowOf 2 (H ⊓ K₀)
  have hPK : IsSylowOf 2 P K₀ := by
    rw [isSylowOf_iff] at hP ⊢
    refine ⟨hP.1.trans inf_le_right, hP.2.1, fun h => ?_⟩
    rw [← relIndex_mul_relIndex P (H ⊓ K₀) K₀ hP.1 inf_le_right] at h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h | h
    · exact hP.2.2 h
    · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  obtain ⟨c, -, hc⟩ := exists_mem_map_conj_le_of_isSylowOf hPK hRK.le hRK.isPGroup
  have hRcH : R.map (G4c.cj c) ≤ H := hc.trans (hP.le.trans inf_le_left)
  obtain ⟨h, hh, hRh⟩ := exists_mem_map_conj_le_of_isSylowOf hsyl hRcH (hRK.isPGroup.map _)
  have hRS : R.map (G4c.cj (h * c)) ≤ 𝔖.S := by
    rw [← G4c.map_cj_map_cj]
    exact hRh.trans inf_le_left
  have hRR : R.map (G4c.cj (h * c)) ≤ R := by
    have h312 := 𝔖.toSec3Setting.lemma_3_12 𝔖.fusion R (h * c) hRS
    rcases hR with rfl | rfl
    · exact map_cj_le_of_involutions 𝔖.decomp.dih₁ (h312.1 le_rfl)
    · exact map_cj_le_of_involutions 𝔖.decomp.isDih₂ (h312.2 le_rfl)
  have heq : R.map (G4c.cj (h * c)) = R :=
    eq_of_le_of_card_ge hRR (by rw [G4c.card_map_cj])
  rw [← heq, ← G4c.map_cj_map_cj]
  rintro _ ⟨y, hy, rfl⟩
  rw [G4c.cj_apply]
  exact mul_mem (mul_mem hh (hRcH hy)) (inv_mem hh)

theorem isSylowOf_sup_inf {H : Subgroup G} (hsyl : IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H)
    (h : 𝔖.S₁ ≤ H ∨ 𝔖.S₂ ≤ H) : IsSylowOf 2 ((𝔖.S₁ ⊓ H) ⊔ (𝔖.S₂ ⊓ H)) H := by
  have heq : (𝔖.S₁ ⊓ H) ⊔ (𝔖.S₂ ⊓ H) = (𝔖.S : Subgroup G) ⊓ H := by
    apply le_antisymm
    · exact sup_le (inf_le_inf_right _ 𝔖.decomp.le_left) (inf_le_inf_right _ 𝔖.decomp.le_right)
    · rintro x ⟨hxS, hxH⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := 𝔖.decomp.mem_iff.mp hxS
      rcases h with h | h
      · have hb' : b ∈ H := by simpa using H.mul_mem (H.inv_mem (h ha)) hxH
        exact mul_mem_sup (mem_inf.mpr ⟨ha, h ha⟩) (mem_inf.mpr ⟨hb, hb'⟩)
      · have ha' : a ∈ H := by simpa using H.mul_mem hxH (H.inv_mem (h hb))
        exact mul_mem_sup (mem_inf.mpr ⟨ha, ha'⟩) (mem_inf.mpr ⟨hb, h hb⟩)
  rw [heq]
  exact hsyl

theorem M_ne_top (hAS : A ≤ 𝔖.S) (hA : IsE16 A) : 𝔖.M A ≠ ⊤ := by
  intro hM
  have hz := G4b.z₁_mem_X 𝔖 hAS hA
  have hX : 𝔖.X A ≤ zpowers 𝔖.z₁ := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · obtain ⟨g, hg⟩ := isConj_iff.mp (𝔖.fusion.conj₁ 𝔖.z₁ 𝔖.hz₁.1 x hx.2 𝔖.hz₁.2.1
        (G4b.orderOf_eq_two_of_isE16 hA hx.1 hx1))
      have hgM : g ∈ 𝔖.M A := hM ▸ mem_top g
      have hgz : g * 𝔖.z₁ * g⁻¹ = 𝔖.z₁ := by
        rw [← mem_centralizer_iff.mp hgM 𝔖.z₁ hz]
        group
      rw [← hg, hgz]
      exact mem_zpowers _
  have h1 := card_le_of_le hX
  have h4 : Nat.card (𝔖.X A) = 4 := (G4b.isKleinFour_X 𝔖 hAS hA).card_four
  rw [Nat.card_zpowers, 𝔖.hz₁.2.1, h4] at h1
  omega

theorem N_ne_top (hAS : A ≤ 𝔖.S) (hA : IsE16 A) : 𝔖.N A ≠ ⊤ := by
  intro hN
  have hz := G4b.z₂_mem_Y 𝔖 hAS hA
  have hY : 𝔖.Y A ≤ zpowers 𝔖.z₂ := by
    intro y hy
    by_cases hy1 : y = 1
    · rw [hy1]
      exact one_mem _
    · obtain ⟨g, hg⟩ := isConj_iff.mp (𝔖.fusion.conj₂ 𝔖.z₂ 𝔖.hz₂.1 y hy.2 𝔖.hz₂.2.1
        (G4b.orderOf_eq_two_of_isE16 hA hy.1 hy1))
      have hgN : g ∈ 𝔖.N A := hN ▸ mem_top g
      have hgz : g * 𝔖.z₂ * g⁻¹ = 𝔖.z₂ := by
        rw [← mem_centralizer_iff.mp hgN 𝔖.z₂ hz]
        group
      rw [← hg, hgz]
      exact mem_zpowers _
  have h1 := card_le_of_le hY
  have h4 : Nat.card (𝔖.Y A) = 4 := (G4b.isKleinFour_Y 𝔖 hAS hA).card_four
  rw [Nat.card_zpowers, 𝔖.hz₂.2.1, h4] at h1
  omega

theorem exists_isIsolatedIn_mem_A (hAS : A ≤ 𝔖.S) (hA : IsE16 A) {H : Subgroup G}
    (hAH : A ≤ H) (hsyl : IsSylowOf 2 ((𝔖.S : Subgroup G) ⊓ H) H) {t : G}
    (ht : IsIsolatedIn H t) : ∃ t' ∈ A, IsIsolatedIn H t' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht.2.1, pow_one])
  obtain ⟨c, hc, hct⟩ := exists_mem_conj_mem_of_isSylowOf hsyl ht.1 ht2
  have hHc : H.map (MulAut.conj c).toMonoidHom = H :=
    G4c.map_cj_eq_of_mem_normalizer (le_normalizer hc)
  have ht' : IsIsolatedIn H (c * t * c⁻¹) := hHc ▸ ht.map_conj c
  refine ⟨c * t * c⁻¹, ?_, ht'⟩
  rw [← 𝔖.decomp.inf_centralizer_e16 (𝔖.decomp.sup_eq ▸ hAS) hA]
  refine mem_inf.mpr ⟨(𝔖.decomp.sup_eq).symm ▸ (mem_inf.mp hct).1,
    mem_centralizer_iff.mpr fun a ha => ?_⟩
  have h1 := ht'.conj_mul_inv_mem_O (hAH ha)
  have h2 : a * (c * t * c⁻¹) * a⁻¹ * (c * t * c⁻¹)⁻¹ ∈ (𝔖.S : Subgroup G) :=
    mul_mem (mul_mem (mul_mem (hAS ha) (mem_inf.mp hct).1) (inv_mem (hAS ha)))
      (inv_mem (mem_inf.mp hct).1)
  have h3 := G4c.inf_eq_bot_of_odd_of_isPGroup (G4c.odd_card_O H) 𝔖.S.isPGroup'
  have h4 : a * (c * t * c⁻¹) * a⁻¹ * (c * t * c⁻¹)⁻¹ = 1 := by
    rw [← mem_bot, ← h3]
    exact mem_inf.mpr ⟨h1, h2⟩
  calc a * (c * t * c⁻¹) = a * (c * t * c⁻¹) * a⁻¹ * (c * t * c⁻¹)⁻¹ * ((c * t * c⁻¹) * a) := by
        group
    _ = (c * t * c⁻¹) * a := by rw [h4, one_mul]

theorem isPGroup_bar_of_isIsolatedIn (hAS : A ≤ 𝔖.S) (hA : IsE16 A)
    (h317 : HasNormalTwoComplement (C (𝔖.z₁ * 𝔖.z₂))) {H : Subgroup G} {t : G}
    (ht : IsIsolatedIn H t) (htA : t ∈ A) (htX : t ∉ 𝔖.X A) (htY : t ∉ 𝔖.Y A) :
    IsPGroup 2 (Bar H) := by
  intro u
  obtain ⟨c, hc, rfl⟩ := exists_mk_eq_of_isIsolatedIn ht u
  set x : G := (c : G) with hx
  have hzx : zpowers x ≤ H ⊓ C t := zpowers_le.mpr (mem_inf.mpr ⟨c.2, hc⟩)
  have hm : TauCeti.pFreePart 2 x ∈ O H := by
    have hmz := TauCeti.pFreePart_mem_zpowers 2 x
    have hD : zpowers (TauCeti.pFreePart 2 x) ≤ O (C t) :=
      G4c.le_O_C_of_isConj (G4c.isConj_z₁z₂ hAS hA htA htX htY) h317
        ((zpowers_le.mpr (hzx hmz)).trans inf_le_right)
        (by rw [Nat.card_zpowers]; exact odd_orderOf_pFreePart x)
    exact inf_O_C_le_O ht (mem_inf.mpr ⟨hzx hmz, hD (mem_zpowers _)⟩)
  have hp : TauCeti.pPart 2 x ∈ H := zpowers_le.mpr c.2 (TauCeti.pPart_mem_zpowers 2 x)
  have hf : TauCeti.pFreePart 2 x ∈ H := zpowers_le.mpr c.2 (TauCeti.pFreePart_mem_zpowers 2 x)
  have hcx : c = ⟨TauCeti.pPart 2 x, hp⟩ * ⟨TauCeti.pFreePart 2 x, hf⟩ :=
    Subtype.ext (TauCeti.pPart_mul_pFreePart 2 x).symm
  have hf1 : QuotientGroup.mk' (CFSG.oddCore H) ⟨TauCeti.pFreePart 2 x, hf⟩ = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_oddCore_iff]
    exact hm
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_zpowers_pPart x))
    ⟨TauCeti.pPart 2 x, mem_zpowers _⟩
  refine ⟨a, ?_⟩
  rw [hcx, map_mul, hf1, mul_one, ← map_pow]
  have h1 : (⟨TauCeti.pPart 2 x, hp⟩ : H) ^ 2 ^ a = 1 := by
    apply Subtype.ext
    rw [coe_pow, Subtype.coe_mk, coe_one]
    have := pow_orderOf_eq_one (⟨TauCeti.pPart 2 x, mem_zpowers _⟩ : zpowers (TauCeti.pPart 2 x))
    rw [ha] at this
    exact congrArg Subtype.val this
  rw [h1, map_one]

theorem M_le_normalizer_M₀ : 𝔖.M A ≤ normalizer (𝔖.M₀ A : Set G) :=
  le_normalizer_commutator_sup_O (𝔖.M A)

theorem N_le_normalizer_N₀ : 𝔖.N A ≤ normalizer (𝔖.N₀ A : Set G) :=
  le_normalizer_commutator_sup_O (𝔖.N A)

end Setting

end G5one

end CFSG.GH72
