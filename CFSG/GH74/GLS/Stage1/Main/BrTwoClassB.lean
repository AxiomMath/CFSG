module

public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassA
public import CFSG.GH74.GLS.Stage1.Main.BrTwoClassF
public import CFSG.GH74.GLS.Stage1.Main.Basic
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Main

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.Stage1.Thm3.Sec7
  CFSG.GH74.GLS.Stage1.Thm3.Sec8 CFSG.GH74.GLS.Stage1.Thm2.Recip CFSG.GH74.GLS.Stage1.Thm6.Prod
  CFSG.GH74.GLS.Stage2.Final CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement Pointwise

structure TwoClassCore (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G)
    (L₁ L₂ : Subgroup (CentralizerBar z)) (q : ℕ) (x : G) : Prop where
  x_mem : x ∈ S
  x_inv : orderOf x = 2
  x_nonCentral : ¬ IsCentralInvolution x
  classes : ∀ u : G, orderOf u = 2 → IsConj z u ∨ IsConj x u
  x_normal : ∀ s ∈ S, ∀ w ∈ zpowers z ⊔ zpowers x, s * w * s⁻¹ ∈ zpowers z ⊔ zpowers x
  coset : ∀ g ∈ LC z ⊔ S, ∃ l ∈ LC z, IsConj z (g * l)
  invol_L : ∀ u ∈ LC z, orderOf u = 2 → u ≠ z →
    IsConj x u ∧ ∀ v ∈ LC z, orderOf v = 2 → v ≠ z → IVK.ConjUnder (LC z) u v
  swap_exists : ∃ t ∈ S, IsConj z t ∧ Swaps z t L₁ L₂
  swap_a : ∀ t ∈ S, IsConj z t → Swaps z t L₁ L₂ → IsConj x (t * z)
  swap_b : ∀ t ∈ S, IsConj z t → Swaps z t L₁ L₂ → IVK.IsL2 ↥(layer ↥(CL z t)) (fun r => r = q)
  swap_c : ∀ t ∈ S, IsConj z t → Swaps z t L₁ L₂ →
    (S ⊓ centralizer ({t} : Set G) = S ⊓ normalizer ((zpowers z ⊔ zpowers t : Subgroup G) : Set G) ∧
      ∃ D : Subgroup G, IsInternalDirectProduct (zpowers z ⊔ zpowers t) D
        (S ⊓ centralizer ({t} : Set G)) ∧ IsDihedral ↥D)
  swap_e : ∀ t ∈ S, IsConj z t → Swaps z t L₁ L₂ →
    ∃ V : Subgroup G, V ≤ LC z ∧ IVK.IsFourSubgroup V ∧
      (AutOrd (Cen z) V = 3 ∨ AutOrd (Cen z) V = 6) ∧ ∀ v ∈ V, t * v = v * t

theorem TwoClassData.of_core {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {q : ℕ} {x : G} (hc : TwoClassCore G z S L₁ L₂ q x) :
    TwoClassData G z S L₁ L₂ q x :=
  ⟨hc.x_mem, hc.x_inv, hc.x_nonCentral, hc.classes, hc.x_normal, hc.coset, hc.invol_L,
    hc.swap_exists, fun t ht htc hsw =>
      ⟨hc.swap_a t ht htc hsw, hc.swap_b t ht htc hsw, hc.swap_c t ht htc hsw,
        hc.swap_e t ht htc hsw⟩⟩

section Helpers

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem imgBar_conjugate {K : Subgroup G} (hK : K ≤ Cz z) {t : G} (ht : t ∈ Cz z) :
    imgBar z (conjugate K t) = conjugate (imgBar z K) (toBar z ⟨t, ht⟩) := by
  have hKt : conjugate K t ≤ Cz z := by
    rintro _ ⟨k, hk, rfl⟩
    show t⁻¹ * k * t⁻¹⁻¹ ∈ Cz z
    exact (Cz z).mul_mem ((Cz z).mul_mem ((Cz z).inv_mem ht) (hK hk))
      ((Cz z).inv_mem ((Cz z).inv_mem ht))
  have key : ∀ (k : G) (hk : k ∈ K),
      piC z ⟨t⁻¹ * k * t⁻¹⁻¹, hKt ⟨k, hk, rfl⟩⟩ =
        (toBar z ⟨t, ht⟩)⁻¹ * piC z ⟨k, hK hk⟩ * ((toBar z ⟨t, ht⟩)⁻¹)⁻¹ := by
    intro k hk
    have : (⟨t⁻¹ * k * t⁻¹⁻¹, hKt ⟨k, hk, rfl⟩⟩ : ↥(Cz z)) =
        (⟨t, ht⟩ : ↥(Cz z))⁻¹ * ⟨k, hK hk⟩ * ((⟨t, ht⟩ : ↥(Cz z))⁻¹)⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, map_inv]
    rfl
  ext x
  rw [mem_imgBar hKt]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk, rfl⟩ := hy
    exact ⟨piC z ⟨k, hK hk⟩, piC_mem_imgBar hK hk, (key k hk).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨k, hk, rfl⟩ := (mem_imgBar hK).1 hy
    refine ⟨t⁻¹ * k * t⁻¹⁻¹, ⟨k, hk, rfl⟩, ?_⟩
    exact (key k hk)

omit [Finite G] in
theorem swaps_of_interchanges {K₁ K₂ : Subgroup G} (hK₁ : K₁ ≤ Cz z) (hK₂ : K₂ ≤ Cz z) {t : G}
    (ht : t ∈ Cz z) (h : Interchanges t K₁ K₂) : Swaps z t (imgBar z K₁) (imgBar z K₂) := by
  refine ⟨ht, ?_, ?_⟩
  · rw [← imgBar_conjugate hK₁ ht, h.1]
  · rw [← imgBar_conjugate hK₂ ht, h.2]

end Helpers

section Cfg

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {q : ℕ}

theorem cfg7_of_std (hII : II4_4_4_center) (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6)
    (hpnf : P_normal_four) (hL44 : Lemma4_4) (hL45 : Lemma4_5) (hstd : Std4 G z S K₁ K₂)
    (hnf : ∀ u ∈ Pz S z, IsConj z u → u = z) (hodd : Odd q) (h5 : 5 ≤ q) (hq₁ : HatSL2 K₁ q)
    (hq₂ : HatSL2 K₂ q) : ∃ t u : G, Cfg7 G z S K₁ K₂ t u q := by
  have hs6 : Std6 G z S := ⟨hstd.simple, hstd.rank, hstd.rank_le, hstd.gen4, hstd.classical, hstd.thm2, hstd.sylow, hstd.kgh⟩
  obtain ⟨ha, hb, -, hd⟩ := h61 G z S hs6
  have hr₁ := hstd.comp_rigid (K := K₁) (Or.inl rfl)
  have hr₂ := hstd.comp_rigid (K := K₂) (Or.inr rfl)
  have ha₁ := ha K₁ hr₁
  have ha₂ := ha K₂ hr₂
  have hb₁ := hb K₁ hr₁
  have hb₂ := hb K₂ hr₂
  have hd₁ := hd K₁ hr₁
  have hd₂ := hd K₂ hr₂
  obtain ⟨hQ, -, -⟩ := h41 G z S K₁ K₂ hstd
  have hp66 := h66 G z S K₁ K₂ hstd ha₁ ha₂ hb₁ hb₂
  have hstd7 : Std7 G z S K₁ K₂ := ⟨hstd, ha₁, ha₂, hb₁, hb₂, hd₁, hd₂, hQ, hp66, hnf⟩
  have hM := m4_of_std hII hstd
  have hzP : z ∈ Pz S z := ⟨hM.z_mem_S, by
    rw [hstd.rigidProduct_eq]
    exact mem_sup_left (hM.z_mem_comp (Or.inl rfl))⟩
  have hA : Hyp4A S z := by
    intro x hx hxc
    apply hnf x _ hxc
    unfold Rz at hx
    rw [hQ] at hx
    exact sup_le le_rfl (zpowers_le.2 hzP) hx
  obtain ⟨t, htS, htc, htne, htint⟩ := hL44 G z S K₁ K₂ hstd hA
  obtain ⟨-, htfus, htz⟩ := hL45 G z S K₁ K₂ hstd hA t htS htc htne htint
  obtain ⟨u, huP, huo, hune, hunorm⟩ := hpnf G z S K₁ K₂ ⟨hstd, hQ, hb₁, hb₂⟩
  exact ⟨t, u, hstd7, ⟨htS, htc, htne, htint, htfus, htz, huP, huo, hune, hunorm, hodd, h5, hq₁,
    hq₂⟩⟩

end Cfg

section Swap

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {q : ℕ}

theorem hyp4A_of_std7 (hII : II4_4_4_center) (h : Std7 G z S K₁ K₂) : Hyp4A S z := by
  have hM := m4_of_std hII h.std
  have hzP : z ∈ Pz S z := ⟨hM.z_mem_S, by
    rw [h.std.rigidProduct_eq]
    exact mem_sup_left (hM.z_mem_comp (Or.inl rfl))⟩
  intro x hx hxc
  apply h.nonfused x _ hxc
  unfold Rz at hx
  rw [h.hQ] at hx
  exact sup_le le_rfl (zpowers_le.2 hzP) hx

theorem interchanges_of_swaps (hs : Std4 G z S K₁ K₂) (hA12 : imgBar z K₁ ≠ imgBar z K₂)
    (hK₁ : K₁ ≤ Cz z) (hK₂ : K₂ ≤ Cz z) {t : G} (ht : t ∈ Cz z)
    (h : Swaps z t (imgBar z K₁) (imgBar z K₂)) : Interchanges t K₁ K₂ := by
  obtain ⟨ht', h1, h2⟩ := h
  have hr₁ := hs.comp_rigid (K := K₁) (Or.inl rfl)
  have hr₂ := hs.comp_rigid (K := K₂) (Or.inr rfl)
  have hc₁ := isRigidRankOneComp_cmap hr₁ (inv_mem ht)
  have hc₂ := isRigidRankOneComp_cmap hr₂ (inv_mem ht)
  have hmem₁ : cmap t⁻¹ K₁ ∈ ({K₁, K₂} : Set (Subgroup G)) := by
    rw [← hs.comps]
    exact hc₁
  have hmem₂ : cmap t⁻¹ K₂ ∈ ({K₁, K₂} : Set (Subgroup G)) := by
    rw [← hs.comps]
    exact hc₂
  have e₁ : imgBar z (conjugate K₁ t) = imgBar z K₂ := by
    rw [imgBar_conjugate hK₁ ht]
    exact h1
  have e₂ : imgBar z (conjugate K₂ t) = imgBar z K₁ := by
    rw [imgBar_conjugate hK₂ ht]
    exact h2
  have hcj₁ : conjugate K₁ t = cmap t⁻¹ K₁ := rfl
  have hcj₂ : conjugate K₂ t = cmap t⁻¹ K₂ := rfl
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem₁ hmem₂
  refine ⟨?_, ?_⟩
  · rcases hmem₁ with h | h
    · exfalso
      rw [hcj₁, h] at e₁
      exact hA12 e₁
    · rw [hcj₁]
      exact h
  · rcases hmem₂ with h | h
    · rw [hcj₂]
      exact h
    · exfalso
      rw [hcj₂, h] at e₂
      exact hA12 e₂.symm

theorem cfg7_of_swap (hII : II4_4_4_center) (hL45 : Lemma4_5) {t u : G}
    (hcfg : Cfg7 G z S K₁ K₂ t u q) {t₀ : G} (ht₀S : t₀ ∈ S) (ht₀c : IsConj z t₀) (ht₀ne : t₀ ≠ z)
    (hint : Interchanges t₀ K₁ K₂) : Cfg7 G z S K₁ K₂ t₀ u q := by
  have hA := hyp4A_of_std7 hII hcfg.std
  obtain ⟨-, hfus, htz⟩ := hL45 G z S K₁ K₂ hcfg.std.std hA t₀ ht₀S ht₀c ht₀ne hint
  exact ⟨hcfg.std, ⟨ht₀S, ht₀c, ht₀ne, hint, hfus, htz, hcfg.ch.u_mem, hcfg.ch.u_ord, hcfg.ch.u_ne,
    hcfg.ch.u_norm, hcfg.ch.q_odd, hcfg.ch.q_ge, hcfg.ch.hq₁, hcfg.ch.hq₂⟩⟩

omit [Finite G] in
theorem mul_self_of_isConj {z t : G} (hzo : orderOf z = 2) (htc : IsConj z t) : t * t = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 htc
  have h1 : orderOf t = 2 := by
    have := SemiconjBy.orderOf_eq c (x := z) (y := t) (by
      show c * z = t * c
      rw [← hc]
      group)
    rw [← this]
    exact hzo
  have := pow_orderOf_eq_one t
  rwa [h1, pow_two] at this

omit [Finite G] in
theorem centralizer_eq_normalizer {t : G} (hzo : orderOf z = 2) (htS : t ∈ S)
    (hzS : ∀ s ∈ S, s * z = z * s) (htc : IsConj z t) (htne : t ≠ z) (htz : ¬ IsConj z (t * z)) :
    S ⊓ centralizer ({t} : Set G) =
      S ⊓ normalizer ((zpowers z ⊔ zpowers t : Subgroup G) : Set G) := by
  have hz2 : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzo, pow_two] at this
  have hto : orderOf t = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 htc
    have := SemiconjBy.orderOf_eq c (x := z) (y := t) (by
      show c * z = t * c
      rw [← hc]
      group)
    rw [← this]
    exact hzo
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hto, pow_two] at this
  have hzt : z * t = t * z := (hzS t htS).symm
  have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers t, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow (show Commute z t from hzt) k m).eq
  ext s
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  constructor
  · rintro ⟨hs, hsc⟩
    refine ⟨hs, ?_⟩
    have hst : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.1 hsc
    have hH : zpowers z ⊔ zpowers t ≤ centralizer ({s} : Set G) :=
      sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 (hzS s hs).symm))
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2 hst.symm))
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : h * s = s * h := Subgroup.mem_centralizer_singleton_iff.1 (hH hh)
      have : s * h * s⁻¹ = h := by
        rw [← h1]
        group
      rw [this]
      exact hh
    · intro hh
      have h1 : (s * h * s⁻¹) * s = s * (s * h * s⁻¹) := Subgroup.mem_centralizer_singleton_iff.1 (hH hh)
      have : h = s * h * s⁻¹ := by
        calc h = s⁻¹ * ((s * h * s⁻¹) * s) := by group
          _ = s⁻¹ * (s * (s * h * s⁻¹)) := by rw [h1]
          _ = s * h * s⁻¹ := by group
      rw [this]
      exact hh
  · rintro ⟨hs, hsn⟩
    refine ⟨hs, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have htH : t ∈ zpowers z ⊔ zpowers t := Subgroup.mem_sup_right (mem_zpowers t)
    have hy : s * t * s⁻¹ ∈ zpowers z ⊔ zpowers t := (Subgroup.mem_normalizer_iff.1 hsn t).1 htH
    obtain ⟨a, ha, b, hb, hab⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hy
    rcases eq_one_or_eq_of_mem_zpowers_sq hz2 ha with ha1 | haz <;>
      rcases eq_one_or_eq_of_mem_zpowers_sq ht2 hb with hb1 | hbt
    · exfalso
      have h1 : s * t * s⁻¹ = 1 := by rw [hab, ha1, hb1, mul_one]
      have : t = 1 := by
        calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
          _ = 1 := by rw [h1]; group
      rw [this, orderOf_one] at hto
      omega
    ·
      have h1 : s * t * s⁻¹ = t := by rw [hab, ha1, hbt, one_mul]
      calc s * t = (s * t * s⁻¹) * s := by group
        _ = t * s := by rw [h1]
    ·
      exfalso
      have h1 : s * t * s⁻¹ = z := by rw [hab, haz, hb1, mul_one]
      have h2 : t = z := by
        calc t = s⁻¹ * (s * t * s⁻¹) * s := by group
          _ = s⁻¹ * z * s := by rw [h1]
          _ = z := by
            have := hzS s⁻¹ (S.inv_mem hs)
            calc s⁻¹ * z * s = z * s⁻¹ * s := by rw [this]
              _ = z := by group
      exact htne h2
    ·
      exfalso
      apply htz
      obtain ⟨c, hc⟩ := isConj_iff.1 htc
      refine isConj_iff.2 ⟨s * c, ?_⟩
      have h1 : s * t * s⁻¹ = z * t := by rw [hab, haz, hbt]
      calc s * c * z * (s * c)⁻¹ = s * (c * z * c⁻¹) * s⁻¹ := by group
        _ = s * t * s⁻¹ := by rw [hc]
        _ = z * t := h1
        _ = t * z := hzt

omit [Finite G] in
theorem conjugate_self_of_le {K : Subgroup G} (hK : K ≤ Cz z) : conjugate K z = K := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hK hk)
    show z⁻¹ * k * z⁻¹⁻¹ ∈ K
    have e : z⁻¹ * k * z⁻¹⁻¹ = k := by
      calc z⁻¹ * k * z⁻¹⁻¹ = z⁻¹ * (k * z) := by group
        _ = z⁻¹ * (z * k) := by rw [this]
        _ = k := by group
    rw [e]
    exact hk
  · intro hx
    refine ⟨x, hx, ?_⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hK hx)
    show z⁻¹ * x * z⁻¹⁻¹ = x
    calc z⁻¹ * x * z⁻¹⁻¹ = z⁻¹ * (x * z) := by group
      _ = z⁻¹ * (z * x) := by rw [this]
      _ = x := by group

end Swap

section Core

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {q : ℕ}

theorem LC_conj_mem {c : G} (hc : c ∈ Cen z) {l : G} (hl : l ∈ LC z) : c * l * c⁻¹ ∈ LC z := by
  have hlC : l ∈ Cen z := by
    obtain ⟨l', -, rfl⟩ := hl
    exact l'.2
  exact (LC_normal (z := z)).conj_mem ⟨l, hlC⟩ hl ⟨c, hc⟩

omit [Finite G] in
theorem swaps_symm {t : G} {A B : Subgroup (CentralizerBar z)} (h : Swaps z t A B) :
    Swaps z t B A := by
  obtain ⟨ht, h1, h2⟩ := h
  exact ⟨ht, h2, h1⟩

theorem psp4_core_exists (hII : II4_4_4_center) (h41 : Prop4_1) (h61 : Prop6_1) (h66 : Prop6_6)
    (hpnf : P_normal_four) (hL44 : Lemma4_4) (hL45 : Lemma4_5) (h31 : IVK_3_1a_lifted) (h73 : Lemma7_3)
    (h74 : Lemma7_4) (h77 : Lemma7_7) (hcen : Cen2 G z S) (hT : Term7Out G z S q 1) {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hpair : Stage1Pair G z S q L₁ L₂) : ∃ x : G, TwoClassCore G z S L₁ L₂ q x := by
  have hnf := nonfused_of_term7 hII h41 hT
  have hidx := psp4_index_thm hII h41 G z S q hT
  obtain ⟨K₁, K₂, hstd, hodd, h5, hK₁, hK₂, hT7⟩ := hT
  obtain ⟨t, u, hcfg⟩ := cfg7_of_std hII h41 h61 h66 hpnf hL44 hL45 hstd hnf hodd h5 hK₁ hK₂
  have ht := hcfg.ch
  have h73' := h73 G z S K₁ K₂ t u q hcfg
  obtain ⟨-, h74c⟩ := h74 G z S K₁ K₂ t u q hcfg h73'
  have hM := m4_of_std hII hstd
  have hzS : z ∈ S := hM.z_mem_S
  have huS : u ∈ S := ht.u_mem.1
  have htS : t ∈ S := ht.t_mem
  have hSC : S ≤ Cen z := hstd.sylow.le
  have htC : t ∈ Cen z := hSC htS
  have hu_tz : IsConj (t * z) u := ht.t_fus u ht.u_mem ht.u_ord ht.u_ne
  have hzC : z ∈ Cen z := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hzL : z ∈ LC z := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (⟨z, hzC⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have : z ^ 2 = 1 := by
        have := pow_orderOf_eq_one z
        rwa [hstd.orderOf_z] at this
      simpa using this
    have hLC : z ∈ LC z ↔ toBar z ⟨z, hzC⟩ ∈ LBar z := mem_LC_iff_of_pElt (z := z) ⟨z, hzC⟩ hk
    rw [hLC, LBar_eq_imgBar hII h41 hstd]
    exact Subgroup.mem_sup_left (zbar_facts4 hII hstd).1.1
  have hto : orderOf t = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 ht.t_conj
    have := SemiconjBy.orderOf_eq c (x := z) (y := t) (by
      show c * z = t * c
      rw [← hc]
      group)
    rw [← this]
    exact hstd.orderOf_z
  have hAcomps := comps_of_std4 hII h41 hstd
  have hsets : ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) = {imgBar z K₁, imgBar z K₂} :=
    hpair.comps.symm.trans hAcomps
  have hA12 : imgBar z K₁ ≠ imgBar z K₂ := by
    intro h
    rw [h] at hsets
    have h1 : L₁ ∈ ({imgBar z K₂, imgBar z K₂} : Set (Subgroup (CentralizerBar z))) := by
      rw [← hsets]
      exact Or.inl rfl
    have h2 : L₂ ∈ ({imgBar z K₂, imgBar z K₂} : Set (Subgroup (CentralizerBar z))) := by
      rw [← hsets]
      exact Or.inr rfl
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_self] at h1 h2
    exact hpair.ne (h1.trans h2.symm)
  have hcommA : ∀ a ∈ imgBar z K₁, ∀ b ∈ imgBar z K₂, a * b = b * a := imgBar_comm4 hII hstd
  have hsw : Swaps z t (imgBar z K₁) (imgBar z K₂) :=
    swaps_of_interchanges hM.K₁_le hM.K₂_le htC ht.t_swap
  have htL : t ∉ LC z := by
    intro htL
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (⟨t, htC⟩ : ↥(Cen z)) ^ (2 ^ k) = 1 := by
      refine ⟨1, ?_⟩
      apply Subtype.ext
      have : t ^ 2 = 1 := by
        have := pow_orderOf_eq_one t
        rwa [hto] at this
      simpa using this
    have hLC : t ∈ LC z ↔ toBar z ⟨t, htC⟩ ∈ LBar z := mem_LC_iff_of_pElt (z := z) ⟨t, htC⟩ hk
    rw [hLC, LBar_eq_imgBar hII h41 hstd] at htL
    obtain ⟨a₁, ha₁, a₂, ha₂, hta⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcommA htL
    obtain ⟨ht', h1, -⟩ := hsw
    rw [hta] at h1
    have h2 : conjugate (imgBar z K₁) (a₁ * a₂) = imgBar z K₁ := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hw : a₁⁻¹ * y * a₁ ∈ imgBar z K₁ :=
          (imgBar z K₁).mul_mem ((imgBar z K₁).mul_mem ((imgBar z K₁).inv_mem ha₁) hy) ha₁
        have hc2 : (a₁⁻¹ * y * a₁) * a₂ = a₂ * (a₁⁻¹ * y * a₁) := hcommA _ hw a₂ ha₂
        have e : (a₁ * a₂)⁻¹ * y * (a₁ * a₂)⁻¹⁻¹ = a₁⁻¹ * y * a₁ := by
          calc (a₁ * a₂)⁻¹ * y * (a₁ * a₂)⁻¹⁻¹ = a₂⁻¹ * (a₁⁻¹ * y * a₁) * a₂ := by group
            _ = (a₁⁻¹ * y * a₁) := by
              calc a₂⁻¹ * (a₁⁻¹ * y * a₁) * a₂ = a₂⁻¹ * ((a₁⁻¹ * y * a₁) * a₂) := by group
                _ = a₂⁻¹ * (a₂ * (a₁⁻¹ * y * a₁)) := by rw [hc2]
                _ = a₁⁻¹ * y * a₁ := by group
        show (a₁ * a₂)⁻¹ * y * (a₁ * a₂)⁻¹⁻¹ ∈ imgBar z K₁
        rw [e]
        exact hw
      · intro hx
        have hy : a₁ * x * a₁⁻¹ ∈ imgBar z K₁ :=
          (imgBar z K₁).mul_mem ((imgBar z K₁).mul_mem ha₁ hx) ((imgBar z K₁).inv_mem ha₁)
        refine ⟨a₁ * x * a₁⁻¹, hy, ?_⟩
        have hc3 : x * a₂ = a₂ * x := hcommA x hx a₂ ha₂
        show (a₁ * a₂)⁻¹ * (a₁ * x * a₁⁻¹) * (a₁ * a₂)⁻¹⁻¹ = x
        calc (a₁ * a₂)⁻¹ * (a₁ * x * a₁⁻¹) * (a₁ * a₂)⁻¹⁻¹ = a₂⁻¹ * x * a₂ := by group
          _ = x := by
            calc a₂⁻¹ * x * a₂ = a₂⁻¹ * (x * a₂) := by group
              _ = a₂⁻¹ * (a₂ * x) := by rw [hc3]
              _ = x := by group
    rw [h2] at h1
    exact hA12 h1
  have hSn : S ≤ normalizer ((LC z : Subgroup G) : Set G) := by
    intro s hs
    have hsC : s ∈ Cen z := hSC hs
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      exact LC_conj_mem hsC hl
    · intro hl
      have := LC_conj_mem (inv_mem hsC) hl
      have e : s⁻¹ * (s * l * s⁻¹) * (s⁻¹)⁻¹ = l := by group
      rw [e] at this
      exact this
  have hsw_match : ∀ t₀, Swaps z t₀ L₁ L₂ → Swaps z t₀ (imgBar z K₁) (imgBar z K₂) := by
    intro t₀ h
    rcases Set.pair_eq_pair_iff.1 hsets with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← h1, ← h2]
      exact h
    · rw [← h1, ← h2]
      exact swaps_symm h
  have hcfg_of : ∀ t₀ ∈ S, IsConj z t₀ → Swaps z t₀ L₁ L₂ → Cfg7 G z S K₁ K₂ t₀ u q := by
    intro t₀ ht₀S ht₀c hsw₀
    have ht₀C : t₀ ∈ Cen z := hSC ht₀S
    have hint := interchanges_of_swaps hstd hA12 hM.K₁_le hM.K₂_le ht₀C (hsw_match t₀ hsw₀)
    have ht₀ne : t₀ ≠ z := by
      intro h
      rw [h] at hint
      exact hstd.ne ((conjugate_self_of_le hM.K₁_le).symm.trans hint.1)
    exact cfg7_of_swap hII hL45 hcfg ht₀S ht₀c ht₀ne hint
  refine ⟨u, huS, ht.u_ord, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro hcu
    have hSG : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := sylow_top_of_central hcen.central hcen.sylow
    obtain ⟨hu2, T, huT, hTc⟩ := hcu
    have hTG : CFSG.ABGLocalTools.IsSylowOf 2 (T : Subgroup G) ⊤ := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff]
      refine ⟨le_top, T.isPGroup', ?_⟩
      rw [Subgroup.relIndex_top_right]
      exact T.not_dvd_index
    obtain ⟨c, -, hc⟩ :=
      CFSG.ComponentClassification.AschbacherTheorem3.exists_rightConjugate_eq_of_isSylowOf hSG hTG
    have hu'S : c⁻¹ * u * c ∈ S := by
      rw [← hc]
      exact CFSG.ComponentClassification.AschbacherTheorem3.conj_mem_rightConjugate huT c
    have hu'c : ∀ s ∈ S, s * (c⁻¹ * u * c) = (c⁻¹ * u * c) * s := by
      intro s hs
      rw [← hc] at hs
      have hs' : c * s * c⁻¹ ∈ T := by
        have := (CFSG.ComponentClassification.AschbacherTightEmbedding.mem_rightConjugate_iff
          (T : Subgroup G) c s).1 hs
        exact this
      have := hTc _ hs'
      calc s * (c⁻¹ * u * c) = c⁻¹ * ((c * s * c⁻¹) * u) * c := by group
        _ = c⁻¹ * (u * (c * s * c⁻¹)) * c := by rw [this]
        _ = (c⁻¹ * u * c) * s := by group
    have hu'o : orderOf (c⁻¹ * u * c) = 2 := by
      have := SemiconjBy.orderOf_eq c (x := c⁻¹ * u * c) (y := u) (by
        show c * (c⁻¹ * u * c) = u * c
        group)
      rw [this]
      exact ht.u_ord
    have hz := hpair.base.zcen _ hu'S hu'c hu'o
    have hconj : IsConj z u := by
      rw [isConj_iff]
      refine ⟨c, ?_⟩
      rw [← hz]
      group
    exact ht.tz_ne (hconj.trans hu_tz.symm)
  ·
    intro v hv
    exact (h74c.1 v hv).imp id (fun h => hu_tz.symm.trans h)
  ·
    intro s hs w hw
    have hsC : s ∈ Cen z := hSC hs
    have hz_s : s * z * s⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hsC
      rw [this]
      group
    have hu_s : s * u * s⁻¹ ∈ zpowers z ⊔ zpowers u := by
      rcases ht.u_norm s hs with h | h
      · rw [h]
        exact Subgroup.mem_sup_right (mem_zpowers u)
      · rw [h]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mem_zpowers u))
          (Subgroup.mem_sup_left (mem_zpowers z))
    have hcomm : ∀ a ∈ zpowers z, ∀ b ∈ zpowers u, a * b = b * a := by
      have hzu : z * u = u * z :=
        (Subgroup.mem_centralizer_singleton_iff.1 (hSC huS)).symm
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_zpow (show Commute z u from hzu) k m).eq
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.mem_sup_of_commute' hcomm hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have e : s * (z ^ k * u ^ m) * s⁻¹ = (s * z * s⁻¹) ^ k * (s * u * s⁻¹) ^ m := by
      rw [conj_zpow, conj_zpow]
      group
    rw [e, hz_s]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (zpow_mem (mem_zpowers z) k))
      (zpow_mem hu_s m)
  ·
    intro g hg
    have hmul := Subgroup.coe_mul_of_right_le_normalizer_left (LC z) S hSn
    have hg' : g ∈ ((LC z : Subgroup G) : Set G) * (S : Set G) := by
      rw [← hmul]
      exact hg
    obtain ⟨l₀, hl₀, s₀, hs₀, rfl⟩ := Set.mem_mul.1 hg'
    by_cases hs₀L : s₀ ∈ LC z
    · refine ⟨(l₀ * s₀)⁻¹ * z, ?_, ?_⟩
      · exact (LC z).mul_mem ((LC z).inv_mem ((LC z).mul_mem hl₀ hs₀L)) hzL
      · rw [mul_inv_cancel_left]
    · have hH2 : ((RC S z).subgroupOf S).index = 2 := hidx
      have hmem := (Subgroup.mul_mem_iff_of_index_two hH2 (a := ⟨s₀, hs₀⟩)
        (b := (⟨t, htS⟩ : ↥S)⁻¹)).2 (by
          constructor
          · intro h
            exact absurd h.2 hs₀L
          · intro h
            exfalso
            have h' : t⁻¹ ∈ LC z := h.2
            exact htL (by simpa using (LC z).inv_mem h'))
      have hmemL : s₀ * t⁻¹ ∈ LC z := hmem.2
      refine ⟨t⁻¹ * (l₀ * (s₀ * t⁻¹))⁻¹ * t, ?_, ?_⟩
      · have h1 : l₀ * (s₀ * t⁻¹) ∈ LC z := (LC z).mul_mem hl₀ hmemL
        have h2 := LC_conj_mem (inv_mem htC) ((LC z).inv_mem h1)
        simpa using h2
      · have e : l₀ * s₀ * (t⁻¹ * (l₀ * (s₀ * t⁻¹))⁻¹ * t) = t := by group
        rw [e]
        exact ht.t_conj
  ·
    have hK : K₁ ⊔ K₂ ≤ Cz z := sup_le hM.K₁_le hM.K₂_le
    have hLB : ((K₁ ⊔ K₂).subgroupOf (Cz z)).map (piC z) = LBar z :=
      (map_K12 hII hstd).trans (LBar_eq_imgBar hII h41 hstd).symm
    have huK : u ∈ K₁ ⊔ K₂ := by
      have := ht.u_mem.2
      rwa [hstd.rigidProduct_eq] at this
    exact invol_L_of_lift (h31 G z S K₁ K₂ hstd) hK hLB huK ht.u_ord ht.u_ne
  ·
    refine ⟨t, htS, ht.t_conj, ?_⟩
    rcases Set.pair_eq_pair_iff.1 hsets with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact hsw
    · rw [h1, h2]
      exact swaps_symm hsw
  ·
    intro t₀ ht₀S ht₀c hsw₀
    have hcfg₀ := hcfg_of t₀ ht₀S ht₀c hsw₀
    exact (hcfg₀.ch.t_fus u ht.u_mem ht.u_ord ht.u_ne).symm
  ·
    intro t₀ ht₀S ht₀c hsw₀
    exact swap_b_of_pair hpair hsw₀ (mul_self_of_isConj hstd.orderOf_z ht₀c)
  ·
    intro t₀ ht₀S ht₀c hsw₀
    have hcfg₀ := hcfg_of t₀ ht₀S ht₀c hsw₀
    have h73₀ := h73 G z S K₁ K₂ t₀ u q hcfg₀
    obtain ⟨⟨D, hD⟩, h74c₀⟩ := h74 G z S K₁ K₂ t₀ u q hcfg₀ h73₀
    refine ⟨?_, D, hD.prod, ?_⟩
    · exact centralizer_eq_normalizer hstd.orderOf_z ht₀S
        (fun s hs => Subgroup.mem_centralizer_singleton_iff.1 (hSC hs)) hcfg₀.ch.t_conj
        hcfg₀.ch.t_ne hcfg₀.ch.tz_ne
    · have hr1 := h73₀.1
      have hrne : (Pz S z).relIndex (S1 S K₁) ≠ 0 := Subgroup.index_ne_zero_of_finite
      rcases (by omega : (Pz S z).relIndex (S1 S K₁) = 1 ∨ (Pz S z).relIndex (S1 S K₁) = 2) with
        h1 | h2
      · have hid := hD.index_eq
        rw [h1, Subgroup.relIndex_eq_one] at hid
        have hDP : D ⊓ Pz S z = D := le_antisymm inf_le_left hid
        obtain ⟨n, hn⟩ := hD.inter_dih
        rw [hDP] at hn
        exact ⟨n, hn⟩
      · obtain ⟨n, hn⟩ := h77 G z S K₁ K₂ t₀ u q hcfg₀ h73₀ h74c₀ h2 D hD
        exact ⟨2 ^ n, hn.2⟩
  ·
    intro t₀ ht₀S ht₀c hsw₀
    exact swapE_of_pair hpair hsw₀ (mul_self_of_isConj hstd.orderOf_z ht₀c)

end Core

end CFSG.GH74.GLS.Stage1.Main
