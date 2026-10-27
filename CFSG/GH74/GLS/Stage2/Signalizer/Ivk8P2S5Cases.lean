module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Diag
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Cmm
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S4aStmt

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

structure S5Hyp : Prop where
  hB12 : Bender12
  h171 : Prop17_1
  h183 : Lemma18_3a
  h184 : Lemma18_4ac
  h185 : Lemma18_5R
  hcl : Claim18Xd

@[expose] def QTriple {G : Type} [Group G] (z : G) (M E : Subgroup G) (p m : ℕ)
    (X D : Subgroup G) : Prop :=
  X ∈ XfamR z M (Vof M E) ∧
    (∃ J₁ J₂ : Subgroup G, IsCompIn X J₁ ∧ IsCompIn X J₂ ∧ J₁ ≠ J₂ ∧ Em X = J₁ ⊔ J₂ ∧
      ordq J₁ = m ∧ ordq J₂ = m) ∧
    D ≤ E ∧ Nat.card ↥D = p ^ 2 ∧ D ≤ centralizer (Em X : Set G)

section Cases

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem abelian_of_inverts {F : Subgroup G} {z : G} (hinv : ∀ f ∈ F, z * f * z⁻¹ = f⁻¹) :
    ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
  intro x hx y hy
  have h1 := hinv (x * y) (F.mul_mem hx hy)
  have h2 := hinv x hx
  have h3 := hinv y hy
  have e : z * (x * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
  rw [e, h2, h3, mul_inv_rev] at h1
  have h4 := congrArg (fun w => w⁻¹) h1
  simp only [mul_inv_rev, inv_inv] at h4
  exact h4.symm

omit [Finite G] in
theorem center_props (K : Subgroup G) :
    (∀ b ∈ (Subgroup.center ↥K).map K.subtype, ∀ b' ∈ (Subgroup.center ↥K).map K.subtype,
      b * b' = b' * b) ∧
    (∀ a ∈ K, ∀ b ∈ (Subgroup.center ↥K).map K.subtype, a * b = b * a) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz' z)
  · rintro a ha _ ⟨z, hz, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨a, ha⟩)

omit [Finite G] in
theorem mem_center_map_of_CenK {K : Subgroup G} {c : G} (h : CenK K c) :
    c ∈ (Subgroup.center ↥K).map K.subtype :=
  ⟨⟨c, h.1⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (h.2 g g.2), rfl⟩

theorem eq_of_le_of_ordq {K J : Subgroup G} (hK : CFSG.IsQuasisimple ↥K)
    (hJ : CFSG.IsQuasisimple ↥J) (hJK : J ≤ K) (hord : ordq K ≤ ordq J) : J = K := by
  have hJbot : ¬ J ≤ (⊥ : Subgroup G) := by
    intro h
    have hnt : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hJ
    exact ((Subgroup.nontrivial_iff_ne_bot J).1 hnt) (le_bot_iff.1 h)
  obtain ⟨-, hsurj⟩ := proj_onto (K := K) (L := ⊥)
    (fun a _ b hb => by rw [Subgroup.mem_bot.1 hb]; simp) hJ (by rwa [sup_bot_eq]) hJbot
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1
  have hKle : K ≤ J ⊔ (Subgroup.center ↥K).map K.subtype := by
    intro a ha
    obtain ⟨a', ha', b, hb, hab, hcen⟩ := hsurj hord a ha
    have hb1 : b = 1 := Subgroup.mem_bot.1 hb
    rw [hb1, mul_one] at hab
    have e : a = a' * (a⁻¹ * a')⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hab)
      (Subgroup.mem_sup_right (mem_center_map_of_CenK hcen.inv))
  have hKJ : K ≤ J := perfect_le_of_sup hKperf hKle (center_props K).1
    (fun a ha b hb => (center_props K).2 a (hJK ha) b hb)
  exact le_antisymm hJK hKJ

theorem le_normalizer_of_isCompIn (h185 : Lemma18_5R) {z : G} {k : Kind} {S M : Subgroup G}
    {p : ℕ} {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t) {Y : Subgroup G}
    (hY : Y ∈ XfamR z M (Vof M E)) {J : Subgroup G} (hJ : IsCompIn Y J) :
    Y ≤ normalizer (J : Set G) := by
  have h5 : Y = Em Y ⊔ Fpi (piF' M) Y := h185 G z k S M p E t hctx Y hY
  have hJE : J ≤ Em Y := le_Em_of_isCompIn hJ
  have hEm : Em Y ≤ normalizer (J : Set G) := by
    refine Em_le_of_forall_comp fun K hK => ?_
    by_cases hKJ : K = J
    · rw [hKJ]
      exact Subgroup.le_normalizer
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      exact Subgroup.mem_centralizer_iff.2 fun j hj =>
        (commute_of_isCompIn hK hJ hKJ x hx j hj).symm
  have hF : Fpi (piF' M) Y ≤ normalizer (J : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro f hf
    exact Subgroup.mem_centralizer_iff.2 fun j hj =>
      Fm_commute_Em' Y f (Fpi_le_Fm _ Y hf) j (hJE hj)
  calc Y = Em Y ⊔ Fpi (piF' M) Y := h5
    _ ≤ normalizer (J : Set G) := sup_le hEm hF

theorem le_Em_of_perfect (h185 : Lemma18_5R) (h171 : Prop17_1) {z : G} {k : Kind}
    {S M : Subgroup G} {p : ℕ} {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t)
    {Y : Subgroup G} (hY : Y ∈ XfamR z M (Vof M E)) {J : Subgroup G} (hJ : ⁅J, J⁆ = J)
    (hJY : J ≤ Y) : J ≤ Em Y := by
  have hF := S5Facts.of_ctx h171 hctx
  have h5 : Y = Em Y ⊔ Fpi (piF' M) Y := h185 G z k S M p E t hctx Y hY
  obtain ⟨-, -, -, hYz, hF1, -⟩ := hY
  have hzY := z_mem_normalizer_of_comm hYz
  obtain ⟨hinv, -⟩ := inverts_F1 hF.hMz (mul_self_eq_one_of_orderOf hF.hz2) hzY hF1
  refine perfect_le_of_sup (A := Em Y) (B := Fpi (piF' M) Y) hJ (hJY.trans h5.le)
    (abelian_of_inverts hinv) ?_
  intro a ha b hb
  exact Fm_commute_Em' Y b (Fpi_le_Fm _ Y hb) a ha

omit [Finite G] in
theorem odd_orderOf_of_mem_elem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hE : IsElementaryAbelian p ↥E) {v : G} (hv : v ∈ E) : Odd (orderOf v) := by
  have : IsElementaryAbelian p ↥E := hE
  have h1 : v ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (A := E) v hv
  exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one h1)

theorem all_comps_of_ncard {Y K₁ K₂ : Subgroup G}
    (hnc : Set.ncard {K : Subgroup G | IsCompIn Y K} ≤ 2) (h1 : IsCompIn Y K₁)
    (h2 : IsCompIn Y K₂) (h12 : K₁ ≠ K₂) : ∀ K, IsCompIn Y K → K = K₁ ∨ K = K₂ := by
  intro K hK
  by_contra hcon
  push Not at hcon
  have hsub : ({K₁, K₂, K} : Set (Subgroup G)) ⊆ {K | IsCompIn Y K} := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact hK
  have h3 : ({K₁, K₂, K} : Set (Subgroup G)).ncard = 3 := by
    rw [Set.ncard_eq_three]
    exact ⟨K₁, K₂, K, h12, hcon.1.symm, hcon.2.symm, rfl⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem isCompIn_XdR (hy : S5Hyp) {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
    {E : Subgroup G} {t : G} (hctx : Ctx18 G z k S M p E t) (hF : S5Facts z M p E) {m : ℕ}
    (hmax : ∀ X' ∈ XfamR z M (Vof M E), ∀ J' : Subgroup G, IsCompIn X' J' → ordq J' ≤ m)
    {X : Subgroup G} (hX : X ∈ XfamR z M (Vof M E)) {J : Subgroup G} (hJ : IsCompIn X J)
    (hJm : ordq J = m) {D : Subgroup G} (hDE : D ≤ E) (hDc : Nat.card ↥D = p ^ 2)
    (hDJ : D ≤ centralizer (J : Set G))
    (hQ : (∃ X' D', QTriple z M E p m X' D') → QTriple z M E p m X D) {d : G}
    (hd : d ∈ Dstar M D) : IsCompIn (XdR M d) J := by
  have hp : p.Prime := hctx.prime
  have hdE : d ∈ E := hDE hd.1
  have hYmem : XdR M d ∈ XfamR z M (Vof M E) :=
    XdR_mem_XfamR hy.hB12 hy.h183 hy.h171 hy.hcl hctx hdE hd.2.1 hd.2.2
  have hc2 := comm2_le_XdR hy.hB12 hy.h184 hy.h171 hctx hdE hd.2.1 hd.2.2
  have hXM : ¬ X ≤ M := not_le_of_mem_XfamR hF.hMz hX
  have hXtop : X ≠ ⊤ := hX.2.1
  have hXn := hX.2.2.1
  have h3X := hy.h183 G z k S M p E t hctx X hXn hXM hXtop J hJ
  have hJz : ⁅J, zpowers z⁆ = J := h3X.2.1
  have hJq := isQuasisimple_of_isCompIn hJ
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJd : J ≤ centralizer ({d} : Set G) := fun j hj =>
    Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hDJ hd.1) j hj)
  have hJY : J ≤ XdR M d := le_XdR_of_comp hc2 hJd hJz
  have hJEm : J ≤ Em (XdR M d) := le_Em_of_perfect hy.h185 hy.h171 hctx hYmem hJperf hJY
  have hJbot : J ≠ ⊥ := ne_bot_of_isCompIn hJ
  have hYM : ¬ XdR M d ≤ M := not_le_of_mem_XfamR hF.hMz hYmem
  have hYtop : XdR M d ≠ ⊤ := hYmem.2.1
  have hYn := hYmem.2.2.1
  by_cases hex : ∃ K₁, IsCompIn (XdR M d) K₁
  swap
  · exfalso
    push Not at hex
    have : Em (XdR M d) ≤ ⊥ := Em_le_of_forall_comp fun K hK => absurd hK (hex K)
    exact hJbot (le_bot_iff.1 (hJEm.trans this))
  obtain ⟨K₁, hK₁⟩ := hex
  have hnc := (hy.h183 G z k S M p E t hctx (XdR M d) hYn hYM hYtop K₁ hK₁).1
  have hordK : ∀ K, IsCompIn (XdR M d) K → ordq K ≤ ordq J := fun K hK =>
    hJm ▸ hmax _ hYmem K hK
  by_cases h2 : ∃ K₂, IsCompIn (XdR M d) K₂ ∧ K₂ ≠ K₁
  · obtain ⟨K₂, hK₂, h21⟩ := h2
    have h12 : K₁ ≠ K₂ := h21.symm
    have hall := all_comps_of_ncard hnc hK₁ hK₂ h12
    have hEmY : Em (XdR M d) = K₁ ⊔ K₂ := by
      refine le_antisymm (Em_le_of_forall_comp fun K hK => ?_)
        (sup_le (le_Em_of_isCompIn hK₁) (le_Em_of_isCompIn hK₂))
      rcases hall K hK with rfl | rfl
      · exact le_sup_left
      · exact le_sup_right
    have hq₁ := isQuasisimple_of_isCompIn hK₁
    have hq₂ := isQuasisimple_of_isCompIn hK₂
    have comm12 := commute_of_isCompIn hK₁ hK₂ h12
    by_cases hJ1 : J ≤ K₁
    · rw [eq_of_le_of_ordq hq₁ hJq hJ1 (hordK K₁ hK₁)]
      exact hK₁
    by_cases hJ2 : J ≤ K₂
    · rw [eq_of_le_of_ordq hq₂ hJq hJ2 (hordK K₂ hK₂)]
      exact hK₂
    exfalso
    have hord1 : ordq K₁ ≤ ordq J := hordK K₁ hK₁
    have hord2 : ordq K₂ ≤ ordq J := hordK K₂ hK₂
    have hJle : J ≤ K₁ ⊔ K₂ := hEmY ▸ hJEm
    have hJle' : J ≤ K₂ ⊔ K₁ := by rwa [sup_comm] at hJle
    have comm21 : ∀ a ∈ K₂, ∀ b ∈ K₁, a * b = b * a := fun a ha b hb => (comm12 b hb a ha).symm
    have e1 : ordq J ≤ ordq K₁ := (proj_onto comm12 hJq hJle hJ2).1
    have e2 : ordq J ≤ ordq K₂ := (proj_onto comm21 hJq hJle' hJ1).1
    have hm1 : ordq K₁ = m := (le_antisymm hord1 e1).trans hJm
    have hm2 : ordq K₂ = m := (le_antisymm hord2 e2).trans hJm
    have hDcent : ∀ v ∈ D, v ∈ centralizer (K₁ : Set G) ∧ v ∈ centralizer (K₂ : Set G) := by
      intro v hv
      have hvY : v ∈ normalizer ((XdR M d : Subgroup G) : Set G) := hYn v (hF.hEV (hDE hv))
      have hodd := odd_orderOf_of_mem_elem hp hctx.odd hctx.E_elem (hDE hv)
      have hvK₁ := cj_fix_of_odd hall h12 hK₁ hK₂ hvY hodd
      have hvK₂ := cj_fix_of_odd (fun K hK => (hall K hK).symm) h12.symm hK₂ hK₁ hvY hodd
      have hvJ : ∀ j ∈ J, v * j * v⁻¹ = j := fun j hj => by
        have := Subgroup.mem_centralizer_iff.1 (hDJ hv) j hj
        calc v * j * v⁻¹ = j * v * v⁻¹ := by rw [this]
          _ = j := by group
      exact ⟨diag_one comm12 hq₁ hJq hJle hJ2 hord1 hvK₁ hvK₂ hvJ,
        diag_one comm21 hq₂ hJq hJle' hJ1 hord2 hvK₂ hvK₁ hvJ⟩
    have hDEm : D ≤ centralizer ((Em (XdR M d) : Subgroup G) : Set G) := by
      intro v hv
      refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute comm12
        (hEmY ▸ hx)
      have h1 := Subgroup.mem_centralizer_iff.1 (hDcent v hv).1 a ha
      have h2 := Subgroup.mem_centralizer_iff.1 (hDcent v hv).2 b hb
      calc a * b * v = a * (b * v) := by group
        _ = a * (v * b) := by rw [h2]
        _ = (a * v) * b := by group
        _ = (v * a) * b := by rw [h1]
        _ = v * (a * b) := by group
    obtain ⟨-, ⟨J₁, J₂, hJ₁, hJ₂, hJ12, hEmX, -, -⟩, -, -, hDEmX⟩ :=
      hQ ⟨XdR M d, D, hYmem, ⟨K₁, K₂, hK₁, hK₂, h12, hEmY, hm1, hm2⟩, hDE, hDc, hDEm⟩
    have hncX := h3X.1
    have hallX := all_comps_of_ncard hncX hJ₁ hJ₂ hJ12
    have key : ∀ J' : Subgroup G, IsCompIn X J' → J' ≠ J → D ≤ centralizer (J' : Set G) →
        False := by
      intro J' hJ' hne hDJ'
      have hJ'z : ⁅J', zpowers z⁆ = J' :=
        (hy.h183 G z k S M p E t hctx X hXn hXM hXtop J' hJ').2.1
      have hJ'q := isQuasisimple_of_isCompIn hJ'
      have hJ'perf : ⁅J', J'⁆ = J' := Subgroup.isPerfect_iff.mp hJ'q.1
      have hJ'd : J' ≤ centralizer ({d} : Set G) := fun j hj =>
        Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hDJ' hd.1) j hj)
      have hJ'Y : J' ≤ XdR M d := le_XdR_of_comp hc2 hJ'd hJ'z
      have hJ'Em : J' ≤ Em (XdR M d) := le_Em_of_perfect hy.h185 hy.h171 hctx hYmem hJ'perf hJ'Y
      have hJ'le : J' ≤ K₁ ⊔ K₂ := hEmY ▸ hJ'Em
      have hcomm : ∀ u ∈ J', ∀ j ∈ J, u * j * u⁻¹ = j := fun u hu j hj => by
        have := commute_of_isCompIn hJ' hJ hne u hu j hj
        calc u * j * u⁻¹ = j * u * u⁻¹ := by rw [this]
          _ = j := by group
      have hN₁ : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G) :=
        sup_le Subgroup.le_normalizer (fun b hb =>
          Subgroup.centralizer_le_normalizer _
            (Subgroup.mem_centralizer_iff.2 fun a ha => comm12 a ha b hb))
      have hN₂ : K₁ ⊔ K₂ ≤ normalizer (K₂ : Set G) :=
        sup_le (fun b hb => Subgroup.centralizer_le_normalizer _
            (Subgroup.mem_centralizer_iff.2 fun a ha => comm21 a ha b hb))
          Subgroup.le_normalizer
      have hcent : ∀ u ∈ J', u ∈ centralizer (K₁ : Set G) ∧ u ∈ centralizer (K₂ : Set G) := by
        intro u hu
        have huK : u ∈ K₁ ⊔ K₂ := hJ'le hu
        exact ⟨diag_one comm12 hq₁ hJq hJle hJ2 hord1 (hN₁ huK) (hN₂ huK) (hcomm u hu),
          diag_one comm21 hq₂ hJq hJle' hJ1 hord2 (hN₂ huK) (hN₁ huK) (hcomm u hu)⟩
      have hab : ∀ u ∈ J', ∀ u' ∈ J', u * u' = u' * u := by
        intro u hu u' hu'
        obtain ⟨a, ha, b, hb, rfl⟩ :=
          CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute comm12 (hJ'le hu)
        have h1 := Subgroup.mem_centralizer_iff.1 (hcent u' hu').1 a ha
        have h2 := Subgroup.mem_centralizer_iff.1 (hcent u' hu').2 b hb
        calc a * b * u' = a * (b * u') := by group
          _ = a * (u' * b) := by rw [h2]
          _ = (a * u') * b := by group
          _ = (u' * a) * b := by rw [h1]
          _ = u' * (a * b) := by group
      apply ne_bot_of_isCompIn hJ'
      rw [← hJ'perf, eq_bot_iff]
      exact Subgroup.commutator_le.2 fun u hu u' hu' =>
        Subgroup.mem_bot.2 (commutatorElement_eq_one_iff_mul_comm.2 (hab u hu u' hu'))
    have hDcentEm : ∀ K, K ≤ Em X → D ≤ centralizer (K : Set G) := fun K hK v hv =>
      Subgroup.mem_centralizer_iff.2 fun x hx => Subgroup.mem_centralizer_iff.1 (hDEmX hv) x (hK hx)
    rcases hallX J hJ with hJc | hJc
    · refine key J₂ hJ₂ ?_ (hDcentEm J₂ (hEmX ▸ le_sup_right))
      rw [hJc]
      exact hJ12.symm
    · refine key J₁ hJ₁ ?_ (hDcentEm J₁ (hEmX ▸ le_sup_left))
      rw [hJc]
      exact hJ12
  · push Not at h2
    have hEmY : Em (XdR M d) = K₁ := le_antisymm
      (Em_le_of_forall_comp fun K hK => (h2 K hK).le) (le_Em_of_isCompIn hK₁)
    have hJK₁ : J ≤ K₁ := hEmY ▸ hJEm
    rw [eq_of_le_of_ordq (isQuasisimple_of_isCompIn hK₁) hJq hJK₁ (hordK K₁ hK₁)]
    exact hK₁

end Cases

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
