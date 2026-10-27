module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma34Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanBender
import CFSG.GroupTheory.Fitting.SelfCentralizingComponent
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.LocalAnalysis.ComponentClassification.AS76bExistBasic
public import CFSG.LocalAnalysis.ComponentClassification.AS76bInputs

public section

namespace CFSG.ComponentClassification.AS76b

open Subgroup CFSG.Open

namespace Lemma34

variable {G : Type} [Group G] [Finite G]

theorem conclusion_of_simple {A N : Subgroup G} (h : Hyp31 A) (hN : N.Normal)
    (hNs : IsSimpleGroup N) (hAN : A ≤ N) :
    normalClosure (A : Set G) = CFSG.generalizedFitting G ∧
      IsSimpleGroup (CFSG.generalizedFitting G) := by
  have hq := h.standard.1
  have hCN : centralizer (N : Set G) = ⊥ :=
    eq_bot_of_normal_le_centralizer h normal_centralizer (centralizer_le hAN)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_not_commute hq
  have hnonab : ∃ x y : N, x * y ≠ y * x :=
    ⟨⟨a, hAN ha⟩, ⟨b, hAN hb⟩, fun e => hab (congrArg Subtype.val e)⟩
  obtain ⟨hNq, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnonab
  have hNcomp : CFSG.IsComponent N := ⟨hNq, hN.isSubnormal⟩
  have hF : CFSG.generalizedFitting G = N :=
    CFSG.generalizedFitting_eq_of_isComponent_of_centralizer_eq_bot N hNcomp hCN
  have hcl : normalClosure (A : Set G) = N := by
    have hle : normalClosure (A : Set G) ≤ N := normalClosure_le_normal hAN
    have hn : ((normalClosure (A : Set G)).subgroupOf N).Normal :=
      normalClosure_normal.subgroupOf N
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((normalClosure (A : Set G)).subgroupOf N)
      with h' | h'
    · exfalso
      rw [subgroupOf_eq_bot] at h'
      have hA : A = ⊥ := le_bot_iff.mp (h' le_normalClosure (le_normalClosure.trans hle))
      rw [hA, mem_bot] at ha hb
      exact hab (by rw [ha, hb])
    · rw [subgroupOf_eq_top] at h'
      exact le_antisymm hle h'
  rw [hF, hcl]
  exact ⟨rfl, hNs⟩

structure Setup (A N L : Subgroup G) : Prop where
  hyp : Hyp31 A
  normal : N.Normal
  min : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N
  le : L ≤ N
  simple : IsSimpleGroup L
  normalizes : N ≤ normalizer (L : Set G)

namespace Setup

variable {A N L : Subgroup G} (S : Setup A N L)
include S

theorem conj_le (g : G) : conj L g ≤ N :=
  conj_le_of_normal S.normal S.le g

theorem le_normalizer (g : G) : N ≤ normalizer (conj L g : Set G) :=
  le_normalizer_conj S.normal S.normalizes g

theorem isSimpleGroup (g : G) : IsSimpleGroup (conj L g) :=
  have := S.simple
  isSimpleGroup_conj L g

theorem conj_ne_bot (g : G) : conj L g ≠ ⊥ := by
  have := S.isSimpleGroup g
  exact (nontrivial_iff_ne_bot _).mp IsSimpleGroup.toNontrivial

theorem ne_bot : N ≠ ⊥ := fun h =>
  S.conj_ne_bot 1 (le_bot_iff.mp ((S.conj_le 1).trans h.le))

theorem conj_inf_eq_bot {g h : G} (hne : conj L g ≠ conj L h) : conj L g ⊓ conj L h = ⊥ :=
  have := S.isSimpleGroup g
  have := S.isSimpleGroup h
  inf_eq_bot_of_isSimpleGroup ((S.conj_le g).trans (S.le_normalizer h))
    ((S.conj_le h).trans (S.le_normalizer g)) hne

theorem commute_of_ne {g h : G} (hne : conj L g ≠ conj L h) {x y : G} (hx : x ∈ conj L g)
    (hy : y ∈ conj L h) : x * y = y * x :=
  commute_of_inf_eq_bot ((S.conj_le g).trans (S.le_normalizer h))
    ((S.conj_le h).trans (S.le_normalizer g)) (S.conj_inf_eq_bot hne) hx hy

theorem normalClosure_eq : normalClosure (L : Set G) = N := by
  have := S.normal
  rcases S.min _ normalClosure_normal (normalClosure_le_normal S.le) with h | h
  · exfalso
    apply S.conj_ne_bot 1
    rw [conj_one]
    exact le_bot_iff.mp (h ▸ le_normalClosure)
  · exact h

theorem even_card (g : G) : Even (Nat.card (conj L g)) := by
  rw [card_conj]
  by_contra hodd
  have := S.normal
  have hn : (L.subgroupOf N).Normal :=
    (normal_subgroupOf_iff S.le).mpr fun x n hx hn =>
      (mem_normalizer_iff.mp (S.normalizes hn) x).mp hx
  have hbot := eq_bot_of_odd_normal S.hyp.oddCore hn
    (by rw [Nat.card_congr (subgroupOfEquivOfLe S.le).toEquiv]; exact Nat.not_even_iff_odd.mp hodd)
  rw [subgroupOf_eq_bot] at hbot
  apply S.conj_ne_bot 1
  rw [conj_one]
  exact le_bot_iff.mp (hbot le_rfl S.le)

theorem conj_normal_of_le {g : G} (hAL : A ≤ conj L g) : (conj L g).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff]
  intro h _
  rw [← conj_eq_self_iff, conj_conj]
  by_contra hne
  apply S.hyp.standard.2.2.2.2 h
  rw [commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [mem_centralizer_iff]
  intro b hb
  have hb' : b ∈ conj L (h * g) := by
    rw [← conj_conj]
    exact map_mono hAL hb
  exact S.commute_of_ne hne hb' (hAL ha)

theorem conj_eq_of_le {g : G} (hAL : A ≤ conj L g) : conj L g = N :=
  (S.min _ (S.conj_normal_of_le hAL) (S.conj_le g)).resolve_left (S.conj_ne_bot g)

theorem false_of_not_le (hAN : ¬ A ≤ N) : False := by
  have hq := S.hyp.standard.1
  have hstd := S.hyp.standard
  have : N.Normal := S.normal
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAnorm : A ≤ normalizer (N : Set G) := by
    rw [normalizer_eq_top_iff.mpr S.normal]
    exact le_top
  have hcen := (le_or_inf_le_centralizer hq hAnorm).resolve_left hAN
  have hKN : ∀ x ∈ N, x ∈ normalizer (A : Set G) → x ∈ centralizer (A : Set G) :=
    fun x hxN hxA => mem_centralizer_of_mem hq hAnorm hcen hxA hxN
  obtain ⟨⟨u, huK⟩, hu⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (A : Set G)) 2
    (even_iff_two_dvd.mp hstd.2.1)
  rw [Subgroup.orderOf_mk] at hu
  have huu : u * u = 1 := by rw [← sq, ← hu, pow_orderOf_eq_one]
  have hNeven : Even (Nat.card N) := by
    by_contra hodd
    have hle : N ≤ standardComponentOddCore G := le_sSup ⟨S.normal, Nat.not_even_iff_odd.mp hodd⟩
    rw [S.hyp.oddCore] at hle
    exact S.ne_bot (le_bot_iff.mp hle)
  obtain ⟨y, hyN, hy2, hyu⟩ := exists_involution_commute huu
    (by rw [normalizer_eq_top_iff.mpr S.normal]; exact mem_top u) hNeven
  have hyK := hKN y hyN (mem_normalizer_of_commute hstd huK hu hyu)
  have hyy : y * y = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
  have hinv : ∀ g, ∃ z ∈ conj L g, z ∈ centralizer (A : Set G) ∧ orderOf z = 2 := by
    intro g
    obtain ⟨z, hzL, hz2, hzy⟩ :=
      exists_involution_commute hyy (S.le_normalizer g hyN) (S.even_card g)
    exact ⟨z, hzL, hKN z (S.conj_le g hzL) (mem_normalizer_of_commute hstd hyK hy2 hzy), hz2⟩
  have hall : ∀ g h, conj L g ≠ conj L h → conj L g ≤ centralizer (A : Set G) := by
    intro g h hne x hx
    obtain ⟨z, hzL, hzK, hz2⟩ := hinv h
    exact hKN x (S.conj_le g hx)
      (mem_normalizer_of_commute hstd hzK hz2 (S.commute_of_ne hne hx hzL))
  have hLN : ∀ g, conj L g = L := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g₀, hg₀⟩ := hcon
    apply S.ne_bot
    apply eq_bot_of_normal_le_centralizer S.hyp S.normal
    rw [← S.normalClosure_eq]
    refine normalClosure_le_of_forall fun g => ?_
    by_cases hg : conj L g = L
    · exact hall g g₀ (by rw [hg]; exact fun h => hg₀ h.symm)
    · exact hall g 1 (by rwa [conj_one])
  have hLnormal : L.Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff]
    intro g _
    exact conj_eq_self_iff.mp (hLN g)
  have hLeq : L = N := (S.min L hLnormal S.le).resolve_left (by
    have := S.conj_ne_bot 1
    rwa [conj_one] at this)
  have hNs : IsSimpleGroup N := by
    rw [← hLeq]
    exact S.simple
  set M : Subgroup N := (centralizer (A : Set G)).subgroupOf N with hM
  have hSE : CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
    refine ⟨?_, ?_, ?_⟩
    · intro htop
      rw [hM, subgroupOf_eq_top] at htop
      exact S.ne_bot (eq_bot_of_normal_le_centralizer S.hyp S.normal htop)
    · have hzp : zpowers (⟨y, hyN⟩ : N) ≤ M := zpowers_le.mpr hyK
      have h2 := card_dvd_of_le hzp
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hy2] at h2
      exact even_iff_two_dvd.mpr h2
    · intro g hg
      have hgA : (g : G) ∉ normalizer (centralizer (A : Set G) : Set G) := by
        rw [hstd.2.2.2.1]
        exact fun h => hg (hKN g g.2 h)
      refine (hstd.2.2.1 g hgA).of_dvd_nat ?_
      rw [← card_map_of_injective N.subtype_injective]
      apply card_dvd_of_le
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxM, hxMg⟩ := mem_inf.mp hx
      refine mem_inf.mpr ⟨hxM, ?_⟩
      obtain ⟨w, hwM, rfl⟩ := hxMg
      exact ⟨w, hwM, rfl⟩
  have hSE' := CFSG.BenderSuzuki.isStronglyEmbedded_of_parity M hSE
  have hBender := CFSG.BenderSuzuki.theorem_SE_simple M hSE' hNs
  obtain ⟨T, hTM⟩ := hSE'.containsSylowTwo
  let θ : A →* MulAut N := (MulAut.conjNormal (H := N)).comp A.subtype
  have : Group.IsPerfect A := ⟨hq.1⟩
  have hperf : Group.IsPerfect θ.range :=
    Group.IsPerfect.ofSurjective (f := θ.rangeRestrict) θ.rangeRestrict_surjective
  have hθ : θ.range = ⊥ := by
    refine CFSG.ComponentClassification.AschbacherToolkit.glaubermanBenderPerfect N hBender T
      θ.range hperf ?_
    rintro _ ⟨a, rfl⟩ s hs
    apply Subtype.ext
    simp only [θ, MonoidHom.coe_comp, Function.comp_apply, coe_subtype, MulAut.conjNormal_apply]
    have hsK : (s : G) ∈ centralizer (A : Set G) := hTM hs
    rw [mem_centralizer_iff.mp hsK a a.2, mul_inv_cancel_right]
  have hNK : N ≤ centralizer (A : Set G) := by
    intro x hx
    rw [mem_centralizer_iff]
    intro a ha
    have h1 : θ ⟨a, ha⟩ ∈ θ.range := ⟨⟨a, ha⟩, rfl⟩
    rw [hθ, mem_bot] at h1
    have h2 := congrArg (fun φ : MulAut N => ((φ ⟨x, hx⟩ : N) : G)) h1
    simp only [θ, MonoidHom.coe_comp, Function.comp_apply, coe_subtype, MulAut.conjNormal_apply,
      MulAut.one_apply] at h2
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h2]
  exact S.ne_bot (eq_bot_of_normal_le_centralizer S.hyp S.normal hNK)

theorem not_mem_normalizer_conj (hAN : A ≤ N) (hdiag : ∀ g, ¬ A ≤ conj L g) {u : G}
    (huK : u ∈ centralizer (A : Set G)) (hu : orderOf u = 2) (g : G) :
    u ∉ normalizer (conj L g : Set G) := by
  have hq := S.hyp.standard.1
  have hstd := S.hyp.standard
  have hAnorm : ∀ h, A ≤ normalizer (conj L h : Set G) := fun h => hAN.trans (S.le_normalizer h)
  have hKL : ∀ h, ∀ x ∈ conj L h, x ∈ normalizer (A : Set G) → x ∈ centralizer (A : Set G) :=
    fun h x hx hxA => mem_centralizer_of_mem hq (hAnorm h)
      ((le_or_inf_le_centralizer hq (hAnorm h)).resolve_left (hdiag h)) hxA hx
  intro hug
  have huu : u * u = 1 := by rw [← sq, ← hu, pow_orderOf_eq_one]
  obtain ⟨y, hyL, hy2, hyu⟩ := exists_involution_commute huu hug (S.even_card g)
  have hyK := hKL g y hyL (mem_normalizer_of_commute hstd huK hu hyu)
  have hother : ∀ h, conj L h ≠ conj L g → conj L h ≤ centralizer (A : Set G) :=
    fun h hne x hx =>
      hKL h x hx (mem_normalizer_of_commute hstd hyK hy2 (S.commute_of_ne hne hx hyL))
  set M : Subgroup G := ⨆ (h : G) (_ : conj L h ≠ conj L g), conj L h
  have hMK : M ≤ centralizer (A : Set G) := iSup₂_le fun h hne => hother h hne
  have hMnorm : M ≤ normalizer (conj L g : Set G) :=
    iSup₂_le fun h _ => (S.conj_le h).trans (S.le_normalizer g)
  have hle : A ≤ conj L g ⊔ M := by
    refine hAN.trans ?_
    rw [← S.normalClosure_eq]
    refine normalClosure_le_of_forall fun h => ?_
    by_cases hh : conj L h = conj L g
    · rw [hh]
      exact le_sup_left
    · exact le_sup_of_le_right
        (le_iSup₂ (f := fun (h : G) (_ : conj L h ≠ conj L g) => conj L h) h hh)
  exact hdiag g (le_of_le_sup (commutator_self_eq hq) (hAnorm g) hMnorm hMK hle)

theorem false_of_diagonal (hAN : A ≤ N) (hdiag : ∀ g, ¬ A ≤ conj L g) : False := by
  have hq := S.hyp.standard.1
  have hstd := S.hyp.standard
  have hAnorm : ∀ h, A ≤ normalizer (conj L h : Set G) := fun h => hAN.trans (S.le_normalizer h)
  have hfree : ∀ {x : G}, x ∈ centralizer (A : Set G) → orderOf x = 2 → ∀ g,
      x ∉ normalizer (conj L g : Set G) :=
    fun hxK hx g => S.not_mem_normalizer_conj hAN hdiag hxK hx g
  obtain ⟨E, hEK, hE, hE4⟩ := exists_elemAbelian_four S.hyp.rank
  obtain ⟨u, huE, v, hvE, hu, hv, huv⟩ := exists_two_involutions hE hE4
  have huK := hEK huE
  have hvK := hEK hvE
  have huu : u * u = 1 := by rw [← sq, ← hu, pow_orderOf_eq_one]
  have hvv : v * v = 1 := by rw [← sq, ← hv, pow_orderOf_eq_one]
  have hcomm : u * v = v * u :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨u, huE⟩ ⟨v, hvE⟩)
  have hw : orderOf (u * v) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · have h1 : u * v * (u * v) = (u * u) * (v * v) := by
        rw [mul_assoc, ← mul_assoc v, ← hcomm]
        group
      rw [sq, h1, huu, hvv, one_mul]
    · intro h1
      apply huv
      rw [← mul_one u, ← hvv, ← mul_assoc, h1, one_mul]
  have hwK : u * v ∈ centralizer (A : Set G) := mul_mem huK hvK
  have hne : ∀ {x : G}, x ∈ centralizer (A : Set G) → orderOf x = 2 → ∀ g,
      conj L (x * g) ≠ conj L g := by
    intro x hxK hx g h
    apply hfree hxK hx g
    rw [← conj_eq_self_iff, conj_conj, h]
  obtain ⟨g, hg⟩ : ∃ g, ¬ conj L g ≤ centralizer (A : Set G) := by
    by_contra hcon
    push Not at hcon
    have hNK : N ≤ centralizer (A : Set G) := by
      rw [← S.normalClosure_eq]
      exact normalClosure_le_of_forall hcon
    exact not_le_centralizer_self hq (hAN.trans hNK)
  have h12 := hne huK hu g
  have hnotle : ¬ A ≤ conj L g ⊔ conj L (u * g) := by
    intro hle
    have h13 := hne hvK hv g
    have h23 : conj L (v * g) ≠ conj L (u * g) := by
      intro h
      apply hne hwK hw g
      calc conj L (u * v * g) = conj (conj L (v * g)) u := by rw [conj_conj, mul_assoc]
        _ = conj (conj L (u * g)) u := by rw [h]
        _ = conj L g := by rw [conj_conj, ← mul_assoc, huu, one_mul]
    have hsub : conj L g ⊔ conj L (u * g) ≤ centralizer (conj L (v * g) : Set G) := by
      refine sup_le (fun y hy => ?_) (fun y hy => ?_)
      · exact mem_centralizer_iff.mpr fun z hz => S.commute_of_ne h13 hz hy
      · exact mem_centralizer_iff.mpr fun z hz => S.commute_of_ne h23 hz hy
    apply hg
    intro x hx
    have hvx : v * x * v⁻¹ ∈ conj L (v * g) := by
      rw [← conj_conj]
      exact conj_mem_conj hx
    rw [mem_centralizer_iff]
    intro a ha
    have h1 : v * x * v⁻¹ * a = a * (v * x * v⁻¹) :=
      mem_centralizer_iff.mp (hsub (hle ha)) _ hvx
    have hva : v⁻¹ * a * v = a := by
      rw [mul_assoc, mem_centralizer_iff.mp hvK a ha, inv_mul_cancel_left]
    calc a * x = v⁻¹ * a * v * x := by rw [hva]
      _ = v⁻¹ * (a * (v * x * v⁻¹)) * v := by group
      _ = v⁻¹ * (v * x * v⁻¹ * a) * v := by rw [h1]
      _ = x * (v⁻¹ * a * v) := by group
      _ = x * a := by rw [hva]
  have hAnorm12 : A ≤ normalizer ((conj L g ⊔ conj L (u * g) : Subgroup G) : Set G) :=
    le_normalizer_sup (hAnorm g) (hAnorm (u * g))
  have hcen12 := (le_or_inf_le_centralizer hq hAnorm12).resolve_left hnotle
  apply hg
  intro x hx
  have hx' : u * x * u⁻¹ ∈ conj L (u * g) := by
    rw [← conj_conj]
    exact conj_mem_conj hx
  have hxx' : x * (u * x * u⁻¹) = u * x * u⁻¹ * x := S.commute_of_ne (Ne.symm h12) hx hx'
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hyu : x * (u * x * u⁻¹) * u = u * (x * (u * x * u⁻¹)) := by
    rw [hui] at hxx' ⊢
    calc x * (u * x * u) * u = x * u * x * (u * u) := by group
      _ = (u * u) * x * u * x := by rw [huu, mul_one, one_mul]
      _ = u * (u * x * u * x) := by group
      _ = u * (x * (u * x * u)) := by rw [hxx']
  have hyK := mem_centralizer_of_mem hq hAnorm12 hcen12
    (mem_normalizer_of_commute hstd huK hu hyu) (mul_mem (mem_sup_left hx) (mem_sup_right hx'))
  rw [mem_centralizer_iff]
  intro a ha
  have h1 : a * (x * (u * x * u⁻¹)) = x * (u * x * u⁻¹) * a := mem_centralizer_iff.mp hyK a ha
  have hax : a * x * a⁻¹ ∈ conj L g := (mem_normalizer_iff.mp (hAnorm g ha) x).mp hx
  have hax' : a * (u * x * u⁻¹) * a⁻¹ ∈ conj L (u * g) :=
    (mem_normalizer_iff.mp (hAnorm (u * g) ha) _).mp hx'
  have h2 : a * x * a⁻¹ = x * (u * x * u⁻¹) * (a * (u * x * u⁻¹) * a⁻¹)⁻¹ := by
    calc a * x * a⁻¹ = a * (x * (u * x * u⁻¹)) * a⁻¹ * (a * (u * x * u⁻¹) * a⁻¹)⁻¹ := by group
      _ = x * (u * x * u⁻¹) * a * a⁻¹ * (a * (u * x * u⁻¹) * a⁻¹)⁻¹ := by rw [h1]
      _ = x * (u * x * u⁻¹) * (a * (u * x * u⁻¹) * a⁻¹)⁻¹ := by group
  have hmem : x⁻¹ * (a * x * a⁻¹) ∈ conj L g ⊓ conj L (u * g) := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hx) hax, ?_⟩
    rw [h2, show x⁻¹ * (x * (u * x * u⁻¹) * (a * (u * x * u⁻¹) * a⁻¹)⁻¹) =
      u * x * u⁻¹ * (a * (u * x * u⁻¹) * a⁻¹)⁻¹ by group]
    exact mul_mem hx' (inv_mem hax')
  rw [S.conj_inf_eq_bot (Ne.symm h12), mem_bot] at hmem
  calc a * x = x * (x⁻¹ * (a * x * a⁻¹)) * a := by group
    _ = x * a := by rw [hmem, mul_one]

end Setup

end Lemma34

theorem asc08Lemma34 : Asc08Lemma34 := by
  intro G _ _ A h
  have hq := h.standard.1
  have hA1 : A ≠ ⊥ := fun hA => Lemma34.not_le_centralizer_self hq (hA ▸ bot_le)
  obtain ⟨N, ⟨hNn, hN1⟩, hNmin⟩ :=
    (Set.toFinite {M : Subgroup G | M.Normal ∧ M ≠ ⊥}).exists_minimal
      ⟨⊤, inferInstance, fun h => hA1 (le_bot_iff.mp (h ▸ le_top))⟩
  have hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N := fun M hM hle =>
    (em (M = ⊥)).imp id fun hM1 => le_antisymm hle (hNmin ⟨hM, hM1⟩ hle)
  obtain ⟨r, T, hr, hTN, hTs, -, hTn, -⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hNn hN1 hmin
  have S : Lemma34.Setup A N (T ⟨0, hr⟩) :=
    ⟨h, hNn, hmin, hTN _, hTs _, Lemma34.le_normalizer_of_normal_subgroupOf (hTN _) (hTn _)⟩
  by_cases hAN : A ≤ N
  · by_cases hex : ∃ g, A ≤ Lemma34.conj (T ⟨0, hr⟩) g
    · obtain ⟨g, hg⟩ := hex
      have hLg := S.conj_eq_of_le hg
      have hNs : IsSimpleGroup N := by
        rw [← hLg]
        exact S.isSimpleGroup g
      exact Lemma34.conclusion_of_simple h hNn hNs hAN
    · exact (S.false_of_diagonal hAN (not_exists.mp hex)).elim
  · exact (S.false_of_not_le hAN).elim

end CFSG.ComponentClassification.AS76b
