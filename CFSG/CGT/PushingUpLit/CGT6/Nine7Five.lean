module

public import CFSG.CGT.PushingUpLit.CGT6.Nine7Two
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBInputs
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension

public section

namespace CFSG.CGT.PushingUpLit.CGT6.Nine7

open CFSG (conjugate)
open CFSG.Open
open CFSG.ComponentClassification
open CFSG.ComponentClassification.AschbacherKnownGroup (IsFourGroup AschbacherKnownGroupFacts)
open CFSG.ComponentClassification.AschbacherTheorem5
  (preimage_subgroupOf preimage_le core_le oddCore_odd core_conjugate_eq mem_core_iff
    centralizes_of_commutes)
open scoped commutatorElement

section Interface

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isQuasisimple_found {L : Subgroup G} (hL : QS L) : CFSG.IsQuasisimple ↥L :=
  ⟨⟨hL.1⟩, hL.2, exists_noncomm_center_quotient hL⟩

omit [Finite G] in
theorem normal_subgroupOf_of_family {r : ℕ} {Ai : Fin r → Subgroup G} {D : Subgroup G}
    (hcomm : ∀ i j, i ≠ j → ⁅Ai i, Ai j⁆ = ⊥) (hgen : ⨆ i, Ai i = D) (i : Fin r) :
    ((Ai i).subgroupOf D).Normal := by
  refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
  rw [← hgen]
  refine iSup_le fun j => ?_
  by_cases hij : j = i
  · subst hij
    exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomm j i hij)).trans
      (Subgroup.centralizer_le_normalizer _)

theorem core_commutator {r : ℕ} {Ai : Fin r → Subgroup G} {D : Subgroup G}
    (hqs : ∀ i, QS (Ai i)) (hcomm : ∀ i j, i ≠ j → ⁅Ai i, Ai j⁆ = ⊥) (hgen : ⨆ i, Ai i = D)
    (i : Fin r) : ⁅Ai i, aschbacherThm5Core D⁆ = ⊥ := by
  have hle : Ai i ≤ D := hgen ▸ le_iSup Ai i
  have hOs : Group.IsSolvable ↥(aschbacherThm5OddCore ↥D) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (oddCore_odd ↥D)
  have hOn : (aschbacherThm5OddCore ↥D).IsSubnormal :=
    (inferInstance : (aschbacherThm5OddCore ↥D).Normal).isSubnormal
  have hK : CFSG.IsComponent ((Ai i).subgroupOf D) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
      (isQuasisimple_found (hqs i)), (normal_subgroupOf_of_family hcomm hgen i).isSubnormal⟩
  have h1 := (CFSG.LocalCores.component_solvable_centralizer hOs hOn).1 _ hK
  have h2 := congrArg (Subgroup.map D.subtype) h1
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_bot] at h2

theorem core_comm {r : ℕ} {Ai : Fin r → Subgroup G} {D : Subgroup G}
    (hqs : ∀ i, QS (Ai i)) (hcomm : ∀ i j, i ≠ j → ⁅Ai i, Ai j⁆ = ⊥) (hgen : ⨆ i, Ai i = D) :
    ∀ o ∈ aschbacherThm5Core D, ∀ d ∈ D, o * d = d * o := by
  intro o ho d hd
  have hdC : D ≤ Subgroup.centralizer ({o} : Set G) := by
    rw [← hgen]
    refine iSup_le fun i x hx => ?_
    rw [mem_centralizer_single]
    exact (mul_comm_of_commutator_eq_bot (core_commutator hqs hcomm hgen i) hx ho).symm
  exact mem_centralizer_single.1 (hdC hd)

@[expose] def barOf (D K : Subgroup G) : Subgroup (↥D ⧸ aschbacherThm5OddCore ↥D) :=
  (K.subgroupOf D).map (QuotientGroup.mk' (aschbacherThm5OddCore ↥D))

omit [Finite G] in
theorem preimage_eq_sup (D K : Subgroup G) (hK : K ≤ D) :
    aschbacherThm5Preimage D (barOf D K) = K ⊔ aschbacherThm5Core D := by
  have h1 := preimage_subgroupOf D (barOf D K)
  rw [barOf, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
  have h2 := congrArg (Subgroup.map D.subtype) h1
  rw [Subgroup.map_subgroupOf_eq_of_le (preimage_le D _), Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hK] at h2
  exact h2

end Interface

section Interface2

variable {G : Type} [Group G] [Finite G]

theorem theorem5_interface (h5 : GSThmB.AschbacherTheorem5Input) {D : Subgroup G} {r : ℕ}
    (hr : 1 ≤ r) {Ai : Fin r → Subgroup G} (hqs : ∀ i, QS (Ai i))
    (hcomm : ∀ i j, i ≠ j → ⁅Ai i, Ai j⁆ = ⊥) (hgen : ⨆ i, Ai i = D)
    (hperm : ∀ h ∈ Subgroup.normalizer (D : Set G), ∀ i, ∃ j,
      (Ai i).map (MulAut.conj h).toMonoidHom = Ai j)
    (hi : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ≠ 1 →
      Ai i ≤ Subgroup.centralizer ({t} : Set G) →
      Ai j ≤ Subgroup.centralizer ({g⁻¹ * t * g} : Set G) → g ∈ Subgroup.normalizer (D : Set G))
    (hii : ∀ (i : Fin r) (g : G), Ai i ≤ Subgroup.normalizer (conjugate D g : Set G) →
      g ∈ Subgroup.normalizer (D : Set G))
    (hH : Subgroup.normalizer (D : Set G) ≠ ⊤) :
    r = 1 ∨ (r = 2 ∧ ∀ i j : Fin r, i ≠ j → Open.pRank 2 (Ai i) ≤ 1 ∧
      ∀ a₁ ∈ Ai i, ∀ a₂ ∈ Ai j, orderOf a₁ = 2 → orderOf a₂ = 2 →
        a₁ ∈ Subgroup.centralizer (Ai i : Set G) → a₂ ∈ Subgroup.centralizer (Ai j : Set G) →
        a₁ = a₂ ∨ a₁ * a₂ ∈ Subgroup.center G) := by
  have hle : ∀ i, Ai i ≤ D := fun i => hgen ▸ le_iSup Ai i
  have hOc := core_comm hqs hcomm hgen
  have hcentAi := core_commutator hqs hcomm hgen
  have hperf : ∀ i, Group.IsPerfect ↥(Ai i) := fun i => ⟨(hqs i).1⟩
  set Abar : Fin r → Subgroup (↥D ⧸ aschbacherThm5OddCore ↥D) := fun i => barOf D (Ai i)
    with hAbar
  have hpre : ∀ i, aschbacherThm5Preimage D (Abar i) = Ai i ⊔ aschbacherThm5Core D :=
    fun i => preimage_eq_sup D (Ai i) (hle i)
  have hAipre : ∀ i, Ai i ≤ aschbacherThm5Preimage D (Abar i) := fun i => by
    rw [hpre]
    exact le_sup_left
  have hdec : ∀ i, ∀ a ∈ aschbacherThm5Preimage D (Abar i),
      ∃ x ∈ Ai i, ∃ o ∈ aschbacherThm5Core D, a = x * o := by
    intro i a ha
    rw [hpre] at ha
    obtain ⟨x, hx, o, ho, hxo⟩ := (mem_sup_iff_of_comm (hcentAi i)).1 ha
    exact ⟨x, hx, o, ho, hxo.symm⟩
  have hinj : Function.Injective Abar := by
    intro i j hij
    by_contra hne
    have h1 : aschbacherThm5Preimage D (Abar i) = aschbacherThm5Preimage D (Abar j) := by
      rw [hij]
    have hAij : Ai i ≤ Ai j := by
      refine perfect_le_of_le_mul (hperf i) (hle i) (core_le D) hOc ?_
      intro a ha
      obtain ⟨x, hx, o, ho, hxo⟩ := hdec j a (h1 ▸ hAipre i ha)
      exact ⟨x, hx, o, ho, hxo⟩
    exact qs_commutator_ne_bot (hqs i)
      (le_bot_iff.1 ((Subgroup.commutator_mono le_rfl hAij).trans (hcomm i j hne).le))
  have hbarqs : ∀ i, QS (Abar i) := by
    intro i
    have hK : CFSG.IsQuasisimple ↥((Ai i).subgroupOf D) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hle i)).symm
        (isQuasisimple_found (hqs i))
    have hnk : ¬ (Ai i).subgroupOf D ≤ (QuotientGroup.mk' (aschbacherThm5OddCore ↥D)).ker := by
      intro hk
      apply qs_commutator_ne_bot (hqs i)
      refine commutator_eq_bot_of_forall_comm fun x hx y hy => ?_
      have hxO : x ∈ aschbacherThm5Core D := by
        have h1 := hk (show (⟨x, hle i hx⟩ : ↥D) ∈ (Ai i).subgroupOf D from hx)
        rw [QuotientGroup.ker_mk'] at h1
        exact (mem_core_iff D ⟨x, hle i hx⟩).2 h1
      exact hOc x hxO y (hle i hy)
    have hq := CFSG.LocalCores.isQuasisimple_map hK (QuotientGroup.mk' (aschbacherThm5OddCore ↥D))
      hnk
    exact ⟨hq.1.commutator_eq_top, hq.2.1⟩
  have hsemi : ∀ i, aschbacherThm5IsSemisimple (Abar i) := fun i => semisimple_of_qs (hbarqs i)
  have hcommbar : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x := by
    intro i j hij x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hy
    simp only [QuotientGroup.mk'_apply]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mul_comm_of_commutator_eq_bot (hcomm i j hij)
      (Subgroup.mem_subgroupOf.1 ha) (Subgroup.mem_subgroupOf.1 hb))
  have hgenbar : ⨆ i, Abar i = ⊤ := by
    have h1 : (⨆ i, (Ai i).subgroupOf D) = ⊤ := by
      apply Subgroup.map_injective D.subtype_injective
      have hm : ∀ i, ((Ai i).subgroupOf D).map D.subtype = Ai i := fun i =>
        Subgroup.map_subgroupOf_eq_of_le (hle i)
      rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
      simp only [hm]
      exact hgen
    change ⨆ i, ((Ai i).subgroupOf D).map (QuotientGroup.mk' (aschbacherThm5OddCore ↥D)) = ⊤
    rw [← Subgroup.map_iSup, h1]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hpermbar : ∀ h ∈ Subgroup.normalizer (D : Set G), ∀ i, ∃ j,
      (aschbacherThm5Preimage D (Abar i)).map (MulAut.conj h).toMonoidHom =
        aschbacherThm5Preimage D (Abar j) := by
    intro h hh i
    obtain ⟨j, hj⟩ := hperm h hh i
    refine ⟨j, ?_⟩
    rw [hpre, hpre, Subgroup.map_sup, hj, core_conjugate_eq D ⟨h, hh⟩]
  have hi' : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ Subgroup.center G →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) → g ∈ Subgroup.normalizer (D : Set G) := by
    intro i j t g ht2 htc hc1 hc2
    have hZ : ∀ z ∈ aschbacherThm5Core D, ∀ z' ∈ aschbacherThm5Core D, z * z' = z' * z :=
      fun z hz z' hz' => hOc z hz z' (core_le D hz')
    have hPZ : ∀ k, ∀ x ∈ Ai k, ∀ z ∈ aschbacherThm5Core D, x * z = z * x :=
      fun k x hx z hz => (hOc z hz x (hle k hx)).symm
    refine hi i j t g ht2 (fun h => htc (h ▸ Subgroup.one_mem _))
      (centralizes_of_perfect (hperf i) hZ (hPZ i) fun x hx => hc1 x (hAipre i hx))
      (centralizes_of_perfect (hperf j) hZ (hPZ j) fun x hx => hc2 x (hAipre j hx))
  have hii' : ∀ (i : Fin r) (g : G) (X : Subgroup G),
      X ≤ (Subgroup.normalizer (D : Set G)).map (MulAut.conj g⁻¹).toMonoidHom →
      (∀ a ∈ aschbacherThm5Preimage D (Abar i), ∃ x ∈ X, ∃ o ∈ aschbacherThm5Core D,
        a = x * o) → g ∈ Subgroup.normalizer (D : Set G) := by
    intro i g X hX hdecX
    have hAX : Ai i ≤ X :=
      perfect_le_of_le_mul (hperf i) (hle i) (core_le D) hOc fun a ha => hdecX a (hAipre i ha)
    exact hii i g (hAX.trans (hX.trans (le_of_eq (conjugate_normalizer D g))))
  have key := h5 G D r hr Abar hinj hsemi hcommbar hgenbar hpermbar hi' hii' hH
  rcases key with h | ⟨hr2, hall⟩
  · exact Or.inl h
  refine Or.inr ⟨hr2, fun i j hij => ?_⟩
  obtain ⟨-, hrank, hcen⟩ := hall i j hij
  refine ⟨?_, fun a₁ ha₁ a₂ ha₂ ho₁ ho₂ hc₁ hc₂ => ?_⟩
  · have := SectionRank.pRank_mono (p := 2) (by norm_num) (hAipre i)
    omega
  · have hcomm12 : a₁ * a₂ = a₂ * a₁ := mul_comm_of_commutator_eq_bot (hcomm i j hij) ha₁ ha₂
    have hcentral : ∀ (k : Fin r) (a : G), a ∈ Ai k → a ∈ Subgroup.centralizer (Ai k : Set G) →
        aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar k)) a := by
      intro k a hak hac
      apply centralizes_of_commutes
      intro b hb
      have hbC : aschbacherThm5Preimage D (Abar k) ≤ Subgroup.centralizer ({a} : Set G) := by
        rw [hpre]
        refine sup_le (fun x hx => ?_) (fun o ho => ?_)
        · rw [mem_centralizer_single]
          exact (Subgroup.mem_centralizer_iff.1 hac x hx).symm
        · rw [mem_centralizer_single]
          exact (hOc o ho a (hle k hak)).symm
      exact mem_centralizer_single.1 (hbC hb)
    exact hcen a₁ (hAipre i ha₁) a₂ (hAipre j ha₂) ho₁ ho₂ hcomm12 (hcentral i a₁ ha₁ hc₁)
      (hcentral j a₂ ha₂ hc₂)

end Interface2

section CliqueApp

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_eq_conjugate (X : Subgroup G) (h : G) :
    X.map (MulAut.conj h).toMonoidHom = conjugate X h⁻¹ := by
  unfold conjugate
  rw [inv_inv]

theorem lemma7 {A B B' : Subgroup G} (hs : Setting A) (hB : B ∈ Clq A) (hB' : B' ∈ Clq A)
    {t g : G} (ht : ∃ k : ℕ, t ^ (2 ^ k) = 1) (ht1 : t ≠ 1)
    (htB : B ≤ Subgroup.centralizer ({t} : Set G))
    (htB' : B' ≤ Subgroup.centralizer ({g⁻¹ * t * g} : Set G)) :
    g ∈ Subgroup.normalizer (Dgrp A A : Set G) := by
  obtain ⟨k, hk⟩ := ht
  have hdvd : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨m, -, hmord⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
    refine ⟨m - 1, ?_⟩
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso
      subst h0
      exact ht1 (orderOf_eq_one_iff.1 (by simpa using hmord))
    · omega
  set n := 2 ^ m' with hn
  have hn0 : n ≠ 0 := by positivity
  have hndvd : n ∣ orderOf t := by
    rw [hmord, hn]
    exact pow_dvd_pow 2 (Nat.le_succ m')
  have ht₀ : orderOf (t ^ n) = 2 := by
    rw [orderOf_pow_of_dvd hn0 hndvd, hmord, hn, pow_succ,
      Nat.mul_div_cancel_left _ (by positivity)]
  set t₀ := t ^ n with ht₀def
  have hB₀ : B ≤ Subgroup.centralizer ({t₀} : Set G) := by
    intro x hx
    have h1 := mem_centralizer_single.1 (htB hx)
    rw [mem_centralizer_single]
    exact (Commute.pow_left (show Commute t x from h1) n).eq
  have hconj : (g⁻¹ * t * g) ^ n = g⁻¹ * t₀ * g := by
    have := conj_pow (a := g⁻¹) (b := t) (i := n)
    simpa [inv_inv, ht₀def] using this
  have hB'₀ : B' ≤ Subgroup.centralizer ({g⁻¹ * t₀ * g} : Set G) := by
    intro x hx
    have h1 := mem_centralizer_single.1 (htB' hx)
    rw [mem_centralizer_single, ← hconj]
    exact (Commute.pow_left (show Commute (g⁻¹ * t * g) x from h1) n).eq
  have hBgm : conjugate B' g⁻¹ ∈ ConjCl A := ConjCl.cj hB'.1 g⁻¹
  have hBg : conjugate B' g⁻¹ ≤ Subgroup.centralizer ({t₀} : Set G) := by
    intro y hy
    rw [mem_conjugate, inv_inv] at hy
    have h1 := mem_centralizer_single.1 (hB'₀ hy)
    rw [mem_centralizer_single]
    have e1 : g⁻¹ * t₀ * g * (g⁻¹ * y * g) = g⁻¹ * (t₀ * y) * g := by group
    have e2 : g⁻¹ * y * g * (g⁻¹ * t₀ * g) = g⁻¹ * (y * t₀) * g := by group
    rw [e1, e2] at h1
    exact mul_left_cancel (mul_right_cancel h1)
  have hBc : IsCompIn B (Subgroup.centralizer ({t₀} : Set G)) :=
    isCompIn_centralizer_involution (ConjCl.qs hs.qs hB.1) (ConjCl.star hs.star hB.1) ht₀ hB₀
  have hBgc : IsCompIn (conjugate B' g⁻¹) (Subgroup.centralizer ({t₀} : Set G)) :=
    isCompIn_centralizer_involution (ConjCl.qs hs.qs hBgm) (ConjCl.star hs.star hBgm) ht₀ hBg
  have hrel : Rel B (conjugate B' g⁻¹) := by
    by_cases hne : B = conjugate B' g⁻¹
    · exact Or.inl hne
    · exact Or.inr (commute_of_isCompIn_ne hBc hBgc hne)
  have hrelA : Rel A (conjugate B' g⁻¹) :=
    Rel.trans' hs.qs hs.star (mem_ConjCl_self A) hB.1 hBgm hB.2 hrel
  have e1 : Dgrp A A = Dgrp A (conjugate B' g⁻¹) :=
    Dgrp_eq hs.qs hs.star (mem_ConjCl_self A) hBgm hrelA
  have e2 : Dgrp A B' = Dgrp A A :=
    (Dgrp_eq hs.qs hs.star (mem_ConjCl_self A) hB'.1 hB'.2).symm
  have e3 : conjugate (Dgrp A A) g⁻¹ = Dgrp A A := by
    calc conjugate (Dgrp A A) g⁻¹ = conjugate (Dgrp A B') g⁻¹ := by rw [e2]
      _ = Dgrp A (conjugate B' g⁻¹) := Dgrp_conjugate g⁻¹
      _ = Dgrp A A := e1.symm
  exact ((Subgroup.normalizer (Dgrp A A : Set G)).inv_mem_iff).1 (mem_normalizer_of_conjugate_eq e3)

theorem theorem5_clique (h5 : GSThmB.AschbacherTheorem5Input) (hK : AschbacherKnownGroupFacts)
    {A : Subgroup G} (hs : Setting A) (hN : Subgroup.normalizer (Dgrp A A : Set G) ≠ ⊤) :
    Nat.card (Clq A) = 1 ∨ (Nat.card (Clq A) = 2 ∧ ∀ B₁ ∈ Clq A, ∀ B₂ ∈ Clq A, B₁ ≠ B₂ →
      Open.pRank 2 B₁ ≤ 1 ∧ ∀ a₁ ∈ B₁, ∀ a₂ ∈ B₂, orderOf a₁ = 2 → orderOf a₂ = 2 →
        a₁ ∈ Subgroup.centralizer (B₁ : Set G) → a₂ ∈ Subgroup.centralizer (B₂ : Set G) →
        a₁ = a₂ ∨ a₁ * a₂ ∈ Subgroup.center G) := by
  classical
  have : Finite (Clq A) := Subtype.finite
  let e : Fin (Nat.card (Clq A)) ≃ Clq A := (Finite.equivFin (Clq A)).symm
  have hr : 1 ≤ Nat.card (Clq A) :=
    Nat.card_pos_iff.2 ⟨⟨⟨A, mem_Clq_self A⟩⟩, inferInstance⟩
  have hgen : ⨆ i, (e i).1 = Dgrp A A := by
    rw [Dgrp_self_eq_iSup]
    apply le_antisymm
    · exact iSup_le fun i => le_iSup₂_of_le (e i).1 (e i).2 le_rfl
    · refine iSup₂_le fun B hB => le_iSup_of_le (e.symm ⟨B, hB⟩) ?_
      rw [Equiv.apply_symm_apply]
  have hcomm : ∀ i j, i ≠ j → ⁅(e i).1, (e j).1⁆ = ⊥ := by
    intro i j hij
    have hne : (e i).1 ≠ (e j).1 := fun h => hij (e.injective (Subtype.ext h))
    rcases Rel.trans' hs.qs hs.star (e i).2.1 (mem_ConjCl_self A) (e j).2.1 (e i).2.2.symm
      (e j).2.2 with h | h
    · exact absurd h hne
    · exact h
  have key := theorem5_interface h5 hr (fun i => ConjCl.qs hs.qs (e i).2.1) hcomm hgen
    (fun h hh i => by
      have hmem : conjugate (e i).1 h⁻¹ ∈ Clq A :=
        conjugate_mem_Clq hs (e i).2 (((Subgroup.normalizer (Dgrp A A : Set G))).inv_mem hh)
      refine ⟨e.symm ⟨_, hmem⟩, ?_⟩
      rw [Equiv.apply_symm_apply, map_conj_eq_conjugate])
    (fun i j t g ht ht1 hti htj => lemma7 hs (e i).2 (e j).2 ht ht1 hti htj)
    (fun i g hig => by
      have hs' := hs.base_change (e i).2
      have := lemma8_normalizer hs' hK g (by
        rw [Dgrp_self_of_mem_Clq (e i).2 hs.qs hs.star]
        exact hig)
      rwa [Dgrp_self_of_mem_Clq (e i).2 hs.qs hs.star] at this)
    hN
  rcases key with h | ⟨h2, hall⟩
  · exact Or.inl h
  · refine Or.inr ⟨h2, fun B₁ hB₁ B₂ hB₂ hne => ?_⟩
    have e1 : (e (e.symm ⟨B₁, hB₁⟩) : Subgroup G) = B₁ := by rw [Equiv.apply_symm_apply]
    have e2 : (e (e.symm ⟨B₂, hB₂⟩) : Subgroup G) = B₂ := by rw [Equiv.apply_symm_apply]
    have := hall (e.symm ⟨B₁, hB₁⟩) (e.symm ⟨B₂, hB₂⟩) (fun h => hne (by rw [← e1, ← e2, h]))
    rwa [e1, e2] at this

end CliqueApp

end CFSG.CGT.PushingUpLit.CGT6.Nine7
