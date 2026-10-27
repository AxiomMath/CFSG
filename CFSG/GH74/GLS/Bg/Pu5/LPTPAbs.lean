module

public import CFSG.GH74.GLS.Bg.Iii2.CMAux

public section

namespace CFSG.GH74.GLS.Bg.Pu5

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Abstract

variable {H : Type} [Group H]

theorem nontrivial_of_quasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) : Nontrivial Q := by
  obtain ⟨-, hsimple, -⟩ := hQ
  exact (QuotientGroup.mk'_surjective (center Q)).nontrivial

theorem false_of_quasisimple_odd {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (hodd : Odd (Nat.card Q)) : False := by
  have := nontrivial_of_quasisimple hQ
  have := hQ.1
  have hsolv : Group.IsSolvable Q := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.IsPerfect.not_isSolvable Q hsolv

theorem commute_of_central_commutators {Q : Subgroup H} (hperf : Group.IsPerfect ↥Q) {g : H}
    (hcQ : ∀ q ∈ Q, ⁅q, g⁆ ∈ Q) (hcen : ∀ q ∈ Q, ∀ x ∈ Q, x * ⁅q, g⁆ = ⁅q, g⁆ * x) :
    ∀ q ∈ Q, q * g = g * q := by
  let c : ↥Q → ↥Q := fun q => ⟨⁅(q : H), g⁆, hcQ q q.2⟩
  have hcc : ∀ q : ↥Q, c q ∈ Subgroup.center ↥Q := fun q =>
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hcen q q.2 x x.2)
  have hmul : ∀ a b : ↥Q, c (a * b) = c a * c b := by
    intro a b
    have h1 : c (a * b) = a * c b * a⁻¹ * c a := by
      apply Subtype.ext
      simp only [c, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
      group
    have h2 : a * c b * a⁻¹ = c b := by
      have := Subgroup.mem_center_iff.mp (hcc b) a
      rw [this]
      group
    have h3 : c b * c a = c a * c b := Subgroup.mem_center_iff.mp (hcc a) (c b)
    rw [h1, h2, h3]
  let φ : ↥Q →* ↥(Subgroup.center ↥Q) := MonoidHom.mk' (fun q => ⟨c q, hcc q⟩) (fun a b =>
    Subtype.ext (hmul a b))
  have hker : φ.ker = ⊤ := by
    refine top_unique ?_
    have h1 := Abelianization.commutator_subset_ker φ
    rwa [hperf.commutator_eq_top] at h1
  intro q hq
  have h1 : (⟨q, hq⟩ : ↥Q) ∈ φ.ker := by rw [hker]; trivial
  have h2 : φ ⟨q, hq⟩ = 1 := h1
  have h3 : c ⟨q, hq⟩ = 1 := congrArg Subtype.val h2
  have h4 : ⁅q, g⁆ = 1 := congrArg Subtype.val h3
  exact commutatorElement_eq_one_iff_mul_comm.mp h4

variable [Finite H]

theorem commute_of_odd_commutators {Q : Subgroup H} (hQ : CFSG.IsQuasisimple ↥Q) {g : H}
    (hg : g ∈ normalizer (Q : Set H)) {M : Subgroup H} (hM : Odd (Nat.card ↥M))
    (hcomm : ∀ q ∈ Q, ⁅q, g⁆ ∈ M) : ∀ q ∈ Q, q * g = g * q := by
  have hcQ : ∀ q ∈ Q, ⁅q, g⁆ ∈ Q := by
    intro q hq
    have h1 : g * q⁻¹ * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hg _).mp (Q.inv_mem hq)
    have : ⁅q, g⁆ = q * (g * q⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact Q.mul_mem hq h1
  let c : ↥Q → ↥Q := fun q => ⟨⁅(q : H), g⁆, hcQ q q.2⟩
  let W : Subgroup ↥Q := Subgroup.closure (Set.range c)
  have hWM : W.map Q.subtype ≤ M := by
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨q, rfl⟩
    exact hcomm q q.2
  have hWodd : Odd (Nat.card ↥W) := by
    have h1 : Nat.card ↥(W.map Q.subtype) = Nat.card ↥W :=
      Subgroup.card_map_of_injective Q.subtype_injective
    have h2 : Nat.card ↥(W.map Q.subtype) ∣ Nat.card ↥M := Subgroup.card_dvd_of_le hWM
    rw [← h1]
    exact hM.of_dvd_nat h2
  have hWn : W.Normal := by
    refine ⟨fun n hn x => ?_⟩
    induction hn using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨q, rfl⟩ := hw
      have : x * c q * x⁻¹ = c (x * q) * (c x)⁻¹ := by
        apply Subtype.ext
        simp only [c, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [this]
      exact W.mul_mem (Subgroup.subset_closure ⟨_, rfl⟩) (W.inv_mem (Subgroup.subset_closure ⟨_, rfl⟩))
    | one => simp
    | mul a b _ _ ha hb =>
      have : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
      rw [this]
      exact W.mul_mem ha hb
    | inv a _ ha =>
      have : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
      rw [this]
      exact W.inv_mem ha
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hWn with htop | hcen
  · exfalso
    have h1 : Nat.card ↥Q = Nat.card ↥W := by
      rw [htop, Subgroup.card_top]
    exact false_of_quasisimple_odd hQ (by rwa [h1])
  · have hcc : ∀ q : ↥Q, c q ∈ Subgroup.center ↥Q := fun q =>
      hcen (Subgroup.subset_closure ⟨q, rfl⟩)
    exact commute_of_central_commutators hQ.1 hcQ fun q hq x hx =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcc ⟨q, hq⟩) ⟨x, hx⟩)

theorem commute_of_odd_commutators_component {Q : Subgroup H} (hQ : CFSG.IsComponent Q) {g : H}
    {M : Subgroup H} (hM : Odd (Nat.card ↥M)) (hcomm : ∀ q ∈ Q, ⁅q, g⁆ ∈ M) :
    ∀ q ∈ Q, q * g = g * q := by
  by_cases hgN : g ∈ normalizer (Q : Set H)
  · exact commute_of_odd_commutators hQ.1 hgN hM hcomm
  exfalso
  set Q' : Subgroup H := conjSub g Q with hQ'
  have hQ'c : CFSG.IsComponent Q' :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hQ
  have hne : Q ≠ Q' := fun h => hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hcomm' : ⁅Q, Q'⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hQ hQ'c).resolve_left hne
  have hQQ' : ∀ x ∈ Q, ∀ y ∈ Q', x * y = y * x := fun x hx y hy => by
    have := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm', Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  set P : Subgroup H := Q ⊔ Q' with hP
  have hQP : Q ≤ P := le_sup_left
  have hQ'P : Q' ≤ P := le_sup_right
  have hPN : P ≤ normalizer (Q' : Set H) := by
    refine sup_le (fun x hx => ?_) Subgroup.le_normalizer
    have hxc : x ∈ Subgroup.centralizer (Q' : Set H) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => (hQQ' x hx y hy).symm
    exact Subgroup.centralizer_le_normalizer _ hxc
  have hn : (Q'.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQ'P).mpr hPN
  let θ : ↥P →* ↥P ⧸ Q'.subgroupOf P := QuotientGroup.mk' (Q'.subgroupOf P)
  have hSM : (Q.subgroupOf P).map θ ≤ (M.subgroupOf P).map θ := by
    rintro _ ⟨s, hs, rfl⟩
    have hq : (s : H) ∈ Q := Subgroup.mem_subgroupOf.mp hs
    have h1 : g * (s : H)⁻¹ * g⁻¹ ∈ Q' := ⟨(s : H)⁻¹, Q.inv_mem hq, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    have hcP : ⁅(s : H), g⁆ ∈ P := by
      have : ⁅(s : H), g⁆ = (s : H) * (g * (s : H)⁻¹ * g⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact P.mul_mem (hQP hq) (hQ'P h1)
    refine ⟨⟨⁅(s : H), g⁆, hcP⟩, Subgroup.mem_subgroupOf.mpr (hcomm _ hq), ?_⟩
    show θ ⟨⁅(s : H), g⁆, hcP⟩ = θ s
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    have h2 : (⁅(s : H), g⁆)⁻¹ * (s : H) = g * (s : H) * g⁻¹ := by
      simp only [commutatorElement_def]; group
    have h3 : g * (s : H) * g⁻¹ ∈ Q' := ⟨(s : H), hq, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    change (⁅(s : H), g⁆)⁻¹ * (s : H) ∈ Q'
    rw [h2]
    exact h3
  have hMPodd : Odd (Nat.card ↥((M.subgroupOf P).map θ)) := by
    have h1 : Nat.card ↥((M.subgroupOf P).map θ) ∣ Nat.card ↥(M.subgroupOf P) :=
      Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥(M.subgroupOf P) ∣ Nat.card ↥M :=
      Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.subtype_injective _)
    exact hM.of_dvd_nat (h1.trans h2)
  have hSodd : Odd (Nat.card ↥((Q.subgroupOf P).map θ)) :=
    hMPodd.of_dvd_nat (Subgroup.card_dvd_of_le hSM)
  have hQQperf : ⁅Q, Q⁆ = Q := commutator_self_of_isQuasisimple
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hQ.1)
  have hSperf : ⁅Q.subgroupOf P, Q.subgroupOf P⁆ = Q.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hQP, hQQperf]
  have hperfθ : ⁅(Q.subgroupOf P).map θ, (Q.subgroupOf P).map θ⁆ = (Q.subgroupOf P).map θ := by
    rw [← Subgroup.map_commutator, hSperf]
  by_cases hbot : (Q.subgroupOf P).map θ = ⊥
  · have hle : Q.subgroupOf P ≤ θ.ker := (Subgroup.map_eq_bot_iff _).mp hbot
    rw [show θ.ker = Q'.subgroupOf P from QuotientGroup.ker_mk' _] at hle
    have hQQ'le : Q ≤ Q' := fun x hx =>
      Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hQP hx⟩ : ↥P) ∈ Q.subgroupOf P))
    have hQbot : Q = ⊥ := by
      have := Subgroup.commutator_mono (le_refl Q) hQQ'le
      rw [hcomm', hQQperf] at this
      exact le_bot_iff.mp this
    have := nontrivial_of_quasisimple hQ.1
    exact (Subgroup.nontrivial_iff_ne_bot Q).mp this hQbot
  · exact CFSG.GH74.GLS.Bg.Iii2.CMEngine.false_of_perfect_odd hperfθ hbot hSodd

omit [Finite H] in
theorem commute_of_mem_range_swapDiag {A : Subgroup H} {t : H}
    (hAB : ⁅A, conjSub t⁻¹ A⁆ = ⊥) (hA : CFSG.IsQuasisimple ↥A) {g : H}
    (hg : g ∈ (swapDiag hAB).range) (hc : ∀ w ∈ (swapDiag hAB).range, w * g = g * w) :
    (∀ a ∈ A, a * g = g * a) ∧ (∀ b ∈ conjSub t⁻¹ A, b * g = g * b) := by
  obtain ⟨c, rfl⟩ := hg
  have hcomm : ∀ x ∈ A, ∀ y ∈ conjSub t⁻¹ A, x * y = y * x := fun x hx y hy =>
    commute_of_commutator_conj_eq_bot hAB hx hy
  have hcA : (c : H) ∈ A := c.2
  have hc'B : t⁻¹ * (c : H) * t ∈ conjSub t⁻¹ A := conj_mem_conjSub hcA
  have hkey : ∀ a ∈ A, (c * a)⁻¹ * (a * c) ∈ conjSub t⁻¹ A := by
    intro a ha
    have ha'B : t⁻¹ * a * t ∈ conjSub t⁻¹ A := conj_mem_conjSub ha
    have hE := hc (swapDiag hAB ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
    simp only [swapDiag_apply] at hE
    have h1 : (c : H) * (t⁻¹ * a * t) = (t⁻¹ * a * t) * c := hcomm _ hcA _ ha'B
    have h2 : a * (t⁻¹ * (c : H) * t) = (t⁻¹ * c * t) * a := hcomm _ ha _ hc'B
    have E' : a * c * ((t⁻¹ * a * t) * (t⁻¹ * c * t)) = c * a * ((t⁻¹ * c * t) * (t⁻¹ * a * t)) := by
      calc a * c * ((t⁻¹ * a * t) * (t⁻¹ * c * t))
          = a * (c * (t⁻¹ * a * t)) * (t⁻¹ * c * t) := by group
        _ = a * ((t⁻¹ * a * t) * c) * (t⁻¹ * c * t) := by rw [h1]
        _ = (a * (t⁻¹ * a * t)) * c * (t⁻¹ * c * t) := by group
        _ = (a * (t⁻¹ * a * t)) * (c * (t⁻¹ * c * t)) := by group
        _ = ((c * (t⁻¹ * c * t)) * (a * (t⁻¹ * a * t))) := by rw [← hE]
        _ = c * ((t⁻¹ * c * t) * a) * (t⁻¹ * a * t) := by group
        _ = c * (a * (t⁻¹ * c * t)) * (t⁻¹ * a * t) := by rw [h2]
        _ = c * a * ((t⁻¹ * c * t) * (t⁻¹ * a * t)) := by group
    have hu : (c * a)⁻¹ * (a * c) =
        ((t⁻¹ * c * t) * (t⁻¹ * a * t)) * ((t⁻¹ * a * t) * (t⁻¹ * c * t))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq]
      calc (c * a)⁻¹ * (a * c) * ((t⁻¹ * a * t) * (t⁻¹ * c * t))
          = (c * a)⁻¹ * (a * c * ((t⁻¹ * a * t) * (t⁻¹ * c * t))) := by group
        _ = (c * a)⁻¹ * (c * a * ((t⁻¹ * c * t) * (t⁻¹ * a * t))) := by rw [E']
        _ = (t⁻¹ * c * t) * (t⁻¹ * a * t) := by group
    rw [hu]
    exact (conjSub t⁻¹ A).mul_mem ((conjSub t⁻¹ A).mul_mem hc'B ha'B)
      ((conjSub t⁻¹ A).inv_mem ((conjSub t⁻¹ A).mul_mem ha'B hc'B))
  have hcQ : ∀ q ∈ A, ⁅q, (c : H)⁻¹⁆ ∈ A := fun q hq => by
    simp only [commutatorElement_def, inv_inv]
    exact A.mul_mem (A.mul_mem (A.mul_mem hq (A.inv_mem hcA)) (A.inv_mem hq)) hcA
  have hcen : ∀ q ∈ A, ∀ x ∈ A, x * ⁅q, (c : H)⁻¹⁆ = ⁅q, (c : H)⁻¹⁆ * x := by
    intro q hq x hx
    have h1 := hkey q⁻¹ (A.inv_mem hq)
    have e : (c * q⁻¹)⁻¹ * (q⁻¹ * c) = ⁅q, (c : H)⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [e] at h1
    exact hcomm x hx _ h1
  have hcc : ∀ q ∈ A, q * c = c * q := fun q hq => by
    have h := commute_of_central_commutators hA.1 hcQ hcen q hq
    have : Commute q (c : H)⁻¹ := h
    simpa using (this.inv_right).eq
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have h1 : a * (t⁻¹ * (c : H) * t) = (t⁻¹ * c * t) * a := hcomm _ ha _ hc'B
    simp only [swapDiag_apply]
    calc a * (c * (t⁻¹ * c * t)) = (a * c) * (t⁻¹ * c * t) := by group
      _ = (c * a) * (t⁻¹ * c * t) := by rw [hcc a ha]
      _ = c * (a * (t⁻¹ * c * t)) := by group
      _ = c * ((t⁻¹ * c * t) * a) := by rw [h1]
      _ = (c * (t⁻¹ * c * t)) * a := by group
  · obtain ⟨a, ha, rfl⟩ := hb
    have hb' : (MulAut.conj t⁻¹) a = t⁻¹ * a * t := by
      simp only [MulAut.conj_apply, inv_inv]
    simp only [MulEquiv.coe_toMonoidHom, hb', swapDiag_apply]
    have h1 : (c : H) * (t⁻¹ * a * t) = (t⁻¹ * a * t) * c := hcomm _ hcA _ (conj_mem_conjSub ha)
    have h2 : (t⁻¹ * (c : H) * t) * (t⁻¹ * a * t) = (t⁻¹ * a * t) * (t⁻¹ * c * t) := by
      calc (t⁻¹ * (c : H) * t) * (t⁻¹ * a * t) = t⁻¹ * (c * a) * t := by group
        _ = t⁻¹ * (a * c) * t := by rw [hcc a ha]
        _ = (t⁻¹ * a * t) * (t⁻¹ * c * t) := by group
    calc (t⁻¹ * a * t) * (c * (t⁻¹ * c * t)) = ((t⁻¹ * a * t) * c) * (t⁻¹ * c * t) := by group
      _ = (c * (t⁻¹ * a * t)) * (t⁻¹ * c * t) := by rw [h1]
      _ = c * ((t⁻¹ * a * t) * (t⁻¹ * c * t)) := by group
      _ = c * ((t⁻¹ * c * t) * (t⁻¹ * a * t)) := by rw [h2]
      _ = (c * (t⁻¹ * c * t)) * (t⁻¹ * a * t) := by group

end Abstract

end CFSG.GH74.GLS.Bg.Pu5
