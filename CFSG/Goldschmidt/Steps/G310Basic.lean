module

public import CFSG.Goldschmidt.StrongClosure
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowSupplements
import CFSG.LocalAnalysis.SignalizerFunctor.PrimeValueHull

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open

open CFSG.SignalizerFunctor.Helpers

section General

variable {X : Type*} [Group X]

theorem fusionIsSylowIn_map {p : ℕ} [Fact p.Prime] {M : Subgroup X} (S : Sylow p M) :
    fusionIsSylowIn p ((S : Subgroup M).map M.subtype) M := by
  refine ⟨Subgroup.map_subtype_le _, S.isPGroup'.map _, fun Q hQM hQ hSQ => ?_⟩
  have hle : (S : Subgroup M) ≤ Q.subgroupOf M := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hSQ ⟨x, hx, rfl⟩)
  have heq := S.3 (hQ.comap_subtype) hle
  rw [← heq]
  exact (Subgroup.map_subgroupOf_eq_of_le hQM).symm

theorem exists_sylow_of_fusionIsSylowIn {p : ℕ} [Fact p.Prime] {S M : Subgroup X}
    (h : fusionIsSylowIn p S M) : ∃ P : Sylow p M, (P : Subgroup M).map M.subtype = S := by
  obtain ⟨hSM, hS, hmax⟩ := h
  refine ⟨⟨S.subgroupOf M, hS.comap_subtype, fun {Q} hQ hSQ => ?_⟩, ?_⟩
  · have h1 := hmax (Q.map M.subtype) (Subgroup.map_subtype_le Q) (hQ.map M.subtype)
      fun s hs => ⟨⟨s, hSM hs⟩, hSQ (show (⟨s, hSM hs⟩ : M) ∈ S.subgroupOf M from hs), rfl⟩
    rw [← h1]
    exact (Subgroup.comap_map_eq_self_of_injective M.subtype_injective Q).symm
  · exact Subgroup.map_subgroupOf_eq_of_le hSM

theorem map_subtype_smul_sylow {q : ℕ} [Fact q.Prime] (M : Subgroup X) (g : M)
    (T : Sylow q M) :
    ((g • T : Sylow q M) : Subgroup M).map M.subtype =
      ((T : Subgroup M).map M.subtype).map (MulAut.conj (g : X)).toMonoidHom := by
  ext x
  simp only [Sylow.coe_subgroup_smul, Subgroup.mem_map,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · refine ⟨g⁻¹ * y * g, ?_, rfl⟩
      simpa [MulAut.smul_def, MulAut.conj_apply] using hy
    · simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨g * z * g⁻¹, ?_, ?_⟩
    · simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hz
    · simp [MulAut.conj_apply]

theorem conjSub_mono {g : X} {Q R : Subgroup X} (h : Q ≤ R) : conjSub g Q ≤ conjSub g R :=
  Subgroup.map_mono h

theorem conjSub_inf (g : X) (Q R : Subgroup X) :
    conjSub g (Q ⊓ R) = conjSub g Q ⊓ conjSub g R :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective

theorem conjSub_inv_conjSub (g : X) (Q : Subgroup X) : conjSub g⁻¹ (conjSub g Q) = Q := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_conjSub_inv (g : X) (Q : Subgroup X) : conjSub g (conjSub g⁻¹ Q) = Q := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_le_conjSub_iff {g : X} {Q R : Subgroup X} :
    conjSub g Q ≤ conjSub g R ↔ Q ≤ R := by
  refine ⟨fun h => ?_, conjSub_mono⟩
  have := conjSub_mono (g := g⁻¹) h
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem conjSub_bot (g : X) : conjSub g (⊥ : Subgroup X) = ⊥ := Subgroup.map_bot _

theorem conjSub_eq_bot_iff {g : X} {Q : Subgroup X} : conjSub g Q = ⊥ ↔ Q = ⊥ := by
  constructor
  · intro h
    rw [← conjSub_inv_conjSub g Q, h, conjSub_bot]
  · rintro rfl
    exact conjSub_bot g

theorem conjSub_eq_of_mem_normalizer {g : X} {A : Subgroup X}
    (hg : g ∈ Subgroup.normalizer (A : Set X)) : conjSub g A = A := by
  ext x
  rw [mem_conjSub]
  exact (Subgroup.mem_normalizer_iff.mp hg x).symm

theorem conj_mem_of_mem_normalizer {g a : X} {A : Subgroup X}
    (hg : g ∈ Subgroup.normalizer (A : Set X)) (ha : a ∈ A) : g * a * g⁻¹ ∈ A :=
  (Subgroup.mem_normalizer_iff.mp hg a).mp ha

theorem conj_inv_mem_of_mem_normalizer {g a : X} {A : Subgroup X}
    (hg : g ∈ Subgroup.normalizer (A : Set X)) (ha : a ∈ A) : g⁻¹ * a * g ∈ A := by
  have := conj_mem_of_mem_normalizer ((Subgroup.normalizer (A : Set X)).inv_mem hg) ha
  simpa using this

theorem le_normalizer_conjSub {A Q : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (A : Set X)) (hAQ : A ≤ Subgroup.normalizer (Q : Set X)) :
    A ≤ Subgroup.normalizer (conjSub g Q : Set X) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_conjSub, mem_conjSub]
  have ha' : g * a * g⁻¹ ∈ A := conj_mem_of_mem_normalizer hg ha
  have key := Subgroup.mem_normalizer_iff.mp (hAQ ha') (g * x * g⁻¹)
  have e : g * (a * x * a⁻¹) * g⁻¹ = g * a * g⁻¹ * (g * x * g⁻¹) * (g * a * g⁻¹)⁻¹ := by group
  rw [e]
  exact key

theorem conjSub_le_of_mem {Q Y : Subgroup X} {g : X} (hQ : Q ≤ Y) (hg : g ∈ Y) :
    conjSub g Q ≤ Y := by
  intro x hx
  rw [mem_conjSub] at hx
  have := Y.mul_mem (Y.mul_mem (Y.inv_mem hg) (hQ hx)) hg
  simpa [mul_assoc] using this

theorem mem_normalizer_of_conjSub_eq {g : X} {A : Subgroup X} (h : conjSub g A = A) :
    g ∈ Subgroup.normalizer (A : Set X) := by
  have hinv : g⁻¹ ∈ Subgroup.normalizer (A : Set X) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  simpa using Subgroup.inv_mem _ hinv

theorem conjSub_eq_map_conj (c : X) (S : Subgroup X) :
    S.map (MulAut.conj c).toMonoidHom = conjSub c⁻¹ S := by
  rw [conjSub, inv_inv]

theorem map_conjSub {Y : Type*} [Group Y] (f : X →* Y) (g : X) (Q : Subgroup X) :
    (conjSub g Q).map f = conjSub (f g) (Q.map f) := by
  ext y
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨f z, ⟨z, hz, rfl⟩, by simp [map_mul, map_inv]⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨g⁻¹ * z * g, ⟨z, hz, rfl⟩, by simp [map_mul, map_inv]⟩

theorem mul_comm_of_isMulCommutative {A : Subgroup X} (hA : IsMulCommutative A) {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) : x * y = y * x :=
  congrArg Subtype.val (hA.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem le_normalizer_inf {A Q C : Subgroup X} (hQ : A ≤ Subgroup.normalizer (Q : Set X))
    (hC : A ≤ Subgroup.normalizer (C : Set X)) :
    A ≤ Subgroup.normalizer ((Q ⊓ C : Subgroup X) : Set X) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_inf]
  rw [Subgroup.mem_normalizer_iff.mp (hQ ha) x, Subgroup.mem_normalizer_iff.mp (hC ha) x]

theorem le_normalizer_sup {A H K : Subgroup X} (hH : A ≤ Subgroup.normalizer (H : Set X))
    (hK : A ≤ Subgroup.normalizer (K : Set X)) :
    A ≤ Subgroup.normalizer ((H ⊔ K : Subgroup X) : Set X) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hH ha),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK ha)]

theorem le_normalizer_of_normal {A K : Subgroup X} [K.Normal] :
    A ≤ Subgroup.normalizer (K : Set X) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
  exact le_top

theorem le_normalizer_comap {Y : Type*} [Group Y] (f : X →* Y) {A : Subgroup X} {Q : Subgroup Y}
    (hQ : A.map f ≤ Subgroup.normalizer (Q : Set Y)) :
    A ≤ Subgroup.normalizer ((Q.comap f : Subgroup X) : Set X) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have ha' := hQ (Subgroup.mem_map_of_mem f ha)
  simp only [Subgroup.mem_comap, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp ha' (f x)

theorem normalizer_le_normalizer_centralizer' (S : Subgroup X) :
    Subgroup.normalizer (S : Set X) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set X) : Set X) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hx s hs
    have hs' : g⁻¹ * s * g ∈ S := conj_inv_mem_of_mem_normalizer hg hs
    have := hx _ hs'
    calc s * (g * x * g⁻¹) = g * ((g⁻¹ * s * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * s := by group
  · intro hx s hs
    have hs' : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hg s).mp hs
    have := hx _ hs'
    have e1 : g * (s * x) * g⁻¹ = g * s * g⁻¹ * (g * x * g⁻¹) := by group
    have e2 : g * (x * s) * g⁻¹ = g * x * g⁻¹ * (g * s * g⁻¹) := by group
    have := e1.trans (this.trans e2.symm)
    simpa using this

@[expose] def IsInv (A : Subgroup X) (p : ℕ) (Q : Subgroup X) : Prop :=
  IsPGroup p Q ∧ A ≤ Subgroup.normalizer (Q : Set X)

@[expose] def IsMaxInv (A : Subgroup X) (p : ℕ) (P : Subgroup X) : Prop :=
  Maximal (IsInv A p) P

@[expose] def NConj (A P P' : Subgroup X) : Prop :=
  ∃ n ∈ Subgroup.normalizer (A : Set X), P' = conjSub n P

@[expose] def IsMaxInvIn {X : Type*} [Group X] (Y A : Subgroup X) (p : ℕ) (P : Subgroup X) : Prop :=
  Maximal (fun Q : Subgroup X => Q ≤ Y ∧ IsInv A p Q) P

theorem isInv_subgroupOf {A W C : Subgroup X} {p : ℕ} (hW : IsInv A p W) :
    IsInv (A.subgroupOf C) p (W.subgroupOf C) := by
  refine ⟨hW.1.comap_subtype, fun a ha => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  exact Subgroup.mem_normalizer_iff.mp (hW.2 ha) x

theorem isInv_map_subtype {A C : Subgroup X} {p : ℕ} (hAC : A ≤ C) {R : Subgroup C}
    (hR : IsInv (A.subgroupOf C) p R) : IsInv A p (R.map C.subtype) := by
  refine ⟨hR.1.map _, fun a ha => ?_⟩
  set a' : C := ⟨a, hAC ha⟩
  have ha' : a' ∈ Subgroup.normalizer (R : Set C) := hR.2 (show a' ∈ A.subgroupOf C from ha)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨a' * y * a'⁻¹, (Subgroup.mem_normalizer_iff.mp ha' y).mp hy, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hyx' : (y : X) = a * x * a⁻¹ := hyx
    have hxC : x ∈ C := by
      have e : x = a⁻¹ * (y : X) * a := by rw [hyx']; group
      rw [e]
      exact C.mul_mem (C.mul_mem (C.inv_mem (hAC ha)) y.2) (hAC ha)
    refine ⟨⟨x, hxC⟩, (Subgroup.mem_normalizer_iff.mp ha' ⟨x, hxC⟩).mpr ?_, rfl⟩
    have : a' * ⟨x, hxC⟩ * a'⁻¹ = y := Subtype.ext hyx'.symm
    rw [this]
    exact hy

theorem mem_normalizer_of_subgroupOf {A C : Subgroup X} (hAC : A ≤ C) {y : C}
    (hy : y ∈ Subgroup.normalizer ((A.subgroupOf C : Subgroup C) : Set C)) :
    (y : X) ∈ Subgroup.normalizer (A : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h := (Subgroup.mem_normalizer_iff.mp hy ⟨x, hAC hx⟩).mp
      (show (⟨x, hAC hx⟩ : C) ∈ A.subgroupOf C from hx)
    exact h
  · intro hx
    have hxC : x ∈ C := by
      have e : x = (y : X)⁻¹ * ((y : X) * x * (y : X)⁻¹) * y := by group
      rw [e]
      exact C.mul_mem (C.mul_mem (C.inv_mem y.2) (hAC hx)) y.2
    exact (Subgroup.mem_normalizer_iff.mp hy ⟨x, hxC⟩).mpr hx

theorem map_subtype_conjSub (C : Subgroup X) (y : C) (R : Subgroup C) :
    (conjSub y R).map C.subtype = conjSub (y : X) (R.map C.subtype) := by
  ext x
  simp only [conjSub, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, ⟨z, hz, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨_, ⟨z, hz, rfl⟩, by simp⟩

theorem isMaxInv_subgroupOf {X : Type*} [Group X] {Y A : Subgroup X} (hAY : A ≤ Y) {p : ℕ}
    {P : Subgroup X} (hP : IsMaxInvIn Y A p P) : IsMaxInv (A.subgroupOf Y) p (P.subgroupOf Y) := by
  refine ⟨isInv_subgroupOf hP.prop.2, fun R hR hle => ?_⟩
  have hR' := isInv_map_subtype hAY hR
  have hPR : P ≤ R.map Y.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hP.prop.1]
    exact Subgroup.map_mono hle
  have heq := le_antisymm (hP.2 ⟨Subgroup.map_subtype_le R, hR'⟩ hPR) hPR
  intro x hx
  have : (x : X) ∈ R.map Y.subtype := ⟨x, hx, rfl⟩
  rw [heq] at this
  exact this

theorem mem_normalizer_of_map_eq' {L : Subgroup X} {x : X}
    (h : L.map (MulAut.conj x).toMonoidHom = L) : x ∈ Subgroup.normalizer (L : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzy
      exact mul_left_cancel (mul_right_cancel hzy)
    rwa [← this]

end General

section Inv

variable {X : Type*} [Group X] {A : Subgroup X} {p : ℕ}

theorem IsInv.conjSub {Q : Subgroup X} (hQ : IsInv A p Q) {g : X}
    (hg : g ∈ Subgroup.normalizer (A : Set X)) : IsInv A p (conjSub g Q) :=
  ⟨hQ.1.map _, le_normalizer_conjSub hg hQ.2⟩

theorem IsMaxInv.isInv {P : Subgroup X} (hP : IsMaxInv A p P) : IsInv A p P := hP.prop

theorem IsMaxInv.eq_of_le {P Q : Subgroup X} (hP : IsMaxInv A p P) (hQ : IsInv A p Q)
    (hPQ : P ≤ Q) : Q = P :=
  le_antisymm (hP.2 hQ hPQ) hPQ

theorem IsMaxInv.conjSub {P : Subgroup X} (hP : IsMaxInv A p P) {g : X}
    (hg : g ∈ Subgroup.normalizer (A : Set X)) : IsMaxInv A p (conjSub g P) := by
  refine ⟨hP.1.conjSub hg, fun Q hQ hle => ?_⟩
  have hg' : g⁻¹ ∈ Subgroup.normalizer (A : Set X) := Subgroup.inv_mem _ hg
  have h1 : P ≤ CFSG.Goldschmidt.conjSub g⁻¹ Q := by
    have := conjSub_mono (g := g⁻¹) hle
    rwa [conjSub_inv_conjSub] at this
  have h2 := hP.eq_of_le (hQ.conjSub hg') h1
  rw [← h2, conjSub_conjSub_inv]

theorem NConj.refl (P : Subgroup X) : NConj A P P :=
  ⟨1, Subgroup.one_mem _, (conjSub_one P).symm⟩

theorem NConj.symm {P P' : Subgroup X} (h : NConj A P P') : NConj A P' P := by
  obtain ⟨n, hn, rfl⟩ := h
  exact ⟨n⁻¹, Subgroup.inv_mem _ hn, (conjSub_inv_conjSub n P).symm⟩

theorem NConj.trans {P P' P'' : Subgroup X} (h : NConj A P P') (h' : NConj A P' P'') :
    NConj A P P'' := by
  obtain ⟨n, hn, rfl⟩ := h
  obtain ⟨m, hm, rfl⟩ := h'
  exact ⟨n * m, Subgroup.mul_mem _ hn hm, by rw [conjSub_mul]⟩

theorem nconj_conjSub (P : Subgroup X) {g : X} (hg : g ∈ Subgroup.normalizer (A : Set X)) :
    NConj A P (conjSub g P) :=
  ⟨g, hg, rfl⟩

end Inv

section Finite

variable {X : Type*} [Group X] [Finite X]

theorem exists_invariant_sylow_containing {r q : ℕ} (hr : r.Prime) (hq : q.Prime)
    {A M Q : Subgroup X} (hA : IsPGroup r A) (hM : ¬ r ∣ Nat.card M)
    (hAM : A ≤ Subgroup.normalizer (M : Set X)) (hQM : Q ≤ M) (hQ : IsPGroup q Q)
    (hAQ : A ≤ Subgroup.normalizer (Q : Set X)) :
    ∃ S : Subgroup X, fusionIsSylowIn q S M ∧ Q ≤ S ∧ A ≤ Subgroup.normalizer (S : Set X) := by
  have : Fact q.Prime := ⟨hq⟩
  let _action := conjugationAction A M hAM
  obtain ⟨S, hQS, hSinv⟩ := invariant_sylow_containing r q hr hq hA
    ((Nat.Prime.coprime_iff_not_dvd hr).mpr hM)
    (Q.subgroupOf M) hQ.comap_subtype (normalized_subgroup_invariant_subgroup A M Q hAM hAQ)
  refine ⟨(S : Subgroup M).map M.subtype, fusionIsSylowIn_map S, ?_, ?_⟩
  · have h := Subgroup.map_mono (f := M.subtype) hQS
    rwa [Subgroup.map_subgroupOf_eq_of_le hQM] at h
  · apply invariant_subgroup_map_normalized A M hAM (S : Subgroup M)
    change ∀ a : A, ∀ x ∈ (S : Subgroup M), a • x ∈ (S : Subgroup M)
    intro a x hx
    have himage := Subgroup.smul_mem_pointwise_smul x a (S : Subgroup M) hx
    rw [← Sylow.pointwise_smul_def, hSinv] at himage
    exact himage

theorem exists_conj_of_invariant_sylows {r q : ℕ} (hr : r.Prime) (hq : q.Prime)
    {A M S S' : Subgroup X} (hA : IsPGroup r A) (hM : ¬ r ∣ Nat.card M)
    (hAM : A ≤ Subgroup.normalizer (M : Set X)) (hS : fusionIsSylowIn q S M)
    (hS' : fusionIsSylowIn q S' M) (hAS : A ≤ Subgroup.normalizer (S : Set X))
    (hAS' : A ≤ Subgroup.normalizer (S' : Set X)) :
    ∃ c ∈ M ⊓ Subgroup.centralizer (A : Set X), S' = S.map (MulAut.conj c).toMonoidHom := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨T, rfl⟩ := exists_sylow_of_fusionIsSylowIn hS
  obtain ⟨T', rfl⟩ := exists_sylow_of_fusionIsSylowIn hS'
  let _action := conjugationAction A M hAM
  obtain ⟨g, hg, hgfix⟩ := invariant_sylows_conjugate_by_fixed_element r q hr hq A hA M
    ((Nat.Prime.coprime_iff_not_dvd hr).mpr hM) T T'
    (invariant_subgroup_sylow_fixed A M hAM q T hAS)
    (invariant_subgroup_sylow_fixed A M hAM q T' hAS')
  refine ⟨g, Subgroup.mem_inf.mpr ⟨g.2, Subgroup.mem_centralizer_iff.mpr ?_⟩, ?_⟩
  · intro a ha
    have h := congrArg Subtype.val (hgfix ⟨a, ha⟩)
    change a * (g : X) * a⁻¹ = g at h
    calc a * (g : X) = a * (g : X) * a⁻¹ * a := by group
      _ = g * a := by rw [h]
  · rw [← hg, map_subtype_smul_sylow]

theorem exists_isMaxInv {A : Subgroup X} {p : ℕ} {Q : Subgroup X} (hQ : IsInv A p Q) :
    ∃ P, Q ≤ P ∧ IsMaxInv A p P := by
  have : Finite (Subgroup X) := Finite.of_injective _ SetLike.coe_injective
  exact Finite.exists_le_maximal hQ

theorem exists_overgroup_of_le {A C : Subgroup X} {p : ℕ} (hAC : A ≤ C)
    (hT : ∀ Q Q' : Subgroup C, IsMaxInv (A.subgroupOf C) p Q →
      IsMaxInv (A.subgroupOf C) p Q' → NConj (A.subgroupOf C) Q Q')
    {W W' : Subgroup X} (hW : IsInv A p W) (hW' : IsInv A p W') (hWC : W ≤ C)
    (hW'C : W' ≤ C) :
    ∃ y ∈ Subgroup.normalizer (A : Set X), ∃ P₂ : Subgroup X,
      IsMaxInv A p P₂ ∧ conjSub y W ≤ P₂ ∧ W' ≤ P₂ := by
  obtain ⟨R, hWR, hR⟩ := exists_isMaxInv (isInv_subgroupOf (C := C) hW)
  obtain ⟨R', hW'R', hR'⟩ := exists_isMaxInv (isInv_subgroupOf (C := C) hW')
  obtain ⟨y, hy, hyR⟩ := hT R R' hR hR'
  obtain ⟨P₂, hR'P₂, hP₂⟩ := exists_isMaxInv (isInv_map_subtype hAC hR'.isInv)
  refine ⟨y, mem_normalizer_of_subgroupOf hAC hy, P₂, hP₂, ?_, ?_⟩
  · have h1 : W ≤ R.map C.subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hWC]
      exact Subgroup.map_mono hWR
    calc conjSub (y : X) W ≤ conjSub (y : X) (R.map C.subtype) := conjSub_mono h1
      _ = (conjSub y R).map C.subtype := (map_subtype_conjSub C y R).symm
      _ = R'.map C.subtype := by rw [hyR]
      _ ≤ P₂ := hR'P₂
  · calc W' = (W'.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hW'C).symm
      _ ≤ R'.map C.subtype := Subgroup.map_mono hW'R'
      _ ≤ P₂ := hR'P₂

theorem three_le_card {E : Subgroup X} {a b c : X} (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Nat.card E := by
  classical
  let f : Fin 3 → E := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem five_le_card {E : Subgroup X} {a b c d e : X} (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E)
    (hd : d ∈ E) (he : e ∈ E) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    5 ≤ Nat.card E := by
  classical
  let f : Fin 5 → E := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩, ⟨e, he⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem eq_of_card_four {E : Subgroup X} (hE4 : Nat.card E = 4) {a b c d y : X} (ha : a ∈ E)
    (hb : b ∈ E) (hc : c ∈ E) (hd : d ∈ E) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hy : y ∈ E) :
    y = a ∨ y = b ∨ y = c ∨ y = d := by
  by_contra h
  push Not at h
  obtain ⟨hya, hyb, hyc, hyd⟩ := h
  have := five_le_card ha hb hc hd hy hab hac had (Ne.symm hya) hbc hbd (Ne.symm hyb) hcd
    (Ne.symm hyc) (Ne.symm hyd)
  omega

theorem lt_inf_normalizer {p : ℕ} [Fact p.Prime] {R Q : Subgroup X} (hQ : IsPGroup p Q)
    (hRQ : R ≤ Q) (hne : R ≠ Q) : R < Q ⊓ Subgroup.normalizer (R : Set X) := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : R.subgroupOf Q < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hne (le_antisymm hRQ ?_)
    intro x hx
    have : (⟨x, hx⟩ : Q) ∈ R.subgroupOf Q := h ▸ Subgroup.mem_top _
    exact this
  obtain ⟨x, hxN, hxR⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine lt_of_le_of_ne (le_inf hRQ Subgroup.le_normalizer) fun h => hxR ?_
  have hx' : (x : X) ∈ Q ⊓ Subgroup.normalizer (R : Set X) :=
    ⟨x.2, mem_normalizer_of_subgroupOf hRQ hxN⟩
  rw [← h] at hx'
  exact hx'

theorem mem_normalizer_of_map_le {H : Subgroup X} {x : X}
    (h : H.map (MulAut.conj x).toMonoidHom ≤ H) : x ∈ Subgroup.normalizer (H : Set X) := by
  apply mem_normalizer_of_map_eq'
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]

end Finite

end CFSG.Goldschmidt.G310
