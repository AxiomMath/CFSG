module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12.Group
public import Mathlib.Data.Set.Finite.Lemmas
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Statements

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12
  CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {X : Type*} [Group X]

theorem conj_mem_of_relIndex_two {A T : Subgroup X} (hAT : A ≤ T) (h : A.relIndex T = 2)
    {t a : X} (ht : t ∈ T) (ha : a ∈ A) : t * a * t⁻¹ ∈ A := by
  have hidx : (A.subgroupOf T).index = 2 := h
  have hN := Subgroup.normal_of_index_eq_two hidx
  have := hN.conj_mem ⟨a, hAT ha⟩ ha ⟨t, ht⟩
  exact this

theorem mem_cent_of_comm {A : Subgroup X} {w x : X} (hxA : x ∈ A) (h : w * x = x * w) :
    x ∈ A ⊓ Subgroup.centralizer ({w} : Set X) := by
  refine Subgroup.mem_inf.2 ⟨hxA, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h' hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact h

theorem comm_of_mem_cent {A : Subgroup X} {w x : X} (hx : x ∈ A ⊓ Subgroup.centralizer ({w} : Set X)) :
    w * x = x * w := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 w (Set.mem_singleton w)


theorem mem_normalizer_of_mem {A T : Subgroup X} (hAT : A ≤ T) (h : A.relIndex T = 2) {t : X}
    (ht : t ∈ T) : t ∈ Subgroup.normalizer (A : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha; exact conj_mem_of_relIndex_two hAT h ht ha
  · intro ha
    have := conj_mem_of_relIndex_two hAT h (T.inv_mem ht) ha
    simpa [mul_assoc] using this

theorem card_of_relIndex_two {A T : Subgroup X} (hAT : A ≤ T) (h : A.relIndex T = 2) :
    Nat.card T = 2 * Nat.card A := by
  have := Subgroup.relIndex_mul_card (H := A) (K := T)
  have h2 : A ⊓ T = A := inf_eq_left.2 hAT
  rw [h2, h] at this
  omega

section Psi

variable {A T : Subgroup X}

@[expose] noncomputable def psi (hAT : A ≤ T) (hidx : A.relIndex T = 2) (hA : IsElemAb2 A) {w : X}
    (hw : w ∈ T) : ↥A →* ↥A :=
  MonoidHom.mk' (fun r => r * ⟨w * r * w⁻¹, conj_mem_of_relIndex_two hAT hidx hw r.2⟩) (by
    intro r s
    apply Subtype.ext
    have hcomm : ∀ u v : ↥A, (u : X) * v = v * u := fun u v => (hA u u.2).2 v v.2
    have hs : (s : X) * (w * r * w⁻¹) = (w * r * w⁻¹) * s :=
      (hA s s.2).2 _ (conj_mem_of_relIndex_two hAT hidx hw r.2)
    simp only [Subgroup.coe_mul]
    calc (r : X) * s * (w * (r * s) * w⁻¹)
        = r * (s * (w * r * w⁻¹)) * (w * s * w⁻¹) := by group
      _ = r * ((w * r * w⁻¹) * s) * (w * s * w⁻¹) := by rw [hs]
      _ = r * (w * r * w⁻¹) * (s * (w * s * w⁻¹)) := by group)

theorem psi_apply (hAT : A ≤ T) (hidx : A.relIndex T = 2) (hA : IsElemAb2 A) {w : X} (hw : w ∈ T)
    (r : ↥A) : ((psi hAT hidx hA hw r : ↥A) : X) = r * (w * r * w⁻¹) := rfl

end Psi

section Psi2

variable {A T : Subgroup X} (hAT : A ≤ T) (hidx : A.relIndex T = 2) (hA : IsElemAb2 A) {w : X} (hw : w ∈ T)
include hAT hidx hA hw

theorem psi_eq_one_iff {r : ↥A} : psi hAT hidx hA hw r = 1 ↔ w * (r : X) = r * w := by
  have hr2 : (r : X) * (r : X) = 1 := (hA r r.2).1
  constructor
  · intro h
    have h1 : (r : X) * (w * r * w⁻¹) = 1 := by
      have := congrArg Subtype.val h
      simpa [psi_apply] using this
    have h2 : w * (r : X) * w⁻¹ = r := by
      have h3 : w * (r : X) * w⁻¹ = (r : X)⁻¹ := eq_inv_of_mul_eq_one_right h1
      rw [h3]
      exact inv_eq_of_mul_eq_one_right hr2
    calc w * (r : X) = (w * r * w⁻¹) * w := by group
      _ = r * w := by rw [h2]
  · intro h
    apply Subtype.ext
    have h2 : w * (r : X) * w⁻¹ = r := by
      calc w * (r : X) * w⁻¹ = (r * w) * w⁻¹ := by rw [h]
        _ = r := by group
    simp [psi_apply, h2, hr2]

theorem psi_commute (hw2 : w * w = 1) (r : ↥A) :
    w * ((psi hAT hidx hA hw r : ↥A) : X) = ((psi hAT hidx hA hw r : ↥A) : X) * w := by
  have hu : w * (r : X) * w⁻¹ ∈ A := conj_mem_of_relIndex_two hAT hidx hw r.2
  have hcomm : (r : X) * (w * r * w⁻¹) = (w * r * w⁻¹) * r := (hA r r.2).2 _ hu
  have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
  rw [psi_apply]
  calc w * ((r : X) * (w * r * w⁻¹)) = w * ((w * r * w⁻¹) * r) := by rw [hcomm]
    _ = (w * w) * r * w⁻¹ * r := by group
    _ = (r : X) * w⁻¹ * r := by rw [hw2, one_mul]
    _ = (r : X) * w * r := by rw [hwi]
    _ = ((r : X) * (w * r * w⁻¹)) * w := by
        have : ((r : X) * (w * r * w⁻¹)) * w = r * w * r * (w⁻¹ * w) := by group
        rw [this, inv_mul_cancel, mul_one]

theorem card_ker_psi (hC : Nat.card ↥(A ⊓ Subgroup.centralizer ({w} : Set X)) = 4) :
    Nat.card (psi hAT hidx hA hw).ker = 4 := by
  rw [← hC]
  exact Nat.card_congr
    { toFun := fun r => ⟨(r.1 : X), mem_cent_of_comm r.1.2 ((psi_eq_one_iff hAT hidx hA hw).1 r.2)⟩
      invFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩,
        (psi_eq_one_iff hAT hidx hA hw (r := ⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩)).2
          (comm_of_mem_cent y.2)⟩
      left_inv := fun r => rfl
      right_inv := fun y => rfl }

variable [Finite X]

omit [Finite X] in
theorem card_range_psi (hcard : Nat.card A = 16)
    (hC : Nat.card ↥(A ⊓ Subgroup.centralizer ({w} : Set X)) = 4) :
    Nat.card (psi hAT hidx hA hw).range = 4 := by
  have h := Subgroup.card_ker_mul_card_range (psi hAT hidx hA hw)
  rw [card_ker_psi hAT hidx hA hw hC, hcard] at h
  omega

theorem exists_psi_eq (hw2 : w * w = 1) (hcard : Nat.card A = 16)
    (hC : Nat.card ↥(A ⊓ Subgroup.centralizer ({w} : Set X)) = 4) {b : X} (hbA : b ∈ A)
    (hbw : b * w = w * b) : ∃ r : ↥A, ((psi hAT hidx hA hw r : ↥A) : X) = b := by
  let g : ↥(psi hAT hidx hA hw).range → ↥(A ⊓ Subgroup.centralizer ({w} : Set X)) :=
    fun y => ⟨((y.1 : ↥A) : X), mem_cent_of_comm (y.1).2 (by
      obtain ⟨r, hr⟩ := y.2
      have := psi_commute hAT hidx hA hw hw2 r
      rw [hr] at this
      exact this)⟩
  have hinj : Function.Injective g := by
    intro y y' h
    have h1 := congrArg (fun z : ↥(A ⊓ Subgroup.centralizer ({w} : Set X)) => (z : X)) h
    exact Subtype.ext (Subtype.ext h1)
  have hbij : Function.Bijective g := by
    refine Function.Injective.bijective_of_nat_card_le hinj ?_
    rw [card_range_psi hAT hidx hA hw hcard hC, hC]
  obtain ⟨y, hy⟩ := hbij.2 ⟨b, mem_cent_of_comm hbA hbw.symm⟩
  obtain ⟨r, hr⟩ := y.2
  refine ⟨r, ?_⟩
  rw [hr]
  exact congrArg Subtype.val hy

omit [Finite X] in
theorem psi_conj_w (r : ↥A) :
    (r : X) * w * (r : X)⁻¹ = ((psi hAT hidx hA hw r : ↥A) : X) * w := by
  have hr2 : (r : X) * (r : X) = 1 := (hA r r.2).1
  have hri : (r : X)⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  rw [psi_apply, hri]
  group

theorem card_normalizer_ge (hw2 : w * w = 1) (hcard : Nat.card A = 16)
    (hC : Nat.card ↥(A ⊓ Subgroup.centralizer ({w} : Set X)) = 4) {B : Subgroup X} (hBA : B ≤ A)
    (hBc : ∀ r ∈ B, r * w = w * r) :
    4 * Nat.card B ≤
      Nat.card ↥(A ⊓ Subgroup.normalizer ((B ⊔ Subgroup.zpowers w : Subgroup X) : Set X)) := by
  classical
  have hex : ∀ b : ↥B, ∃ r : ↥A, ((psi hAT hidx hA hw r : ↥A) : X) = b :=
    fun b => exists_psi_eq hAT hidx hA hw hw2 hcard hC (hBA b.2) (hBc b b.2)
  choose rb hrb using hex
  have hBcz : ∀ a ∈ B, ∀ b ∈ Subgroup.zpowers w, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hBc a ha) m).eq
  let kA : ↥(A ⊓ Subgroup.centralizer ({w} : Set X)) → ↥A :=
    fun k => ⟨k.1, (Subgroup.mem_inf.1 k.2).1⟩
  have hψk : ∀ k, psi hAT hidx hA hw (kA k) = 1 := fun k =>
    (psi_eq_one_iff hAT hidx hA hw).2 (comm_of_mem_cent k.2)
  have hψr : ∀ (b : ↥B) k, psi hAT hidx hA hw (rb b * kA k) = ⟨b.1, hBA b.2⟩ := by
    intro b k
    rw [map_mul, hψk k, mul_one]
    exact Subtype.ext (hrb b)
  have hconj : ∀ (b : ↥B) k, ∀ e ∈ B ⊔ Subgroup.zpowers w,
      ((rb b * kA k : ↥A) : X) * e * ((rb b * kA k : ↥A) : X)⁻¹ ∈ B ⊔ Subgroup.zpowers w := by
    intro b k e he
    set r : ↥A := rb b * kA k with hr
    obtain ⟨a, ha, c, hc, rfl⟩ := mem_sup_of_commute hBcz he
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
    have h1 : (r : X) * (a * w ^ m) * (r : X)⁻¹ =
        ((r : X) * a * (r : X)⁻¹) * ((r : X) * w * (r : X)⁻¹) ^ m := by
      rw [conj_zpow]; group
    rw [h1]
    have hra : (r : X) * a * (r : X)⁻¹ = a := by
      have : (r : X) * a = a * r := (hA r r.2).2 a (hBA ha)
      rw [this]; group
    rw [hra, psi_conj_w hAT hidx hA hw r, hr, hψr b k]
    have hbE : (b : X) ∈ B ⊔ Subgroup.zpowers w := Subgroup.mem_sup_left b.2
    have hwE : w ∈ B ⊔ Subgroup.zpowers w := Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    exact mul_mem (Subgroup.mem_sup_left ha) (zpow_mem (mul_mem hbE hwE) m)
  have hr2 : ∀ (b : ↥B) k, ((rb b * kA k : ↥A) : X) * ((rb b * kA k : ↥A) : X) = 1 :=
    fun b k => (hA _ (rb b * kA k).2).1
  have hmem : ∀ (b : ↥B) k, ((rb b * kA k : ↥A) : X) ∈
      A ⊓ Subgroup.normalizer ((B ⊔ Subgroup.zpowers w : Subgroup X) : Set X) := by
    intro b k
    refine Subgroup.mem_inf.2 ⟨(rb b * kA k).2, Subgroup.mem_normalizer_iff.2 (fun e => ⟨?_, ?_⟩)⟩
    · exact hconj b k e
    · intro he
      have h3 := hconj b k _ he
      have hinv : ((rb b * kA k : ↥A) : X)⁻¹ = ((rb b * kA k : ↥A) : X) :=
        inv_eq_of_mul_eq_one_right (hr2 b k)
      have hinv2 : ((rb b * kA k : ↥A) : X)⁻¹ * ((rb b * kA k : ↥A) : X)⁻¹ = 1 := by
        rw [hinv]; exact hr2 b k
      have e' : ((rb b * kA k : ↥A) : X) * (((rb b * kA k : ↥A) : X) * e *
          ((rb b * kA k : ↥A) : X)⁻¹) * ((rb b * kA k : ↥A) : X)⁻¹ = e := by
        calc _ = (((rb b * kA k : ↥A) : X) * ((rb b * kA k : ↥A) : X)) * e *
              (((rb b * kA k : ↥A) : X)⁻¹ * ((rb b * kA k : ↥A) : X)⁻¹) := by group
          _ = e := by rw [hr2 b k, hinv2]; group
      rw [e'] at h3
      exact h3
  let W := A ⊓ Subgroup.normalizer ((B ⊔ Subgroup.zpowers w : Subgroup X) : Set X)
  let F : ↥B × ↥(A ⊓ Subgroup.centralizer ({w} : Set X)) → ↥W := fun p =>
    ⟨((rb p.1 * kA p.2 : ↥A) : X), hmem p.1 p.2⟩
  have hF : Function.Injective F := by
    rintro ⟨b, k⟩ ⟨b', k'⟩ h
    have h1 : rb b * kA k = rb b' * kA k' :=
      Subtype.ext (congrArg (fun z : ↥W => (z : X)) h)
    have h2 : (⟨b.1, hBA b.2⟩ : ↥A) = ⟨b'.1, hBA b'.2⟩ := by
      rw [← hψr b k, ← hψr b' k', h1]
    have hbb : b = b' := Subtype.ext (congrArg (fun z : ↥A => (z : X)) h2)
    subst hbb
    have h3 : kA k = kA k' := mul_left_cancel h1
    have : k = k' := Subtype.ext (congrArg (fun z : ↥A => (z : X)) h3)
    rw [this]
  have hle := Nat.card_le_card_of_injective F hF
  rw [Nat.card_prod, hC] at hle
  linarith

end Psi2


theorem card_le_two_mul [Finite X] {A T W : Subgroup X} (hidx : A.relIndex T = 2)
    {c : X} (hc : ∀ n ∈ W, c * n * c⁻¹ ∈ T) :
    Nat.card W ≤ 2 * Nat.card ↥(W ⊓ Hconj c A) := by
  have hidx' : (A.subgroupOf T).index = 2 := hidx
  have : (A.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hidx'
  let g : ↥W →* ↥T := MonoidHom.mk' (fun n => ⟨c * n.1 * c⁻¹, hc n.1 n.2⟩) (by
    intro a b
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group)
  let f : ↥W →* ↥T ⧸ A.subgroupOf T := (QuotientGroup.mk' (A.subgroupOf T)).comp g
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.range ≤ 2 := by
    have : Nat.card f.range ≤ Nat.card (↥T ⧸ A.subgroupOf T) := Subgroup.card_le_card_group f.range
    rw [← Subgroup.index_eq_card, hidx'] at this
    exact this
  have h3 : Nat.card f.ker ≤ Nat.card ↥(W ⊓ Hconj c A) := by
    refine Nat.card_le_card_of_injective
      (fun n : f.ker => (⟨(n.1 : X), Subgroup.mem_inf.2 ⟨n.1.2, ?_⟩⟩ : ↥(W ⊓ Hconj c A))) ?_
    · have h4 : f n.1 = 1 := MonoidHom.mem_ker.1 n.2
      have h5 : g n.1 ∈ A.subgroupOf T :=
        (QuotientGroup.eq_one_iff (N := A.subgroupOf T) (g n.1)).1 h4
      exact h5
    · intro n n' h
      have h6 := congrArg (fun z : ↥(W ⊓ Hconj c A) => (z : X)) h
      exact Subtype.ext (Subtype.ext h6)
  calc Nat.card W = Nat.card f.ker * Nat.card f.range := h1.symm
    _ ≤ Nat.card ↥(W ⊓ Hconj c A) * 2 := Nat.mul_le_mul h3 h2
    _ = 2 * Nat.card ↥(W ⊓ Hconj c A) := mul_comm _ _


theorem isSylow2In_of_le {T H : Subgroup X} (hT : IsSylow2In T ⊤) (hTH : T ≤ H) :
    IsSylow2In T H := by
  refine ⟨hTH, hT.2.1, ?_⟩
  have h1 := Subgroup.relIndex_mul_index hTH
  have h2 : ¬ 2 ∣ T.index := by
    have := hT.2.2
    rwa [Subgroup.relIndex_top_right] at this
  intro hdvd
  exact h2 (h1 ▸ Dvd.dvd.mul_right hdvd _)

section Extremal

variable [Finite X] {T A : Subgroup X}

theorem step_a (hT : IsSylow2In T ⊤) (hAT : A ≤ T) (hidx : A.relIndex T = 2)
    (hA : IsElemAb2 A) (hcard : Nat.card A = 16) {E : Subgroup X} {c₀ : X}
    (hE : ∀ e ∈ E, c₀ * e * c₀⁻¹ ∈ A) :
    ∃ c₁ : X, (∀ e ∈ E, c₁ * e * c₁⁻¹ ∈ A) ∧
      IsSylow2In (T ⊓ Subgroup.normalizer ((Hconj c₁⁻¹ E : Subgroup X) : Set X))
        (Subgroup.normalizer ((Hconj c₁⁻¹ E : Subgroup X) : Set X)) := by
  classical
  have hT32 : Nat.card T = 32 := by
    have := card_of_relIndex_two hAT hidx
    omega
  set Es : Subgroup X := Hconj c₀⁻¹ E with hEs
  have hEsA : Es ≤ A := by
    intro a ha
    have h1 : c₀⁻¹ * a * c₀ ∈ E := by simpa [hEs] using ha
    have := hE _ h1
    simpa [mul_assoc] using this
  set Ds : Subgroup X := Subgroup.normalizer (Es : Set X) with hDs
  have hAD : A ≤ Ds := by
    intro a ha
    rw [hDs, Subgroup.mem_normalizer_iff]
    intro h
    have hcom : ∀ e ∈ Es, a * e = e * a := fun e he => (hA a ha).2 e (hEsA he)
    constructor
    · intro he
      have := hcom h he
      have h3 : a * h * a⁻¹ = h := by rw [this]; group
      rw [h3]; exact he
    · intro he
      have hcm := hcom _ he
      have h4 : a * (a * h * a⁻¹) = a * h := by
        calc a * (a * h * a⁻¹) = (a * h * a⁻¹) * a := hcm
          _ = a * h := by group
      have h3 : a * h * a⁻¹ = h := mul_left_cancel h4
      rw [h3] at he; exact he
  have hAN : A ≤ T ⊓ Ds := le_inf hAT hAD
  obtain ⟨P', hP', hNP'⟩ := exists_sylow2_ge (A := T ⊓ Ds) (H := Ds) (IsPGroup.to_le hT.2.1 inf_le_left)
    inf_le_right
  by_cases hcase : Nat.card P' ≤ Nat.card ↥(T ⊓ Ds)
  · have hEq : T ⊓ Ds = P' := Subgroup.eq_of_le_of_card_ge hNP' hcase
    refine ⟨c₀, hE, ?_⟩
    rw [hEq]
    exact hP'
  · have hlt : Nat.card ↥(T ⊓ Ds) < Nat.card P' := not_le.1 hcase
    have h16 : 16 ≤ Nat.card ↥(T ⊓ Ds) := by
      have := Subgroup.card_le_of_le hAN
      omega
    obtain ⟨P'', hP'', hP'P''⟩ := exists_sylow2_ge (A := P') (H := ⊤) hP'.2.1 le_top
    have hP''card : Nat.card P'' = 32 := by
      rw [← hT32]; exact (sylow2_card_eq hP'' hT)
    have hdvd : Nat.card P' ∣ 32 := by
      rw [← hP''card]; exact Subgroup.card_dvd_of_le hP'P''
    have hP'32 : Nat.card P' = 32 := by
      obtain ⟨k, hk⟩ := hdvd
      rcases k with _ | _ | k
      · omega
      · omega
      · nlinarith
    have hP'eq : P' = P'' := Subgroup.eq_of_le_of_card_ge hP'P'' (by omega)
    have hP'S : IsSylow2In P' ⊤ := by rw [hP'eq]; exact hP''
    have hAP' : A ≤ P' := hAN.trans hNP'
    have hidxP' : A.relIndex P' = 2 := by
      have h5 := Subgroup.relIndex_mul_card (H := A) (K := P')
      have h6 : A ⊓ P' = A := inf_eq_left.2 hAP'
      rw [h6, hcard, hP'32] at h5
      omega
    have hTN : T ≤ Subgroup.normalizer (A : Set X) := fun t ht =>
      mem_normalizer_of_mem hAT hidx ht
    have hP'N : P' ≤ Subgroup.normalizer (A : Set X) := fun t ht =>
      mem_normalizer_of_mem hAP' hidxP' ht
    obtain ⟨n, hn, hPn⟩ := sylow2_exists_conj (isSylow2In_of_le hT hTN)
      (isSylow2In_of_le hP'S hP'N)
    refine ⟨n * c₀, ?_, ?_⟩
    · intro e he
      have h1 := (Subgroup.mem_normalizer_iff.1 hn (c₀ * e * c₀⁻¹)).1 (hE e he)
      have h2 : n * c₀ * e * (n * c₀)⁻¹ = n * (c₀ * e * c₀⁻¹) * n⁻¹ := by group
      rw [h2]; exact h1
    · have hE1 : ∀ a : X, a ∈ Hconj (n * c₀)⁻¹ E ↔ n⁻¹ * a * n ∈ Es := by
        intro a
        simp [hEs, mem_Hconj, mul_assoc]
      have hTN1 : T ≤ Subgroup.normalizer ((Hconj (n * c₀)⁻¹ E : Subgroup X) : Set X) := by
        intro t ht
        rw [Subgroup.mem_normalizer_iff]
        intro a
        have hp : n⁻¹ * t * n ∈ P' := by
          rw [hPn, mem_Hconj]
          have : n * (n⁻¹ * t * n) * n⁻¹ = t := by group
          rw [this]; exact ht
        have hpD : n⁻¹ * t * n ∈ Ds := hP'.1 hp
        rw [hDs, Subgroup.mem_normalizer_iff] at hpD
        rw [hE1, hE1, hpD (n⁻¹ * a * n)]
        have : n⁻¹ * t * n * (n⁻¹ * a * n) * (n⁻¹ * t * n)⁻¹ = n⁻¹ * (t * a * t⁻¹) * n := by
          group
        rw [this]
      rw [inf_eq_left.2 hTN1]
      exact isSylow2In_of_le hT hTN1

theorem extremal_conj (hT : IsSylow2In T ⊤) (hAT : A ≤ T) (hidx : A.relIndex T = 2)
    (hA : IsElemAb2 A) (hcard : Nat.card A = 16) {E : Subgroup X} {c₀ : X}
    (hE : ∀ e ∈ E, c₀ * e * c₀⁻¹ ∈ A) :
    ∃ c : X, (∀ e ∈ E, c * e * c⁻¹ ∈ A) ∧
      ∀ n ∈ T, n ∈ Subgroup.normalizer (E : Set X) → c * n * c⁻¹ ∈ T := by
  classical
  obtain ⟨c₁, hc₁, hsyl⟩ := step_a hT hAT hidx hA hcard hE
  set E₁ : Subgroup X := Hconj c₁⁻¹ E with hE₁
  set N₁ : Subgroup X := Subgroup.normalizer (E₁ : Set X) with hN₁
  have hE₁A : E₁ ≤ A := by
    intro y hy
    have h1 : c₁⁻¹ * y * c₁ ∈ E := by simpa [hE₁, mem_Hconj] using hy
    have := hc₁ _ h1
    simpa [mul_assoc] using this
  set M : Subgroup X := T ⊓ Subgroup.normalizer (E : Set X) with hM
  have hM2 : IsPGroup 2 ↥M := IsPGroup.to_le hT.2.1 inf_le_left
  set M₁ : Subgroup X := Hconj c₁⁻¹ M with hM₁
  have hM₁2 : IsPGroup 2 ↥M₁ :=
    hM2.comap_of_injective (MulAut.conj c₁⁻¹).toMonoidHom (MulAut.conj c₁⁻¹).injective
  have hM₁N : M₁ ≤ N₁ := by
    intro a ha
    have hm : c₁⁻¹ * a * c₁ ∈ M := by simpa [hM₁, mem_Hconj] using ha
    have hmN : c₁⁻¹ * a * c₁ ∈ Subgroup.normalizer (E : Set X) := (Subgroup.mem_inf.1 hm).2
    rw [hN₁, Subgroup.mem_normalizer_iff]
    intro y
    have hy : ∀ y : X, y ∈ E₁ ↔ c₁⁻¹ * y * c₁ ∈ E := by
      intro y; simp [hE₁, mem_Hconj]
    rw [hy, hy, Subgroup.mem_normalizer_iff.1 hmN (c₁⁻¹ * y * c₁)]
    have e : c₁⁻¹ * a * c₁ * (c₁⁻¹ * y * c₁) * (c₁⁻¹ * a * c₁)⁻¹ = c₁⁻¹ * (a * y * a⁻¹) * c₁ := by
      group
    rw [e]
  obtain ⟨Q, hQ, hM₁Q⟩ := exists_sylow2_ge (A := M₁) (H := N₁) hM₁2 hM₁N
  obtain ⟨d, hd, hQd⟩ := sylow2_exists_conj hsyl hQ
  refine ⟨d * c₁, ?_, ?_⟩
  · intro e he
    have h1 : c₁ * e * c₁⁻¹ ∈ E₁ := by simpa [hE₁, mem_Hconj, mul_assoc] using he
    have h2 := (Subgroup.mem_normalizer_iff.1 hd (c₁ * e * c₁⁻¹)).1 h1
    have e2 : d * c₁ * e * (d * c₁)⁻¹ = d * (c₁ * e * c₁⁻¹) * d⁻¹ := by group
    rw [e2]; exact hE₁A h2
  · intro n hnT hnN
    have hnM : n ∈ M := Subgroup.mem_inf.2 ⟨hnT, hnN⟩
    have ha : c₁ * n * c₁⁻¹ ∈ M₁ := by simpa [hM₁, mem_Hconj, mul_assoc] using hnM
    have hQa : c₁ * n * c₁⁻¹ ∈ Q := hM₁Q ha
    rw [hQd, mem_Hconj] at hQa
    have e2 : d * c₁ * n * (d * c₁)⁻¹ = d * (c₁ * n * c₁⁻¹) * d⁻¹ := by group
    rw [e2]
    exact (Subgroup.mem_inf.1 hQa).1

theorem no_fusion (hT : IsSylow2In T ⊤) (hAT : A ≤ T) (hidx : A.relIndex T = 2)
    (hA : IsElemAb2 A) (hcard : Nat.card A = 16)
    (hC : ∀ w ∈ T, w ∉ A → Nat.card ↥(A ⊓ Subgroup.centralizer ({w} : Set X)) = 4) :
    ∀ w ∈ T, w ∉ A → ∀ c : X, c * w * c⁻¹ ∉ A := by
  classical
  intro w₁ hw₁T hw₁A c₁ hc₁
  let S : Set X := {c | ∃ w ∈ T, w ∉ A ∧ c * w * c⁻¹ ∈ A}
  have hSne : S.Nonempty := ⟨c₁, w₁, hw₁T, hw₁A, hc₁⟩
  let ov : X → ℕ := fun c => Nat.card ↥(A ⊓ Hconj c A)
  obtain ⟨c₀, ⟨w₀, hw₀T, hw₀A, hc₀⟩, hmax⟩ := Set.exists_max_image S ov (Set.toFinite S) hSne
  set B : Subgroup X := A ⊓ Hconj c₀ A with hB
  have hBA : B ≤ A := inf_le_left
  have hw₀2 : w₀ * w₀ = 1 := by
    have h := (hA _ hc₀).1
    calc w₀ * w₀ = c₀⁻¹ * (c₀ * w₀ * c₀⁻¹ * (c₀ * w₀ * c₀⁻¹)) * c₀ := by group
      _ = 1 := by rw [h]; group
  have hBc : ∀ r ∈ B, r * w₀ = w₀ * r := by
    intro r hr
    have hrA : r ∈ A := (Subgroup.mem_inf.1 hr).1
    have hrc : c₀ * r * c₀⁻¹ ∈ A := (Subgroup.mem_inf.1 hr).2
    have h := (hA _ hrc).2 _ hc₀
    have h2 : c₀ * (r * w₀) * c₀⁻¹ = c₀ * (w₀ * r) * c₀⁻¹ := by
      calc c₀ * (r * w₀) * c₀⁻¹ = (c₀ * r * c₀⁻¹) * (c₀ * w₀ * c₀⁻¹) := by group
        _ = (c₀ * w₀ * c₀⁻¹) * (c₀ * r * c₀⁻¹) := h
        _ = c₀ * (w₀ * r) * c₀⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hBcz : ∀ a ∈ B, ∀ b ∈ Subgroup.zpowers w₀, a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (hBc a ha) m).eq
  set E : Subgroup X := B ⊔ Subgroup.zpowers w₀ with hE
  have hEc : ∀ e ∈ E, c₀ * e * c₀⁻¹ ∈ A := by
    intro e he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hBcz he
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have h1 : c₀ * (a * w₀ ^ m) * c₀⁻¹ = (c₀ * a * c₀⁻¹) * (c₀ * w₀ * c₀⁻¹) ^ m := by
      rw [conj_zpow]; group
    rw [h1]
    exact mul_mem (Subgroup.mem_inf.1 ha).2 (zpow_mem hc₀ m)
  obtain ⟨c, hcE, hcN⟩ := extremal_conj hT hAT hidx hA hcard hEc
  have hcS : c ∈ S := ⟨w₀, hw₀T, hw₀A, hcE w₀ (Subgroup.mem_sup_right (Subgroup.mem_zpowers w₀))⟩
  have hBle : B ≤ A ⊓ Hconj c A := fun r hr =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hr).1, hcE r (Subgroup.mem_sup_left hr)⟩
  have hov : Nat.card ↥(A ⊓ Hconj c A) ≤ Nat.card B := hmax c hcS
  have hBeq : B = A ⊓ Hconj c A := Subgroup.eq_of_le_of_card_ge hBle hov
  set W : Subgroup X := A ⊓ Subgroup.normalizer (E : Set X) with hW
  have hW4 : 4 * Nat.card B ≤ Nat.card W :=
    card_normalizer_ge hAT hidx hA hw₀T hw₀2 hcard (hC w₀ hw₀T hw₀A) hBA hBc
  have hWT : ∀ n ∈ W, c * n * c⁻¹ ∈ T := fun n hn =>
    hcN n (hAT (Subgroup.mem_inf.1 hn).1) (Subgroup.mem_inf.1 hn).2
  have hW2 : Nat.card W ≤ 2 * Nat.card ↥(W ⊓ Hconj c A) := card_le_two_mul hidx hWT
  have hWB : W ⊓ Hconj c A ≤ B := by
    intro r hr
    rw [hBeq]
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hr).1).1,
      (Subgroup.mem_inf.1 hr).2⟩
  have hcardWB : Nat.card ↥(W ⊓ Hconj c A) ≤ Nat.card B := Subgroup.card_le_of_le hWB
  have hBpos : 0 < Nat.card B := Nat.card_pos
  omega

end Extremal

end CFSG.GH74.GLS.Stage1.Thm6.Sec14.Rn
