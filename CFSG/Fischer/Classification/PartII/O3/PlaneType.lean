module

public import CFSG.Fischer.Classification.PartII.O3.AffineF3
public import CFSG.Fischer.Classification.PartII.O3.Witness

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

namespace O3

variable {X : Type} [Group X] {E : Set X}

structure IsPlane (E : Set X) (φ : Pt → X) : Prop where
  mem : ∀ p, φ p ∈ E
  inj : Function.Injective φ
  ncomm : ∀ p q, p ≠ q → φ p * φ q ≠ φ q * φ p
  tau : ∀ p q, φ q * φ p * φ q = φ (-p - q)
  trans : ∀ t : Pt, ∃ g ∈ Subgroup.closure (Set.range φ), ∀ p, g * φ p * g⁻¹ = φ (p + t)

@[expose] def Cent (E : Set X) (φ : Pt → X) (v : X) : Prop :=
  v ∈ E ∧ ∀ p, φ p ∈ LocalClass E v

@[expose] def lineSet (r : Pt) : Set Pt := {x | x = 0 ∨ x = r ∨ x = r + r}

@[expose] def typ (E : Set X) (φ : Pt → X) (v : X) : Set Pt := {r | φ r ∈ fib E v (φ 0)}

theorem sub_zero_pt (r : Pt) : r - 0 = r := sub_zero r

theorem add_sub_cancel_left_pt (p s : Pt) : p + s - p = s := add_sub_cancel_left p s

theorem eq_zero_of_add_eq_pt : ∀ p s : Pt, p + s = p → s = 0 := by decide

theorem eq_sub_of_add_eq_pt : ∀ p q s : Pt, p + s = q → s = q - p := by decide

theorem eq_of_add_eq_neg_sub_pt : ∀ p q s : Pt, p + s = -p - q → s = q - p + (q - p) := by
  decide +kernel

namespace IsPlane

variable {φ : Pt → X} (hπ : IsPlane E φ) (hP : Pair X E)
include hπ hP

omit hπ hP in
theorem commute_of_mem_closure {v g : X} (hv : Cent E φ v)
    (hg : g ∈ Subgroup.closure (Set.range φ)) : g * v = v * g := by
  have hle : Subgroup.closure (Set.range φ) ≤ Subgroup.centralizer ({v} : Set X) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨p, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hv.2 p).2.2
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

omit hπ hP in
theorem ne_of_cent {v : X} (hv : Cent E φ v) (p : Pt) : v ≠ φ p := fun h =>
  (hv.2 p).2.1 h.symm

theorem exists_typ {v : X} (hv : Cent E φ v) :
    ∃ K : AddSubgroup Pt, (K : Set Pt) = typ E φ v ∧
      ∀ p q, φ q ∈ fib E v (φ p) ↔ q - p ∈ K := by
  obtain ⟨K, hK⟩ := exists_addSubgroup_of_equivalence (R := fun p q => φ q ∈ fib E v (φ p))
    ⟨fun p => Pair.mem_fib_self hP (hπ.mem p),
      fun {p q} h => Pair.fib_symm hP (hπ.mem p) h, fun h1 h2 => Pair.fib_trans hP h1 h2⟩
    (fun p q t h => by
      obtain ⟨g, hg, hgt⟩ := hπ.trans t
      refine ⟨hπ.mem _, ?_⟩
      have hgv := IsPlane.commute_of_mem_closure hv hg
      have h' := Pair.conj_mem_core_of_commute hP hgv h.2
      rwa [show g * (φ p * φ q) * g⁻¹ = g * φ p * g⁻¹ * (g * φ q * g⁻¹) by group,
        hgt, hgt] at h')
    (fun p q hq q' hq' => by
      have h := Pair.tau_mem_fib hP (hπ.mem p) hq hq'
      rwa [hπ.tau] at h)
  refine ⟨K, ?_, hK⟩
  ext r
  have h0 : r - 0 = r := by ext <;> simp
  simpa [typ, h0] using (hK 0 r).symm

theorem fib_iff {v : X} (hv : Cent E φ v) (p q : Pt) :
    φ q ∈ fib E v (φ p) ↔ q - p ∈ typ E φ v := by
  obtain ⟨K, hKt, hK⟩ := hπ.exists_typ hP hv
  rw [← hKt, SetLike.mem_coe, hK]

theorem isWit_iff {v : X} (hv : Cent E φ v) {p q : Pt} :
    IsWit E v (φ p) (φ q) ↔ q - p ∈ typ E φ v := by
  rw [← hπ.fib_iff hP hv]
  exact ⟨fun h => ⟨hπ.mem q, h.2⟩,
    fun h => ⟨⟨mem_localClass_symm hv.1 (hv.2 p), mem_localClass_symm hv.1 (hv.2 q)⟩, h.2⟩⟩

omit hP in
theorem isTauClosed_commute {e : X} : IsTauClosed {p | e * φ p = φ p * e} := by
  intro p hp q hq
  show e * φ (-p - q) = φ (-p - q) * e
  rw [← hπ.tau]
  calc e * (φ q * φ p * φ q) = φ q * (e * φ p) * φ q := by
        rw [← mul_assoc, ← mul_assoc, hq]
        simp only [mul_assoc]
    _ = φ q * φ p * φ q * e := by
        rw [hp, mul_assoc, mul_assoc, hq]
        simp only [mul_assoc]

theorem commute_add {v e : X} (hv : Cent E φ v) (he : e ∈ LocalClass E v)
    (heπ : ∀ p, e ≠ φ p) {p q : Pt} (hp : e * φ p = φ p * e) (hpq : q - p ∈ typ E φ v) :
    e * φ q = φ q * e :=
  Pair.commute_of_mem_fib hP he (hv.2 p) (heπ p) hp ((hπ.fib_iff hP hv p q).2 hpq)

theorem typ_eq_of_not_commute {v v' : X} (hv : Cent E φ v) (hv' : Cent E φ v')
    (hvv : v * v' ≠ v' * v) : typ E φ v = typ E φ v' := by
  have key : ∀ {a b : X}, Cent E φ a → Cent E φ b → a * b ≠ b * a →
      typ E φ a ⊆ typ E φ b := by
    intro a b ha hb hab r hr
    by_contra hrb
    have hwa : IsWit E a (φ 0) (φ r) := (hπ.isWit_iff hP ha).2 (by rwa [sub_zero_pt])
    have hnb : ¬ IsWit E b (φ 0) (φ r) := fun h => by
      have h' := (hπ.isWit_iff hP hb).1 h
      rw [sub_zero_pt] at h'
      exact hrb h'
    have hbmu : b ∈ muSet E (φ 0) (φ r) :=
      ⟨mem_localClass_symm hb.1 (hb.2 0), mem_localClass_symm hb.1 (hb.2 r)⟩
    exact hab (Pair.commute_of_isWit hP hwa hbmu hnb)
  exact Set.Subset.antisymm (key hv hv' hvv) (key hv' hv fun h => hvv h.symm)

theorem cent_of_isWit {v e : X} (hv : Cent E φ v) {p q s : Pt} (hpq : p ≠ q)
    (hs : s ∈ typ E φ v) (hsl : s ∉ lineSet (q - p))
    (hnw : ¬ IsWit E v (φ p) (φ q)) (he : IsWit E e (φ p) (φ q)) : Cent E φ e := by
  have hvmu : v ∈ muSet E (φ p) (φ q) :=
    ⟨mem_localClass_symm hv.1 (hv.2 p), mem_localClass_symm hv.1 (hv.2 q)⟩
  have hev : e * v = v * e := Pair.commute_of_isWit hP he hvmu hnw
  have heD : e ∈ LocalClass E v := ⟨he.1.1.1, fun h => hnw (h ▸ he), hev⟩
  have heπ : ∀ r, e ≠ φ r := by
    intro r her
    have h1 := he.1.1
    rw [her] at h1
    have hrp : r ≠ p := fun h => h1.2.1 (by rw [h])
    exact hπ.ncomm r p hrp h1.2.2
  have hsS : IsTauClosed {r | e * φ r = φ r * e} := hπ.isTauClosed_commute
  have hp : e * φ p = φ p * e := he.1.1.2.2
  have hq : e * φ q = φ q * e := he.1.2.2.2
  have hps : e * φ (p + s) = φ (p + s) * e :=
    hπ.commute_add hP hv heD heπ (q := p + s) hp (by rwa [add_sub_cancel_left_pt])
  have hs0 : s ≠ 0 := fun h => hsl (Or.inl h)
  have huniv := hsS.eq_univ_of_not_collinear hp hq hps (Ne.symm hpq)
    (fun h => hs0 (eq_zero_of_add_eq_pt p s h))
    (fun h => hsl (Or.inr (Or.inl (eq_sub_of_add_eq_pt p q s h))))
    (fun h => hsl (Or.inr (Or.inr (eq_of_add_eq_neg_sub_pt p q s h))))
  refine ⟨he.1.1.1, fun r => ⟨hπ.mem r, (heπ r).symm, ?_⟩⟩
  have hr : r ∈ {r | e * φ r = φ r * e} := huniv ▸ Set.mem_univ r
  exact hr.symm

theorem typ_cases {v : X} (hv : Cent E φ v) :
    typ E φ v = {0} ∨ typ E φ v = Set.univ ∨ ∃ r ≠ 0, typ E φ v = lineSet r := by
  obtain ⟨K, hKt, -⟩ := hπ.exists_typ hP hv
  rw [← hKt]
  have hline : ∀ r : Pt, (AddSubgroup.zmultiples r : Set Pt) = lineSet r := fun r => by
    ext x
    exact mem_zmultiples_iff
  rcases addSubgroup_cases K with h | h | h | h | h | h <;> subst h
  · exact Or.inl AddSubgroup.coe_bot
  · exact Or.inr (Or.inl AddSubgroup.coe_top)
  · exact Or.inr (Or.inr ⟨(1, 0), by decide, hline _⟩)
  · exact Or.inr (Or.inr ⟨(0, 1), by decide, hline _⟩)
  · exact Or.inr (Or.inr ⟨(1, 1), by decide, hline _⟩)
  · exact Or.inr (Or.inr ⟨(1, 2), by decide, hline _⟩)

end IsPlane

end O3

end CFSG.Fischer.Classification
