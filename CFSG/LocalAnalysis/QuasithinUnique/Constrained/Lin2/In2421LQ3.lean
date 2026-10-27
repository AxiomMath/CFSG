module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3TI

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

section W

variable {G : Type*} [Group G] {R Z : Subgroup G} {a : G}

theorem central_conj' (hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r) {z r : G} (hz : z ∈ Z) (hr : r ∈ R) :
    r⁻¹ * z * r = z := by
  have := hZc z hz r hr
  calc r⁻¹ * z * r = r⁻¹ * (z * r) := by group
    _ = r⁻¹ * (r * z) := by rw [this]
    _ = z := by group

theorem central_conj (hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r) {z r : G} (hz : z ∈ Z) (hr : r ∈ R) :
    r * z * r⁻¹ = z := by
  have := central_conj' hZc hz (R.inv_mem hr)
  simpa using this

variable (R Z a)

@[expose] def Wsub (hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r) : Subgroup G where
  carrier := {x | x ∈ R ∧ x⁻¹ * (a * x * a⁻¹) ∈ Z}
  mul_mem' := by
    rintro x y ⟨hxR, hx⟩ ⟨hyR, hy⟩
    refine ⟨R.mul_mem hxR hyR, ?_⟩
    have e : (x * y)⁻¹ * (a * (x * y) * a⁻¹) =
        (y⁻¹ * (x⁻¹ * (a * x * a⁻¹)) * y) * (y⁻¹ * (a * y * a⁻¹)) := by group
    rw [e, central_conj' hZc hx hyR]
    exact Z.mul_mem hx hy
  one_mem' := ⟨R.one_mem, by simp⟩
  inv_mem' := by
    rintro x ⟨hxR, hx⟩
    refine ⟨R.inv_mem hxR, ?_⟩
    have e : (x⁻¹)⁻¹ * (a * x⁻¹ * a⁻¹) = (x * (x⁻¹ * (a * x * a⁻¹)) * x⁻¹)⁻¹ := by group
    rw [e, central_conj hZc hx hxR]
    exact Z.inv_mem hx

variable {R Z a}

theorem Wsub_le {hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r} : Wsub R Z a hZc ≤ R := fun _ hx => hx.1

theorem Z_le_Wsub {hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r} (hZR : Z ≤ R)
    (hacent : ∀ z ∈ Z, a * z * a⁻¹ = z) : Z ≤ Wsub R Z a hZc := by
  intro z hz
  refine ⟨hZR hz, ?_⟩
  rw [hacent z hz]
  simp

theorem conj_mem_Wsub {hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r} (hZR : Z ≤ R)
    (hacent : ∀ z ∈ Z, a * z * a⁻¹ = z) (hcomm : ∀ x ∈ R, ∀ y ∈ R, ⁅x, y⁆ ∈ Z) {r w : G}
    (hr : r ∈ R) (hw : w ∈ Wsub R Z a hZc) : r * w * r⁻¹ ∈ Wsub R Z a hZc := by
  have h1 : ⁅r, w⁆ ∈ Wsub R Z a hZc := Z_le_Wsub hZR hacent (hcomm r hr w hw.1)
  have e : r * w * r⁻¹ = ⁅r, w⁆ * w := by rw [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ h1 hw

theorem orbit_mem_Wsub {hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r} (ha2 : a ^ 2 = 1)
    (hnR : ∀ r ∈ R, a * r * a⁻¹ ∈ R) (hsq : ∀ y ∈ R, y ^ 2 ∈ Z) {s : G} (hs : s ∈ R) :
    a⁻¹ * (s * a * s⁻¹) ∈ Wsub R Z a hZc := by
  have hinv : a⁻¹ = a := inv_eq_self_of_sq_eq_one' ha2
  have hoo : (s * a * s⁻¹) ^ 2 = 1 := by
    have : (s * a * s⁻¹) ^ 2 = s * a ^ 2 * s⁻¹ := by simp only [pow_two]; group
    rw [this, ha2]; group
  have ho : (s * a * s⁻¹)⁻¹ = s * a * s⁻¹ := inv_eq_self_of_sq_eq_one' hoo
  have hy : s * a * s⁻¹ * a ∈ R := by
    have : s * a * s⁻¹ * a = s * (a * s⁻¹ * a⁻¹) := by rw [hinv]; group
    rw [this]
    exact R.mul_mem hs (hnR _ (R.inv_mem hs))
  refine ⟨?_, ?_⟩
  · have : a⁻¹ * (s * a * s⁻¹) = (a * s * a⁻¹) * s⁻¹ := by rw [hinv]; group
    rw [this]
    exact R.mul_mem (hnR s hs) (R.inv_mem hs)
  · have e : (a⁻¹ * (s * a * s⁻¹))⁻¹ * (a * (a⁻¹ * (s * a * s⁻¹)) * a⁻¹) =
        (s * a * s⁻¹)⁻¹ * a * (s * a * s⁻¹) * a⁻¹ := by group
    rw [e, ho, hinv]
    have : s * a * s⁻¹ * a * (s * a * s⁻¹) * a = (s * a * s⁻¹ * a) ^ 2 := by
      simp only [pow_two]; group
    rw [this]
    exact hsq _ hy

theorem conj_eq_mul_of_mem_Wsub {hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r}
    (hacent : ∀ z ∈ Z, a * z * a⁻¹ = z) {w : G} (hw : w ∈ Wsub R Z a hZc) :
    ∃ z ∈ Z, w⁻¹ * a * w = a * z := by
  refine ⟨w⁻¹ * (a * w * a⁻¹), hw.2, ?_⟩
  have h1 := hacent _ hw.2
  have h2 : a * (w⁻¹ * (a * w * a⁻¹)) = (w⁻¹ * (a * w * a⁻¹)) * a := by
    calc a * (w⁻¹ * (a * w * a⁻¹)) = (a * (w⁻¹ * (a * w * a⁻¹)) * a⁻¹) * a := by group
      _ = (w⁻¹ * (a * w * a⁻¹)) * a := by rw [h1]
  rw [h2]
  group

theorem card_quotient_le_of_fiber {H : Type*} [Group H] {X : Type*} [Finite X] (f : H → X)
    (K : Subgroup H) (hf : ∀ s s' : H, f s = f s' ↔ s⁻¹ * s' ∈ K) :
    Nat.card (H ⧸ K) ≤ Nat.card X := by
  classical
  let g : H ⧸ K → X := Quotient.lift f
    (fun s s' h => (hf s s').2 (QuotientGroup.leftRel_apply.1 h))
  have hg : Function.Injective g := by
    intro p q hpq
    induction p using Quotient.inductionOn
    induction q using Quotient.inductionOn
    exact Quotient.sound (QuotientGroup.leftRel_apply.2 ((hf _ _).1 hpq))
  exact Nat.card_le_card_of_injective g hg

theorem card_R_le_card_Wsub [Finite G] {hZc : ∀ z ∈ Z, ∀ r ∈ R, r * z = z * r}
    (ha2 : a ^ 2 = 1) (hnR : ∀ r ∈ R, a * r * a⁻¹ ∈ R) (hsq : ∀ y ∈ R, y ^ 2 ∈ Z) :
    Nat.card R ≤ Nat.card (R ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) *
      Nat.card (Wsub R Z a hZc) := by
  classical
  set C : Subgroup G := R ⊓ Subgroup.centralizer ({a} : Set G) with hC
  let C' : Subgroup ↥R := C.subgroupOf R
  let f : ↥R → ↥(Wsub R Z a hZc) := fun s =>
    ⟨a⁻¹ * ((s : G) * a * (s : G)⁻¹), orbit_mem_Wsub ha2 hnR hsq s.2⟩
  have hf : ∀ s s' : ↥R, f s = f s' ↔ s⁻¹ * s' ∈ C' := by
    intro s s'
    simp only [f, Subtype.mk.injEq]
    rw [Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : (s : G) * a * (s : G)⁻¹ = (s' : G) * a * (s' : G)⁻¹ := mul_left_cancel h
      refine ⟨(s⁻¹ * s').2, ?_⟩
      show ((s⁻¹ * s' : ↥R) : G) ∈ Subgroup.centralizer ({a} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (s : G)⁻¹ * s' * a = (s : G)⁻¹ * ((s' : G) * a * (s' : G)⁻¹) * s' := by group
        _ = (s : G)⁻¹ * ((s : G) * a * (s : G)⁻¹) * s' := by rw [h1]
        _ = a * ((s : G)⁻¹ * s') := by group
    · intro h
      have h2 := Subgroup.mem_centralizer_singleton_iff.1 h.2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
      have key : (s : G) * a * (s : G)⁻¹ = (s' : G) * a * (s' : G)⁻¹ := by
        calc (s : G) * a * (s : G)⁻¹
            = (s : G) * (a * ((s : G)⁻¹ * (s' : G))) * ((s : G)⁻¹ * (s' : G))⁻¹ * (s : G)⁻¹ := by
              group
          _ = (s : G) * (((s : G)⁻¹ * (s' : G)) * a) * ((s : G)⁻¹ * (s' : G))⁻¹ * (s : G)⁻¹ := by
              rw [h2]
          _ = (s' : G) * a * (s' : G)⁻¹ := by group
      rw [key]
  have h1 := card_quotient_le_of_fiber f C' hf
  have h2 : Nat.card C' * C'.index = Nat.card ↥R := Subgroup.card_mul_index C'
  have h3 : Nat.card C' = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ R)).toEquiv
  have h4 : C'.index = Nat.card (↥R ⧸ C') := Subgroup.index_eq_card C'
  rw [← h2, h3, h4]
  exact Nat.mul_le_mul le_rfl h1

end W

end CFSG.QuasithinUnique.Lin2
