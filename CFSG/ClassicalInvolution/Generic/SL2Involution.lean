module

public import CFSG.ClassicalInvolution.Generic.SL2Anticommute
public import CFSG.ClassicalInvolution.SL2Facts

public section

namespace CFSG.ClassicalInvolution.Generic

open scoped MatrixGroups
open CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {F : Type*} [Field F] {G : Type*} [Group G]

@[expose] def axisSub (E K : Subgroup G) : Subgroup G :=
  E ⊓ Subgroup.centralizer (K : Set G)

theorem mem_axisSub_iff {E K : Subgroup G} {x : G} :
    x ∈ axisSub E K ↔ x ∈ E ∧ ∀ k ∈ K, k * x = x * k := by
  simp [axisSub, Subgroup.mem_centralizer_iff]

@[expose] def centSub (φ : SL(2, F) →* G) (E : Subgroup G) : Subgroup SL(2, F) :=
  (Subgroup.centralizer (E : Set G)).comap φ

@[expose] def normSub (φ : SL(2, F) →* G) (E : Subgroup G) : Subgroup SL(2, F) :=
  (Subgroup.normalizer (E : Set G)).comap φ

structure DiagData (φ : SL(2, F) →* G) (E : Subgroup G) : Prop where
  inj : Function.Injective φ
  comm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  sq : ∀ x ∈ E, x * x = 1
  neg_mem : φ (-1) ∈ E
  diag : ∀ e ∈ E, ∃ g : GL (Fin 2) F, ∀ s : SL(2, F),
    e * φ s * e⁻¹ = φ (slConjugation 2 F g s)
  index_two : (axisSub E φ.range).relIndex E = 2

structure Witness (φ : SL(2, F) →* G) (E : Subgroup G) where
  a : G
  g : GL (Fin 2) F
  ha : a ∈ E
  na : a ∉ axisSub E φ.range
  split : ∀ x ∈ E, x ∈ axisSub E φ.range ∨ x * a ∈ axisSub E φ.range
  hg : ∀ s : SL(2, F), a * φ s * a⁻¹ = φ (slConjugation 2 F g s)
  inv : IsInvolDiag g

namespace DiagData

variable {φ : SL(2, F) →* G} {E : Subgroup G}

theorem inv_eq_self (hD : DiagData φ E) {a : G} (ha : a ∈ E) : a⁻¹ = a :=
  inv_eq_of_mul_eq_one_right (hD.sq a ha)

theorem nonempty_witness (hD : DiagData φ E) : Nonempty (Witness φ E) := by
  obtain ⟨a, ha, hxor⟩ := Subgroup.relIndex_eq_two_iff.mp hD.index_two
  have hna : a ∉ axisSub E φ.range := by
    intro hmem
    have h1 : (1 : G) ∈ axisSub E φ.range := (axisSub E φ.range).one_mem
    have := hxor 1 E.one_mem
    simp [Xor, hmem, h1] at this
  have hsplit : ∀ x ∈ E, x ∈ axisSub E φ.range ∨ x * a ∈ axisSub E φ.range := by
    intro x hx
    rcases hxor x hx with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inr h1
    · exact Or.inl h1
  obtain ⟨g, hg⟩ := hD.diag a ha
  have hainv := hD.inv_eq_self ha
  refine ⟨⟨a, g, ha, hna, hsplit, hg, ⟨?_, ?_⟩⟩⟩
  · intro s
    apply hD.inj
    have h1 := hg (slConjugation 2 F g s)
    rw [← hg s] at h1
    rw [← h1, hainv]
    calc a * (a * φ s * a) * a = (a * a) * φ s * (a * a) := by group
      _ = φ s := by rw [hD.sq a ha]; simp
  · by_contra hcon
    push Not at hcon
    apply hna
    rw [mem_axisSub_iff]
    refine ⟨ha, ?_⟩
    rintro _ ⟨s, rfl⟩
    have := hg s
    rw [hcon s] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm

end DiagData

theorem sl2_sq_eq_one (h2 : (2 : F) ≠ 0) {u : SL(2, F)} (hu : u * u = 1) : u = 1 ∨ u = -1 :=
  CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 u
    (inv_eq_of_mul_eq_one_right hu)

namespace Witness

variable {φ : SL(2, F) →* G} {E : Subgroup G} (W : Witness φ E)

theorem mul_phi (s : SL(2, F)) : W.a * φ s = φ (slConjugation 2 F W.g s) * W.a :=
  mul_inv_eq_iff_eq_mul.mp (W.hg s)

theorem phi_conj_a (s : SL(2, F)) :
    φ s * W.a * (φ s)⁻¹ = φ (s * (slConjugation 2 F W.g s)⁻¹) * W.a := by
  have h := W.mul_phi s⁻¹
  simp only [map_inv] at h
  rw [mul_assoc, h, map_mul, map_inv, mul_assoc]

theorem axis_comm {x : G} (hx : x ∈ axisSub E φ.range) (s : SL(2, F)) :
    φ s * x = x * φ s :=
  (mem_axisSub_iff.mp hx).2 (φ s) ⟨s, rfl⟩

theorem mem_centSub_iff (hD : DiagData φ E) (s : SL(2, F)) :
    s ∈ centSub φ E ↔ slConjugation 2 F W.g s = s := by
  rw [centSub, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    apply hD.inj
    rw [← W.hg s]
    exact mul_inv_eq_iff_eq_mul.mpr (h W.a W.ha)
  · intro h x hx
    rcases W.split x hx with hxc | hxc
    · exact (axis_comm hxc s).symm
    · obtain ⟨c, hcdef⟩ : ∃ c, c = x * W.a := ⟨_, rfl⟩
      have hcax : c ∈ axisSub E φ.range := hcdef ▸ hxc
      have hx' : x = c * W.a := by rw [hcdef, mul_assoc, hD.sq _ W.ha, mul_one]
      have hcomm : W.a * φ s = φ s * W.a := by rw [W.mul_phi s, h]
      rw [hx', mul_assoc, hcomm, ← mul_assoc, ← axis_comm hcax s, mul_assoc]

@[expose] def InS (s : SL(2, F)) : Prop :=
  slConjugation 2 F W.g s = s ∨ slConjugation 2 F W.g s = s * (-1)

theorem InS.inv {W : Witness φ E} {s : SL(2, F)} (hs : W.InS s) : W.InS s⁻¹ := by
  rcases hs with hs | hs
  · left
    rw [map_inv, hs]
  · right
    rw [map_inv, hs, _root_.mul_inv_rev, neg_one_inv]
    exact (mul_neg_one_comm _).symm

theorem conj_a_mem (hD : DiagData φ E) {s : SL(2, F)} (hs : W.InS s) :
    φ s * W.a * (φ s)⁻¹ ∈ E := by
  rw [W.phi_conj_a s]
  refine E.mul_mem ?_ W.ha
  rcases hs with hs | hs
  · rw [hs, mul_inv_cancel, map_one]
    exact E.one_mem
  · have h1 : s * (slConjugation 2 F W.g s)⁻¹ = -1 := by
      rw [hs, _root_.mul_inv_rev, neg_one_inv, ← mul_assoc, mul_neg_one_comm s, mul_assoc,
        mul_inv_cancel, mul_one]
    rw [h1]
    exact hD.neg_mem

theorem conj_mem (hD : DiagData φ E) {s : SL(2, F)} (hs : W.InS s) {x : G} (hx : x ∈ E) :
    φ s * x * (φ s)⁻¹ ∈ E := by
  rcases W.split x hx with hxc | hxc
  · rw [axis_comm hxc s]
    simpa using hx
  · obtain ⟨c, hcdef⟩ : ∃ c, c = x * W.a := ⟨_, rfl⟩
    have hcax : c ∈ axisSub E φ.range := hcdef ▸ hxc
    have hx' : x = c * W.a := by rw [hcdef, mul_assoc, hD.sq _ W.ha, mul_one]
    have hcE : c ∈ E := (mem_axisSub_iff.mp hcax).1
    have : φ s * x * (φ s)⁻¹ = c * (φ s * W.a * (φ s)⁻¹) := by
      rw [hx', ← mul_assoc (φ s) c W.a, axis_comm hcax s]
      group
    rw [this]
    exact E.mul_mem hcE (W.conj_a_mem hD hs)

theorem mem_normSub_iff (hD : DiagData φ E) (h2 : (2 : F) ≠ 0) (s : SL(2, F)) :
    s ∈ normSub φ E ↔ W.InS s := by
  rw [normSub, Subgroup.mem_comap, Subgroup.mem_normalizer_iff]
  constructor
  · intro hs
    have h1 : φ s * W.a * (φ s)⁻¹ ∈ E := (hs W.a).mp W.ha
    rw [W.phi_conj_a s] at h1
    have hu : φ (s * (slConjugation 2 F W.g s)⁻¹) ∈ E := by
      have := E.mul_mem h1 (E.inv_mem W.ha)
      simpa using this
    have huu : (s * (slConjugation 2 F W.g s)⁻¹) * (s * (slConjugation 2 F W.g s)⁻¹) = 1 := by
      apply hD.inj
      rw [map_mul, map_one]
      exact hD.sq _ hu
    rcases sl2_sq_eq_one h2 huu with h | h
    · left
      exact (mul_inv_eq_one.mp h).symm
    · right
      have h3 : (slConjugation 2 F W.g s)⁻¹ = s⁻¹ * (-1) := eq_inv_mul_iff_mul_eq.mpr h
      have h4 := inv_eq_iff_eq_inv.mp h3
      rw [h4, _root_.mul_inv_rev, neg_one_inv, inv_inv]
      exact (mul_neg_one_comm s).symm
  · intro hs x
    constructor
    · intro hx
      exact W.conj_mem hD hs hx
    · intro hx
      have := W.conj_mem hD hs.inv hx
      rw [map_inv] at this
      simpa [mul_assoc] using this

end Witness

namespace DiagData

variable {φ : SL(2, F) →* G} {E : Subgroup G}

theorem centSub_le_normSub : centSub φ E ≤ normSub φ E :=
  Subgroup.comap_mono (Subgroup.centralizer_le_normalizer _)

theorem exists_mem_normSub_not_mem_centSub [Finite F] (hD : DiagData φ E)
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) :
    ∃ w ∈ normSub φ E, w ∉ centSub φ E := by
  obtain ⟨W⟩ := hD.nonempty_witness
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  obtain ⟨w, hw⟩ := W.inv.exists_anticomm hodd h5
  refine ⟨w, (W.mem_normSub_iff hD h2 w).mpr (Or.inr hw), ?_⟩
  rw [W.mem_centSub_iff hD]
  exact IsInvolDiag.ne_of_anticomm (A := W.g) (sl2_neg_one_ne_one hodd) hw

theorem Witness.anticomm_of_mem [Finite F] {W : Witness φ E} (hD : DiagData φ E)
    (h2 : (2 : F) ≠ 0) {s : SL(2, F)} (hs : s ∈ normSub φ E) (hs' : s ∉ centSub φ E) :
    slConjugation 2 F W.g s = s * (-1) := by
  rcases (W.mem_normSub_iff hD h2 s).mp hs with h | h
  · exact absurd ((W.mem_centSub_iff hD s).mpr h) hs'
  · exact h

theorem sq_eq_neg_one_of_mem [Finite F] (hD : DiagData φ E) (hodd : Odd (Nat.card F))
    {s : SL(2, F)} (hs : s ∈ normSub φ E) (hs' : s ∉ centSub φ E) : s * s = -1 := by
  obtain ⟨W⟩ := hD.nonempty_witness
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  exact IsInvolDiag.sq_eq_neg_one (A := W.g) h2 (Witness.anticomm_of_mem hD h2 hs hs')

theorem mul_inv_mul_inv [Finite F] (hD : DiagData φ E) (hodd : Odd (Nat.card F))
    {s k : SL(2, F)} (hs : s ∈ normSub φ E) (hs' : s ∉ centSub φ E) (hk : k ∈ centSub φ E) :
    s * k * s⁻¹ = k⁻¹ := by
  obtain ⟨W⟩ := hD.nonempty_witness
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  exact W.inv.mul_inv_eq_inv h2 (Witness.anticomm_of_mem hD h2 hs hs')
    ((W.mem_centSub_iff hD k).mp hk)

theorem inv_mul_mem_centSub [Finite F] (hD : DiagData φ E) (hodd : Odd (Nat.card F))
    {s t : SL(2, F)} (hs : s ∈ normSub φ E) (hs' : s ∉ centSub φ E) (ht : t ∈ normSub φ E)
    (ht' : t ∉ centSub φ E) : s⁻¹ * t ∈ centSub φ E := by
  obtain ⟨W⟩ := hD.nonempty_witness
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  rw [W.mem_centSub_iff hD]
  exact IsInvolDiag.fixed_of_anticomm_inv_mul (A := W.g) (Witness.anticomm_of_mem hD h2 hs hs')
    (Witness.anticomm_of_mem hD h2 ht ht')

theorem relIndex_centSub_normSub [Finite F] (hD : DiagData φ E) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) : (centSub φ E).relIndex (normSub φ E) = 2 := by
  obtain ⟨w, hw, hw'⟩ := hD.exists_mem_normSub_not_mem_centSub hodd h5
  refine Subgroup.relIndex_eq_two_iff.mpr ⟨w, hw, fun b hb => ?_⟩
  by_cases hbC : b ∈ centSub φ E
  · refine Or.inr ⟨hbC, fun h => hw' ?_⟩
    have := (centSub φ E).mul_mem ((centSub φ E).inv_mem hbC) h
    simpa using this
  · refine Or.inl ⟨?_, hbC⟩
    have hbinv : b⁻¹ ∈ normSub φ E := (normSub φ E).inv_mem hb
    have hbinv' : b⁻¹ ∉ centSub φ E := fun h => hbC (by simpa using (centSub φ E).inv_mem h)
    simpa using hD.inv_mul_mem_centSub hodd hbinv hbinv' hw hw'

theorem natCard_normSub [Finite F] (hD : DiagData φ E) (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) : Nat.card (normSub φ E) = 2 * Nat.card (centSub φ E) := by
  have h := Subgroup.relIndex_mul_card (H := centSub φ E) (K := normSub φ E)
  rw [hD.relIndex_centSub_normSub hodd h5, inf_eq_left.mpr centSub_le_normSub] at h
  exact h.symm

theorem orderOf_phi_eq_four [Finite F] (hD : DiagData φ E) (hodd : Odd (Nat.card F))
    {s : SL(2, F)} (hs : s ∈ normSub φ E) (hs' : s ∉ centSub φ E) : orderOf (φ s) = 4 := by
  have h2 : s ^ 2 = -1 := by
    rw [pow_two]
    exact hD.sq_eq_neg_one_of_mem hodd hs hs'
  have hne : (-1 : SL(2, F)) ≠ 1 := sl2_neg_one_ne_one hodd
  have h4 : s ^ 2 ^ (1 + 1) = 1 := by
    have e : s ^ 2 ^ (1 + 1) = (s ^ 2) ^ 2 := by
      rw [← pow_mul]
      norm_num
    rw [e, h2]
    have := pow_orderOf_eq_one (-1 : SL(2, F))
    rwa [sl2_orderOf_neg_one hodd] at this
  have hord : orderOf s = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa [h2] using hne) h4
  exact (orderOf_injective φ hD.inj s).trans (hord.trans (by norm_num))

theorem conj_mem_axis {x : G} (hx : x ∈ axisSub E φ.range) (s : SL(2, F)) :
    φ s * x * (φ s)⁻¹ = x := by
  rw [Witness.axis_comm hx s]
  simp

theorem conj_not_mem_axis [Finite F] (hD : DiagData φ E) (hodd : Odd (Nat.card F))
    {s : SL(2, F)} (hs : s ∈ normSub φ E) (hs' : s ∉ centSub φ E) {x : G} (hx : x ∈ E)
    (hx' : x ∉ axisSub E φ.range) : φ s * x * (φ s)⁻¹ = x * φ (-1) := by
  obtain ⟨W⟩ := hD.nonempty_witness
  have h2 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd
  have hα := Witness.anticomm_of_mem (W := W) hD h2 hs hs'
  have hxc : x * W.a ∈ axisSub E φ.range := (W.split x hx).resolve_left hx'
  obtain ⟨c, hcdef⟩ : ∃ c, c = x * W.a := ⟨_, rfl⟩
  have hcax : c ∈ axisSub E φ.range := hcdef ▸ hxc
  have hx2 : x = c * W.a := by rw [hcdef, mul_assoc, hD.sq _ W.ha, mul_one]
  have h1 : s * (slConjugation 2 F W.g s)⁻¹ = -1 := by
    rw [hα, _root_.mul_inv_rev, neg_one_inv, ← mul_assoc, mul_neg_one_comm s, mul_assoc,
      mul_inv_cancel, mul_one]
  have h3 : φ s * W.a * (φ s)⁻¹ = φ (-1) * W.a := by rw [W.phi_conj_a s, h1]
  have hcomm : W.a * φ (-1) = φ (-1) * W.a := hD.comm _ W.ha _ hD.neg_mem
  have h4 : φ s * x * (φ s)⁻¹ = c * (φ s * W.a * (φ s)⁻¹) := by
    rw [hx2, ← mul_assoc (φ s) c W.a, Witness.axis_comm hcax s]
    group
  rw [h4, h3, ← hcomm, hx2, mul_assoc]

theorem mem_axis_or_mul_mem [Finite F] (hD : DiagData φ E) {x : G} (hx : x ∈ E) :
    ∃ a ∈ E, a ∉ axisSub E φ.range ∧ (x ∈ axisSub E φ.range ∨ x * a ∈ axisSub E φ.range) := by
  obtain ⟨W⟩ := hD.nonempty_witness
  exact ⟨W.a, W.ha, W.na, W.split x hx⟩

end DiagData

end CFSG.ClassicalInvolution.Generic
