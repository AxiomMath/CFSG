module

public import CFSG.GH74.Uniqueness.Bender.Aut

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section ConjAut

variable {X : Type*} [Group X]

@[expose] noncomputable def conjAut (L : Subgroup X) : ↥(normalizer (L : Set X)) →* MulAut ↥L where
  toFun g :=
    { toFun := fun l => ⟨(g : X) * l * (g : X)⁻¹, (mem_normalizer_iff.mp g.2 l).mp l.2⟩
      invFun := fun l => ⟨(g : X)⁻¹ * l * g, by
        have h := (mem_normalizer_iff.mp (inv_mem g.2) l).mp l.2
        simpa using h⟩
      left_inv := fun l => Subtype.ext (by simp [mul_assoc])
      right_inv := fun l => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by ext l; simp
  map_mul' g h := by ext l; simp [mul_assoc]

theorem conjAut_apply (L : Subgroup X) (g : ↥(normalizer (L : Set X))) (l : ↥L) :
    ((conjAut L g l : ↥L) : X) = (g : X) * l * (g : X)⁻¹ := rfl

theorem conjAut_eq_one_iff (L : Subgroup X) (g : ↥(normalizer (L : Set X))) :
    conjAut L g = 1 ↔ (g : X) ∈ centralizer (L : Set X) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro l hl
    have := congrArg (fun σ : MulAut ↥L => ((σ ⟨l, hl⟩ : ↥L) : X)) h
    simp only [conjAut_apply, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro h
    ext l
    simp only [conjAut_apply, MulAut.one_apply]
    rw [mul_inv_eq_iff_eq_mul]
    exact ((mem_centralizer_iff.mp h) l l.2).symm

theorem conjAut_of_mem (L : Subgroup X) {l : X} (hl : l ∈ L) :
    conjAut L ⟨l, le_normalizer hl⟩ = MulAut.conj (⟨l, hl⟩ : ↥L) := by
  ext x
  simp [conjAut_apply]

theorem mul_inv_mem_centralizer_of_conjAut_eq (L : Subgroup X) (g : ↥(normalizer (L : Set X)))
    (l : ↥L) (h : conjAut L g = MulAut.conj l) :
    (g : X) * (l : X)⁻¹ ∈ centralizer (L : Set X) := by
  have hl : ((l⁻¹ : ↥L) : X) ∈ L := (l⁻¹).2
  have h1 : conjAut L (g * ⟨((l⁻¹ : ↥L) : X), le_normalizer hl⟩) = 1 := by
    rw [map_mul, h, conjAut_of_mem L hl]
    have e : (⟨((l⁻¹ : ↥L) : X), hl⟩ : ↥L) = l⁻¹ := rfl
    rw [e, ← map_mul, mul_inv_cancel, map_one]
  have h2 := (conjAut_eq_one_iff L _).mp h1
  simpa using h2

theorem mem_of_odd_index {G : Type*} [Group G] (I : Subgroup G) [I.Normal] (hodd : Odd I.index)
    {σ : G} {k : ℕ} (hσ : σ ^ 2 ^ k = 1) : σ ∈ I := by
  have h1 : orderOf (QuotientGroup.mk σ : G ⧸ I) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hσ, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk σ : G ⧸ I) ∣ I.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk σ : G ⧸ I) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases j with _ | j
    · simpa using hj
    · exfalso
      rw [hj, pow_succ] at h2
      exact (Nat.not_even_iff_odd.mpr hodd)
        (even_iff_two_dvd.mpr (dvd_trans (dvd_mul_left 2 _) h2))
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem conjAut_mem_inner_of_two (L : Subgroup X)
    (hodd : Odd (MulAut.conj : ↥L →* MulAut ↥L).range.index) (g : ↥(normalizer (L : Set X)))
    {k : ℕ} (hg : (g : X) ^ 2 ^ k = 1) :
    conjAut L g ∈ (MulAut.conj : ↥L →* MulAut ↥L).range := by
  have : (MulAut.conj : ↥L →* MulAut ↥L).range.Normal := Bender.normal_range_conj ↥L
  apply mem_of_odd_index _ hodd (k := k)
  rw [← map_pow]
  have hg' : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using hg)
  rw [hg', map_one]

theorem card_eq_card_inf_ker_mul {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (H : Subgroup G) : Nat.card H = Nat.card ↥(f.ker ⊓ H) * Nat.card ↥(H.map f) := by
  have h1 := Subgroup.card_mul_index (f.comp H.subtype).ker
  rw [Subgroup.index_ker] at h1
  have h2 : (f.comp H.subtype).range = H.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h3 : (f.comp H.subtype).ker = (f.ker ⊓ H).subgroupOf H := by
    ext x
    simp [Subgroup.mem_subgroupOf]
  have h4 : Nat.card ((f.ker ⊓ H).subgroupOf H) = Nat.card ↥(f.ker ⊓ H) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  rw [h2, h3, h4] at h1
  exact h1.symm

theorem ker_conjAut (L : Subgroup X) :
    (conjAut L).ker = (centralizer (L : Set X)).subgroupOf (normalizer (L : Set X)) := by
  ext g
  rw [MonoidHom.mem_ker, conjAut_eq_one_iff, mem_subgroupOf]

theorem card_eq_card_inf_centralizer_mul (L H : Subgroup X)
    (hH : H ≤ normalizer (L : Set X)) :
    Nat.card H = Nat.card ↥(centralizer (L : Set X) ⊓ H) *
      Nat.card ↥((H.subgroupOf (normalizer (L : Set X))).map (conjAut L)) := by
  have h := card_eq_card_inf_ker_mul (conjAut L) (H.subgroupOf (normalizer (L : Set X)))
  have e1 : Nat.card (H.subgroupOf (normalizer (L : Set X))) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
  have e3 : (conjAut L).ker ⊓ H.subgroupOf (normalizer (L : Set X)) =
      (centralizer (L : Set X) ⊓ H).subgroupOf (normalizer (L : Set X)) := by
    rw [ker_conjAut]
    ext x
    simp [mem_subgroupOf]
  have e2 : Nat.card ↥((conjAut L).ker ⊓ H.subgroupOf (normalizer (L : Set X))) =
      Nat.card ↥(centralizer (L : Set X) ⊓ H) := by
    rw [e3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hH)).toEquiv
  rw [e1, e2] at h
  exact h

end ConjAut

end CFSG.GH74.Uniqueness
