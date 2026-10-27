
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListPermLat
public import CFSG.Quasithin.Vol2.Ch1Comm

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

open CFSG.QuasithinUnique.Unc25K1.Six
open scoped commutatorElement

section Diag

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

theorem nonempty_mulEquiv_of_diag (a : List G) (b : List H) (hlen : a.length = b.length)
    (hD : Nat.card (Subgroup.closure {p : G × H | p ∈ a.zip b}) =
      Nat.card (Subgroup.closure {g | g ∈ a}))
    (hD' : Nat.card (Subgroup.closure {p : G × H | p ∈ a.zip b}) =
      Nat.card (Subgroup.closure {h | h ∈ b})) :
    Nonempty (↥(Subgroup.closure {g | g ∈ a}) ≃* ↥(Subgroup.closure {h | h ∈ b})) := by
  set D := Subgroup.closure {p : G × H | p ∈ a.zip b} with hDdef
  have hfst : D.map (MonoidHom.fst G H) = Subgroup.closure {g | g ∈ a} := by
    rw [hDdef, MonoidHom.map_closure]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_ofPred_eq, MonoidHom.coe_fst]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (List.of_mem_zip hp).1
    · intro hg
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
      exact ⟨(a[k], b[k]'(by omega)), List.mem_iff_getElem.mpr ⟨k, by simp [List.length_zip]; omega,
        by simp⟩, rfl⟩
  have hsnd : D.map (MonoidHom.snd G H) = Subgroup.closure {h | h ∈ b} := by
    rw [hDdef, MonoidHom.map_closure]
    congr 1
    ext h
    simp only [Set.mem_image, Set.mem_ofPred_eq, MonoidHom.coe_snd]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (List.of_mem_zip hp).2
    · intro hh
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hh
      exact ⟨(a[k]'(by omega), b[k]), List.mem_iff_getElem.mpr ⟨k, by simp [List.length_zip]; omega,
        by simp⟩, rfl⟩
  let π₁ : ↥D →* ↥(Subgroup.closure {g | g ∈ a}) :=
    ((MonoidHom.fst G H).comp D.subtype).codRestrict _ (fun d => by
      rw [← hfst]
      exact ⟨d.1, d.2, rfl⟩)
  let π₂ : ↥D →* ↥(Subgroup.closure {h | h ∈ b}) :=
    ((MonoidHom.snd G H).comp D.subtype).codRestrict _ (fun d => by
      rw [← hsnd]
      exact ⟨d.1, d.2, rfl⟩)
  have h1 : Function.Surjective π₁ := by
    rintro ⟨x, hx⟩
    rw [← hfst] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact ⟨⟨d, hd⟩, rfl⟩
  have h2 : Function.Surjective π₂ := by
    rintro ⟨x, hx⟩
    rw [← hsnd] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    exact ⟨⟨d, hd⟩, rfl⟩
  have hb1 : Function.Bijective π₁ := h1.bijective_of_nat_card_le hD.le
  have hb2 : Function.Bijective π₂ := h2.bijective_of_nat_card_le hD'.le
  exact ⟨(MulEquiv.ofBijective π₁ hb1).symm.trans (MulEquiv.ofBijective π₂ hb2)⟩

end Diag

theorem isEnc_prod {G H R S : Type*} [Group G] [Group H] [Mul R] [One R] [Mul S] [One S]
    {e₁ : G → R} {e₂ : H → S} (h₁ : IsEnc e₁) (h₂ : IsEnc e₂) :
    IsEnc (fun p : G × H => (e₁ p.1, e₂ p.2)) where
  inj := fun p q hpq => by
    have h1 := congrArg Prod.fst hpq
    have h2 := congrArg Prod.snd hpq
    exact Prod.ext (h₁.inj h1) (h₂.inj h2)
  map_mul := fun p q => by
    show (e₁ (p.1 * q.1), e₂ (p.2 * q.2)) = (e₁ p.1 * e₁ q.1, e₂ p.2 * e₂ q.2)
    rw [h₁.map_mul, h₂.map_mul]
  map_one := by
    show (e₁ 1, e₂ 1) = (1, 1)
    rw [h₁.map_one, h₂.map_one]

section DiagOK

variable {G H : Type} [Group G] [Group H] {R S : Type} [Mul R] [One R] [DecidableEq R] [Hashable R]
  [Mul S] [One S] [DecidableEq S] [Hashable S]

def diagOK (e₁ : G → R) (e₂ : H → S) (depth : ℕ) (a : List G) (b : List H) (n : ℕ) : Bool :=
  closedH (a.map e₁) (elts e₁ depth a) && (elts e₁ depth a).size == n &&
    closedH (b.map e₂) (elts e₂ depth b) && (elts e₂ depth b).size == n &&
    closedH ((a.zip b).map fun p => (e₁ p.1, e₂ p.2))
      (elts (fun p : G × H => (e₁ p.1, e₂ p.2)) depth (a.zip b)) &&
    (elts (fun p : G × H => (e₁ p.1, e₂ p.2)) depth (a.zip b)).size == n &&
    decide (a.length = b.length)

theorem nonempty_mulEquiv_of_diagOK [Finite G] [Finite H] {e₁ : G → R} {e₂ : H → S}
    (h₁ : IsEnc e₁) (h₂ : IsEnc e₂) {depth : ℕ} {a : List G} {b : List H} {n : ℕ}
    (hc : diagOK e₁ e₂ depth a b n = true) :
    Nat.card (Subgroup.closure {g | g ∈ a}) = n ∧
      Nonempty (↥(Subgroup.closure {g | g ∈ a}) ≃* ↥(Subgroup.closure {h | h ∈ b})) := by
  simp only [diagOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hca, hsa⟩, hcb⟩, hsb⟩, hcd⟩, hsd⟩, hlen⟩ := hc
  unfold elts at hca hsa hcb hsb hcd hsd
  have hA := card_closure_of_closedH h₁ a depth hca
  have hB := card_closure_of_closedH h₂ b depth hcb
  have hD := card_closure_of_closedH (isEnc_prod h₁ h₂) (a.zip b) depth hcd
  refine ⟨hA.trans hsa, nonempty_mulEquiv_of_diag a b hlen ?_ ?_⟩
  · rw [hD, hsd, hA, hsa]
  · rw [hD, hsd, hB, hsb]

end DiagOK

theorem commutator_le_of_card_eq_two_mul {G : Type*} [Group G] [Finite G] {A L : Subgroup G}
    (hAL : A ≤ L) (hcard : Nat.card L = 2 * Nat.card A) : ⁅L, L⁆ ≤ A := by
  have hidx : (A.subgroupOf L).index = 2 := by
    have h := Subgroup.card_mul_index (A.subgroupOf L)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hcard] at h
    have hpos : 0 < Nat.card A := Nat.card_pos
    have : Nat.card A * (A.subgroupOf L).index = Nat.card A * 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have : (A.subgroupOf L).Normal := Subgroup.normal_of_index_eq_two hidx
  have hQ : Nat.card (↥L ⧸ A.subgroupOf L) = 2 := hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (↥L ⧸ A.subgroupOf L) := isCyclic_of_prime_card hQ
  have hcomm : ∀ x y : ↥L ⧸ A.subgroupOf L, x * y = y * x := fun x y => by
    let := IsCyclic.commGroup (α := ↥L ⧸ A.subgroupOf L)
    exact mul_comm x y
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : (⁅(⟨x, hx⟩ : ↥L), ⟨y, hy⟩⁆ : ↥L) ∈ A.subgroupOf L := by
    rw [← QuotientGroup.eq_one_iff]
    rw [commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm (QuotientGroup.mk ⟨x, hx⟩) (QuotientGroup.mk ⟨y, hy⟩)]
    group
  exact Subgroup.mem_subgroupOf.mp h1

open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem perfectCore_subgroupOf_eq {G : Type*} [Group G] [Finite G] {M L A : Subgroup G}
    (hAL : A ≤ L) (hLM : L ≤ M) (hcomm : ⁅L, L⁆ ≤ A) (hperf : ⁅A, A⁆ = A) :
    perfectCore (L.subgroupOf M) = A.subgroupOf M := by
  have hAM : A ≤ M := hAL.trans hLM
  have hperfA : Group.IsPerfect ↥A := Subgroup.isPerfect_iff.mpr hperf
  have hperfN : Group.IsPerfect ↥(A.subgroupOf M) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hAM).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hAM).symm.surjective
  have hperfN' : ⁅A.subgroupOf M, A.subgroupOf M⁆ = A.subgroupOf M := Subgroup.isPerfect_iff.mp hperfN
  apply le_antisymm
  · calc perfectCore (L.subgroupOf M)
        = ⁅perfectCore (L.subgroupOf M), perfectCore (L.subgroupOf M)⁆ :=
          (perfectCore_perfect _).symm
      _ ≤ ⁅L.subgroupOf M, L.subgroupOf M⁆ :=
          Subgroup.commutator_mono (perfectCore_le _) (perfectCore_le _)
      _ ≤ A.subgroupOf M := by
          rw [Subgroup.commutator_le]
          intro x hx y hy
          rw [Subgroup.mem_subgroupOf]
          have hxL : (x : G) ∈ L := Subgroup.mem_subgroupOf.mp hx
          have hyL : (y : G) ∈ L := Subgroup.mem_subgroupOf.mp hy
          have : ((⁅x, y⁆ : ↥M) : G) = ⁅(x : G), (y : G)⁆ := by
            simp [commutatorElement_def]
          rw [this]
          exact hcomm (Subgroup.commutator_mem_commutator hxL hyL)
  · exact le_perfectCore_of_perfect (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hAL (Subgroup.mem_subgroupOf.mp hx))) hperfN'

end CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
