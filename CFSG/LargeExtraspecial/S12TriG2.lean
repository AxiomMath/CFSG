module

public import CFSG.LargeExtraspecial.S12TriG
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification

public section

namespace CFSG.LargeExtraspecial.S12Tri

open Equiv Subgroup

theorem card_mulAut_alternatingGroup_six_le :
    Nat.card (MulAut (alternatingGroup (Fin 6))) ≤ 1440 := by
  obtain ⟨-, hpair, hcount⟩ := a6_parts
  obtain ⟨h1, h2, h3, h4, h5, h6, hsa, hsb⟩ := a6Pair_iff.1 hpair
  set a : alternatingGroup (Fin 6) := ⟨a6a, Perm.mem_alternatingGroup.2 hsa⟩
  set b : alternatingGroup (Fin 6) := ⟨a6b, Perm.mem_alternatingGroup.2 hsb⟩
  have hgen : closure ({a, b} : Set (alternatingGroup (Fin 6))) = ⊤ :=
    closure_subtype_eq_top closure_a6
  let S : Set (alternatingGroup (Fin 6) × alternatingGroup (Fin 6)) :=
    {p | a6Pair (p.1 : Perm (Fin 6)) (p.2 : Perm (Fin 6)) = true}
  have hS : ∀ σ : MulAut (alternatingGroup (Fin 6)), (σ a, σ b) ∈ S := by
    intro σ
    show a6Pair ((σ a : alternatingGroup (Fin 6)) : Perm (Fin 6)) (σ b : alternatingGroup (Fin 6))
      = true
    have hmul : ((σ a : alternatingGroup (Fin 6)) : Perm (Fin 6)) *
        ((σ b : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
          ((σ (a * b) : alternatingGroup (Fin 6)) : Perm (Fin 6)) := by
      rw [map_mul, Subgroup.coe_mul]
    rw [a6Pair_iff, hmul]
    refine ⟨(coe_mulAut_pow_eq_one_iff σ a 2).2 h1, fun h => h2 ?_,
      (coe_mulAut_pow_eq_one_iff σ b 4).2 h3,
      fun h => h4 ((coe_mulAut_pow_eq_one_iff σ b 2).1 h),
      (coe_mulAut_pow_eq_one_iff σ (a * b) 5).2 (by rw [Subgroup.coe_mul]; exact h5),
      fun h => h6 ?_, Perm.mem_alternatingGroup.1 (σ a).2, Perm.mem_alternatingGroup.1 (σ b).2⟩
    · have := (coe_mulAut_pow_eq_one_iff σ a 1).1 (by rw [pow_one]; exact h)
      rwa [pow_one] at this
    · have := (coe_mulAut_pow_eq_one_iff σ (a * b) 1).1 (by rw [pow_one]; exact h)
      rwa [pow_one, Subgroup.coe_mul] at this
  have : Finite S := Set.toFinite _
  calc Nat.card (MulAut (alternatingGroup (Fin 6))) ≤ Nat.card S :=
        card_mulAut_le_of_closure hgen S hS
    _ ≤ Nat.card {q : Perm (Fin 6) × Perm (Fin 6) // a6Pair q.1 q.2 = true} := by
        refine Nat.card_le_card_of_injective
          (fun p => ⟨((p.1.1 : Perm (Fin 6)), (p.1.2 : Perm (Fin 6))), p.2⟩) ?_
        rintro ⟨⟨x, y⟩, hp⟩ ⟨⟨x', y'⟩, hp'⟩ h
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
        exact Subtype.ext (Prod.ext (Subtype.ext h.1) (Subtype.ext h.2))
    _ = a6Count := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        rfl
    _ ≤ 1440 := hcount

theorem card_mulAut_alternatingGroup_five_le :
    Nat.card (MulAut (alternatingGroup (Fin 5))) ≤ 120 := by
  obtain ⟨-, hpair, hcount⟩ := a5_parts
  obtain ⟨h1, h2, h3, h4, h5, h6, hsa, hsb⟩ := a5Pair_iff.1 hpair
  set a : alternatingGroup (Fin 5) := ⟨a5a, Perm.mem_alternatingGroup.2 hsa⟩
  set b : alternatingGroup (Fin 5) := ⟨a5b, Perm.mem_alternatingGroup.2 hsb⟩
  have hgen : closure ({a, b} : Set (alternatingGroup (Fin 5))) = ⊤ :=
    closure_subtype_eq_top closure_a5
  let S : Set (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
    {p | a5Pair (p.1 : Perm (Fin 5)) (p.2 : Perm (Fin 5)) = true}
  have hS : ∀ σ : MulAut (alternatingGroup (Fin 5)), (σ a, σ b) ∈ S := by
    intro σ
    show a5Pair ((σ a : alternatingGroup (Fin 5)) : Perm (Fin 5)) (σ b : alternatingGroup (Fin 5))
      = true
    have hmul : ((σ a : alternatingGroup (Fin 5)) : Perm (Fin 5)) *
        ((σ b : alternatingGroup (Fin 5)) : Perm (Fin 5)) =
          ((σ (a * b) : alternatingGroup (Fin 5)) : Perm (Fin 5)) := by
      rw [map_mul, Subgroup.coe_mul]
    rw [a5Pair_iff, hmul]
    refine ⟨(coe_mulAut_pow_eq_one_iff σ a 2).2 h1, fun h => h2 ?_,
      (coe_mulAut_pow_eq_one_iff σ b 3).2 h3, fun h => h4 ?_,
      (coe_mulAut_pow_eq_one_iff σ (a * b) 5).2 (by rw [Subgroup.coe_mul]; exact h5),
      fun h => h6 ?_, Perm.mem_alternatingGroup.1 (σ a).2, Perm.mem_alternatingGroup.1 (σ b).2⟩
    · have := (coe_mulAut_pow_eq_one_iff σ a 1).1 (by rw [pow_one]; exact h)
      rwa [pow_one] at this
    · have := (coe_mulAut_pow_eq_one_iff σ b 1).1 (by rw [pow_one]; exact h)
      rwa [pow_one] at this
    · have := (coe_mulAut_pow_eq_one_iff σ (a * b) 1).1 (by rw [pow_one]; exact h)
      rwa [pow_one, Subgroup.coe_mul] at this
  have : Finite S := Set.toFinite _
  calc Nat.card (MulAut (alternatingGroup (Fin 5))) ≤ Nat.card S :=
        card_mulAut_le_of_closure hgen S hS
    _ ≤ Nat.card {q : Perm (Fin 5) × Perm (Fin 5) // a5Pair q.1 q.2 = true} := by
        refine Nat.card_le_card_of_injective
          (fun p => ⟨((p.1.1 : Perm (Fin 5)), (p.1.2 : Perm (Fin 5))), p.2⟩) ?_
        rintro ⟨⟨x, y⟩, hp⟩ ⟨⟨x', y'⟩, hp'⟩ h
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
        exact Subtype.ext (Prod.ext (Subtype.ext h.1) (Subtype.ext h.2))
    _ = a5Count := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        rfl
    _ ≤ 120 := hcount

theorem nonempty_mulEquiv_alternatingGroup_five_of_card_sixty {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hG : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨P⟩ : Nonempty (Sylow 5 G) := inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity, hG, show (60 : ℕ) = 5 * 12 by rfl,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hnot_normal : ¬ (P : Subgroup G).Normal := fun hN => by
    rcases hN.eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hP
      omega
    · rw [h, Subgroup.card_top, hG] at hP
      omega
  have hcard : Nat.card (Sylow 5 G) = 6 := by
    have hmod := card_sylow_modEq_one 5 G
    have hdvd : Nat.card (Sylow 5 G) ∣ 12 := by
      have h := P.card_dvd_index
      rwa [(P : Subgroup G).index_eq_card, show Nat.card (G ⧸ (P : Subgroup G)) = 12 by
        have := (P : Subgroup G).card_mul_index
        rw [hP, hG, (P : Subgroup G).index_eq_card] at this
        omega] at h
    have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have hne1 : Nat.card (Sylow 5 G) ≠ 1 := fun h1 => by
      have : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hnot_normal (Sylow.normal_of_subsingleton P)
    unfold Nat.ModEq at hmod
    interval_cases h : Nat.card (Sylow 5 G) <;> simp_all
  have hfaithful : FaithfulSMul G (Sylow 5 G) := by
    let φ := MulAction.toPermHom G (Sylow 5 G)
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with hk | hk
    · refine ⟨fun {g h} hgh => ?_⟩
      have : φ g = φ h := Equiv.ext hgh
      exact (MonoidHom.ker_eq_bot_iff φ).mp hk this
    · refine absurd ?_ hnot_normal
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
      intro g _
      have hg : g ∈ φ.ker := hk ▸ Subgroup.mem_top g
      exact Sylow.smul_eq_iff_mem_normalizer.mp
        (congrArg (fun σ : Equiv.Perm (Sylow 5 G) => σ P) hg)
  exact CFSG.Glauberman.Dickson.huppert_II_8_25_transitive_degree_six_order_sixty
    (Ω := Sylow 5 G) inferInstance hcard hG

theorem card_mulAut_congr {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    Nat.card (MulAut H) = Nat.card (MulAut K) :=
  Nat.card_congr
    { toFun := fun σ => (e.symm.trans σ).trans e
      invFun := fun τ => (e.trans τ).trans e.symm
      left_inv := fun σ => by ext x; simp
      right_inv := fun τ => by ext x; simp }

theorem card_le_card_mulAut {Y : Type*} [Group Y] [Finite Y] {Q : Subgroup Y} [Q.Normal]
    (hC : ∀ y : Y, (∀ q ∈ Q, y * q = q * y) → y = 1) : Nat.card Y ≤ Nat.card (MulAut Q) := by
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun σ : MulAut Q => (σ : Q → Q)) DFunLike.coe_injective
  refine Nat.card_le_card_of_injective MulAut.conjNormal ?_
  rw [injective_iff_map_eq_one]
  intro y hy
  refine hC y fun q hq => ?_
  have h := congrArg (fun σ : MulAut Q => ((σ ⟨q, hq⟩ : Q) : Y)) hy
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
  calc y * q = y * q * y⁻¹ * y := by group
    _ = q * y := by rw [h]

theorem false_of_alternating_six
    {Y : Type*} [Group Y] [Finite Y] {Q : Subgroup Y} [Q.Normal]
    (e : Q ≃* alternatingGroup (Fin 6)) (hC : ∀ y : Y, (∀ q ∈ Q, y * q = q * y) → y = 1)
    (h6 : 6 * Nat.card Q ≤ Nat.card Y) : False := by
  have h1 := card_le_card_mulAut hC
  rw [card_mulAut_congr e] at h1
  have h2 := card_mulAut_alternatingGroup_six_le
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin,
    show (6 : ℕ).factorial / 2 = 360 from rfl] at h6
  omega

theorem false_of_card_sixty
    {Y : Type} [Group Y] [Finite Y] {Q : Subgroup Y} [Q.Normal]
    (hs : IsSimpleGroup Q) (h60 : Nat.card Q = 60)
    (hC : ∀ y : Y, (∀ q ∈ Q, y * q = q * y) → y = 1) (h6 : 6 * Nat.card Q ≤ Nat.card Y) :
    False := by
  obtain ⟨e⟩ := nonempty_mulEquiv_alternatingGroup_five_of_card_sixty h60
  have h1 := card_le_card_mulAut hC
  rw [card_mulAut_congr e] at h1
  have h2 := card_mulAut_alternatingGroup_five_le
  rw [h60] at h6
  omega

end CFSG.LargeExtraspecial.S12Tri
