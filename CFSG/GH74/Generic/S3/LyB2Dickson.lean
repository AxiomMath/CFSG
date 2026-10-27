module

public import CFSG.Dihedral.Glauberman.DicksonMaxUp
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import CFSG.GH74.Generic.Front.OuterModels
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.Glauberman CFSG.Glauberman.Dickson CFSG.BenderSuzuki.MatrixGroups Subgroup
open scoped commutatorElement

theorem false_of_solvable_surj {H S : Type} [Group H] [Group S] (hH : Group.IsSolvable H)
    (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) (ψ : H →* S)
    (hψ : Function.Surjective ψ) : False := by
  have : Group.IsSolvable S := Group.isSolvable_of_surjective hψ
  obtain ⟨a, b, hab⟩ := hnab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := S)).2 inferInstance a b)

theorem not_perfect_of_index_two {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : N.index = 2) : ¬ Group.IsPerfect G := by
  intro hG
  have : N.Normal := Subgroup.normal_of_index_eq_two hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (G ⧸ N) = 2 := hN
  have : IsCyclic (G ⧸ N) := isCyclic_of_prime_card hcard
  let : CommGroup (G ⧸ N) := IsCyclic.commGroup
  have hcomm : ∀ a b : G, ⁅a, b⁆ ∈ N := by
    intro a b
    have h1 : ⁅(QuotientGroup.mk' N) a, (QuotientGroup.mk' N) b⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    rw [← map_commutatorElement] at h1
    exact (QuotientGroup.eq_one_iff _).1 h1
  have hle : commutator G ≤ N := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro g _ h _
    exact hcomm g h
  rw [hG.commutator_eq_top, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hN
  omega

theorem isSolvable_of_comm {H : Type} [Group H] (h : ∀ a b : H, a * b = b * a) :
    Group.IsSolvable H := by
  let : CommGroup H := { ‹Group H› with mul_comm := h }
  infer_instance

theorem card_alternating_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem isSolvable_of_normal_sup_cyclic {H : Type} [Group H] (N C : Subgroup H) [N.Normal]
    (hN : ∀ a b : N, a * b = b * a) (hC : IsCyclic C) (hsup : N ⊔ C = ⊤) : Group.IsSolvable H := by
  have hNs : Group.IsSolvable N := isSolvable_of_comm hN
  have hq : ∀ a b : H ⧸ N, a * b = b * a := by
    have hC' : ∀ a b : C, a * b = b * a := by
      let : CommGroup C := IsCyclic.commGroup
      exact fun a b => mul_comm a b
    have hrep : ∀ a : H ⧸ N, ∃ c : C, (QuotientGroup.mk (c : H) : H ⧸ N) = a := by
      intro a
      obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective a
      have hh : h ∈ (N ⊔ C : Subgroup H) := by rw [hsup]; trivial
      rw [← SetLike.mem_coe, Subgroup.normal_mul] at hh
      obtain ⟨n, hn, c, hc, rfl⟩ := hh
      exact ⟨⟨c, hc⟩, by rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]⟩
    intro a b
    obtain ⟨c₁, rfl⟩ := hrep a
    obtain ⟨c₂, rfl⟩ := hrep b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact congrArg Subtype.val (hC' c₁ c₂)
  have hQs : Group.IsSolvable (H ⧸ N) := isSolvable_of_comm hq
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem card_eq_of_simple_surj {H S : Type} [Group H] [Group S] (hH : IsSimpleGroup H)
    (hS : IsSimpleGroup S) (ψ : H →* S) (hψ : Function.Surjective ψ) :
    Nat.card S = Nat.card H := by
  have hker : ψ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha⟩ : ∃ a : S, a ≠ 1 := exists_ne 1
      obtain ⟨h', rfl⟩ := hψ a
      apply ha
      exact (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top h'))
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 hker
  exact (Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hψ⟩)).symm

section Dickson

variable {F : Type} [Field F] [Finite F]

theorem lemmaD_perfect {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a)
    (H : Subgroup (PSL2MatrixGroup F)) (hH : Group.IsPerfect H) (ψ : H →* S)
    (hψ : Function.Surjective ψ) :
    Nat.card S = 60 ∨ ∃ m : ℕ, m ≠ 0 ∧ Nat.card S = p ^ m * (p ^ (2 * m) - 1) / 2 := by
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification hFcard H with
    hel | ⟨z, -, -, hcyc⟩ | ⟨z, -, hz, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t, -, -, N, C, hN, hNel, hNcard, hC, hCcard, hdisj, hsup⟩ | ⟨m, hm, -, ⟨e⟩⟩ |
    ⟨m, hm, -, ⟨e⟩⟩
  ·
    exfalso
    exact false_of_solvable_surj (isSolvable_of_comm hel.toIsMulCommutative.is_comm.comm) hS hnab ψ hψ
  ·
    exfalso
    have : IsCyclic H := hcyc
    exact false_of_solvable_surj (isSolvable_of_comm (fun a b => by
      let : CommGroup H := IsCyclic.commGroup
      exact mul_comm a b)) hS hnab ψ hψ
  ·
    exfalso
    have : NeZero z := ⟨fun hz0 => by
      rw [hz0, mul_zero] at hz
      exact Nat.card_pos.ne' hz⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact false_of_solvable_surj (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom)
      e.symm.surjective) hS hnab ψ hψ
  ·
    exfalso
    have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact false_of_solvable_surj (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom)
      e.symm.surjective) hS hnab ψ hψ
  ·
    exfalso
    have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact false_of_solvable_surj (Group.isSolvable_of_surjective (f := e.symm.toMonoidHom)
      e.symm.surjective) hS hnab ψ hψ
  ·
    left
    have h5 : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have := card_eq_of_simple_surj h5 hS (ψ.comp e.symm.toMonoidHom) (hψ.comp e.symm.surjective)
    rw [this, card_alternating_five]
  ·
    exfalso
    exact false_of_solvable_surj (isSolvable_of_normal_sup_cyclic N C
      (fun a b => hNel.toIsMulCommutative.is_comm.comm a b) hC hsup) hS hnab ψ hψ
  ·
    have hK : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    have hcardH : Nat.card (PSL2MatrixGroup (GaloisField p m)) = p ^ m * (p ^ (2 * m) - 1) / 2 :=
      MaxUp.card_psl2_galoisField hp2 hm
    have hp1 := (Fact.out : p.Prime)
    by_cases h3 : p ^ m = 3
    · exfalso
      have h9 : p ^ (2 * m) = 9 := by
        rw [mul_comm, pow_mul, h3]; norm_num
      have hlt : Nat.card H < 60 := by
        rw [Nat.card_congr e.toEquiv, hcardH, h9, h3]; norm_num
      exact false_of_solvable_surj (CFSG.GroupTheory.groups_order_below_sixty_solvable hlt)
        hS hnab ψ hψ
    · have hne2 : p ^ m ≠ 2 := fun h2 => hp2 (by
        have hd : p ∣ 2 := h2 ▸ dvd_pow_self p hm
        exact (Nat.prime_dvd_prime_iff_eq hp1 Nat.prime_two).1 hd)
      have hsimple : IsSimpleGroup (PSL2MatrixGroup (GaloisField p m)) :=
        BenderSuzuki.External.huppert_II_6_13 2 le_rfl (Or.inr (by rw [hK]; exact hne2))
          (Or.inr (by rw [hK]; exact h3))
      right
      refine ⟨m, hm, ?_⟩
      rw [← hcardH]
      rw [card_eq_of_simple_surj hsimple hS (ψ.comp e.symm.toMonoidHom)
        (hψ.comp e.symm.surjective)]
  ·
    exfalso
    have hK : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm
    have hcardP : Nat.card (PSL2MatrixGroup (GaloisField p m)) = p ^ m * (p ^ (2 * m) - 1) / 2 :=
      MaxUp.card_psl2_galoisField hp2 hm
    have hcardG : Nat.card (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) =
        p ^ m * (p ^ (2 * m) - 1) := MaxUp.card_pgl2_galoisField hm
    have hp1 := (Fact.out : p.Prime)
    obtain ⟨k, hk⟩ : Odd (p ^ (2 * m)) := (hp1.odd_of_ne_two hp2).pow
    have hev : p ^ (2 * m) - 1 = 2 * k := by omega
    set R : Subgroup (Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) :=
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := GaloisField p m)).range
    have hR : Nat.card R = p ^ m * k := by
      have h1 : Nat.card R = Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
        (Nat.card_congr (MonoidHom.ofInjective
          Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).toEquiv).symm
      rw [h1, hcardP, hev, mul_left_comm]
      exact Nat.mul_div_cancel_left _ (by norm_num)
    have hidx : R.index = 2 := by
      have h1 := Subgroup.card_mul_index R
      rw [hR, hcardG, hev] at h1
      have hpos : 0 < p ^ m * k := by
        have : 0 < p ^ m := pow_pos hp1.pos m
        have hk0 : 0 < k := by
          by_contra hk0
          have : k = 0 := by omega
          have h1p : 1 < p ^ (2 * m) := Nat.one_lt_pow (by omega) hp1.one_lt
          omega
        positivity
      nlinarith
    have hidx' : (R.comap e.toMonoidHom).index = 2 := by
      rw [Subgroup.index_comap_of_surjective R e.surjective]
      exact hidx
    exact not_perfect_of_index_two hidx' hH

theorem commutator_eq_top_of_simple {S : Type} [Group S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : commutator S = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have : ⁅a, b⁆ ∈ commutator S := Subgroup.commutator_mem_commutator trivial trivial
    rw [h, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · exact h

theorem lemmaD_aux {p f : ℕ} [Fact p.Prime]
    (hFcard : Nat.card F = p ^ f) (hp2 : p ≠ 2) {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) (hnab : ∃ a b : S, a * b ≠ b * a) (n : ℕ) :
    ∀ (Q : Type) [Group Q] [Finite Q], Nat.card Q = n →
      ∀ (j : Q →* PSL2MatrixGroup F), Function.Injective j → ∀ (ψ : Q →* S),
        Function.Surjective ψ →
        Nat.card S = 60 ∨ ∃ m : ℕ, m ≠ 0 ∧ Nat.card S = p ^ m * (p ^ (2 * m) - 1) / 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q _ _ hn j hj ψ hψ
    by_cases hQ : Group.IsPerfect Q
    · have hR : Group.IsPerfect j.range := Group.IsPerfect.ofSurjective
        (f := (MonoidHom.ofInjective hj).toMonoidHom) (MonoidHom.ofInjective hj).surjective
      exact lemmaD_perfect hFcard hp2 hS hnab j.range hR
        (ψ.comp (MonoidHom.ofInjective hj).symm.toMonoidHom)
        (hψ.comp (MonoidHom.ofInjective hj).symm.surjective)
    · have hlt : Nat.card (commutator Q) < n := by
        rw [← hn]
        refine lt_of_le_of_ne (Subgroup.card_le_card_group _) fun h => hQ ?_
        exact Group.isPerfect_def.2 (Subgroup.card_eq_iff_eq_top _ |>.1 h)
      refine ih _ hlt (commutator Q) rfl (j.comp (commutator Q).subtype)
        (hj.comp (commutator Q).subtype_injective) (ψ.comp (commutator Q).subtype) ?_
      intro s
      have h1 : (commutator Q).map ψ = ⊤ := by
        rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective ψ hψ,
          ← _root_.commutator_def]
        exact commutator_eq_top_of_simple hS hnab
      have hs : s ∈ (commutator Q).map ψ := by rw [h1]; trivial
      obtain ⟨q, hq, rfl⟩ := hs
      exact ⟨⟨q, hq⟩, rfl⟩

end Dickson
theorem simple_quotient_of_le_psl2 {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) (H : Subgroup (PSL2MatrixGroup F)) (ψ : H →* S)
    (hψ : Function.Surjective ψ) :
    Nat.card S = 60 ∨ ∃ q : ℕ, Nat.card S * 2 = q * (q ^ 2 - 1) := by
  obtain ⟨p, f, hp, hf, hFcard⟩ := exists_prime_pow_card F
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    rw [hFcard] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)
  rcases lemmaD_aux hFcard hp2 hS hnab _ H rfl H.subtype H.subtype_injective ψ hψ with h | ⟨m, hm, h⟩
  · exact Or.inl h
  · right
    refine ⟨p ^ m, ?_⟩
    obtain ⟨k, hk⟩ : Odd (p ^ (2 * m)) := (hp.odd_of_ne_two hp2).pow
    have hev : p ^ (2 * m) - 1 = 2 * k := by omega
    have hsq : (p ^ m) ^ 2 = p ^ (2 * m) := by rw [← pow_mul, mul_comm]
    rw [hsq, h, hev, mul_left_comm, Nat.mul_div_cancel_left _ (by norm_num)]
    ring

end CFSG.GH74.Generic.S3
