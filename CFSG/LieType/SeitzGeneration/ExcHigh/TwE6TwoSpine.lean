module

public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LieType.SeitzGeneration.ExcHigh.Generic

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open scoped MatrixGroups
open CFSG.Open

section TwoCovers

theorem range_le_closure_centralizers_of_cover {G H : Type*} [Group G] [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (ψ : H →* G) (hker : ¬ p ∣ Nat.card ψ.ker)
    (hH : ∀ F : Subgroup H, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {h : H | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤)
    (E : Subgroup G) (hE : E ≤ ψ.range) (hEp : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) :
    ψ.range ≤ Subgroup.closure {k | ∃ x ∈ E, x ≠ 1 ∧ Commute k x} :=
  (closure_in_range_of_cover ψ hker hH E hE hEp hEc).trans
    (Subgroup.closure_mono fun _ hg => hg.2)

theorem closure_centralizers_eq_top_of_two_covers {G H₁ H₂ : Type*} [Group G] [Group H₁]
    [Group H₂] [Finite H₁] [Finite H₂] {p : ℕ} [Fact p.Prime] (ψ₁ : H₁ →* G) (ψ₂ : H₂ →* G)
    (hk₁ : ¬ p ∣ Nat.card ψ₁.ker) (hk₂ : ¬ p ∣ Nat.card ψ₂.ker)
    (h₁ : ∀ F : Subgroup H₁, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {h : H₁ | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤)
    (h₂ : ∀ F : Subgroup H₂, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {h : H₂ | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤)
    (hclose : ∀ M : Subgroup G, ψ₁.range ≤ M → ψ₂.range ≤ M → M = ⊤)
    (P : Subgroup G) (hP₁ : P ≤ ψ₁.range) (hP₂ : P ≤ ψ₂.range) (E₀ : Subgroup G)
    (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2)
    (hSyl : ∃ g : G, E₀.map (MulAut.conj g).toMonoidHom ≤ P) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤ := by
  obtain ⟨g, hg⟩ := hSyl
  set E₁ := E₀.map (MulAut.conj g).toMonoidHom with hE₁
  have hE₁p : ∀ x ∈ E₁, x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE₀p x hx, map_one]
  have hE₁c : Nat.card E₁ = p ^ 2 := by
    rw [hE₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hE₀c]
  have htop : Subgroup.closure {k | ∃ x ∈ E₁, x ≠ 1 ∧ Commute k x} = ⊤ :=
    hclose _ (range_le_closure_centralizers_of_cover ψ₁ hk₁ h₁ E₁ (hg.trans hP₁) hE₁p hE₁c)
      (range_le_closure_centralizers_of_cover ψ₂ hk₂ h₂ E₁ (hg.trans hP₂) hE₁p hE₁c)
  exact closure_centralizers_eq_top_of_map_conj_eq_top g E₀ htop

end TwoCovers

section AbelianProd

variable {A B : Type*} [CommGroup A] [Group B] {p : ℕ} [Fact p.Prime]

theorem closure_centralizers_prod_of_abelian_plane
    (hB : ∀ F : Subgroup B, IsElemAbelian p F → Nat.card F = p ^ 2 →
      Subgroup.closure {b : B | ∃ x ∈ F, x ≠ 1 ∧ Commute b x} = ⊤)
    (F : Subgroup (A × B)) (hF : IsElemAbelian p F) (hc : Nat.card F = p ^ 2) :
    Subgroup.closure {h : A × B | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} = ⊤ := by
  classical
  set S : Set (A × B) := {h | ∃ x ∈ F, x ≠ 1 ∧ Commute h x} with hS
  have hcentral : ∀ (a : A) (h : A × B), Commute h (a, (1 : B)) := fun a h =>
    Prod.ext (by simp [mul_comm]) (by simp)
  by_cases hx : ∃ x ∈ F, x ≠ 1 ∧ x.2 = 1
  · obtain ⟨x, hxF, hx1, hx2⟩ := hx
    have hxe : x = (x.1, 1) := Prod.ext rfl hx2
    rw [eq_top_iff]
    rintro h -
    exact Subgroup.subset_closure ⟨x, hxF, hx1, by rw [hxe]; exact hcentral _ _⟩
  · push Not at hx
    have hdis : Disjoint F (MonoidHom.snd A B).ker := by
      rw [Subgroup.disjoint_def]
      intro x hx' hx1
      by_contra hne
      exact hx x hx' hne (MonoidHom.mem_ker.1 hx1)
    have hFB : IsElemAbelian p (F.map (MonoidHom.snd A B)) := hF.map _
    have hcardFB : Nat.card (F.map (MonoidHom.snd A B)) = p ^ 2 := by
      rw [card_map_eq_of_disjoint_ker _ hdis, hc]
    have htop := hB _ hFB hcardFB
    have hB1 : ∀ b : B, ((1 : A), b) ∈ Subgroup.closure S := by
      intro b
      have hb : b ∈ Subgroup.closure {b : B | ∃ f ∈ F.map (MonoidHom.snd A B), f ≠ 1 ∧
          Commute b f} := by
        rw [htop]
        exact Subgroup.mem_top _
      have hmap := Subgroup.mem_map_of_mem (MonoidHom.inr A B) hb
      rw [MonoidHom.map_closure] at hmap
      refine Subgroup.closure_mono ?_ hmap
      rintro _ ⟨b', ⟨_, ⟨x, hxF, rfl⟩, hf1, hcb⟩, rfl⟩
      refine ⟨x, hxF, fun h => hf1 (by simp [h]), ?_⟩
      exact Prod.ext (by simp) (by simpa using hcb.eq)
    have hne : ∃ x ∈ F, x ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have h1 : Nat.card F = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩, ⟨1⟩⟩
      have hp2 := (Fact.out : p.Prime).two_le
      rw [hc] at h1
      nlinarith
    obtain ⟨x, hxF, hx1⟩ := hne
    have hA1 : ∀ a : A, (a, (1 : B)) ∈ Subgroup.closure S := fun a =>
      Subgroup.subset_closure ⟨x, hxF, hx1, (hcentral a x).symm⟩
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have := (Subgroup.closure S).mul_mem (hA1 a) (hB1 b)
    simpa using this

end AbelianProd

section SylowFrameTorus

variable {K : Type} [Field K] [Finite K]

theorem exists_conj_le_map_sylow {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    {p : ℕ} [hpF : Fact p.Prime] (ψ : H →* G) (Q : Sylow p H)
    (hdisj : Disjoint (Q : Subgroup H) ψ.ker)
    (hord : (Nat.card G).factorization p ≤ (Nat.card H).factorization p) (E : Subgroup G)
    (hE : ∀ x ∈ E, x ^ p = 1) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup H).map ψ := by
  have h1 : Nat.card ((Q : Subgroup H).map ψ) = Nat.card Q := card_map_eq_of_disjoint_ker ψ hdisj
  have h2 : (Nat.card ((Q : Subgroup H).map ψ)).factorization p = (Nat.card H).factorization p := by
    rw [h1, Sylow.card_eq_multiplicity Q, Nat.Prime.factorization_pow hpF.out,
      Finsupp.single_eq_same]
  have h3 : (Nat.card ((Q : Subgroup H).map ψ)).factorization p ≤ (Nat.card G).factorization p :=
    (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
      (Subgroup.card_subgroup_dvd_card _) p
  obtain ⟨g, -, hg⟩ := CFSG.RankThree.PartOne.K133H.exists_conj_le_of_sylow (p := p) (Y := ⊤)
    (H := (Q : Subgroup H).map ψ) (A := E) le_top le_top hE
    (by rw [Subgroup.card_top]; omega)
  exact ⟨g, hg⟩

theorem exists_conj_le_frame_torus {G : Type*} [Group G] [Finite G] {k : ℕ}
    (ρ : Fin k → SL(2, K) →* G) (hρi : ∀ i, Function.Injective (ρ i))
    (hρc : Pairwise fun i j => ∀ x y : SL(2, K), Commute (ρ i x) (ρ j y))
    (A : Subgroup G) (hAc : ∀ a ∈ A, ∀ (i : Fin k) (y : SL(2, K)), Commute a (ρ i y))
    {p : ℕ} [hpF : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (hord : (Nat.card G).factorization p ≤
      k * (Nat.card K + 1).factorization p + (Nat.card A).factorization p)
    (E : Subgroup G) (hE : ∀ x ∈ E, x ^ p = 1) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ (⨆ i, (ρ i).range) ⊔ A := by
  classical
  set μ := MonoidHom.noncommPiCoprod ρ hρc with hμ
  have hcomm : ∀ (y : Fin k → SL(2, K)) (a : A), Commute (μ y) (A.subtype a) := by
    intro y a
    rw [hμ, MonoidHom.noncommPiCoprod_apply]
    exact (Finset.noncommProd_commute _ _ _ (A.subtype a) fun j _ => hAc a a.2 j (y j)).symm
  set ψ : (Fin k → SL(2, K)) × A →* G := MonoidHom.noncommCoprod μ A.subtype hcomm with hψ
  have hψapply : ∀ (y : Fin k → SL(2, K)) (a : A), ψ (y, a) = μ y * (a : G) := fun y a => rfl
  obtain ⟨Q⟩ : Nonempty (Sylow p ((Fin k → SL(2, K)) × A)) := inferInstance
  have hdisj : Disjoint (Q : Subgroup ((Fin k → SL(2, K)) × A)) ψ.ker := by
    rw [Subgroup.disjoint_def]
    rintro ⟨y, a⟩ hxQ hxk
    have hx1 : μ y * (a : G) = 1 := hxk
    have hcent : ∀ i, ∀ z : SL(2, K), y i * z = z * y i := by
      intro i z
      set y' : Fin k → SL(2, K) := Function.update y i 1 with hy'
      have hsplit : y = Pi.mulSingle i (y i) * y' := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [hy']
        · simp [hy', hj]
      have hcomm' : Commute (μ y') (ρ i z) := by
        rw [hμ, MonoidHom.noncommPiCoprod_apply]
        refine (Finset.noncommProd_commute _ _ _ (ρ i z) fun j _ => ?_).symm
        by_cases hj : j = i
        · subst hj
          simp [hy']
        · exact (hρc (Ne.symm hj) _ _)
      have h1 : ρ i (y i) * μ y' * (a : G) = 1 := by
        have h := hx1
        rw [hsplit, map_mul, hμ, MonoidHom.noncommPiCoprod_mulSingle] at h
        exact h
      have h2 : ρ i (y i) = ((μ y') * (a : G))⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h1)
      have h3 : Commute (ρ i (y i)) (ρ i z) := by
        rw [h2]
        exact (hcomm'.mul_left (hAc (a : G) a.2 i z)).inv_left
      apply (hρi i)
      rw [map_mul, map_mul]
      exact h3.eq
    have hsq : y ^ 2 = 1 := by
      funext i
      have hc : y i ∈ Subgroup.center SL(2, K) :=
        Subgroup.mem_center_iff.2 fun z => (hcent i z).symm
      obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
      simp only [Fintype.card_fin] at hr
      have hmul : y i * y i = 1 := by
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_mul, ← hrx, ← map_mul, ← pow_two, hr, map_one,
          Matrix.SpecialLinearGroup.coe_one]
      rw [Pi.pow_apply, Pi.one_apply, pow_two]
      exact hmul
    obtain ⟨m, hm⟩ := Q.isPGroup' ⟨(y, a), hxQ⟩
    have hm' : (y, a) ^ (p ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hym : y ^ (p ^ m) = 1 := by
      have := congrArg Prod.fst hm'
      simpa using this
    have hcop : Nat.Coprime 2 (p ^ m) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hpF.out).2 (by omega))
    have hd : orderOf y ∣ Nat.gcd 2 (p ^ m) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hsq) (orderOf_dvd_of_pow_eq_one hym)
    rw [hcop] at hd
    have hy1 : y = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
    have ha1 : (a : G) = 1 := by
      rw [hy1, map_one, one_mul] at hx1
      exact hx1
    exact Prod.ext hy1 (Subtype.ext ha1)
  have hcardH : (Nat.card ((Fin k → SL(2, K)) × A)).factorization p =
      k * (Nat.card K + 1).factorization p + (Nat.card A).factorization p := by
    have hpi : Nat.card (Fin k → SL(2, K)) = Nat.card SL(2, K) ^ k := by
      rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hSL0 : Nat.card SL(2, K) ≠ 0 := Nat.card_pos.ne'
    have hA0 : Nat.card A ≠ 0 := Nat.card_pos.ne'
    rw [Nat.card_prod, hpi, Nat.factorization_mul (pow_ne_zero _ hSL0) hA0, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      factorization_card_SL2_of_dvd_add_one hpF.out hp5 hpq]
  obtain ⟨g, hg⟩ := exists_conj_le_map_sylow ψ Q hdisj (by rw [hcardH]; exact hord) E hE
  refine ⟨g, hg.trans ?_⟩
  rintro _ ⟨⟨y, a⟩, -, rfl⟩
  rw [hψapply]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right a.2)
  exact map_noncommPiCoprod_le ρ hρc ⊤ ⟨y, Subgroup.mem_top _, rfl⟩

end SylowFrameTorus

end CFSG.LieType.SeitzGeneration.ExcHigh
