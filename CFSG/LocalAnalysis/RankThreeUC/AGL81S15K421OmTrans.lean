module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421SpData

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421OmTransProof

open CFSG.Open K421MonoProof K421OrbProof K421AbsProof K421SylProof K421LinProof K421SpProof
  K421SpCWProof K421SpSylProof K421SpDataProof

section Sylow

variable {X S : Type} [Group X] [Group S] [Finite X] [Finite S] {ι : X →* S}

theorem factorization_eq_of_index (hι : Function.Injective ι) (hidx : ¬ 3 ∣ ι.range.index) :
    (Nat.card S).factorization 3 = (Nat.card X).factorization 3 := by
  have h1 : ι.range.index * Nat.card ι.range = Nat.card S := Subgroup.index_mul_card _
  have h2 : Nat.card ι.range = Nat.card X := Nat.card_congr (MonoidHom.ofInjective hι).toEquiv.symm
  have hne : ι.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hX : Nat.card X ≠ 0 := Nat.card_pos.ne'
  rw [← h1, h2, Nat.factorization_mul hne hX, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hidx, zero_add]

@[expose] noncomputable def sylowMap (hι : Function.Injective ι) (hidx : ¬ 3 ∣ ι.range.index)
    (P : Sylow 3 X) : Sylow 3 S :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  Sylow.ofCard ((P : Subgroup X).map ι) (by
    rw [Subgroup.card_map_of_injective hι, Sylow.card_eq_multiplicity,
      factorization_eq_of_index hι hidx])

theorem coe_sylowMap (hι : Function.Injective ι) (hidx : ¬ 3 ∣ ι.range.index) (P : Sylow 3 X) :
    ((sylowMap hι hidx P : Sylow 3 S) : Subgroup S) = (P : Subgroup X).map ι := rfl

theorem exists_conj_le_map (hι : Function.Injective ι) (hidx : ¬ 3 ∣ ι.range.index)
    (Q₀ : Sylow 3 X) {E : Subgroup S} (hE : IsPGroup 3 E) :
    ∃ g : S, E.map (MulAut.conj g).toMonoidHom ≤ (Q₀ : Subgroup X).map ι := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hEP⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S P (sylowMap hι hidx Q₀)
  refine ⟨g, ?_⟩
  have h1 : (P : Subgroup S).map (MulAut.conj g).toMonoidHom = (Q₀ : Subgroup X).map ι := by
    rw [← sylow_smul_coe, hg]
    rfl
  rw [← h1]
  exact Subgroup.map_mono hEP

theorem hconj_of_embedding (hι : Function.Injective ι) (hidx : ¬ 3 ∣ ι.range.index) {D : Mono81 X}
    (hconjX : ∀ E : Subgroup X, IsElemAbelian 3 E →
      ∃ g : X, E.map (MulAut.conj g).toMonoidHom ≤ D.A0)
    {E : Subgroup S} (hE : IsElemAbelian 3 E) :
    ∃ g : S, E.map (MulAut.conj g).toMonoidHom ≤ (D.map ι hι).A0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q₀⟩ : Nonempty (Sylow 3 X) := inferInstance
  have hp : IsPGroup 3 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using hE.2 x x.2⟩
  obtain ⟨g, hg⟩ := exists_conj_le_map hι hidx Q₀ hp
  have hE' : IsElemAbelian 3 (E.map (MulAut.conj g).toMonoidHom) :=
    K21bTransProof.isElemAbelian_map_inj (MulAut.conj g).injective hE
  have hle : E.map (MulAut.conj g).toMonoidHom ≤ ι.range :=
    hg.trans (Subgroup.map_le_range ι _)
  have hmap : ((E.map (MulAut.conj g).toMonoidHom).comap ι).map ι =
      E.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hle
  have hE'' : IsElemAbelian 3 ((E.map (MulAut.conj g).toMonoidHom).comap ι) :=
    isElemAbelian_of_map_inj hι (by rw [hmap]; exact hE')
  obtain ⟨h, hh⟩ := hconjX _ hE''
  refine ⟨ι h * g, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have hz' : (MulAut.conj g) z ∈ ((E.map (MulAut.conj g).toMonoidHom).comap ι).map ι := by
    rw [hmap]
    exact Subgroup.mem_map_of_mem _ hz
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.1 hz'
  obtain ⟨x, hx⟩ := D.mem_A0_iff.1 (hh (Subgroup.mem_map_of_mem _ hy))
  refine (D.map ι hι).mem_A0_iff.2 ⟨x, ?_⟩
  show (MulAut.conj (ι h * g)) z = (D.map ι hι).av x
  have h1 : (MulAut.conj (ι h * g)) z = (MulAut.conj (ι h)) ((MulAut.conj g) z) := by
    simp [MulAut.conj_apply, mul_assoc]
  rw [h1, ← hyz, Mono81.map_av]
  have h2 : (MulAut.conj (ι h)) (ι y) = ι ((MulAut.conj h) y) := by
    simp [MulAut.conj_apply]
  rw [h2]
  exact congrArg ι hx

theorem isCyclic_center_sylow_of_embedding (hι : Function.Injective ι)
    (hidx : ¬ 3 ∣ ι.range.index)
    (hcen : ∀ P : Sylow 3 X, IsCyclic ↥(Subgroup.center ↥(P : Subgroup X)))
    (P' : Sylow 3 S) : IsCyclic ↥(Subgroup.center ↥(P' : Subgroup S)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q₀⟩ : Nonempty (Sylow 3 X) := inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S (sylowMap hι hidx Q₀) P'
  have h1 : (P' : Subgroup S) = (Q₀ : Subgroup X).map ((MulAut.conj g).toMonoidHom.comp ι) := by
    rw [← hg, sylow_smul_coe, ← Subgroup.map_map]
    rfl
  have hψ : Function.Injective ((MulAut.conj g).toMonoidHom.comp ι) :=
    (MulAut.conj g).injective.comp hι
  exact K421SpWrProof.isCyclic_center_of_mulEquiv
    (((Subgroup.equivMapOfInjective _ _ hψ).trans (MulEquiv.subgroupCongr h1.symm)).symm)
    (hcen Q₀)

theorem three_le_pRank_sylow_of_embedding (hι : Function.Injective ι)
    (hidx : ¬ 3 ∣ ι.range.index)
    (hrk : ∀ P : Sylow 3 X, 3 ≤ CFSG.Open.pRank 3 (P : Subgroup X))
    (P' : Sylow 3 S) : 3 ≤ CFSG.Open.pRank 3 (P' : Subgroup S) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q₀⟩ : Nonempty (Sylow 3 X) := inferInstance
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S (sylowMap hι hidx Q₀) P'
  have h1 : (P' : Subgroup S) = (Q₀ : Subgroup X).map ((MulAut.conj g).toMonoidHom.comp ι) := by
    rw [← hg, sylow_smul_coe, ← Subgroup.map_map]
    rfl
  have hψ : Function.Injective ((MulAut.conj g).toMonoidHom.comp ι) :=
    (MulAut.conj g).injective.comp hι
  rw [h1]
  exact (hrk Q₀).trans (CFSG.SectionRank.pRank_le_map (by norm_num) _ hψ _)

theorem sylowAt_of_embedding (hι : Function.Injective ι) (hidx : ¬ 3 ∣ ι.range.index) {x : X}
    (h : SylowAt x) : SylowAt (ι x) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨sylowMap hι hidx P, ?_⟩
  rw [coe_sylowMap]
  rintro _ ⟨w, hw, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.1 (hP hw) x (Set.mem_singleton x)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  rw [← map_mul, ← map_mul, h1]

end Sylow

section Witness

variable {X S : Type} [Group X] [Group S] (ι : X →* S) {p : ℕ} {x : X}

theorem range_comp_le_centralizer {A : Type} [Group A] (ψ : A →* X)
    (hle : ψ.range ≤ Subgroup.centralizer ({x} : Set X)) :
    (ι.comp ψ).range ≤ Subgroup.centralizer ({ι x} : Set S) := by
  rintro _ ⟨a, rfl⟩
  have h1 := Subgroup.mem_centralizer_iff.1 (hle ⟨a, rfl⟩) x (Set.mem_singleton x)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  show ι x * ι (ψ a) = ι (ψ a) * ι x
  rw [← map_mul, ← map_mul, h1]

theorem rankTwoAt_map (hι : Function.Injective ι) (h : RankTwoAt p x) : RankTwoAt p (ι x) := by
  obtain ⟨A, B, _, _, _, _, φ, hφ, hle, hA, hB⟩ := h
  exact ⟨A, B, inferInstance, inferInstance, inferInstance, inferInstance, ι.comp φ, hι.comp hφ,
    range_comp_le_centralizer ι φ hle, hA, hB⟩

theorem simpleAt_map (hι : Function.Injective ι) (h : SimpleAt p x) : SimpleAt p (ι x) := by
  obtain ⟨A, _, _, _, ψ, hψ, hle, hA, hne⟩ := h
  exact ⟨A, inferInstance, inferInstance, inferInstance, ι.comp ψ, hι.comp hψ,
    range_comp_le_centralizer ι ψ hle, hA, hne⟩

theorem rankOneAt_map (hι : Function.Injective ι) (h : RankOneAt p x) : RankOneAt p (ι x) := by
  obtain ⟨A, _, _, ψ, hψ, hle, hA⟩ := h
  exact ⟨A, inferInstance, inferInstance, ι.comp ψ, hι.comp hψ,
    range_comp_le_centralizer ι ψ hle, hA⟩

end Witness

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2] {p : ℕ}

theorem data421_of_embedding (hp : p.Prime) (hp5 : 5 ≤ p) (hpF : p ∣ Nat.card F + 1)
    {S : Type} [Group S] [Finite S] (ι : ↥(SpI F) →* S) (hι : Function.Injective ι)
    (hidx : ¬ 3 ∣ ι.range.index) : Data421 S p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h4 : 4 ≤ Nat.card F := by
    have := Nat.le_of_dvd (by omega) hpF
    omega
  have hSP : SignedPerms ((monoSp F).map ι hι) := (signedPerms_monoSp F).map ι hι
  have hconj : ∀ E : Subgroup S, IsElemAbelian 3 E →
      ∃ g : S, E.map (MulAut.conj g).toMonoidHom ≤ ((monoSp F).map ι hι).A0 :=
    fun E hE => hconj_of_embedding hι hidx (fun E' hE' => hconj_sp F hE') hE
  have hcaseA : ∀ {x : S} {t : Fin 3}, IsType ((monoSp F).map ι hι) x t →
      (t ≠ 2 ∨ ¬ 3 ∣ Nat.card F - 1) →
      2 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({x} : Set S)) ∧
        ¬ CFSG.HallHigman.IsPSolvable p ↥(Subgroup.centralizer ({x} : Set S)) := by
    intro x t hty ht
    obtain ⟨n, hn⟩ := hty
    obtain ⟨hR, hSi⟩ := caseAWit hp hpF h4 t ht
    have hR' : RankTwoAt p x := RankTwoAt.conj hn (rankTwoAt_map ι hι hR)
    have hS' : SimpleAt p x := SimpleAt.conj hn (simpleAt_map ι hι hSi)
    exact ⟨two_le_pRank_of_rankTwoAt hR', hS'.not_isPSolvable⟩
  refine ⟨?_, ?_⟩
  · intro D hD
    obtain ⟨x, hx, rfl⟩ := exists_zpowers_of_card_three hD
    obtain ⟨t, hty⟩ := exists_type_sp hSP hconj hx
    rw [centralizer_zpowers_eq]
    by_cases hc : t ≠ 2 ∨ ¬ 3 ∣ Nat.card F - 1
    · left
      obtain ⟨h1, h2⟩ := hcaseA hty hc
      exact ⟨by omega, h2⟩
    · right
      have ht2 : t = 2 := by
        by_contra h
        exact hc (Or.inl h)
      have h3 : 3 ∣ Nat.card F - 1 := by
        by_contra h
        exact hc (Or.inr h)
      have hN : Nat.card F % 3 = 1 := by omega
      subst ht2
      obtain ⟨n, hn⟩ := hty
      refine ⟨?_, ?_⟩
      · have h1 : SylowAt (ι ((monoSp F).av (rep 2))) :=
          sylowAt_of_embedding hι hidx sylowAt_rep2
        exact sylowShape_of_sylow_le_centralizer
          (isCyclic_center_sylow_of_embedding hι hidx (isCyclic_center_sylow hN (spIEquiv F)))
          (three_le_pRank_sylow_of_embedding hι hidx (three_le_pRank_sylow hN (spIEquiv F)))
          (SylowAt.conj hn h1)
      · have hpS := K421SpSLProof.sl2_dvd_card_of_dvd_succ hpF
        have h1 : RankOneAt p x :=
          RankOneAt.conj hn (rankOneAt_map ι hι (K421SpProof.rankOneAt_rep2 hpS))
        have h2 := h1.one_le_pRank
        omega
  · intro E hE h9
    obtain ⟨c, hcE, hc1, t, ht2, hty⟩ := exists_type_ne_two_of_card_nine hSP hconj hE h9
    have hc3 : c ^ 3 = 1 := hE.2 c hcE
    have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    refine ⟨Subgroup.zpowers c, (Subgroup.zpowers_le).2 hcE, by rw [Nat.card_zpowers, hcord], ?_⟩
    rw [centralizer_zpowers_eq]
    obtain ⟨h1, h2⟩ := hcaseA hty (Or.inl ht2)
    exact ⟨by omega, h2⟩

theorem not_dvd_index_of_card {X S : Type} [Group X] [Group S] [Finite X] [Finite S] {ι : X →* S}
    (hι : Function.Injective ι) {k : ℕ} (hk : Nat.card S = k * Nat.card X) (hk3 : ¬ 3 ∣ k) :
    ¬ 3 ∣ ι.range.index := by
  have h1 : ι.range.index * Nat.card ι.range = Nat.card S := Subgroup.index_mul_card _
  have h2 : Nat.card ι.range = Nat.card X := Nat.card_congr (MonoidHom.ofInjective hι).toEquiv.symm
  have hX : 0 < Nat.card X := Nat.card_pos
  have h3 : ι.range.index = k := by
    rw [h2, hk] at h1
    exact Nat.eq_of_mul_eq_mul_right hX h1
  rwa [h3]

end Main

end K421OmTransProof

end CFSG.LocalAnalysis.RankThreeUC.S15
