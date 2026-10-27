module

public import CFSG.GF2Type.Aschbacher1976Full.LeafDihedral
public import CFSG.GF2Type.Aschbacher1976Full.LeafQ8
import CFSG.GF2Type.Aschbacher1976Full.ShapeSmall
import CFSG.Adapters.StatedPSLTwoNine
import CFSG.Permutation.FiveTransitive.AbelianTwoCyclic

public section

namespace CFSG.GF2Type.Aschbacher1977

open CFSG CFSG.Blueprint CFSG.GF2Type.Aschbacher1976Full

private def d8Sigma : DihedralGroup 4 ≃* DihedralGroup 4 where
  toFun
    | .r i => .r i
    | .sr i => .sr (i + 1)
  invFun
    | .r i => .r i
    | .sr i => .sr (i - 1)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

@[simp] private theorem d8Sigma_sr (i : ZMod 4) :
    d8Sigma (DihedralGroup.sr i) = DihedralGroup.sr (i + 1) := rfl

private theorem d8_sr_mul_sr_ne :
    ∀ i : ZMod 4, DihedralGroup.sr i * DihedralGroup.sr (i + 1) ≠
      DihedralGroup.sr (i + 1) * DihedralGroup.sr i := by
  decide

theorem isCyclic_of_characteristic_dihedralGroup_four {A : Subgroup (DihedralGroup 4)}
    (hA : A.Characteristic) (hAc : IsMulCommutative A) : IsCyclic A := by
  have hsigma_mem : ∀ x ∈ A, d8Sigma x ∈ A := by
    intro x hx
    exact Subgroup.mem_comap.mp (by rw [hA.fixed d8Sigma]; exact hx)
  have hno_sr : ∀ i : ZMod 4, DihedralGroup.sr i ∉ A := by
    intro i hi
    have h1 : d8Sigma (DihedralGroup.sr i) ∈ A := hsigma_mem _ hi
    have hc := mul_comm' (⟨DihedralGroup.sr i, hi⟩ : A)
      (⟨d8Sigma (DihedralGroup.sr i), h1⟩ : A)
    have h2 : DihedralGroup.sr i * DihedralGroup.sr (i + 1) =
        DihedralGroup.sr (i + 1) * DihedralGroup.sr i := by
      simpa [d8Sigma_sr] using congrArg Subtype.val hc
    exact d8_sr_mul_sr_ne i h2
  refine Subgroup.isCyclic_of_le (H' := Subgroup.zpowers (DihedralGroup.r 1)) ?_
  intro x hx
  rcases x with i | i
  · rw [Subgroup.mem_zpowers_iff]
    refine ⟨(i.val : ℤ), ?_⟩
    rw [DihedralGroup.r_one_zpow, Int.cast_natCast, ZMod.natCast_zmod_val]
  · exact absurd hx (hno_sr i)

theorem isCyclic_of_isMulCommutative_quaternionGroup_two {A : Subgroup (QuaternionGroup 2)}
    (hAc : IsMulCommutative A) : IsCyclic A := by
  classical
  have hcardQ : Nat.card (QuaternionGroup 2) = 2 ^ 3 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num
  have hQ8 : IsPGroup 2 (QuaternionGroup 2) := IsPGroup.of_card hcardQ
  have hker : Nat.card {x : QuaternionGroup 2 // x ^ 2 = 1} ≤ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    decide
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  refine FiveTransitive.AbelianTwoCyclic.isCyclic_of_square_kernel_card_le_two
    (hQ8.to_subgroup A) ?_
  have hinj : Function.Injective (fun a : {a : A // a ^ 2 = 1} =>
      (⟨(a.1 : QuaternionGroup 2), by
        have h := congrArg (fun t : A => (t : QuaternionGroup 2)) a.2
        simpa using h⟩ : {x : QuaternionGroup 2 // x ^ 2 = 1})) := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val hab
  exact (Nat.card_le_card_of_injective _ hinj).trans hker

theorem forall_characteristic_isMulCommutative_isCyclic_of_mulEquiv {P Q : Type*} [Group P]
    [Group Q] (e : P ≃* Q)
    (h : ∀ B : Subgroup Q, B.Characteristic → IsMulCommutative B → IsCyclic B) :
    ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A := by
  intro A hA hAc
  have hBchar : (A.map (e : P →* Q)).Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro ψ
    have hφ : A.map ((e.trans (ψ.trans e.symm) : P ≃* P) : P →* P) = A :=
      (Subgroup.characteristic_iff_map_eq.mp hA) _
    calc (A.map (e : P →* Q)).map (ψ : Q →* Q)
        = A.map ((ψ : Q →* Q).comp (e : P →* Q)) := by rw [Subgroup.map_map]
      _ = A.map ((e : P →* Q).comp ((e.trans (ψ.trans e.symm) : P ≃* P))) := by
            congr 1
            ext x
            simp [MulEquiv.trans_apply]
      _ = (A.map ((e.trans (ψ.trans e.symm) : P ≃* P))).map (e : P →* Q) := by
            rw [Subgroup.map_map]
      _ = A.map (e : P →* Q) := by rw [hφ]
  have hBc : IsMulCommutative (A.map (e : P →* Q)) := inferInstance
  exact (MulEquiv.isCyclic (e.subgroupMap A)).mpr (h _ hBchar hBc)

theorem isCyclic_of_characteristic_of_extraspecial_card_eight {P : Type*} [Group P]
    (hP : IsExtraspecialPGroup 2 P) (hcard : Nat.card P = 8) :
    ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A := by
  haveI : Finite P := Nat.finite_of_card_ne_zero (by omega)
  rcases ComponentClassification.WalterSchur.dihedral_or_quaternion_of_card_eq_eight hcard
      (Shape.nonabelian_of_extraspecial hP) with hD | hQ
  · obtain ⟨e⟩ := hD
    exact forall_characteristic_isMulCommutative_isCyclic_of_mulEquiv e
      (fun B hB hBc => isCyclic_of_characteristic_dihedralGroup_four hB hBc)
  · obtain ⟨e⟩ := hQ
    exact forall_characteristic_isMulCommutative_isCyclic_of_mulEquiv e
      (fun B _ hBc => isCyclic_of_isMulCommutative_quaternionGroup_two hBc)

theorem glaSymplecticType_of_extraspecial_card_eight {G : Type} [Group G] {T : Subgroup G}
    (hT : IsExtraspecialPGroup 2 T) (hcard : Nat.card T = 8) :
    CFSG.Open.GLASymplecticType T :=
  ⟨hT.1, isCyclic_of_characteristic_of_extraspecial_card_eight hT hcard⟩

theorem asc76Setting_of_extraspecial_card_eight {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {z : G} (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2 ↥(Fz z)) (hcard : Nat.card ↥(Fz z) = 8) :
    Asc76Setting G z :=
  ⟨inferInstance, hnonab, hz, glaSymplecticType_of_extraspecial_card_eight hext hcard⟩

theorem Hz_eq_Fz_of_dihedral_eight {G : Type} [Group G] [Finite G] {z : G}
    (hF2 : IsPGroup 2 ↥(Fz z)) (e : ↥(Fz z) ≃* DihedralGroup 4) : Hz z = Fz z :=
  Shape.Hz_eq_Fz_of_mulAut hF2
    ((GorensteinWalter.dihedral_mulAut_is_twoGroup (m := 2) le_rfl).of_equiv
      (MulAut.congr e).symm)

theorem lieModel_psl_two_seven_or_alternating_six_of_centralizer {G : Type} [Group G] {z : G}
    (hz : orderOf z = 2) (hcard : Nat.card (Subgroup.centralizer ({z} : Set G)) = 8) {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hLie : LieModel G .PSL 2 p f) :
    LieModel G .PSL 2 7 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) := by
  have hSC : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 2 p f :=
    hLie.statedClassicalModel (by decide)
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨φ⟩⟩ := hSC
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  let e2 : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    φ.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have ht : orderOf (e2 z) = 2 := (orderOf_injective e2.toMonoidHom e2.injective z).trans hz
  have hcT : Nat.card (Subgroup.centralizer
      ({e2 z} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))) = 8 := by
    rw [LeafDihedral.card_centralizer_transport e2 z, hcard]
  obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution K hKcard hodd (by omega) ht
  have hq : p ^ f = 7 ∨ p ^ f = 9 := by
    have hpodd : p ^ f % 2 = 1 := Nat.odd_iff.mp hodd.pow
    rcases (by omega : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3) with h4 | h4
    · obtain ⟨hc, -⟩ := h1 h4
      rw [hc] at hcT
      omega
    · obtain ⟨hc, -⟩ := h3 h4
      rw [hc] at hcT
      omega
  rcases hq with hq | hq
  · left
    obtain ⟨rfl, rfl⟩ := (Nat.Prime.pow_eq_iff Nat.prime_seven).mp hq
    exact hLie
  · right
    have hp3 : p = 3 := by
      have hpdvd : p ∣ 3 ^ 2 := by
        have h1 : p ∣ p ^ f := by simpa using pow_dvd_pow p hf
        rw [hq] at h1
        norm_num at h1 ⊢
        exact h1
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        (Nat.Prime.dvd_of_dvd_pow hp hpdvd)
    subst hp3
    have hf2 : f = 2 := by
      have hpow : 3 ^ f = 3 ^ 2 := by simpa using hq
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
    subst hf2
    exact LieModel.nonempty_mulEquiv_alternating_six hLie

section Certs

theorem lieModel_or_alternating_six_of_dihedral_eight {G : Type} [Group G] [Finite G] {z : G}
    (hS : Asc76Setting G z) (hH : Hz z = Fz z) (hcard : Nat.card ↥(Fz z) = 8)
    (e : ↥(Fz z) ≃* DihedralGroup 4) :
    LieModel G .PSL 2 7 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨p, f, -, hp, hp2, hf, -, -, hLie⟩ :=
    leafDihedral_holds G z hS 3 le_rfl hH ⟨e⟩
  have hcard' : Nat.card (Subgroup.centralizer ({z} : Set G)) = 8 := by
    change Nat.card (Hz z) = 8
    rw [hH]
    exact hcard
  exact lieModel_psl_two_seven_or_alternating_six_of_centralizer hS.2.2.1 hcard' hp hp2 hf hLie

end Certs

theorem lieModel_or_sporadic_of_width_one
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2
      (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))))
    (hcard : Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) =
      2 ^ (1 + 2 * 1)) :
    LieModel G .PSL 2 7 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
      NativeSporadic.IsSporadic G .M11 ∨ LieModel G .PSL 3 3 1 := by
  have h8 : Nat.card ↥(Fz z) = 8 := by
    change Nat.card (inSubgroup generalizedFitting (Subgroup.centralizer ({z} : Set G))) = 8
    rw [hcard]
    norm_num
  have hS : Asc76Setting G z := asc76Setting_of_extraspecial_card_eight hnonab hz hext h8
  rcases ComponentClassification.WalterSchur.dihedral_or_quaternion_of_card_eq_eight h8
    (Shape.nonabelian_of_extraspecial hext) with hD | hQ
  · obtain ⟨e⟩ := hD
    have hH : Hz z = Fz z := Hz_eq_Fz_of_dihedral_eight hext.1 e
    rcases lieModel_or_alternating_six_of_dihedral_eight hS hH h8 e with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · obtain ⟨e⟩ := hQ
    exact Or.inr (Or.inr (leafQ8_holds G z hS ⟨e⟩))

end CFSG.GF2Type.Aschbacher1977
