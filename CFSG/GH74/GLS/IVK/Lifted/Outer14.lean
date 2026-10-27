module

public import CFSG.GH74.GLS.IVK.Lifted.CentSylow
public import CFSG.GH74.GLS.IVK.Lifted.PGLQuot
public import CFSG.GH74.GLS.IVK.Lifted.OuterStruct
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.QuatMod

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup Matrix CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter CFSG.ABGLocalTools
  CFSG.ABGDGroups CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm6 CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped commutatorElement

section Transfer

theorem isDihedralTwoGroup_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (h : IsDihedralTwoGroup A n) : IsDihedralTwoGroup B n := by
  obtain ⟨hn, k, hk, hk2, ⟨d⟩⟩ := h
  exact ⟨hn, k, hk, hk2, ⟨e.symm.trans d⟩⟩

theorem isSemidihedralTwoGroup_congr {A B : Type} [Group A] [Group B] (e : A ≃* B) {n : ℕ}
    (h : IsSemidihedralTwoGroup A n) : IsSemidihedralTwoGroup B n := by
  obtain ⟨hn, ⟨d⟩⟩ := h
  exact ⟨hn, ⟨e.symm.trans d⟩⟩

end Transfer

section Bridge

variable {F : Type} [Field F] [Finite F]

theorem thetaEquiv_eq (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F) (x : PGammaL2 F) :
    thetaEquiv hodd h3 x = semilinearEquivAut F x :=
  (DFunLike.congr_fun (semilinearAction_eq_native F (isOddPrimePower_card_of_odd hodd) h3) x).symm

theorem fieldProj_psl2AutHom (hodd : Odd (Nat.card F)) (h3 : 3 < Nat.card F)
    (α : MulAut (SpecialLinearGroup (Fin 2) F)) :
    fieldProj (L2.equivPSL F).symm (psl2AutHom α) = (gammaOf hodd h3 α).right := by
  have hθ : thetaEquiv hodd h3 = semilinearEquivAut F := MulEquiv.ext (thetaEquiv_eq hodd h3)
  rw [fieldProj_apply]
  show ((semilinearEquivAut F).symm (MulAut.congr (toPSL (L2.equivPSL F).symm) (psl2AutHom α))).right =
    ((thetaEquiv hodd h3).symm (psl2AutHom α)).right
  rw [hθ]
  have : toPSL (L2.equivPSL F).symm = MulEquiv.refl (PSL2 F) := by
    ext x
    simp [toPSL]
  rw [this]
  rfl

omit [Finite F] in
theorem psl2AutHom_conj (j : SpecialLinearGroup (Fin 2) F) :
    psl2AutHom (MulAut.conj j) =
      MulAut.conj (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F)) j) := by
  ext x
  induction x using QuotientGroup.induction_on with | H b => ?_
  simp [psl2AutHom, MulAut.conj_apply]
  rfl

theorem sl_outer_structure
    {Q : Type} [Group Q] [Finite Q] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (e : Q ≃* SpecialLinearGroup (Fin 2) F) (M : Subgroup (MulAut Q))
    (hM : IsPGroup 2 ↥M) (P₀ : Sylow 2 Q)
    (hP₀ : (P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ≤ M)
    (hf : ∀ φ ∈ M, orderOf φ = 2 → (gammaOf hodd h3 (MulAut.congr e φ)).right = 1) :
    ((P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q)).relIndex M ≤ 2 ∧
      ((∃ n, IsDihedralTwoGroup ↥M n) ∨ ∃ n, IsSemidihedralTwoGroup ↥M n) := by
  have hL2 : L2Field F := ⟨hodd, h3⟩
  let ι : MulAut Q →* MulAut (PSL2 F) := psl2AutHom.comp (MulAut.congr e).toMonoidHom
  have hι : Function.Injective ι :=
    (psl2AutHom_injective hodd h3).comp (MulAut.congr e).injective
  let π : Q →* PSL2 F :=
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))).comp e.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hιconj : ∀ x : Q, ι (MulAut.conj x) = MulAut.conj (π x) := by
    intro x
    show psl2AutHom (MulAut.congr e (MulAut.conj x)) = _
    rw [congr_conj, psl2AutHom_conj]
    rfl
  let e₀ : PSL2 F ≃* L2 F := (L2.equivPSL F).symm
  let P₀' : Sylow 2 (PSL2 F) := P₀.mapSurjective hπ
  have hP₀'coe : (P₀' : Subgroup (PSL2 F)) = (P₀ : Subgroup Q).map π :=
    Sylow.coe_mapSurjective _ _
  have hM' : IsPGroup 2 ↥(M.map ι) := hM.of_equiv (Subgroup.equivMapOfInjective M ι hι)
  have hD' : ((P₀' : Subgroup (PSL2 F)).map (MulAut.conj : PSL2 F →* MulAut (PSL2 F))) =
      ((P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q)).map ι := by
    rw [hP₀'coe, Subgroup.map_map, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun x => (hιconj x).symm
  have hP₀'M : (P₀' : Subgroup (PSL2 F)).map (MulAut.conj : PSL2 F →* MulAut (PSL2 F)) ≤
      M.map ι := by
    rw [hD']
    exact Subgroup.map_mono hP₀
  have hf' : ∀ φ' ∈ M.map ι, orderOf φ' = 2 → fieldProj e₀ φ' = 1 := by
    rintro _ ⟨φ, hφ, rfl⟩ hord
    have hord' : orderOf φ = 2 := by rw [← hord]; exact (orderOf_injective ι hι φ).symm
    have : ι φ = psl2AutHom (MulAut.congr e φ) := rfl
    rw [this, fieldProj_psl2AutHom hodd h3]
    exact hf φ hφ hord'
  obtain ⟨hrel, hdih⟩ := outer_structure hL2 e₀ (M.map ι) hM' P₀' hP₀'M hf'
  rw [hD', Subgroup.relIndex_map_map_of_injective _ _ hι] at hrel
  refine ⟨hrel, ?_⟩
  have eM : ↥M ≃* ↥(M.map ι) := Subgroup.equivMapOfInjective M ι hι
  rcases hdih with ⟨n, hn⟩ | ⟨n, hn⟩
  · exact Or.inl ⟨n, isDihedralTwoGroup_congr eM.symm hn⟩
  · exact Or.inr ⟨n, isSemidihedralTwoGroup_congr eM.symm hn⟩

theorem sl_dihedral_field {Q : Type} [Group Q] [Finite Q] (hodd : Odd (Nat.card F))
    (h3 : 3 < Nat.card F) (e : Q ≃* SpecialLinearGroup (Fin 2) F) (M : Subgroup (MulAut Q))
    (hM : IsPGroup 2 ↥M) (P₀ : Sylow 2 Q)
    (hP₀ : (P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ≤ M)
    (hdih : ∃ n, IsDihedralTwoGroup ↥M n) :
    ∀ φ ∈ M, (gammaOf hodd h3 (MulAut.congr e φ)).right = 1 := by
  have hL2 : L2Field F := ⟨hodd, h3⟩
  let ι : MulAut Q →* MulAut (PSL2 F) := psl2AutHom.comp (MulAut.congr e).toMonoidHom
  have hι : Function.Injective ι :=
    (psl2AutHom_injective hodd h3).comp (MulAut.congr e).injective
  let π : Q →* PSL2 F :=
    (QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin 2) F))).comp e.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp e.surjective
  have hιconj : ∀ x : Q, ι (MulAut.conj x) = MulAut.conj (π x) := by
    intro x
    show psl2AutHom (MulAut.congr e (MulAut.conj x)) = _
    rw [congr_conj, psl2AutHom_conj]
    rfl
  let e₀ : PSL2 F ≃* L2 F := (L2.equivPSL F).symm
  let P₀' : Sylow 2 (PSL2 F) := P₀.mapSurjective hπ
  have hP₀'coe : (P₀' : Subgroup (PSL2 F)) = (P₀ : Subgroup Q).map π :=
    Sylow.coe_mapSurjective _ _
  have hM' : IsPGroup 2 ↥(M.map ι) := hM.of_equiv (Subgroup.equivMapOfInjective M ι hι)
  have hD' : ((P₀' : Subgroup (PSL2 F)).map (MulAut.conj : PSL2 F →* MulAut (PSL2 F))) =
      ((P₀ : Subgroup Q).map (MulAut.conj : Q →* MulAut Q)).map ι := by
    rw [hP₀'coe, Subgroup.map_map, Subgroup.map_map]
    congr 1
    exact MonoidHom.ext fun x => (hιconj x).symm
  have hP₀'M : (P₀' : Subgroup (PSL2 F)).map (MulAut.conj : PSL2 F →* MulAut (PSL2 F)) ≤
      M.map ι := by
    rw [hD']
    exact Subgroup.map_mono hP₀
  have eM : ↥M ≃* ↥(M.map ι) := Subgroup.equivMapOfInjective M ι hι
  have hdih' : ∃ n, IsDihedralTwoGroup ↥(M.map ι) n := by
    obtain ⟨n, hn⟩ := hdih
    exact ⟨n, isDihedralTwoGroup_congr eM hn⟩
  intro φ hφ
  have h1 := dihedral_overgroup_field hL2 e₀ (M.map ι) hM' P₀' hP₀'M hdih' (ι φ) ⟨φ, hφ, rfl⟩
  have : ι φ = psl2AutHom (MulAut.congr e φ) := rfl
  rw [this, fieldProj_psl2AutHom hodd h3] at h1
  exact h1

end Bridge

section A7

variable {Q : Type} [Group Q] [Finite Q]

omit [Finite Q] in
theorem card_of_double_cover_alt7 (h7 : IsDoubleCoverOfAlt Q 7) : Nat.card Q = 5040 := by
  obtain ⟨-, hZ, ⟨iso⟩⟩ := h7
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q), Nat.card_congr iso.toEquiv, hZ,
    Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem eq_or_eq_of_index_two {X : Type} [Group X] {D M T : Subgroup X} (hDM : D ≤ M) (hMT : M ≤ T)
    (hidx : (D.subgroupOf T).index = 2) : M = D ∨ M = T := by
  by_cases hMD : M ≤ D
  · exact Or.inl (le_antisymm hMD hDM)
  · right
    have hex : ∃ m ∈ M, m ∉ D := by
      by_contra hcon
      push Not at hcon
      exact hMD fun m hm => hcon m hm
    obtain ⟨m, hmM, hmD⟩ := hex
    apply le_antisymm hMT
    intro y hy
    by_cases hyD : y ∈ D
    · exact hDM hyD
    · have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨y, hy⟩ : T))
        (b := (⟨m⁻¹, T.inv_mem (hMT hmM)⟩ : T))
      have h1 : (⟨y, hy⟩ : T) ∉ D.subgroupOf T := hyD
      have h2 : (⟨m⁻¹, T.inv_mem (hMT hmM)⟩ : T) ∉ D.subgroupOf T := fun hh =>
        hmD (by simpa using D.inv_mem (Subgroup.mem_subgroupOf.1 hh))
      have h3 := key.2 (iff_of_false h1 h2)
      have h4 : y * m⁻¹ ∈ D := Subgroup.mem_subgroupOf.1 h3
      have : y = (y * m⁻¹) * m := by group
      rw [this]
      exact M.mul_mem (hDM h4) hmM

theorem a7_cases (h2A7 : II4_2A7) (h7 : IsDoubleCoverOfAlt Q 7)
    (M : Subgroup (MulAut Q)) (hM : IsPGroup 2 ↥M) (P : Sylow 2 Q)
    (hDM : (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ≤ M) :
    M = (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ∨
      ∃ T : Sylow 2 (MulAut Q), M = (T : Subgroup (MulAut Q)) ∧
        (¬ ∃ n, IsDihedralTwoGroup ↥T n) ∧
        ∃ φ ∈ (T : Subgroup (MulAut Q)), φ ∉ innOf Q ∧ φ * φ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, c3, c4, c5, -, -⟩ := h2A7 Q h7
  have hInnN : (innOf Q).Normal := innOf_normal Q
  set D : Subgroup (MulAut Q) := (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) with hD
  have hDInn : D ≤ innOf Q := Subgroup.map_le_range _ _
  obtain ⟨T, hMT⟩ := hM.exists_le_sylow
  obtain ⟨-, hTnd, φ₀, hφ₀T, hφ₀inn, hφ₀2⟩ := c5 T
  obtain ⟨P', hP'⟩ := Glauberman.sylow_inf_normal (G := MulAut Q) (p := 2) T (N := innOf Q)
  have hcardT : Nat.card ↥((T : Subgroup (MulAut Q)) ⊓ innOf Q) =
      2 ^ (Nat.card ↥(innOf Q)).factorization 2 := by
    have h1 : Nat.card ↥((T : Subgroup (MulAut Q)) ⊓ innOf Q) =
        Nat.card ↥(((T : Subgroup (MulAut Q)) ⊓ innOf Q).subgroupOf (innOf Q)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        (T : Subgroup (MulAut Q)) ⊓ innOf Q ≤ innOf Q)).toEquiv.symm
    have h2 := Sylow.card_eq_multiplicity P'
    rw [hP'] at h2
    rw [h1, h2]
  have hcardD : Nat.card ↥D = 2 ^ (Nat.card ↥(innOf Q)).factorization 2 := by
    let f : Q →* ↥(innOf Q) := (MulAut.conj : Q →* MulAut Q).rangeRestrict
    have hf : Function.Surjective f := (MulAut.conj : Q →* MulAut Q).rangeRestrict_surjective
    let P'' : Sylow 2 ↥(innOf Q) := P.mapSurjective hf
    have h2 := Sylow.card_eq_multiplicity P''
    have h3 : (P'' : Subgroup ↥(innOf Q)) = (P : Subgroup Q).map f := Sylow.coe_mapSurjective _ _
    rw [h3] at h2
    have h4 : D = ((P : Subgroup Q).map f).map (innOf Q).subtype := by
      rw [Subgroup.map_map]
      rfl
    rw [h4, Subgroup.card_map_of_injective (innOf Q).subtype_injective]
    exact h2
  have hDT : D ≤ (T : Subgroup (MulAut Q)) ⊓ innOf Q := le_inf (hDM.trans hMT) hDInn
  have hDeq : D = (T : Subgroup (MulAut Q)) ⊓ innOf Q :=
    Subgroup.eq_of_le_of_card_ge hDT (by rw [hcardT, hcardD])
  have hrel : (D.subgroupOf (T : Subgroup (MulAut Q))).index = 2 := by
    have h1 : D.relIndex (T : Subgroup (MulAut Q)) =
        (innOf Q).relIndex (T : Subgroup (MulAut Q)) := by
      rw [hDeq, inf_comm, Subgroup.inf_relIndex_right]
    have h2 : (innOf Q).relIndex (T : Subgroup (MulAut Q)) ∣ (innOf Q).index :=
      Subgroup.relIndex_dvd_index_of_normal _ _
    rw [c4] at h2
    have h3 : (innOf Q).relIndex (T : Subgroup (MulAut Q)) ≠ 1 := by
      intro h
      exact hφ₀inn (Subgroup.relIndex_eq_one.1 h hφ₀T)
    have h4 := (Nat.dvd_prime Nat.prime_two).1 h2
    show D.relIndex (T : Subgroup (MulAut Q)) = 2
    rw [h1]
    exact h4.resolve_left h3
  rcases eq_or_eq_of_index_two hDM hMT hrel with hMD | hMT'
  · exact Or.inl hMD
  · exact Or.inr ⟨T, hMT', hTnd, φ₀, hφ₀T, hφ₀inn, hφ₀2⟩

theorem a7_range_eq (h2A7 : II4_2A7) (h7 : IsDoubleCoverOfAlt Q 7) (hOK : HatOK Q)
    (M : Subgroup (MulAut Q)) (hM : IsPGroup 2 ↥M) (P : Sylow 2 Q)
    (hDM : (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) ≤ M)
    (hno : ∀ φ ∈ M, IsFAutomorphism Q φ → φ = 1) :
    M = (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) := by
  obtain ⟨-, -, c3, -⟩ := h2A7 Q h7
  rcases a7_cases h2A7 h7 M hM P hDM with hMD | ⟨T, hMT, -, φ₀, hφ₀T, hφ₀inn, hφ₀2⟩
  · exact hMD
  · exfalso
    have hφ₀M : φ₀ ∈ M := by rw [hMT]; exact hφ₀T
    have hφ₀1 : φ₀ = 1 := hno φ₀ hφ₀M (c3 φ₀ hφ₀2 hφ₀inn hOK.kgrp)
    exact hφ₀inn (hφ₀1 ▸ Subgroup.one_mem _)

theorem a7_dihedral
    (h7 : IsDoubleCoverOfAlt Q 7) (hOK : HatOK Q) (P : Sylow 2 Q) :
    ∃ n, IsDihedralTwoGroup ↥((P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q)) n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5040 := card_of_double_cover_alt7 h7
  have h16 : 16 ∣ Nat.card ↥(P : Subgroup Q) := by
    rw [Sylow.card_eq_multiplicity P, h5040]
    have h4 : 4 ≤ (5040 : ℕ).factorization 2 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (by norm_num)).1
        (by norm_num : 2 ^ 4 ∣ 5040)
    calc (16 : ℕ) = 2 ^ 4 := by norm_num
      _ ∣ 2 ^ (5040 : ℕ).factorization 2 := pow_dvd_pow 2 h4
  obtain ⟨n, hn2, ⟨ε⟩⟩ :=
    sylow_quaternion_of_quasisimple hOK.quasi (noCommInv_of_pRank hOK.rank) P h16
  obtain ⟨-, hZ, -⟩ := h7
  obtain ⟨zc, hzc2⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Q)) 2 (by rw [hZ])
  set z : Q := (zc : Q) with hz
  have hzcen : z ∈ Subgroup.center Q := zc.2
  have hz2 : orderOf z = 2 := by rw [hz, Subgroup.orderOf_coe]; exact hzc2
  have hzz : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
  have hznorm : z ∈ normalizer ((P : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hc : z * h * z⁻¹ = h := by
      have := Subgroup.mem_center_iff.1 hzcen h
      calc z * h * z⁻¹ = (h * z) * z⁻¹ := by rw [this]
        _ = h := by group
    rw [hc]
  have hzP : z ∈ (P : Subgroup Q) :=
    CFSG.Walter.J1.JankoHyp.mem_sylow_of_mem_normalizer P hznorm (k := 1)
      (by rw [pow_one, pow_two]; exact hzz)
  have hcen : ∀ y ∈ Subgroup.center Q, y = 1 ∨ y = z :=
    fun y hy => eq_one_or_of_center_card_two hzcen hz2 hZ hy
  let g : ↥(P : Subgroup Q) →* MulAut Q :=
    (MulAut.conj : Q →* MulAut Q).comp (P : Subgroup Q).subtype
  have hgr : g.range = (P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hgk : g.ker = (zpowers z).subgroupOf (P : Subgroup Q) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show MulAut.conj (x : Q) = 1 ↔ (x : Q) ∈ zpowers z
    constructor
    · intro h
      rcases hcen x (mem_center_of_conj_eq_one h) with h1 | h1
      · rw [h1]
        exact one_mem _
      · rw [h1]
        exact mem_zpowers z
    · intro h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
      have : (x : Q) ∈ Subgroup.center Q := by
        rw [← hk]
        exact zpow_mem hzcen k
      exact conj_eq_one_of_mem_center this
  have : NeZero (2 ^ n) := ⟨by positivity⟩
  obtain ⟨hN, ⟨d⟩⟩ := CFSG.GH74.GLS.Stage1.Thm3.Sec7.QM.quot_equiv ε.symm hzP hz2
  have eD : ↥((P : Subgroup Q).map (MulAut.conj : Q →* MulAut Q)) ≃* DihedralGroup (2 ^ n) :=
    (MulEquiv.subgroupCongr hgr.symm).trans ((QuotientGroup.quotientKerEquivRange g).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hgk).trans d))
  refine ⟨n + 1, by omega, 2 ^ n, by rw [pow_succ]; ring, ?_, ⟨eD⟩⟩
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

end A7

section Main

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G}

theorem std6_S_pgroup (h : Std6 G z S) : IsPGroup 2 ↥S := h.sylow.isPGroup

theorem std6_exists_sylow_P (h : Std6 G z S) {K : Subgroup G} (hK : IsRigidRankOneComp z K) :
    ∃ P : Sylow 2 ↥K, (P : Subgroup ↥K).map K.subtype = S ⊓ K := by
  have hS : CFSG.QuasithinUnique.IsSylowTwoOf S (centralizer ({z} : Set G)) :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.2 h.sylow
  obtain ⟨Kc, hKcomp, hsub, hmap, hmin⟩ := (rigid_isPCompIn hK).2
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hS (rigid_isPCompIn hK).1 hsub
  exact CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_iff_exists.1 hSK

theorem ivk_1_4hij_outer_of_II4
    (h44 : II4_44) (h2A7 : II4_2A7) :
    CFSG.GH74.GLS.Stage1.Thm3.Sec6.IVK_1_4hij_outer := by
  intro G _ _ z S h K hK hcond
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOK := std6_hatOK h44 h hK
  obtain ⟨Pbar, hPbar⟩ := exists_sylow_hatImg (std6_exists_sylow_P h hK)
  have hS₁N : S1 S K ≤ normalizer (K : Set G) := inf_le_right
  have hS₁S : S1 S K ≤ S := inf_le_left
  let ρ : ↥(S1 S K) →* MulAut (Hat K) := (phiHom K).comp (Subgroup.inclusion hS₁N)
  have hρ : ∀ x : ↥(S1 S K), ρ x = phi K (x : G) (hS₁N x.2) := fun x => rfl
  have hker : ρ.ker = (Qof S K).subgroupOf (S1 S K) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hρ, phi_eq_one_iff K (hS₁N x.2)]
    exact ⟨fun hx => ⟨hS₁S x.2, hx⟩, fun hx => hx.2⟩
  have hS₁p : IsPGroup 2 ↥(S1 S K) := (std6_S_pgroup h).to_inf_left
  have hPS₁ : Pof S K ≤ S1 S K := le_inf inf_le_left (inf_le_right.trans le_normalizer)
  have hQS₁ : Qof S K ≤ S1 S K := fun x hx => ⟨hx.1, hx.2.1⟩
  have hD : ((Pof S K).subgroupOf (S1 S K)).map ρ =
      (Pbar : Subgroup (Hat K)).map (MulAut.conj : Hat K →* MulAut (Hat K)) := by
    ext φ
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxP : (x : G) ∈ S ⊓ K := hx
      refine ⟨hatMk K ⟨(x : G), hxP.2⟩, ?_, ?_⟩
      · rw [hPbar]
        exact hatMk_mem_hatImg (inf_le_right : S ⊓ K ≤ K) hxP
      · rw [hρ]
        exact (phi_of_mem K hxP.2).symm
    · rintro ⟨y, hy, rfl⟩
      rw [hPbar] at hy
      obtain ⟨a, haP, rfl⟩ := mem_hatImg.1 hy
      refine ⟨⟨(a : G), hPS₁ haP⟩, haP, ?_⟩
      rw [hρ]
      exact phi_of_mem K a.2
  have hMp : IsPGroup 2 ↥ρ.range := hS₁p.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hDM : (Pbar : Subgroup (Hat K)).map (MulAut.conj : Hat K →* MulAut (Hat K)) ≤ ρ.range := by
    rw [← hD]
    exact Subgroup.map_le_range _ _
  have hrelI : (Pof S K ⊔ Qof S K).relIndex (S1 S K) =
      ((Pbar : Subgroup (Hat K)).map (MulAut.conj : Hat K →* MulAut (Hat K))).relIndex ρ.range := by
    have h1 : ((Pof S K ⊔ Qof S K).subgroupOf (S1 S K)) =
        (Pof S K).subgroupOf (S1 S K) ⊔ ρ.ker := by
      rw [Subgroup.subgroupOf_sup hPS₁ hQS₁, hker]
    have h2 := Subgroup.relIndex_map_map ρ ((Pof S K).subgroupOf (S1 S K)) ⊤
    rw [← MonoidHom.range_eq_map, top_sup_eq, Subgroup.relIndex_top_right, hD] at h2
    show ((Pof S K ⊔ Qof S K).subgroupOf (S1 S K)).index = _
    rw [h1, ← h2]
  have key : ((Pbar : Subgroup (Hat K)).map (MulAut.conj : Hat K →* MulAut (Hat K))).relIndex
        ρ.range ≤ 2 ∧
      ((∃ n, IsDihedralTwoGroup ↥ρ.range n) ∨ ∃ n, IsSemidihedralTwoGroup ↥ρ.range n) ∧
      (IsDoubleCoverOfAlt (Hat K) 7 →
        ρ.range = (Pbar : Subgroup (Hat K)).map (MulAut.conj : Hat K →* MulAut (Hat K))) := by
    rcases sl_or_a7 hOK.sl2 with ⟨F, hFf, hFin, hodd, h3, ⟨e⟩⟩ | h7
    · have hf : ∀ φ ∈ ρ.range, orderOf φ = 2 →
          (gammaOf hodd h3 (MulAut.congr e φ)).right = 1 := by
        rintro _ ⟨x, rfl⟩ hord
        by_contra hσ
        have hφ2 : ρ x * ρ x = 1 := mul_self_eq_one_of_orderOf_eq_two hord
        have hα2 : MulAut.congr e (ρ x) * MulAut.congr e (ρ x) = 1 := by
          rw [← map_mul, hφ2, map_one]
        have hF : InducesFAut (x : G) K := ⟨hS₁N x.2, hOK.quasi, hOK.kgrp, hOK.rank,
          exists_pow_two_orderOf hφ2, fixedCond_of_congr e (fixedCond_of_field_part hodd h3 _ hα2 hσ)⟩
        have hcs : (x : G) ∈ cSec K := hcond x x.2 hF
        have h1 : ρ x = 1 := by
          rw [hρ]
          exact (phi_eq_one_iff K _).2 hcs
        rw [h1, orderOf_one] at hord
        omega
      obtain ⟨hrel, hdih⟩ := sl_outer_structure hodd h3 e ρ.range hMp Pbar hDM hf
      exact ⟨hrel, hdih, fun h7 =>
        (not_sl2_of_double_cover_alt7 h7 (e.trans (specialLinearGroupEquivStatedSL 2 F))).elim⟩
    · have hno : ∀ φ ∈ ρ.range, IsFAutomorphism (Hat K) φ → φ = 1 := by
        rintro _ ⟨x, rfl⟩ hFA
        have hcs := hcond x x.2 ⟨hS₁N x.2, hFA⟩
        rw [hρ]
        exact (phi_eq_one_iff K _).2 hcs
      have hMD := a7_range_eq h2A7 h7 hOK ρ.range hMp Pbar hDM hno
      refine ⟨by rw [hMD, Subgroup.relIndex_self]; norm_num, ?_, fun _ => hMD⟩
      obtain ⟨n, hn⟩ := a7_dihedral h7 hOK Pbar
      exact Or.inl ⟨n, isDihedralTwoGroup_congr (MulEquiv.subgroupCongr hMD.symm) hn⟩
  obtain ⟨hrel, hdih, hmid⟩ := key
  have hN : ((Qof S K).subgroupOf (S1 S K)).Normal := by
    rw [← hker]
    exact ρ.normal_ker
  refine ⟨?_, ?_, ?_⟩
  · rw [hrelI]
    exact hrel
  · intro h7
    have hMD := hmid h7
    have h1 : (Pof S K ⊔ Qof S K).relIndex (S1 S K) = 1 := by
      rw [hrelI, hMD, Subgroup.relIndex_self]
    exact le_antisymm (Subgroup.relIndex_eq_one.1 h1) (sup_le hPS₁ hQS₁)
  · refine ⟨hN, ?_⟩
    have eΦ : (↥(S1 S K) ⧸ (Qof S K).subgroupOf (S1 S K)) ≃* ↥ρ.range :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange ρ)
    rcases hdih with ⟨n, hn⟩ | ⟨n, hn⟩
    · exact Or.inl ⟨n, isDihedralTwoGroup_congr eΦ.symm hn⟩
    · exact Or.inr ⟨n, isSemidihedralTwoGroup_congr eΦ.symm hn⟩

end Main

end CFSG.GH74.GLS.IVK.Lifted
