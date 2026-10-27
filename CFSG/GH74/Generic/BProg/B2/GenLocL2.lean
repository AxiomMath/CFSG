module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasicRed
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Model
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGenMain

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 Subgroup CFSG.Blueprint CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts

namespace GenLocL2

variable {J : Type} [Group J] {A : Type} [Group A]

theorem smul_mem_gammaAct (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut J) (c : A)
    {x : J} (hx : x ∈ gammaAct α) : α c x ∈ gammaAct α := by
  have hle : gammaAct α ≤ (gammaAct α).comap (α c).toMonoidHom := by
    refine iSup₂_le fun E hE y hy => ?_
    rw [Subgroup.mem_comap]
    refine le_gammaAct α hE ?_
    rw [GenLocBasic.mem_fixedIn_map]
    intro e he
    have hy' := (GenLocBasic.mem_fixedIn_map α E y).1 hy e he
    have hcomm : e * c = c * e := mul_comm' e c
    calc α e ((α c).toMonoidHom y) = α (e * c) y := by simp [map_mul]
      _ = α (c * e) y := by rw [hcomm]
      _ = α c (α e y) := by simp [map_mul]
      _ = (α c).toMonoidHom y := by rw [hy']; rfl
  exact hle hx

theorem fixedIn_zpowers (α : A →* MulAut J) {c : A} {y : J} (h : α c y = y) :
    y ∈ fixedIn J ((Subgroup.zpowers c).map α) := by
  rw [GenLocBasic.mem_fixedIn_map]
  intro a ha
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  have hmem : α c ∈ MulAction.stabilizer (MulAut J) y := by
    rw [MulAction.mem_stabilizer_iff]
    exact h
  have := (MulAction.stabilizer (MulAut J) y).zpow_mem hmem n
  rw [MulAction.mem_stabilizer_iff] at this
  rw [map_zpow]
  exact this

theorem adm_zpowers [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (h4 : Nat.card A = 4) {c : A}
    (hc : c ≠ 1) : pRank 2 A - 1 ≤ pRank 2 ↥(Subgroup.zpowers c) := by
  rw [GenLocBasic.adm_iff_index hA]
  have hsq : c * c = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA c
  have hord : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsq) hc
  have h1 := Subgroup.card_mul_index (Subgroup.zpowers c)
  rw [Nat.card_zpowers, hord, h4] at h1
  omega


theorem exists_klein_gens [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (h4 : Nat.card A = 4) :
    ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ ∀ c : A, c = 1 ∨ c = a ∨ c = b ∨ c = a * b := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have hcardF : Fintype.card A = 4 := by rw [← Nat.card_eq_fintype_card, h4]
  have hsq : ∀ x : A, x * x = 1 := fun x => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA x
  obtain ⟨a, ha⟩ : ∃ a : A, a ≠ 1 := by
    by_contra h
    push Not at h
    have : Fintype.card A ≤ 1 := Fintype.card_le_one_iff.mpr (fun a b => by rw [h a, h b])
    omega
  obtain ⟨b, hb1, hba⟩ : ∃ b : A, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset A) ⊆ {1, a} := by
      intro x _
      by_cases hx : x = 1
      · simp [hx]
      · simp [h x hx]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, hcardF] at this
    have h2 := Finset.card_le_two (a := (1 : A)) (b := a)
    omega
  have hinv : ∀ x : A, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hba
    have : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this, hinv]
  have habA : a * b ≠ a := by
    intro h
    exact hb1 (by simpa using h)
  have habB : a * b ≠ b := by
    intro h
    exact ha (by simpa using h)
  refine ⟨a, b, ha, hb1, fun h => hba h.symm, ?_⟩
  intro c
  have e1 : (1 : A) ∉ ({a, b, a * b} : Finset A) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm ha, Ne.symm hb1, Ne.symm hab1⟩
  have e2 : a ∉ ({b, a * b} : Finset A) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hba, Ne.symm habA⟩
  have hc4 : ({1, a, b, a * b} : Finset A).card = 4 := by
    rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
      Finset.card_pair (Ne.symm habB)]
  have hall : (Finset.univ : Finset A) = {1, a, b, a * b} :=
    (Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      (by rw [Finset.card_univ, hcardF, hc4])).symm
  have hx : c ∈ (Finset.univ : Finset A) := Finset.mem_univ c
  rw [hall] at hx
  simpa using hx


section Transport

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
theorem conjPSL_eq_semilinear {F : Type} [Field F] [Finite F] (hK : IsOddPrimePower (Nat.card F))
    (hcard : 3 < Nat.card F) (γ : PGammaL2 F) (x : PSL2 F) :
    conjPSL F hK hcard γ x = CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction F γ x := by
  apply incl_injective F
  have h1 := psl2Incl_conjPSL F hK hcard γ x
  have h2 := conj_incl γ x
  exact h1.trans h2

end Transport


section Core

open CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2 in
theorem gammaAct_psl2_core {J : Type} [Group J] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hJ : LieModel J .PSL 2 p f)
    {A : Type} [Group A] [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (h4 : Nat.card A = 4)
    (α : A →* MulAut J) :
    gammaAct α = ⊤ ∨ (p ^ f ∈ ({5, 7, 9} : Finset ℕ) ∧
      α.range ≤ (MulAut.conj : J →* MulAut J).range) := by
  obtain ⟨-, hf1, -, -, F, _, _, hF, ⟨e⟩⟩ := lieModel_psl2_data hJ
  have : Fact p.Prime := ⟨hp⟩
  have hK : IsOddPrimePower (Nat.card F) := isOddPrimePower_of hp hp2 hf1 hF
  have hcard : 3 < Nat.card F := by rw [hF]; omega
  obtain ⟨a, b, ha, hb, hab, hall⟩ := exists_klein_gens hA h4
  by_cases hker : ∃ c : A, c ≠ 1 ∧ α c = 1
  · left
    obtain ⟨c, hc1, hc⟩ := hker
    refine gammaAct_eq_top_of_le_ker α (E := Subgroup.zpowers c) (adm_zpowers hA h4 hc1) ?_
    rw [Subgroup.zpowers_le]
    exact hc
  push Not at hker
  set Φ := autEquiv e with hΦ
  have hsqA : ∀ c : A, c * c = 1 := fun c => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA c
  have hab' : a * b ≠ 1 := by
    intro h
    apply hab
    have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [h1, inv_eq_of_mul_eq_one_right (hsqA a)]
  have hβ1 : ∀ c : A, c ≠ 1 → Φ (α c) ≠ 1 := fun c hc h =>
    hker c hc (Φ.injective (by rw [h, map_one]))
  have hβ2 : ∀ c : A, Φ (α c) ^ 2 = 1 := fun c => by
    rw [← map_pow, ← map_pow, pow_two, hsqA c, map_one, map_one]
  have hβne : Φ (α a) ≠ Φ (α b) := by
    intro h
    apply hker (a * b) hab'
    have h1 : α a = α b := Φ.injective h
    rw [map_mul, ← h1, ← map_mul, hsqA a, map_one]
  have hβcomm : Φ (α a) * Φ (α b) = Φ (α b) * Φ (α a) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm' a b]
  set H : Subgroup (PSL2 F) := (gammaAct α).map e.toMonoidHom with hH
  have hmemH : ∀ y : J, e y ∈ H ↔ y ∈ gammaAct α := by
    intro y
    constructor
    · rintro ⟨z, hz, hzy⟩
      have : z = y := e.injective hzy
      rwa [← this]
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hγ : ∀ γ ∈ ({Φ (α a), Φ (α b), Φ (α a) * Φ (α b)} : Set (PGammaL2 F)),
      ∃ c : A, c ≠ 1 ∧ γ = Φ (α c) := by
    intro γ hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl
    · exact ⟨a, ha, rfl⟩
    · exact ⟨b, hb, rfl⟩
    · exact ⟨a * b, hab', by rw [map_mul, map_mul]⟩
  have hinv : ∀ γ ∈ ({Φ (α a), Φ (α b), Φ (α a) * Φ (α b)} : Set (PGammaL2 F)), ∀ x ∈ H,
      conjPSL F hK hcard γ x ∈ H := by
    intro γ hγ' x hx
    obtain ⟨c, hc1, rfl⟩ := hγ γ hγ'
    obtain ⟨y, hy, rfl⟩ := hx
    rw [conjPSL_eq_semilinear hK hcard]
    change CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction F (autEquiv e (α c)) (e y) ∈ H
    rw [semilinearAction_autEquiv_apply]
    exact (hmemH _).2 (smul_mem_gammaAct hA α c hy)
  have hP1 : ∀ γ ∈ ({Φ (α a), Φ (α b), Φ (α a) * Φ (α b)} : Set (PGammaL2 F)), ∀ x : PSL2 F,
      γ * psl2Incl F x = psl2Incl F x * γ → Odd (orderOf x) → x ∈ H := by
    intro γ hγ' x hcomm _
    obtain ⟨c, hc1, rfl⟩ := hγ γ hγ'
    have h1 : CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction F
        (Φ (α c)) x = x := (commute_incl_iff _ _).1 hcomm
    obtain ⟨y, rfl⟩ := e.surjective x
    have h2 : α c y = y :=
      e.injective ((semilinearAction_autEquiv_apply e (α c) y).symm.trans h1)
    exact (hmemH y).2 (le_gammaAct α (adm_zpowers hA h4 hc1) (fixedIn_zpowers α h2))
  have hP2 : ∀ γ ∈ ({Φ (α a), Φ (α b), Φ (α a) * Φ (α b)} : Set (PGammaL2 F)), ∀ t : PSL2 F,
      t ^ 2 = 1 → t ≠ 1 → γ = psl2Incl F t → ∀ y : PSL2 F, t ∈ Subgroup.zpowers y → y ∈ H := by
    intro γ hγ' t _ _ hγt y hty
    obtain ⟨c, hc1, rfl⟩ := hγ γ hγ'
    obtain ⟨t', rfl⟩ := e.surjective t
    obtain ⟨y', rfl⟩ := e.surjective y
    have h1 : α c = MulAut.conj t' := by
      apply Φ.injective
      rw [autEquiv_conj]
      exact hγt
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hty
    have hn' : y' ^ n = t' := e.injective (by rw [map_zpow, hn])
    have hcomm : t' * y' * t'⁻¹ = y' := by
      rw [← hn']
      exact (Commute.zpow_left (Commute.refl y') n).mul_inv_cancel
    have h2 : α c y' = y' := by rw [h1, MulAut.conj_apply]; exact hcomm
    exact (hmemH y').2 (le_gammaAct α (adm_zpowers hA h4 hc1) (fixedIn_zpowers α h2))
  have hmain := psl2_generation_model (K := F) (p := p) (f := f) hF hK hcard
    (a := Φ (α a)) (b := Φ (α b)) hβcomm (hβ2 a) (hβ2 b) (hβ1 a ha) (hβ1 b hb) hβne H hinv hP1 hP2
  rcases hmain with htop | ⟨hq, haI, hbI⟩
  · left
    rw [eq_top_iff]
    intro y _
    exact (hmemH y).1 (htop ▸ Subgroup.mem_top _)
  · right
    refine ⟨by rw [← hF]; exact hq, ?_⟩
    have hinner : ∀ c : A, Φ (α c) ∈ (psl2Incl F).range →
        α c ∈ (MulAut.conj : J →* MulAut J).range := by
      rintro c ⟨s, hs⟩
      refine ⟨e.symm s, Φ.injective ?_⟩
      rw [autEquiv_conj, MulEquiv.apply_symm_apply]
      exact hs
    rintro φ ⟨c, rfl⟩
    rcases hall c with rfl | rfl | rfl | rfl
    · rw [map_one]
      exact one_mem _
    · exact hinner _ haI
    · exact hinner _ hbI
    · rw [map_mul]
      exact mul_mem (hinner _ haI) (hinner _ hbI)

end Core


section Rank3

theorem pGammaL2_card_le_four_of_sq_of_odd
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : Odd f)
    (hF : Nat.card F = p ^ f) (E : Subgroup (PGammaL2 F)) (hE : ∀ e ∈ E, e * e = 1) :
    Nat.card E ≤ 4 := by
  have h1 : Nat.card (linearPart E) ≤ 4 :=
    pgl2_card_le_four_of_sq (isOddPrimePower_of hp hp2 hf.pos hF) _ fun g hg =>
      SemidirectProduct.inl_injective (by rw [map_mul, map_one]; exact hE _ hg)
  have h2 : Nat.card (E.map (fieldProj F)) ≤ 1 := by
    have hbot : E.map (fieldProj F) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      rintro _ ⟨x, hx, rfl⟩
      refine eq_one_of_two_power_ringAut hp hF hf _ 1 ?_
      rw [pow_one, pow_two, ← map_mul, hE x hx, map_one]
    rw [hbot, Subgroup.card_bot]
  rw [card_eq_linearPart_mul]
  calc Nat.card (linearPart E) * Nat.card (E.map (fieldProj F)) ≤ 4 * 1 := Nat.mul_le_mul h1 h2
    _ = 4 := by norm_num

theorem gammaAct_subtype_eq_top_of_card_eight
    {J : Type} [Group J] [Finite J] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h13 : 13 ≤ p ^ f) (hJ : LieModel J .PSL 2 p f) (D : Subgroup (MulAut J))
    (hD : CFSG.IsElementaryAbelian 2 ↥D) (h8 : Nat.card D = 8) : gammaAct D.subtype = ⊤ := by
  have : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [h8]; norm_num)
  have hsq : ∀ x ∈ D, x * x = 1 := fun x hx =>
    congrArg Subtype.val (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD (⟨x, hx⟩ : D))
  have hfix := fourgroup_fix_generation hp hp2 h13 hJ hsq h8
  rw [eq_top_iff, ← hfix]
  refine iSup₂_le fun W hWD => iSup_le fun hW4 => ?_
  set E0 : Subgroup ↥D := W.comap D.subtype with hE0
  have hmap : E0.map D.subtype = W := by
    rw [hE0, Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact inf_eq_right.2 hWD
  have hcard : Nat.card E0 = 4 := by
    rw [← Subgroup.card_map_of_injective D.subtype_injective, hmap, hW4]
  have hadm : pRank 2 ↥D - 1 ≤ pRank 2 ↥E0 := by
    rw [GenLocBasic.adm_iff_index hD]
    have h1 := Subgroup.card_mul_index E0
    rw [hcard, h8] at h1
    omega
  refine le_trans ?_ (le_gammaAct D.subtype hadm)
  rw [hmap]
  intro x hx φ hφ
  exact (Subgroup.mem_iInf.1 ((Subgroup.mem_iInf.1 hx) φ) hφ)

end Rank3

end GenLocL2

section L2

variable {A : Type} [Group A] [Finite A]

theorem gammaAct_psl2_rank2 {J : Type} [Group J] [Finite J] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hJ : LieModel J .PSL 2 p f)
    (α : A →* MulAut J) (hA : IsRank23 A) (hk : pRank 2 A = 2)
    (hexc : ¬ (p ^ f ∈ ({5, 7, 9} : Finset ℕ) ∧ α.range ≤ (MulAut.conj : J →* MulAut J).range)) :
    gammaAct α = ⊤ := by
  have h4 : Nat.card A = 4 := by
    rw [GenLocBasic.card_eq_two_pow_pRank_type hA.1, hk]
    norm_num
  exact (GenLocL2.gammaAct_psl2_core hp hp2 h5 hJ hA.1 h4 α).resolve_right hexc

theorem gammaAct_psl2_rank3
    {J : Type} [Group J] [Finite J] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h11 : 11 ≤ p ^ f) (hJ : LieModel J .PSL 2 p f)
    (α : A →* MulAut J) (hA : IsRank23 A) (hk : pRank 2 A = 3) : gammaAct α = ⊤ := by
  have _ := hk
  by_cases hker : ∃ E : Subgroup A, pRank 2 A - 1 ≤ pRank 2 ↥E ∧ E ≤ α.ker
  · obtain ⟨E, hE, hle⟩ := hker
    exact gammaAct_eq_top_of_le_ker α hE hle
  push Not at hker
  obtain ⟨hD, hγ, -⟩ := range_reduction α hA (fun E hE hle => hker E hE hle)
  rw [hγ]
  have : Finite ↥α.range := Finite.of_surjective _ α.rangeRestrict_surjective
  rcases hD.2 with hr2 | hr3
  · have h4 : Nat.card α.range = 4 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr2]
      norm_num
    rcases GenLocL2.gammaAct_psl2_core hp hp2 (by omega) hJ hD.1 h4 α.range.subtype with h | ⟨hq, -⟩
    · exact h
    · exfalso
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      omega
  · have h8 : Nat.card α.range = 8 := by
      rw [GenLocBasic.card_eq_two_pow_pRank_type hD.1, hr3]
      norm_num
    obtain ⟨-, hf1, -, -, F, _, _, hF, ⟨e⟩⟩ := ComponentClassification.AutL2Facts.lieModel_psl2_data hJ
    have hfeven : Even f := by
      by_contra hodd
      rw [Nat.not_even_iff_odd] at hodd
      set E' := α.range.map (autEquiv e).toMonoidHom with hE'
      have hE'2 : ∀ x ∈ E', x * x = 1 := by
        rintro _ ⟨x, hx, rfl⟩
        have hx2 : x * x = 1 := congrArg Subtype.val
          (WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hD.1 (⟨x, hx⟩ : α.range))
        change (autEquiv e) x * (autEquiv e) x = 1
        rw [← map_mul, hx2, map_one]
      have hle := GenLocL2.pGammaL2_card_le_four_of_sq_of_odd hp hp2 hodd hF E' hE'2
      rw [hE', Subgroup.card_map_of_injective (autEquiv e).injective, h8] at hle
      omega
    have h13 : 13 ≤ p ^ f := by
      obtain ⟨m, hm⟩ := hfeven
      have hpf : p ^ f = p ^ m * p ^ m := by rw [hm, pow_add]
      by_contra hlt
      have hm3 : p ^ m ≤ 3 := by
        by_contra h
        have h4 : 4 ≤ p ^ m := by omega
        have := Nat.mul_le_mul h4 h4
        omega
      have := Nat.mul_le_mul hm3 hm3
      omega
    exact GenLocL2.gammaAct_subtype_eq_top_of_card_eight hp hp2 h13 hJ α.range hD.1 h8

theorem genLoc_psl2_of_small_loc
    {J : Type} [Group J] [Finite J] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hJ : LieModel J .PSL 2 p f)
    (hloc : p ^ f ∈ ({5, 7, 9} : Finset ℕ) → ∀ (A : Type) [Group A] [Finite A]
      (α : A →* MulAut J), IsRank23 A → gammaAct α ≠ ⊤ → LocE1 α ∧ LocE2 α ∧ LocE3 α) :
    GenLoc J := by
  intro A _ _ α hA
  by_cases hq : p ^ f ∈ ({5, 7, 9} : Finset ℕ)
  · by_cases hg : gammaAct α = ⊤
    · exact Or.inl hg
    · exact Or.inr (hloc hq A α hA hg)
  · left
    have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two hp2).pow
    have hq' : ¬ (p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9) := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hq
    have h11 : 11 ≤ p ^ f := by omega
    rcases hA.2 with hk | hk
    · exact gammaAct_psl2_rank2 hp hp2 h5 hJ α hA hk (fun h => hq h.1)
    · exact gammaAct_psl2_rank3 hp hp2 h11 hJ α hA hk

end L2

end CFSG.GH74.Generic.BProg.B2
