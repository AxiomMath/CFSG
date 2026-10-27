module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82L2
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourMapInjective

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace L2Comm

open CFSG Subgroup CFSG.ComponentClassification.GSThmB GorensteinWalter
open scoped commutatorElement

theorem commutator_le_of_isCyclic {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [IsCyclic (G ⧸ N)] : commutator G ≤ N := by
  rw [commutator_def, commutator_le]
  intro a _ b _
  rw [← QuotientGroup.eq_one_iff]
  change QuotientGroup.mk' N ⁅a, b⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact (IsMulCommutative.is_comm (M := G ⧸ N)).comm _ _

variable (K : Type) [Field K] [Finite K]

theorem mem_range_of_mem_commutator (hK : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K) {p f : ℕ} [Fact p.Prime] (hKc : Nat.card K = p ^ f)
    {σ : MulAut (PSL2 K)} (hσ : σ ∈ commutator (MulAut (PSL2 K))) :
    ∃ g : PGL2 K, σ = pgl2InnerAutPSL2 K hK hcard g := by
  set Φ := pGammaL2ToMulAutPSL2 K hK hcard with hΦ
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hKc hK hcard
  have hc : commutator (MulAut (PSL2 K)) = (commutator (PGammaL2 K)).map Φ := by
    rw [_root_.commutator_def, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hsurj]
  rw [hc] at hσ
  obtain ⟨x, hx, rfl⟩ := hσ
  have := pGammaL2_quotient_pgl_isCyclic K hK
  have hx' := commutator_le_of_isCyclic
    ((SemidirectProduct.inl : PGL2 K →* PGammaL2 K).range) hx
  obtain ⟨g, rfl⟩ := hx'
  exact ⟨g, pGammaL2ToMulAutPSL2_inl K hK hcard g⟩

theorem apply_eq_of_comm_conj' {G : Type*} [Group G] (hZ : center G = ⊥) {σ : MulAut G} {t : G}
    (h : MulAut.conj t * σ = σ * MulAut.conj t) : σ t = t := by
  have h1 : MulAut.conj (σ t) = MulAut.conj t := by
    ext y
    have := congrArg (fun χ : MulAut G => χ (σ.symm y)) h
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulEquiv.apply_symm_apply] at this
    rw [MulAut.conj_apply, MulAut.conj_apply, this, map_mul, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have h2 : (σ t)⁻¹ * t ∈ center G := by
    rw [mem_center_iff]
    intro y
    have := congrArg (fun χ : MulAut G => χ y) h1
    simp only [MulAut.conj_apply] at this
    calc y * ((σ t)⁻¹ * t) = (σ t)⁻¹ * (σ t * y * (σ t)⁻¹) * t := by group
      _ = (σ t)⁻¹ * (t * y * t⁻¹) * t := by rw [this]
      _ = (σ t)⁻¹ * t * y := by group
  rw [hZ, mem_bot, inv_mul_eq_one] at h2
  exact h2

theorem exists_center_of_fix (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (T : Subgroup (PSL2 K)) {V : Subgroup (PSL2 K)} (hVT : V ≤ T) (hV : IsKleinFour V)
    (g : PGL2 K) (hfix : ∀ t ∈ T, pgl2InnerAutPSL2 K hK hcard g t = t) :
    ∃ t ∈ T, t ∈ centralizer (T : Set (PSL2 K)) ∧
      pgl2InnerAutPSL2 K hK hcard g = MulAut.conj t := by
  set toPGL : PSL2 K →* PGL2 K := Matrix.ProjectiveSpecialLinearGroup.toPGL with htoPGL
  have hinj : Function.Injective toPGL := fun x y hxy =>
    Matrix.ProjectiveSpecialLinearGroup.toPGL_injective hxy
  have hcomm : ∀ t ∈ T, g * toPGL t = toPGL t * g := by
    intro t ht
    have h1 := congrArg toPGL (hfix t ht)
    rw [htoPGL, toPGL_pgl2InnerAutPSL2_apply] at h1
    rw [← htoPGL] at h1
    calc g * toPGL t = g * toPGL t * g⁻¹ * g := by group
      _ = toPGL t * g := by rw [h1]
  have hVP := isKleinFour_map_of_injective V hV toPGL hinj
  have hgC : g ∈ centralizer ((V.map toPGL : Subgroup (PGL2 K)) : Set (PGL2 K)) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨v, hv, rfl⟩
    exact (hcomm v (hVT hv)).symm
  rw [pgl2_kleinFour_centralizer_eq_self K hK _ hVP] at hgC
  obtain ⟨v, hv, rfl⟩ := hgC
  refine ⟨v, hVT hv, ?_, pgl2InnerAutPSL2_toPGL K hK hcard v⟩
  rw [mem_centralizer_iff]
  intro t ht
  apply hinj
  rw [map_mul, map_mul]
  exact (hcomm t ht).symm

end L2Comm

open CFSG Subgroup CFSG.ComponentClassification.GSThmB GorensteinWalter L2Comm

theorem cf82L2Comm : CF82L2Comm := by
  intro Y _ _ p f hp hp2 hf hL T hT σ hσc hσT
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, F, hFf, hFfin, hF, ⟨e₀⟩⟩ := GSLit.statedClassicalModel_of_lieModel_psl_two hL
  set e₁ : Y ≃* PSL2 F :=
    e₀.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm with he₁
  have hK : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hF⟩
  have hcard : 3 < Nat.card F := by
    by_contra hle
    have h3 : Nat.card F = 3 := by
      have h2 : 2 ≤ p := hp.two_le
      have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      have hodd : Odd (Nat.card F) := by rw [hF]; exact (hp.odd_of_ne_two hp2).pow
      obtain ⟨k, hk⟩ := hodd
      have : p ≠ 2 := hp2
      omega
    have hY : Nat.card Y = 12 := by
      rw [Nat.card_congr e₁.toEquiv, psl2_card_formula F hK, h3]
      norm_num
    have hTd : Nat.card T ∣ 12 := hY ▸ card_subgroup_dvd_card (T : Subgroup Y)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 T.isPGroup'
    have hle12 : Nat.card T ≤ 12 := Nat.le_of_dvd (by norm_num) hTd
    rw [hk] at hT hTd hle12
    have hk3 : k = 3 := by
      rcases Nat.lt_or_ge k 4 with h | h
      · interval_cases k <;> simp_all
      · have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
        omega
    subst hk3
    norm_num at hTd
  have hZ : center Y = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have : e₁ z ∈ center (PSL2 F) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := e₁.surjective y
      rw [← map_mul, ← map_mul, mem_center_iff.mp hz x]
    rw [psl2_center_eq_bot F, mem_bot, MulEquiv.map_eq_one_iff] at this
    rw [mem_bot]
    exact this
  have hfix : ∀ t ∈ (T : Subgroup Y), σ t = t := by
    intro t ht
    apply apply_eq_of_comm_conj' hZ
    exact (mem_centralizer_iff.mp hσT) (MulAut.conj t) ⟨t, ht, rfl⟩
  set σ' := MulAut.congr e₁ σ with hσ'
  have hσ'c : σ' ∈ commutator (MulAut (PSL2 F)) := by
    have hc : (commutator (MulAut Y)).map (MulAut.congr e₁).toMonoidHom =
        commutator (MulAut (PSL2 F)) := by
      rw [_root_.commutator_def, _root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr (MulAut.congr e₁).surjective]
    rw [← hc]
    exact ⟨σ, hσc, rfl⟩
  obtain ⟨g, hg⟩ := mem_range_of_mem_commutator F hK hcard hF hσ'c
  set T' : Sylow 2 (PSL2 F) := Sylow.mapSurjective (f := e₁.toMonoidHom) e₁.surjective T with hT'
  have hT'v : (T' : Subgroup (PSL2 F)) = (T : Subgroup Y).map e₁.toMonoidHom := rfl
  have hfix' : ∀ t' ∈ (T' : Subgroup (PSL2 F)), pgl2InnerAutPSL2 F hK hcard g t' = t' := by
    intro t' ht'
    rw [hT'v] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    rw [← hg, hσ', MulEquiv.coe_toMonoidHom]
    change e₁ (σ (e₁.symm (e₁ t))) = e₁ t
    rw [MulEquiv.symm_apply_apply, hfix t ht]
  obtain ⟨m, hm, ⟨eD⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hK T'
  obtain ⟨V, hVT, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (T' : Subgroup (PSL2 F)) hm eD
  obtain ⟨t', ht', ht'C, hconj⟩ := exists_center_of_fix F hK hcard (T' : Subgroup (PSL2 F)) hVT
    hV g hfix'
  refine ⟨e₁.symm t', ?_, ?_, ?_⟩
  · rw [hT'v] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    exact ht
  · rw [mem_centralizer_iff]
    intro x hx
    apply e₁.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact (mem_centralizer_iff.mp ht'C) (e₁ x) (by rw [hT'v]; exact ⟨x, hx, rfl⟩)
  · have h1 : σ = (MulAut.congr e₁).symm σ' := by rw [hσ', MulEquiv.symm_apply_apply]
    rw [h1, hg, hconj]
    ext y
    simp [MulAut.conj_apply]

end CFSG.ComponentClassification.CatFactsL4U4
