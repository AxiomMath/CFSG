module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24PSpClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24PSp5
public import CFSG.Adapters.RankTwoModelTransports

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open CFSG.ComponentClassification.CatFactsSp4 CFSG.Open Subgroup

private abbrev invClassSet {G : Type*} [Group G] (x : G) : Set G :=
  {c : G | c ∈ centralizer ({x} : Set G) ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧ IsConj x c}

private theorem map_centralizer_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    (centralizer ({x} : Set G)).map e.toMonoidHom = centralizer ({e x} : Set H) := by
  ext z
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg (⇑e) h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h'
  · intro h
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h

private theorem card_centralizer_conj {G : Type*} [Group G] (g x : G) :
    Nat.card (centralizer ({g * x * g⁻¹} : Set G)) = Nat.card (centralizer ({x} : Set G)) := by
  have h := map_centralizer_equiv (MulAut.conj g) x
  rw [MulAut.conj_apply] at h
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem mem_invClassSet_map_iff {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (x : G) (d : H) : d ∈ invClassSet (e x) ↔ e.symm d ∈ invClassSet x := by
  simp only [invClassSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hdC, hd2, hd1, hdconj⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← map_centralizer_equiv e x] at hdC
      exact (Subgroup.mem_map_equiv).mp hdC
    · have h := congrArg (⇑e.symm) hd2
      simpa only [map_pow, map_one] using h
    · intro h
      exact hd1 (by simpa only [map_one, MulEquiv.apply_symm_apply] using congrArg (⇑e) h)
    · rw [← MulEquiv.symm_apply_apply e x]
      exact MonoidHom.map_isConj (e.symm : H →* G) hdconj
  · rintro ⟨hdC, hd2, hd1, hdconj⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← map_centralizer_equiv e x]
      exact (Subgroup.mem_map_equiv).mpr hdC
    · have h := congrArg (⇑e) hd2
      simpa only [map_pow, map_one, MulEquiv.apply_symm_apply] using h
    · intro h
      exact hd1 (by simpa only [map_one] using congrArg (⇑e.symm) h)
    · rw [← MulEquiv.apply_symm_apply e d]
      exact MonoidHom.map_isConj (e : G →* H) hdconj

private theorem invClassSet_map_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    invClassSet (e x) = e '' invClassSet x := by
  ext d
  rw [Set.mem_image]
  constructor
  · intro hd
    exact ⟨e.symm d, (mem_invClassSet_map_iff e x d).mp hd, by simp⟩
  · rintro ⟨c, hc, rfl⟩
    exact (mem_invClassSet_map_iff e x (e c)).mpr (by simpa using hc)

private theorem ncard_invClassSet_map {G H : Type*} [Group G] [Group H] (e : G ≃* H) (x : G) :
    (invClassSet (e x)).ncard = (invClassSet x).ncard := by
  rw [invClassSet_map_eq e x, Set.ncard_image_of_injective _ e.injective]

private theorem ncard_invClassSet_conj {G : Type*} [Group G] (g x : G) :
    (invClassSet (g * x * g⁻¹)).ncard = (invClassSet x).ncard := by
  simpa only [MulAut.conj_apply] using ncard_invClassSet_map (MulAut.conj g) x

private theorem le_ncard_invClassSet_of_map {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (x : G) (h : 47 ≤ (invClassSet (e x)).ncard) : 47 ≤ (invClassSet x).ncard := by
  rwa [ncard_invClassSet_map e x] at h

private noncomputable def statedProjStatedSpEquivZModFive {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5) :
    StatedProj (StatedSp 2 K) ≃* StatedProj (StatedSp 2 (ZMod 5)) :=
  haveI := Fintype.ofFinite K
  let φ : K ≃+* ZMod 5 :=
    (ZMod.ringEquivOfPrime K Nat.prime_five (by rw [← Nat.card_eq_fintype_card, hK])).symm
  CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedSp φ 2)
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)

private theorem exists_conj_u2_and_card_K {K : Type} [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) {x : StatedProj (StatedSp 2 K)} (hx : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hC : Nat.card (centralizer ({x} : Set (StatedProj (StatedSp 2 K)))) = 480)
    {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hMC : M ≤ centralizer ({x} : Set (StatedProj (StatedSp 2 K))))
    (hMp : ⁅M, M⁆ = M) (hM : Nat.card M = 60) :
    (∃ g : StatedProj (StatedSp 2 K), g⁻¹ * x * g = u2 K) ∧ Nat.card K = 5 := by
  have horder : orderOf x = 2 := orderOf_eq_prime hx hx1
  obtain ⟨g, hg | hg⟩ := exists_conj_of_orderOf_eq_two hodd horder
  · have hCu1 : Nat.card (centralizer ({u1 K} : Set (StatedProj (StatedSp 2 K)))) = 480 := by
      have h := (card_centralizer_conj (g⁻¹) x).trans hC
      rwa [show g⁻¹ * x * (g⁻¹)⁻¹ = u1 K by simpa [inv_inv] using hg] at h
    exact absurd hCu1 (card_centralizer_u1_ne hodd)
  · have hCu2 : Nat.card (centralizer ({u2 K} : Set (StatedProj (StatedSp 2 K)))) = 480 := by
      have h := (card_centralizer_conj (g⁻¹) x).trans hC
      rwa [show g⁻¹ * x * (g⁻¹)⁻¹ = u2 K by simpa [inv_inv] using hg] at h
    have hfx : (MulAut.conj (g⁻¹)) x = u2 K := by
      rw [MulAut.conj_apply]
      simpa [inv_inv] using hg
    have hNC : M.map (MulAut.conj (g⁻¹)).toMonoidHom ≤
        centralizer ({u2 K} : Set (StatedProj (StatedSp 2 K))) := by
      rw [← hfx, ← map_centralizer_equiv (MulAut.conj (g⁻¹)) x]
      exact Subgroup.map_mono hMC
    have hNp : ⁅M.map (MulAut.conj (g⁻¹)).toMonoidHom,
        M.map (MulAut.conj (g⁻¹)).toMonoidHom⁆ = M.map (MulAut.conj (g⁻¹)).toMonoidHom := by
      rw [← Subgroup.map_commutator M M (MulAut.conj (g⁻¹)).toMonoidHom, hMp]
    have hN : Nat.card (M.map (MulAut.conj (g⁻¹)).toMonoidHom) = 60 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj (g⁻¹)).injective, hM]
    exact ⟨⟨g, hg⟩, card_K_eq_five_of_u2 hodd hCu2 hNC hNp hN⟩

private theorem psp_count_of_field {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    {x : StatedProj (StatedSp 2 K)} (hx : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hC : Nat.card (centralizer ({x} : Set (StatedProj (StatedSp 2 K)))) = 480)
    {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hMC : M ≤ centralizer ({x} : Set (StatedProj (StatedSp 2 K))))
    (hMp : ⁅M, M⁆ = M) (hM : Nat.card M = 60) :
    47 ≤ (invClassSet x).ncard := by
  obtain ⟨⟨g, hg⟩, hK5⟩ := exists_conj_u2_and_card_K hodd hx hx1 hC hMC hMp hM
  set ψ : StatedProj (StatedSp 2 K) ≃* StatedProj (StatedSp 2 (ZMod 5)) :=
    statedProjStatedSpEquivZModFive hK5 with hψ
  have hy : (ψ x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hy1 : ψ x ≠ 1 := by
    intro h
    exact hx1 (ψ.injective (by rw [h, map_one]))
  have hCy : Nat.card (centralizer ({(ψ x)} : Set (StatedProj (StatedSp 2 (ZMod 5))))) = 480 := by
    rw [← map_centralizer_equiv ψ x]
    exact (Nat.card_congr ((centralizer ({x} : Set (StatedProj (StatedSp 2 K)))).equivMapOfInjective
      ψ.toMonoidHom ψ.injective).toEquiv).symm.trans hC
  have hM5C : M.map ψ.toMonoidHom ≤
      centralizer ({(ψ x)} : Set (StatedProj (StatedSp 2 (ZMod 5)))) := by
    rw [← map_centralizer_equiv ψ x]
    exact Subgroup.map_mono hMC
  have hM5p : ⁅M.map ψ.toMonoidHom, M.map ψ.toMonoidHom⁆ = M.map ψ.toMonoidHom := by
    rw [← Subgroup.map_commutator M M ψ.toMonoidHom, hMp]
  have hM5 : Nat.card (M.map ψ.toMonoidHom) = 60 := by
    exact (Nat.card_congr (M.equivMapOfInjective ψ.toMonoidHom ψ.injective).toEquiv).symm.trans hM
  have hodd5 : Odd (Nat.card (ZMod 5)) := by
    rw [Nat.card_zmod]
    exact ⟨2, by norm_num⟩
  obtain ⟨⟨g5, hg5⟩, -⟩ :=
    exists_conj_u2_and_card_K hodd5 hy hy1 hCy hM5C hM5p hM5
  have hconj : (invClassSet (u2 (ZMod 5))).ncard = (invClassSet (ψ x)).ncard := by
    have h := ncard_invClassSet_conj g5 (u2 (ZMod 5))
    have hy_eq : g5 * u2 (ZMod 5) * g5⁻¹ = ψ x := by
      rw [← hg5]
      group
    rw [hy_eq] at h
    exact h.symm
  calc 47 ≤ (invClassSet (u2 (ZMod 5))).ncard := psp5_u2_count
    _ = (invClassSet (ψ x)).ncard := hconj
    _ = (invClassSet x).ncard := ncard_invClassSet_map ψ x

theorem psp_conj_count {X : Type} [Group X] [Finite X] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (hX : CFSG.Blueprint.LieModel X .PSp 2 p f) {x : X} (hx : x ^ 2 = 1)
    (hx1 : x ≠ 1) (hC : Nat.card (centralizer ({x} : Set X)) = 480) {M : Subgroup X}
    (hMC : M ≤ centralizer ({x} : Set X)) (hMp : ⁅M, M⁆ = M) (hM : Nat.card M = 60) :
    47 ≤ Set.ncard {c : X | c ∈ centralizer ({x} : Set X) ∧ c ^ 2 = 1 ∧ c ≠ 1 ∧ IsConj x c} := by
  change 47 ≤ (invClassSet x).ncard
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (G := X) (n := 2)
      (by norm_num) hX
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact (hp.odd_of_ne_two hp2).pow
  have hx' : (e x) ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hx'1 : e x ≠ 1 := by
    intro h
    exact hx1 (e.injective (by rw [h, map_one]))
  have hC' : Nat.card (centralizer ({(e x)} : Set (StatedProj (StatedSp 2 K)))) = 480 := by
    rw [← map_centralizer_equiv e x, Subgroup.card_map_of_injective e.injective, hC]
  have hM'C : M.map e.toMonoidHom ≤
      centralizer ({(e x)} : Set (StatedProj (StatedSp 2 K))) := by
    rw [← map_centralizer_equiv e x]
    exact Subgroup.map_mono hMC
  have hM'p : ⁅M.map e.toMonoidHom, M.map e.toMonoidHom⁆ = M.map e.toMonoidHom := by
    rw [← Subgroup.map_commutator M M e.toMonoidHom, hMp]
  have hM' : Nat.card (M.map e.toMonoidHom) = 60 := by
    rw [Subgroup.card_map_of_injective e.injective, hM]
  exact le_ncard_invClassSet_of_map e x (psp_count_of_field hodd hx' hx'1 hC' hM'C hM'p hM')

end CFSG.EvenSporadicStandard.HNRecog.Harada
