module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5YDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step2
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5Step4

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

open CFSG.EvenSporadicStandard.HNRecog

private abbrev centY (S : Subgroup (Equiv.Perm (Fin 1408))) (t : Equiv.Perm (Fin 1408)) :
    Subgroup (Equiv.Perm (Fin 1408)) :=
  S ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))

private noncomputable abbrev centC (t : Equiv.Perm (Fin 1408)) :
    Subgroup (Equiv.Perm (Fin 1408)) :=
  pPrime ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408)))

private lemma zpowers_eq_one_or_self {G : Type*} [Group G] {t x : G} (ht : t * t = 1)
    (ht1 : t ≠ 1) (hx : x ∈ Subgroup.zpowers t) : x = 1 ∨ x = t := by
  haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  have ho2 : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht) ht1
  have hmod : (orderOf t : ℤ) = 2 := by rw [ho2]; norm_num
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← hk, ← zpow_mod_orderOf t k, hmod, h]
    simp
  · right
    rw [← hk, ← zpow_mod_orderOf t k, hmod, h]
    simp

private theorem exists_filtered_pair {t : Equiv.Perm (Fin 1408)}
    {O : Subgroup (Equiv.Perm (Fin 1408))} {s₁ s₂ : Equiv.Perm (Fin 1408)}
    {S : Subgroup (Equiv.Perm (Fin 1408))} (hC : CentFacts t O s₁ s₂) (hS : Good S t)
    (hSP : S ≤ pPrime) :
    ∃ o₁ ∈ O, ∃ o₂ ∈ O,
      s₁ * o₁ ∈ centY S t ∧ s₂ * o₂ ∈ centY S t ∧
      ((s₁ * o₁) * (s₁ * o₁) = 1 ∨ (s₁ * o₁) * (s₁ * o₁) = t) ∧
      ((s₂ * o₂) ^ 5 = 1 ∨ (s₂ * o₂) ^ 5 = t) ∧
      Nat.card ↥(centY S t) = 240 ∧
      (∀ w ∈ Subgroup.closure ({s₁ * o₁, s₂ * o₂} : Set (Equiv.Perm (Fin 1408))),
        w ∈ O → w = 1 ∨ w = t) ∧
      Subgroup.closure ({s₁ * o₁, s₂ * o₂} : Set (Equiv.Perm (Fin 1408))) ≤ centY S t := by
  have htY : t ∈ centY S t :=
    ⟨hS.mem, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hcomm : ∀ y ∈ centY S t, t * y = y * t := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp hy.2).symm
  obtain ⟨hYcard0, hnorm2⟩ := step2 hS.cover htY hcomm hS.ne
  have hYcard : Nat.card ↥(centY S t) = 240 := hYcard0
  have hYO_p : IsPGroup 2 ↥(centY S t ⊓ O) :=
    (IsPGroup.of_card (n := 7) (by rw [hC.card_O]; norm_num)).to_le inf_le_right
  have hnormYO : ∀ y ∈ centY S t, ∀ n ∈ centY S t ⊓ O, y * n * y⁻¹ ∈ centY S t ⊓ O := by
    intro y hy n hn
    refine ⟨(centY S t).mul_mem ((centY S t).mul_mem hy hn.1) ((centY S t).inv_mem hy), ?_⟩
    exact hC.norm_O y ⟨pPrime_le (hSP hy.1), hy.2⟩ n hn.2
  have hYO_le : centY S t ⊓ O ≤ Subgroup.zpowers t :=
    hnorm2 (centY S t ⊓ O) inf_le_left hnormYO hYO_p
  have hzw_le : Subgroup.zpowers t ≤ centY S t ⊓ O :=
    le_inf (Subgroup.zpowers_le.mpr htY) (Subgroup.zpowers_le.mpr hC.mem_O)
  have hYO_eq : centY S t ⊓ O = Subgroup.zpowers t := le_antisymm hYO_le hzw_le
  haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact hS.sq
  have hcard_zpw : Nat.card ↥(Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime ht2 hS.ne]
  have hcardYO : Nat.card ↥(centY S t ⊓ O) = 2 := by rw [hYO_eq, hcard_zpw]
  have hYC : centY S t ≤ centC t := le_inf (fun x hx => hSP hx.1) inf_le_right
  have hcard_le : Nat.card ↥(centC t) * Nat.card ↥(centY S t ⊓ O) ≤
      Nat.card ↥(centY S t) * Nat.card ↥O := by
    rw [hcardYO, hYcard, hC.card_O]
    calc Nat.card ↥(centC t) * 2 ≤ 15360 * 2 := Nat.mul_le_mul_right 2 hC.card_C
      _ = 240 * 128 := by norm_num
  obtain ⟨y₁, hy₁Y, o₁, ho₁O, hs₁⟩ :=
    exists_mul_of_card hYC hC.O_le hcard_le s₁ hC.s₁_mem
  obtain ⟨y₂, hy₂Y, o₂, ho₂O, hs₂⟩ :=
    exists_mul_of_card hYC hC.O_le hcard_le s₂ hC.s₂_mem
  have hmemY₁ : s₁ * o₁⁻¹ ∈ centY S t := by
    rw [show s₁ * o₁⁻¹ = y₁ by rw [hs₁]; group]
    exact hy₁Y
  have hmemY₂ : s₂ * o₂⁻¹ ∈ centY S t := by
    rw [show s₂ * o₂⁻¹ = y₂ by rw [hs₂]; group]
    exact hy₂Y
  have hs₁C : s₁ ∈ P1408 ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408))) :=
    ⟨pPrime_le hC.s₁_mem.1, hC.s₁_mem.2⟩
  have hs₂C : s₂ ∈ P1408 ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408))) :=
    ⟨pPrime_le hC.s₂_mem.1, hC.s₂_mem.2⟩
  have hsqO : (s₁ * o₁⁻¹) ^ 2 ∈ O :=
    pow_mem_of_coset (C := P1408 ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408))))
      hC.norm_O hs₁C (O.inv_mem ho₁O) rfl (by rw [pow_two]; exact hC.s₁_sq)
  have hpowO : (s₂ * o₂⁻¹) ^ 5 ∈ O :=
    pow_mem_of_coset (C := P1408 ⊓ Subgroup.centralizer ({t} : Set (Equiv.Perm (Fin 1408))))
      hC.norm_O hs₂C (O.inv_mem ho₂O) rfl hC.s₂_pow
  have hsq : (s₁ * o₁⁻¹) * (s₁ * o₁⁻¹) = 1 ∨ (s₁ * o₁⁻¹) * (s₁ * o₁⁻¹) = t := by
    have h : (s₁ * o₁⁻¹) ^ 2 ∈ Subgroup.zpowers t := by
      rw [← hYO_eq]
      exact ⟨(centY S t).pow_mem hmemY₁ 2, hsqO⟩
    rw [pow_two] at h
    exact zpowers_eq_one_or_self hS.sq hS.ne h
  have hpow : (s₂ * o₂⁻¹) ^ 5 = 1 ∨ (s₂ * o₂⁻¹) ^ 5 = t := by
    have h : (s₂ * o₂⁻¹) ^ 5 ∈ Subgroup.zpowers t := by
      rw [← hYO_eq]
      exact ⟨(centY S t).pow_mem hmemY₂ 5, hpowO⟩
    exact zpowers_eq_one_or_self hS.sq hS.ne h
  have hclY : Subgroup.closure ({s₁ * o₁⁻¹, s₂ * o₂⁻¹} :
      Set (Equiv.Perm (Fin 1408))) ≤ centY S t := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hmemY₁
    · exact hmemY₂
  have hclO : ∀ w ∈ Subgroup.closure ({s₁ * o₁⁻¹, s₂ * o₂⁻¹} :
      Set (Equiv.Perm (Fin 1408))), w ∈ O → w = 1 ∨ w = t := by
    intro w hw hwO
    have h : w ∈ Subgroup.zpowers t := by
      rw [← hYO_eq]
      exact ⟨hclY hw, hwO⟩
    exact zpowers_eq_one_or_self hS.sq hS.ne h
  exact ⟨o₁⁻¹, O.inv_mem ho₁O, o₂⁻¹, O.inv_mem ho₂O, hmemY₁, hmemY₂, hsq, hpow,
    hYcard, hclO, hclY⟩

theorem exists_conj_Yk (hF : YFacts) {S : Subgroup (Equiv.Perm (Fin 1408))}
    {t : Equiv.Perm (Fin 1408)} (hS : Good S t) (hSP : S ≤ pPrime)
    (ht : t = elemZ ∨ t = elemA * elemZ) :
    t = elemA * elemZ ∧ ∃ k < 2,
      ∃ c ∈ P1408 ⊓ Subgroup.centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408))),
        (S ⊓ Subgroup.centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408)))).map
          (MulAut.conj c).toMonoidHom = yK k := by
  rcases ht with hz | haz
  · subst t
    obtain ⟨o₁, ho₁, o₂, ho₂, _hy₁, _hy₂, hsq, hpow, _hcard, hclO, _hclY⟩ :=
      exists_filtered_pair hF.z hS hSP
    exfalso
    have hpz := hF.pairs_z
    simp only [PairsBad] at hpz
    obtain ⟨w, hwcl, hwO, hw1, hwt⟩ := hpz o₁ ho₁ o₂ ho₂ hsq hpow
    rcases hclO w hwcl hwO with h | h
    · exact hw1 h
    · exact hwt h
  · subst t
    obtain ⟨o₁, ho₁, o₂, ho₂, _hy₁, _hy₂, hsq, hpow, hcard, hclO, hclY⟩ :=
      exists_filtered_pair hF.az hS hSP
    have haz := hF.pairs_az
    simp only [PairsBadOrGood] at haz
    rcases haz o₁ ho₁ o₂ ho₂ hsq hpow with hbad | hgood
    · exfalso
      obtain ⟨w, hwcl, hwO, hw1, hwt⟩ := hbad
      rcases hclO w hwcl hwO with h | h
      · exact hw1 h
      · exact hwt h
    · obtain ⟨k, hk2, c, hc, hcy₁, hcy₂, hcardK⟩ := hgood
      let K : Subgroup (Equiv.Perm (Fin 1408)) :=
        Subgroup.closure ({elemW sOne * o₁, elemW sTwo * o₂} :
          Set (Equiv.Perm (Fin 1408)))
      have hKle : K ≤ centY S (elemA * elemZ) := hclY
      have hKY : K = centY S (elemA * elemZ) := by
        refine Subgroup.eq_of_le_of_card_ge hKle ?_
        rw [hcard]
        exact hcardK
      have hKmap_le : K.map (MulAut.conj c).toMonoidHom ≤ yK k := by
        rw [Subgroup.map_le_iff_le_comap]
        change Subgroup.closure ({elemW sOne * o₁, elemW sTwo * o₂} :
          Set (Equiv.Perm (Fin 1408))) ≤ (yK k).comap (MulAut.conj c).toMonoidHom
        rw [Subgroup.closure_le]
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · simpa [MulAut.conj_apply] using hcy₁
        · simpa [MulAut.conj_apply] using hcy₂
      have hKmap_card : Nat.card ↥(K.map (MulAut.conj c).toMonoidHom) = 240 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj c).injective, hKY, hcard]
      have hyKcard : Nat.card ↥(yK k) = 240 := by
        have hk01 : k = 0 ∨ k = 1 := by omega
        rcases hk01 with rfl | rfl
        · exact hF.card_y₀
        · exact hF.card_y₁
      have hKmap_eq : K.map (MulAut.conj c).toMonoidHom = yK k := by
        refine Subgroup.eq_of_le_of_card_ge hKmap_le ?_
        rw [hKmap_card, hyKcard]
      have hfin : centY S (elemA * elemZ) = S ⊓
          Subgroup.centralizer ({elemA * elemZ} : Set (Equiv.Perm (Fin 1408))) := rfl
      refine ⟨rfl, k, hk2, c, hc, ?_⟩
      rw [← hfin, ← hKY]
      exact hKmap_eq

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
