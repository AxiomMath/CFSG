module

public import CFSG.LocalAnalysis.ComponentClassification.GS82TheoremDDatum
public import CFSG.Quasithin.Recognition.GoldschmidtF112RAutJ2
public import CFSG.Quasithin.Recognition.HSTypeOutS5

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open CFSG.GorensteinWalter

theorem eq_three_or_five_of_dvd {p k : ℕ} (hp : p.Prime) (hmod : p ^ k % 8 = 3 ∨ p ^ k % 8 = 5)
    (hdvd : p ^ k * ((p ^ k) ^ 2 - 1) ∣ 20158709760) : p ^ k = 3 ∨ p ^ k = 5 := by
  have hk : k ≠ 0 := by
    rintro rfl
    simp at hmod
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk
  have hq : p ^ k ∣ 20158709760 := (Nat.dvd_mul_right _ _).trans hdvd
  have hpN : p ∣ 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 := by
    have := (dvd_pow_self p hk).trans hq
    norm_num at this ⊢
    exact this
  have hp' : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 31 := by
    rcases (Nat.Prime.dvd_mul hp).mp hpN with h | h
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
        · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
          · exact Or.inr (Or.inl
              ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h)))
        · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl
          ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))))
  rcases hp' with rfl | rfl | rfl | rfl | rfl
  · exfalso
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [pow_succ] at hmod
    omega
  · have hk4 : k ≤ 4 := by
      by_contra hlt
      have h5 : 3 ^ 5 ∣ 20158709760 := (pow_dvd_pow 3 (by omega)).trans hq
      norm_num at h5
    interval_cases k <;> revert hmod hdvd <;> norm_num
  · have hk1' : k ≤ 1 := by
      by_contra hlt
      have h5 : 5 ^ 2 ∣ 20158709760 := (pow_dvd_pow 5 (by omega)).trans hq
      norm_num at h5
    interval_cases k <;> revert hmod hdvd <;> norm_num
  · have hk2 : k ≤ 2 := by
      by_contra hlt
      have h5 : 7 ^ 3 ∣ 20158709760 := (pow_dvd_pow 7 (by omega)).trans hq
      norm_num at h5
    interval_cases k <;> revert hmod hdvd <;> norm_num
  · have hk1' : k ≤ 1 := by
      by_contra hlt
      have h5 : 31 ^ 2 ∣ 20158709760 := (pow_dvd_pow 31 (by omega)).trans hq
      norm_num at h5
    interval_cases k <;> revert hmod hdvd <;> norm_num

theorem nonempty_mulEquiv_perm_four_of_pgl2 {L K : Type} [Group L] [Field K] [Finite K]
    (e : L ≃* PGL2 K) (hK : Nat.card K = 3) : Nonempty (L ≃* Equiv.Perm (Fin 4)) := by
  have : Fintype K := Fintype.ofFinite K
  let eK : ZMod 3 ≃+* K :=
    ZMod.ringEquivOfPrime K Nat.prime_three (by simpa [Nat.card_eq_fintype_card] using hK)
  exact ⟨e.trans ((pgl2RingEquiv eK).symm.trans pgl2_three_equiv_perm)⟩

private theorem eq_bot_of_normal_isPGroup_of_alt5 {H : Type*} [Group H]
    (eA : H ≃* alternatingGroup (Fin 5)) {P : Subgroup H} (hPn : P.Normal) (hP2 : IsPGroup 2 P) :
    P = ⊥ := by
  have hmapn : (P.map eA.toMonoidHom).Normal := hPn.map _ eA.surjective
  have hmap2 : IsPGroup 2 (P.map eA.toMonoidHom) := hP2.map _
  rcases hmapn.eq_bot_or_eq_top with h | h
  · exact (Subgroup.map_eq_bot_iff_of_injective _ eA.injective).mp h
  · exfalso
    rw [h] at hmap2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hmap2
    rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin] at hn
    norm_num [Nat.factorial] at hn
    have h6 : n < 6 := by
      by_contra hge
      have : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases n <;> omega

theorem nonempty_mulEquiv_perm_five_of_pgl2 {L K : Type} [Group L] [Finite L] [Field K]
    [Finite K] (e : L ≃* PGL2 K) (hK : Nat.card K = 5) : Nonempty (L ≃* Equiv.Perm (Fin 5)) := by
  have hKodd : IsOddPrimePower (Nat.card K) := ⟨5, 1, Nat.prime_five, ⟨2, rfl⟩, le_rfl, by
    rw [hK, pow_one]⟩
  have hcard : Nat.card L = 120 := by
    rw [Nat.card_congr e.toEquiv, pgl2_card_formula, hK]
    norm_num
  obtain ⟨eN⟩ := commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three K hKodd (by omega) e
  have : Fintype K := Fintype.ofFinite K
  let eK : ZMod 5 ≃+* K :=
    ZMod.ringEquivOfPrime K Nat.prime_five (by simpa [Nat.card_eq_fintype_card] using hK)
  obtain ⟨eA⟩ := CFSG.ComponentClassification.GS82PumpInputs.TheoremD.nonempty_psl_two_five_equiv
  let eNA : commutator L ≃* alternatingGroup (Fin 5) :=
    eN.trans ((psl2RingEquiv eK).symm.trans eA)
  refine CFSG.Quasithin.F112R.nonempty_perm_five_of_normal_alt5 hcard (commutator L) eNA ?_
  intro C hCn hC2
  have hCN : C ⊓ commutator L = ⊥ := by
    have h1 : C.subgroupOf (commutator L) = ⊥ :=
      eq_bot_of_normal_isPGroup_of_alt5 eNA (hCn.subgroupOf _) (hC2.comap_subtype)
    rw [← Subgroup.subgroupOf_map_subtype, h1, Subgroup.map_bot]
  have hcent : ∀ c ∈ C, c = 1 := by
    intro c hc
    have hc' : c ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hmem : g * c * g⁻¹ * c⁻¹ ∈ C ⊓ commutator L := by
        refine ⟨C.mul_mem (hCn.conj_mem c hc g) (C.inv_mem hc), ?_⟩
        have := Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top c)
        rw [commutatorElement_def] at this
        exact this
      rw [hCN, Subgroup.mem_bot] at hmem
      calc g * c = g * c * g⁻¹ * c⁻¹ * (c * g) := by group
        _ = c * g := by rw [hmem, one_mul]
    have hec : e c ∈ Subgroup.center (PGL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨x, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc' x]
    rw [pgl2_center_eq_bot, Subgroup.mem_bot] at hec
    exact e.injective (hec.trans (map_one e).symm)
  exact (Subgroup.eq_bot_iff_forall C).mpr hcent

theorem exists_inner_of_mulEquiv_perm {L : Type*} [Group L] {n : ℕ} (hn : n = 4 ∨ n = 5)
    (e : L ≃* Equiv.Perm (Fin n)) (α : MulAut L) : ∃ l : L, ∀ x : L, α x = l * x * l⁻¹ := by
  have key : ∃ ρ : Equiv.Perm (Fin n), ∀ σ, (e.symm.trans (α.trans e)) σ = ρ * σ * ρ⁻¹ := by
    rcases hn with rfl | rfl
    · exact CFSG.Quasithin.HSType.perm_four_aut_inner _
    · exact CFSG.Quasithin.HSType.perm_five_aut_inner _
  obtain ⟨ρ, hρ⟩ := key
  refine ⟨e.symm ρ, fun x => e.injective ?_⟩
  have := hρ (e x)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at this
  rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem eq_top_of_normal_of_odd_index {Y : Type*} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥) {L : Subgroup Y} [L.Normal] (hLi : Odd L.index)
    (hZ : Subgroup.center L = ⊥) (haut : ∀ α : MulAut L, ∃ l : L, ∀ x : L, α x = l * x * l⁻¹) :
    L = ⊤ := by
  set C := Subgroup.centralizer (L : Set Y) with hCdef
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hCL : C ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro c ⟨hcC, hcL⟩
    have hz : (⟨c, hcL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro x
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hcC x x.2
    rw [hZ, Subgroup.mem_bot] at hz
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hz)
  have hCodd : Odd (Nat.card C) := by
    let f : C →* Y ⧸ L := (QuotientGroup.mk' L).comp C.subtype
    have hf : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro c hc
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hc
      have : (c : Y) ∈ C ⊓ L := ⟨c.2, hc⟩
      rw [hCL, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (Subtype.ext this)
    have hdvd : Nat.card C ∣ L.index := by
      rw [Subgroup.index, Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    exact hLi.of_dvd_nat hdvd
  have hCbot : C = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact le_sSup ⟨hCn, Nat.coprime_two_left.mpr hCodd⟩
  rw [eq_top_iff]
  intro y _
  obtain ⟨l, hl⟩ := haut (MulAut.conjNormal y)
  have hly : (l : Y)⁻¹ * y ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have := congrArg Subtype.val (hl ⟨x, hx⟩)
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
    calc x * ((l : Y)⁻¹ * y) = (l : Y)⁻¹ * ((l : Y) * x * (l : Y)⁻¹) * y := by group
      _ = (l : Y)⁻¹ * (y * x * y⁻¹) * y := by rw [this]
      _ = (l : Y)⁻¹ * y * x := by group
  rw [hCbot, Subgroup.mem_bot, inv_mul_eq_one] at hly
  rw [← hly]
  exact l.2

end CFSG.CGT.Foote81L6.Normalizer
