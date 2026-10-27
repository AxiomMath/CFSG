module

public import CFSG.ClassicalInvolution.AschTight.S19GC3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.NDB.G2S

open scoped MatrixGroups
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.Blueprint.Chevalley

theorem two_ne_zero_of_neg_one_ne_one_sl2 {F : Type} [Field F] (h : (-1 : SL(2, F)) ≠ 1) :
    (2 : F) ≠ 0 := by
  intro h2
  apply h
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination -h2

theorem exists_rank_three_of_sl2_pair {K : Type} [Group K] {F₀ F : Type} [Field F₀] [Finite F₀]
    [Field F] [Finite F] (φ : SL(2, F₀) →* K) (hφ : Function.Injective φ)
    {R : Subgroup K} (hφR : φ.range = R)
    (ε : ↥(Subgroup.centralizer (R : Set K)) ≃* SL(2, F))
    {r : K} (hrR : r ∈ R) (hrc : ∀ y ∈ R, r * y = y * r) (hr2 : r * r = 1) (hr1 : r ≠ 1) :
    ∃ w w' : K, w * w = 1 ∧ w' * w' = 1 ∧ w ≠ 1 ∧ w' ≠ 1 ∧ w ≠ w' ∧ r * w = w * r ∧
      r * w' = w' * r ∧ w * w' = w' * w ∧ w ≠ r ∧ w' ≠ r ∧ w * w' ≠ r := by
  classical
  obtain ⟨c, hc⟩ : r ∈ φ.range := hφR ▸ hrR
  have hcc : c ∈ Subgroup.center SL(2, F₀) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply hφ
    rw [map_mul, map_mul, hc]
    exact (hrc (φ y) (hφR ▸ ⟨y, rfl⟩)).symm
  have hc1 : c ≠ 1 := fun h => hr1 (by rw [← hc, h, map_one])
  have hcneg : c = -1 := ((mem_center_sl2_iff c).mp hcc).resolve_left hc1
  have hφneg : φ (-1) = r := by rw [← hcneg, hc]
  have hF₀ : (2 : F₀) ≠ 0 := two_ne_zero_of_neg_one_ne_one_sl2 (hcneg ▸ hc1)
  have hrS : r ∈ Subgroup.centralizer (R : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hrc h hh).symm
  set rS : ↥(Subgroup.centralizer (R : Set K)) := ⟨r, hrS⟩ with hrSdef
  have hεc : ε rS ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨s, rfl⟩ := ε.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp s.2 r hrR).symm
  have hε1 : ε rS ≠ 1 := fun h => hr1 (by
    have := ε.injective (h.trans (map_one ε).symm)
    exact congrArg Subtype.val this)
  have hεneg : ε rS = -1 := ((mem_center_sl2_iff _).mp hεc).resolve_left hε1
  have hεsymm : ε.symm (-1) = rS := by rw [← hεneg]; exact ε.symm_apply_apply rS
  have hF : (2 : F) ≠ 0 := two_ne_zero_of_neg_one_ne_one_sl2 (hεneg ▸ hε1)
  have hodd₀ : Odd (Nat.card F₀) := by
    have : Fintype F₀ := Fintype.ofFinite F₀
    have hch : ringChar F₀ ≠ 2 := fun h => by
      have : CharP F₀ 2 := ringChar.of_eq h
      exact hF₀ (CharTwo.two_eq_zero)
    have := FiniteField.odd_card_of_char_ne_two hch
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr this
  have hodd₁ : Odd (Nat.card F) := by
    have : Fintype F := Fintype.ofFinite F
    have hch : ringChar F ≠ 2 := fun h => by
      have : CharP F 2 := ringChar.of_eq h
      exact hF (CharTwo.two_eq_zero)
    have := FiniteField.odd_card_of_char_ne_two hch
    rw [Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mpr this
  obtain ⟨a₀, b₀, hab₀⟩ := exists_sq_add_sq_eq_neg_one hodd₀
  obtain ⟨a₁, b₁, hab₁⟩ := exists_sq_add_sq_eq_neg_one hodd₁
  set a : K := φ quatI with ha
  set a' : K := φ (quatJ hab₀) with ha'
  set bS : ↥(Subgroup.centralizer (R : Set K)) := ε.symm quatI with hbS
  set bS' : ↥(Subgroup.centralizer (R : Set K)) := ε.symm (quatJ hab₁) with hbS'
  set b : K := (bS : K) with hb
  set b' : K := (bS' : K) with hb'
  have haR : a ∈ R := hφR ▸ ⟨_, rfl⟩
  have ha'R : a' ∈ R := hφR ▸ ⟨_, rfl⟩
  have hbC : b ∈ Subgroup.centralizer (R : Set K) := bS.2
  have hb'C : b' ∈ Subgroup.centralizer (R : Set K) := bS'.2
  have hrC : r ∈ Subgroup.centralizer (R : Set K) := hrS
  have hbc : ∀ h ∈ R, h * b = b * h := fun h hh => Subgroup.mem_centralizer_iff.mp hbC h hh
  have hb'c : ∀ h ∈ R, h * b' = b' * h := fun h hh => Subgroup.mem_centralizer_iff.mp hb'C h hh
  have haa : a * a = r := by rw [ha, ← map_mul, quatI_mul_self, hφneg]
  have ha'a' : a' * a' = r := by rw [ha', ← map_mul, quatJ_mul_self, hφneg]
  have haa' : a * a' = r * (a' * a) := by
    rw [ha, ha', ← map_mul, quatI_mul_quatJ, map_mul, map_mul, hφneg]
  have hbb : b * b = r := by
    have : bS * bS = rS := by rw [hbS, ← map_mul, quatI_mul_self, hεsymm]
    exact congrArg Subtype.val this
  have hb'b' : b' * b' = r := by
    have : bS' * bS' = rS := by rw [hbS', ← map_mul, quatJ_mul_self, hεsymm]
    exact congrArg Subtype.val this
  have hbb' : b * b' = r * (b' * b) := by
    have : bS * bS' = rS * (bS' * bS) := by
      rw [hbS, hbS', ← map_mul, quatI_mul_quatJ, map_mul, map_mul, hεsymm]
    exact congrArg Subtype.val this
  have hZ : ∀ x ∈ Subgroup.centralizer (R : Set K), ∀ h ∈ R, h * x = x * h :=
    fun x hx h hh => Subgroup.mem_centralizer_iff.mp hx h hh
  have hnc : a * a' ≠ a' * a := by
    intro h
    rw [h] at haa'
    exact hr1 (by simpa using haa'.symm)
  have hA : a ∈ Subgroup.centralizer (R : Set K) → False := fun hC => hnc (hZ a hC a' ha'R).symm
  have hA' : a' ∈ Subgroup.centralizer (R : Set K) → False := fun hC => hnc (hZ a' hC a haR)
  have hba : b * a = a * b := (hbc a haR).symm
  have hba' : b * a' = a' * b := (hbc a' ha'R).symm
  have hb'a : b' * a = a * b' := (hb'c a haR).symm
  have hb'a' : b' * a' = a' * b' := (hb'c a' ha'R).symm
  have hra : r * a = a * r := hrc a haR
  have hra' : r * a' = a' * r := hrc a' ha'R
  have hrb : r * b = b * r := hbc r hrR
  have hrb' : r * b' = b' * r := hb'c r hrR
  have hraa : r * (a' * a) = (a' * a) * r := hrc _ (R.mul_mem ha'R haR)
  have hbb'C : b * b' ∈ Subgroup.centralizer (R : Set K) := Subgroup.mul_mem _ hbC hb'C
  refine ⟨a * b, a' * b', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hba]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb, hr2]
  · calc a' * b' * (a' * b') = a' * (b' * a') * b' := by group
      _ = a' * (a' * b') * b' := by rw [hb'a']
      _ = (a' * a') * (b' * b') := by group
      _ = 1 := by rw [ha'a', hb'b', hr2]
  · intro h
    have : a = b⁻¹ := (inv_eq_of_mul_eq_one_left h).symm
    exact hA (this ▸ Subgroup.inv_mem _ hbC)
  · intro h
    have : a' = b'⁻¹ := (inv_eq_of_mul_eq_one_left h).symm
    exact hA' (this ▸ Subgroup.inv_mem _ hb'C)
  · intro h
    have h1 : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
        _ = b' * b⁻¹ := by group
    have hC : a'⁻¹ * a ∈ Subgroup.centralizer (R : Set K) := by
      rw [h1]
      exact Subgroup.mul_mem _ hb'C (Subgroup.inv_mem _ hbC)
    have h2 := hZ _ hC a haR
    have h3 : a * a'⁻¹ = a'⁻¹ * a := by
      have : a * a'⁻¹ * a = a'⁻¹ * a * a := by simpa [mul_assoc] using h2
      exact mul_right_cancel this
    have h4 : Commute a a' := by
      have : Commute a a'⁻¹ := h3
      simpa using this.inv_right
    exact hnc h4.eq
  · calc r * (a * b) = (r * a) * b := by group
      _ = (a * r) * b := by rw [hra]
      _ = a * (r * b) := by group
      _ = a * (b * r) := by rw [hrb]
      _ = a * b * r := by group
  · calc r * (a' * b') = (r * a') * b' := by group
      _ = (a' * r) * b' := by rw [hra']
      _ = a' * (r * b') := by group
      _ = a' * (b' * r) := by rw [hrb']
      _ = a' * b' * r := by group
  · have e1 : a * b * (a' * b') = (a * a') * (b * b') := by
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [hba']
        _ = (a * a') * (b * b') := by group
    have e2 : (r * (a' * a)) * (r * (b' * b)) = (a' * a) * (b' * b) := by
      calc (r * (a' * a)) * (r * (b' * b)) = r * ((a' * a) * r) * (b' * b) := by group
        _ = r * (r * (a' * a)) * (b' * b) := by rw [← hraa]
        _ = (r * r) * (a' * a) * (b' * b) := by group
        _ = (a' * a) * (b' * b) := by rw [hr2, one_mul]
    have e3 : a' * b' * (a * b) = (a' * a) * (b' * b) := by
      calc a' * b' * (a * b) = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [hb'a]
        _ = (a' * a) * (b' * b) := by group
    rw [e1, haa', hbb', e2, e3]
  · intro h
    have : a = r * b⁻¹ := by
      calc a = a * b * b⁻¹ := by group
        _ = r * b⁻¹ := by rw [h]
    exact hA (this ▸ Subgroup.mul_mem _ hrC (Subgroup.inv_mem _ hbC))
  · intro h
    have : a' = r * b'⁻¹ := by
      calc a' = a' * b' * b'⁻¹ := by group
        _ = r * b'⁻¹ := by rw [h]
    exact hA' (this ▸ Subgroup.mul_mem _ hrC (Subgroup.inv_mem _ hb'C))
  · intro h
    have h1 : a * a' = r * (b * b')⁻¹ := by
      calc a * a' = (a * a') * (b * b') * (b * b')⁻¹ := by group
        _ = a * b * (a' * b') * (b * b')⁻¹ := by
          calc (a * a') * (b * b') * (b * b')⁻¹ = a * (a' * b) * b' * (b * b')⁻¹ := by group
            _ = a * (b * a') * b' * (b * b')⁻¹ := by rw [hba']
            _ = a * b * (a' * b') * (b * b')⁻¹ := by group
        _ = r * (b * b')⁻¹ := by rw [h]
    have hC : a * a' ∈ Subgroup.centralizer (R : Set K) := by
      rw [h1]
      exact Subgroup.mul_mem _ hrC (Subgroup.inv_mem _ hbb'C)
    have h2 := hZ _ hC a haR
    have h3 : a * (a * a') = a * (a' * a) := by
      calc a * (a * a') = (a * a') * a := h2
        _ = a * (a' * a) := by group
    exact hnc (mul_left_cancel h3)

theorem exists_sl2_pair_g2 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    {R : Subgroup ↥(adjointGroup .G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2 (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e))) :
    ∃ (F₀ F : Type) (_ : Field F₀) (_ : Finite F₀) (_ : Field F) (_ : Finite F)
      (φ : SL(2, F₀) →* ↥(adjointGroup .G2 (GaloisField p e))), Function.Injective φ ∧
        φ.range = R ∧ Nonempty (↥(Subgroup.centralizer
          (R : Set ↥(adjointGroup .G2 (GaloisField p e)))) ≃* SL(2, F)) := by
  have hK2 : ringChar (GaloisField p e) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e) p]
    exact hp2
  obtain ⟨i, g, hRg⟩ := Disconnected.AschTight.S19F.exists_eq_conjSub_g2Chart hR
  obtain ⟨ε⟩ := Disconnected.AschTight.S19G.nonempty_centralizer_equiv_g2 hp2 he
    (MonoidHom.id _) Function.bijective_id hR
  have hid : R.map (MonoidHom.id ↥(adjointGroup .G2 (GaloisField p e))) = R := Subgroup.map_id R
  refine ⟨GaloisField p e, GaloisField p e, inferInstance, inferInstance, inferInstance,
    inferInstance, (MulAut.conj g).toMonoidHom.comp
      (Disconnected.AschTight.S19F.g2Chart (GaloisField p e) i), ?_, ?_,
    ⟨(MulEquiv.subgroupCongr (congrArg (fun S : Subgroup ↥(adjointGroup .G2 (GaloisField p e)) =>
      Subgroup.centralizer (S : Set ↥(adjointGroup .G2 (GaloisField p e)))) hid.symm)).trans
      ε⟩⟩
  · exact (MulAut.conj g).injective.comp
      (Disconnected.AschTight.S19F.g2Chart_injective hK2 i)
  · have h := MonoidHom.range_comp (MulAut.conj g).toMonoidHom
      (Disconnected.AschTight.S19F.g2Chart (GaloisField p e) i)
    refine h.trans ?_
    rw [hRg]
    rfl

theorem exists_sl2_pair_td4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e)
    {R : Subgroup ↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup
      (iterateFrobenius (GaloisField p (3 * e)) p e))}
    (hR : R ∈ fundamentalSubgroups .trialityD4 (CFSG.LieType.Steinberg.TwistedD4.twistedDatum
      (iterateFrobenius (GaloisField p (3 * e)) p e))) :
    ∃ (F₀ F : Type) (_ : Field F₀) (_ : Finite F₀) (_ : Field F) (_ : Finite F)
      (φ : SL(2, F₀) →* ↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup
        (iterateFrobenius (GaloisField p (3 * e)) p e))), Function.Injective φ ∧
        φ.range = R ∧ Nonempty (↥(Subgroup.centralizer (R : Set ↥(
          CFSG.LieType.Steinberg.TwistedD4.twistedGroup
            (iterateFrobenius (GaloisField p (3 * e)) p e)))) ≃* SL(2, F)) := by
  obtain ⟨hσ3, hK1, hC₀, hgF, -, -⟩ := Disconnected.AschTight.S19G.d4_model_data hp2 he
  obtain ⟨i, g₀, hRg⟩ := Asc77.exists_conj_rankOne_node_of_trialityD4 0 p e
    ⟨Fact.out, he, rfl⟩ hR
  obtain ⟨F, hF, hFfin, ⟨ε⟩⟩ := Disconnected.AschTight.S19G.nonempty_centralizer_equiv_d4 hp2 he
    (MonoidHom.id _) Function.bijective_id hR
  have hid : R.map (MonoidHom.id ↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup
      (iterateFrobenius (GaloisField p (3 * e)) p e))) = R := Subgroup.map_id R
  have ε' : ↥(Subgroup.centralizer (R : Set ↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup
      (iterateFrobenius (GaloisField p (3 * e)) p e)))) ≃* SL(2, F) :=
    (MulEquiv.subgroupCongr (congrArg (fun S : Subgroup ↥(
      CFSG.LieType.Steinberg.TwistedD4.twistedGroup
        (iterateFrobenius (GaloisField p (3 * e)) p e)) => Subgroup.centralizer
        (S : Set ↥(CFSG.LieType.Steinberg.TwistedD4.twistedGroup
          (iterateFrobenius (GaloisField p (3 * e)) p e)))) hid.symm)).trans ε
  have hR' : R = (CFSG.LieType.CurtisTits.rankOne (CFSG.LieType.Steinberg.TwistedD4.twistedRootGroup
      (iterateFrobenius (GaloisField p (3 * e)) p e)) i).map (MulAut.conj g₀).toMonoidHom := hRg
  have hi : (i : ℕ) < 2 := i.2
  rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h0 | h1
  · have hi' : i = CFSG.LieType.Steinberg.TwistedD4.ng 0 := Fin.ext h0
    subst hi'
    rw [ModelFacts.rankOne_long_eq_range hσ3] at hR'
    refine ⟨↥(CFSG.LieType.Steinberg.TwistedD4.fixedField
        (iterateFrobenius (GaloisField p (3 * e)) p e)), F, inferInstance,
      inferInstance, hF, Finite.of_fintype F,
      (MulAut.conj g₀).toMonoidHom.comp (CFSG.LieType.Steinberg.TwistedD4.slLong _ hσ3), ?_, ?_,
      ⟨ε'⟩⟩
    · exact (MulAut.conj g₀).injective.comp
        (CFSG.LieType.Steinberg.TwistedD4.slLong_injective hσ3)
    · exact (MonoidHom.range_comp (MulAut.conj g₀).toMonoidHom
        (CFSG.LieType.Steinberg.TwistedD4.slLong _ hσ3)).trans hR'.symm
  · have hi' : i = CFSG.LieType.Steinberg.TwistedD4.ng 1 := Fin.ext h1
    subst hi'
    rw [ModelFacts.rankOne_short_eq_range hσ3] at hR'
    refine ⟨GaloisField p (3 * e), F, inferInstance, inferInstance, hF, Finite.of_fintype F,
      (MulAut.conj g₀).toMonoidHom.comp (CFSG.LieType.Steinberg.TwistedD4.slShort _ hσ3), ?_, ?_,
      ⟨ε'⟩⟩
    · exact (MulAut.conj g₀).injective.comp
        (CFSG.LieType.Steinberg.TwistedD4.slShort_injective hσ3)
    · exact (MonoidHom.range_comp (MulAut.conj g₀).toMonoidHom
        (CFSG.LieType.Steinberg.TwistedD4.slShort _ hσ3)).trans hR'.symm

theorem exists_rank_three_model {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {t : StatedLieTag}
    {n e : ℕ} (hadm : StatedLieAdmissible t n p e) (ht : t = .G2 ∨ t = .trialityD4)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    {r : (modelUniv t n p e Fact.out).K} (hrR : r ∈ R) (hrc : ∀ y ∈ R, r * y = y * r)
    (hr2 : r * r = 1) (hr1 : r ≠ 1) :
    ∃ w w' : (modelUniv t n p e Fact.out).K, w * w = 1 ∧ w' * w' = 1 ∧ w ≠ 1 ∧ w' ≠ 1 ∧
      w ≠ w' ∧ r * w = w * r ∧ r * w' = w' * r ∧ w * w' = w' * w ∧ w ≠ r ∧ w' ≠ r ∧
        w * w' ≠ r := by
  have he : 1 ≤ e := hadm.2.1
  obtain ⟨F₀, F, _, _, _, _, φ, hφ, hφR, ⟨ε⟩⟩ : ∃ (F₀ F : Type) (_ : Field F₀) (_ : Finite F₀)
      (_ : Field F) (_ : Finite F) (φ : SL(2, F₀) →* (modelUniv t n p e Fact.out).K),
      Function.Injective φ ∧ φ.range = R ∧
        Nonempty (↥(Subgroup.centralizer (R : Set (modelUniv t n p e Fact.out).K)) ≃*
          SL(2, F)) := by
    rcases ht with rfl | rfl
    · obtain ⟨hk, -⟩ := hadm.2.2
      subst hk
      exact exists_sl2_pair_g2 hp2 he hR
    · have hk : n = 0 := hadm.2.2
      subst hk
      exact exists_sl2_pair_td4 hp2 he hR
  exact exists_rank_three_of_sl2_pair φ hφ hφR ε hrR hrc hr2 hr1

end CFSG.ClassicalInvolution.NDB.G2S
