module

public import CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7.A5LinearRank
public import CFSG.LieType.SeitzGeneration.Defs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
public import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7

open CFSG.LieType.SeitzGeneration CFSG.Open

section Lift

theorem exists_lift_isElemAbelian_card {K L : Type*} [Group K] [Group L] [Finite K] {p : ℕ}
    (hp : p.Prime) (ρ : K →* L) (hρs : Function.Surjective ρ)
    (hker : Nat.Coprime (Nat.card ρ.ker) p) {Ē : Subgroup L} (hE : IsElemAbelian p Ē) :
    ∃ E₁ : Subgroup K, IsElemAbelian p E₁ ∧ Nat.card E₁ = Nat.card Ē := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let P : Subgroup K := Ē.comap ρ
  obtain ⟨Q⟩ : Nonempty (Sylow p P) := inferInstance
  let E₁ : Subgroup K := (Q : Subgroup P).map P.subtype
  have hE₁p : IsPGroup p E₁ := Q.isPGroup'.map P.subtype
  have hinj : ∀ x ∈ E₁, ρ x = 1 → x = 1 := by
    intro x hx h1
    have hxk : x ∈ ρ.ker := h1
    have hord : orderOf x ∣ Nat.card ρ.ker := by
      have h := orderOf_dvd_natCard (⟨x, hxk⟩ : ρ.ker)
      rwa [Subgroup.orderOf_mk] at h
    have hcop := hE₁p.orderOf_coprime hker.symm ⟨x, hx⟩
    rw [Subgroup.orderOf_mk] at hcop
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hord)
  have hmem : ∀ x ∈ E₁, ρ x ∈ Ē := by
    rintro x ⟨⟨y, hy⟩, -, rfl⟩
    exact hy
  let f : P →* Ē := (ρ.comp P.subtype).codRestrict Ē (fun y => y.2)
  have hfs : Function.Surjective f := by
    intro e
    obtain ⟨k, hk⟩ := hρs e
    exact ⟨⟨k, by simp [P, Subgroup.mem_comap, hk]⟩, Subtype.ext hk⟩
  have hĒp : IsPGroup p (⊤ : Subgroup Ē) := by
    intro x
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    simpa using hE.2 ((x : Ē) : L) (x : Ē).2
  have hQtop : (Q : Subgroup P).map f = ⊤ := by
    have h := (Q.mapSurjective hfs).is_maximal' hĒp le_top
    rw [Sylow.coe_mapSurjective] at h
    exact h.symm
  have himg : E₁.map ρ = Ē := by
    have h1 : E₁.map ρ = ((Q : Subgroup P).map f).map Ē.subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [h1, hQtop, Subgroup.map_top, Subgroup.range_subtype]
  have hcomm : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    intro x hx y hy
    have hxy : x * y * (y * x)⁻¹ ∈ E₁ :=
      E₁.mul_mem (E₁.mul_mem hx hy) (E₁.inv_mem (E₁.mul_mem hy hx))
    have h1 : ρ (x * y * (y * x)⁻¹) = 1 := by
      have := hE.1.is_comm.comm (⟨ρ x, hmem x hx⟩ : Ē) ⟨ρ y, hmem y hy⟩
      have h2 : ρ x * ρ y = ρ y * ρ x := congrArg Subtype.val this
      rw [map_mul, map_inv, map_mul, map_mul, h2, mul_inv_cancel]
    have := hinj _ hxy h1
    rwa [mul_inv_eq_one] at this
  have hexp : ∀ x ∈ E₁, x ^ p = 1 := by
    intro x hx
    have hxp : x ^ p ∈ E₁ := E₁.pow_mem hx p
    refine hinj _ hxp ?_
    rw [map_pow]
    exact hE.2 _ (hmem x hx) |>.trans rfl
  refine ⟨E₁, ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩, hexp⟩, ?_⟩
  have hinj' : Function.Injective (ρ.comp E₁.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h
    exact Subtype.ext (hinj x hx h)
  have hc : Nat.card E₁ = Nat.card (E₁.map ρ) := by
    have h := MonoidHom.range_comp ρ E₁.subtype
    rw [Subgroup.range_subtype] at h
    rw [← h]
    exact Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv
  rw [hc, himg]

end Lift

section Numerics

theorem not_dvd_of_dvd_phiSix {p q : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpq : p ∣ q ^ 2 - q + 1) :
    ¬ p ∣ q ^ 2 ∧ ¬ p ∣ q ^ 2 - 1 ∧ ¬ p ∣ (q ^ 2) ^ 2 - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hle : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
  have h0 : ((q : ZMod p)) ^ 2 - q + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).2 hpq
    rwa [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one] at this
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).1 (by exact_mod_cast h)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this)
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
  have hqsq : (q : ZMod p) ^ 2 ≠ 1 := by
    intro h
    have hq2 : (q : ZMod p) = 2 := by linear_combination h - h0
    rw [hq2] at h
    apply h3
    linear_combination h
  have hq3 : (q : ZMod p) ^ 3 + 1 = 0 := by linear_combination ((q : ZMod p) + 1) * h0
  have hq4 : ((q : ZMod p) ^ 2) ^ 2 ≠ 1 := by
    intro h
    apply hqsq
    have h6 : ((q : ZMod p) ^ 2) ^ 3 = 1 := by
      linear_combination ((q : ZMod p) ^ 3 - 1) * hq3
    have e : ((q : ZMod p) ^ 2) ^ 3 = (q : ZMod p) ^ 2 * ((q : ZMod p) ^ 2) ^ 2 := by ring
    rw [h, mul_one, h6] at e
    exact e.symm
  have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.2 fun h => hq0 (by simp [h])
  have key : ∀ n : ℕ, 1 ≤ n → (p ∣ n - 1 ↔ (n : ZMod p) = 1) := by
    intro n hn
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hn, Nat.cast_one, sub_eq_zero]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := (ZMod.natCast_eq_zero_iff _ p).2 h
    rw [Nat.cast_pow] at this
    exact hq0 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · rw [key _ (Nat.one_le_pow _ _ hqpos)]
    push_cast
    exact hqsq
  · rw [key _ (Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hqpos))]
    push_cast
    exact hq4

theorem ne_two_of_dvd_phiSix {p q : ℕ} (hpq : p ∣ q ^ 2 - q + 1) : p ≠ 2 := by
  rintro rfl
  have hle : q ≤ q ^ 2 := Nat.le_self_pow two_ne_zero q
  have h0 := (ZMod.natCast_eq_zero_iff _ 2).2 hpq
  rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one] at h0
  generalize (q : ZMod 2) = x at h0
  revert x
  decide

end Numerics

section Rank

theorem rankLE2_statedProj_of_det {K : Type} [Field K] [Finite K] {q p : ℕ}
    (hK : Nat.card K = q ^ 2) (hp : p.Prime) (hp3 : p ≠ 3) (hpq : p ∣ q ^ 2 - q + 1)
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin 6) K))
    (hdet : ∀ A ∈ H, (A : Matrix (Fin 6) (Fin 6) K).det = 1) :
    RankLE2 p (CFSG.Assembly.LowTwoRank.StatedProj H) := by
  classical
  obtain ⟨hpK, h1, h2⟩ := not_dvd_of_dvd_phiSix hp hp3 hpq
  rw [← hK] at hpK h1 h2
  have hp2 := ne_two_of_dvd_phiSix hpq
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Matrix.GeneralLinearGroup (Fin 6) K) := inferInstance
  intro F hF
  let ρ : H →* CFSG.Assembly.LowTwoRank.StatedProj H := QuotientGroup.mk' _
  have hρs : Function.Surjective ρ := QuotientGroup.mk'_surjective _
  have hkerexp : ∀ x : ρ.ker, (x : H) ^ 6 = 1 := by
    rintro ⟨x, hx⟩
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff x).1 hx)
    have hd := hdet (x : Matrix.GeneralLinearGroup (Fin 6) K) x.2
    have hc6 : c ^ 6 = 1 := by
      apply Units.ext
      have h3 := Matrix.GeneralLinearGroup.det_scalar (n := Fin 6) c
      have h4 := congrArg (fun u : Kˣ => (u : K)) h3
      simp only [Matrix.GeneralLinearGroup.val_det_apply, hc, Fintype.card_fin] at h4
      rw [hd] at h4
      simpa using h4.symm
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hc6, map_one]
    rfl
  have hcop : Nat.Coprime (Nat.card ρ.ker) p := by
    by_contra hnc
    have hdvd : p ∣ Nat.card ρ.ker := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp] at hnc
      exact not_not.1 hnc
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hx6 : x ^ 6 = 1 := Subtype.ext (hkerexp x)
    have : p ∣ 6 := hx ▸ orderOf_dvd_of_pow_eq_one hx6
    have h6 : p ∣ 2 * 3 := this
    rcases (Nat.Prime.dvd_mul hp).1 h6 with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
  obtain ⟨E₁, hE₁, hcard⟩ := exists_lift_isElemAbelian_card hp ρ hρs hcop hF
  rw [← hcard]
  have hcard' : Nat.card (E₁.map H.subtype) = Nat.card E₁ :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hc : ∀ g ∈ E₁.map H.subtype, ∀ h ∈ E₁.map H.subtype, g * h = h * g := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hE₁.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg (fun x : E₁ => ((x : H) : Matrix.GeneralLinearGroup (Fin 6) K)) this
  have he : ∀ g ∈ E₁.map H.subtype, g ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hE₁.2 a ha, map_one]
  have := card_le_pow_div_three_of_gl hp hpK h1 h2 (E₁.map H.subtype) hc he
  rw [hcard', Fintype.card_fin] at this
  simpa using this

theorem rankLE2_cat_twistedA_five {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 5 q).Valid) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpq : p ∣ q.card ^ 2 - q.card + 1) :
    RankLE2 p (Cat ⟨.twistedA 5 q, hv⟩) := by
  set ℓ := TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 5 q, hv⟩ with hℓ
  set f := TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 5 q, hv⟩ with hf
  have hU := CFSG.RankThree.PartTwo.Census.unitaryFieldData_galoisField ℓ f
    (TauCeti.ValidLieTypeIndex.fieldExponent_pos ⟨.twistedA 5 q, hv⟩)
  have : Fact ℓ.Prime := ⟨hU.prime⟩
  have hqcard : ℓ ^ f = q.card := by simp [hℓ, hf, TauCeti.ValidLieTypeIndex.characteristic,
    TauCeti.ValidLieTypeIndex.fieldExponent, TauCeti.PrimePower.card_def]
  have hfin := hU.finite
  have hK : Nat.card (GaloisField ℓ (2 * f)) = q.card ^ 2 := by
    rw [hU.card, ← hqcard, ← pow_mul, mul_comm]
  refine RankLE2.of_mulEquiv
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 5 q hv).symm ?_
  refine rankLE2_statedProj_of_det hK hp hp3 hpq _ fun A hA => ?_
  have hA' := hA
  clear hA
  unfold CFSG.Assembly.LowTwoRank.StatedSU at hA'
  induction hA' using Subgroup.closure_induction with
  | mem x hx => exact hx.1
  | one => simp
  | mul x y _ _ hx hy => simp [Matrix.det_mul, hx, hy]
  | inv x _ hx => simp [Matrix.coe_units_inv, Matrix.det_nonsing_inv, hx]

end Rank

end CFSG.HardMathSupport.Curtis.Coordinator.AnisoE7
