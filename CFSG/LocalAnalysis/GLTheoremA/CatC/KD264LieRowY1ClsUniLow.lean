module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsUniLowEmb
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsUni
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsLin
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1ClsUniModel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutUniCat

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.UniLow

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.GLTheoremA.KD264Lie.KU7
  CFSG.Open

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def Wgl {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) (z : Fin 4 → ZMod 3) :
    GL (Fin (8 + r)) K :=
  ⟨W β r z, W β r (-z), by rw [W_mul, add_neg_cancel, W_zero],
    by rw [W_mul, neg_add_cancel, W_zero]⟩

theorem Wgl_val {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) (z : Fin 4 → ZMod 3) :
    ((Wgl β r z : GL (Fin (8 + r)) K) : Matrix (Fin (8 + r)) (Fin (8 + r)) K) = W β r z := rfl

@[expose] def Φ {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) :
    Multiplicative (Fin 4 → ZMod 3) →* GL (Fin (8 + r)) K where
  toFun z := Wgl β r (Multiplicative.toAdd z)
  map_one' := Units.ext (W_zero β r)
  map_mul' x y := Units.ext (by
    change W β r (Multiplicative.toAdd (x * y)) =
      W β r (Multiplicative.toAdd x) * W β r (Multiplicative.toAdd y)
    rw [toAdd_mul, W_mul])

theorem Φ_mem {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ)
    (z : Multiplicative (Fin 4 → ZMod 3)) : Φ β r z ∈ StatedSU (8 + r) (p ^ f) K := by
  refine (KU7.mem_statedSU_iff h (8 + r) (Φ β r z)).mpr ⟨?_, ?_⟩
  · exact W_det β r (Multiplicative.toAdd z)
  · exact W_dagI β r (Multiplicative.toAdd z)

@[expose] def Ψ {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) :
    Multiplicative (Fin 4 → ZMod 3) →* ↥(StatedSU (8 + r) (p ^ f) K) :=
  (Φ β r).codRestrict (StatedSU (8 + r) (p ^ f) K) (fun z => Φ_mem β r z)

@[expose] def Θ {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) :
    Multiplicative (Fin 4 → ZMod 3) →* StatedProj (StatedSU (8 + r) (p ^ f) K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin (8 + r)) K).subgroupOf
    (StatedSU (8 + r) (p ^ f) K))).comp (Ψ β r)

theorem Θ_injective {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) :
    Function.Injective (Θ β r) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  unfold Θ at ha
  rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at ha
  unfold StatedScalars at ha
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp ha
  have hWs : W β r (Multiplicative.toAdd a) = (c : K) • (1 : Matrix (Fin (8 + r)) (Fin (8 + r)) K) := by
    have h1 := congrArg Units.val hc
    simp only [Matrix.GeneralLinearGroup.coe_scalar] at h1
    rw [show ((Ψ β r a : ↥(StatedSU (8 + r) (p ^ f) K)) : GL (Fin (8 + r)) K)
      = Wgl β r (Multiplicative.toAdd a) from rfl, Wgl_val] at h1
    rw [← h1, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hz := W_scalar β r (Multiplicative.toAdd a) (c : K) hWs
  exact toAdd_eq_zero.mp hz

theorem Θ_range_card [Finite K] {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) :
    Nat.card (Θ β r).range = 3 ^ 4 := by
  have hdom : Nat.card (Multiplicative (Fin 4 → ZMod 3)) = 3 ^ 4 := by
    rw [← Nat.card_congr Multiplicative.ofAdd]
    simp [Nat.card_pi, Nat.card_zmod]
  rw [← hdom]
  exact (Nat.card_congr (MonoidHom.ofInjective (Θ_injective β r)).toEquiv).symm

theorem Θ_range_isElemAbelian {h : UnitaryFieldData p f K} (β : BlockOrder3 h) (r : ℕ) :
    CFSG.Open.IsElemAbelian 3 (Θ β r).range := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · intro z hz
    obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hz
    have hy : y ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      have h3 : (3 : ZMod 3) = 0 := rfl
      funext i
      simp [Pi.smul_apply, nsmul_eq_mul, h3]
    rw [← map_pow, hy, map_one]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.UniLow

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.ComponentInitial LinearFlag Matrix

variable {K : Type} [Field K]

@[expose] def KD264Y1UniLowEightPos : Prop :=
  ∀ (ℓ f m : ℕ) [Fact ℓ.Prime], 0 < f → 3 ∣ ℓ ^ f - 1 → 8 ≤ m →
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU m (ℓ ^ f) (GaloisField ℓ (2 * f)))))

theorem KD264Y1UniLowEightPos_holds : KD264Y1UniLowEightPos := by
  intro ℓ f m _ hf hdiv hm
  obtain ⟨r, rfl⟩ : ∃ r, m = 8 + r := ⟨m - 8, by omega⟩
  have hℓ3 : ℓ ≠ 3 := by
    rintro rfl
    have h1 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
    have h2 : 1 ≤ 3 ^ f := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hK : Nat.card (GaloisField ℓ (2 * f)) = ℓ ^ (2 * f) :=
    GaloisField.card ℓ (2 * f) (by omega)
  let h : UnitaryFieldData ℓ f (GaloisField ℓ (2 * f)) := ⟨Fact.out, hf, hK⟩
  have h3 : (3 : GaloisField ℓ (2 * f)) ≠ 0 := three_ne_zero_of_charP ℓ hℓ3
  obtain ⟨β⟩ := UniLow.nonempty_blockOrder3 h h3
  exact le_pRank_of_elemAbelian_card (k := 4) (by norm_num) le_top
    (UniLow.Θ_range_isElemAbelian β r) (UniLow.Θ_range_card β r)

theorem KD264Y1ClsUni_core_pos (r : ℕ) (q : TauCeti.PrimePower) (ℓ f : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ = q.p) (hf : f = q.exponent) {S : Type} [Group S] [Finite S]
    (e : S ≃* StatedProj (StatedSU (r + 1) (ℓ ^ f) (GaloisField ℓ (2 * f))))
    (hr2 : 2 ≤ r) (hp3 : q.p ≠ 3) (hq3 : r = 2 → 3 ≤ q.card)
    (hk2 : ¬ k2Lie 3 (TauCeti.LieTypeIndex.twistedA r q))
    (hk3 : ¬ k3Lie (TauCeti.LieTypeIndex.twistedA r q))
    (hpR : CFSG.Open.pRank 3 (⊤ : Subgroup S) = 3) (hL : KD264Y1UniLowEightPos) :
    KD264Y1Fam (TauCeti.LieTypeIndex.twistedA r q) := by
  subst hℓ hf
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hqcard : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hpS : CFSG.Open.pRank 3
      (⊤ : Subgroup (StatedProj (StatedSU (r + 1) (q.p ^ q.exponent)
        (GaloisField q.p (2 * q.exponent))))) = 3 := by
    have h := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
    rw [← h]
    exact hpR
  set K : Type := GaloisField q.p (2 * q.exponent) with hKdef
  have hK : Nat.card K = q.p ^ (2 * q.exponent) :=
    GaloisField.card q.p (2 * q.exponent) (by have := q.exponent_pos; omega)
  have h3K : (3 : K) ≠ 0 := three_ne_zero_of_charP (K := K) q.p hp3
  have h3Q : ¬ 3 ∣ q.card := three_not_dvd_card_of_char_ne_three q hp3
  have hUF : UnitaryFieldData q.p q.exponent K := ⟨q.prime_p, q.exponent_pos, hK⟩
  rcases (show 3 ∣ q.card + 1 ∨ 3 ∣ q.card - 1 by omega) with hdiv | hdiv
  ·
    have hdivp : 3 ∣ q.p ^ q.exponent + 1 := by rw [← hqcard]; exact hdiv
    rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with hr3 | hr3 | hr3 | hr3
    · exfalso
      subst hr3
      rcases A2'_excluded q hdiv (hq3 rfl) with h | h
      · exact hk2 h
      · exact hk3 h
    · subst hr3
      exact Or.inr (Or.inl ⟨q, rfl, hdiv⟩)
    · exfalso
      have h4 := statedProj_pRank_ge_four_of_five' (m := r + 1) (by omega) q.p q.exponent hdivp
      omega
    · exfalso
      obtain ⟨E, hE, hc⟩ := exists_elemAbelian_card_81_unitary hUF hdivp (m := r + 1) (by omega)
      have h4 := le_pRank_of_elemAbelian_card (k := 4) (by norm_num) le_top hE hc
      omega
  ·
    have hnd : ¬ 3 ∣ q.p ^ q.exponent + 1 := by
      rw [← hqcard]
      omega
    have hq : ∀ c : K, c ^ 3 = 1 → c ^ (q.p ^ q.exponent + 1) = 1 → c = 1 := by
      intro c h3 hQ
      have hg := pow_gcd_eq_one.mpr ⟨h3, hQ⟩
      have hcop : Nat.gcd 3 (q.p ^ q.exponent + 1) = 1 :=
        (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd
      rwa [hcop, pow_one] at hg
    rcases (show r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ 7 ≤ r by omega) with
      hr3 | hr3 | hr3 | hr3 | hr3 | hr3
    · exfalso
      have := statedProj_pRank_le (K := K) (m := r + 1) h3K hq
      omega
    · exfalso
      have := statedProj_pRank_le (K := K) (m := r + 1) h3K hq
      omega
    · exfalso
      have := statedProj_pRank_le (K := K) (m := r + 1) h3K hq
      omega
    · subst hr3
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, hdiv⟩)))
    · subst hr3
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q, rfl, hdiv⟩)))))
    · exfalso
      have h8 := hL q.p q.exponent (r + 1) q.exponent_pos (by rw [← hqcard]; exact hdiv) (by omega)
      omega


theorem KD264Y1ClsUni_holds : KD264Y1ClsUni := by
  intro ⟨e, hv⟩ hfin hR hk2 hk3 hpR hA
  obtain ⟨r, q, hd⟩ := hA
  have hd' : e = TauCeti.LieTypeIndex.twistedA r q := hd
  subst hd'
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
    ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
  have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ = q.p :=
    TauCeti.LieTypeIndex.characteristic_twistedA r q
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩ =
      q.exponent := TauCeti.LieTypeIndex.fieldExponent_twistedA r q
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hp3 : q.p ≠ 3 := by
    intro hp3
    apply hR
    exact Or.inl ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedA r q, hv⟩,
      by simp [CFSG.Yardstones.Md0ec50421ce4.onLie, hp3], ⟨MulEquiv.refl _⟩⟩
  have hq3 : r = 2 → 3 ≤ q.card := fun h => hr.2 h
  exact KD264Y1ClsUni_core_pos r q _ _ hc hf
    (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj r q hv) hr.1 hp3 hq3 hk2 hk3 hpR KD264Y1UniLowEightPos_holds


end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
