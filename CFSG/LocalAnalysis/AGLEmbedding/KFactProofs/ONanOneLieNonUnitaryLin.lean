module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanOneLieNonUnitaryPLe
public import CFSG.LocalAnalysis.AGLEmbedding.GenericTargetFacts
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelSolvable
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields

public section

namespace CFSG.AGLEmbedding.KFactProofs.NonUnitary

open CFSG.AGLEmbedding CFSG.PSL2Table CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

section Squares

variable {F : Type} [Field F]

theorem eq_top_of_mul_sq_stable' (h2 : (2 : F) ≠ 0) (W : AddSubgroup F)
    (hW : ∃ w ∈ W, w ≠ 0) (hsq : ∀ μ : Fˣ, ∀ a ∈ W, (μ : F) ^ 2 * a ∈ W) : W = ⊤ := by
  obtain ⟨w, hw, hw0⟩ := hW
  have hsq' : ∀ u : F, u ^ 2 * w ∈ W := by
    intro u
    by_cases hu : u = 0
    · rw [hu]; simp
    · simpa using hsq (Units.mk0 u hu) w hw
  rw [eq_top_iff]
  intro x _
  set y : F := x / w with hy
  have h4 : (2 : F) * 2 ≠ 0 := mul_ne_zero h2 h2
  have hxy : x = ((y + 1) / 2) ^ 2 * w - ((y - 1) / 2) ^ 2 * w := by
    have : ((y + 1) / 2) ^ 2 - ((y - 1) / 2) ^ 2 = y := by
      field_simp
      ring
    rw [← sub_mul, this, hy, div_mul_cancel₀ _ hw0]
  rw [hxy]
  exact W.sub_mem (hsq' _) (hsq' _)

end Squares

section Lin

variable {p n : ℕ} [Fact p.Prime]

theorem psl2GF_invariant' (hp2 : p ≠ 2) (hn : 1 ≤ n) (U : Sylow p (PSL2GF p n))
    (V : Subgroup (PSL2GF p n)) (hVU : V ≤ (U : Subgroup (PSL2GF p n))) (hV : V ≠ ⊥)
    (hVN : Subgroup.normalizer ((U : Subgroup (PSL2GF p n)) : Set (PSL2GF p n)) ≤
      Subgroup.normalizer (V : Set (PSL2GF p n))) : V = (U : Subgroup (PSL2GF p n)) := by
  have hF : ringChar (GaloisField p n) ≠ 2 := by rw [ringChar.eq (GaloisField p n) p]; exact hp2
  obtain ⟨ψ, hψ, hψU, hψc⟩ := exists_torus_action hp2 hn U
  let W : AddSubgroup (GaloisField p n) :=
    { carrier := {a | ψ (Multiplicative.ofAdd a) ∈ V}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        have : ψ (Multiplicative.ofAdd (a + b)) =
            ψ (Multiplicative.ofAdd a) * ψ (Multiplicative.ofAdd b) := by
          rw [ofAdd_add, map_mul]
        show ψ (Multiplicative.ofAdd (a + b)) ∈ V
        rw [this]
        exact V.mul_mem ha hb
      neg_mem' := fun {a} ha => by
        have : ψ (Multiplicative.ofAdd (-a)) = (ψ (Multiplicative.ofAdd a))⁻¹ := by
          rw [ofAdd_neg, map_inv]
        show ψ (Multiplicative.ofAdd (-a)) ∈ V
        rw [this]
        exact V.inv_mem ha }
  have hW : ∃ w ∈ W, w ≠ 0 := by
    obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hV
    have hvU : v ∈ ψ.range := by
      rw [hψU]
      exact hVU hv
    obtain ⟨m, hm⟩ := hvU
    refine ⟨Multiplicative.toAdd m, ?_, fun h0 => hv1 (Subtype.ext ?_)⟩
    · show ψ (Multiplicative.ofAdd (Multiplicative.toAdd m)) ∈ V
      rw [ofAdd_toAdd, hm]
      exact hv
    · show v = 1
      rw [← hm]
      have : m = 1 := by
        apply Multiplicative.toAdd.injective
        simpa using h0
      rw [this, map_one]
  have hsq : ∀ μ : (GaloisField p n)ˣ, ∀ a ∈ W, (μ : GaloisField p n) ^ 2 * a ∈ W := by
    intro μ a ha
    obtain ⟨c, hcN, hc⟩ := hψc μ
    have h1 := (Subgroup.mem_normalizer_iff.1 (hVN hcN) _).1 ha
    have h2 := hc (Multiplicative.ofAdd a)
    rw [toAdd_ofAdd] at h2
    show ψ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * a)) ∈ V
    rw [← h2]
    exact h1
  have hWtop : W = ⊤ := eq_top_of_mul_sq_stable' (Ring.two_ne_zero hF) W hW hsq
  refine le_antisymm hVU fun u hu => ?_
  have hu' : u ∈ ψ.range := by
    rw [hψU]
    exact hu
  obtain ⟨m, rfl⟩ := hu'
  have : Multiplicative.toAdd m ∈ W := by
    rw [hWtop]
    trivial
  have h3 : ψ (Multiplicative.ofAdd (Multiplicative.toAdd m)) ∈ V := this
  rwa [ofAdd_toAdd] at h3

theorem psl2GF_torus' (hp2 : p ≠ 2) (hn : 2 ≤ n) (U : Sylow p (PSL2GF p n)) :
    ∃ T₀ : Subgroup (PSL2GF p n), T₀ ≤ Subgroup.normalizer ((U : Subgroup (PSL2GF p n)) :
      Set (PSL2GF p n)) ∧ p.Coprime (Nat.card T₀) ∧
      (U : Subgroup (PSL2GF p n)) ⊓ Subgroup.centralizer (T₀ : Set (PSL2GF p n)) = ⊥ := by
  have hp : p.Prime := Fact.out
  obtain ⟨ψ, hψ, hψU, hψc⟩ := exists_torus_action hp2 (by omega : 1 ≤ n) U
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p n)ˣ)
  obtain ⟨c, hcN, hc⟩ := hψc g
  set lam : GaloisField p n := (g : GaloisField p n) ^ 2 with hlam
  have hF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  have hlam1 : lam ≠ 1 := by
    intro h1
    have h2 : g ^ 2 = 1 := Units.ext (by simpa [hlam] using h1)
    have h3 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h4 : orderOf g = p ^ n - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
    rw [h4] at h3
    have h5 := Nat.le_of_dvd (by norm_num) h3
    have h6 : 2 ≤ p := hp.two_le
    have h7 : 3 ≤ p := by omega
    have h8 : 3 ^ 2 ≤ p ^ n := (Nat.pow_le_pow_left h7 n).trans' (Nat.pow_le_pow_right (by norm_num)
      hn)
    omega
  have hpow : ∀ (k : ℕ) (a : Multiplicative (GaloisField p n)),
      c ^ k * ψ a * (c ^ k)⁻¹ = ψ (Multiplicative.ofAdd (lam ^ k * Multiplicative.toAdd a)) := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      have h1 : c ^ (k + 1) * ψ a * (c ^ (k + 1))⁻¹ = c * (c ^ k * ψ a * (c ^ k)⁻¹) * c⁻¹ := by
        group
      rw [h1, ih, hc, toAdd_ofAdd, pow_succ', mul_assoc]
  obtain ⟨e, m', hm', hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' p hp.ne_one
  refine ⟨Subgroup.zpowers (c ^ p ^ e), ?_, ?_, ?_⟩
  · exact Subgroup.zpowers_le.2 (Subgroup.pow_mem _ hcN _)
  · rw [Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero e hp.ne_zero) ⟨m', hord⟩, hord,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos e)]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm'
  · rw [eq_bot_iff]
    rintro x ⟨hxU, hxC⟩
    have hxψ : x ∈ ψ.range := by
      rw [hψU]
      exact hxU
    obtain ⟨m, rfl⟩ := hxψ
    have hcomm := Subgroup.mem_centralizer_iff.1 hxC (c ^ p ^ e) (Subgroup.mem_zpowers _)
    have h1 : ψ (Multiplicative.ofAdd (lam ^ p ^ e * Multiplicative.toAdd m)) = ψ m := by
      rw [← hpow, hcomm]
      group
    have h2 := congrArg Multiplicative.toAdd (hψ h1)
    rw [toAdd_ofAdd] at h2
    by_cases hm0 : Multiplicative.toAdd m = 0
    · have : m = 1 := Multiplicative.toAdd.injective (by simpa using hm0)
      rw [this, map_one]
      exact Subgroup.one_mem _
    · exfalso
      have h3 : lam ^ p ^ e = 1 := by
        have := mul_right_cancel₀ hm0 (h2.trans (one_mul _).symm)
        exact this
      have h4 : (iterateFrobenius (GaloisField p n) p e) lam =
          (iterateFrobenius (GaloisField p n) p e) 1 := by
        rw [iterateFrobenius_def, iterateFrobenius_def, h3, one_pow]
      exact hlam1 (iterateFrobenius_inj (GaloisField p n) p e h4)

theorem center_psl2GF' (hn : 2 ≤ n) : Subgroup.center (PSL2GF p n) = ⊥ := by
  have hp : p.Prime := Fact.out
  have : IsSimpleGroup (PSL2GF p n) := isSimpleGroup_psl2GF_of_two_le hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSL2GF p n)) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : PSL2GF p n, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
    have : IsMulCommutative (PSL2GF p n) := ⟨⟨hcomm⟩⟩
    have hpr : (Nat.card (PSL2GF p n)).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    obtain ⟨U⟩ : Nonempty (Sylow p (PSL2GF p n)) := inferInstance
    have h1 : p ^ n ∣ Nat.card (PSL2GF p n) := by
      have := Subgroup.card_subgroup_dvd_card (U : Subgroup (PSL2GF p n))
      rwa [(psl2GF_sylow p n (by omega) U).2] at this
    rcases hpr.eq_one_or_self_of_dvd p ((dvd_pow_self p (by omega)).trans h1) with h2 | h2
    · exact hp.one_lt.ne' h2
    · have h3 := Nat.le_of_dvd hpr.pos h1
      rw [← h2] at h3
      have h4 := hp.two_le
      have h5 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos hn
      nlinarith

theorem pLe_psl2GF (hp2 : p ≠ 2) (hn : 1 ≤ n) (hZ : Subgroup.center (PSL2GF p n) = ⊥)
    (U : Sylow p (PSL2GF p n)) (Y : Subgroup (MulAut (PSL2GF p n))) (hY : IsPGroup p Y)
    (hYN : ∀ b ∈ Subgroup.normalizer ((U : Subgroup (PSL2GF p n)) : Set (PSL2GF p n)), ∀ α ∈ Y,
      MulAut.conj b * α * (MulAut.conj b)⁻¹ ∈ Y) :
    ∀ α ∈ Y, ∃ u ∈ (U : Subgroup (PSL2GF p n)), α = MulAut.conj u := by
  have hp : p.Prime := Fact.out
  have hF : ringChar (GaloisField p n) ≠ 2 := by rw [ringChar.eq (GaloisField p n) p]; exact hp2
  have h2 : (2 : GaloisField p n) ≠ 0 := Ring.two_ne_zero hF
  obtain ⟨ψ, hψ, hψU, hψc⟩ := exists_torus_action hp2 hn U
  have hmem : ∀ a, ψ a ∈ (U : Subgroup (PSL2GF p n)) := fun a => by
    rw [← hψU]; exact ⟨a, rfl⟩
  refine pLe_of_scalar_torus hp U hZ ψ hψ (fun a => ⟨hmem a, fun t ht => ?_⟩) ?_
    {y | ∃ μ : (GaloisField p n)ˣ, y = (μ : GaloisField p n) ^ 2} ?_ ?_ ?_ Y hY hYN
  · rw [← hψU] at ht
    obtain ⟨b, rfl⟩ := ht
    rw [← map_mul, ← map_mul, mul_comm]
  · intro f hf a
    have : f (ψ a) ∈ ψ.range := by
      rw [hψU]
      exact hf _ (hmem a)
    obtain ⟨b, hb⟩ := this
    exact ⟨b, hb.symm⟩
  · intro x
    refine ⟨((x + 1) / 2) ^ 2, ((x - 1) / 2) ^ 2, ?_, ?_, ?_⟩
    · by_cases hu : (x + 1) / 2 = 0
      · left; rw [hu]; simp
      · right; exact ⟨Units.mk0 _ hu, by simp⟩
    · by_cases hu : (x - 1) / 2 = 0
      · left; rw [hu]; simp
      · right; exact ⟨Units.mk0 _ hu, by simp⟩
    · field_simp
      ring
  · rintro _ ⟨μ, rfl⟩
    exact hψc μ
  · intro f hf
    refine kFactL2UnipotentCentralizer p n hp2 hn U f fun x hx => ?_
    rw [← hψU] at hx
    obtain ⟨b, rfl⟩ := hx
    exact hf b

theorem smallRankOneData_psl2GF' (hp2 : p ≠ 2) (hn : 2 ≤ n) (U : Sylow p (PSL2GF p n)) :
    SmallRankOneData p (PSL2GF p n) U := by
  have hp : p.Prime := Fact.out
  have hcard : Nat.card (U : Subgroup (PSL2GF p n)) = p ^ n :=
    (psl2GF_sylow p n (by omega) U).2
  have hZ := center_psl2GF' (p := p) hn
  exact
    { dvd := by rw [hcard]; exact dvd_pow_self p (by omega)
      ti := psl2GF_ti hp2 (by omega) U
      center := hZ
      maximal := psl2GF_borelCoatom p n hp2 (by omega) U
      solvable := isSolvable_normalizer_sylow_psl2GF hp2 (by omega) U
      inner := fun f hf => kFactL2UnipotentCentralizer p n hp2 (by omega) U f hf
      pLe := fun Y hY hYN => pLe_psl2GF hp2 (by omega) hZ U Y hY hYN
      outer := outer_solvable (GaloisField p n)
      torus := psl2GF_torus' hp2 hn U
      invariant := fun V hVU hV hVN => Or.inl (psl2GF_invariant' hp2 (by omega) U V hVU hV hVN) }

theorem smallRankOneData_of_isLinTwo {K : Type} [Group K] [Finite K] (hp2 : p ≠ 2)
    (hn : 2 ≤ n) {d : TauCeti.ValidLieTypeIndex} (hd : IsLinTwoIndex p n d)
    (hK : Nonempty (K ≃* CatGroup d)) (T : Sylow p K) : SmallRankOneData p K T := by
  obtain ⟨e₁⟩ := hK
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  let e : K ≃* PSL2GF p n := e₁.trans e₂
  have hfs : Function.Surjective (e : K →* PSL2GF p n) := e.surjective
  exact SmallRankOneData.of_equiv e (Sylow.coe_mapSurjective hfs T).symm
    (smallRankOneData_psl2GF' hp2 hn (T.mapSurjective hfs))

end Lin

end CFSG.AGLEmbedding.KFactProofs.NonUnitary
