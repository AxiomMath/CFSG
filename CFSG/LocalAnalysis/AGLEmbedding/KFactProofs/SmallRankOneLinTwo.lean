module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneData
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelSolvable
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoTorus
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLargeTorus
import CFSG.Dihedral.Glauberman.DicksonMaxStructure
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.PSL2Table CFSG.Glauberman.Dickson.MaxStructure
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

section Sylow

variable {p n : ℕ} [Fact p.Prime]

theorem exists_eq_map_conj_unipotent (hp2 : p ≠ 2) (hn : 1 ≤ n) (U : Sylow p (PSL2GF p n)) :
    ∃ g : PSL2GF p n, (U : Subgroup (PSL2GF p n)) =
      (unipotent (GaloisField p n)).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨U₀, hU₀⟩ := exists_sylow_eq_unipotent_psl2GF hp2 hn
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (PSL2GF p n) U₀ U
  refine ⟨g, ?_⟩
  rw [← hg]
  ext x
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map, hU₀]
  rfl

theorem psl2GF_ti (hp2 : p ≠ 2) (hn : 1 ≤ n) (U : Sylow p (PSL2GF p n)) :
    ∀ t ∈ (U : Subgroup (PSL2GF p n)), t ≠ 1 → ∀ g : PSL2GF p n,
      g * t * g⁻¹ ∈ (U : Subgroup (PSL2GF p n)) →
      g ∈ Subgroup.normalizer ((U : Subgroup (PSL2GF p n)) : Set (PSL2GF p n)) := by
  have hF : ringChar (GaloisField p n) ≠ 2 := by rw [ringChar.eq (GaloisField p n) p]; exact hp2
  obtain ⟨g₀, hg₀⟩ := exists_eq_map_conj_unipotent hp2 hn U
  intro t ht ht1 g hg
  rw [hg₀, mem_map_conj_iff] at ht hg
  rw [hg₀, normalizer_map_conj, normalizer_unipotent_eq_borel hF, mem_map_conj_iff]
  have hs1 : g₀⁻¹ * t * g₀ ≠ 1 := by
    intro h
    apply ht1
    have : t = g₀ * (g₀⁻¹ * t * g₀) * g₀⁻¹ := by group
    rw [this, h]
    group
  have key := (unipotent_TI hF _ ht hs1 (g₀⁻¹ * g * g₀)).1 (by
    have e : g₀⁻¹ * g * g₀ * (g₀⁻¹ * t * g₀) * (g₀⁻¹ * g * g₀)⁻¹ =
        g₀⁻¹ * (g * t * g⁻¹) * g₀ := by group
    rw [e]
    exact hg)
  exact key

theorem exists_torus_action (hp2 : p ≠ 2) (hn : 1 ≤ n) (U : Sylow p (PSL2GF p n)) :
    ∃ ψ : Multiplicative (GaloisField p n) →* PSL2GF p n, Function.Injective ψ ∧
      ψ.range = (U : Subgroup (PSL2GF p n)) ∧
      ∀ μ : (GaloisField p n)ˣ, ∃ c ∈ Subgroup.normalizer ((U : Subgroup (PSL2GF p n)) :
        Set (PSL2GF p n)), ∀ a : Multiplicative (GaloisField p n),
          c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 *
            Multiplicative.toAdd a)) := by
  have hcard : Nat.card (U : Subgroup (PSL2GF p n)) = p ^ n := (psl2GF_sylow p n hn U).2
  obtain ⟨ψ, hψ, hψU, hc⟩ := exists_torus_param_of_mulEquiv_psl2GF hp2 hn
    (K := (⊤ : Subgroup (PSL2GF p n))) Subgroup.topEquiv (U : Subgroup (PSL2GF p n)) le_top hcard
  refine ⟨ψ, hψ, hψU, fun μ => ?_⟩
  obtain ⟨c, -, hcψ⟩ := hc μ
  refine ⟨c, ?_, hcψ⟩
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have hx' : x ∈ ψ.range := by
    rw [hψU]
    exact hx
  obtain ⟨a, rfl⟩ := hx'
  rw [hcψ]
  change _ ∈ ((U : Subgroup (PSL2GF p n)) : Set (PSL2GF p n))
  rw [← hψU]
  exact ⟨_, rfl⟩

end Sylow

section Squares

variable {F : Type} [Field F] [Finite F]

def mulStabSubfield (W : AddSubgroup F) : Subfield F where
  carrier := {x | ∀ a ∈ W, x * a ∈ W}
  zero_mem' := by intro a ha; simp
  one_mem' := by intro a ha; simpa using ha
  add_mem' := by
    intro x y hx hy a ha
    rw [add_mul]
    exact W.add_mem (hx a ha) (hy a ha)
  neg_mem' := by
    intro x hx a ha
    rw [neg_mul]
    exact W.neg_mem (hx a ha)
  mul_mem' := by
    intro x y hx hy a ha
    rw [mul_assoc]
    exact hx _ (hy a ha)
  inv_mem' := by
    intro x hx a ha
    by_cases hx0 : x = 0
    · simp [hx0]
    · have : Fintype F := Fintype.ofFinite F
      have hpow : ∀ n : ℕ, ∀ b ∈ W, x ^ n * b ∈ W := by
        intro n
        induction n with
        | zero => intro b hb; simpa using hb
        | succ n ih =>
          intro b hb
          rw [pow_succ, mul_comm (x ^ n) x, mul_assoc]
          exact hx _ (ih b hb)
      have hc : 2 ≤ Fintype.card F := Fintype.one_lt_card
      have h1 : x⁻¹ = x ^ (Fintype.card F - 2) := by
        have h2 := FiniteField.pow_card_sub_one_eq_one x hx0
        have h3 : x * x ^ (Fintype.card F - 2) = 1 := by
          rw [← pow_succ', show Fintype.card F - 2 + 1 = Fintype.card F - 1 by omega, h2]
        exact inv_eq_of_mul_eq_one_right h3
      rw [h1]
      exact hpow _ a ha

end Squares

section Invariant

variable {p : ℕ} [Fact p.Prime]

theorem eq_top_of_mul_sq_stable (W : AddSubgroup (GaloisField p 2)) (hW : ∃ w ∈ W, w ≠ 0)
    (hsq : ∀ μ : (GaloisField p 2)ˣ, ∀ a ∈ W, (μ : GaloisField p 2) ^ 2 * a ∈ W) : W = ⊤ := by
  have hF : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hfd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 (GaloisField p 2) :=
    ⟨Fact.out, le_rfl, by simpa using hF⟩
  let H : Subgroup (GaloisField p 2)ˣ := (powMonoidHom 2 : (GaloisField p 2)ˣ →* _).range
  have hH : p ^ 1 - 1 < Nat.card H := by
    have hcardH : Nat.card H = (p ^ 2 - 1) / Nat.gcd (p ^ 2 - 1) 2 := by
      show Nat.card (powMonoidHom 2 : (GaloisField p 2)ˣ →* _).range = _
      rw [IsCyclic.card_powMonoidHom_range, Nat.card_units, hF]
    rw [hcardH, pow_one]
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have hg : Nat.gcd (p ^ 2 - 1) 2 ≤ 2 := Nat.gcd_le_right _ (by norm_num)
    rw [Nat.lt_div_iff_mul_lt' (Nat.gcd_dvd_left _ _)]
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    have e1 : (k + 1) ^ 2 - 1 = k * (k + 2) := by
      have : (k + 1) ^ 2 = k * (k + 2) + 1 := by ring
      omega
    rw [e1, show k + 1 - 1 = k by omega]
    rw [e1] at hg
    have hk : 1 ≤ k := by omega
    calc Nat.gcd (k * (k + 2)) 2 * k ≤ 2 * k := Nat.mul_le_mul_right k hg
      _ < k * (k + 2) := by nlinarith
  have hcl := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.closure_eq_top hfd hH
  have hM : mulStabSubfield W = ⊤ := by
    rw [eq_top_iff, ← hcl, Subfield.closure_le]
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨μ, rfl⟩ := hu
    intro a ha
    simpa [pow_two] using hsq μ a ha
  obtain ⟨w, hw, hw0⟩ := hW
  rw [eq_top_iff]
  intro x _
  have hx : x / w ∈ mulStabSubfield W := by
    rw [hM]
    trivial
  have := hx w hw
  rwa [div_mul_cancel₀ _ hw0] at this

theorem psl2GF_invariant (hp2 : p ≠ 2) (U : Sylow p (PSL2GF p 2))
    (V : Subgroup (PSL2GF p 2)) (hVU : V ≤ (U : Subgroup (PSL2GF p 2))) (hV : V ≠ ⊥)
    (hVN : Subgroup.normalizer ((U : Subgroup (PSL2GF p 2)) : Set (PSL2GF p 2)) ≤
      Subgroup.normalizer (V : Set (PSL2GF p 2))) : V = (U : Subgroup (PSL2GF p 2)) := by
  obtain ⟨ψ, hψ, hψU, hψc⟩ := exists_torus_action hp2 (by norm_num : 1 ≤ 2) U
  let W : AddSubgroup (GaloisField p 2) :=
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
  have hsq : ∀ μ : (GaloisField p 2)ˣ, ∀ a ∈ W, (μ : GaloisField p 2) ^ 2 * a ∈ W := by
    intro μ a ha
    obtain ⟨c, hcN, hc⟩ := hψc μ
    have h1 := (Subgroup.mem_normalizer_iff.1 (hVN hcN) _).1 ha
    have h2 := hc (Multiplicative.ofAdd a)
    rw [toAdd_ofAdd] at h2
    show ψ (Multiplicative.ofAdd ((μ : GaloisField p 2) ^ 2 * a)) ∈ V
    rw [← h2]
    exact h1
  have hWtop : W = ⊤ := eq_top_of_mul_sq_stable W hW hsq
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

theorem psl2GF_torus (hp2 : p ≠ 2) (U : Sylow p (PSL2GF p 2)) :
    ∃ T₀ : Subgroup (PSL2GF p 2), T₀ ≤ Subgroup.normalizer ((U : Subgroup (PSL2GF p 2)) :
      Set (PSL2GF p 2)) ∧ p.Coprime (Nat.card T₀) ∧
      (U : Subgroup (PSL2GF p 2)) ⊓ Subgroup.centralizer (T₀ : Set (PSL2GF p 2)) = ⊥ := by
  have hp : p.Prime := Fact.out
  obtain ⟨ψ, hψ, hψU, hψc⟩ := exists_torus_action hp2 (by norm_num : 1 ≤ 2) U
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  obtain ⟨c, hcN, hc⟩ := hψc g
  set lam : GaloisField p 2 := (g : GaloisField p 2) ^ 2 with hlam
  have hF : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hlam1 : lam ≠ 1 := by
    intro h1
    have h2 : g ^ 2 = 1 := Units.ext (by simpa [hlam] using h1)
    have h3 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have h4 : orderOf g = p ^ 2 - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
    rw [h4] at h3
    have h5 := Nat.le_of_dvd (by norm_num) h3
    have h6 : 2 ≤ p := hp.two_le
    have h7 : 3 ≤ p := by omega
    have h8 : 9 ≤ p ^ 2 := by nlinarith
    omega
  have hpow : ∀ (k : ℕ) (a : Multiplicative (GaloisField p 2)),
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
      have h4 : (iterateFrobenius (GaloisField p 2) p e) lam =
          (iterateFrobenius (GaloisField p 2) p e) 1 := by
        rw [iterateFrobenius_def, iterateFrobenius_def, h3, one_pow]
      exact hlam1 (iterateFrobenius_inj (GaloisField p 2) p e h4)

end Invariant

section Data

variable {p : ℕ} [Fact p.Prime]

theorem center_psl2GF_two : Subgroup.center (PSL2GF p 2) = ⊥ := by
  have hp : p.Prime := Fact.out
  have : IsSimpleGroup (PSL2GF p 2) := isSimpleGroup_psl2GF_of_two_le (p := p) (n := 2) le_rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (PSL2GF p 2)) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ a b : PSL2GF p 2, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm
    have : IsMulCommutative (PSL2GF p 2) := ⟨⟨hcomm⟩⟩
    have hpr : (Nat.card (PSL2GF p 2)).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    obtain ⟨U⟩ : Nonempty (Sylow p (PSL2GF p 2)) := inferInstance
    have h1 : p ^ 2 ∣ Nat.card (PSL2GF p 2) := by
      have := Subgroup.card_subgroup_dvd_card (U : Subgroup (PSL2GF p 2))
      rwa [(psl2GF_sylow p 2 (by norm_num) U).2] at this
    rcases hpr.eq_one_or_self_of_dvd p ((dvd_pow_self p two_ne_zero).trans h1) with h2 | h2
    · exact hp.one_lt.ne' h2
    · have h3 := Nat.le_of_dvd hpr.pos h1
      rw [← h2] at h3
      have h4 := hp.two_le
      nlinarith

theorem smallRankOneData_psl2GF (hp2 : p ≠ 2) (U : Sylow p (PSL2GF p 2)) :
    SmallRankOneData p (PSL2GF p 2) U := by
  have hp : p.Prime := Fact.out
  have hcard : Nat.card (U : Subgroup (PSL2GF p 2)) = p ^ 2 := (psl2GF_sylow p 2 (by norm_num) U).2
  have hZ := center_psl2GF_two (p := p)
  have hin : ∀ Y : Subgroup (MulAut (PSL2GF p 2)), IsPGroup p Y →
      Y ≤ (MulAut.conj : PSL2GF p 2 →* MulAut (PSL2GF p 2)).range := by
    refine pInner_of_card_dvd hp U hZ 2 (fun h => hp2 ?_) fun S hS => ?_
    · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h
    · rw [hcard]
      exact kFactL2AutPCard p 2 hp2 (by norm_num) S hS
  exact
    { dvd := by rw [hcard]; exact dvd_pow_self p two_ne_zero
      ti := psl2GF_ti hp2 (by norm_num) U
      center := hZ
      maximal := psl2GF_borelCoatom p 2 hp2 (by norm_num) U
      solvable := isSolvable_normalizer_sylow_psl2GF hp2 (by norm_num) U
      inner := fun f hf => kFactL2UnipotentCentralizer p 2 hp2 (by norm_num) U f hf
      pLe := fun Y hY hYN => pLe_of_pInner hp U hZ hin Y hY hYN
      outer := outer_solvable (GaloisField p 2)
      torus := psl2GF_torus hp2 U
      invariant := fun V hVU hV hVN => Or.inl (psl2GF_invariant hp2 U V hVU hV hVN) }

theorem smallRankOneData_of_isSmallLinTwo {K : Type} [Group K] [Finite K] (hp2 : p ≠ 2)
    (hK : IsSmallLinTwo p K) (T : Sylow p K) : SmallRankOneData p K T := by
  obtain ⟨d, hd, ⟨e₁⟩⟩ := hK
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  let e : K ≃* PSL2GF p 2 := e₁.trans e₂
  have hfs : Function.Surjective (e : K →* PSL2GF p 2) := e.surjective
  exact SmallRankOneData.of_equiv e (Sylow.coe_mapSurjective hfs T).symm
    (smallRankOneData_psl2GF hp2 (T.mapSurjective hfs))

end Data

end CFSG.AGLEmbedding
