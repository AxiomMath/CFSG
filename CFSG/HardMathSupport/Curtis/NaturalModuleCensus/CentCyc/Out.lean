module

public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
import CFSG.RankThree.PartOne.K1214.Basic
import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OddOutPSL2
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsIICenter
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThree.PartOne.OutStructure CFSG.Assembly.LowTwoRank
open Subgroup

section Comparable

variable {G : Type} [Group G]

theorem comparable_of_outPChain' {p : ℕ} (J : Subgroup G) [Group.IsPerfect J]
    (h : OutPChain p (J ⧸ center J)) {P : Subgroup G} (hP : IsPGroup p P)
    (hPN : P ≤ normalizer (J : Set G)) {u v : G} (hu : u ∈ P) (hv : v ∈ P) :
    u ∈ zpowers v ⊔ (P ⊓ (J ⊔ centralizer (J : Set G))) ∨
      v ∈ zpowers u ⊔ (P ⊓ (J ⊔ centralizer (J : Set G))) := by
  obtain ⟨D, E, hID, hD2, hpE, hD4⟩ := h
  set ρ := actionOnQuot J with hρ
  have hρmem : ∀ {a : G} (ha : a ∈ normalizer (J : Set G)),
      ρ ⟨a, ha⟩ ∈ Inn (J ⧸ center J) ↔ a ∈ J ⊔ centralizer (J : Set G) :=
    fun ha => actionOnQuot_mem_inner_iff J ha
  have hpow : ∀ {a : G} (ha : a ∈ P), ∃ k : ℕ, a ^ (p ^ k) = 1 := fun {a} ha => by
    obtain ⟨k, hk⟩ := hP ⟨a, ha⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hρpow : ∀ {a : G} (ha : a ∈ P) (k : ℕ), a ^ (p ^ k) = 1 →
      (ρ ⟨a, hPN ha⟩) ^ (p ^ k) = 1 := fun {a} ha k hk => by
    rw [← map_pow]
    have : (⟨a, hPN ha⟩ : normalizer (J : Set G)) ^ (p ^ k) = 1 :=
      Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hun := hPN hu
  have hvn := hPN hv
  obtain ⟨k, hk⟩ := hpow hu
  obtain ⟨l, hl⟩ := hpow hv
  have hαD : ∃ k : ℕ, (ρ ⟨u, hun⟩) ^ (p ^ k) ∈ D := ⟨k, by rw [hρpow hu k hk]; exact D.one_mem⟩
  have hβD : ∃ k : ℕ, (ρ ⟨v, hvn⟩) ^ (p ^ k) ∈ D := ⟨l, by rw [hρpow hv l hl]; exact D.one_mem⟩
  have hcrit : ∀ {a b : G} (ha : a ∈ P) (hb : b ∈ P) (m : ℤ),
      ρ ⟨a, hPN ha⟩ * (ρ ⟨b, hPN hb⟩) ^ m ∈ D → a * b ^ m ∈ J ⊔ centralizer (J : Set G) := by
    intro a b ha hb m hm
    have hbm : b ^ m ∈ P := P.zpow_mem hb m
    have hab : a * b ^ m ∈ P := P.mul_mem ha hbm
    have himg : ρ ⟨a * b ^ m, hPN hab⟩ = ρ ⟨a, hPN ha⟩ * (ρ ⟨b, hPN hb⟩) ^ m := by
      rw [← map_zpow, ← map_mul]
      rfl
    obtain ⟨j, hj⟩ := hpow hab
    have hinner : ρ ⟨a * b ^ m, hPN hab⟩ ∈ Inn (J ⧸ center J) :=
      hD2 _ (himg ▸ hm) j (hρpow hab j hj ▸ (Inn _).one_mem)
    exact (hρmem _).mp hinner
  have hP' : ∀ {a b : G}, a ∈ P → b ∈ P → ∀ m : ℤ, a * b ^ m ∈ J ⊔ centralizer (J : Set G) →
      a ∈ zpowers b ⊔ (P ⊓ (J ⊔ centralizer (J : Set G))) := by
    intro a b ha hb m h1
    have hbm : b ^ m ∈ P := P.zpow_mem hb m
    have hab : a * b ^ m ∈ P := P.mul_mem ha hbm
    have : a = (a * b ^ m) * b ^ (-m) := by group
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_right ⟨hab, h1⟩) (mem_sup_left (zpow_mem (mem_zpowers b) _))
  have hαE := hpE _ hαD
  have hβE := hpE _ hβD
  rcases hD4 _ hαE _ hβE hαD hβD with ⟨m, hm⟩ | ⟨m, hm⟩
  · exact Or.inl (hP' hu hv m (hcrit hu hv m hm))
  · exact Or.inr (hP' hv hu m (hcrit hv hu m hm))

theorem mem_normalizer_sup_centralizer {L : Subgroup G} {g : G}
    (hg : g ∈ normalizer (L : Set G)) :
    g ∈ normalizer ((L ⊔ centralizer (L : Set G) : Subgroup G) : Set G) := by
  have key : ∀ {g : G}, g ∈ normalizer (L : Set G) → ∀ x : G, x ∈ L ⊔ centralizer (L : Set G) →
      g * x * g⁻¹ ∈ L ⊔ centralizer (L : Set G) := by
    intro g hg x hx
    obtain ⟨j, hj, z, hz, rfl⟩ := (mem_sup_centralizer_iff L).mp hx
    have h1 : g * j * g⁻¹ ∈ L := ((Subgroup.mem_normalizer_iff.1 hg j).1 hj)
    have h2 : g * z * g⁻¹ ∈ centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun i hi => ?_
      have hi' : g⁻¹ * i * g ∈ L := (Subgroup.mem_normalizer_iff''.1 hg i).1 hi
      have h := Subgroup.mem_centralizer_iff.1 hz _ hi'
      calc i * (g * z * g⁻¹) = g * ((g⁻¹ * i * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * i * g)) * g⁻¹ := by rw [h]
        _ = g * z * g⁻¹ * i := by group
    have : g * (j * z) * g⁻¹ = (g * j * g⁻¹) * (g * z * g⁻¹) := by group
    rw [this]
    exact Subgroup.mul_mem _ (mem_sup_left h1) (mem_sup_right h2)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key hg x, fun hx => ?_⟩
  have hg' : g⁻¹ ∈ normalizer (L : Set G) := (normalizer (L : Set G)).inv_mem hg
  have := key hg' _ hx
  simpa [mul_assoc] using this

theorem exists_mul_zpow_of_mem_sup {M : Subgroup G} {f g : G}
    (hf : f ∈ normalizer (M : Set G)) (hg : g ∈ M ⊔ zpowers f) :
    ∃ x ∈ M, ∃ m : ℤ, g = x * f ^ m := by
  have hconj : ∀ (m : ℤ) (y : G), y ∈ M → f ^ m * y * (f ^ m)⁻¹ ∈ M := fun m y hy =>
    (Subgroup.mem_normalizer_iff.1 ((normalizer (M : Set G)).zpow_mem hf m) y).1 hy
  let S : Subgroup G :=
    { carrier := {g | ∃ x ∈ M, ∃ m : ℤ, g = x * f ^ m}
      one_mem' := ⟨1, M.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x, hx, m, rfl⟩ ⟨y, hy, n, rfl⟩
        refine ⟨x * (f ^ m * y * (f ^ m)⁻¹), M.mul_mem hx (hconj m y hy), m + n, ?_⟩
        rw [zpow_add]
        group
      inv_mem' := by
        rintro _ ⟨x, hx, m, rfl⟩
        refine ⟨f ^ (-m) * x⁻¹ * (f ^ (-m))⁻¹, ?_, -m, ?_⟩
        · exact hconj (-m) x⁻¹ (M.inv_mem hx)
        · simp only [mul_inv_rev, zpow_neg, inv_inv]
          group }
  have hle : M ⊔ zpowers f ≤ S :=
    sup_le (fun x hx => ⟨x, hx, 0, by simp⟩)
      (fun y hy => by
        obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
        exact ⟨1, M.one_mem, m, by simp⟩)
  exact hle hg

end Comparable

section Cyclic

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_cyclic_mod_of_outPChain {p : ℕ} {L : Subgroup Y} [Group.IsPerfect L]
    (h : OutPChain p (L ⧸ center L)) {E : Subgroup Y} (hE : IsPGroup p E)
    (hEN : E ≤ normalizer (L : Set Y)) :
    ∃ u ∈ E, ∀ e ∈ E, ∃ k : ℕ, e * (u ^ k)⁻¹ ∈ L ⊔ centralizer (L : Set Y) := by
  obtain ⟨f, hfE, hEf⟩ := CFSG.RankThree.PartOne.K1214.exists_sup_zpowers_eq_of_comparable
    (P := E) (Q := E ⊓ (L ⊔ centralizer (L : Set Y))) inf_le_left
    (fun u hu v hv => comparable_of_outPChain' L h hE hEN hu hv)
  refine ⟨f, hfE, fun e he => ?_⟩
  have hfM : f ∈ normalizer ((L ⊔ centralizer (L : Set Y) : Subgroup Y) : Set Y) :=
    mem_normalizer_sup_centralizer (hEN hfE)
  have he' : e ∈ (L ⊔ centralizer (L : Set Y)) ⊔ zpowers f := by
    rw [hEf] at he
    have hle : (E ⊓ (L ⊔ centralizer (L : Set Y))) ⊔ zpowers f ≤
        (L ⊔ centralizer (L : Set Y)) ⊔ zpowers f :=
      sup_le (le_trans inf_le_right le_sup_left) le_sup_right
    exact hle he
  obtain ⟨x, hx, m, hm⟩ := exists_mul_zpow_of_mem_sup hfM he'
  have hn : 0 < orderOf f := orderOf_pos f
  refine ⟨(m % (orderOf f : ℤ)).toNat, ?_⟩
  have hnn : 0 ≤ m % (orderOf f : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
  have hpow : f ^ (m % (orderOf f : ℤ)).toNat = f ^ m := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hnn, zpow_mod_orderOf]
  rw [hpow, hm]
  simpa using hx

end Cyclic

section Small

theorem outPChain_of_not_dvd_card_outer {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (h : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X)) :
    OutPChain p X := by
  refine ⟨⊤, ⊤, le_top, ?_, fun α _ => trivial, fun α _ β _ _ _ => Or.inl ⟨0, trivial⟩⟩
  intro δ _ k hk
  have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) := Quotient.finite _
  set x : CFSG.ComponentClassification.OuterAutomorphisms.Outer X := QuotientGroup.mk δ with hx
  have hxk : x ^ (p ^ k) = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hk
  have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hxk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 h1
  have h2 : orderOf x ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) :=
    orderOf_dvd_natCard x
  have hi0 : i = 0 := by
    by_contra hne
    apply h
    have : p ∣ orderOf x := by
      rw [hi]
      exact dvd_pow_self p hne
    exact this.trans h2
  have : x = 1 := orderOf_eq_one_iff.mp (by rw [hi, hi0, pow_zero])
  exact (QuotientGroup.eq_one_iff δ).mp this

theorem outPChain_small {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : IsSmallTwoOrG2 X) : OutPChain p X := by
  have hp2 : p ≠ 2 := by omega
  rcases hX with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, ⟨q, hq7, hdq⟩ | ⟨q, hq3, hdq⟩, ⟨e⟩⟩
  · have hn5 : 5 ≤ n := by omega
    exact OutPChain.of_mulEquiv e (outPChain_of_not_dvd_card_outer hp
      (CFSG.AGLEmbedding.not_dvd_card_outer_alternatingGroup n hn5 p hp hp2))
  · simp only at hdq
    subst hdq
    obtain ⟨hq, hf⟩ : q.p = 7 ∧ q.exponent = 1 := by
      rw [TauCeti.PrimePower.card_def] at hq7
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq7
    have hc := CFSG.AGLEmbedding.statedClassicalModel_of_typeA hv (MulEquiv.refl _)
    exact OutPChain.of_mulEquiv e
      (outPNice_PSL_two_odd hp (by omega) (ℓ := q.p) (by omega) hc).toChain
  · simp only at hdq
    subst hdq
    obtain ⟨hq, hf⟩ : q.p = 3 ∧ q.exponent = 1 := by
      rw [TauCeti.PrimePower.card_def] at hq3
      exact (Nat.Prime.pow_eq_iff (by norm_num)).1 hq3
    have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv (MulEquiv.refl _)
    rw [hq, hf] at hc
    have : Finite (TauCeti.ValidLieTypeIndex.Group ⟨.twistedA 2 q, hv⟩) :=
      Finite.of_equiv _ e.toEquiv
    have hb := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inr rfl) (by norm_num) Nat.prime_three le_rfl hc).1
    have h1 : CFSG.RankThree.OuterOrder.determinantParameter .PSU 3 (3 ^ 1) = 1 := by
      norm_num [CFSG.RankThree.OuterOrder.determinantParameter]
    rw [h1] at hb
    refine OutPChain.of_mulEquiv e (outPChain_of_not_dvd_card_outer hp fun hd => ?_)
    have h2 : p ∣ 2 := hd.trans (by simpa using hb)
    have := Nat.le_of_dvd (by norm_num) h2
    omega

end Small

section Families

theorem outPChain_b {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : IsLieOf IdxB X) : OutPChain p X := by
  obtain ⟨⟨d, hv⟩, hPd, ⟨e⟩⟩ := hX
  cases d with
  | B r q =>
    have hq2 : q.p = 2 := hPd
    have hr : 2 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1 |>.1
    by_cases h2 : r = 2
    · subst h2
      have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
      rw [hq2] at hm
      exact (outPNice_PSp_two hp hm).toChain
    · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq2
        (by omega) e
      exact (outPNice_PSp_ge_three_odd hp (by omega) (by omega) hm).toChain
  | _ => exact hPd.elim

theorem outPChain_d {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : IsLieOf IdxD X) : OutPChain p X := by
  obtain ⟨⟨d, hv⟩, hPd, ⟨e⟩⟩ := hX
  cases d with
  | D r q =>
    have hr : 4 ≤ r := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q hv e
    by_cases h4 : r = 4
    · subst h4
      exact outPChain_POmegaPlus_four_gen hp hp5 hm
    · exact (outPNice_POmegaPlus_gen_ge_five hp hp5 (by omega) hm).toChain
  | _ => exact hPd.elim

theorem outPChain_twistedD {X : Type} [Group X] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hX : IsLieOf IdxTwistedD X) : OutPChain p X := by
  obtain ⟨⟨d, hv⟩, hPd, ⟨e⟩⟩ := hX
  cases d with
  | twistedD r q =>
    have hq2 : q.p = 2 := hPd
    have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq2 e
    exact (outPNice_POmegaMinus_gen hp hp5 hm).toChain
  | _ => exact hPd.elim

end Families

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.CentCyc
