module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Trans
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428U6D4Holds2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4XAsm2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YBMain
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4YIFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthMark
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExcLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FSimple
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
public import CFSG.HardMathSupport.Solomon.LocalBalance.Components
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.LargeExtraspecial.S14Defs
public import CFSG.LargeExtraspecial.S14Inputs
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreEven
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreL34
public import CFSG.LocalAnalysis.ComponentClassification.Foote5CoreRes
public import CFSG.LocalAnalysis.GLTheoremA.S11.Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.D4T (conjAut innerAut)
open CFSG.LocalAnalysis.GLTheoremA.D4Y (NotCentralOut D4RankCase)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open scoped commutatorElement

section Generic

private theorem t1428_three_dvd_two_pow_add_one {r : ℕ} (hr : Odd r) : 3 ∣ 2 ^ r + 1 := by
  obtain ⟨k, rfl⟩ := hr
  have h4 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h2]
  omega

theorem t1428_exists_D4_of_isD4n {n : ℕ} {i : TauCeti.CFSGIndex} (hi : isD4n n i) :
    ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), q.p = 2 ∧
      q.exponent = n ∧ i = TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩ := by
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D m q =>
      rcases m with _ | _ | _ | _ | _ | m
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · exact ⟨q, hv, hi.1, hi.2, rfl⟩
      · exact hi.elim
    | _ => exact hi.elim
  | _ => exact hi.elim

theorem t1428_isD4n_one_of_isD4two {i : TauCeti.CFSGIndex} (hi : S9.isD4two i) : isD4n 1 i := by
  cases i with
  | lie idx =>
    obtain ⟨d, hv⟩ := idx
    cases d with
    | D m q =>
      rcases m with _ | _ | _ | _ | _ | m
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · exact hi.elim
      · have hc0 : q.card = 2 := hi
        have hc : q.p ^ q.exponent = 2 := by rw [← TauCeti.PrimePower.card_def]; exact hc0
        have hdvd : q.p ∣ 2 := by
          rw [← hc]
          exact dvd_pow_self _ (Nat.ne_of_gt q.exponent_pos)
        have hp : q.p = 2 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 hdvd
        refine ⟨hp, ?_⟩
        rw [hp] at hc
        have : q.exponent = 1 := by
          have h1 : (2 : ℕ) ^ q.exponent = 2 ^ 1 := by rw [hc]; norm_num
          exact Nat.pow_right_injective le_rfl h1
        exact this
      · exact hi.elim
    | _ => exact hi.elim
  | _ => exact hi.elim

theorem t1428_isD4any_of_isD4n {n : ℕ} {S : Type} [Group S] (h : catalogIs S (isD4n n)) :
    catalogIs S isD4any := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  obtain ⟨q, hv, hp, -, rfl⟩ := t1428_exists_D4_of_isD4n hi
  exact ⟨TauCeti.CFSGIndex.lie ⟨.D 4 q, hv⟩, hp, ⟨f⟩⟩

theorem t1428_isD4pow2_of_isD4n {n : ℕ} {S : Type} [Group S] (h : catalogIs S (isD4n n)) :
    catalogIs S (D4Y.isD4pow2 n) := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  obtain ⟨q, hv, hp, hn, rfl⟩ := t1428_exists_D4_of_isD4n hi
  exact ⟨_, ⟨q, hv, hp, hn, rfl⟩, ⟨f⟩⟩

theorem t1428_hasLabel_D4 {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hK : GLAPComponent 3 X K) {n : ℕ} (h : catalogIs (PSimple 3 K) (isD4n n)) :
    Y10F.HasLabel (PQuot 3 K) (· = ⟨.D, 4, n⟩) := by
  obtain ⟨i, hi, ⟨f⟩⟩ := h
  obtain ⟨q, hv, hp, hn, rfl⟩ := t1428_exists_D4_of_isD4n hi
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD 4 q hv f
  rw [hp, hn] at hm
  have hs := chev_pSimple_simple_nonabelian Nat.prime_three hK
  exact Y10F.hasLabel_of_statedClassicalModel_POmegaPlus
    ⟨⟨(isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK).1⟩, hs.1, hs.2⟩ hm

theorem t1428_eq_of_canonLabel {lab : GLALabel} {n : ℕ} (h : canonLabel lab = ⟨.D, 4, n⟩) :
    lab.tag = .D ∧ lab.rank = 4 ∧ lab.n = n := by
  obtain ⟨t, k, m⟩ := lab
  cases t <;> simp only [canonLabel] at h <;> (try split_ifs at h) <;> simp_all

theorem t1428_chevTransfer_gLBConj {G : Type} [Group G] (p : ℕ) {K J : Subgroup G} (hJK : J ≤ K)
    {b : G} (hb : b ∈ Subgroup.normalizer (K : Set G)) :
    chevTransfer p K (GLBConj b⁻¹ J) =
      (chevTransfer p K J).map (chevAut p K ⟨b, hb⟩).toMonoidHom := by
  ext s
  constructor
  · rintro ⟨⟨k, hkK⟩, hk, rfl⟩
    have hk' : b⁻¹ * k * b ∈ J := by
      have := mem_gLBConj.1 (Subgroup.mem_subgroupOf.1 hk)
      simpa using this
    have hkK' : b⁻¹ * k * b ∈ K := hJK hk'
    refine ⟨chevQuotHom p K ⟨b⁻¹ * k * b, hkK'⟩, ⟨⟨b⁻¹ * k * b, hkK'⟩,
      Subgroup.mem_subgroupOf.2 hk', rfl⟩, ?_⟩
    change chevAut p K ⟨b, hb⟩ (chevQuotHom p K ⟨b⁻¹ * k * b, hkK'⟩) = _
    rw [chevAut_chevQuotHom]
    congr 1
    all_goals (apply Subtype.ext; simp [chev_coe_normalizerMonoidHom, mul_assoc])
  · rintro ⟨_, ⟨⟨j, hjK⟩, hj, rfl⟩, rfl⟩
    have hj' : (j : G) ∈ J := Subgroup.mem_subgroupOf.1 hj
    have hbj : b * j * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hb j).1 hjK
    refine ⟨⟨b * j * b⁻¹, hbj⟩,
      Subgroup.mem_subgroupOf.2 (mem_gLBConj.2 (by simpa [mul_assoc] using hj')), ?_⟩
    change chevQuotHom p K ⟨b * j * b⁻¹, hbj⟩ = chevAut p K ⟨b, hb⟩ (chevQuotHom p K ⟨j, hjK⟩)
    rw [chevAut_chevQuotHom]
    congr 1
    all_goals (apply Subtype.ext; simp [chev_coe_normalizerMonoidHom, mul_assoc])

private theorem t1428_mem_normalizer_inf {G : Type} [Group G] {K : Subgroup G} {y b : G}
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) (hby : Commute b y) :
    b ∈ Subgroup.normalizer ((K ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hK' := (Subgroup.mem_normalizer_iff.1 hbK) h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hK'.1 h1, ?_⟩
    calc b * h * b⁻¹ * y = b * h * (b⁻¹ * y) := by group
      _ = b * h * (y * b⁻¹) := by rw [(hby.inv_left).eq]
      _ = b * (h * y) * b⁻¹ := by group
      _ = b * (y * h) * b⁻¹ := by rw [h2]
      _ = (b * y) * h * b⁻¹ := by group
      _ = (y * b) * h * b⁻¹ := by rw [hby.eq]
      _ = y * (b * h * b⁻¹) := by group
  · rintro ⟨h1, h2⟩
    refine ⟨hK'.2 h1, ?_⟩
    have e : h = b⁻¹ * (b * h * b⁻¹) * b := by group
    rw [e]
    calc b⁻¹ * (b * h * b⁻¹) * b * y = b⁻¹ * (b * h * b⁻¹) * (b * y) := by group
      _ = b⁻¹ * (b * h * b⁻¹) * (y * b) := by rw [hby.eq]
      _ = b⁻¹ * ((b * h * b⁻¹) * y) * b := by group
      _ = b⁻¹ * (y * (b * h * b⁻¹)) * b := by rw [h2]
      _ = (b⁻¹ * y) * (b * h * b⁻¹) * b := by group
      _ = (y * b⁻¹) * (b * h * b⁻¹) * b := by rw [(hby.inv_left).eq]
      _ = y * (b⁻¹ * (b * h * b⁻¹) * b) := by group

private theorem t1428_mem_normalizer_inf' {G : Type} [Group G] {A C : Subgroup G} {b : G}
    (hA : b ∈ Subgroup.normalizer (A : Set G)) (hC : b ∈ Subgroup.normalizer (C : Set G)) :
    b ∈ Subgroup.normalizer ((A ⊓ C : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.1 hA) h,
    (Subgroup.mem_normalizer_iff.1 hC) h]

@[expose] def T1428U6Census : Prop :=
  ∀ (d : TauCeti.ValidLieTypeIndex), d.1.characteristic = 2 →
    ∀ η : MulAut (TauCeti.CFSGIndex.lie d).Group,
      η ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
        (TauCeti.CFSGIndex.lie d).Group →
      η ^ 3 = 1 → η ≠ 1 → ∀ r : ℕ, Odd r → 1 < r →
      ∀ J₁ J₂ J₃ : Subgroup (TauCeti.CFSGIndex.lie d).Group,
        CFSG.Open.IsComponentOf J₁ (fixSubgroup η) → CFSG.Open.IsComponentOf J₂ (fixSubgroup η) →
        CFSG.Open.IsComponentOf J₃ (fixSubgroup η) → J₁ ≠ J₂ → J₁ ≠ J₃ → J₂ ≠ J₃ →
        catalogIs (↥J₁ ⧸ Subgroup.center ↥J₁) (S10.isL2n r) →
        catalogIs (↥J₂ ⧸ Subgroup.center ↥J₂) (S10.isL2n r) →
        catalogIs (↥J₃ ⧸ Subgroup.center ↥J₃) (S10.isL2n r) →
        (catalogIs (TauCeti.CFSGIndex.lie d).Group (S10.isU6n r) ∧
          ∀ M : Subgroup (TauCeti.CFSGIndex.lie d).Group,
            CFSG.Open.IsComponentOf M (fixSubgroup η) →
              catalogIs (↥M ⧸ Subgroup.center ↥M) (S10.isL2n r)) ∨
        catalogIs (TauCeti.CFSGIndex.lie d).Group (isD4n r)

private theorem t1428u6_exists_label_of_marking {X : Type} [Group X] {S : GLALabel → Prop}
    (h : Y10F.HasLabel X S) : ∃ lab : GLALabel, S lab ∧ Y10F.HasLabel X (· = lab) := by
  obtain ⟨hX, lab, hlam, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hS⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact ⟨lab, hS, hX, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩

private theorem t1428u6_canonLabel_n_dvd_two_mul (lab : GLALabel) :
    (canonLabel lab).n ∣ 2 * lab.n := by
  obtain ⟨t, r, n⟩ := lab
  cases t
  case D =>
    simp only [canonLabel]
    split_ifs <;> exact dvd_mul_left n 2
  case twD =>
    simp only [canonLabel]
    split_ifs
    · exact dvd_mul_left n 2
    · exact dvd_rfl
    · exact dvd_mul_left n 2
  case B2der => exact one_dvd _
  case G2der => exact one_dvd _
  case twF4der => exact one_dvd _
  all_goals exact dvd_mul_left n 2

private theorem t1428u6_centerQuot_equiv_pSimple {S : Type} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) {X J : Subgroup S} (hJ : GLAPComponent p X J)
    (hq : CFSG.Open.IsQuasisimple ↥J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J) := by
  have hQ := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hne : GLAPPrimeCore p ↥J ≠ ⊤ := by
    intro htop
    haveI : Nontrivial (PQuot p J) := isQuasisimple_nontrivial hQ
    haveI : Subsingleton (↥J ⧸ GLAPPrimeCore p ↥J) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton (PQuot p J) ‹_›
  have hle : GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J :=
    le_center_of_normal_of_isQuasisimple hq inferInstance hne
  exact Y10F.quotEquiv_of_perfect_central (QuotientGroup.mk' (GLAPPrimeCore p ↥J))
    (QuotientGroup.mk'_surjective _) ⟨hq.1⟩ (by rw [QuotientGroup.ker_mk']; exact hle)

private theorem t1428u6_type_iff {G : Type} [Group G] [Finite G] {K J : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hap : IsPGroup 3 (Subgroup.zpowers y))
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (hJc : CFSG.Open.IsComponentOf (chevTransfer 3 K J) (fixSubgroup (chevAut 3 K ⟨y, hyN⟩)))
    {T : Type} [Group T] (e : PSimple 3 K ≃* T) (Q : TauCeti.CFSGIndex → Prop) :
    catalogIs (PSimple 3 J) Q ↔
      catalogIs (↥((chevTransfer 3 K J).map (e : PSimple 3 K →* T)) ⧸
        Subgroup.center ↥((chevTransfer 3 K J).map (e : PSimple 3 K →* T))) Q := by
  obtain ⟨e₁⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hyN hap hJ
  obtain ⟨e₂⟩ := t1428u6_centerQuot_equiv_pSimple Nat.prime_three
    (glaPComponent_chevTransfer Nat.prime_three hyN hap hJ) hJc.2.2
  let e₃ : ↥(chevTransfer 3 K J) ≃* ↥((chevTransfer 3 K J).map (e : PSimple 3 K →* T)) :=
    (chevTransfer 3 K J).equivMapOfInjective (e : PSimple 3 K →* T) e.injective
  let e₄ := QuotientGroup.congr _ _ e₃ (Subgroup.map_center_eq e₃)
  exact catalogIs_congr (e₁.trans (e₂.symm.trans e₄))

end Generic

section Certified

set_option linter.unusedSectionVars false


theorem t1428_diag
    {H : Type} [Group H] [Finite H] {Kb Bb : Subgroup H}
    (hcatK : catalogIs ↥Kb isD4any) (hnotK : ¬ catalogIs ↥Kb S9.isD4two)
    (hKc : ∀ k ∈ Kb, (∀ y ∈ Kb, y * k = k * y) → k = 1) (hBbel : IsElemAbelian 3 Bb)
    (hBbK : Bb ≤ Subgroup.normalizer (Kb : Set H))
    {c₀ : H} (hc₀ : c₀ ∈ Bb) (hc₀N : c₀ ∈ Subgroup.normalizer (Kb : Set H))
    (hNC : NotCentralOut (conjAut Kb c₀ hc₀N))
    (hP2 : ∀ P W : Subgroup H, IsElemAbelian 3 P → IsPGroup 2 W → W ≠ ⊥ →
      P ≤ Subgroup.normalizer (W : Set H) → Nat.card P ≤ Nat.card Bb)
    {t : H} (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hcomm : ∀ x ∈ Kb, ∀ z ∈ GLBConj t Kb, x * z = z * x)
    (hBt : ∀ c ∈ Bb, c * t = t * c) : False := by
  classical
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hconj : ∀ k ∈ Kb, t⁻¹ * k * t ∈ GLBConj t Kb := fun k hk => by
    rw [mem_gLBConj]
    simpa [mul_assoc] using hk
  let δ : ↥Kb →* H :=
    { toFun := fun k => (k : H) * (t⁻¹ * k * t)
      map_one' := by simp
      map_mul' := fun k l => by
        simp only [Subgroup.coe_mul]
        have h1 := hcomm (l : H) l.2 _ (hconj (k : H) k.2)
        calc (k : H) * l * (t⁻¹ * (k * l) * t) = k * (l * (t⁻¹ * k * t)) * (t⁻¹ * l * t) := by
              group
          _ = k * ((t⁻¹ * k * t) * l) * (t⁻¹ * l * t) := by rw [h1]
          _ = k * (t⁻¹ * k * t) * (l * (t⁻¹ * l * t)) := by group }
  have hδ : ∀ k : ↥Kb, δ k = (k : H) * (t⁻¹ * k * t) := fun _ => rfl
  have hδinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    rw [hδ] at hk
    have hkinv : t⁻¹ * (k : H) * t = (k : H)⁻¹ := eq_inv_of_mul_eq_one_right hk
    have hmem : ((k : H))⁻¹ ∈ GLBConj t Kb := hkinv ▸ hconj (k : H) k.2
    have hc : ∀ y ∈ Kb, y * (k : H)⁻¹ = (k : H)⁻¹ * y := fun y hy => hcomm y hy _ hmem
    have h1 : ((k : H))⁻¹ = 1 := hKc _ (Kb.inv_mem k.2) hc
    exact Subtype.ext (by simpa using h1)
  set Δ : Subgroup H := δ.range with hΔ
  let ψ : ↥Kb ≃* ↥Δ := MonoidHom.ofInjective hδinj
  have hψ : ∀ k : ↥Kb, ((ψ k : ↥Δ) : H) = δ k := fun _ => rfl
  have hcatΔ : catalogIs ↥Δ isD4any := (catalogIs_congr ψ).1 hcatK
  have hnotΔ : ¬ catalogIs ↥Δ S9.isD4two := fun h => hnotK ((catalogIs_congr ψ).2 h)
  have hΔc : ∀ d ∈ Δ, (∀ y ∈ Δ, y * d = d * y) → d = 1 := by
    intro d hd hcd
    obtain ⟨k, rfl⟩ := hd
    have hk : (k : H) = 1 := by
      refine hKc _ k.2 fun y hy => ?_
      have h1 := hcd (δ ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
      have h2 : δ (⟨y, hy⟩ * k) = δ (k * ⟨y, hy⟩) := by rw [map_mul, map_mul, h1]
      have h3 := congrArg Subtype.val (hδinj h2)
      simpa using h3
    have : k = 1 := Subtype.ext hk
    rw [this, map_one]
  have hδc : ∀ c : H, c * t = t * c → ∀ (k : H) (hk : k ∈ Kb) (hck : c * k * c⁻¹ ∈ Kb),
      c * δ ⟨k, hk⟩ * c⁻¹ = δ ⟨c * k * c⁻¹, hck⟩ := by
    intro c hct k hk hck
    rw [hδ, hδ]
    have hct' : c * t⁻¹ = t⁻¹ * c := by
      rw [htinv]
      exact hct
    calc c * (k * (t⁻¹ * k * t)) * c⁻¹ = c * k * c⁻¹ * ((c * t⁻¹) * k * (t * c⁻¹)) := by group
      _ = c * k * c⁻¹ * ((t⁻¹ * c) * k * (c⁻¹ * t)) := by
          rw [hct', show t * c⁻¹ = c⁻¹ * t by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hct, ← mul_assoc, inv_mul_cancel, one_mul]]
      _ = c * k * c⁻¹ * (t⁻¹ * (c * k * c⁻¹) * t) := by group
  have hNΔ : ∀ c : H, c * t = t * c → c ∈ Subgroup.normalizer (Kb : Set H) →
      c ∈ Subgroup.normalizer (Δ : Set H) := by
    intro c hct hcN
    have hct' : c⁻¹ * t = t * c⁻¹ := (Commute.inv_left (show Commute c t from hct)).eq
    have hcN' : c⁻¹ ∈ Subgroup.normalizer (Kb : Set H) := Subgroup.inv_mem _ hcN
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨⟨k, hk⟩, rfl⟩
      have hck : c * k * c⁻¹ ∈ Kb := (Subgroup.mem_normalizer_iff.1 hcN k).1 hk
      exact ⟨⟨c * k * c⁻¹, hck⟩, (hδc c hct k hk hck).symm⟩
    · rintro ⟨⟨k, hk⟩, hkx⟩
      have hck : c⁻¹ * k * c⁻¹⁻¹ ∈ Kb := (Subgroup.mem_normalizer_iff.1 hcN' k).1 hk
      refine ⟨⟨c⁻¹ * k * c⁻¹⁻¹, hck⟩, ?_⟩
      rw [← hδc c⁻¹ hct' k hk hck]
      change c⁻¹ * δ ⟨k, hk⟩ * c⁻¹⁻¹ = x
      rw [hkx]
      group
  have hBbΔ : Bb ≤ Subgroup.normalizer (Δ : Set H) := fun c hc => hNΔ c (hBt c hc) (hBbK hc)
  have hc₀Δ : c₀ ∈ Subgroup.normalizer (Δ : Set H) := hBbΔ hc₀
  have hcongr : MulAut.congr ψ (conjAut Kb c₀ hc₀N) = conjAut Δ c₀ hc₀Δ := by
    refine MulEquiv.ext fun d => ?_
    obtain ⟨k, rfl⟩ := ψ.surjective d
    have e1 : (MulAut.congr ψ (conjAut Kb c₀ hc₀N)) (ψ k) = ψ (conjAut Kb c₀ hc₀N k) := by
      simp [MulAut.congr_apply]
    rw [e1]
    apply Subtype.ext
    have hck : c₀ * (k : H) * c₀⁻¹ ∈ Kb := (Subgroup.mem_normalizer_iff.1 hc₀N k).1 k.2
    change δ ⟨c₀ * (k : H) * c₀⁻¹, hck⟩ = c₀ * δ k * c₀⁻¹
    exact (hδc c₀ (hBt c₀ hc₀) k k.2 hck).symm
  have hNCΔ : NotCentralOut (conjAut Δ c₀ hc₀Δ) := by
    obtain ⟨γ, hγ⟩ := hNC
    refine ⟨MulAut.congr ψ γ, fun hmem => hγ ?_⟩
    rw [← hcongr] at hmem
    have h1 : MulAut.congr ψ (γ * conjAut Kb c₀ hc₀N * γ⁻¹ * (conjAut Kb c₀ hc₀N)⁻¹) ∈
        innerAut ↥Δ := by
      simpa only [map_mul, map_inv] using hmem
    have h2 := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr ψ
    have h3 : MulAut.congr ψ (γ * conjAut Kb c₀ hc₀N * γ⁻¹ * (conjAut Kb c₀ hc₀N)⁻¹) ∈
        (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥Kb).map
          (MulAut.congr ψ).toMonoidHom := by
      rw [h2]
      exact h1
    obtain ⟨z, hz, hzx⟩ := h3
    have : z = γ * conjAut Kb c₀ hc₀N * γ⁻¹ * (conjAut Kb c₀ hc₀N)⁻¹ :=
      (MulAut.congr ψ).injective hzx
    exact this ▸ hz
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hT2 : IsPGroup 2 ↥(Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hto, pow_one]
  have hTne : Subgroup.zpowers t ≠ ⊥ := by
    intro h
    apply ht1
    have : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
    rw [h, Subgroup.mem_bot] at this
    exact this
  have hBT : Bb ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup H) : Set H) := by
    intro c hc
    refine D4T.mem_normalizer_of_centralizes fun w hw => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact ((Commute.zpow_right (show Commute c t from hBt c hc) n)).eq
  have htΔ : t ∈ Subgroup.normalizer (Δ : Set H) := by
    refine D4T.mem_normalizer_of_centralizes fun w hw => ?_
    obtain ⟨k, rfl⟩ := hw
    rw [hδ]
    have hz := hconj (k : H) k.2
    have h1 := hcomm (k : H) k.2 _ hz
    have e1 : t * ((k : H) * (t⁻¹ * k * t)) * t⁻¹ = (t⁻¹ * k * t) * k := by
      rw [htinv]
      calc t * ((k : H) * (t * k * t)) * t = (t * k * t) * k * (t * t) := by group
        _ = (t * k * t) * k := by rw [ht2, mul_one]
    rw [← mul_inv_eq_iff_eq_mul, e1, ← h1]
  have hTΔ : Subgroup.zpowers t ≤ Subgroup.normalizer (Δ : Set H) := Subgroup.zpowers_le.2 htΔ
  exact D4Y.d4BigCoreAt_holds H Δ Bb hcatΔ hnotΔ hΔc hBbel hBbΔ ⟨c₀, hc₀, hc₀Δ, hNCΔ⟩
    (Or.inr ⟨hP2, Subgroup.zpowers t, hT2, hTne, hBT, hTΔ⟩)


open CFSG.LocalAnalysis.GLTheoremA.S9

theorem t1428_noTri
    {Ω : Type} [Group Ω] [Finite Ω] {B K : Subgroup Ω} (hBmax : GLAIsBmax 3 B)
    (hK : GLAPComponent 3 ⊤ K) (hD4 : catalogIs (PSimple 3 K) isD4any)
    (hnD4 : ¬ catalogIs (PSimple 3 K) S9.isD4two)
    (hBall : ∀ g : Ω, B ≤ Subgroup.normalizer ((GLBConj g K : Subgroup Ω) : Set Ω))
    {b : Ω} (hb : b ∈ B) (hbN : b ∈ Subgroup.normalizer (K : Set Ω)) (γ : MulAut (PSimple 3 K)) :
    γ * chevAut 3 K ⟨b, hbN⟩ * γ⁻¹ * (chevAut 3 K ⟨b, hbN⟩)⁻¹ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 K) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  set C : Subgroup Ω := ⊤ with hC
  obtain ⟨hBel, hBcard, T₀, hT₀ne, hT₀2, hBT₀⟩ := glaIsBmax_iff.1 hBmax
  have hBC : B ≤ C := le_top
  have hLC : K ≤ C := le_top
  have hLsn : CFSG.Open.IsSubnormal K C := hK.2.1
  have hBL : B ≤ Subgroup.normalizer (K : Set Ω) := by
    have := hBall 1
    rwa [gLBConj_one] at this
  have hq := isQuasisimple_pQuot_of_glaPComponent hp3 hK
  have hZ : Subgroup.center (PQuot 3 K) = ⊥ :=
    D4Y.center_pQuot_eq_bot_of_d4big
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement hq hD4 hnD4
  set Kb : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C K with hKb
  set Bb : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C) := barX 3 C B with hBb
  let e : PQuot 3 K ≃* ↥Kb := quotEquivBarX hp3 hLC hLsn
  let e0 : PSimple 3 K ≃* PQuot 3 K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e1 : PSimple 3 K ≃* ↥Kb := e0.trans e
  have hcatK : catalogIs ↥Kb isD4any := (catalogIs_congr e1).1 hD4
  have hnotK : ¬ catalogIs ↥Kb S9.isD4two := fun h => hnD4 ((catalogIs_congr e1).2 h)
  have hKc : ∀ k ∈ Kb, (∀ y ∈ Kb, y * k = k * y) → k = 1 := by
    intro k hk hcomm
    obtain ⟨q, hq'⟩ := e.surjective ⟨k, hk⟩
    have hqc : q ∈ Subgroup.center (PQuot 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro q'
      apply e.injective
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul]
      rw [hq']
      exact hcomm _ (e q').2
    rw [hZ, Subgroup.mem_bot] at hqc
    subst hqc
    have := congrArg Subtype.val hq'
    simpa using this.symm
  have hBO : B ⊓ GLAPPrimeCoreOf 3 C = ⊥ := by
    have hOcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 C)) :=
      (Nat.Prime.coprime_iff_not_dvd hp3).2 (not_dvd_card_glaPPrimeCoreOf hp3 C)
    have hcopB : Nat.Coprime (Nat.card B) (Nat.card (GLAPPrimeCoreOf 3 C)) := by
      rw [hBcard]
      exact Nat.Coprime.pow_left _ hOcop
    have h1 := Nat.eq_one_of_dvd_coprimes hcopB (Subgroup.card_dvd_of_le inf_le_left)
      (Subgroup.card_dvd_of_le inf_le_right)
    exact Subgroup.card_eq_one.1 h1
  have hBbel : IsElemAbelian 3 Bb := l94t_isElemAbelian_barX hBel hBC
  have hBbcard : Nat.card Bb = Nat.card B := l94t_card_barX hBC hBO
  have hBbK : Bb ≤ Subgroup.normalizer (Kb : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) :=
    l94t_barX_le_normalizer (p := 3) hLC hBL
  have hbC : b ∈ C := hBC hb
  set π : ↥C →* ↥C ⧸ GLAPPrimeCore 3 ↥C := QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) with hπ
  have hbBb : π ⟨b, hbC⟩ ∈ Bb := ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hb, rfl⟩
  have hbNK : π ⟨b, hbC⟩ ∈ Subgroup.normalizer (Kb : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) := hBbK hbBb
  have hcong : MulAut.congr e1 (chevAut 3 K ⟨b, hbN⟩) = conjAut Kb (π ⟨b, hbC⟩) hbNK := by
    ext k
    obtain ⟨s, rfl⟩ := e1.surjective k
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hbl : b * (l : Ω) * b⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hbN (l : Ω)).1 l.2
    have h1 : chevAut 3 K ⟨b, hbN⟩ (QuotientGroup.mk (QuotientGroup.mk l)) =
        QuotientGroup.mk (QuotientGroup.mk ⟨b * (l : Ω) * b⁻¹, hbl⟩) := by
      have := chevAut_chevQuotHom 3 K ⟨b, hbN⟩ l
      have e2 : K.normalizerMonoidHom ⟨b, hbN⟩ l = ⟨b * (l : Ω) * b⁻¹, hbl⟩ :=
        Subtype.ext (chev_coe_normalizerMonoidHom _ _)
      rw [e2] at this
      exact this
    change ((e1 (chevAut 3 K ⟨b, hbN⟩ (e1.symm (e1 (QuotientGroup.mk (QuotientGroup.mk l))))) :
        ↥Kb) : ↥C ⧸ GLAPPrimeCore 3 ↥C) = _
    rw [MulEquiv.symm_apply_apply, h1]
    change π ⟨b * (l : Ω) * b⁻¹, hLC hbl⟩ = π ⟨b, hbC⟩ * π ⟨(l : Ω), hLC l.2⟩ * (π ⟨b, hbC⟩)⁻¹
    have : (⟨b * (l : Ω) * b⁻¹, hLC hbl⟩ : ↥C) = ⟨b, hbC⟩ * ⟨(l : Ω), hLC l.2⟩ * ⟨b, hbC⟩⁻¹ :=
      Subtype.ext (by simp)
    rw [this, map_mul, map_mul, map_inv]
  by_contra hγ
  have hNC : NotCentralOut (conjAut Kb (π ⟨b, hbC⟩) hbNK) := by
    refine ⟨MulAut.congr e1 γ, fun hmem => hγ ?_⟩
    rw [← hcong] at hmem
    have h1 : MulAut.congr e1 (γ * chevAut 3 K ⟨b, hbN⟩ * γ⁻¹ * (chevAut 3 K ⟨b, hbN⟩)⁻¹) ∈
        innerAut ↥Kb := by
      simpa only [map_mul, map_inv] using hmem
    have h2 := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr e1
    have h3 : MulAut.congr e1 (γ * chevAut 3 K ⟨b, hbN⟩ * γ⁻¹ * (chevAut 3 K ⟨b, hbN⟩)⁻¹) ∈
        (CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 K)).map
          (MulAut.congr e1).toMonoidHom := by
      rw [h2]
      exact h1
    obtain ⟨z, hz, hzx⟩ := h3
    have : z = γ * chevAut 3 K ⟨b, hbN⟩ * γ⁻¹ * (chevAut 3 K ⟨b, hbN⟩)⁻¹ :=
      (MulAut.congr e1).injective hzx
    exact this ▸ hz
  have hout : ∃ c ∈ Bb, ∃ hc : c ∈ Subgroup.normalizer (Kb : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)),
      NotCentralOut (conjAut Kb c hc) := ⟨π ⟨b, hbC⟩, hbBb, hbNK, hNC⟩
  have hP2 : ∀ P W : Subgroup (↥C ⧸ GLAPPrimeCore 3 ↥C), IsElemAbelian 3 P → IsPGroup 2 W →
      W ≠ ⊥ → P ≤ Subgroup.normalizer (W : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) →
      Nat.card P ≤ Nat.card Bb := by
    intro P W hP hW2 hWne hPW
    have := l94_card_le_of_quot (C := C) hP hW2 hWne hPW
    rw [hBbcard, hBcard]
    exact this
  by_cases hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 C))
  · by_cases hT₁ : T₀ ⊓ Subgroup.normalizer (K : Set Ω) = ⊥
    ·
      have hBcT : ∀ t ∈ T₀, ∀ b' ∈ B, t * b' = b' * t := by
        intro t ht b' hb'
        have h1 : t * b' * t⁻¹ ∈ Subgroup.normalizer (K : Set Ω) := by
          have hBn := hBall t hb'
          rw [Subgroup.mem_normalizer_iff]
          intro z
          have h2 := Subgroup.mem_normalizer_iff.1 hBn (t⁻¹ * z * t)
          rw [mem_gLBConj, mem_gLBConj] at h2
          have e1 : t * (t⁻¹ * z * t) * t⁻¹ = z := by group
          have e2 : t * (b' * (t⁻¹ * z * t) * b'⁻¹) * t⁻¹ =
              t * b' * t⁻¹ * z * (t * b' * t⁻¹)⁻¹ := by group
          rw [e1, e2] at h2
          exact h2
        have hcN : t * b' * t⁻¹ * b'⁻¹ ∈ Subgroup.normalizer (K : Set Ω) :=
          Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (hBL hb'))
        have hcT : t * b' * t⁻¹ * b'⁻¹ ∈ T₀ := by
          have h3 : b' * t⁻¹ * b'⁻¹ ∈ T₀ :=
            (Subgroup.mem_normalizer_iff.1 (hBT₀ hb') t⁻¹).1 (T₀.inv_mem ht)
          have e : t * b' * t⁻¹ * b'⁻¹ = t * (b' * t⁻¹ * b'⁻¹) := by group
          rw [e]
          exact T₀.mul_mem ht h3
        have hc1 : t * b' * t⁻¹ * b'⁻¹ = 1 := by
          have : t * b' * t⁻¹ * b'⁻¹ ∈ T₀ ⊓ Subgroup.normalizer (K : Set Ω) := ⟨hcT, hcN⟩
          rw [hT₁, Subgroup.mem_bot] at this
          exact this
        calc t * b' = (t * b' * t⁻¹ * b'⁻¹) * (b' * t) := by group
          _ = b' * t := by rw [hc1, one_mul]
      obtain ⟨t, htT, ht2, ht1⟩ : ∃ t ∈ T₀, t * t = 1 ∧ t ≠ 1 := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have hcard : 2 ∣ Nat.card T₀ := by
          rcases hT₀2.card_eq_or_dvd with h1 | h2
          · exact absurd (Subgroup.card_eq_one.1 h1) hT₀ne
          · exact h2
        obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hcard
        refine ⟨x, x.2, ?_, ?_⟩
        · have h1 := pow_orderOf_eq_one x
          rw [hx, pow_two] at h1
          exact congrArg Subtype.val h1
        · intro h
          have h1 : x = 1 := Subtype.ext h
          rw [h1, orderOf_one] at hx
          norm_num at hx
      have htN : t ∉ Subgroup.normalizer (K : Set Ω) := fun h => by
        have h1 : t ∈ T₀ ⊓ Subgroup.normalizer (K : Set Ω) := ⟨htT, h⟩
        rw [hT₁, Subgroup.mem_bot] at h1
        exact ht1 h1
      have htC : t ∈ C := Subgroup.mem_top t
      set tb : ↥C ⧸ GLAPPrimeCore 3 ↥C := π ⟨t, htC⟩ with htb
      have htb2 : tb * tb = 1 := by
        rw [htb, ← map_mul]
        have : (⟨t, htC⟩ : ↥C) * ⟨t, htC⟩ = 1 := Subtype.ext ht2
        rw [this, map_one]
      have htb1 : tb ≠ 1 := by
        intro h
        have h1 : t ∈ GLAPPrimeCoreOf 3 C := (l94t_mk_eq_one_iff (p := 3) htC).1 h
        have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
        have h2 : orderOf (⟨t, h1⟩ : ↥(GLAPPrimeCoreOf 3 C)) ∣ Nat.card (GLAPPrimeCoreOf 3 C) :=
          orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk, hto] at h2
        exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
      have htbN : tb ∉ Subgroup.normalizer (Kb : Set (↥C ⧸ GLAPPrimeCore 3 ↥C)) := fun h =>
        htN (mem_normalizer_of_barX_normalizes hp3 le_rfl hK htC
          (Subgroup.mem_normalizer_iff.2 fun _ => ⟨fun _ => Subgroup.mem_top _,
            fun _ => Subgroup.mem_top _⟩) h)
      have hK' : GLAPComponent 3 C (GLBConj t K) :=
        CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_gLBConj_of_mem hK htC
      have hKb' : barX 3 C (GLBConj t K) = GLBConj tb Kb := barX_gLBConj_eq 3 htC K
      have hc1 : CFSG.Open.IsComponentOf Kb ⊤ := hK.2.2.1
      have hc2 : CFSG.Open.IsComponentOf (GLBConj tb Kb) ⊤ := hKb' ▸ hK'.2.2.1
      have hne : Kb ≠ GLBConj tb Kb := fun h => htbN (mem_normalizer_iff_gLBConj_eq.2 h.symm)
      have hcomm : ∀ x ∈ Kb, ∀ z ∈ GLBConj tb Kb, x * z = z * x := fun x hx z hz =>
        CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hc1 hc2 hne hx hz
      have hBt : ∀ c ∈ Bb, c * tb = tb * c := by
        rintro _ ⟨⟨b', hb'C⟩, hb', rfl⟩
        rw [htb, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hBcT t htT b' (Subgroup.mem_subgroupOf.1 hb')).symm
      exact t1428_diag hcatK hnotK hKc hBbel hBbK hbBb hbNK hNC hP2 htb2 htb1 hcomm hBt
    ·
      have hT₁2 : IsPGroup 2 ↥(T₀ ⊓ Subgroup.normalizer (K : Set Ω)) := hT₀2.to_le inf_le_left
      have hBT₁ : B ≤ Subgroup.normalizer
          ((T₀ ⊓ Subgroup.normalizer (K : Set Ω) : Subgroup Ω) : Set Ω) := fun b' hb' =>
        t1428_mem_normalizer_inf' (hBT₀ hb') (Subgroup.le_normalizer (hBL hb'))
      refine D4Y.d4BigCoreAt_holds _ Kb Bb hcatK hnotK hKc hBbel hBbK hout (Or.inr ⟨hP2, ?_⟩)
      exact ⟨barX 3 C (T₀ ⊓ Subgroup.normalizer (K : Set Ω)), l94t_isPGroup_barX le_top hT₁2,
        l94t_barX_ne_bot le_top hT₁2 hT₁ hodd, l94t_barX_le_normalizer (p := 3) le_top hBT₁,
        l94t_barX_le_normalizer (p := 3) le_top inf_le_right⟩
  ·
    have heven : 2 ∣ Nat.card (GLAPPrimeCoreOf 3 C) :=
      even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
    refine D4Y.d4BigCoreAt_holds _ Kb Bb hcatK hnotK hKc hBbel hBbK hout (Or.inl fun P hP => ?_)
    have := D4T.card_le_of_quot_even (G := Ω) (C := C) heven hP
    rw [hBbcard, hBcard]
    exact this


open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind FamOrth)

theorem t1428_innDiagKind_chevAut
    {G : Type} [Group G] {p : ℕ} {K : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) (hq : CFSG.Open.IsQuasisimple (PQuot p K))
    (hInn : S10.InnDiagOn p (Subgroup.zpowers y) K) :
    ∃ labL : GLALabel, HasLabel (PQuot p K) (· = labL) ∧
      InnDiagKind (PSimple p K) labL (chevAut p K ⟨y, hy⟩) := by
  have hcen := Y10F.center_centerQuot_eq_bot hq
  haveI : Group.IsPerfect (PQuot p K) := ⟨hq.1⟩
  have hS : commutator (PSimple p K) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (PQuot p K)))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  obtain ⟨hX, labL, hlam, hraw⟩ := hInn.2
  refine ⟨labL, ⟨hX, labL, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩,
    hS, labL, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hall⟩
  obtain ⟨φ, hφ, hind⟩ := hall y⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
  refine ⟨hs, hna, (CanonInn.quotCenterEquivOfBot hcen).trans θ, rfl, φ, hφ, ?_⟩
  intro s s' hss'
  subst hss'
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, CanonInn.quotCenterEquivOfBot_mk,
    CanonInn.quotCenterEquivOfBot_mk]
  have hc := chevAut_chevQuotHom p K ⟨y, hy⟩ k
  have hi := hind (QuotientGroup.mk k) (QuotientGroup.mk (K.normalizerMonoidHom ⟨y, hy⟩ k))
    ⟨k, K.normalizerMonoidHom ⟨y, hy⟩ k, rfl, rfl, by rw [chev_coe_normalizerMonoidHom, inv_inv]⟩
  exact hi.trans (congrArg θ hc.symm)

theorem t1428_chevAut_mem_inner
    {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hK : GLAPComponent 3 X K) {r : ℕ} (hD4 : catalogIs (PSimple 3 K) (isD4n r)) {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) (hInn : S10.InnDiagOn 3 (Subgroup.zpowers y) K) :
    chevAut 3 K ⟨y, hy⟩ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 K) := by
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hK
  obtain ⟨labL, hXL, hin⟩ := t1428_innDiagKind_chevAut hy hq hInn
  have hX₀ := t1428_hasLabel_D4 hK hD4
  have hc := Y10GInnExcLabel.canonLabel_eq_of_hasLabel CFSG.StandardType.ggLabelRigidInput_holds
    hXL hX₀
  have hc' : canonLabel labL = ⟨.D, 4, r⟩ := by
    rw [hc]
    simp [canonLabel]
  obtain ⟨htag, hrank, -⟩ := t1428_eq_of_canonLabel hc'
  have hFam : FamOrth labL := Or.inl ⟨htag, by omega⟩
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian Nat.prime_three hK
  haveI := hsimple
  have hcen : Subgroup.center (PSimple 3 K) = ⊥ := chev_center_eq_bot_of_simple_nonabelian hna
  obtain ⟨-, a, ha⟩ := Y10GInnOrthMark.innDiagKind_orth_data hcen hFam hin
  exact ⟨a, ha⟩

theorem t1428D4Fact_holds
    : T1428D4Fact := by
  intro Ω _ _ K B y J₁ J₂ J₃ r hcfg hD4
  obtain ⟨hΩ, hBmax, hK, -, -, hyB, -, hInn, hr_odd, hr1, h12, -, -, hJ1, hJ2, -, -, -, -⟩ := hcfg
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨hBel, hBcard, -⟩ := glaIsBmax_iff.1 hBmax
  have hD4any := t1428_isD4any_of_isD4n hD4
  have hnD4 : ¬ catalogIs (PSimple 3 K) S9.isD4two := by
    intro h2
    obtain ⟨i, hi, ⟨f⟩⟩ := h2
    have h1 : catalogIs (PSimple 3 K) (isD4n 1) := ⟨i, t1428_isD4n_one_of_isD4two hi, ⟨f⟩⟩
    have hl := t1428_hasLabel_D4 hK hD4
    have hl1 := t1428_hasLabel_D4 hK h1
    have h3 := Y10GInnExcLabel.canonLabel_eq_of_hasLabel CFSG.StandardType.ggLabelRigidInput_holds
      hl hl1
    simp [canonLabel] at h3
    omega
  have hrankB : GLATwoLocalRank 3 ↥(⊤ : Subgroup Ω) ≤ CFSG.Open.pRank 3 B :=
    (CFSG.HardMathSupport.Solomon.LocalBalance.glaTwoLocalRank_subgroup_le hp3 ⊤).trans
      (CFSG.SectionRank.le_pRank hp3.one_lt (le_refl B) hBel hBcard)
  have hBall : ∀ g : Ω, B ≤ Subgroup.normalizer ((GLBConj g K : Subgroup Ω) : Set Ω) := by
    intro g
    refine D4Y.d4BigNormalizes_holds Ω ⊤ B (GLBConj g K) (CFSG.Open.IsKGroup.subgroup hΩ ⊤) hBel
      le_top hrankB
      (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_gLBConj_of_mem hK (Subgroup.mem_top g))
      (S8.L84.catalogIs_pSimple_conj g hD4any) fun h => hnD4 ?_
    have := S8.L84.catalogIs_pSimple_conj g⁻¹ h
    rwa [gLBConj_gLBConj, mul_inv_cancel, gLBConj_one] at this
  have hBK : B ≤ Subgroup.normalizer (K : Set Ω) := by
    have := hBall 1
    rwa [gLBConj_one] at this
  have hyN : y ∈ Subgroup.normalizer (K : Set Ω) := hInn.1 (Subgroup.mem_zpowers y)
  have hy3 : y ^ 3 = 1 := hBel.2 y hyB
  have hap : IsPGroup 3 (Subgroup.zpowers y) :=
    CFSG.LocalAnalysis.GLTheoremA.isPGroup_zpowers_of_pow_eq_one hy3
  have hηI : chevAut 3 K ⟨y, hyN⟩ ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 K) :=
    t1428_chevAut_mem_inner hK hD4 hyN hInn
  have hη1 : chevAut 3 K ⟨y, hyN⟩ ≠ 1 := by
    intro h1
    obtain ⟨-, huniq, -⟩ :=
      glaPLayer_inf_centralizer hp3 hK hap ((chevAut_eq_one_iff hp3 hK hyN).1 h1)
    exact h12 ((huniq J₁ hJ1).trans (huniq J₂ hJ2).symm)
  have hη3 : orderOf (chevAut 3 K ⟨y, hyN⟩) = 3 :=
    orderOf_eq_prime (chevAut_pow_eq_one 3 K hyN hy3) hη1
  obtain ⟨K₀, _, _, _, hK₀, ⟨Φ⟩⟩ :=
    D4Y.exists_om8_of_isD4pow2 (by omega : 2 ≤ r) (t1428_isD4pow2_of_isD4n hD4)
  have hpq : 3 ∣ Nat.card K₀ + 1 := by
    rw [hK₀]
    exact t1428_three_dvd_two_pow_add_one hr_odd
  have hJs := glaPComponent_chevTransfer hp3 hyN hap hJ1
  obtain ⟨i, hi, ⟨f⟩⟩ := hD4
  obtain ⟨q, hv, hqp, -, rfl⟩ := t1428_exists_D4_of_isD4n hi
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian hp3 hK
  have hchar : (3 : ℕ) ≠ (TauCeti.LieTypeIndex.D 4 q).characteristic := by
    rw [TauCeti.LieTypeIndex.characteristic_D 4 q, hqp]
    norm_num
  have hpil := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
    (PSimple 3 K) hsimple hna ⟨.D 4 q, hv⟩ ⟨f⟩ 3 hp3 (by norm_num) hchar
    (chevAut 3 K ⟨y, hyN⟩) (chevAut_pow_eq_one 3 K hyN hy3) hη1
  have hJle := hpil _ hJs.1 (glaPComponent_perfect hJs)
  have hJc :=
    (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJs hJle).1
  intro b hb
  have hbN : b ∈ Subgroup.normalizer (K : Set Ω) := hBK hb
  have hb3 : b ^ 3 = 1 := hBel.2 b hb
  have hβ3 : chevAut 3 K ⟨b, hbN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hbN hb3
  have hβc : ∀ γ : MulAut (PSimple 3 K),
      γ * chevAut 3 K ⟨b, hbN⟩ * γ⁻¹ * (chevAut 3 K ⟨b, hbN⟩)⁻¹ ∈
        CFSG.ComponentClassification.OuterAutomorphisms.inner (PSimple 3 K) :=
    fun γ => t1428_noTri hBmax hK hD4any hnD4 hBall hb hbN γ
  have hβη : chevAut 3 K ⟨b, hbN⟩ * chevAut 3 K ⟨y, hyN⟩ =
      chevAut 3 K ⟨y, hyN⟩ * chevAut 3 K ⟨b, hbN⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (isElemAbelian_commute hBel hb hyB)
  have key := t1428_d4_map_eq hpq Φ hηI hη3 hβ3 hβc hβη hJc
  by_contra hnot
  have hnot' : GLBConj b⁻¹ J₁ ≠ J₁ := by
    intro h
    apply hnot
    have : b⁻¹ ∈ Subgroup.normalizer (J₁ : Set Ω) := mem_normalizer_iff_gLBConj_eq.2 h
    simpa using Subgroup.inv_mem _ this
  have hbinvC : b⁻¹ ∈ Subgroup.normalizer
      ((K ⊓ Subgroup.centralizer ({y} : Set Ω) : Subgroup Ω) : Set Ω) :=
    t1428_mem_normalizer_inf (Subgroup.inv_mem _ hbN)
      (isElemAbelian_commute hBel (Subgroup.inv_mem _ hb) hyB)
  have hJ1' : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) (GLBConj b⁻¹ J₁) := by
    have := CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_gLBConj b⁻¹ hJ1
    rwa [mem_normalizer_iff_gLBConj_eq.1 hbinvC] at this
  have hJK : J₁ ≤ K := hJ1.1.trans inf_le_left
  apply hnot'
  apply eq_of_chevTransfer_eq hp3 hyN hap hJ1' hJ1
  rw [t1428_chevTransfer_gLBConj 3 hJK hbN]
  exact key


theorem t1428U6Fact_of_census
    (hC : T1428U6Census) : T1428U6Fact := by
  intro Ω _ _ K B y J₁ J₂ J₃ r hcfg _
  obtain ⟨-, hBmax, hK, -, hmark, hyB, -, hInn, hr_odd, hr1, h12, h13, h23, hJ1, hJ2, hJ3,
    hc1, hc2, hc3⟩ := hcfg
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  obtain ⟨hBel, -, -⟩ := glaIsBmax_iff.1 hBmax
  have hyN : y ∈ Subgroup.normalizer (K : Set Ω) := hInn.1 (Subgroup.mem_zpowers y)
  have hy3 : y ^ 3 = 1 := hBel.2 y hyB
  have hap : IsPGroup 3 (Subgroup.zpowers y) :=
    CFSG.LocalAnalysis.GLTheoremA.isPGroup_zpowers_of_pow_eq_one hy3
  have hq := isQuasisimple_pQuot_of_glaPComponent hp3 hK
  have hcen := Y10F.center_centerQuot_eq_bot hq
  obtain ⟨labL, hXL, hin⟩ := t1428_innDiagKind_chevAut hyN hq hInn
  have hlamL := CanonSubcomp.lambda2_of_hasLabel hXL
  obtain ⟨lab₀, hp₀, hX₀⟩ := t1428u6_exists_label_of_marking (S := fun lab => 3 ∣ lab.n) hmark
  have hdvdL : 3 ∣ (canonLabel labL).n := by
    rw [Y10GInnExcLabel.canonLabel_eq_of_hasLabel CFSG.StandardType.ggLabelRigidInput_holds
      hXL hX₀]
    exact hp₀.trans (CanonSubcomp.n_dvd_canonLabel_n (CanonSubcomp.lambda2_of_hasLabel hX₀))
  have hn2 : 2 ≤ labL.n := by
    by_contra hlt
    have hn1 : labL.n = 1 := by have := hlamL.1; omega
    have h2 := t1428u6_canonLabel_n_dvd_two_mul labL
    rw [hn1, mul_one] at h2
    have := Nat.le_of_dvd two_pos (hdvdL.trans h2)
    omega
  have hη1 : chevAut 3 K ⟨y, hyN⟩ ≠ 1 := by
    intro h1
    obtain ⟨-, huniq, -⟩ :=
      glaPLayer_inf_centralizer hp3 hK hap ((chevAut_eq_one_iff hp3 hK hyN).1 h1)
    exact h12 ((huniq J₁ hJ1).trans (huniq J₂ hJ2).symm)
  have hη3 : chevAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hyN hy3
  have hηD := CanonSubcomp.mem_innAutDerived_of_innDiagKind
    CFSG.StandardType.ggInndiagCommRestInput_holds hcen hn2 hin
  have hc := CanonSubcomp.markChar_eq_two_of_two_le hlamL hn2
  have hLM := CanonSubcomp.markedModel_of_hasLabel hXL
  unfold CFSG.StandardType.MarkedModel at hLM
  rw [hc] at hLM
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian hp3 hK
  have hJs : ∀ {J : Subgroup Ω}, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J →
      GLAPComponent 3 (fixSubgroup (chevAut 3 K ⟨y, hyN⟩)) (chevTransfer 3 K J) :=
    fun hJ => glaPComponent_chevTransfer hp3 hyN hap hJ
  rcases CanonSubcomp.exists_index_or_small_of_lieModel_two hLM with ⟨d, hd2, ⟨e⟩⟩ | h60 | h1
  ·
    have hpd : (3 : ℕ) ≠ d.1.characteristic := by
      rw [hd2]
      norm_num
    have hpil := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent
      (PSimple 3 K) hsimple hna d ⟨e⟩ 3 hp3 (by norm_num) hpd _ hη3 hη1
    have hcomp : ∀ {J : Subgroup Ω}, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J →
        CFSG.Open.IsComponentOf (chevTransfer 3 K J) (fixSubgroup (chevAut 3 K ⟨y, hyN⟩)) :=
      fun hJ => (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer
        (hJs hJ) (hpil _ (hJs hJ).1 (glaPComponent_perfect (hJs hJ)))).1
    have hη'D : MulAut.congr e (chevAut 3 K ⟨y, hyN⟩) ∈
        CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived
          (TauCeti.CFSGIndex.lie d).Group :=
      (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr e).2 hηD
    have hη'3 : MulAut.congr e (chevAut 3 K ⟨y, hyN⟩) ^ 3 = 1 := by
      rw [← map_pow, hη3, map_one]
    have hη'1 : MulAut.congr e (chevAut 3 K ⟨y, hyN⟩) ≠ 1 := fun h =>
      hη1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
    have hfix : fixSubgroup (MulAut.congr e (chevAut 3 K ⟨y, hyN⟩)) =
        (fixSubgroup (chevAut 3 K ⟨y, hyN⟩)).map
          (e : PSimple 3 K →* (TauCeti.CFSGIndex.lie d).Group) :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.fixSubgroup_congr e _
    have htrc : ∀ {J : Subgroup Ω}, GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J →
        CFSG.Open.IsComponentOf
          ((chevTransfer 3 K J).map (e : PSimple 3 K →* (TauCeti.CFSGIndex.lie d).Group))
          (fixSubgroup (MulAut.congr e (chevAut 3 K ⟨y, hyN⟩))) := by
      intro J hJ
      rw [hfix]
      exact CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map e (hcomp hJ)
    have htrinj : ∀ {J J' : Subgroup Ω},
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J →
        GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set Ω)) J' →
        (chevTransfer 3 K J).map (e : PSimple 3 K →* (TauCeti.CFSGIndex.lie d).Group) =
          (chevTransfer 3 K J').map (e : PSimple 3 K →* (TauCeti.CFSGIndex.lie d).Group) →
        J = J' := fun hJ hJ' h =>
      eq_of_chevTransfer_eq hp3 hyN hap hJ hJ' (Subgroup.map_injective e.injective h)
    have hres := hC d hd2 _ hη'D hη'3 hη'1 r hr_odd hr1 _ _ _
      (htrc hJ1) (htrc hJ2) (htrc hJ3)
      (fun h => h12 (htrinj hJ1 hJ2 h)) (fun h => h13 (htrinj hJ1 hJ3 h))
      (fun h => h23 (htrinj hJ2 hJ3 h))
      ((t1428u6_type_iff hyN hap hJ1 (hcomp hJ1) e _).1 hc1)
      ((t1428u6_type_iff hyN hap hJ2 (hcomp hJ2) e _).1 hc2)
      ((t1428u6_type_iff hyN hap hJ3 (hcomp hJ3) e _).1 hc3)
    rcases hres with ⟨hU6, hall⟩ | hD4
    · left
      refine ⟨(catalogIs_congr e).2 hU6, fun M hM => ?_⟩
      exact (t1428u6_type_iff hyN hap hM (hcomp hM) e _).2 (hall _ (htrc hM))
    · right
      exact (catalogIs_congr e).2 hD4
  ·
    exfalso
    have hfix : fixSubgroup (chevAut 3 K ⟨y, hyN⟩) ≠ ⊤ := by
      intro h
      apply hη1
      ext s
      have hs : s ∈ fixSubgroup (chevAut 3 K ⟨y, hyN⟩) := by
        rw [h]
        exact Subgroup.mem_top s
      exact CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup.1 hs
    have hlt : Nat.card ↥(chevTransfer 3 K J₁) < 60 := by
      rw [← h60]
      calc Nat.card ↥(chevTransfer 3 K J₁)
          ≤ Nat.card ↥(fixSubgroup (chevAut 3 K ⟨y, hyN⟩)) := Subgroup.card_le_of_le (hJs hJ1).1
        _ < Nat.card ↥(⊤ : Subgroup (PSimple 3 K)) :=
          Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hfix)
        _ = Nat.card (PSimple 3 K) := Subgroup.card_top
    haveI := CFSG.GroupTheory.groups_order_below_sixty_solvable hlt
    have hQs := isQuasisimple_pQuot_of_glaPComponent hp3 (hJs hJ1)
    haveI := hQs.2
    haveI : Nontrivial (PQuot 3 (chevTransfer 3 K J₁)) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 (chevTransfer 3 K J₁)))).nontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
      (PQuot 3 (chevTransfer 3 K J₁))).ne hQs.1
  ·
    exfalso
    have h1' : (canonLabel labL).n = 1 :=
      (CanonSubcomp.canonLabel_n_eq_markDeg hlamL hc).trans h1
    rw [h1'] at hdvdL
    exact hp3.ne_one (Nat.dvd_one.1 hdvdL)

end Certified

end CFSG.LocalAnalysis.GLTheoremA.T1428

end
