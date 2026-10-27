module

public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Main27
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Core
public import CFSG.HardMathSupport.Solomon.Coordinator.I25_3Main512

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

@[expose] def SU38Trivial {Y : Type} [Group Y] [Finite Y] (A J : Subgroup Y) : Prop :=
  IsSU38 (barOf 3 J) → ∀ a ∈ A, ∀ h : a ∈ Subgroup.normalizer (J : Set Y), barAut 3 J ⟨a, h⟩ = 1

theorem i253_barAut_eq_one_of_centralizes {Y : Type} [Group Y] [Finite Y] {A J : Subgroup Y}
    (hA : A ≤ Subgroup.centralizer (J : Set Y)) {a : Y} (ha : a ∈ A)
    (h : a ∈ Subgroup.normalizer (J : Set Y)) : barAut 3 J ⟨a, h⟩ = 1 := by
  ext w
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective w
  rw [MulAut.one_apply]
  have h1 := barAut_mk 3 J ⟨a, h⟩ j
  rw [h1]
  congr 1
  apply Subtype.ext
  have hc := Subgroup.mem_centralizer_iff.1 (hA ha) (j : Y) j.2
  show a * (j : Y) * a⁻¹ = j
  rw [← hc]; group

theorem i253_su38Trivial_of_centralizes {Y : Type} [Group Y] [Finite Y] {A J : Subgroup Y}
    (hA : A ≤ Subgroup.centralizer (J : Set Y)) : SU38Trivial A J :=
  fun _ _ ha h => i253_barAut_eq_one_of_centralizes hA ha h

@[expose] def Input25_3_512 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K J A : Subgroup Y) (b : Y) (hbJ : b ∈ J),
    CFSG.Open.IsQuasisimple ↥K → CFSG.Open.IsKGroup ↥K → GLAPPrimeCore 3 ↥K = ⊥ → b ∈ K →
    orderOf b = 3 →
    CFSG.Open.IsComponentOf J (GLALayer (K ⊓ Subgroup.centralizer ({b} : Set Y))) →
    IsSLThreeEpsAny (barOf 3 J) →
    Subgroup.center (barOf 3 J) = Subgroup.zpowers (QuotientGroup.mk (⟨b, hbJ⟩ : ↥J)) →
    A ≤ Subgroup.normalizer (K : Set Y) → CFSG.Open.IsElemAbelian 3 A → Nat.card A = 9 →
    b ∈ A → (∀ a ∈ A, a ≠ 1 → InducesFieldAut 3 J a) → SU38Trivial A J →
      J = K ∨ ∃ a ∈ A, a ≠ 1 ∧ b ∉ oPrimePOf 3 (K ⊓ Subgroup.centralizer ({a} : Set Y))

@[expose] def Input25_3_27 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K J A : Subgroup Y) (b : Y),
    CFSG.IsQuasisimple ↥K → CFSG.IsKGroup ↥K → b ∈ K → orderOf b = 3 →
    CFSG.Open.IsComponentOf J (K ⊓ Subgroup.centralizer ({b} : Set Y)) →
    ∀ hbJ : b ∈ J, Lemma27Ns.IsSL3Eps (↥J ⧸ GLAPPrimeCore 3 ↥J) →
    Subgroup.center (↥J ⧸ GLAPPrimeCore 3 ↥J) =
      Subgroup.zpowers (QuotientGroup.mk (⟨b, hbJ⟩ : ↥J)) →
    A ≤ Subgroup.normalizer (K : Set Y) → CFSG.Open.IsElemAbelian 3 A → Nat.card A = 9 →
    b ∈ A → (∀ a ∈ A, a ≠ 1 → InducesFieldAut 3 J a) → SU38Trivial A J →
    J = K ∨ ∃ a ∈ A, a ≠ 1 ∧ b ∉ oPrimePOf 3 (K ⊓ Subgroup.centralizer ({a} : Set Y))

theorem input25_3_of_residuals' (hF : Input25_3FactsNo38)
    (h181 : LocalBalance.Lemma514CoverNs.Input18_1) (hB : B3Quasi) : Input25_3_512 := by
  intro Y _ _ K J A b hbJ hKq hKK _ hbK hb3 hJ hJT hZ hAN hAel hA9 hbA hfield hU8
  exact input25_3_core hF h181 hB hKq hKK hbK hb3 (i253_isComponentOf_of_layer hJ) hbJ hJT hZ hAN
    hAel hA9 hbA hfield hU8

theorem input25_3_of_residuals_27' (hF : Input25_3FactsNo38)
    (h181 : LocalBalance.Lemma514CoverNs.Input18_1) (hB : B3Quasi) : Input25_3_27 := by
  intro Y _ _ K J A b hKq hKK hbK hb3 hJ hbJ hSL hZ hAN hAel hA9 hbA hfield hU8
  have hKq' : CFSG.Open.IsQuasisimple ↥K := by
    obtain ⟨hperf, hsimple, -⟩ := hKq
    exact ⟨hperf.commutator_eq_top, hsimple⟩
  have hKK' : CFSG.Open.IsKGroup ↥K := fun K' L _ _ hs _ => hKK K' (L.subgroupOf K') hs
  have hb3' : b ^ 3 = 1 := by have := pow_orderOf_eq_one b; rwa [hb3] at this
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb3; omega
  have h3J : 3 ∣ Nat.card ↥J := by
    have : orderOf (⟨b, hbJ⟩ : ↥J) = 3 := by
      rw [orderOf_eq_prime_iff]
      exact ⟨Subtype.ext (by simpa using hb3'), fun h => hb1 (congrArg Subtype.val h)⟩
    rw [← this]; exact orderOf_dvd_natCard _
  have hcomp : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({b} : Set Y)) J :=
    i253_glaPComponent_of_subnormal hJ.1 hJ.2.1 hJ.2.2 h3J
  have hJbar : CFSG.Open.IsQuasisimple (barOf 3 J) :=
    LocalBalance.isQuasisimple_quotient_of_glaPComponent hcomp
  exact input25_3_core hF h181 hB hKq' hKK' hbK hb3 hJ hbJ (i253_any_of_isSL3Eps hJbar hSL) hZ hAN
    hAel hA9 hbA hfield hU8

end CFSG.HardMathSupport.Solomon.Coordinator
