module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalGroups.UnitaryFlag.SplitTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial

variable {p f : ℕ} {K : Type} [Field K] {r ε : ℕ}

theorem exists_piSubgroup_three_le_pRank_in_borel_projective_unitary_split
    (h : UnitaryFieldData p f K) {r ε : ℕ} (hr : 3 ≤ r) (hε : ε ≤ 1)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hdvd : q ∣ p ^ f - 1) :
    ∃ Hc : Subgroup (hypPSU h r ε),
      Hc ≤ Subgroup.normalizer (hypProjUnitriangular h r ε : Set (hypPSU h r ε)) ∧
      IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc ∧
      3 ≤ CFSG.Open.pRank q Hc := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite K := h.finite
  have hr1 : 1 ≤ r := by omega
  haveI := finite_hypSU (r := r) (ε := ε) h
  haveI : Finite (hypPSU h r ε) :=
    Finite.of_surjective (hypProj h r ε) (hypProj_surjective h r ε)
  have hdvdK : q ∣ Nat.card K - 1 := by
    rw [h.card, show 2 * f = f * 2 by ring, pow_mul]
    have hsq : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
      rw [mul_comm, ← Nat.sq_sub_sq (p ^ f) 1, one_pow]
    rw [hsq]
    exact dvd_mul_of_dvd_left hdvd _
  have hdvd' : q ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hdvdK
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' q hdvd'
  have hζq : ζ ^ q = 1 := by rw [← hζ, pow_orderOf_eq_one]
  let μ : Subgroup Kˣ := Subgroup.zpowers ζ
  have hμcard : Nat.card μ = q := by
    change Nat.card (Subgroup.zpowers ζ) = q
    rw [Nat.card_zpowers, hζ]
  have hμsplit : SplitInv h μ := by
    change SplitInv h (Subgroup.zpowers ζ)
    exact splitInv_zpowers h (d := q) hq.one_lt hζq hdvd
  have hoddμ : Odd (Nat.card μ) := by
    rw [hμcard]
    exact hq.odd_of_ne_two hq2
  let E : Subgroup (hypSU h r ε) := (splitTorusHom h r ε μ hμsplit).range
  have hEcard : Nat.card E = q ^ r := by
    change Nat.card (splitTorusHom h r ε μ hμsplit).range = q ^ r
    rw [splitTorusHom_range_card hμsplit, hμcard]
  have hEsub : E ≤ hypTorus h r ε := by
    rintro _ ⟨x, rfl⟩
    exact splitTorusHom_mem_hypTorus hμsplit x
  have hEel : IsElemAbelian q E :=
    splitTorusHom_range_isElemAbelian hμsplit fun a => by
      rw [← hμcard]
      exact pow_card_eq_one'
  have hker : ∀ s : hypSU h r ε, hypProj h r ε s = 1 → s ∈ hypScalars h r ε := by
    intro s hs
    have hs' : s ∈ MonoidHom.ker (hypProj h r ε) := MonoidHom.mem_ker.mpr hs
    rwa [ker_hypProj h r ε] at hs'
  have hinj : Function.Injective
      ((hypProj h r ε).comp (splitTorusHom h r ε μ hμsplit)) :=
    splitTorusHom_comp_injective hμsplit hoddμ (hypProj h r ε) hker
  let Hc : Subgroup (hypPSU h r ε) := E.map (hypProj h r ε)
  have hHccard : Nat.card Hc = q ^ r := by
    let e : E → Hc := fun x =>
      ⟨hypProj h r ε x, Subgroup.mem_map_of_mem (hypProj h r ε) x.2⟩
    have he_inj : Function.Injective e := by
      intro x y hxy
      have hxE : (x : hypSU h r ε) ∈ (splitTorusHom h r ε μ hμsplit).range := x.2
      have hyE : (y : hypSU h r ε) ∈ (splitTorusHom h r ε μ hμsplit).range := y.2
      obtain ⟨a, ha⟩ := hxE
      obtain ⟨b, hb⟩ := hyE
      have hπ : hypProj h r ε (splitTorusHom h r ε μ hμsplit a) =
          hypProj h r ε (splitTorusHom h r ε μ hμsplit b) := by
        rw [ha, hb]
        exact congrArg Subtype.val hxy
      have hab : a = b := hinj hπ
      apply Subtype.ext
      calc (x : hypSU h r ε) = splitTorusHom h r ε μ hμsplit a := ha.symm
        _ = splitTorusHom h r ε μ hμsplit b := by rw [hab]
        _ = (y : hypSU h r ε) := hb
    have he_surj : Function.Surjective e := by
      intro y
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
    have hcard_eq : Nat.card E = Nat.card Hc :=
      Nat.card_congr (Equiv.ofBijective e ⟨he_inj, he_surj⟩)
    rw [← hcard_eq, hEcard]
  have hHcel : IsElemAbelian q Hc := CFSG.SectionRank.isElemAbelian_map hEel (hypProj h r ε)
  have hHcle : Hc ≤ Subgroup.normalizer
      (hypProjUnitriangular h r ε : Set (hypPSU h r ε)) := by
    have hEB : E ≤ hypBorel h r ε := fun x hx => hypTorus_le_hypBorel h (hEsub hx)
    calc Hc = E.map (hypProj h r ε) := rfl
      _ ≤ (hypBorel h r ε).map (hypProj h r ε) := Subgroup.map_mono hEB
      _ = hypProjBorel h r ε := rfl
      _ = Subgroup.normalizer (hypProjUnitriangular h r ε : Set (hypPSU h r ε)) :=
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.normalizer_hypProjUnitriangular
          h hr1 hε).symm
  have hHcpi : IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc := by
    intro s hs
    change (s : ℕ) ≠ 2
    rw [hHccard] at hs
    have hsq : (s : ℕ) ∣ q := s.2.dvd_of_dvd_pow hs
    have hseq : (s : ℕ) = q := (Nat.prime_dvd_prime_iff_eq s.2 hq).mp hsq
    rw [hseq]
    exact hq2
  have hrank : r ≤ CFSG.Open.pRank q Hc :=
    CFSG.SectionRank.le_pRank hq.one_lt le_rfl hHcel hHccard
  exact ⟨Hc, hHcle, hHcpi, le_trans hr hrank⟩

end CFSG.ClassicalGroups.UnitaryFlag
