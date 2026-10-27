module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62yBasic
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62xDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem sr629_mem_normalizer_smallRankCenter {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) : g ∈ normalizer (smallRankCenter H : Set G) := by
  have key : ∀ g ∈ normalizer (H : Set G), ∀ y ∈ smallRankCenter H,
      g * y * g⁻¹ ∈ smallRankCenter H := by
    intro g hg y hy
    obtain ⟨hyH, hyC⟩ := hy
    refine ⟨(mem_normalizer_iff.mp hg y).mp hyH, mem_centralizer_iff.mpr fun h' hh' => ?_⟩
    have hh'' : g⁻¹ * h' * g ∈ H := by
      simpa using (mem_normalizer_iff.mp (inv_mem hg) h').mp hh'
    have hc : g⁻¹ * h' * g * y = y * (g⁻¹ * h' * g) := mem_centralizer_iff.mp hyC _ hh''
    calc h' * (g * y * g⁻¹) = g * (g⁻¹ * h' * g * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * h' * g)) * g⁻¹ := by rw [hc]
      _ = g * y * g⁻¹ * h' := by group
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem sr629_mem_normalizer_smallRankOmega (f : ℕ) {A : Subgroup G} {g : G}
    (hg : g ∈ normalizer (A : Set G)) : g ∈ normalizer (smallRankOmega f A : Set G) := by
  have key : ∀ g ∈ normalizer (A : Set G), ∀ y ∈ smallRankOmega f A,
      g * y * g⁻¹ ∈ smallRankOmega f A := by
    intro g hg y hy
    have hle : (smallRankOmega f A).map (MulAut.conj g).toMonoidHom ≤ smallRankOmega f A := by
      unfold smallRankOmega
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨a, ⟨haA, haf⟩, rfl⟩
      refine ⟨(mem_normalizer_iff.mp hg a).mp haA, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, conj_pow, haf]
      simp
    exact hle ⟨y, hy, rfl⟩
  rw [mem_normalizer_iff]
  intro y
  refine ⟨key g hg y, fun hy => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hy
  simpa [mul_assoc] using this

omit [Finite G] in
theorem sr629_isElemAbelian_omega_center (f : ℕ) (H : Subgroup G) :
    IsElemAbelian f (smallRankOmega f (smallRankCenter H)) := by
  have hcomm : ∀ a ∈ smallRankCenter H, ∀ b ∈ smallRankCenter H, a * b = b * a :=
    fun a ha b hb => mem_centralizer_iff.mp hb.2 a ha.1
  have key : ∀ y ∈ smallRankOmega f (smallRankCenter H), y ∈ smallRankCenter H ∧ y ^ f = 1 := by
    intro y hy
    unfold smallRankOmega at hy
    induction hy using Subgroup.closure_induction with
    | mem a ha => exact ⟨ha.1, ha.2⟩
    | one => exact ⟨one_mem _, one_pow _⟩
    | mul a b _ _ ha hb =>
      refine ⟨mul_mem ha.1 hb.1, ?_⟩
      rw [(show Commute a b from hcomm a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]
    | inv a _ ha => exact ⟨inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => (key y hy).2⟩
  exact hcomm a (key a a.2).1 b (key b b.2).1


theorem sr629_ne_prime {p f : ℕ} (hp : p.Prime) (hfp : f.Prime) (x : G)
    (hfD : pCoreOf f (smallRankD p x) ≠ ⊥) : f ≠ p := by
  intro hfp'
  have : Fact f.Prime := ⟨hfp⟩
  have : Fact p.Prime := ⟨hp⟩
  subst hfp'
  have hP := CFSG.LieType.BorelTits.pCoreOf_isPGroup f (smallRankD f x)
  have hle := CFSG.LieType.BorelTits.pCoreOf_le f (smallRankD f x)
  obtain ⟨-, -, hcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec f
    (centralizer ({x} : Set G))
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : Nat.card (pCoreOf f (smallRankD f x)) ∣ Nat.card (smallRankD f x) :=
    Subgroup.card_dvd_of_le hle
  have hcop' : Nat.Coprime f (Nat.card (pCoreOf f (smallRankD f x))) :=
    Nat.Coprime.coprime_dvd_right hdvd hcop
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · apply hfD
    apply Subgroup.eq_bot_of_card_eq
    rw [hn, h0, pow_zero]
  · rw [hn] at hcop'
    have h1 : Nat.Coprime f f :=
      Nat.Coprime.coprime_dvd_right (dvd_pow_self f hpos.ne') hcop'
    exact hfp.ne_one ((Nat.coprime_self f).mp h1)

theorem sr629_omega_center_ne_bot {f : ℕ} (hfp : f.Prime) {A : Subgroup G} (hA : IsPGroup f A)
    (hA1 : A ≠ ⊥) : smallRankOmega f (smallRankCenter A) ≠ ⊥ := by
  have : Fact f.Prime := ⟨hfp⟩
  have hnt : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
  have hZ : Nontrivial (center A) := hA.center_nontrivial
  have hdvd : f ∣ Nat.card (center A) :=
    (hA.to_subgroup _).card_eq_or_dvd.resolve_left fun h =>
      (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' h
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' f hdvd
  have hc' : orderOf ((c : A) : G) = f := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  have hcC : ((c : A) : G) ∈ smallRankCenter A := by
    refine ⟨(c : A).2, mem_centralizer_iff.mpr fun h hh => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨h, hh⟩)
  have hcf : ((c : A) : G) ^ f = 1 := by
    have h := pow_orderOf_eq_one ((c : A) : G)
    rwa [hc'] at h
  intro hbot
  have hmem : ((c : A) : G) ∈ smallRankOmega f (smallRankCenter A) :=
    Subgroup.subset_closure ⟨hcC, hcf⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hc'
  exact hfp.one_lt.ne hc'

omit [Finite G] in
theorem sr629_omega_center_le (f : ℕ) (A : Subgroup G) :
    smallRankOmega f (smallRankCenter A) ≤ A :=
  (Subgroup.closure_le A).mpr fun _ ha => ha.1.1

theorem sr629_centralizer_le_normalizer_F {p f : ℕ} (hp : p.Prime) (x : G) :
    centralizer ({x} : Set G) ≤ normalizer (smallRankF p f x : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  intro g hg
  have h1 : g ∈ normalizer (smallRankD p x : Set G) :=
    sr628_mem_normalizer_primeCore p (centralizer ({x} : Set G)) (Subgroup.le_normalizer hg)
  have h2 : g ∈ normalizer (pCoreOf f (smallRankD p x) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf f (smallRankD p x) h1
  exact sr629_mem_normalizer_smallRankOmega f (sr629_mem_normalizer_smallRankCenter h2)

theorem sr629_F_isPGroup {p f : ℕ} (hfp : f.Prime) (x : G) : IsPGroup f (smallRankF p f x) := by
  have : Fact f.Prime := ⟨hfp⟩
  exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup f (smallRankD p x)).to_le
    (sr629_omega_center_le f _)

theorem sr629_F_le_fitting {p f : ℕ} (hp : p.Prime) (hfp : f.Prime) (hf2 : f ≠ 2) (x : G) :
    smallRankF p f x ≤ CFSG.fittingSubgroupOf (rankThreePrimeCore 2 (smallRankD p x)) := by
  have : Fact f.Prime := ⟨hfp⟩
  have : Fact p.Prime := ⟨hp⟩
  have hAD : pCoreOf f (smallRankD p x) ≤ smallRankD p x :=
    CFSG.LieType.BorelTits.pCoreOf_le f (smallRankD p x)
  have hFA : smallRankF p f x ≤ pCoreOf f (smallRankD p x) := sr629_omega_center_le f _
  have hAOD : pCoreOf f (smallRankD p x) ≤ rankThreePrimeCore 2 (smallRankD p x) := by
    refine le_sSup ⟨hAD, ?_, ?_⟩
    · exact CFSG.RankThreeEvenClassification.Helpers.pCoreOf_normal_subgroupOf f
        (smallRankD p x) (smallRankD p x) le_rfl
        (by rw [Subgroup.subgroupOf_self]; infer_instance)
    · obtain ⟨n, hn⟩ :=
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup f (smallRankD p x)).exists_card_eq
      rw [hn]
      exact Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hfp).mpr (Ne.symm hf2))
  have hFOD : smallRankF p f x ≤ rankThreePrimeCore 2 (smallRankD p x) := hFA.trans hAOD
  have hDC : smallRankD p x ≤ centralizer ({x} : Set G) :=
    (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p (centralizer ({x} : Set G))).1
  have hODD : rankThreePrimeCore 2 (smallRankD p x) ≤ smallRankD p x :=
    (CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec 2 (smallRankD p x)).1
  have hODN : rankThreePrimeCore 2 (smallRankD p x) ≤ normalizer (smallRankF p f x : Set G) :=
    (hODD.trans hDC).trans (sr629_centralizer_le_normalizer_F hp x)
  have hnorm : ((smallRankF p f x).subgroupOf (rankThreePrimeCore 2 (smallRankD p x))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFOD).mpr hODN
  have : Group.IsNilpotent (smallRankF p f x) := (sr629_F_isPGroup (p := p) hfp x).isNilpotent
  have hnil : Group.IsNilpotent
      ((smallRankF p f x).subgroupOf (rankThreePrimeCore 2 (smallRankD p x))) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFOD).symm
  have hle : (smallRankF p f x).subgroupOf (rankThreePrimeCore 2 (smallRankD p x)) ≤
      CFSG.fittingSubgroup ↥(rankThreePrimeCore 2 (smallRankD p x)) :=
    le_sSup ⟨hnorm, hnil⟩
  have hmap := Subgroup.map_mono (f := (rankThreePrimeCore 2 (smallRankD p x)).subtype) hle
  rw [Subgroup.map_subgroupOf_eq_of_le hFOD] at hmap
  exact hmap

end CFSG.LocalAnalysis.RankThreeTheoremC
