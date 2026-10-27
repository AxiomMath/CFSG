module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabPrime
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open CFSG.RankThree.PartOne.OutStructure (OutPNice Inn)
open scoped commutatorElement

class OddPrime (p : ℕ) : Prop where
  prime : p.Prime
  odd : Odd p

instance : OddPrime 5 := ⟨by norm_num, by decide⟩

instance (priority := low) OddPrime.fact {p : ℕ} [OddPrime p] : Fact p.Prime :=
  ⟨OddPrime.prime⟩

theorem OddPrime.odd_pow (p : ℕ) [OddPrime p] (k : ℕ) : Odd (p ^ k) :=
  (OddPrime.odd (p := p)).pow

theorem OddPrime.ne_two (p : ℕ) [OddPrime p] : p ≠ 2 := by
  rintro rfl
  exact absurd (OddPrime.odd (p := 2)) (by decide)

theorem OddPrime.three_le (p : ℕ) [OddPrime p] : 3 ≤ p := by
  have h2 := (OddPrime.prime (p := p)).two_le
  have h3 := OddPrime.ne_two p
  omega

theorem exists_normal_index_prime {p : ℕ} [Fact p.Prime] {Y Γ : Type*} [Group Y] [Finite Y]
    [Group Γ] [Finite Γ] (φ : Y →* Γ) {D : Subgroup Γ} (hD : PCentral p D) {a : Y}
    (ha3 : IsPGroup p (Subgroup.zpowers a)) (hφa : φ a ∉ D) :
    ∃ N : Subgroup Y, N.Normal ∧ N.index = p := by
  classical
  haveI : D.Normal := hD.1
  set q : Y →* Γ ⧸ D := (QuotientGroup.mk' D).comp φ with hq
  have hqa : q a ≠ 1 := fun h => hφa ((QuotientGroup.eq_one_iff _).1 h)
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hqak : (q a) ^ (p ^ k) = 1 := by rw [← map_pow, hak, map_one]
  have hcent : ∀ y : Γ ⧸ D, (∃ k : ℕ, y ^ (p ^ k) = 1) → y ∈ Subgroup.center (Γ ⧸ D) := by
    rintro y ⟨k, hk⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 : ⁅γ, g⁆ ∈ D := hD.2 g ⟨k, by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact hk⟩ γ
    have h2 : ⁅(QuotientGroup.mk' D γ), (QuotientGroup.mk' D g)⁆ = 1 := by
      rw [← map_commutatorElement]; exact (QuotientGroup.eq_one_iff _).2 h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  obtain ⟨S⟩ : Nonempty (Sylow p (Γ ⧸ D)) := inferInstance
  have hSc : (S : Subgroup (Γ ⧸ D)) ≤ Subgroup.center (Γ ⧸ D) := by
    intro s hs
    apply hcent
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hS : Subgroup.normalizer ((S : Subgroup (Γ ⧸ D)) : Set (Γ ⧸ D)) ≤
      Subgroup.centralizer ((S : Subgroup (Γ ⧸ D)) : Set (Γ ⧸ D)) := by
    intro n _
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (Subgroup.mem_center_iff.1 (hSc hs) n).symm
  let T : Γ ⧸ D →* S := MonoidHom.transferSylow S hS
  let t : Y →* S := T.comp q
  have hdisj := MonoidHom.ker_transferSylow_disjoint S hS (Subgroup.zpowers (q a)) (by
    rintro ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    exact ⟨k, Subtype.ext (by
      show (q a ^ m) ^ p ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hqak, one_zpow])⟩)
  have hta : t a ≠ 1 := by
    intro h
    have hmem : q a ∈ T.ker := by rw [MonoidHom.mem_ker]; exact h
    exact hqa (Subgroup.disjoint_def.1 hdisj hmem (Subgroup.mem_zpowers _))
  have htak : (t a) ^ (p ^ k) = 1 := by rw [← map_pow, hak, map_one]
  have hB3 : IsPGroup p t.range := S.isPGroup'.of_injective t.range.subtype
    (Subgroup.subtype_injective _)
  haveI : Group.IsNilpotent t.range := hB3.isNilpotent
  have hd3 : p ∣ Nat.card t.range := by
    have h1 : orderOf (t a) ∣ p ^ k := orderOf_dvd_of_pow_eq_one htak
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).1 h1
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hta (orderOf_eq_one_iff.1 (by simpa using hj))
    have h2 : orderOf (⟨t a, MonoidHom.mem_range.2 ⟨a, rfl⟩⟩ : t.range) = p ^ j := by
      rw [← hj, ← Subgroup.orderOf_coe]
    have h3 := orderOf_dvd_natCard (⟨t a, MonoidHom.mem_range.2 ⟨a, rfl⟩⟩ : t.range)
    rw [h2] at h3
    exact (dvd_pow_self p hj0).trans h3
  obtain ⟨M, hMi, hMn⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card hd3
  refine ⟨M.comap t.rangeRestrict, Subgroup.Normal.comap hMn _, ?_⟩
  rw [Subgroup.index_comap_of_surjective _ t.rangeRestrict_surjective, hMi]

section Levi

variable {Y : Type} [Group Y]

@[expose] def LeviInnAtP (p : ℕ) (P : Subgroup Y) : Prop :=
  ∀ l ∈ P, ∀ k : ℕ, (∀ w ∈ perfectJoin P, ⁅l ^ (p ^ k), w⁆ = 1) →
    ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅l * v, w⁆ ∈ pCoreOf 2 (perfectJoin P)

variable [Finite Y]

theorem actsInnerly_of_innP {p : ℕ} {L P : Subgroup Y} [L.Normal] (hCP : CompParab L P)
    (hLevi : LeviInnAtP p P) {a : Y} (ha3 : IsPGroup p (Subgroup.zpowers a))
    (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hin : convAut L a ∈ Inn (↥L ⧸ Subgroup.center ↥L)) :
    ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P) := by
  have hPL : P ≤ L := hCP.parab.1
  obtain ⟨l₀, hc⟩ := exists_mem_centralizer_of_convAut_mem_inn L hCP.comp.2.2.1 hin
  set c : Y := a * (l₀ : Y)⁻¹ with hcdef
  have hcL : ∀ x ∈ L, x * c = c * x := fun x hx => Subgroup.mem_centralizer_iff.1 hc x hx
  have hac : a = c * (l₀ : Y) := by rw [hcdef]; group
  have hconj : ∀ h : Y, h ∈ L → (l₀ : Y) * h * (l₀ : Y)⁻¹ = a * h * a⁻¹ := by
    intro h hh
    have hX : (l₀ : Y) * h * (l₀ : Y)⁻¹ ∈ L := L.mul_mem (L.mul_mem l₀.2 hh) (L.inv_mem l₀.2)
    have key : c * ((l₀ : Y) * h * (l₀ : Y)⁻¹) * c⁻¹ = (l₀ : Y) * h * (l₀ : Y)⁻¹ := by
      rw [← hcL _ hX]; group
    rw [hac]
    calc (l₀ : Y) * h * (l₀ : Y)⁻¹ = c * ((l₀ : Y) * h * (l₀ : Y)⁻¹) * c⁻¹ := key.symm
      _ = c * (l₀ : Y) * h * (c * (l₀ : Y))⁻¹ := by group
  have hl₀N : (l₀ : Y) ∈ Subgroup.normalizer (P : Set Y) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hconj h (hPL hh)]
      exact (Subgroup.mem_normalizer_iff.1 haN h).1 hh
    · intro hh
      have hhL : h ∈ L := by
        have := L.mul_mem (L.mul_mem (L.inv_mem l₀.2) (hPL hh)) l₀.2
        simpa [mul_assoc] using this
      rw [hconj h hhL] at hh
      exact (Subgroup.mem_normalizer_iff.1 haN h).2 hh
  have hl₀P : (l₀ : Y) ∈ P :=
    CFSG.HardMathSupport.Curtis.UnitaryLevi.mem_of_mem_normalizer_of_isParabolicTwo hCP.parab
      l₀.2 hl₀N
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hcomm : Commute c (l₀ : Y) := (hcL _ l₀.2).symm
  have hpow : (l₀ : Y) ^ (p ^ k) = (c ^ (p ^ k))⁻¹ := by
    rw [hac, hcomm.mul_pow] at hak
    exact eq_inv_of_mul_eq_one_right hak
  have hVL : perfectJoin P ≤ L := (perfectJoin_le P).trans hPL
  obtain ⟨v, hv, hvw⟩ := hLevi _ hl₀P k fun w hw => by
    have h1 : Commute (c ^ (p ^ k)) w := Commute.pow_left (hcL w (hVL hw)).symm _
    rw [commutatorElement_eq_one_iff_mul_comm, hpow]
    exact h1.inv_left.eq
  refine ⟨v, hv, fun w hw => ?_⟩
  have hvL : v ∈ L := hVL hv
  have hwL : w ∈ L := hVL hw
  have hX : (l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem (L.mul_mem (L.mul_mem l₀.2 hvL) hwL) (L.inv_mem hvL)) (L.inv_mem l₀.2)
  have hkey : c * ((l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹) * c⁻¹ =
      (l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹ := by
    rw [← hcL _ hX]; group
  have : ⁅a * v, w⁆ = ⁅(l₀ : Y) * v, w⁆ := by
    rw [commutatorElement_def, commutatorElement_def, hac]
    calc c * (l₀ : Y) * v * w * (c * (l₀ : Y) * v)⁻¹ * w⁻¹
        = (c * ((l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹) * c⁻¹) * w⁻¹ := by group
      _ = ((l₀ : Y) * v * w * v⁻¹ * (l₀ : Y)⁻¹) * w⁻¹ := by rw [hkey]
      _ = (l₀ : Y) * v * w * ((l₀ : Y) * v)⁻¹ * w⁻¹ := by group
  rw [this]
  exact hvw w hw

theorem fieldIndex_coreP {p : ℕ} [Fact p.Prime] {L P : Subgroup Y} [L.Normal]
    {D : Subgroup (MulAut (↥L ⧸ Subgroup.center ↥L))} (hD : PCentral p D) {a : Y}
    (ha3 : IsPGroup p (Subgroup.zpowers a))
    (hout : ¬ ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P))
    (hLevi : convAut L a ∈ D →
      ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P)) :
    ∃ N : Subgroup Y, N.Normal ∧ N.index = p := by
  have : Finite (↥L ⧸ Subgroup.center ↥L) := inferInstance
  by_cases h : convAut L a ∈ D
  · exact absurd (hLevi h) hout
  · exact exists_normal_index_prime (convAut L) hD ha3 h

theorem fieldIndex_of_outPNiceP {p : ℕ} [Fact p.Prime] {L P : Subgroup Y} [L.Normal]
    (hCP : CompParab L P) (hO : OutPNice p (↥L ⧸ Subgroup.center ↥L))
    (hLevi : LeviInnAtP p P) {a : Y}
    (ha3 : IsPGroup p (Subgroup.zpowers a)) (haN : a ∈ Subgroup.normalizer (P : Set Y))
    (hout : ¬ ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P)) :
    ∃ N : Subgroup Y, N.Normal ∧ N.index = p := by
  obtain ⟨D, hD, hID, hD2⟩ := pCentral_of_outPNice hO
  refine fieldIndex_coreP hD ha3 hout fun hmem => ?_
  obtain ⟨k, hk⟩ := ha3 ⟨a, Subgroup.mem_zpowers a⟩
  have hak : a ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  refine actsInnerly_of_innP hCP hLevi ha3 haN (hD2 _ hmem k ?_)
  rw [← map_pow, hak, map_one]
  exact Subgroup.one_mem _

end Levi

section Families

@[expose] def FieldIndexAtP (p : ℕ) {Y : Type} [Group Y] [Finite Y] (L P : Subgroup Y) : Prop :=
  L.Normal → (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) →
    p ∣ Nat.card (perfectJoin P) → Open.pRank p (perfectJoin P) ≤ 1 →
    ∀ a : Y, IsPGroup p (Subgroup.zpowers a) → a ∈ Subgroup.normalizer (P : Set Y) →
    (¬ ∃ v ∈ perfectJoin P, ∀ w ∈ perfectJoin P, ⁅a * v, w⁆ ∈ pCoreOf 2 (perfectJoin P)) →
    ∃ N : Subgroup Y, N.Normal ∧ N.index = p

@[expose] def FieldIndexOnP (p : ℕ) (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → FieldIndexAtP p L P

@[expose] def LeviInnOnP (p : ℕ) (C : (X : Type) → [Group X] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
    C (↥L ⧸ Subgroup.center ↥L) → L.Normal → (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) →
    p ∣ Nat.card (perfectJoin P) → Open.pRank p (perfectJoin P) ≤ 1 → LeviInnAtP p P

theorem fieldIndexOnP_of_outPNice {p : ℕ} [Fact p.Prime] {C : (X : Type) → [Group X] → Prop}
    (hT : ∀ (Y : Type) [Group Y] [Finite Y] (L P : Subgroup Y), CompParab L P →
      C (↥L ⧸ Subgroup.center ↥L) → (∀ q : ℕ, q.Prime → q ≠ 2 → Open.pRank q L ≤ 3) →
      OutPNice p (↥L ⧸ Subgroup.center ↥L))
    (hL : LeviInnOnP p C) : FieldIndexOnP p C := by
  intro Y _ _ L P hCP hC hLn hrank h3 hrk a ha3 haN hout
  haveI := hLn
  exact fieldIndex_of_outPNiceP hCP (hT Y L P hCP hC hrank) (hL Y L P hCP hC hLn hrank h3 hrk)
    ha3 haN hout

end Families

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
