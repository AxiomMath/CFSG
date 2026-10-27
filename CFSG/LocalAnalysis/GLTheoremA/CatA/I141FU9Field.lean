module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Char
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FU9Small

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup lieOrderBridge_holds)

open CFSG.LocalAnalysis.GLTheoremA.I2018 (catalogIs_congr' fixSubgroup_one_eq_top)


theorem u9_fieldSize_eq_two_pow {d : TauCeti.LieTypeIndex} (hd : d.characteristic = 2) :
    KD264Lie.fieldSize d = 2 ^ (CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf d).2.2 := by
  cases d with
  | A r q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | twistedA r q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | B r q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | C r q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | D r q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | twistedD r q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | E6 q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | E7 q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | E8 q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | F4 q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | G2 q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | twistedE6 q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | trialityD4 q =>
    have hp : q.p = 2 := by simpa using hd
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf, hp]
  | suzuki m =>
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf]
  | reeG2 m => simp at hd
  | reeF4 m =>
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf]
  | tits =>
    simp [KD264Lie.fieldSize, CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf]

section CardAlphaOne


theorem u9_card_of_chevAut_eq_one {Γ : Type} [Group Γ] [Finite Γ] {K J : Subgroup Γ} {x : Γ} (hx : x ^ 3 = 1)
    (hI1 : S10.InnDiagOn 3 (Subgroup.zpowers x) K)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J)
    (hJU : catalogIs (PSimple 3 J) S9.isU3eight)
    (hα1 : chevAut 3 K ⟨x, hI1.1 (Subgroup.mem_zpowers x)⟩ = 1) :
    Nat.card (PSimple 3 K) = 5515776 := by
  obtain ⟨hs, hna⟩ := u9_simple_nonabelian hI1
  obtain ⟨hα3, hJ', ⟨eJ⟩⟩ := u9_transfer_chev hx hI1 hJ
  have hU' : catalogIs (PSimple 3 (chevTransfer 3 K J)) S9.isU3eight := catalogIs_congr' eJ hJU
  haveI := hs
  have hI : GLAPComponent 3 (⊤ : Subgroup (PSimple 3 K)) (chevTransfer 3 K J) := by
    rw [hα1, fixSubgroup_one_eq_top] at hJ'
    exact hJ'
  obtain ⟨eT⟩ := chevQ_pSimple_top_equiv Nat.prime_three hna hI
  rw [← Nat.card_congr eT.toEquiv]
  exact CatSingle.card_isU3eight lieOrderBridge_holds hU'

end CardAlphaOne

section Certs


theorem u9_field_cases {Γ : Type} [Group Γ] [Finite Γ] {K J : Subgroup Γ} {x : Γ} (hx : x ^ 3 = 1)
    (hI1 : S10.InnDiagOn 3 (Subgroup.zpowers x) K)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J)
    (hJU : catalogIs (PSimple 3 J) S9.isU3eight) {d : TauCeti.ValidLieTypeIndex}
    (e : PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hα1 : chevAut 3 K ⟨x, hI1.1 (Subgroup.mem_zpowers x)⟩ ≠ 1) :
    d.1.characteristic = 2 ∧ (KD264Lie.fieldSize d.1 = 2 ∨ KD264Lie.fieldSize d.1 = 8 ∨
      ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ q.card = 512) := by
  obtain ⟨hs, hna⟩ := u9_simple_nonabelian hI1
  obtain ⟨hα3, hJ', ⟨eJ⟩⟩ := u9_transfer_chev hx hI1 hJ
  have hU' : catalogIs (PSimple 3 (chevTransfer 3 K J)) S9.isU3eight := catalogIs_congr' eJ hJU
  have hdvd0 : 5515776 ∣ Nat.card (PSimple 3 K) := u9_dvd_card lieOrderBridge_holds hU'
  have hchar2 : d.1.characteristic = 2 := by
    rcases u9_char_two hI1 e with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd Nat.card_pos hdvd0) (by omega)
  refine ⟨hchar2, ?_⟩
  obtain ⟨-, -, -, -, hdiv | ⟨hPSU, hr, hf⟩⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.I2018Core.field_bound hs hna d hchar2 e hα3 hα1 hJ' hU'
  · rcases (Nat.dvd_prime Nat.prime_three).1 hdiv with h1 | h3
    · left
      rw [u9_fieldSize_eq_two_pow hchar2, h1]
      norm_num
    · right; left
      rw [u9_fieldSize_eq_two_pow hchar2, h3]
      norm_num
  · right; right
    obtain ⟨d0, hv⟩ := d
    cases d0 with
    | twistedA r q =>
      have hp : q.p = 2 := by simpa using hchar2
      have hr' : r + 1 = 3 := by simpa [CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf] using hr
      have hf' : q.exponent = 9 := by simpa [CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf] using hf
      obtain rfl : r = 2 := by omega
      refine ⟨q, rfl, ?_⟩
      rw [TauCeti.PrimePower.card_def, hp, hf']
      norm_num
    | _ => simp [CFSG.LocalAnalysis.GLTheoremA.I2018Core.specOf] at hPSU

theorem u9_lie_cases {Γ : Type} [Group Γ] [Finite Γ] {K J : Subgroup Γ} {x : Γ} (hx : x ^ 3 = 1)
    (hI1 : S10.InnDiagOn 3 (Subgroup.zpowers x) K)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({x} : Set Γ)) J)
    (hJU : catalogIs (PSimple 3 J) S9.isU3eight) {d : TauCeti.ValidLieTypeIndex}
    (e : PSimple 3 K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    d.1.characteristic = 2 ∧
      ((chevAut 3 K ⟨x, hI1.1 (Subgroup.mem_zpowers x)⟩ = 1 ∧ Nat.card (PSimple 3 K) = 5515776) ∨
        (chevAut 3 K ⟨x, hI1.1 (Subgroup.mem_zpowers x)⟩ ≠ 1 ∧
          (KD264Lie.fieldSize d.1 = 2 ∨ KD264Lie.fieldSize d.1 = 8 ∨
            ∃ q : TauCeti.PrimePower, d.1 = .twistedA 2 q ∧ q.card = 512))) := by
  by_cases hα1 : chevAut 3 K ⟨x, hI1.1 (Subgroup.mem_zpowers x)⟩ = 1
  · refine ⟨?_, Or.inl ⟨hα1, u9_card_of_chevAut_eq_one hx hI1 hJ hJU hα1⟩⟩
    obtain ⟨hs, hna⟩ := u9_simple_nonabelian hI1
    obtain ⟨hα3, hJ', ⟨eJ⟩⟩ := u9_transfer_chev hx hI1 hJ
    have hU' : catalogIs (PSimple 3 (chevTransfer 3 K J)) S9.isU3eight := catalogIs_congr' eJ hJU
    have hdvd0 : 5515776 ∣ Nat.card (PSimple 3 K) := u9_dvd_card lieOrderBridge_holds hU'
    rcases u9_char_two hI1 e with h | h
    · exact h
    · exact absurd (Nat.le_of_dvd Nat.card_pos hdvd0) (by omega)
  · obtain ⟨hchar, hf⟩ := u9_field_cases hx hI1 hJ hJU e hα1
    exact ⟨hchar, Or.inr ⟨hα1, hf⟩⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.I141F
