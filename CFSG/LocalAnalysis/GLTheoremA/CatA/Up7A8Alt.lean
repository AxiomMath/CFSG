module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Root
public import CFSG.LocalAnalysis.GLTheoremA.CatC.ChevQ
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open CFSG.LocalAnalysis.GLTheoremA.AltDown
open Equiv Equiv.Perm
open scoped commutatorElement

theorem up7a8_char_prime (d : TauCeti.LieTypeIndex) : d.characteristic.Prime := by
  cases d <;> simp <;> first | exact ‹TauCeti.PrimePower›.prime_p | exact Nat.prime_two | exact Nat.prime_three

theorem up7a8_zpowers_elemAb {G : Type} [Group G] {y : G} (hyp : y ^ 3 = 1) :
    IsElemAbelian 3 (Subgroup.zpowers y) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    show (a : G) * b = b * a
    rw [← hm, ← hn]
    exact (Commute.refl y).zpow_zpow m n |>.eq
  · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyp, one_zpow]

theorem up7a8_psimple_iso_of_pQuot {G : Type} [Group G] [Finite G] {J : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (e : PQuot 3 J ≃* alternatingGroup (Fin n)) : Nonempty (PSimple 3 J ≃* alternatingGroup (Fin n)) := by
  have hZ : Subgroup.center (PQuot 3 J) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    have h1 : e q ∈ Subgroup.center (alternatingGroup (Fin n)) := by
      rw [Subgroup.mem_center_iff] at hq ⊢
      intro g
      obtain ⟨u, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hq u]
    rw [alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega),
      Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact e.injective (h1.trans (map_one e).symm)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans e)⟩

theorem up7a8_psimple_root {G : Type} [Group G] [Finite G] {X K J : Subgroup G} {y : G} {n : ℕ}
    (hn : 5 ≤ n) (hK : GLAPComponent 3 X K) (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyp : y ^ 3 = 1)
    (hncent : ¬ CentMod 3 K y) (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (e : PSimple 3 K ≃* alternatingGroup (Fin n)) :
    ∃ m k : ℕ, 5 ≤ m ∧ 0 < k ∧ n = m + 3 * k ∧ Nonempty (PSimple 3 J ≃* alternatingGroup (Fin m)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyp' : IsPGroup 3 (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hα3 : chevAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := chevAut_pow_eq_one 3 K hyN hyp
  have hα1 : chevAut 3 K ⟨y, hyN⟩ ≠ 1 := fun h =>
    hncent ((chevAut_eq_one_iff Nat.prime_three hK hyN).1 h)
  have hJ' := glaPComponent_chevTransfer Nat.prime_three hyN hyp' hJ
  obtain ⟨hJe, ⟨eP⟩⟩ := chevQ_transport Nat.prime_three e hJ'
  have hβ3 : MulAut.congr e (chevAut 3 K ⟨y, hyN⟩) ^ 3 = 1 := by rw [← map_pow, hα3, map_one]
  have hβ1 : MulAut.congr e (chevAut 3 K ⟨y, hyN⟩) ≠ 1 := fun h =>
    hα1 ((MulAut.congr e).injective (h.trans (map_one _).symm))
  obtain ⟨m, k, hm5, hk0, hnk, ⟨eI⟩⟩ := up7a8_kdAltExact hn Nat.prime_three (by norm_num) hβ3 hβ1 hJe
  haveI : IsSimpleGroup (alternatingGroup (Fin m)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hcA : Subgroup.center (alternatingGroup (Fin m)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  obtain ⟨eJP⟩ := nonempty_pSimple_equiv_chevTransfer Nat.prime_three hyN hyp' hJ
  obtain ⟨eIP⟩ := nonempty_pSimple_equiv Nat.prime_three hJe hcA eI
  exact ⟨m, k, hm5, hk0, hnk, ⟨eJP.trans (eP.trans eIP)⟩⟩

theorem up7a8_pQuot_alt_of_center {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hK : GLAPComponent 3 X K) {n : ℕ} (hn : 8 ≤ n) (e : PSimple 3 K ≃* alternatingGroup (Fin n)) :
    Nonempty (PQuot 3 K ≃* alternatingGroup (Fin n)) := by
  have hZ := up7a8_center_bot hK hn e
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e⟩

theorem up7a8_imageMod_alt {G : Type} [Group G] [Finite G] {X K J : Subgroup G} {y : G} {n : ℕ}
    (hn : 5 ≤ n) (hK : GLAPComponent 3 X K) (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyp : y ^ 3 = 1)
    (hncent : ¬ CentMod 3 K y) (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set G)) J)
    (eK : PQuot 3 K ≃* alternatingGroup (Fin n)) :
    ∃ m : ℕ, 5 ≤ m ∧ Nonempty (↥(imageMod 3 K J) ≃* alternatingGroup (Fin m)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyp' : IsPGroup 3 (Subgroup.zpowers y) := isPGroup_zpowers_of_pow_eq_one hyp
  have hJt := glaPComponent_map_pQuotHom Nat.prime_three hyN hyp' hJ
  obtain ⟨hJte, -⟩ := chevQ_transport Nat.prime_three eK hJt
  have hb3 : barAut 3 K ⟨y, hyN⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 := Subtype.ext hyp
    rw [this, map_one]
  have hβ3 : MulAut.congr eK (barAut 3 K ⟨y, hyN⟩) ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have hβ1 : MulAut.congr eK (barAut 3 K ⟨y, hyN⟩) ≠ 1 := by
    intro h
    have hb : barAut 3 K ⟨y, hyN⟩ = 1 := (MulAut.congr eK).injective (h.trans (map_one _).symm)
    apply hncent
    apply (chevAut_eq_one_iff Nat.prime_three hK hyN).1
    show (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom (PQuot 3 K))
      (barAut 3 K ⟨y, hyN⟩) = 1
    rw [hb, map_one]
  obtain ⟨m, k, hm5, -, -, ⟨eI⟩⟩ := up7a8_kdAltExact hn Nat.prime_three (by norm_num) hβ3 hβ1 hJte
  exact ⟨m, hm5, ⟨(MulEquiv.subgroupMap eK _).trans eI⟩⟩

end CFSG.LocalAnalysis.GLTheoremA
