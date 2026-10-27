module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThreeOne
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11TwoSetFourGroup
import CFSG.Permutation.OrderThreeCentralizer
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.SupCommute
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightFourProof
import CFSG.GroupTheory.SteinbergBSQuotientLifting
import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolSmallPure1
import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1OuterGmbCore

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThree

open CFSG.Open Subgroup
open scoped commutatorElement
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD

variable {G : Type} [Group G] [Finite G] {M H E Q : Subgroup G} {p : ℕ}

namespace Ctx

variable (c : Ctx G M H E Q)

private theorem mem_normalizer_closure_of_conj {σ c₁ c₃ v : alternatingGroup (Fin 11)}
    (h₁ : v * σ * v⁻¹ ∈
      Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))))
    (h₂ : v * c₁ * v⁻¹ ∈
      Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))))
    (h₃ : v * c₃ * v⁻¹ ∈
      Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) :
    v ∈ Subgroup.normalizer
      (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) := by
  have key : ∀ x ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
      v * x * v⁻¹ ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) := by
    intro x hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact h₁
      · exact h₂
      · exact h₃
    · have e : v * 1 * v⁻¹ = 1 := by group
      rw [e]; exact Subgroup.one_mem _
    · intro x y _ _ hx' hy'
      have e : v * (x * y) * v⁻¹ = (v * x * v⁻¹) * (v * y * v⁻¹) := by group
      rw [e]; exact Subgroup.mul_mem _ hx' hy'
    · intro x _ hx'
      have e : v * x⁻¹ * v⁻¹ = (v * x * v⁻¹)⁻¹ := by group
      rw [e]; exact Subgroup.inv_mem _ hx'
  exact CFSG.SeitzReduction.RankOne.gmb_mem_normalizer_of_conj key

private theorem zpowers_sup_eq_closure (u v : alternatingGroup (Fin 11)) :
    Subgroup.zpowers u ⊔ Subgroup.zpowers v =
      Subgroup.closure ({u, v} : Set (alternatingGroup (Fin 11))) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
    show ({u, v} : Set (alternatingGroup (Fin 11))) = {u} ∪ {v} from rfl,
    Subgroup.closure_union]

private theorem closure_not_le_sup {σ c₁ c₃ u v : alternatingGroup (Fin 11)}
    (hJcard : Nat.card ↥(Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11)))) = 27)
    (hupow : u ^ 3 = 1) (hvpow : v ^ 3 = 1) (hcomm : Commute u v) :
    ¬ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ≤
      Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  intro h
  have h1 : Nat.card ↥(Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11)))) ≤
      Nat.card ↥(Subgroup.zpowers u ⊔ Subgroup.zpowers v) := Subgroup.card_le_of_le h
  rw [zpowers_sup_eq_closure u v] at h1
  have h2 := CFSG.RankThree.PartTwo.Sec11.Item1119Sym.aux_SmallPure1_card_pair_le_nine
    u v hcomm hupow hvpow
  rw [hJcard] at h1
  omega

private theorem closure_le_sup {σ c₁ c₃ u v : alternatingGroup (Fin 11)}
    (h1 : σ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
    (h2 : c₁ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
    (h3 : c₃ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v) :
    Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ≤
      Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  refine (Subgroup.closure_le _).mpr ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

private theorem Jstar_elem_abelian {σ c₁ c₃ : alternatingGroup (Fin 11)}
    (hσord : orderOf σ = 3) (hc₁ord : orderOf c₁ = 3) (hc₃ord : orderOf c₃ = 3)
    (hcommσc₁ : Commute σ c₁) (hcommσc₃ : Commute σ c₃) (hcommc₁c₃ : Commute c₁ c₃) :
    CFSG.Open.IsElemAbelian 3
        (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) ∧
      (∀ y ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))), y ^ 3 = 1) ∧
      IsPGroup 3 ↥(Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) := by
  have hJ : CFSG.Open.IsElemAbelian 3
      (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) := by
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro x hx y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
      all_goals rw [hx, hy]
      all_goals first
        | rfl
        | exact hcommσc₁.eq | exact hcommσc₁.eq.symm
        | exact hcommσc₃.eq | exact hcommσc₃.eq.symm
        | exact hcommc₁c₃.eq | exact hcommc₁c₃.eq.symm
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with hx | hx | hx
      · rw [hx]; simpa [hσord] using pow_orderOf_eq_one σ
      · rw [hx]; simpa [hc₁ord] using pow_orderOf_eq_one c₁
      · rw [hx]; simpa [hc₃ord] using pow_orderOf_eq_one c₃
  exact ⟨hJ, fun y hy => hJ.2 y hy, hJ.isPGroup⟩

private theorem conj_eq_self_of_isElemAbelian {J : Subgroup (alternatingGroup (Fin 11))}
    (hJ : CFSG.Open.IsElemAbelian 3 J) {j z : alternatingGroup (Fin 11)}
    (hj : j ∈ J) (hz : z ∈ J) : j * z * j⁻¹ = z := by
  rw [hJ.comm hj hz]; group

private theorem zpowers_le_relPPrimeCore_centralizer (hp : p.Prime) (hp3 : p ≠ 3) {a : G}
    (ha3 : orderOf a = 3) :
    Subgroup.zpowers a ≤
      CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) := by
  have haC : a ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rfl
  have hcop : Nat.Coprime p (Nat.card ↥(Subgroup.zpowers a)) := by
    rw [Nat.card_zpowers, ha3, hp.coprime_iff_not_dvd]
    intro h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h1
    · exact hp.ne_one h1
    · exact hp3 h1
  refine le_sSup ⟨Subgroup.zpowers_le.mpr haC, ?_, hcop⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.zpowers_le.mpr haC),
    Subgroup.le_normalizer_iff]
  intro g hg k hk
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have hc : Commute a g := Subgroup.mem_centralizer_iff.mp hg a (by simp)
  have heq : g * a ^ n * g⁻¹ = a ^ n := by
    rw [(hc.symm.zpow_right n).eq]
    group
  rw [heq]
  exact (Subgroup.zpowers a).zpow_mem (Subgroup.mem_zpowers a) n

private theorem kSub_le_centralizer_of_mem_relPPrimeCore (h1 : NineFourTwoSigmaGen)
    (h2 : NineTwelveOneSigmaStrong) (hp3 : p ≠ 3) {d y : G}
    {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (Subgroup.centralizer ({d} : Set G)) F' p)
    (hyO : y ∈ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({d} : Set G))) :
    kSub p M (Subgroup.centralizer ({d} : Set G)) ≤ Subgroup.centralizer ({y} : Set G) := by
  have hOcent := s.relPPrimeCore_le_centralizer_kSub h1 h2 hp3
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  subst hw
  exact (Subgroup.mem_centralizer_iff.mp (hOcent hyO) z hz).symm

private theorem false_of_mem_relPPrimeCore_support_nine (h1 : NineFourTwoSigmaGen)
    (h2 : NineTwelveOneSigmaStrong) (hp : p ∈ sigmaSet G M) {d y : G} (hy3 : orderOf y = 3)
    (hyKM : y ∈ kSub 3 M H ⊓ M)
    (hy9 : ((c.φ ⟨y, hyKM.1⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 9)
    {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (Subgroup.centralizer ({d} : Set G)) F' p)
    (hyO : y ∈ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({d} : Set G))) :
    False := by
  have hp3 : p ≠ 3 := by have := c.five_le hp; omega
  refine s.kSub_not_le h1
    ((kSub_le_centralizer_of_mem_relPPrimeCore h1 h2 hp3 s hyO).trans ?_)
  exact c.centralizer_le_of_card_support_eq_nine hyKM hy3 hy9

private theorem le_relPPrimeCore_of_mem_support_three (h1 : NineFourTwoSigmaGen)
    (h2 : NineTwelveOneSigmaStrong) (hKF1 : KFactNineFourRankOneAut)
    (hKF2 : KFactNineFourStronglyEmbedded) (hp : p ∈ sigmaSet G M)
    {d y : G} (hy3 : orderOf y = 3) (hyKM : y ∈ kSub 3 M H ⊓ M)
    (hy3supp :
      ((c.φ ⟨y, hyKM.1⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 3)
    {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (Subgroup.centralizer ({d} : Set G)) F' p)
    (hyO : y ∈ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({d} : Set G)))
    {J : Subgroup G} (hJC : J ≤ Subgroup.centralizer ({d} : Set G)) (hJp : IsPGroup 3 J) :
    J ≤ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({d} : Set G)) := by
  have hp3 : p ≠ 3 := by have := c.five_le hp; omega
  have hp5 : 5 ≤ p := c.five_le hp
  have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hle : CFSG.Open.pRank p (⊤ : Subgroup ↥(kStar p M (Subgroup.centralizer ({d} : Set G))))
      ≤ 1 :=
    (s.pRank_kStar_le h1
      (kSub_le_centralizer_of_mem_relPPrimeCore h1 h2 hp3 s hyO)).trans
      (c.pRank_le_one_of_card_support_eq_three h1 hKF2 hp hyKM hy3 hy3supp)
  have h3 : ¬ 3 ∣ Nat.card (MulAut ↥(kStar p M (Subgroup.centralizer ({d} : Set G)))) :=
    hKF1 p hpp hp5 _ (s.kStructure h1).2.2.2 hle
  exact s.le_relPPrimeCore_of_not_three_dvd h1 h3 hJC hJp

private theorem exists_normalizing_conj {X : Type} [Group X] [Finite X]
    {D0 : Subgroup X} (P : Sylow 3 D0) {w : X}
    (hw : w ∈ Subgroup.normalizer (D0 : Set X)) :
    ∃ n : X, (∃ d : ↥D0, n = (d : X)⁻¹ * w) ∧
      ∀ q : ↥D0, q ∈ P → n * (q : X) * n⁻¹ ∈ (P : Subgroup D0).map D0.subtype := by
  classical
  let PK : Subgroup X := (P : Subgroup D0).map D0.subtype
  let PwK : Subgroup X := PK.map (MulAut.conj w).toMonoidHom
  have hPK : PK ≤ D0 := by
    rintro x ⟨p, -, rfl⟩
    exact p.2
  have hDw : D0.map (MulAut.conj w).toMonoidHom = D0 :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hw
  have hPwK : PwK ≤ D0 := by
    rintro x ⟨y, hy, rfl⟩
    rw [← hDw]
    exact Subgroup.mem_map_of_mem _ (hPK hy)
  let Pw : Subgroup D0 := PwK.subgroupOf D0
  have hPwcard : Nat.card ↥Pw = 3 ^ (Nat.card ↥D0).factorization 3 := by
    have h1 : Nat.card ↥Pw = Nat.card ↥PwK :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPwK).toEquiv
    have h2 : Nat.card ↥PwK = Nat.card ↥PK := Subgroup.card_map_of_injective
      (f := (MulAut.conj w).toMonoidHom) (MulAut.conj w).injective (K := PK)
    rw [h1, h2, Subgroup.card_map_of_injective D0.subtype_injective,
      Sylow.card_eq_multiplicity P]
  let PwS : Sylow 3 D0 := Sylow.ofCard Pw hPwcard
  have hPwS : (PwS : Subgroup D0) = Pw := Sylow.coe_ofCard Pw hPwcard
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq ↥D0 P PwS
  have hdmap : (P : Subgroup D0).map (MulAut.conj d).toMonoidHom = Pw := by
    rw [← CFSG.Glauberman.sylow_smul_subgroup_eq_map_conj d P, hd, hPwS]
  refine ⟨(d : X)⁻¹ * w, ⟨d, rfl⟩, ?_⟩
  intro q hq
  have hqK : (q : X) ∈ PK := Subgroup.mem_map_of_mem D0.subtype hq
  have hwqw : w * (q : X) * w⁻¹ ∈ PwK := Subgroup.mem_map_of_mem _ hqK
  have hwqD : w * (q : X) * w⁻¹ ∈ D0 := hPwK hwqw
  have hwqPw : (⟨w * (q : X) * w⁻¹, hwqD⟩ : ↥D0) ∈ Pw := by
    rw [show (⟨w * (q : X) * w⁻¹, hwqD⟩ : ↥D0) ∈ Pw ↔
      w * (q : X) * w⁻¹ ∈ PwK from Subgroup.mem_subgroupOf]
    exact hwqw
  rw [← hdmap] at hwqPw
  obtain ⟨p, hpP, hpd⟩ := Subgroup.mem_map.mp hwqPw
  have hpX : ((MulAut.conj d) p : ↥D0) = ⟨w * (q : X) * w⁻¹, hwqD⟩ := hpd
  have hkey : (d : X) * (p : X) * (d : X)⁻¹ = w * (q : X) * w⁻¹ := by
    have h1 := congrArg (fun z : ↥D0 => (z : X)) hpX
    simpa [MulAut.conj_apply] using h1
  have hcalc : ((d : X)⁻¹ * w) * (q : X) * ((d : X)⁻¹ * w)⁻¹ = (p : X) := by
    calc ((d : X)⁻¹ * w) * (q : X) * ((d : X)⁻¹ * w)⁻¹
        = (d : X)⁻¹ * (w * (q : X) * w⁻¹) * (d : X) := by group
      _ = (d : X)⁻¹ * ((d : X) * (p : X) * (d : X)⁻¹) * (d : X) := by rw [hkey]
      _ = (p : X) := by group
  rw [hcalc]
  exact Subgroup.mem_map_of_mem D0.subtype hpP


private theorem conj_of_mem_centralizer {σ v : alternatingGroup (Fin 11)}
    (hv : v ∈ Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11)))) :
    v * σ * v⁻¹ = σ := by
  have h := Subgroup.mem_centralizer_iff.mp hv σ (by simp)
  calc v * σ * v⁻¹ = σ * v * v⁻¹ := by rw [h.symm]
    _ = σ := by group

private theorem v₁_normalizes {σ c₁ c₃ v₁ : alternatingGroup (Fin 11)}
    (hvσ : v₁ * σ * v₁⁻¹ = σ) (hvc₁ : v₁ * c₁ * v₁⁻¹ = c₁)
    (hvc₃ : v₁ * c₃ * v₁⁻¹ = c₃⁻¹) :
    v₁ ∈ Subgroup.normalizer
      (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) := by
  refine mem_normalizer_closure_of_conj ?_ ?_ ?_
  · rw [hvσ]; exact Subgroup.subset_closure (by simp)
  · rw [hvc₁]; exact Subgroup.subset_closure (by simp)
  · rw [hvc₃]; exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

private theorem v₂_normalizes {σ c₁ c₃ v₂ : alternatingGroup (Fin 11)}
    (hvσ : v₂ * σ * v₂⁻¹ = σ) (hvc₁ : v₂ * c₁ * v₂⁻¹ = σ * c₁⁻¹)
    (hvc₃ : v₂ * c₃ * v₂⁻¹ = c₃) :
    v₂ ∈ Subgroup.normalizer
      (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) := by
  refine mem_normalizer_closure_of_conj ?_ ?_ ?_
  · rw [hvσ]; exact Subgroup.subset_closure (by simp)
  · rw [hvc₁]
    exact (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))).mul_mem
      (Subgroup.subset_closure (by simp))
      (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
  · rw [hvc₃]; exact Subgroup.subset_closure (by simp)

private theorem a11_data (σ : alternatingGroup (Fin 11))
    (hσS : σ ∈ a11TwoSetStab 9 10) (hσord : orderOf σ = 3)
    (hs : ((σ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 6) :
    ∃ c₁ c₃ v₁ v₂ : alternatingGroup (Fin 11),
      c₁ ∈ a11TwoSetStab 9 10 ∧ c₃ ∈ a11TwoSetStab 9 10 ∧
      orderOf c₁ = 3 ∧ orderOf c₃ = 3 ∧
      ((c₁ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 3 ∧
      ((c₃ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 3 ∧
      ((σ * c₃ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 9 ∧
      Commute σ c₁ ∧ Commute σ c₃ ∧ Commute c₁ c₃ ∧
      Nat.card ↥(Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) = 27 ∧
      (∀ Y : Subgroup (alternatingGroup (Fin 11)),
        Y ≤ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) →
        (∀ y ∈ Y, y ≠ 1 → (y : Equiv.Perm (Fin 11)).support.card = 6) → Nat.card ↥Y ≤ 3) ∧
      v₁ ∈ a11TwoSetStab 9 10 ⊓
        Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) ∧
      v₂ ∈ a11TwoSetStab 9 10 ⊓
        Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) ∧
      v₁ * c₁ * v₁⁻¹ = c₁ ∧ v₁ * c₃ * v₁⁻¹ = c₃⁻¹ ∧
      v₂ * c₁ * v₂⁻¹ = σ * c₁⁻¹ ∧ v₂ * c₃ * v₂⁻¹ = c₃ ∧
      orderOf (σ * c₁) = 3 ∧
      ¬ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ≤
        Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₃ ∧
      ¬ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ≤
        Subgroup.zpowers (σ * c₁) ⊔ Subgroup.zpowers c₃ ∧
      (∀ (u v : alternatingGroup (Fin 11)),
        σ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
        c₁ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
        c₃ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
        Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ≤
          Subgroup.zpowers u ⊔ Subgroup.zpowers v) ∧
      (∀ j ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
        ∀ z ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
        j * z * j⁻¹ = z) ∧
      v₁ ∈ Subgroup.normalizer
        (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) ∧
      v₂ ∈ Subgroup.normalizer
        (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) ∧
      CFSG.Open.IsElemAbelian 3
        (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) ∧
      (∀ y ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))), y ^ 3 = 1) ∧
      IsPGroup 3 ↥(Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) := by
  obtain ⟨c₁, c₃, v₁, v₂, hc₁S, hc₃S, hc₁ord, hc₃ord, hc₁supp, hc₃supp, hσc₃supp,
    hcommσc₁, hcommσc₃, hcommc₁c₃, hJcard, hbound, hv₁mem, hv₂mem, hv₁c₁, hv₁c₃, hv₂c₁,
    hv₂c₃⟩ := exists_fourGroup_of_card_support_eq_six hσS hσord hs
  obtain ⟨hJstar_ea, hJstar_cube, hJstar_p⟩ :=
    Jstar_elem_abelian hσord hc₁ord hc₃ord hcommσc₁ hcommσc₃ hcommc₁c₃
  have hc₁pow : c₁ ^ 3 = 1 := by
    have := pow_orderOf_eq_one c₁; rwa [hc₁ord] at this
  have hc₃pow : c₃ ^ 3 = 1 := by
    have := pow_orderOf_eq_one c₃; rwa [hc₃ord] at this
  have hσpow : σ ^ 3 = 1 := by
    have := pow_orderOf_eq_one σ; rwa [hσord] at this
  have hnot_sup₁ := closure_not_le_sup hJcard hc₁pow hc₃pow hcommc₁c₃
  have hσc₁ord : orderOf (σ * c₁) = 3 := by
    have hcube : (σ * c₁) ^ 3 = 1 := by rw [hcommσc₁.mul_pow, hσpow, hc₁pow, mul_one]
    refine orderOf_eq_prime hcube ?_
    intro h
    apply hnot_sup₁
    refine closure_le_sup ?_ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c₁))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₃))
    have hσeq : σ = c₁⁻¹ := by
      calc σ = σ * c₁ * c₁⁻¹ := by group
        _ = 1 * c₁⁻¹ := by rw [← h]
        _ = c₁⁻¹ := one_mul _
    rw [hσeq]
    exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers c₁))
  have hσc₁pow : (σ * c₁) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (σ * c₁); rwa [hσc₁ord] at this
  have hnot_sup₂ := closure_not_le_sup (u := σ * c₁) (v := c₃) hJcard hσc₁pow hc₃pow
    (hcommσc₃.mul_left hcommc₁c₃)
  have hv₁σ := conj_of_mem_centralizer hv₁mem.2
  have hv₂σ := conj_of_mem_centralizer hv₂mem.2
  have hv₁N := v₁_normalizes hv₁σ hv₁c₁ hv₁c₃
  have hv₂N := v₂_normalizes hv₂σ hv₂c₁ hv₂c₃
  exact ⟨c₁, c₃, v₁, v₂, hc₁S, hc₃S, hc₁ord, hc₃ord, hc₁supp, hc₃supp, hσc₃supp,
    hcommσc₁, hcommσc₃, hcommc₁c₃, hJcard, hbound, hv₁mem, hv₂mem, hv₁c₁, hv₁c₃, hv₂c₁,
    hv₂c₃, hσc₁ord, hnot_sup₁, hnot_sup₂, fun u v h1 h2 h3 => closure_le_sup h1 h2 h3,
    fun j hj z hz => conj_eq_self_of_isElemAbelian hJstar_ea hj hz, hv₁N, hv₂N, hJstar_ea,
    hJstar_cube, hJstar_p⟩


private theorem D_data {a : G} (ha : a ∈ kSub 3 M H ⊓ M) (ha3 : orderOf a = 3)
    {σ : alternatingGroup (Fin 11)} (hσdef : σ = c.φ ⟨a, ha.1⟩)
    {c₁ c₃ : alternatingGroup (Fin 11)}
    (hσS : σ ∈ a11TwoSetStab 9 10) (hc₁S : c₁ ∈ a11TwoSetStab 9 10)
    (hc₃S : c₃ ∈ a11TwoSetStab 9 10) (hcommσc₁ : Commute σ c₁) (hcommσc₃ : Commute σ c₃) :
    ∃ D : Subgroup ↥(kSub 3 M H),
      D = (M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (kSub 3 M H) ∧
      D.map c.φ = a11TwoSetStab 9 10 ⊓
        Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) ∧
      Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ≤ D.map c.φ := by
  have hmapD : ((M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (kSub 3 M H)).map c.φ =
      a11TwoSetStab 9 10 ⊓
        Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) := by
    rw [hσdef]
    exact c.map_φ_inf_centralizer_singleton ha.1 ha3
  refine ⟨(M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (kSub 3 M H), rfl, hmapD, ?_⟩
  rw [hmapD]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hcent : ∀ z : alternatingGroup (Fin 11),
      z ∈ Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))) ↔ σ * z = z * σ := by
    intro z
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h; exact h σ (by simp)
    · intro h y hy; rw [Set.mem_singleton_iff] at hy; subst hy; exact h
  rcases hx with hx | hx | hx
  · rw [hx]; exact Subgroup.mem_inf.mpr ⟨hσS, (hcent σ).mpr rfl⟩
  · rw [hx]; exact Subgroup.mem_inf.mpr ⟨hc₁S, (hcent c₁).mpr hcommσc₁.eq⟩
  · rw [hx]; exact Subgroup.mem_inf.mpr ⟨hc₃S, (hcent c₃).mpr hcommσc₃.eq⟩

private theorem D0_data {a : G} (ha : a ∈ kSub 3 M H ⊓ M) (ha3 : orderOf a = 3)
    {σ : alternatingGroup (Fin 11)} (hσdef : σ = c.φ ⟨a, ha.1⟩)
    {c₁ c₃ : alternatingGroup (Fin 11)} (D : Subgroup ↥(kSub 3 M H))
    (hDdef : D = (M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (kSub 3 M H))
    (hJstar_le_D : Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ≤
      D.map c.φ) :
    ∃ D0 : Subgroup ↥(kSub 3 M H),
      D0 = D ⊓ (Subgroup.closure ({σ, c₁, c₃} :
        Set (alternatingGroup (Fin 11)))).comap c.φ ∧
      D0.map c.φ = Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ∧
      (⟨a, ha.1⟩ : ↥(kSub 3 M H)) ∈ D0 := by
  refine ⟨D ⊓ (Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11)))).comap c.φ, rfl, ?_, ?_⟩
  · refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) ?_
    intro y hy
    obtain ⟨d, hdD, hdφ⟩ := Subgroup.mem_map.mp (hJstar_le_D hy)
    exact Subgroup.mem_map.mpr
      ⟨d, Subgroup.mem_inf.mpr ⟨hdD, by rw [Subgroup.mem_comap, hdφ]; exact hy⟩, hdφ⟩
  · have haCent : a ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rfl
    have haD : (⟨a, ha.1⟩ : ↥(kSub 3 M H)) ∈ D := by
      rw [hDdef]
      exact Subgroup.mem_subgroupOf.mpr ⟨ha.2, haCent⟩
    exact Subgroup.mem_inf.mpr ⟨haD, by
      rw [Subgroup.mem_comap, ← hσdef]
      exact Subgroup.subset_closure (by simp)⟩

private theorem sylow_data {a : G} (ha : a ∈ kSub 3 M H ⊓ M) (ha3 : orderOf a = 3)
    {σ c₁ c₃ : alternatingGroup (Fin 11)} (D0 : Subgroup ↥(kSub 3 M H))
    (haD0 : (⟨a, ha.1⟩ : ↥(kSub 3 M H)) ∈ D0)
    (hD0map : D0.map c.φ = Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))))
    (hJcard : Nat.card ↥(Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11)))) = 27) :
    ∃ P : Sylow 3 D0, (⟨⟨a, ha.1⟩, haD0⟩ : ↥D0) ∈ P ∧
      ∀ y ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
        ∃ x : ↥D0, x ∈ P ∧ c.φ x.1 = y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hza : orderOf (⟨⟨a, ha.1⟩, haD0⟩ : ↥D0) = 3 := by simpa using ha3
  have hzap : IsPGroup 3 ↥(Subgroup.zpowers (⟨⟨a, ha.1⟩, haD0⟩ : ↥D0)) := by
    have h3 : (⟨⟨a, ha.1⟩, haD0⟩ : ↥D0) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one (⟨⟨a, ha.1⟩, haD0⟩ : ↥D0)
      rwa [hza] at h
    exact (CFSG.Open.isElemAbelian_zpowers (p := 3) h3).isPGroup
  obtain ⟨P, haP⟩ := IsPGroup.exists_le_sylow hzap
  have haP' : (⟨⟨a, ha.1⟩, haD0⟩ : ↥D0) ∈ P := haP (Subgroup.mem_zpowers _)
  let g : ↥D0 →* ↥(Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) :=
    { toFun := fun x => ⟨c.φ x.1, by
        have hx : c.φ x.1 ∈ D0.map c.φ := Subgroup.mem_map_of_mem c.φ x.2
        rwa [hD0map] at hx⟩
      map_one' := Subtype.ext (map_one c.φ)
      map_mul' := fun x y => Subtype.ext (map_mul c.φ x.1 y.1) }
  have hg_surj : Function.Surjective g := by
    intro y
    have hy : (y : alternatingGroup (Fin 11)) ∈ D0.map c.φ := by
      rw [hD0map]; exact y.2
    obtain ⟨x, hx, hxφ⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxφ⟩
  let Pg : Sylow 3 ↥(Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) :=
    Sylow.mapSurjective hg_surj P
  have hPg : (Pg : Subgroup ↥(Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11))))) = ⊤ := by
    have htop : IsPGroup 3 ↥(⊤ :
        Subgroup ↥(Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))))) := by
      rw [IsPGroup.iff_card]
      exact ⟨3, by rw [Subgroup.card_top, hJcard]; norm_num⟩
    exact (Pg.is_maximal' htop le_top).symm
  refine ⟨P, haP', ?_⟩
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥(Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11))))) ∈ (Pg : Subgroup _) := by
    rw [hPg]; exact Subgroup.mem_top _
  rw [Sylow.coe_mapSurjective] at hy'
  obtain ⟨x, hxP, hxg⟩ := Subgroup.mem_map.mp hy'
  exact ⟨x, hxP, congrArg Subtype.val hxg⟩

private theorem PK_data {σ c₁ c₃ : alternatingGroup (Fin 11)}
    (D0 : Subgroup ↥(kSub 3 M H)) (P : Sylow 3 D0)
    (hD0map : D0.map c.φ = Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))))
    (hJstar_cube : ∀ y ∈ Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11))), y ^ 3 = 1) :
    ∃ PK : Subgroup ↥(kSub 3 M H),
      PK = (P : Subgroup ↥D0).map D0.subtype ∧ PK ≤ D0 ∧
      (∀ x ∈ PK, c.φ x ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) ∧
      IsPGroup 3 PK ∧ PK ⊓ (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) = ⊥ ∧
      (∀ x y : ↥(kSub 3 M H), x ∈ PK → y ∈ PK → c.φ x = c.φ y → x = y) ∧
      (∀ x ∈ PK, x ^ 3 = 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let PK : Subgroup ↥(kSub 3 M H) := (P : Subgroup ↥D0).map D0.subtype
  have hPK_le_D0 : PK ≤ D0 := by
    rintro x ⟨q, -, rfl⟩
    exact q.2
  have hφPK_le : ∀ x ∈ PK, c.φ x ∈
      Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) := by
    intro x hx
    have hxD : c.φ x ∈ D0.map c.φ := Subgroup.mem_map_of_mem c.φ (hPK_le_D0 hx)
    rwa [hD0map] at hxD
  have hPKp : IsPGroup 3 PK := IsPGroup.map P.isPGroup' D0.subtype
  have hPKker : PK ⊓ (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) = ⊥ :=
    CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd
      c.not_three_dvd_card_pPrimeCore hPKp
  have hinjPK : ∀ x y : ↥(kSub 3 M H), x ∈ PK → y ∈ PK → c.φ x = c.φ y → x = y := by
    intro x y hx hy hxy
    have hmem : x * y⁻¹ ∈ PK ⊓ (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) :=
      Subgroup.mem_inf.mpr ⟨PK.mul_mem hx (PK.inv_mem hy), by
        rw [← c.ker_φ, MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]⟩
    rw [hPKker] at hmem
    have h1 : x * y⁻¹ = 1 := by simpa using hmem
    calc x = x * y⁻¹ * y := by group
      _ = y := by rw [h1, one_mul]
  have hPKcube : ∀ x ∈ PK, x ^ 3 = 1 := by
    intro x hx
    refine hinjPK (x ^ 3) 1 (PK.pow_mem hx 3) PK.one_mem ?_
    rw [map_pow, map_one, hJstar_cube (c.φ x) (hφPK_le x hx)]
  exact ⟨PK, rfl, hPK_le_D0, hφPK_le, hPKp, hPKker, hinjPK, hPKcube⟩


private theorem JG_data {a : G} (ha : a ∈ kSub 3 M H ⊓ M)
    {σ : alternatingGroup (Fin 11)} {c₁ c₃ : alternatingGroup (Fin 11)}
    (D D0 : Subgroup ↥(kSub 3 M H)) (P : Sylow 3 D0) (PK : Subgroup ↥(kSub 3 M H))
    (hDdef : D = (M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (kSub 3 M H))
    (hD0def : D0 = D ⊓ (Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11)))).comap c.φ)
    (hPKdef : PK = (P : Subgroup ↥D0).map D0.subtype)
    (hPK_le_D0 : PK ≤ D0) (hPKp : IsPGroup 3 PK) (hPKcube : ∀ x ∈ PK, x ^ 3 = 1)
    (hPsurj : ∀ y ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
      ∃ x : ↥D0, x ∈ P ∧ c.φ x.1 = y)
    (haD0 : (⟨a, ha.1⟩ : ↥(kSub 3 M H)) ∈ D0)
    (haP : (⟨⟨a, ha.1⟩, haD0⟩ : ↥D0) ∈ P) :
    ∃ (JG : Subgroup G) (x₁D x₃D : ↥D0),
      JG = PK.map (kSub 3 M H).subtype ∧
      x₁D ∈ P ∧ x₃D ∈ P ∧ c.φ x₁D.1 = c₁ ∧ c.φ x₃D.1 = c₃ ∧
      (x₁D : ↥(kSub 3 M H)) ∈ PK ∧ (x₃D : ↥(kSub 3 M H)) ∈ PK ∧
      ((x₁D : ↥(kSub 3 M H)) : G) ∈ JG ∧ ((x₃D : ↥(kSub 3 M H)) : G) ∈ JG ∧
      JG ≤ kSub 3 M H ∧ JG ≤ M ⊓ Subgroup.centralizer ({a} : Set G) ∧
      IsPGroup 3 JG ∧ (∀ y ∈ JG, y ^ 3 = 1) ∧
      (⟨a, ha.1⟩ : ↥(kSub 3 M H)) ∈ PK ∧ a ∈ JG := by
  have hPK_le_D : PK ≤ D := hPK_le_D0.trans (by rw [hD0def]; exact inf_le_left)
  have hJG_le_K : PK.map (kSub 3 M H).subtype ≤ kSub 3 M H := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  have hJG_le_MC : PK.map (kSub 3 M H).subtype ≤
      M ⊓ Subgroup.centralizer ({a} : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    have hyD : y ∈ D := hPK_le_D hy
    rw [hDdef, Subgroup.mem_subgroupOf] at hyD
    exact hyD
  have hJG_p : IsPGroup 3 (PK.map (kSub 3 M H).subtype) :=
    IsPGroup.map hPKp (kSub 3 M H).subtype
  have hJGcube : ∀ y ∈ PK.map (kSub 3 M H).subtype, y ^ 3 = 1 := by
    rintro y ⟨x, hx, rfl⟩
    simpa using congrArg (fun z : ↥(kSub 3 M H) => (z : G)) (hPKcube x hx)
  obtain ⟨x₁D, hx₁P, hx₁φ⟩ := hPsurj c₁ (Subgroup.subset_closure (by simp))
  obtain ⟨x₃D, hx₃P, hx₃φ⟩ := hPsurj c₃ (Subgroup.subset_closure (by simp))
  have hx₁PK : (x₁D : ↥(kSub 3 M H)) ∈ PK := by
    rw [hPKdef]; exact Subgroup.mem_map_of_mem D0.subtype hx₁P
  have hx₃PK : (x₃D : ↥(kSub 3 M H)) ∈ PK := by
    rw [hPKdef]; exact Subgroup.mem_map_of_mem D0.subtype hx₃P
  have hx₁JG : ((x₁D : ↥(kSub 3 M H)) : G) ∈ PK.map (kSub 3 M H).subtype :=
    Subgroup.mem_map_of_mem _ hx₁PK
  have hx₃JG : ((x₃D : ↥(kSub 3 M H)) : G) ∈ PK.map (kSub 3 M H).subtype :=
    Subgroup.mem_map_of_mem _ hx₃PK
  have haPK : (⟨a, ha.1⟩ : ↥(kSub 3 M H)) ∈ PK := by
    rw [hPKdef]
    simpa using Subgroup.mem_map_of_mem D0.subtype haP
  have haJG : a ∈ PK.map (kSub 3 M H).subtype := Subgroup.mem_map_of_mem _ haPK
  exact ⟨PK.map (kSub 3 M H).subtype, x₁D, x₃D, rfl, hx₁P, hx₃P, hx₁φ, hx₃φ, hx₁PK, hx₃PK,
    hx₁JG, hx₃JG, hJG_le_K, hJG_le_MC, hJG_p, hJGcube, haPK, haJG⟩

private theorem injJG_data {σ c₁ c₃ : alternatingGroup (Fin 11)}
    (PK : Subgroup ↥(kSub 3 M H)) (JG : Subgroup G)
    (hJGdef : JG = PK.map (kSub 3 M H).subtype)
    (hJG_le_K : JG ≤ kSub 3 M H)
    (hinjPK : ∀ x y : ↥(kSub 3 M H), x ∈ PK → y ∈ PK → c.φ x = c.φ y → x = y)
    (hφPK_le : ∀ x ∈ PK,
      c.φ x ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) :
    (∀ (x : G) (hx : x ∈ JG), ∀ (y : G) (hy : y ∈ JG),
      c.φ ⟨x, hJG_le_K hx⟩ = c.φ ⟨y, hJG_le_K hy⟩ → x = y) ∧
    (∀ (y : G) (hy : y ∈ JG),
      c.φ ⟨y, hJG_le_K hy⟩ ∈
        Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))) := by
  constructor
  · intro x hx y hy hxy
    obtain ⟨p, hp, hpeq⟩ := Subgroup.mem_map.mp (hJGdef ▸ hx)
    obtain ⟨q, hq, hqeq⟩ := Subgroup.mem_map.mp (hJGdef ▸ hy)
    have hpx : p = ⟨x, hJG_le_K hx⟩ := Subtype.ext hpeq
    have hqy : q = ⟨y, hJG_le_K hy⟩ := Subtype.ext hqeq
    have hpq : p = q := by
      apply hinjPK p q hp hq
      rw [hpx, hqy]
      exact hxy
    calc x = (p : G) := hpeq.symm
      _ = (q : G) := by rw [hpq]
      _ = y := hqeq
  · intro y hy
    obtain ⟨p, hp, hpeq⟩ := Subgroup.mem_map.mp (hJGdef ▸ hy)
    have hpy : p = ⟨y, hJG_le_K hy⟩ := Subtype.ext hpeq
    exact hpy ▸ hφPK_le p hp


private theorem JG_support_nine_false {a : G} (h1 : NineFourTwoSigmaGen)
    (h2 : NineTwelveOneSigmaStrong) (hp : p ∈ sigmaSet G M) {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (Subgroup.centralizer ({a} : Set G)) F' p)
    {JG : Subgroup G} (hJG_le_K : JG ≤ kSub 3 M H)
    (hJG_le_MC : JG ≤ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hJGcube : ∀ y ∈ JG, y ^ 3 = 1) :
    ∀ (y : G) (hyJ : y ∈ JG),
      y ∈ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) →
      ((c.φ ⟨y, hJG_le_K hyJ⟩ : alternatingGroup (Fin 11)) :
        Equiv.Perm (Fin 11)).support.card = 9 → False := by
  intro y hyJ hyO hy9
  have hy1 : y ≠ 1 := by
    intro h
    have hK : (⟨y, hJG_le_K hyJ⟩ : ↥(kSub 3 M H)) = 1 := Subtype.ext h
    have h0 : ((c.φ ⟨y, hJG_le_K hyJ⟩ : alternatingGroup (Fin 11)) :
        Equiv.Perm (Fin 11)).support.card = 0 := by
      rw [show c.φ ⟨y, hJG_le_K hyJ⟩ = 1 from by rw [hK, map_one]]
      simp
    rw [h0] at hy9
    omega
  have hyKM : y ∈ kSub 3 M H ⊓ M := ⟨hJG_le_K hyJ, (hJG_le_MC hyJ).1⟩
  have hy3 : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one (hJGcube y hyJ)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h (fun h1 => hy1 (orderOf_eq_one_iff.mp h1))
    · exact h
  exact false_of_mem_relPPrimeCore_support_nine c h1 h2 hp hy3 hyKM
    (by simpa using hy9) s hyO

private theorem JG_le_relPPrimeCore_of_support_three {a : G} (h1 : NineFourTwoSigmaGen)
    (h2 : NineTwelveOneSigmaStrong) (hKF1 : KFactNineFourRankOneAut)
    (hKF2 : KFactNineFourStronglyEmbedded) (hp : p ∈ sigmaSet G M) {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (Subgroup.centralizer ({a} : Set G)) F' p)
    {JG : Subgroup G} (hJG_le_K : JG ≤ kSub 3 M H)
    (hJG_le_MC : JG ≤ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hJGcube : ∀ y ∈ JG, y ^ 3 = 1) (hJG_p : IsPGroup 3 JG) :
    ∀ (y : G) (hyJ : y ∈ JG),
      y ∈ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) →
      ((c.φ ⟨y, hJG_le_K hyJ⟩ : alternatingGroup (Fin 11)) :
        Equiv.Perm (Fin 11)).support.card = 3 →
      JG ≤ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) := by
  intro y hyJ hyO hy3
  have hy1 : y ≠ 1 := by
    intro h
    have hK : (⟨y, hJG_le_K hyJ⟩ : ↥(kSub 3 M H)) = 1 := Subtype.ext h
    have h0 : ((c.φ ⟨y, hJG_le_K hyJ⟩ : alternatingGroup (Fin 11)) :
        Equiv.Perm (Fin 11)).support.card = 0 := by
      rw [show c.φ ⟨y, hJG_le_K hyJ⟩ = 1 from by rw [hK, map_one]]
      simp
    rw [h0] at hy3
    omega
  have hyKM : y ∈ kSub 3 M H ⊓ M := ⟨hJG_le_K hyJ, (hJG_le_MC hyJ).1⟩
  have hyord : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one (hJGcube y hyJ)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h (fun h1 => hy1 (orderOf_eq_one_iff.mp h1))
    · exact h
  exact le_relPPrimeCore_of_mem_support_three c h1 h2 hKF1 hKF2 hp hyord hyKM
    (by simpa using hy3) s hyO (hJG_le_MC.trans inf_le_right) hJG_p

private theorem JG_support_six {a : G} (h1 : NineFourTwoSigmaGen)
    (h2 : NineTwelveOneSigmaStrong) (hKF1 : KFactNineFourRankOneAut)
    (hKF2 : KFactNineFourStronglyEmbedded) (hp : p ∈ sigmaSet G M) {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (Subgroup.centralizer ({a} : Set G)) F' p)
    (ha : a ∈ kSub 3 M H ⊓ M) {σ c₃ : alternatingGroup (Fin 11)}
    (hσdef : σ = c.φ ⟨a, ha.1⟩)
    (hσc₃supp : ((σ * c₃ : alternatingGroup (Fin 11)) :
      Equiv.Perm (Fin 11)).support.card = 9)
    {JG : Subgroup G} {D0 : Subgroup ↥(kSub 3 M H)} (x₃D : ↥D0)
    (hJG_le_K : JG ≤ kSub 3 M H)
    (hJG_le_MC : JG ≤ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hJGcube : ∀ y ∈ JG, y ^ 3 = 1) (haJG : a ∈ JG)
    (hx₃JG : ((x₃D : ↥(kSub 3 M H)) : G) ∈ JG)
    (hx₃φ : c.φ (x₃D : ↥(kSub 3 M H)) = c₃)
    (hfalse9 : ∀ (y : G) (hyJ : y ∈ JG),
      y ∈ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) →
      ((c.φ ⟨y, hJG_le_K hyJ⟩ : alternatingGroup (Fin 11)) :
        Equiv.Perm (Fin 11)).support.card = 9 → False)
    (hleO3 : ∀ (y : G) (hyJ : y ∈ JG),
      y ∈ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) →
      ((c.φ ⟨y, hJG_le_K hyJ⟩ : alternatingGroup (Fin 11)) :
        Equiv.Perm (Fin 11)).support.card = 3 →
      JG ≤ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G))) :
    ∀ (y : G) (hyJ : y ∈ JG), y ≠ 1 →
      y ∈ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) →
      ((c.φ ⟨y, hJG_le_K hyJ⟩ : alternatingGroup (Fin 11)) :
        Equiv.Perm (Fin 11)).support.card = 6 := by
  intro y hyJ hy1 hyO
  have hyKM : y ∈ kSub 3 M H ⊓ M := ⟨hJG_le_K hyJ, (hJG_le_MC hyJ).1⟩
  have hyord : orderOf y = 3 := by
    have hdvd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one (hJGcube y hyJ)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h (fun h1 => hy1 (orderOf_eq_one_iff.mp h1))
    · exact h
  have hperm : orderOf ((c.φ ⟨y, hyKM.1⟩ : alternatingGroup (Fin 11)) :
      Equiv.Perm (Fin 11)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact c.orderOf_φ hyord
  have hperm' : orderOf ((c.φ ⟨y, hJG_le_K hyJ⟩ : alternatingGroup (Fin 11)) :
      Equiv.Perm (Fin 11)) = 3 := hperm
  rcases CFSG.Permutation.card_support_eq_three_or_six_or_nine hperm' with h3 | h6 | h9
  · have hJO : JG ≤ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) :=
      hleO3 y hyJ hyO h3
    have hφax3 : c.φ ⟨a * ((x₃D : ↥(kSub 3 M H)) : G),
        hJG_le_K (JG.mul_mem haJG hx₃JG)⟩ = σ * c₃ := by
      have heq : (⟨a * ((x₃D : ↥(kSub 3 M H)) : G),
          hJG_le_K (JG.mul_mem haJG hx₃JG)⟩ : ↥(kSub 3 M H)) =
          ⟨a, ha.1⟩ * (x₃D : ↥(kSub 3 M H)) := Subtype.ext rfl
      rw [heq, map_mul, hσdef.symm, hx₃φ]
    have hy'J : a * ((x₃D : ↥(kSub 3 M H)) : G) ∈ JG := JG.mul_mem haJG hx₃JG
    exact (hfalse9 _ hy'J (hJO hy'J) (by rw [hφax3]; exact hσc₃supp)).elim
  · exact h6
  · exact (hfalse9 y hyJ hyO h9).elim

private theorem JO_le {a : G} (ha : a ∈ kSub 3 M H ⊓ M)
    {σ c₁ c₃ : alternatingGroup (Fin 11)} (hσdef : σ = c.φ (⟨a, ha.1⟩ : ↥(kSub 3 M H)))
    (hσord : orderOf σ = 3)
    {PK : Subgroup ↥(kSub 3 M H)}
    (hφPK_le : ∀ x ∈ PK,
      c.φ x ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))))
    (hinjPK : ∀ x y : ↥(kSub 3 M H), x ∈ PK → y ∈ PK → c.φ x = c.φ y → x = y)
    (haPK : ((⟨a, ha.1⟩ : ↥(kSub 3 M H)) : ↥(kSub 3 M H)) ∈ PK)
    (hOa : Subgroup.zpowers a ≤
      CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)))
    (hbound : ∀ Y : Subgroup (alternatingGroup (Fin 11)),
      Y ≤ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) →
      (∀ y ∈ Y, y ≠ 1 → (y : Equiv.Perm (Fin 11)).support.card = 6) → Nat.card ↥Y ≤ 3)
    {JG : Subgroup G} (hJGdef : JG = PK.map (kSub 3 M H).subtype)
    (hJG_le_K : JG ≤ kSub 3 M H)
    (hsupp_six : ∀ (y : G) (hyJ : y ∈ JG), y ≠ 1 →
      y ∈ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) →
      ((c.φ ⟨y, hJG_le_K hyJ⟩ : alternatingGroup (Fin 11)) :
        Equiv.Perm (Fin 11)).support.card = 6) :
    JG ⊓ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) ≤
      Subgroup.zpowers a := by

  set OK : Subgroup ↥(kSub 3 M H) :=
    (CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G))).subgroupOf
      (kSub 3 M H) with hOKdef
  have haOK : ((⟨a, ha.1⟩ : ↥(kSub 3 M H)) : ↥(kSub 3 M H)) ∈ OK := by
    rw [hOKdef, Subgroup.mem_subgroupOf]
    exact hOa (Subgroup.mem_zpowers a)
  have hY_le : (PK ⊓ OK).map c.φ ≤
      Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    exact hφPK_le x hx.1
  have hY_six : ∀ z ∈ (PK ⊓ OK).map c.φ, z ≠ 1 →
      ((z : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 6 := by
    intro z hz hz1
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    obtain ⟨hxPK, hxOK⟩ := Subgroup.mem_inf.mp hx
    have hxJ : ((x : ↥(kSub 3 M H)) : G) ∈ JG := by
      rw [hJGdef]; exact Subgroup.mem_map_of_mem _ hxPK
    have hxO : ((x : ↥(kSub 3 M H)) : G) ∈
        CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) := by
      rw [hOKdef] at hxOK
      exact Subgroup.mem_subgroupOf.mp hxOK
    have hx1 : ((x : ↥(kSub 3 M H)) : G) ≠ 1 := by
      intro h
      apply hz1
      have hx1' : x = 1 := Subtype.ext h
      rw [hx1', map_one]
    exact hsupp_six _ hxJ hx1 hxO
  have hσY : σ ∈ (PK ⊓ OK).map c.φ := by
    have h := Subgroup.mem_map_of_mem c.φ (Subgroup.mem_inf.mpr ⟨haPK, haOK⟩)
    rwa [← hσdef] at h
  have hYeq : (PK ⊓ OK).map c.φ = Subgroup.zpowers σ := by
    have h1 : Subgroup.zpowers σ ≤ (PK ⊓ OK).map c.φ := Subgroup.zpowers_le.mpr hσY
    have h2 : Nat.card ↥((PK ⊓ OK).map c.φ) ≤ Nat.card ↥(Subgroup.zpowers σ) := by
      rw [Nat.card_zpowers, hσord]; exact hbound _ hY_le hY_six
    exact (Subgroup.eq_of_le_of_card_ge h1 h2).symm
  have hPKOK_le : PK ⊓ OK ≤ Subgroup.zpowers (⟨a, ha.1⟩ : ↥(kSub 3 M H)) := by
    intro x hx
    have hxσ : c.φ x ∈ Subgroup.zpowers σ := by
      rw [← hYeq]
      exact Subgroup.mem_map_of_mem c.φ hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxσ
    have hxk : x = (⟨a, ha.1⟩ : ↥(kSub 3 M H)) ^ k := by
      apply hinjPK x ((⟨a, ha.1⟩ : ↥(kSub 3 M H)) ^ k) hx.1 (Subgroup.zpow_mem PK haPK k)
      rw [map_zpow, hσdef.symm]; exact hk.symm
    rw [hxk]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k
  have hzmap : ((Subgroup.zpowers (⟨a, ha.1⟩ : ↥(kSub 3 M H))) : Subgroup ↥(kSub 3 M H)).map
      (kSub 3 M H).subtype = Subgroup.zpowers a := by
    rw [MonoidHom.map_zpowers]; rfl
  rintro x ⟨hxJ, hxO⟩
  obtain ⟨p, hp, hpeq⟩ := Subgroup.mem_map.mp (hJGdef ▸ hxJ)
  have hpOK : p ∈ OK := by
    rw [hOKdef, Subgroup.mem_subgroupOf, show (p : G) = x from hpeq]
    exact hxO
  have hx : x ∈ (Subgroup.zpowers (⟨a, ha.1⟩ : ↥(kSub 3 M H))).map (kSub 3 M H).subtype := by
    rw [← hpeq]
    exact Subgroup.mem_map_of_mem _ (hPKOK_le (Subgroup.mem_inf.mpr ⟨hp, hpOK⟩))
  rwa [hzmap] at hx

private theorem JO_eq {a : G} (ha : a ∈ kSub 3 M H ⊓ M)
    {σ c₁ c₃ : alternatingGroup (Fin 11)} (hσdef : σ = c.φ ⟨a, ha.1⟩)
    (hσord : orderOf σ = 3)
    {PK : Subgroup ↥(kSub 3 M H)}
    (hφPK_le : ∀ x ∈ PK,
      c.φ x ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))))
    (hinjPK : ∀ x y : ↥(kSub 3 M H), x ∈ PK → y ∈ PK → c.φ x = c.φ y → x = y)
    (haPK : (⟨a, ha.1⟩ : ↥(kSub 3 M H)) ∈ PK)
    (hOa : Subgroup.zpowers a ≤
      CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)))
    (hbound : ∀ Y : Subgroup (alternatingGroup (Fin 11)),
      Y ≤ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) →
      (∀ y ∈ Y, y ≠ 1 → (y : Equiv.Perm (Fin 11)).support.card = 6) → Nat.card ↥Y ≤ 3)
    {JG : Subgroup G} (hJGdef : JG = PK.map (kSub 3 M H).subtype)
    (hJG_le_K : JG ≤ kSub 3 M H) (haJG : a ∈ JG)
    (hsupp_six : ∀ (y : G) (hyJ : y ∈ JG), y ≠ 1 →
      y ∈ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) →
      ((c.φ ⟨y, hJG_le_K hyJ⟩ : alternatingGroup (Fin 11)) :
        Equiv.Perm (Fin 11)).support.card = 6) :
    JG ⊓ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) =
      Subgroup.zpowers a := by
  refine le_antisymm ?_ ?_
  · exact JO_le c ha hσdef hσord hφPK_le hinjPK haPK hOa hbound hJGdef hJG_le_K hsupp_six
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨haJG, hOa (Subgroup.mem_zpowers a)⟩

private theorem W_data {a : G} (ha : a ∈ kSub 3 M H ⊓ M)
    {c₁ c₃ : alternatingGroup (Fin 11)} {D0 : Subgroup ↥(kSub 3 M H)}
    (x₁D x₃D : ↥D0) {JG : Subgroup G} (hJG_le_K : JG ≤ kSub 3 M H)
    (haJG : a ∈ JG) (hx₁JG : ((x₁D : ↥(kSub 3 M H)) : G) ∈ JG)
    (hx₃JG : ((x₃D : ↥(kSub 3 M H)) : G) ∈ JG)
    (hc₁ord : orderOf c₁ = 3) (hc₃ord : orderOf c₃ = 3)
    (hx₁φ : c.φ (x₁D : ↥(kSub 3 M H)) = c₁)
    (hx₃φ : c.φ (x₃D : ↥(kSub 3 M H)) = c₃) :
    ∃ (ax₁ x₃G : G) (W : Subgroup G),
      ax₁ = a * ((x₁D : ↥(kSub 3 M H)) : G) ∧ x₃G = ((x₃D : ↥(kSub 3 M H)) : G) ∧
      W = Subgroup.closure ({ax₁, x₃G} : Set G) ∧
      ax₁ ∈ JG ∧ x₃G ∈ JG ∧ W ≤ JG ∧
      ((x₁D : ↥(kSub 3 M H)) : G) ≠ 1 ∧ x₃G ≠ 1 := by
  refine ⟨a * ((x₁D : ↥(kSub 3 M H)) : G), ((x₃D : ↥(kSub 3 M H)) : G),
    Subgroup.closure ({a * ((x₁D : ↥(kSub 3 M H)) : G), ((x₃D : ↥(kSub 3 M H)) : G)} : Set G),
    rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact JG.mul_mem haJG hx₁JG
  · exact hx₃JG
  · rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact JG.mul_mem haJG hx₁JG
    · exact hx₃JG
  · intro h
    have h1 : (x₁D : ↥(kSub 3 M H)) = 1 := Subtype.ext h
    have h2 : c₁ = 1 := by rw [← hx₁φ, h1, map_one]
    rw [h2] at hc₁ord
    exact absurd hc₁ord (by norm_num)
  · intro h
    have h1 : (x₃D : ↥(kSub 3 M H)) = 1 := Subtype.ext h
    have h2 : c₃ = 1 := by rw [← hx₃φ, h1, map_one]
    rw [h2] at hc₃ord
    exact absurd hc₃ord (by norm_num)

private theorem W_basic {a : G} (ha : a ∈ kSub 3 M H ⊓ M)
    {σ c₁ c₃ : alternatingGroup (Fin 11)} {D0 : Subgroup ↥(kSub 3 M H)}
    (x₁D : ↥D0) {JG : Subgroup G} {ax₁ x₃G : G} {W : Subgroup G}
    (hax₁def : ax₁ = a * ((x₁D : ↥(kSub 3 M H)) : G))
    (hWdef : W = Subgroup.closure ({ax₁, x₃G} : Set G)) (hW_le_JG : W ≤ JG)
    (hJG_le_MC : JG ≤ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hJG_le_K : JG ≤ kSub 3 M H) (hax₁K : ax₁ ∈ kSub 3 M H)
    (hJstar_ea : CFSG.Open.IsElemAbelian 3
      (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))))
    (hinjJG : ∀ (x : G) (hx : x ∈ JG), ∀ (y : G) (hy : y ∈ JG),
      c.φ ⟨x, hJG_le_K hx⟩ = c.φ ⟨y, hJG_le_K hy⟩ → x = y)
    (hφJG_le : ∀ (y : G) (hy : y ∈ JG),
      c.φ ⟨y, hJG_le_K hy⟩ ∈
        Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))))
    (hφaK : c.φ ⟨a, ha.1⟩ = σ) (hx₁φ : c.φ (x₁D : ↥(kSub 3 M H)) = c₁) :
    ax₁ ∈ W ∧ x₃G ∈ W ∧ W ≤ Subgroup.centralizer ({a} : Set G) ∧
      W = Subgroup.zpowers ax₁ ⊔ Subgroup.zpowers x₃G ∧
      (∀ u ∈ W, ∀ v ∈ W, u * v = v * u) ∧
      (⟨ax₁, hax₁K⟩ : ↥(kSub 3 M H)) = ⟨a, ha.1⟩ * (x₁D : ↥(kSub 3 M H)) ∧
      c.φ ⟨ax₁, hax₁K⟩ = σ * c₁ := by
  have hax₁W : ax₁ ∈ W := by
    rw [hWdef]; exact Subgroup.subset_closure (by simp)
  have hx₃GW : x₃G ∈ W := by
    rw [hWdef]; exact Subgroup.subset_closure (by simp)
  have hW_le_C : W ≤ Subgroup.centralizer ({a} : Set G) :=
    (hW_le_JG.trans hJG_le_MC).trans inf_le_right
  have hW_eq_sup : W = Subgroup.zpowers ax₁ ⊔ Subgroup.zpowers x₃G := by
    rw [hWdef]
    rw [show ({ax₁, x₃G} : Set G) = {ax₁} ∪ {x₃G} from rfl, Subgroup.closure_union,
      Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure]
  have hW_comm : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u := by
    intro u hu v hv
    have h1 : u ∈ JG := hW_le_JG hu
    have h2 : v ∈ JG := hW_le_JG hv
    refine hinjJG (u * v) (JG.mul_mem h1 h2) (v * u) (JG.mul_mem h2 h1) ?_
    have h1' : (⟨u * v, hJG_le_K (JG.mul_mem h1 h2)⟩ : ↥(kSub 3 M H)) =
        ⟨u, hJG_le_K h1⟩ * ⟨v, hJG_le_K h2⟩ := Subtype.ext rfl
    have h2' : (⟨v * u, hJG_le_K (JG.mul_mem h2 h1)⟩ : ↥(kSub 3 M H)) =
        ⟨v, hJG_le_K h2⟩ * ⟨u, hJG_le_K h1⟩ := Subtype.ext rfl
    rw [h1', h2', map_mul, map_mul]
    exact hJstar_ea.comm (hφJG_le u h1) (hφJG_le v h2)
  have hax₁K_eq : (⟨ax₁, hax₁K⟩ : ↥(kSub 3 M H)) =
      ⟨a, ha.1⟩ * (x₁D : ↥(kSub 3 M H)) := Subtype.ext hax₁def
  have hφax₁ : c.φ ⟨ax₁, hax₁K⟩ = σ * c₁ := by
    rw [hax₁K_eq, map_mul, hφaK, hx₁φ]
  exact ⟨hax₁W, hx₃GW, hW_le_C, hW_eq_sup, hW_comm, hax₁K_eq, hφax₁⟩

private theorem W_orders {σ c₁ c₃ : alternatingGroup (Fin 11)}
    {D0 : Subgroup ↥(kSub 3 M H)} (x₃D : ↥D0) {JG : Subgroup G} {ax₁ x₃G : G}
    (hx₃Gdef : x₃G = ((x₃D : ↥(kSub 3 M H)) : G))
    (hx₃φ : c.φ (x₃D : ↥(kSub 3 M H)) = c₃)
    (hJGcube : ∀ y ∈ JG, y ^ 3 = 1) (hx₃JG : x₃G ∈ JG) (hx₃G_ne : x₃G ≠ 1)
    (hclosure_le_of : ∀ (u v : alternatingGroup (Fin 11)),
      σ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
      c₁ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
      c₃ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
      Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ≤
        Subgroup.zpowers u ⊔ Subgroup.zpowers v)
    (hnot_sup₁ : ¬ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ≤
      Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₃)
    (hax₁JG : ax₁ ∈ JG) (hax₁K : ax₁ ∈ kSub 3 M H)
    (hφax₁ : c.φ ⟨ax₁, hax₁K⟩ = σ * c₁) :
    orderOf x₃G = 3 ∧ orderOf ax₁ = 3 ∧
      Subgroup.zpowers ax₁ ⊓ Subgroup.zpowers x₃G = ⊥ := by
  have hord_x₃G : orderOf x₃G = 3 := by
    refine orderOf_eq_prime ?_ hx₃G_ne
    simpa using hJGcube x₃G hx₃JG
  have hord_ax₁ : orderOf ax₁ = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · simpa using hJGcube ax₁ hax₁JG
    · intro h
      apply hnot_sup₁
      have h1 : σ * c₁ = 1 := by
        have h2 : (⟨ax₁, hax₁K⟩ : ↥(kSub 3 M H)) = 1 := Subtype.ext h
        rw [← hφax₁, h2, map_one]
      refine hclosure_le_of c₁ c₃ ?_ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c₁))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₃))
      have hσeq : σ = c₁⁻¹ := by
        calc σ = σ * c₁ * c₁⁻¹ := by group
          _ = 1 * c₁⁻¹ := by rw [h1]
          _ = c₁⁻¹ := one_mul _
      rw [hσeq]
      exact Subgroup.mem_sup_left (Subgroup.inv_mem _ (Subgroup.mem_zpowers c₁))
  refine ⟨hord_x₃G, hord_ax₁, ?_⟩
  by_contra h
  have hne : ∃ z ∈ Subgroup.zpowers ax₁ ⊓ Subgroup.zpowers x₃G, z ≠ 1 := by
    by_contra hc
    apply h
    rw [eq_bot_iff]
    intro z hz
    by_contra hz1
    exact hc ⟨z, hz, hz1⟩
  obtain ⟨z, hz, hz1⟩ := hne
  have hEq : Subgroup.zpowers ax₁ = Subgroup.zpowers x₃G :=
    CFSG.GorensteinWalter.subgroup_eq_of_card_eq_prime_of_common_ne_one
      Nat.prime_three _ _ (by rw [Nat.card_zpowers, hord_ax₁])
      (by rw [Nat.card_zpowers, hord_x₃G]) hz.1 hz.2 hz1
  have hmem : ax₁ ∈ Subgroup.zpowers x₃G := by
    rw [← hEq]; exact Subgroup.mem_zpowers ax₁
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hφk : c.φ ⟨ax₁, hax₁K⟩ = c₃ ^ k := by
    have h1 : (⟨ax₁, hax₁K⟩ : ↥(kSub 3 M H)) = (x₃D : ↥(kSub 3 M H)) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, ← hx₃Gdef]
      exact hk.symm
    rw [h1, map_zpow, hx₃φ]
  have hσc₁ : σ * c₁ = c₃ ^ k := by rw [← hφax₁, hφk]
  apply hnot_sup₁
  refine hclosure_le_of c₁ c₃ ?_ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c₁))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₃))
  have hσeq : σ = c₃ ^ k * c₁⁻¹ := by
    calc σ = σ * c₁ * c₁⁻¹ := by group
      _ = c₃ ^ k * c₁⁻¹ := by rw [hσc₁]
  rw [hσeq]
  exact (Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₃).mul_mem
    (Subgroup.zpow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₃)) k)
    (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers c₁)))

private theorem W_card_ea {JG : Subgroup G} {ax₁ x₃G : G} {W : Subgroup G}
    (hWdef : W = Subgroup.closure ({ax₁, x₃G} : Set G))
    (hW_eq_sup : W = Subgroup.zpowers ax₁ ⊔ Subgroup.zpowers x₃G)
    (hW_comm : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u)
    (hord_ax₁ : orderOf ax₁ = 3) (hord_x₃G : orderOf x₃G = 3)
    (hdisj : Subgroup.zpowers ax₁ ⊓ Subgroup.zpowers x₃G = ⊥)
    (hJGcube : ∀ y ∈ JG, y ^ 3 = 1) (hax₁JG : ax₁ ∈ JG) (hx₃JG : x₃G ∈ JG) :
    Nat.card ↥W = 9 ∧ CFSG.Open.IsElemAbelian 3 W := by
  have hWcard : Nat.card ↥W = 9 := by
    have hcard := CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers ax₁)
      (Subgroup.zpowers x₃G)
      (fun u hu v hv => hW_comm u (by rw [hW_eq_sup]; exact Subgroup.mem_sup_left hu)
        v (by rw [hW_eq_sup]; exact Subgroup.mem_sup_right hv)) hdisj
    rw [hW_eq_sup, hcard, Nat.card_zpowers, Nat.card_zpowers, hord_ax₁, hord_x₃G]
  have hW_ea : CFSG.Open.IsElemAbelian 3 W := by
    have h : CFSG.Open.IsElemAbelian 3 (Subgroup.closure ({ax₁, x₃G} : Set G)) := by
      refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
      · intro u hu v hv
        exact hW_comm u (by rw [hWdef]; exact Subgroup.subset_closure hu)
          v (by rw [hWdef]; exact Subgroup.subset_closure hv)
      · intro u hu
        rcases hu with h | h
        · rw [h]; simpa using hJGcube ax₁ hax₁JG
        · rw [h]; simpa using hJGcube x₃G hx₃JG
    rwa [← hWdef] at h
  exact ⟨hWcard, hW_ea⟩

private theorem W_subgroup {a : G} (ha : a ∈ kSub 3 M H ⊓ M)
    {σ c₁ c₃ : alternatingGroup (Fin 11)} {D0 : Subgroup ↥(kSub 3 M H)}
    (x₁D x₃D : ↥D0) {JG : Subgroup G} {ax₁ x₃G : G} {W : Subgroup G}
    (hax₁def : ax₁ = a * ((x₁D : ↥(kSub 3 M H)) : G))
    (hx₃Gdef : x₃G = ((x₃D : ↥(kSub 3 M H)) : G))
    (hWdef : W = Subgroup.closure ({ax₁, x₃G} : Set G)) (hW_le_JG : W ≤ JG)
    (hJG_le_K : JG ≤ kSub 3 M H)
    (hφaK : c.φ ⟨a, ha.1⟩ = σ) (hx₁φ : c.φ (x₁D : ↥(kSub 3 M H)) = c₁)
    (hx₃φ : c.φ (x₃D : ↥(kSub 3 M H)) = c₃) :
    W.subgroupOf (kSub 3 M H) = Subgroup.closure
        ({⟨a, ha.1⟩ * (x₁D : ↥(kSub 3 M H)), (x₃D : ↥(kSub 3 M H))} :
          Set ↥(kSub 3 M H)) ∧
      (W.subgroupOf (kSub 3 M H)).map c.φ =
        Subgroup.zpowers (σ * c₁) ⊔ Subgroup.zpowers c₃ := by
  have hWsub : W.subgroupOf (kSub 3 M H) = Subgroup.closure
      ({⟨a, ha.1⟩ * (x₁D : ↥(kSub 3 M H)), (x₃D : ↥(kSub 3 M H))} :
        Set ↥(kSub 3 M H)) := by
    rw [hWdef]
    refine Subgroup.map_injective (f := (kSub 3 M H).subtype)
      (kSub 3 M H).subtype_injective ?_
    have hle : Subgroup.closure ({ax₁, x₃G} : Set G) ≤ kSub 3 M H := by
      rw [← hWdef]
      exact hW_le_JG.trans hJG_le_K
    rw [Subgroup.map_subgroupOf_eq_of_le hle, MonoidHom.map_closure]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro (h | h)
      · rw [h]
        exact ⟨(⟨a, ha.1⟩ : ↥(kSub 3 M H)) * (x₁D : ↥(kSub 3 M H)), Or.inl rfl,
          by show a * ((x₁D : ↥(kSub 3 M H)) : G) = ax₁; rw [hax₁def]⟩
      · rw [h]
        exact ⟨(x₃D : ↥(kSub 3 M H)), Or.inr rfl,
          by show ((x₃D : ↥(kSub 3 M H)) : G) = x₃G; rw [hx₃Gdef]⟩
    · rintro ⟨y, rfl | rfl, hzy⟩
      · left
        rw [← hzy]
        show a * ((x₁D : ↥(kSub 3 M H)) : G) = ax₁
        rw [hax₁def]
      · right
        rw [← hzy]
        show ((x₃D : ↥(kSub 3 M H)) : G) = x₃G
        rw [hx₃Gdef]
  refine ⟨hWsub, ?_⟩
  have h1 : c.φ (⟨a, ha.1⟩ * (x₁D : ↥(kSub 3 M H))) = σ * c₁ := by
    rw [map_mul, hφaK, hx₁φ]
  have h2 : c.φ (x₃D : ↥(kSub 3 M H)) = c₃ := hx₃φ
  rw [hWsub, MonoidHom.map_closure,
    show ({⟨a, ha.1⟩ * (x₁D : ↥(kSub 3 M H)), (x₃D : ↥(kSub 3 M H))} :
      Set ↥(kSub 3 M H)) =
      {⟨a, ha.1⟩ * (x₁D : ↥(kSub 3 M H))} ∪ {(x₃D : ↥(kSub 3 M H))} from rfl,
    Set.image_union, Set.image_singleton, Set.image_singleton, h1, h2,
    Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]

private theorem W_not_a {a : G} (ha : a ∈ kSub 3 M H ⊓ M)
    {σ c₁ c₃ : alternatingGroup (Fin 11)} {ax₁ x₃G : G} {W : Subgroup G}
    (hWdef : W = Subgroup.closure ({ax₁, x₃G} : Set G))
    (hφW : (W.subgroupOf (kSub 3 M H)).map c.φ =
      Subgroup.zpowers (σ * c₁) ⊔ Subgroup.zpowers c₃)
    (hφaK : c.φ ⟨a, ha.1⟩ = σ)
    (hnot_sup₂ : ¬ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ≤
      Subgroup.zpowers (σ * c₁) ⊔ Subgroup.zpowers c₃)
    (hclosure_le_of : ∀ (u v : alternatingGroup (Fin 11)),
      σ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
      c₁ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
      c₃ ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
      Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) ≤
        Subgroup.zpowers u ⊔ Subgroup.zpowers v) :
    a ∉ W := by
  intro haW
  have hmem : c.φ ⟨a, ha.1⟩ ∈ (W.subgroupOf (kSub 3 M H)).map c.φ :=
    Subgroup.mem_map_of_mem c.φ (Subgroup.mem_subgroupOf.mpr haW)
  have hσW : σ ∈ Subgroup.zpowers (σ * c₁) ⊔ Subgroup.zpowers c₃ := by
    rw [← hφW, ← hφaK]
    exact hmem
  apply hnot_sup₂
  refine hclosure_le_of (σ * c₁) c₃ hσW ?_
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers c₃))
  have hmem1 : σ⁻¹ * (σ * c₁) ∈ Subgroup.zpowers (σ * c₁) ⊔ Subgroup.zpowers c₃ :=
    (Subgroup.zpowers (σ * c₁) ⊔ Subgroup.zpowers c₃).mul_mem
      (Subgroup.inv_mem _ hσW) (Subgroup.mem_sup_left (Subgroup.mem_zpowers (σ * c₁)))
  have h2 : σ⁻¹ * (σ * c₁) = c₁ := by group
  rwa [h2] at hmem1

private theorem W_inf_O {a : G} (ha3 : orderOf a = 3) {W JG : Subgroup G}
    (hW_le_JG : W ≤ JG)
    (hJO_eq : JG ⊓ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) =
      Subgroup.zpowers a)
    (ha_notW : a ∉ W) :
    W ⊓ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzW, hzO⟩ := Subgroup.mem_inf.mp hz
  have hzJO : z ∈ JG ⊓
      CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) :=
    ⟨hW_le_JG hzW, hzO⟩
  rw [hJO_eq] at hzJO
  by_contra hz1
  have hcard_a : Nat.card ↥(Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, ha3]
  have hdvd : Nat.card ↥(Subgroup.zpowers z) ∣ 3 := by
    rw [← hcard_a]
    exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hzJO)
  have hne1 : Nat.card ↥(Subgroup.zpowers z) ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one, Subgroup.zpowers_eq_bot] at h1
    exact hz1 h1
  have h3 : Nat.card ↥(Subgroup.zpowers z) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have heq : Subgroup.zpowers z = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzJO) (by rw [hcard_a, h3])
  have haW : a ∈ W := by
    have h1 : a ∈ Subgroup.zpowers z := by rw [heq]; exact Subgroup.mem_zpowers a
    exact Subgroup.zpowers_le.mpr hzW h1
  exact ha_notW haW

private theorem D1_data {σ c₁ c₃ : alternatingGroup (Fin 11)}
    (D D0 : Subgroup ↥(kSub 3 M H))
    (hD0def : D0 = D ⊓ (Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11)))).comap c.φ) :
    ∃ D1 : Subgroup ↥(kSub 3 M H),
      D1 = D ⊓ (Subgroup.normalizer (Subgroup.closure ({σ, c₁, c₃} :
        Set (alternatingGroup (Fin 11))) : Set (alternatingGroup (Fin 11)))).comap c.φ ∧
      D0 ≤ D1 ∧ (D0.subgroupOf D1).Normal := by
  let D1 : Subgroup ↥(kSub 3 M H) :=
    D ⊓ (Subgroup.normalizer (Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11))) : Set (alternatingGroup (Fin 11)))).comap c.φ
  have hD0_le_D1 : D0 ≤ D1 := by
    intro x hx
    rw [hD0def] at hx
    obtain ⟨hxD, hxJ⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxD, ?_⟩
    rw [Subgroup.mem_comap] at hxJ ⊢
    exact Subgroup.le_normalizer hxJ
  have hD0norm : (D0.subgroupOf D1).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hD0_le_D1, Subgroup.le_normalizer_iff]
    intro g hg k hk
    obtain ⟨hgD, hgN⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_comap] at hgN
    rw [hD0def] at hk
    obtain ⟨hkD, hkJ⟩ := Subgroup.mem_inf.mp hk
    rw [Subgroup.mem_comap] at hkJ
    rw [hD0def]
    refine Subgroup.mem_inf.mpr ⟨D.mul_mem (D.mul_mem hgD hkD) (D.inv_mem hgD), ?_⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hgN (c.φ k)).mp hkJ
  exact ⟨D1, rfl, hD0_le_D1, hD0norm⟩

private theorem lift_data {a : G} {σ c₁ c₃ v₁ v₂ : alternatingGroup (Fin 11)}
    {D D0 : Subgroup ↥(kSub 3 M H)}
    (hDdef : D = (M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (kSub 3 M H))
    (hmapD : D.map c.φ = a11TwoSetStab 9 10 ⊓
      Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))))
    (hv₁mem : v₁ ∈ a11TwoSetStab 9 10 ⊓
      Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))))
    (hv₂mem : v₂ ∈ a11TwoSetStab 9 10 ⊓
      Subgroup.centralizer ({σ} : Set (alternatingGroup (Fin 11))))
    (hv₁N : v₁ ∈ Subgroup.normalizer
      (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))))
    (hv₂N : v₂ ∈ Subgroup.normalizer
      (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))))
    {D1 : Subgroup ↥(kSub 3 M H)}
    (hD1def : D1 = D ⊓ (Subgroup.normalizer (Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11))) : Set (alternatingGroup (Fin 11)))).comap c.φ)
    (hD0_le_D1 : D0 ≤ D1) (hD0norm : (D0.subgroupOf D1).Normal)
    (hD0map : D0.map c.φ = Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11)))) (P : Sylow 3 D0) :
    ∃ (w₁ w₂ n₁ n₂ : ↥(kSub 3 M H)) (d₁ d₂ : ↥D0),
      w₁ ∈ D1 ∧ w₂ ∈ D1 ∧ c.φ w₁ = v₁ ∧ c.φ w₂ = v₂ ∧
      n₁ = (d₁ : ↥(kSub 3 M H))⁻¹ * w₁ ∧ n₂ = (d₂ : ↥(kSub 3 M H))⁻¹ * w₂ ∧
      (∀ q : ↥D0, q ∈ P → n₁ * (q : ↥(kSub 3 M H)) * n₁⁻¹ ∈
        (P : Subgroup D0).map D0.subtype) ∧
      (∀ q : ↥D0, q ∈ P → n₂ * (q : ↥(kSub 3 M H)) * n₂⁻¹ ∈
        (P : Subgroup D0).map D0.subtype) ∧
      (∃ j ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
        c.φ n₁ = j * v₁) ∧
      (∃ j ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
        c.φ n₂ = j * v₂) := by
  have hv₁D : v₁ ∈ D.map c.φ := by rw [hmapD]; exact hv₁mem
  have hv₂D : v₂ ∈ D.map c.φ := by rw [hmapD]; exact hv₂mem
  obtain ⟨w₁, hw₁D, hw₁φ⟩ := Subgroup.mem_map.mp hv₁D
  obtain ⟨w₂, hw₂D, hw₂φ⟩ := Subgroup.mem_map.mp hv₂D
  have hw₁D1 : w₁ ∈ D1 := by
    rw [hD1def]
    exact Subgroup.mem_inf.mpr ⟨hw₁D, by
      rw [Subgroup.mem_comap, hw₁φ]; exact hv₁N⟩
  have hw₂D1 : w₂ ∈ D1 := by
    rw [hD1def]
    exact Subgroup.mem_inf.mpr ⟨hw₂D, by
      rw [Subgroup.mem_comap, hw₂φ]; exact hv₂N⟩
  obtain ⟨n₁, ⟨d₁, hn₁⟩, hn₁norm⟩ := Ctx.exists_normalizing_conj P
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hD0_le_D1).mp hD0norm hw₁D1)
  obtain ⟨n₂, ⟨d₂, hn₂⟩, hn₂norm⟩ := Ctx.exists_normalizing_conj P
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hD0_le_D1).mp hD0norm hw₂D1)
  have hn₁φ : ∃ j ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
      c.φ n₁ = j * v₁ := by
    refine ⟨(c.φ d₁)⁻¹, ?_, ?_⟩
    · have h : c.φ d₁ ∈ D0.map c.φ := Subgroup.mem_map_of_mem c.φ d₁.2
      rw [hD0map] at h
      exact (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))).inv_mem h
    · rw [hn₁, map_mul, map_inv, hw₁φ]
  have hn₂φ : ∃ j ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
      c.φ n₂ = j * v₂ := by
    refine ⟨(c.φ d₂)⁻¹, ?_, ?_⟩
    · have h : c.φ d₂ ∈ D0.map c.φ := Subgroup.mem_map_of_mem c.φ d₂.2
      rw [hD0map] at h
      exact (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))).inv_mem h
    · rw [hn₂, map_mul, map_inv, hw₂φ]
  exact ⟨w₁, w₂, n₁, n₂, d₁, d₂, hw₁D1, hw₂D1, hw₁φ, hw₂φ, hn₁, hn₂, hn₁norm, hn₂norm,
    hn₁φ, hn₂φ⟩

private theorem commutator_x₃ {σ c₁ c₃ v₁ : alternatingGroup (Fin 11)}
    {D0 : Subgroup ↥(kSub 3 M H)} (P : Sylow 3 D0) (x₃D : ↥D0)
    (PK : Subgroup ↥(kSub 3 M H)) (n₁ : ↥(kSub 3 M H))
    (hv₁c₃ : v₁ * c₃ * v₁⁻¹ = c₃⁻¹)
    (hJconj : ∀ j ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
      ∀ z ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
      j * z * j⁻¹ = z)
    (hx₃φ : c.φ (x₃D : ↥(kSub 3 M H)) = c₃)
    (hPKdef : PK = (P : Subgroup ↥D0).map D0.subtype)
    (hx₃P : x₃D ∈ P) (hx₃PK : (x₃D : ↥(kSub 3 M H)) ∈ PK)
    (hinjPK : ∀ x y : ↥(kSub 3 M H), x ∈ PK → y ∈ PK → c.φ x = c.φ y → x = y)
    (hn₁norm : ∀ q : ↥D0, q ∈ P → n₁ * (q : ↥(kSub 3 M H)) * n₁⁻¹ ∈
      (P : Subgroup D0).map D0.subtype)
    (hn₁φ : ∃ j ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
      c.φ n₁ = j * v₁) :
    ((n₁ : ↥(kSub 3 M H)) : G) * ((x₃D : ↥(kSub 3 M H)) : G) *
        ((n₁ : ↥(kSub 3 M H)) : G)⁻¹ =
      (((x₃D : ↥(kSub 3 M H)) : G))⁻¹ := by
  obtain ⟨j₁, hj₁J, hj₁⟩ := hn₁φ
  have huPK : n₁ * (x₃D : ↥(kSub 3 M H)) * n₁⁻¹ ∈ PK := by
    rw [hPKdef]; exact hn₁norm x₃D hx₃P
  have huinv : (x₃D : ↥(kSub 3 M H))⁻¹ ∈ PK := PK.inv_mem hx₃PK
  have huφ : c.φ (n₁ * (x₃D : ↥(kSub 3 M H)) * n₁⁻¹) = c₃⁻¹ := by
    rw [map_mul, map_mul, map_inv, hj₁, hx₃φ]
    calc (j₁ * v₁) * c₃ * (j₁ * v₁)⁻¹ = j₁ * (v₁ * c₃ * v₁⁻¹) * j₁⁻¹ := by group
      _ = j₁ * c₃⁻¹ * j₁⁻¹ := by rw [hv₁c₃]
      _ = c₃⁻¹ := hJconj j₁ hj₁J _
        ((Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))).inv_mem
          (Subgroup.subset_closure (by simp)))
  have hinvφ : c.φ ((x₃D : ↥(kSub 3 M H))⁻¹) = c₃⁻¹ := by rw [map_inv, hx₃φ]
  have heq : n₁ * (x₃D : ↥(kSub 3 M H)) * n₁⁻¹ = (x₃D : ↥(kSub 3 M H))⁻¹ :=
    hinjPK _ _ huPK huinv (by rw [huφ, hinvφ])
  simpa using congrArg (fun z : ↥(kSub 3 M H) => (z : G)) heq

private theorem commutator_x₁ {a : G} (ha : a ∈ kSub 3 M H ⊓ M)
    {σ c₁ c₃ v₂ : alternatingGroup (Fin 11)} {D0 : Subgroup ↥(kSub 3 M H)}
    (P : Sylow 3 D0) (x₁D : ↥D0) (PK : Subgroup ↥(kSub 3 M H)) (n₂ : ↥(kSub 3 M H))
    (hσdef : σ = c.φ ⟨a, ha.1⟩)
    (hv₂c₁ : v₂ * c₁ * v₂⁻¹ = σ * c₁⁻¹)
    (hJconj : ∀ j ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
      ∀ z ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
      j * z * j⁻¹ = z)
    (hx₁φ : c.φ (x₁D : ↥(kSub 3 M H)) = c₁)
    (hPKdef : PK = (P : Subgroup ↥D0).map D0.subtype)
    (hx₁P : x₁D ∈ P) (hx₁PK : (x₁D : ↥(kSub 3 M H)) ∈ PK)
    (haPK : (⟨a, ha.1⟩ : ↥(kSub 3 M H)) ∈ PK)
    (hinjPK : ∀ x y : ↥(kSub 3 M H), x ∈ PK → y ∈ PK → c.φ x = c.φ y → x = y)
    (hn₂norm : ∀ q : ↥D0, q ∈ P → n₂ * (q : ↥(kSub 3 M H)) * n₂⁻¹ ∈
      (P : Subgroup D0).map D0.subtype)
    (hn₂φ : ∃ j ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))),
      c.φ n₂ = j * v₂) :
    ((n₂ : ↥(kSub 3 M H)) : G) * ((x₁D : ↥(kSub 3 M H)) : G) *
        ((n₂ : ↥(kSub 3 M H)) : G)⁻¹ =
      a * (((x₁D : ↥(kSub 3 M H)) : G))⁻¹ := by
  obtain ⟨j₂, hj₂J, hj₂⟩ := hn₂φ
  have huPK : n₂ * (x₁D : ↥(kSub 3 M H)) * n₂⁻¹ ∈ PK := by
    rw [hPKdef]; exact hn₂norm x₁D hx₁P
  have huinv : (⟨a, ha.1⟩ : ↥(kSub 3 M H)) * (x₁D : ↥(kSub 3 M H))⁻¹ ∈ PK :=
    PK.mul_mem haPK (PK.inv_mem hx₁PK)
  have hσc₁J : σ * c₁⁻¹ ∈ Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11))) :=
    (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))).mul_mem
      (Subgroup.subset_closure (by simp))
      ((Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))).inv_mem
        (Subgroup.subset_closure (by simp)))
  have huφ : c.φ (n₂ * (x₁D : ↥(kSub 3 M H)) * n₂⁻¹) = σ * c₁⁻¹ := by
    rw [map_mul, map_mul, map_inv, hj₂, hx₁φ]
    calc (j₂ * v₂) * c₁ * (j₂ * v₂)⁻¹ = j₂ * (v₂ * c₁ * v₂⁻¹) * j₂⁻¹ := by group
      _ = j₂ * (σ * c₁⁻¹) * j₂⁻¹ := by rw [hv₂c₁]
      _ = σ * c₁⁻¹ := hJconj j₂ hj₂J _ hσc₁J
  have hinvφ : c.φ ((⟨a, ha.1⟩ : ↥(kSub 3 M H)) * (x₁D : ↥(kSub 3 M H))⁻¹) =
      σ * c₁⁻¹ := by
    rw [map_mul, map_inv, hσdef.symm, hx₁φ]
  have heq : n₂ * (x₁D : ↥(kSub 3 M H)) * n₂⁻¹ =
      (⟨a, ha.1⟩ : ↥(kSub 3 M H)) * (x₁D : ↥(kSub 3 M H))⁻¹ :=
    hinjPK _ _ huPK huinv (by rw [huφ, hinvφ])
  simpa using congrArg (fun z : ↥(kSub 3 M H) => (z : G)) heq


private theorem lift_mem_D {σ c₁ c₃ : alternatingGroup (Fin 11)}
    {D D0 D1 : Subgroup ↥(kSub 3 M H)}
    (hD1def : D1 = D ⊓ (Subgroup.normalizer (Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11))) : Set (alternatingGroup (Fin 11)))).comap c.φ)
    (hD0_le_D1 : D0 ≤ D1) {d : ↥D0} {w n : ↥(kSub 3 M H)}
    (hwD1 : w ∈ D1) (hn : n = (d : ↥(kSub 3 M H))⁻¹ * w) : n ∈ D := by
  have h1 : n ∈ D1 := by
    rw [hn]
    exact D1.mul_mem (D1.inv_mem (hD0_le_D1 d.2)) hwD1
  rw [hD1def] at h1
  exact h1.1


private theorem lift_mem_MC {a : G} {D D0 D1 : Subgroup ↥(kSub 3 M H)}
    (hDdef : D = (M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (kSub 3 M H))
    {σ c₁ c₃ : alternatingGroup (Fin 11)}
    (hD1def : D1 = D ⊓ (Subgroup.normalizer (Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11))) : Set (alternatingGroup (Fin 11)))).comap c.φ)
    (hD0_le_D1 : D0 ≤ D1) {d : ↥D0} {w n : ↥(kSub 3 M H)}
    (hwD1 : w ∈ D1) (hn : n = (d : ↥(kSub 3 M H))⁻¹ * w) :
    ((n : ↥(kSub 3 M H)) : G) ∈ M ⊓ Subgroup.centralizer ({a} : Set G) := by
  have hnD := lift_mem_D c hD1def hD0_le_D1 hwD1 hn
  rw [hDdef, Subgroup.mem_subgroupOf] at hnD
  exact hnD

private theorem star_map (hpp : p.Prime) {a : G} (W : Subgroup G)
    (hW_le_C : W ≤ Subgroup.centralizer ({a} : Set G))
    (hW_inf_O : W ⊓ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) = ⊥)
    (hW_comm : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u)
    (hW_ea : CFSG.Open.IsElemAbelian 3 W) :
    ∃ f : ↥W →* StarGroup p (Subgroup.centralizer ({a} : Set G)),
      (∀ x : ↥W, f x = QuotientGroup.mk'
        (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
          (G := ↥(Subgroup.centralizer ({a} : Set G))) p) ⟨(x : G), hW_le_C x.2⟩) ∧
      Function.Injective f ∧ (∀ u v : ↥W, u * v = v * u) ∧ (∀ u : ↥W, u ^ 3 = 1) := by
  classical
  let Cc : Subgroup G := Subgroup.centralizer ({a} : Set G)
  let ιW : ↥W →* ↥Cc :=
    { toFun := fun x => ⟨(x : G), hW_le_C x.2⟩
      map_one' := rfl
      map_mul' := fun x y => rfl }
  let f : ↥W →* StarGroup p Cc :=
    (QuotientGroup.mk' (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
      (G := ↥Cc) p)).comp ιW
  have hf_apply : ∀ x : ↥W, f x = QuotientGroup.mk'
      (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥Cc) p)
      ⟨(x : G), hW_le_C x.2⟩ := fun x => rfl
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : G) ∈ CFSG.Open.relPPrimeCore p Cc := by
      have h1 : (ιW x : ↥Cc) ∈
          CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥Cc) p :=
        (QuotientGroup.eq_one_iff (ιW x)).mp hx
      have hmain : Cc.subtype (ιW x) ∈ CFSG.Open.relPPrimeCore p Cc := by
        rw [CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.NineEightFour.relPPrimeCore_eq_map hpp Cc]
        exact Subgroup.mem_map_of_mem Cc.subtype h1
      have heq : Cc.subtype (ιW x) = (x : G) := rfl
      rwa [heq] at hmain
    have hmem : (x : G) ∈ W ⊓ CFSG.Open.relPPrimeCore p Cc := ⟨x.2, hxO⟩
    rw [hW_inf_O] at hmem
    exact Subtype.ext (by simpa using hmem)
  exact ⟨f, hf_apply, hf_inj, fun u v => Subtype.ext (hW_comm u.1 u.2 v.1 v.2),
    fun u => Subtype.ext (by simpa using hW_ea.2 u.1 u.2)⟩

private theorem star_commutators {a : G} (Cc : Subgroup G)
    (hCc : Cc = Subgroup.centralizer ({a} : Set G))
    (πC : ↥Cc →* StarGroup p Cc)
    (hπC : πC = QuotientGroup.mk'
      (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥Cc) p))
    {n₁c n₂c x₁c x₃c ac : ↥Cc}
    (hx₁c_cube : x₁c ^ 3 = 1) (hx₃c_cube : x₃c ^ 3 = 1)
    (hcomm₁c : n₁c * x₃c * n₁c⁻¹ = x₃c⁻¹)
    (hcomm₂c : n₂c * x₁c * n₂c⁻¹ = ac * x₁c⁻¹) :
    ⁅πC n₁c, πC x₃c⁆ = πC x₃c ∧ ⁅πC n₂c, πC x₁c⁆ = πC ac * πC x₁c := by
  constructor
  · have h4 : πC n₁c * πC x₃c * (πC n₁c)⁻¹ = (πC x₃c)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, hcomm₁c, map_inv]
    have hb : (πC x₃c) ^ 3 = 1 := by rw [← map_pow, hx₃c_cube, map_one]
    calc ⁅πC n₁c, πC x₃c⁆ = (πC n₁c * πC x₃c * (πC n₁c)⁻¹) * (πC x₃c)⁻¹ := rfl
      _ = (πC x₃c)⁻¹ * (πC x₃c)⁻¹ := by rw [h4]
      _ = πC x₃c := by
        rw [CFSG.LocalAnalysis.ComponentInitial.inv_eq_sq_of_pow_three hb]
        calc (πC x₃c) ^ 2 * (πC x₃c) ^ 2 = (πC x₃c) ^ (2 + 2) := (pow_add _ 2 2).symm
          _ = (πC x₃c) ^ 3 * πC x₃c := by
            rw [show 2 + 2 = 3 + 1 from rfl, pow_add, pow_one]
          _ = πC x₃c := by rw [hb, one_mul]
  · have h4 : πC n₂c * πC x₁c * (πC n₂c)⁻¹ = πC ac * (πC x₁c)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, hcomm₂c, map_mul, map_inv]
    have hb : (πC x₁c) ^ 3 = 1 := by rw [← map_pow, hx₁c_cube, map_one]
    calc ⁅πC n₂c, πC x₁c⁆ =
        (πC n₂c * πC x₁c * (πC n₂c)⁻¹) * (πC x₁c)⁻¹ := rfl
      _ = (πC ac * (πC x₁c)⁻¹) * (πC x₁c)⁻¹ := by rw [h4]
      _ = πC ac * ((πC x₁c)⁻¹ * (πC x₁c)⁻¹) := by group
      _ = πC ac * πC x₁c := by
        rw [CFSG.LocalAnalysis.ComponentInitial.inv_eq_sq_of_pow_three hb]
        congr 1
        calc (πC x₁c) ^ 2 * (πC x₁c) ^ 2 = (πC x₁c) ^ (2 + 2) := (pow_add _ 2 2).symm
          _ = (πC x₁c) ^ 3 * πC x₁c := by
            rw [show 2 + 2 = 3 + 1 from rfl, pow_add, pow_one]
          _ = πC x₁c := by rw [hb, one_mul]

private theorem star_generator_mem {a : G} (ha : a ∈ kSub 3 M H ⊓ M)
    {W : Subgroup G} (hW_le_C : W ≤ Subgroup.centralizer ({a} : Set G))
    {ax₁ x₃G : G} (hax₁W : ax₁ ∈ W) (hx₃GW : x₃G ∈ W)
    {x₁K x₃K n₁ n₂ : ↥(kSub 3 M H)}
    (hax₁def : ax₁ = a * (x₁K : G)) (hx₃Gdef : x₃G = (x₃K : G))
    (hx₁MC : (x₁K : G) ∈ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hx₃MC : (x₃K : G) ∈ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hn₁MC : (n₁ : G) ∈ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hn₂MC : (n₂ : G) ∈ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hx₁cube : (x₁K : G) ^ 3 = 1) (hx₃cube : (x₃K : G) ^ 3 = 1)
    (hcomm₁ : (n₁ : G) * (x₃K : G) * (n₁ : G)⁻¹ = ((x₃K : G))⁻¹)
    (hcomm₂ : (n₂ : G) * (x₁K : G) * (n₂ : G)⁻¹ = a * ((x₁K : G))⁻¹)
    (f : ↥W →* StarGroup p (Subgroup.centralizer ({a} : Set G)))
    (hf_apply : ∀ x : ↥W, f x = QuotientGroup.mk'
      (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore
        (G := ↥(Subgroup.centralizer ({a} : Set G))) p) ⟨(x : G), hW_le_C x.2⟩) :
    f ⟨x₃G, hx₃GW⟩ ∈ ⁅starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M),
      starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M)⁆ ∧
    f ⟨ax₁, hax₁W⟩ ∈ ⁅starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M),
      starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M)⁆ := by
  classical
  let Cc : Subgroup G := Subgroup.centralizer ({a} : Set G)
  let πC : ↥Cc →* StarGroup p Cc := QuotientGroup.mk'
    (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥Cc) p)
  have haCent : a ∈ Cc := by
    rw [show Cc = Subgroup.centralizer ({a} : Set G) from rfl, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rfl
  let n₁c : ↥Cc := ⟨(n₁ : G), hn₁MC.2⟩
  let n₂c : ↥Cc := ⟨(n₂ : G), hn₂MC.2⟩
  let x₁c : ↥Cc := ⟨(x₁K : G), hx₁MC.2⟩
  let x₃c : ↥Cc := ⟨(x₃K : G), hx₃MC.2⟩
  let ac : ↥Cc := ⟨a, haCent⟩
  have hx₃c_cube : x₃c ^ 3 = 1 := Subtype.ext hx₃cube
  have hx₁c_cube : x₁c ^ 3 = 1 := Subtype.ext hx₁cube
  have hcomm₁c : n₁c * x₃c * n₁c⁻¹ = x₃c⁻¹ := Subtype.ext hcomm₁
  have hcomm₂c : n₂c * x₁c * n₂c⁻¹ = ac * x₁c⁻¹ := Subtype.ext hcomm₂
  have hn₁N : πC n₁c ∈ starImg p Cc (Cc ⊓ M) :=
    Subgroup.mem_map_of_mem πC (Subgroup.mem_subgroupOf.mpr ⟨hn₁MC.2, hn₁MC.1⟩)
  have hn₂N : πC n₂c ∈ starImg p Cc (Cc ⊓ M) :=
    Subgroup.mem_map_of_mem πC (Subgroup.mem_subgroupOf.mpr ⟨hn₂MC.2, hn₂MC.1⟩)
  have hx₃N : πC x₃c ∈ starImg p Cc (Cc ⊓ M) :=
    Subgroup.mem_map_of_mem πC (Subgroup.mem_subgroupOf.mpr ⟨hx₃MC.2, hx₃MC.1⟩)
  have hx₁N : πC x₁c ∈ starImg p Cc (Cc ⊓ M) :=
    Subgroup.mem_map_of_mem πC (Subgroup.mem_subgroupOf.mpr ⟨hx₁MC.2, hx₁MC.1⟩)
  obtain ⟨hcx₃, hcx₁⟩ := star_commutators Cc rfl πC rfl hx₁c_cube hx₃c_cube hcomm₁c hcomm₂c
  have hfx₃ : f ⟨x₃G, hx₃GW⟩ = πC x₃c := by
    rw [hf_apply]
    congr 1
    exact Subtype.ext hx₃Gdef
  have hfax₁ : f ⟨ax₁, hax₁W⟩ = πC ac * πC x₁c := by
    rw [hf_apply]
    have h1 : (⟨ax₁, hW_le_C hax₁W⟩ : ↥Cc) = ac * x₁c := by
      refine Subtype.ext ?_
      show ax₁ = ((ac * x₁c : ↥Cc) : G)
      rw [Subgroup.coe_mul]
      rw [show ((ac : ↥Cc) : G) = a from rfl, show ((x₁c : ↥Cc) : G) = (x₁K : G) from rfl,
        hax₁def]
    rw [h1, map_mul]
  exact ⟨by rw [hfx₃, ← hcx₃]; exact Subgroup.commutator_mem_commutator hn₁N hx₃N,
    by rw [hfax₁, ← hcx₁]; exact Subgroup.commutator_mem_commutator hn₂N hx₁N⟩

private theorem rank_NN {a : G} {W : Subgroup G} {ax₁ x₃G : G}
    (hax₁W : ax₁ ∈ W) (hx₃GW : x₃G ∈ W)
    (hWdef : W = Subgroup.closure ({ax₁, x₃G} : Set G)) (hWcard : Nat.card ↥W = 9)
    (f : ↥W →* StarGroup p (Subgroup.centralizer ({a} : Set G)))
    (hf_inj : Function.Injective f) (hf_comm : ∀ u v : ↥W, u * v = v * u)
    (hf_pow : ∀ u : ↥W, u ^ 3 = 1)
    (hmem₁ : f ⟨ax₁, hax₁W⟩ ∈ ⁅starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M),
      starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M)⁆)
    (hmem₂ : f ⟨x₃G, hx₃GW⟩ ∈ ⁅starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M),
      starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M)⁆) :
    2 ≤ CFSG.Open.pRank 3 ⁅starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M),
      starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M)⁆ := by
  have htop : (⊤ : Subgroup ↥W) = Subgroup.closure
      ({(⟨ax₁, hax₁W⟩ : ↥W), (⟨x₃G, hx₃GW⟩ : ↥W)} : Set ↥W) := by
    apply Subgroup.map_injective (f := W.subtype) W.subtype_injective
    rw [MonoidHom.map_closure]
    have h1 : (⊤ : Subgroup ↥W).map W.subtype = W := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, -, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have h3 : Subgroup.closure
        (W.subtype '' ({(⟨ax₁, hax₁W⟩ : ↥W), (⟨x₃G, hx₃GW⟩ : ↥W)} : Set ↥W)) = W := by
      have himg : W.subtype '' ({(⟨ax₁, hax₁W⟩ : ↥W), (⟨x₃G, hx₃GW⟩ : ↥W)} :
          Set ↥W) = ({ax₁, x₃G} : Set G) := by
        ext z
        simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨y, h | h, rfl⟩ <;> simp [h]
        · rintro (rfl | rfl)
          · exact ⟨_, Or.inl rfl, rfl⟩
          · exact ⟨_, Or.inr rfl, rfl⟩
      rw [himg, hWdef.symm]
    rw [h1]
    exact h3.symm
  have hfr : f.range ≤ ⁅starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M),
      starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M)⁆ := by
    rw [MonoidHom.range_eq_map, htop, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro z ⟨y, h | h, rfl⟩
    · rw [h]; exact hmem₁
    · rw [h]; exact hmem₂
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hf_comm hf_pow
    (k := 2) ?_ f hf_inj hfr
  rw [hWcard]
  norm_num

private theorem final_false (c : Ctx G M H E Q) (h1 : NineFourTwoSigmaGen)
    (hKF2 : KFactNineFourStronglyEmbedded)
    (hp : p ∈ sigmaSet G M) {a : G} (ha : a ∈ kSub 3 M H ⊓ M) (ha3 : orderOf a = 3)
    (hrank : 2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer ({a} : Set G)))
    (hpp : p.Prime) (hp5 : 5 ≤ p) {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (Subgroup.centralizer ({a} : Set G)) F' p)
    (h2rank : 2 ≤ CFSG.Open.pRank 3 ⁅starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M),
      starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M)⁆) : False := by
  have hlist : CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup p
      ↥(CFSG.generalizedFitting (StarGroup p (Subgroup.centralizer ({a} : Set G)))) := by
    rw [s.generalizedFitting_eq_kStar h1]
    exact (s.kStructure h1).2.2.2
  have hO : CFSG.pPrimeCore 3 ↥(starImg p (Subgroup.centralizer ({a} : Set G))
      (Subgroup.centralizer ({a} : Set G) ⊓ M)) = ⊥ :=
    hKF2 p hpp hp5 (StarGroup p (Subgroup.centralizer ({a} : Set G))) hlist
      (starImg p (Subgroup.centralizer ({a} : Set G))
        (Subgroup.centralizer ({a} : Set G) ⊓ M)) s.isStronglyPEmbedded_starImg
      (Or.inr h2rank)
  exact c.false_of_pPrimeCore_starImg_eq_bot hp ha.2 ha3 hrank s hO


private theorem JO_stage (c : Ctx G M H E Q) (h1 : NineFourTwoSigmaGen)
    (h2 : NineTwelveOneSigmaStrong) (hKF1 : KFactNineFourRankOneAut)
    (hKF2 : KFactNineFourStronglyEmbedded) (hp : p ∈ sigmaSet G M) {a : G}
    (ha : a ∈ kSub 3 M H ⊓ M) (ha3 : orderOf a = 3) {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (Subgroup.centralizer ({a} : Set G)) F' p)
    {σ c₁ c₃ : alternatingGroup (Fin 11)} (hσdef : σ = c.φ ⟨a, ha.1⟩)
    (hσord : orderOf σ = 3)
    (hσc₃supp : ((σ * c₃ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 9)
    {D D0 : Subgroup ↥(kSub 3 M H)}
    (hDdef : D = (M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (kSub 3 M H))
    (hD0def : D0 = D ⊓ (Subgroup.closure ({σ, c₁, c₃} :
      Set (alternatingGroup (Fin 11)))).comap c.φ)
    {PK : Subgroup ↥(kSub 3 M H)} (hPK_le_D0 : PK ≤ D0)
    (hφPK_le : ∀ x ∈ PK,
      c.φ x ∈ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))))
    (hinjPK : ∀ x y : ↥(kSub 3 M H), x ∈ PK → y ∈ PK → c.φ x = c.φ y → x = y)
    (haPK : (⟨a, ha.1⟩ : ↥(kSub 3 M H)) ∈ PK)
    (hbound : ∀ Y : Subgroup (alternatingGroup (Fin 11)),
      Y ≤ Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11))) →
      (∀ y ∈ Y, y ≠ 1 → (y : Equiv.Perm (Fin 11)).support.card = 6) → Nat.card ↥Y ≤ 3)
    {JG : Subgroup G} (hJGdef : JG = PK.map (kSub 3 M H).subtype)
    (hJG_le_K : JG ≤ kSub 3 M H)
    (hJG_le_MC : JG ≤ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hJG_p : IsPGroup 3 JG) (hJGcube : ∀ y ∈ JG, y ^ 3 = 1) (haJG : a ∈ JG)
    (x₃D : ↥D0) (hx₃JG : ((x₃D : ↥(kSub 3 M H)) : G) ∈ JG)
    (hx₃φ : c.φ (x₃D : ↥(kSub 3 M H)) = c₃) :
    JG ⊓ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) =
      Subgroup.zpowers a := by
  have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  have hp3 : p ≠ 3 := by have := c.five_le hp; omega
  have hOa : Subgroup.zpowers a ≤
      CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) :=
    zpowers_le_relPPrimeCore_centralizer hpp hp3 ha3
  have hPKD0 : PK ≤ (M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (kSub 3 M H) ⊓
      (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))).comap c.φ := by
    have h1 : (M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf (kSub 3 M H) ⊓
        (Subgroup.closure ({σ, c₁, c₃} : Set (alternatingGroup (Fin 11)))).comap c.φ = D0 := by
      rw [hD0def, hDdef]
    rw [h1]
    exact hPK_le_D0
  have hfalse9 := JG_support_nine_false c h1 h2 hp s hJG_le_K hJG_le_MC hJGcube
  have hleO3 := JG_le_relPPrimeCore_of_support_three c h1 h2 hKF1 hKF2 hp s
    hJG_le_K hJG_le_MC hJGcube hJG_p
  have hsupp_six := JG_support_six c h1 h2 hKF1 hKF2 hp s ha hσdef hσc₃supp x₃D
    hJG_le_K hJG_le_MC hJGcube haJG hx₃JG hx₃φ hfalse9 hleO3
  exact JO_eq c ha hσdef hσord hφPK_le hinjPK haPK hOa hbound hJGdef hJG_le_K
    haJG hsupp_six

private theorem final_stage (c : Ctx G M H E Q) (h1 : NineFourTwoSigmaGen)
    (hKF2 : KFactNineFourStronglyEmbedded) (hp : p ∈ sigmaSet G M) {a : G}
    (ha : a ∈ kSub 3 M H ⊓ M) (ha3 : orderOf a = 3)
    (hrank : 2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer ({a} : Set G)))
    (hpp : p.Prime) (hp5 : 5 ≤ p) {Q' F' : Subgroup G}
    (s : O1217.Setting1417 G M Q' (Subgroup.centralizer ({a} : Set G)) F' p)
    {W : Subgroup G} (hW_le_C : W ≤ Subgroup.centralizer ({a} : Set G))
    (hW_inf_O : W ⊓ CFSG.Open.relPPrimeCore p (Subgroup.centralizer ({a} : Set G)) = ⊥)
    (hW_comm : ∀ u ∈ W, ∀ v ∈ W, u * v = v * u)
    (hW_ea : CFSG.Open.IsElemAbelian 3 W)
    {ax₁ x₃G : G} (hax₁W : ax₁ ∈ W) (hx₃GW : x₃G ∈ W)
    (hWdef : W = Subgroup.closure ({ax₁, x₃G} : Set G)) (hWcard : Nat.card ↥W = 9)
    {x₁K x₃K n₁ n₂ : ↥(kSub 3 M H)}
    (hax₁def : ax₁ = a * (x₁K : G)) (hx₃Gdef : x₃G = (x₃K : G))
    (hx₁MC : (x₁K : G) ∈ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hx₃MC : (x₃K : G) ∈ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hn₁MC : (n₁ : G) ∈ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hn₂MC : (n₂ : G) ∈ M ⊓ Subgroup.centralizer ({a} : Set G))
    (hx₁cube : (x₁K : G) ^ 3 = 1) (hx₃cube : (x₃K : G) ^ 3 = 1)
    (hcomm₁ : (n₁ : G) * (x₃K : G) * (n₁ : G)⁻¹ = ((x₃K : G))⁻¹)
    (hcomm₂ : (n₂ : G) * (x₁K : G) * (n₂ : G)⁻¹ = a * ((x₁K : G))⁻¹) : False := by
  obtain ⟨f, hf_apply, hf_inj, hf_comm, hf_pow⟩ :=
    star_map hpp W hW_le_C hW_inf_O hW_comm hW_ea
  obtain ⟨hmem₁, hmem₂⟩ := star_generator_mem ha hW_le_C hax₁W hx₃GW hax₁def hx₃Gdef
    hx₁MC hx₃MC hn₁MC hn₂MC hx₁cube hx₃cube hcomm₁ hcomm₂ f hf_apply
  exact final_false c h1 hKF2 hp ha ha3 hrank hpp hp5 s
    (rank_NN hax₁W hx₃GW hWdef hWcard f hf_inj hf_comm hf_pow hmem₂ hmem₁)

theorem false_of_card_support_eq_six (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong)
    (hKF1 : KFactNineFourRankOneAut) (hKF2 : KFactNineFourStronglyEmbedded) {p : ℕ}
    (hp : p ∈ sigmaSet G M) {a : G} (ha : a ∈ kSub 3 M H ⊓ M) (ha3 : orderOf a = 3)
    (hs : ((c.φ ⟨a, ha.1⟩ : alternatingGroup (Fin 11)) : Equiv.Perm (Fin 11)).support.card = 6)
    (hrank : 2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer ({a} : Set G))) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpp : p.Prime := CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime p hp.1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp5 : 5 ≤ p := c.five_le hp
  have hp3 : p ≠ 3 := by omega
  obtain ⟨Q', F', s⟩ := c.exists_setting1417 hp ha ha3 (le_of_eq hs) hrank
  let σ : alternatingGroup (Fin 11) := c.φ ⟨a, ha.1⟩
  have hσdef : σ = c.φ ⟨a, ha.1⟩ := rfl
  have hσS : σ ∈ a11TwoSetStab 9 10 := by
    rw [hσdef]; exact (c.mem_M_iff ⟨a, ha.1⟩).mp ha.2
  have hσord : orderOf σ = 3 := by
    rw [hσdef]; exact c.orderOf_φ (by simpa using ha3)
  obtain ⟨c₁, c₃, v₁, v₂, hc₁S, hc₃S, hc₁ord, hc₃ord, hc₁supp, hc₃supp, hσc₃supp,
    hcommσc₁, hcommσc₃, hcommc₁c₃, hJcard, hbound, hv₁mem, hv₂mem, hv₁c₁, hv₁c₃, hv₂c₁,
    hv₂c₃, hσc₁ord, hnot_sup₁, hnot_sup₂, hclosure_le_of, hJconj, hv₁N, hv₂N, hJstar_ea,
    hJstar_cube, hJstar_p⟩ := a11_data σ hσS hσord hs
  obtain ⟨D, hDdef, hmapD, hJstar_le_D⟩ :=
    D_data c ha ha3 hσdef hσS hc₁S hc₃S hcommσc₁ hcommσc₃
  obtain ⟨D0, hD0def, hD0map, haD0⟩ := D0_data c ha ha3 hσdef D hDdef hJstar_le_D
  obtain ⟨P, haP, hPsurj⟩ := sylow_data c ha ha3 D0 haD0 hD0map hJcard
  obtain ⟨PK, hPKdef, hPK_le_D0, hφPK_le, hPKp, hPKker, hinjPK, hPKcube⟩ :=
    PK_data c D0 P hD0map hJstar_cube
  obtain ⟨JG, x₁D, x₃D, hJGdef, hx₁P, hx₃P, hx₁φ, hx₃φ, hx₁PK, hx₃PK, hx₁JG, hx₃JG,
    hJG_le_K, hJG_le_MC, hJG_p, hJGcube, haPK, haJG⟩ :=
    JG_data c ha D D0 P PK hDdef hD0def hPKdef hPK_le_D0 hPKp hPKcube hPsurj haD0 haP
  obtain ⟨hinjJG, hφJG_le⟩ := injJG_data c PK JG hJGdef hJG_le_K hinjPK hφPK_le
  have hJO_eq := JO_stage c h1 h2 hKF1 hKF2 hp ha ha3 s hσdef hσord hσc₃supp hDdef hD0def
    hPK_le_D0 hφPK_le hinjPK haPK hbound hJGdef hJG_le_K hJG_le_MC hJG_p hJGcube haJG x₃D
    hx₃JG hx₃φ
  obtain ⟨ax₁, x₃G, W, hax₁def, hx₃Gdef, hWdef, hax₁JG, hx₃JG', hW_le_JG, hx₁G_ne,
    hx₃G_ne⟩ := W_data c ha x₁D x₃D hJG_le_K haJG hx₁JG hx₃JG hc₁ord hc₃ord hx₁φ hx₃φ
  have hax₁K : ax₁ ∈ kSub 3 M H := hJG_le_K hax₁JG
  obtain ⟨hax₁W, hx₃GW, hW_le_C, hW_eq_sup, hW_comm, hax₁K_eq, hφax₁⟩ :=
    W_basic c ha x₁D hax₁def hWdef hW_le_JG hJG_le_MC hJG_le_K hax₁K hJstar_ea hinjJG hφJG_le
      (hσdef.symm) hx₁φ
  obtain ⟨hord_x₃G, hord_ax₁, hdisj⟩ := W_orders c x₃D hx₃Gdef hx₃φ hJGcube hx₃JG' hx₃G_ne
    hclosure_le_of hnot_sup₁ hax₁JG hax₁K hφax₁
  obtain ⟨hWcard, hW_ea⟩ := W_card_ea hWdef hW_eq_sup hW_comm hord_ax₁ hord_x₃G hdisj
    hJGcube hax₁JG hx₃JG'
  obtain ⟨hWsub, hφW⟩ := W_subgroup c ha x₁D x₃D hax₁def hx₃Gdef hWdef hW_le_JG hJG_le_K
    (hσdef.symm) hx₁φ hx₃φ
  have ha_notW := W_not_a c ha hWdef hφW (hσdef.symm) hnot_sup₂ hclosure_le_of
  have hW_inf_O := W_inf_O ha3 hW_le_JG hJO_eq ha_notW
  obtain ⟨D1, hD1def, hD0_le_D1, hD0norm⟩ := D1_data c D D0 hD0def
  obtain ⟨w₁, w₂, n₁, n₂, d₁, d₂, hw₁D1, hw₂D1, hw₁φ, hw₂φ, hn₁, hn₂, hn₁norm, hn₂norm,
    hn₁φ, hn₂φ⟩ := lift_data c hDdef hmapD hv₁mem hv₂mem hv₁N hv₂N hD1def hD0_le_D1 hD0norm
      hD0map P
  have hcomm₁ := commutator_x₃ c P x₃D PK n₁ hv₁c₃ hJconj hx₃φ hPKdef hx₃P hx₃PK hinjPK
    hn₁norm hn₁φ
  have hcomm₂ := commutator_x₁ c ha P x₁D PK n₂ hσdef hv₂c₁ hJconj hx₁φ hPKdef hx₁P hx₁PK haPK
    hinjPK hn₂norm hn₂φ
  exact final_stage c h1 hKF2 hp ha ha3 hrank hpp hp5 s hW_le_C hW_inf_O hW_comm hW_ea
    hax₁W hx₃GW hWdef hWcard hax₁def hx₃Gdef (hJG_le_MC hx₁JG) (hJG_le_MC hx₃JG)
    (lift_mem_MC c hDdef hD1def hD0_le_D1 hw₁D1 hn₁)
    (lift_mem_MC c hDdef hD1def hD0_le_D1 hw₂D1 hn₂)
    (by simpa using hJGcube _ hx₁JG) (by simpa using hJGcube _ hx₃JG) hcomm₁ hcomm₂

end Ctx

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThree
