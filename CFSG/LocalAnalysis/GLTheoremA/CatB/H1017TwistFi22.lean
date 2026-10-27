module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Twist
public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.ExcFi22
public import Certificates.Certificate431009

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22Twist

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.H1017
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.RankThree.Native CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22TwistNative

theorem factorization_three_mul {a c : ℕ} (hc : ¬ 3 ∣ c) : (3 ^ a * c).factorization 3 = a := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero 3)
  rw [Nat.factorization_mul (by positivity) hc0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hc, add_zero]

theorem card_centralizer_mk {G : Type*} [Group G] {H : Subgroup G} {t : G} (ht : t ∈ H) :
    Nat.card (Subgroup.centralizer ({⟨t, ht⟩} : Set H)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) := by
  rw [← Subgroup.card_map_of_injective H.subtype_injective]
  have e : (Subgroup.centralizer ({⟨t, ht⟩} : Set H)).map H.subtype =
      H ⊓ Subgroup.centralizer ({t} : Set G) := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq, Subgroup.coe_subtype]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, by simpa using congrArg Subtype.val hx⟩
    · rintro ⟨hg, hc⟩
      exact ⟨⟨g, hg⟩, Subtype.ext (by simpa using hc), rfl⟩
  rw [e]

@[expose] noncomputable def Qk (k : ℕ) : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure (permsA 3510 (qGens k))

@[expose] noncomputable def Dj (j : ℕ) : Subgroup (Equiv.Perm (Fin 3510)) :=
  Subgroup.closure {permOfArr 3510 (repX j), permOfArr 3510 (repY j), permOfArr 3510 (repZ j)}

@[expose] noncomputable def DK (j : ℕ) : Subgroup fi22P := (Dj j).subgroupOf fi22P

section Cert


theorem Qk_le {k : ℕ} (hk : k < 3) : Qk k ≤ fi22P := Certificates.certificate431009.qk_le k hk

theorem card_Qk {k : ℕ} (hk : k < 3) : Nat.card (Qk k) = [27, 81, 729][k]! :=
  Certificates.certificate431009.qk_card k hk

theorem Qk_le_centralizer {k : ℕ} (hk : k < 3) :
    Qk k ≤ Subgroup.centralizer ({fi22ExtRep k} : Set (Equiv.Perm (Fin 3510))) :=
  Certificates.certificate431009.qk_le_cent k hk

theorem card_DK {j : ℕ} (hj : j < 5) : Nat.card (DK j) = 27 := by
  have hle : Dj j ≤ fi22P := Certificates.certificate431009.dj_le j hj
  rw [DK, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact Certificates.certificate431009.dj_card j hj

theorem closed_DK {j : ℕ} (hj : j < 5) :
    PElemsClosed 3 (Subgroup.centralizer ((DK j : Subgroup fi22P) : Set fi22P)) := by
  have hc : ∀ {c : fi22P}, c ∈ Subgroup.centralizer ((DK j : Subgroup fi22P) : Set fi22P) →
      (c : Equiv.Perm (Fin 3510)) ∈
        fi22P ⊓ Subgroup.centralizer (Dj j : Set (Equiv.Perm (Fin 3510))) := by
    intro c hc
    refine ⟨c.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    have := Subgroup.mem_centralizer_iff.1 hc ⟨y, Certificates.certificate431009.dj_le j hj hy⟩
      (Subgroup.mem_subgroupOf.2 hy)
    exact congrArg Subtype.val this
  rintro a ha b hb ⟨m, hm⟩ ⟨m', hm'⟩
  obtain ⟨n, hn⟩ := Certificates.certificate431009.cent_closed j hj _ (hc ha) _ (hc hb)
    ⟨m, by simpa using congrArg Subtype.val hm⟩ ⟨m', by simpa using congrArg Subtype.val hm'⟩
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

end Cert

section Assembly


theorem exists_conj_ext (t : fi22P) (ht : orderOf t = 2) :
    ∃ k < 3, ∃ g : fi22P, ((g * t * g⁻¹ : fi22P) : Equiv.Perm (Fin 3510)) = fi22ExtRep k := by
  have ht' : orderOf (t : Equiv.Perm (Fin 3510)) = 2 := by rw [Subgroup.orderOf_coe, ht]
  obtain ⟨g, hg, hc⟩ := fi22P_involution_conj t t.2 ht'
  obtain ⟨-, -, -, -, hx, hz, -⟩ := CTUC_Fi22_all_extension_involutions_covered
  have e : ∀ m < 3, ∀ w, g * t * g⁻¹ = w → w = fi22ExtRep m →
      ∃ k < 3, ∃ g : fi22P, ((g * t * g⁻¹ : fi22P) : Equiv.Perm (Fin 3510)) = fi22ExtRep k :=
    fun m hm w hw hwm => ⟨m, hm, ⟨g, hg⟩, by simpa [hwm] using hw⟩
  rcases hc with h | h | h
  · exact e 0 (by norm_num) _ h (hx 0 (by norm_num)).symm
  · exact e 1 (by norm_num) _ h (hx 1 (by norm_num)).symm
  · exact e 2 (by norm_num) _ h hz.symm

theorem card_Qk_eq {k : ℕ} (hk : k < 3) :
    Nat.card ((Qk k).subgroupOf fi22P) = 3 ^ (Nat.card (Subgroup.centralizer
      ({⟨fi22ExtRep k, CTUC_Fi22_all_extension_involutions_covered.1 k hk⟩} : Set fi22P))).factorization 3 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Qk_le hk)).toEquiv, card_Qk hk,
    card_centralizer_mk, CFSG.EvenSporadicStandard.Co3Std.CentT.card_fi22P_inf_centralizer_ext
      (by omega)]
  interval_cases k
  · rw [show ([1769472, 53084160, 18393661440, 3317760, 1045094400, 2903040] : List ℕ).getD 0 0 =
      3 ^ 3 * 65536 by norm_num, factorization_three_mul (by norm_num)]
    rfl
  · rw [show ([1769472, 53084160, 18393661440, 3317760, 1045094400, 2903040] : List ℕ).getD 1 0 =
      3 ^ 4 * 655360 by norm_num, factorization_three_mul (by norm_num)]
    rfl
  · rw [show ([1769472, 53084160, 18393661440, 3317760, 1045094400, 2903040] : List ℕ).getD 2 0 =
      3 ^ 6 * 25231360 by norm_num, factorization_three_mul (by norm_num)]
    rfl

theorem closed_of_inv (D : Subgroup fi22P) (hD : IsElemAbelian 3 D) (hc : Nat.card D = 27)
    (t : fi22P) (ht : orderOf t = 2) (hDt : D ≤ Subgroup.centralizer ({t} : Set fi22P)) :
    PElemsClosed 3 (Subgroup.centralizer (D : Set fi22P)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk, g, hg⟩ := exists_conj_ext t ht
  have htk : fi22ExtRep k ∈ fi22P := CTUC_Fi22_all_extension_involutions_covered.1 k hk
  set tk : fi22P := ⟨fi22ExtRep k, htk⟩
  have hgt : g * t * g⁻¹ = tk := Subtype.ext hg
  set D₁ := D.map (MulAut.conj g).toMonoidHom with hD₁
  have hD₁t : D₁ ≤ Subgroup.centralizer ({tk} : Set fi22P) := by
    rw [← hgt]
    exact map_conj_le_centralizer_singleton g hDt
  have hD₁c : Nat.card D₁ = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hc]
  have hD₁e : IsElemAbelian 3 D₁ := isElemAbelian_map' _ hD
  have hQC : (Qk k).subgroupOf fi22P ≤ Subgroup.centralizer ({tk} : Set fi22P) := by
    intro q hq
    have hq' := Qk_le_centralizer hk (Subgroup.mem_subgroupOf.1 hq)
    rw [Subgroup.mem_centralizer_iff] at hq' ⊢
    rintro s rfl
    exact Subtype.ext (hq' _ rfl)
  have hD₁p : IsPGroup 3 D₁ := fun d => ⟨1, Subtype.ext (by simpa using hD₁e.2 d d.2)⟩
  obtain ⟨h, -, hh⟩ := exists_conj_into_of_card hQC (card_Qk_eq hk) hD₁t hD₁p
  set D₂ := D₁.map (MulAut.conj h).toMonoidHom with hD₂
  have hD₂c : Nat.card D₂ = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hD₁c]
  have hD₂e : IsElemAbelian 3 D₂ := isElemAbelian_map' _ hD₁e
  have hAQ : D₂.map fi22P.subtype ≤ Qk k := by
    rintro _ ⟨w, hw, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hh hw)
  have hAc : Nat.card (D₂.map fi22P.subtype) = 27 := by
    rw [Subgroup.card_map_of_injective fi22P.subtype_injective, hD₂c]
  obtain ⟨g', hg', j, hj, hx⟩ := Certificates.certificate431009.e27_conj k hk _ hAQ hAc
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (comm_of_isElemAbelian' hD₂e ha hb))
    (by
      rintro _ ⟨a, ha, rfl⟩
      simpa using congrArg Subtype.val (hD₂e.2 _ ha))
  set gK : fi22P := ⟨g', hg'⟩
  have hle : D₂.map (MulAut.conj gK).toMonoidHom ≤ DK j := by
    rintro _ ⟨w, hw, rfl⟩
    rw [DK, Subgroup.mem_subgroupOf]
    simpa [gK, Dj] using hx _ ⟨w, hw, rfl⟩
  have heq : D₂.map (MulAut.conj gK).toMonoidHom = DK j :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [card_DK hj, Subgroup.card_map_of_injective (MulAut.conj gK).injective, hD₂c])
  have hcl := closed_DK hj
  rw [← heq] at hcl
  exact pElemsClosed_of_map_conj g (pElemsClosed_of_map_conj h (pElemsClosed_of_map_conj gK hcl))

end Assembly

end CFSG.LocalAnalysis.GLTheoremA.H1017.Fi22Twist

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Monster.B.Fischer

theorem i1017FiTwoTwoTwist_holds :
    I1017FiTwoTwoTwist := by
  obtain ⟨b⟩ : Nonempty (CFSG.Blueprint.NativeSporadic.Fi22 ≃*
      (TauCeti.CFSGIndex.sporadic .Fi22).Group) := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  have hbr : Nonempty (↥fi22P ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group) :=
    ⟨fi22PermEquiv.symm.trans b⟩
  refine noTwistRank_of_model (s := .Fi22) (r := 4) (X := ↥fi22P) hbr ?_
  intro E hE hcard T hT hET
  refine noTwist_of_invClosed (r := 4) (by norm_num) ?_ E hE hcard T hT hET
  rintro E' D hE' - hDE hDc ⟨t, ht, hDt⟩
  exact Fi22Twist.closed_of_inv D (CFSG.Open.IsElemAbelian.mono hE' hDE) (by simpa using hDc) t ht
    hDt

end CFSG.LocalAnalysis.GLTheoremA.H1017
