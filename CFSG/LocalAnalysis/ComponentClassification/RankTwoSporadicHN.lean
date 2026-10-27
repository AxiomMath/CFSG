module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNA
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNT4
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHNData
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicYCriterion
public import CFSG.Sporadic.HNOddCore.FusB
public import CFSG.Sporadic.HNSchreier.FullAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.Monster.Code.Weights

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.HN

open Subgroup Equiv CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G] {H : Subgroup G}

theorem mem_centralizer_of_isElemAbelian {E : Subgroup ↥H} (hE : IsElemAbelian 2 E) {b r : ↥H}
    (hb : b ∈ E) (hr : r ∈ E) : b ∈ centralizer {r} := by
  rw [mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hE.1.is_comm.comm ⟨b, hb⟩ ⟨r, hr⟩)

theorem conj_mem_map_conj {E : Subgroup ↥H} {a e r : ↥H} (he : e ∈ E)
    (hr : r * a * r⁻¹ = e) : a ∈ E.map (MulAut.conj r⁻¹).toMonoidHom := by
  refine ⟨e, he, ?_⟩
  show r⁻¹ * e * r⁻¹⁻¹ = a
  rw [← hr]
  group

theorem yWitness_of_sylow_root [Finite G] {X E : Subgroup ↥H} (hX : X.Normal) {r : ↥H}
    (hr : orderOf r = 2) {P : Subgroup ↥(centralizer {r} : Subgroup ↥H)} (hP : IsPGroup 2 P)
    (hidx : ¬ 2 ∣ P.index)
    (hwit : ∀ b ∈ P.map (centralizer {r} : Subgroup ↥H).subtype, b ^ 2 = 1 → b ∉ zpowers r →
      ∃ w ∈ closure {y | ∃ c ∈ centDer X r, y = ⁅b, c⁆}, 4 ∣ orderOf w)
    (hE : IsElemAbelian 2 E) (hE4 : 4 ≤ Nat.card E) (hrE : r ∈ E) : YWitness X E := by
  have hr1 : r ≠ 1 := fun h => by rw [h, orderOf_one] at hr; exact absurd hr (by norm_num)
  obtain ⟨b, hbE, hbz⟩ := exists_mem_not_mem_zpowers hr hE4
  have hbC : b ∈ centralizer {r} := mem_centralizer_of_isElemAbelian hE hbE hrE
  have hb2 : b ^ 2 = 1 := hE.2 b hbE
  have he : (⟨b, hbC⟩ : ↥(centralizer {r} : Subgroup ↥H)) ^ 2 = 1 := Subtype.ext (by
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact hb2)
  obtain ⟨g, hg⟩ := exists_conj_mem_of_index hP hidx he
  have hgt : (g : ↥H) * r = r * g := mem_centralizer_singleton_iff.mp g.2
  have hbP : (g : ↥H) * b * (g : ↥H)⁻¹ ∈ P.map (centralizer {r} : Subgroup ↥H).subtype :=
    ⟨_, hg, by simp⟩
  have hb'2 : ((g : ↥H) * b * (g : ↥H)⁻¹) ^ 2 = 1 := by
    rw [conj_pow, hb2, mul_one, mul_inv_cancel]
  have hb'z : (g : ↥H) * b * (g : ↥H)⁻¹ ∉ zpowers r := by
    intro h
    apply hbz
    have hb : b = (g : ↥H)⁻¹ * ((g : ↥H) * b * (g : ↥H)⁻¹) * g := by group
    rcases eq_one_or_eq_of_mem_zpowers hr h with h' | h'
    · rw [hb, h', mul_one, inv_mul_cancel]
      exact one_mem _
    · rw [hb, h', mul_assoc, ← hgt, ← mul_assoc, inv_mul_cancel, one_mul]
      exact mem_zpowers _
  obtain ⟨w, hw, h4⟩ := hwit _ hbP hb'2 hb'z
  exact yWitness_of_root_conj hX hrE hr1 hbE hgt hw h4

theorem yCensus_of_three_roots [Finite G] {X : Subgroup ↥H} (hX : X.Normal) {c t t' : ↥H}
    (hcov : ∀ y : ↥H, y ^ 2 = 1 → y ≠ 1 → IsConj c y ∨ IsConj t y ∨ IsConj t' y)
    (hcX : c ∉ X) (htX : t ∈ X) (ht'X : t' ∈ X)
    (hC : ∀ E : Subgroup ↥H, IsElemAbelian 2 E → 4 ≤ Nat.card E → c ∈ E → YWitness X E)
    (hT : ∀ E : Subgroup ↥H, IsElemAbelian 2 E → 4 ≤ Nat.card E → E ≤ X → t ∈ E →
      YWitness X E)
    (hT' : ∀ E : Subgroup ↥H, IsElemAbelian 2 E → 4 ≤ Nat.card E → t' ∈ E → YWitness X E) :
    YCensus X (fun _ => False) := by
  intro E hE hE4 _
  have hmap : ∀ r : ↥H, IsElemAbelian 2 (E.map (MulAut.conj r).toMonoidHom) ∧
      4 ≤ Nat.card (E.map (MulAut.conj r).toMonoidHom) := fun r =>
    ⟨isElemAbelian_map hE _, by rw [card_map_of_injective (MulAut.conj r).injective]; exact hE4⟩
  have hconjX : ∀ {a y : ↥H}, IsConj a y → a ∈ X → y ∈ X := fun {a y} h ha => by
    obtain ⟨r, rfl⟩ := isConj_iff.mp h
    exact hX.conj_mem a ha r
  by_cases hout : E ≤ X
  · obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have hbot : E = ⊥ := (eq_bot_iff_forall E).mpr hcon
      rw [hbot, card_bot] at hE4
      omega
    rcases hcov e (hE.2 e heE) he1 with h | h | h
    · exact absurd (hconjX h.symm (hout heE)) hcX
    · obtain ⟨r, hr⟩ := isConj_iff.mp h
      refine yWitness_of_map_conj hX r⁻¹ ?_
      refine hT _ (hmap _).1 (hmap _).2 ?_ (conj_mem_map_conj heE hr)
      rintro _ ⟨x, hx, rfl⟩
      exact hX.conj_mem x (hout hx) r⁻¹
    · obtain ⟨r, hr⟩ := isConj_iff.mp h
      refine yWitness_of_map_conj hX r⁻¹ ?_
      exact hT' _ (hmap _).1 (hmap _).2 (conj_mem_map_conj heE hr)
  · obtain ⟨e, heE, heX⟩ : ∃ e ∈ E, e ∉ X := by
      by_contra hcon
      push Not at hcon
      exact hout hcon
    have he1 : e ≠ 1 := fun h => heX (h ▸ one_mem _)
    rcases hcov e (hE.2 e heE) he1 with h | h | h
    · obtain ⟨r, hr⟩ := isConj_iff.mp h
      refine yWitness_of_map_conj hX r⁻¹ ?_
      exact hC _ (hmap _).1 (hmap _).2 (conj_mem_map_conj heE hr)
    · exact absurd (hconjX h htX) heX
    · exact absurd (hconjX h ht'X) heX

end Generic

theorem hnAutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .HN) ↥RH (JH.subgroupOf RH) :=
  Cert.autModel_of_conj JH_le_RH hnEquivJ.symm (MulEquiv.ofBijective conjR conjR_bijective)
    fun x p => by
      change ((conjR x p : JH) : GL (Fin hnsData.d) (ZMod 5)) = _
      exact conjR_apply x p

theorem orderOf_t4R :
    orderOf t4R = 2 := by
  rw [← t4C_val, Subgroup.orderOf_coe, orderOf_t4C]

theorem Pc_isPGroup :
    IsPGroup 2 Pc := IsPGroup.of_card (n := 15) (card_Pc.trans (by norm_num))

theorem Pc_index :
    ¬ 2 ∣ Pc.index := fun h => PR_not_dvd (by
  have e : PR.index = Pc.index * C4.index := Subgroup.index_map_subtype Pc
  rw [e]
  exact dvd_mul_of_dvd_left h _)

theorem yWitness_of_mem_t4
    {pool : Array (List ℤ × List ℤ)} {wits : Array T4Wit}
    (hc : hnT4Check pool wits = true) {E : Subgroup ↥RH} (hE : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) (ht : t4R ∈ E) : YWitness (JH.subgroupOf RH) E :=
  yWitness_of_sylow_root normal_X orderOf_t4R Pc_isPGroup Pc_index
    (fun _ hb hb2 hbz => witness_t4 hc hb hb2 hbz) hE hE4 ht

theorem hn_yCensus
    {pool : Array (List ℤ × List ℤ)} {wits : Array T4Wit}
    {prog : List (ℕ × ℕ)} {pregs : List ℕ} {poolA : Array (ℕ × ℕ)} {witsA : Array AWit}
    (hc4 : hnT4Check pool wits = true) (hcA : hnAOCheck prog pregs poolA witsA = true) :
    YCensus (JH.subgroupOf RH) (fun _ => False) :=
  yCensus_of_three_roots normal_X (c := cR) (t := jR aJ) (t' := t4R)
    (fun _ h2 h1 => (involution_cover_R h2 h1).imp_right
      (Or.imp_left ((MonoidHom.map_isConj jR isConj_t2_aJ).symm.trans)))
    (fun h => isOuter_cR (mem_subgroupOf.mp h))
    (mem_subgroupOf.mpr (by rw [jR_val]; exact aJ.2))
    (mem_subgroupOf.mpr (by rw [jR_val]; exact t4J.2))
    (fun _ hE hE4 hc => yWitness_of_mem_cR hE hE4 hc)
    (fun _ hE hE4 hEX ha => yWitness_of_mem_aR hcA hE hE4 hEX ha)
    (fun _ hE hE4 ht => yWitness_of_mem_t4 hc4 hE hE4 ht)

theorem sporadicCaseOdd_HN_of_check
    (hc4 : hnT4Check (decodePoolT4 hnT4PoolStr) (decodeT4 hnT4WitStr) = true)
    (hcA : hnAOCheck (decodePairsO hnAProgStr) hnAPregs (decodePairsO hnAPoolStr).toArray
      (decodeAO hnAWitStr) = true)
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : SporadicCaseOdd .HN :=
  sporadicCaseOdd_of_yCensus h32 h33 hnAutModel (hn_yCensus hc4 hcA)

end CFSG.ComponentClassification.RankTwoSporadic.HN
