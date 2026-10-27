module

public import CFSG.LocalAnalysis.EvenBN.G2.ProductCommute
public import CFSG.LocalAnalysis.EvenBN.G2.EndgameBase
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (diagonalHom)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase
open scoped commutatorElement Pointwise MatrixGroups

namespace ProductG0Aux

section Generic

variable {G : Type*} [Group G]

theorem map_conj_inv_map_conj_inv {g : G} (hg : g * g = 1) (A : Subgroup G) :
    (Aᵍ[g])ᵍ[g] = A := by
  have hcomp : (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)).comp
      (MulEquiv.toMonoidHom (MulAut.conj g⁻¹)) = MonoidHom.id G := by
    ext x
    have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
    have h1 : g * (g * x * g) * g = (g * g) * x * (g * g) := by group
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgi, inv_inv,
      MonoidHom.id_apply]
    rw [h1, hg]
    simp
  rw [Subgroup.map_map, hcomp, Subgroup.map_id]

theorem map_subgroupOf_diagonalHom {A B : Subgroup G} {t : G}
    (hA : ⁅A, Aᵍ[t]⁆ = ⊥) (hB : ⁅B, Bᵍ[t]⁆ = ⊥) (hAB : A ≤ B) :
    (A.subgroupOf B).map (diagonalHom B t hB) = (diagonalHom A t hA).range := by
  ext y
  constructor
  · rintro ⟨⟨a, _⟩, ha, rfl⟩
    exact ⟨⟨a, ha⟩, rfl⟩
  · rintro ⟨⟨a, ha⟩, rfl⟩
    exact ⟨⟨a, hAB ha⟩, ha, rfl⟩

theorem range_diagonalHom_le_sup {A : Subgroup G} {t : G} (hA : ⁅A, Aᵍ[t]⁆ = ⊥) :
    (diagonalHom A t hA).range ≤ A ⊔ Aᵍ[t] := by
  rintro _ ⟨a, rfl⟩
  exact mul_mem (mem_sup_left a.2) (mem_sup_right (Common.conj_mem_map_conj_inv t a.2))

theorem isPerfect_of_injective {H K : Type*} [Group H] [Group K] (f : H →* K)
    (hf : Function.Injective f) [Group.IsPerfect f.range] : Group.IsPerfect H := by
  let e : H ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.2 hf, f.rangeRestrict_surjective⟩
  exact Group.IsPerfect.ofSurjective (f := (e.symm : f.range →* H)) e.symm.surjective

theorem map_conj_inv_le {K : Subgroup G} {g : G} (hg : g ∈ K) {A : Subgroup G} (hA : A ≤ K) :
    Aᵍ[g] ≤ K := by
  rintro _ ⟨a, ha, rfl⟩
  change g⁻¹ * a * g⁻¹⁻¹ ∈ K
  exact mul_mem (mul_mem (inv_mem hg) (hA ha)) (by rw [inv_inv]; exact hg)

theorem map_conj_inv_le_of_centralizer {L : Subgroup G} {t : G}
    (htL : t ∈ centralizer (L : Set G)) : Lᵍ[t] ≤ L := by
  rintro _ ⟨l, hl, rfl⟩
  have h1 : l * t = t * l := mem_centralizer_iff.1 htL l hl
  change t⁻¹ * l * t⁻¹⁻¹ ∈ L
  rw [inv_inv, mul_assoc, h1, inv_mul_cancel_left]
  exact hl

end Generic

section Hall

variable {G : Type*} [Group G] [Finite G]

private theorem isHallSubgroup_odd {U J : Subgroup G} (hJU : J ≤ U) (hodd : Odd (Nat.card J))
    (hidx : ∃ k : ℕ, (J.subgroupOf U).index ∣ 2 ^ k) :
    CFSG.IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} (J.subgroupOf U) := by
  refine CFSG.isHallSubgroup_of _ _ (fun p hp => ?_) (fun p hp hpd => ?_)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJU).toEquiv] at hp
    intro hp2
    rw [hp2] at hp
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hp)
  · obtain ⟨k, hk⟩ := hidx
    exact hp ((Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).1 (p.2.dvd_of_dvd_pow (hpd.trans hk)))

theorem exists_mem_mul_mem_normalizer {S J : Subgroup G} {c : G} (hS : IsPGroup 2 S)
    (hJodd : Odd (Nat.card J)) (hJcomm : ∀ x ∈ J, ∀ y ∈ J, x * y = y * x)
    (hJS : J ≤ normalizer (S : Set G)) (hcJ : ∀ j ∈ J, c * j * c⁻¹ ∈ J ⊔ S) :
    ∃ s ∈ S, s⁻¹ * c ∈ normalizer (J : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U : Subgroup G := J ⊔ S with hU
  have hJU : J ≤ U := le_sup_left
  have hSU : S ≤ U := le_sup_right
  set J' : Subgroup G := J.map (MulAut.conj c).toMonoidHom with hJ'
  have hJ'U : J' ≤ U := by
    rintro _ ⟨j, hj, rfl⟩
    exact hcJ j hj
  have hcardJ' : Nat.card J' = Nat.card J :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hdec : ∀ u ∈ U, ∃ s ∈ S, ∃ j ∈ J, u = s * j := by
    intro u hu
    rw [hU, sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hJS,
      Set.mem_mul] at hu
    obtain ⟨s, hs, j, hj, rfl⟩ := hu
    exact ⟨s, hs, j, hj, rfl⟩
  have hsolv : Group.IsSolvable U := by
    set S' : Subgroup U := S.subgroupOf U with hS'
    have hSn : S'.Normal := by
      rw [hS', Subgroup.normal_subgroupOf_iff_le_normalizer hSU]
      exact sup_le hJS le_normalizer
    have hS'nil : Group.IsNilpotent S' :=
      (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hSU)).2 hS.isNilpotent
    have hrep : ∀ x : U, ∃ j : J, (QuotientGroup.mk x : U ⧸ S') =
        QuotientGroup.mk (⟨j, hJU j.2⟩ : U) := by
      intro x
      obtain ⟨s, hs, j, hj, hx⟩ := hdec x x.2
      refine ⟨⟨j, hj⟩, ?_⟩
      rw [QuotientGroup.eq, hS', Subgroup.mem_subgroupOf]
      change ((x : G))⁻¹ * j ∈ S
      rw [hx, mul_inv_rev, mul_assoc]
      have := (mem_normalizer_iff.1 (inv_mem (hJS hj)) s⁻¹).1 (inv_mem hs)
      rwa [show j⁻¹ * s⁻¹ * j⁻¹⁻¹ = j⁻¹ * (s⁻¹ * j) by group] at this
    have hquot : Group.IsSolvable (U ⧸ S') := Group.isSolvable_of_comm fun x y => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨j, hx⟩ := hrep x
      obtain ⟨j', hy⟩ := hrep y
      rw [hx, hy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      exact congrArg _ (Subtype.ext (hJcomm j j.2 j' j'.2))
    exact Group.isSolvable_of_ker_le_range S'.subtype (QuotientGroup.mk' S')
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  have hidx : ∃ k : ℕ, (J.subgroupOf U).index ∣ 2 ^ k ∧ (J'.subgroupOf U).index ∣ 2 ^ k := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS
    have hcard := Common.card_sup_mul_card_inf_eq hJS
    have hpos : 0 < Nat.card J := Nat.card_pos
    have e1 : (J.subgroupOf U).index * Nat.card J = Nat.card U := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJU).toEquiv]
      exact Subgroup.index_mul_card _
    have e2 : (J'.subgroupOf U).index * Nat.card J = Nat.card U := by
      rw [← hcardJ', ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ'U).toEquiv]
      exact Subgroup.index_mul_card _
    have hSU' : Nat.card U = Nat.card (S ⊔ J : Subgroup G) := by rw [hU, sup_comm]
    have e3 : (J.subgroupOf U).index * Nat.card ↥(S ⊓ J) = Nat.card S := by
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      calc (J.subgroupOf U).index * Nat.card ↥(S ⊓ J) * Nat.card J
          = ((J.subgroupOf U).index * Nat.card J) * Nat.card ↥(S ⊓ J) := by ring
        _ = Nat.card (S ⊔ J : Subgroup G) * Nat.card ↥(S ⊓ J) := by rw [e1, hSU']
        _ = Nat.card S * Nat.card J := hcard
    have e4 : (J'.subgroupOf U).index = (J.subgroupOf U).index :=
      Nat.eq_of_mul_eq_mul_right hpos (e2.trans e1.symm)
    exact ⟨k, Dvd.intro _ (e3.trans hk), e4 ▸ Dvd.intro _ (e3.trans hk)⟩
  obtain ⟨k, hk₁, hk₂⟩ := hidx
  have hH₁ := isHallSubgroup_odd hJU hJodd ⟨k, hk₁⟩
  have hH₂ := isHallSubgroup_odd hJ'U (hcardJ' ▸ hJodd) ⟨k, hk₂⟩
  obtain ⟨g, hg⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hsolv hH₁ hH₂
  have hJ'eq : J' = J.map (MulAut.conj (g : G)).toMonoidHom := by
    have h1 := congrArg (Subgroup.map U.subtype) hg
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hJ'U,
      CFSG.map_subgroupOf_map_conj_eq hJU g] at h1
    exact h1
  obtain ⟨s, hs, j, hj, hgsj⟩ := hdec g g.2
  refine ⟨s, hs, mem_normalizer_fintype fun x hx => ?_⟩
  have hxJ' : c * x * c⁻¹ ∈ J' := ⟨x, hx, rfl⟩
  rw [hJ'eq] at hxJ'
  obtain ⟨y, hy, hyx⟩ := hxJ'
  have hyx' : (s * j) * y * (s * j)⁻¹ = c * x * c⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hgsj] at hyx
    exact hyx
  have : s⁻¹ * c * x * (s⁻¹ * c)⁻¹ = j * y * j⁻¹ := by
    calc s⁻¹ * c * x * (s⁻¹ * c)⁻¹ = s⁻¹ * (c * x * c⁻¹) * s := by group
      _ = s⁻¹ * ((s * j) * y * (s * j)⁻¹) * s := by rw [hyx']
      _ = j * y * j⁻¹ := by group
  rw [this]
  exact mul_mem (mul_mem hj hy) (inv_mem hj)

end Hall

end ProductG0Aux

section Local

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

variable
  {K : Type} [Field K] [Finite K]
  [CharP K 2]

namespace DiagonalPair

variable {d : G2Data L K} (X : DiagonalPair d t)

theorem commutator_sup_eq_bot (hK : 4 ≤ Nat.card K) (htL : t ∈ centralizer (L : Set G))
    (ht : t * t = 1) : ⁅X.A₁ ⊔ X.A₂, (X.A₁ ⊔ X.A₂)ᵍ[t]⁆ = ⊥ := by
  obtain ⟨h₁₂, h₂₁⟩ := X.commutator_cross_eq_bot hK ht htL
  have hA₁A₁ : X.A₁ ≤ centralizer (X.A₁ᵍ[t] : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 X.comm₁
  have hA₂A₂ : X.A₂ ≤ centralizer (X.A₂ᵍ[t] : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 X.comm₂
  have hA₁A₂ : X.A₁ ≤ centralizer (X.A₂ᵍ[t] : Set G) :=
    commutator_eq_bot_iff_le_centralizer.1 h₁₂
  have hA₂A₁ : X.A₂ ≤ centralizer (X.A₁ᵍ[t] : Set G) := by
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact h₂₁
  rw [Subgroup.map_sup, commutator_eq_bot_iff_le_centralizer]
  refine sup_le ?_ ?_
  · rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.1 hA₁A₁) (le_centralizer_iff.1 hA₁A₂)
  · rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.1 hA₂A₁) (le_centralizer_iff.1 hA₂A₂)

theorem range_and_isPerfect (h : Setup G L f t) (hK : 4 ≤ Nat.card K) :
    (diagonalHom (X.A₁ ⊔ X.A₂) t (X.commutator_sup_eq_bot hK h.htL h.t_mul_t)).range = L ∧
      Group.IsPerfect ↥(X.A₁ ⊔ X.A₂) := by
  obtain ⟨-, -, -, -, h5, h6₁, h6₂⟩ := d.weyl_facts hK
  refine ⟨?_, ?_⟩
  · set hcomm := X.commutator_sup_eq_bot hK h.htL h.t_mul_t
    have hmap₁ := ProductG0Aux.map_subgroupOf_diagonalHom X.comm₁ hcomm
      (le_sup_left : X.A₁ ≤ X.A₁ ⊔ X.A₂)
    have hmap₂ := ProductG0Aux.map_subgroupOf_diagonalHom X.comm₂ hcomm
      (le_sup_right : X.A₂ ≤ X.A₁ ⊔ X.A₂)
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self (X.A₁ ⊔ X.A₂),
      Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.map_sup, hmap₁, hmap₂,
      X.range₁, X.range₂, h5]
  · haveI : Group.IsPerfect ↥X.A₁ := by
      haveI : Group.IsPerfect (diagonalHom X.A₁ t X.comm₁).range := by
        rw [Subgroup.isPerfect_iff, X.range₁]
        exact h6₁
      exact ProductG0Aux.isPerfect_of_injective _ X.injective₁
    haveI : Group.IsPerfect ↥X.A₂ := by
      haveI : Group.IsPerfect (diagonalHom X.A₂ t X.comm₂).range := by
        rw [Subgroup.isPerfect_iff, X.range₂]
        exact h6₂
      exact ProductG0Aux.isPerfect_of_injective _ X.injective₂
    exact Common.isPerfect_sup_of_isPerfect

end DiagonalPair

namespace Setup

theorem ncs_le_normalizer_yamadaP (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (hQ : h.QFacts d) :
    centralizer ({t} : Set G) ⊓ normalizer (d.S : Set G) ≤ normalizer (yamadaP d t : Set G) := by
  intro c hc
  have hD := hQ.doubling
  have hcR₈ : c ∈ normalizer (yamadaR₈ d t : Set G) :=
    le_normalizer_yamadaR₈ d t
      (h.q49_centralizer_inf_normalizer_S_le_normalizer_yamadaR₅ d hK hD hc)
  have hcL : c ∈ normalizer (L : Set G) := h.centralizer_le_normalizer (Subgroup.mem_inf.1 hc).1
  have hcS : c ∈ normalizer (d.S : Set G) := (Subgroup.mem_inf.1 hc).2
  have hJS : d.J ≤ normalizer (d.S : Set G) :=
    (h.J_le_centralizer_inf_normalizer_S d).trans inf_le_right
  have hJcomm : ∀ x ∈ d.J, ∀ y ∈ d.J, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := d.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := d.mem_image.1 hy
    rw [← map_mul, ← map_mul]
    exact congrArg d.emb (Subtype.ext (Model.J_comm ha hb))
  have hcJ : ∀ j ∈ d.J, c * j * c⁻¹ ∈ d.J ⊔ d.S := by
    intro j hj
    rw [← d.yamada_3_13_1_G.2.2]
    exact Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 hcL j).1 (d.image_le _ hj),
      mul_mem (mul_mem hcS (hJS hj)) (inv_mem hcS)⟩
  obtain ⟨s, hs, hn⟩ := ProductG0Aux.exists_mem_mul_mem_normalizer d.isSylowOf_S.isPGroup
    (odd_card_J d) hJcomm hJS hcJ
  have hsR₈ : s ∈ yamadaR₈ d t := h.S_le_yamadaR₈ hW d hK hQ hs
  have hnP : s⁻¹ * c ∈ normalizer (yamadaP d t : Set G) :=
    mem_normalizer_commutator (mul_mem (inv_mem (le_normalizer hsR₈)) hcR₈) hn
  have := mul_mem (h.S_le_normalizer_yamadaP hW d hK hQ hs) hnP
  rwa [mul_inv_cancel_left] at this

end Setup

namespace DiagonalPair

variable {d : G2Data L K} (X : DiagonalPair d t)

theorem sup_conj_eq_yamadaP_sup_L (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (hK₁ : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (hP : yamadaP d t = X.P₀ ⊔ X.P₀ᵍ[t]) :
    (X.A₁ ⊔ X.A₂) ⊔ (X.A₁ ⊔ X.A₂)ᵍ[t] = yamadaP d t ⊔ L := by
  have hK : 4 ≤ Nat.card K := hQ.four_le
  have htt := h.t_mul_t
  have hcomm := X.commutator_sup_eq_bot hK h.htL htt
  obtain ⟨hL, -⟩ := X.range_and_isPerfect h hK
  have hPt : t ∈ normalizer (yamadaP d t : Set G) := (h.yamada_5_51 hW d hK₁ hQ).1.2.1
  have hPtt : (yamadaP d t)ᵍ[t] ≤ yamadaP d t := by
    rw [hP, Subgroup.map_sup, ProductG0Aux.map_conj_inv_map_conj_inv htt, sup_comm]
  apply le_antisymm
  · set K' : Subgroup G := yamadaP d t ⊔ L with hK'
    have hPK : yamadaP d t ≤ K' := le_sup_left
    have hLK : L ≤ K' := le_sup_right
    have hKt : K'ᵍ[t] ≤ K' := by
      rw [hK', Subgroup.map_sup]
      exact sup_le_sup hPtt (ProductG0Aux.map_conj_inv_le_of_centralizer h.htL)
    have hP₀ : X.P₀ ≤ K' := by
      rw [hP] at hPK
      exact le_sup_left.trans hPK
    obtain ⟨hA₁, hA₂⟩ := X.eq_sup_conj hK htt h.htL
    have hwa : d.wa ∈ L := d.emb_mem _
    have hwb : d.wb ∈ L := d.emb_mem _
    have hA₁K : X.A₁ ≤ K' := by
      rw [hA₁]
      exact sup_le hP₀ (ProductG0Aux.map_conj_inv_le (hLK hwa) hP₀)
    have hA₂K : X.A₂ ≤ K' := by
      rw [hA₂]
      exact sup_le hP₀ (ProductG0Aux.map_conj_inv_le (hLK hwb) hP₀)
    refine sup_le (sup_le hA₁K hA₂K) ?_
    rw [Subgroup.map_sup]
    exact sup_le ((Subgroup.map_mono hA₁K).trans hKt) ((Subgroup.map_mono hA₂K).trans hKt)
  · refine sup_le ?_ ?_
    · rw [hP]
      exact sup_le (X.le₁.trans ((le_sup_left : X.A₁ ≤ X.A₁ ⊔ X.A₂).trans le_sup_left))
        (((Subgroup.map_mono X.le₁).trans (Subgroup.map_mono
          (le_sup_left : X.A₁ ≤ X.A₁ ⊔ X.A₂))).trans le_sup_right)
    · exact hL.symm.le.trans ((ProductG0Aux.range_diagonalHom_le_sup hcomm))

theorem normalizer_yamadaR_le (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (hK₁ : Nat.card K = 2 ^ f) (hQ : h.QFacts d)
    (hP : yamadaP d t = X.P₀ ⊔ X.P₀ᵍ[t]) :
    normalizer ((yamadaR d t : Subgroup G) : Set G) ≤
      normalizer (((X.A₁ ⊔ X.A₂) ⊔ (X.A₁ ⊔ X.A₂)ᵍ[t] : Subgroup G) : Set G) := by
  rw [X.sup_conj_eq_yamadaP_sup_L hW h hK₁ hQ hP, (h.yamada_5_3_3 d hK₁).1]
  have hPt : t ∈ normalizer (yamadaP d t : Set G) := (h.yamada_5_51 hW d hK₁ hQ).1.2.1
  have hLt : t ∈ normalizer (L : Set G) := Subgroup.centralizer_le_normalizer (L : Set G) h.htL
  have hPLt : t ∈ normalizer ((yamadaP d t ⊔ L : Subgroup G) : Set G) :=
    Common.mem_normalizer_sup hPt hLt
  have hD := hQ.doubling
  have hC₁C₇ : yamadaC₁ d t ≤ yamadaC₇ d t := by
    rw [← (h.yamada_5_19 d hK₁ hD).1.2.2]
    exact inf_le_left
  have hC₇ : yamadaC₇ d t ≤ yamadaP d t ⊔ zpowers t := by
    rw [← (h.yamada_5_51 hW d hK₁ hQ).2.2.1]
    exact sup_le_sup_right (yamadaD₇_le_yamadaP d t) _
  refine sup_le ?_ ?_
  · intro c hc
    have hc' := hC₇ (hC₁C₇ hc)
    exact (sup_le (le_sup_left.trans le_normalizer)
      ((zpowers_le).2 hPLt)) hc'
  · intro c hc
    exact Common.mem_normalizer_sup (h.ncs_le_normalizer_yamadaP hW d hK₁ hQ hc)
      (h.centralizer_le_normalizer hc.1)

end DiagonalPair

end Local

end CFSG.LocalAnalysis.EvenBN.G2
