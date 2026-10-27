module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitC3A
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitConn

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup

section ElemTwo

variable {H K : Type*} [Group H] [Group K]

theorem isElemTwo_map (f : H →* K) {A : Subgroup H} (hA : GrSLit.IsElemTwo A) :
    GrSLit.IsElemTwo (A.map f) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hA.1 a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hA.2 a ha, map_one]

theorem isElemTwo_comap_of_injective {f : H →* K} (hf : Function.Injective f) {A : Subgroup K}
    (hA : GrSLit.IsElemTwo A) : GrSLit.IsElemTwo (A.comap f) := by
  refine ⟨fun a ha b hb => hf ?_, fun a ha => hf ?_⟩
  · rw [map_mul, map_mul]
    exact hA.1 _ ha _ hb
  · rw [map_mul, map_one]
    exact hA.2 _ ha

end ElemTwo

variable {G : Type} [Group G] [Finite G] {Q : Subgroup G} {x : G} {P : Type*} [Group P]
  (e : ↥Q ⧸ center ↥Q ≃* P)

theorem b_alternative (hLZ : center ↥(Lay Q x) = ⊥) {κ : ↥Q}
    (hκx : (κ : G) ∈ centralizer ({x} : Set G)) (hκ2 : κ * κ = 1)
    (hκJ : piQ e κ ∉ Jp e x) (hBZ : center ↥(Jp e x ⊔ zpowers (piQ e κ)) = ⊥)
    (hE8 : ∃ A : Subgroup P, A ≤ Jp e x ⊔ zpowers (piQ e κ) ∧ GrSLit.IsElemTwo A ∧
      Nat.card A = 8) :
    ∃ B : Subgroup G, B ≤ Q ⊓ centralizer ({x} : Set G) ∧ center ↥B = ⊥ ∧
      ∃ A : Subgroup G, A ≤ B ∧ GrSLit.IsElemTwo A ∧ Nat.card A = 8 := by
  have : Finite P := Finite.of_surjective _ (piQ_surjective e)
  set BQ : Subgroup ↥Q := LQ Q x ⊔ zpowers κ with hBQ
  set BP : Subgroup P := Jp e x ⊔ zpowers (piQ e κ) with hBP
  have hmap : BQ.map (piQ e) = BP := by
    rw [hBQ, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hκN : κ ∈ normalizer ((LQ Q x : Subgroup ↥Q) : Set ↥Q) := by
    rw [mem_normalizer_iff]
    intro l
    exact mem_normalizer_iff.mp (le_normalizer_Lay (Q := Q) (x := x) ⟨κ.2, hκx⟩) (l : G)
  have hcardBQ : Nat.card BQ ≤ 2 * Nat.card (LQ Q x) := by
    rw [hBQ, sup_comm]
    exact GrSLit.card_zpowers_sup_le hκ2 hκN
  have hcardL : Nat.card (LQ Q x) = Nat.card (Jp e x) :=
    Nat.card_congr ((subgroupOfEquivOfLe (Lay_le.trans inf_le_left)).trans
      (equivJp e hLZ)).toEquiv
  have hcardBP : 2 * Nat.card (Jp e x) ≤ Nat.card BP := by
    have hlt : Jp e x < BP := lt_of_le_of_ne le_sup_left fun h =>
      hκJ (h ▸ mem_sup_right (mem_zpowers _))
    obtain ⟨n, hn⟩ := Subgroup.card_dvd_of_le hlt.le
    have hne : Nat.card (Jp e x) ≠ Nat.card BP := fun h =>
      hlt.ne (Subgroup.eq_of_le_of_card_ge hlt.le h.symm.le)
    have hpos : 0 < Nat.card (Jp e x) := Nat.card_pos
    have hBPpos : 0 < Nat.card BP := Nat.card_pos
    rw [hn] at hne hBPpos ⊢
    rcases n with _ | _ | n
    · simp at hBPpos
    · simp at hne
    · nlinarith
  set g := (piQ e).subgroupMap BQ with hg
  have hbij : Function.Bijective g := by
    apply (MonoidHom.subgroupMap_surjective (piQ e) BQ).bijective_of_nat_card_le
    rw [hmap]
    omega
  let eQ : ↥BQ ≃* ↥BP :=
    (MulEquiv.ofBijective g hbij).trans (MulEquiv.subgroupCongr hmap)
  let eB : ↥(BQ.map Q.subtype) ≃* ↥BP :=
    (BQ.equivMapOfInjective Q.subtype Q.subtype_injective).symm.trans eQ
  refine ⟨BQ.map Q.subtype, ?_, Sporadic.HeldB.center_eq_bot_of_mulEquiv eB hBZ, ?_⟩
  · rintro _ ⟨q, hq, rfl⟩
    have hle : BQ ≤ CQ Q x := sup_le LQ_le_CQ (zpowers_le.mpr hκx)
    exact ⟨q.2, hle hq⟩
  · obtain ⟨A₀, hA₀, hA₀e, hA₀c⟩ := hE8
    set A₁ : Subgroup ↥BP := A₀.subgroupOf BP with hA₁
    have hA₁e : GrSLit.IsElemTwo A₁ := isElemTwo_comap_of_injective BP.subtype_injective hA₀e
    have hA₁c : Nat.card A₁ = 8 := by
      rw [← hA₀c]
      exact Nat.card_congr (subgroupOfEquivOfLe hA₀).toEquiv
    refine ⟨(A₁.map eB.symm.toMonoidHom).map (BQ.map Q.subtype).subtype, map_subtype_le _,
      isElemTwo_map _ (isElemTwo_map _ hA₁e), ?_⟩
    rw [Subgroup.card_map_of_injective (BQ.map Q.subtype).subtype_injective,
      Subgroup.card_map_of_injective eB.symm.injective, hA₁c]

end CFSG.ComponentClassification.HarrisLit.C3
