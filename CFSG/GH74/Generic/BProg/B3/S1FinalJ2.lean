module

public import CFSG.GH74.Generic.BProg.B3.S1FinalJ1
public import CFSG.GH74.Generic.BProg.B3.S3L3KGroup
public import CFSG.GH74.Generic.BProg.B3.S1FinalLift

public section

namespace CFSG.GH74.Generic.BProg.B3

namespace S1FinalJ2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic
  CFSG.GH74.Generic.BProg CFSG.Blueprint CFSG.GH74.L5U5 Subgroup
open CFSG.GH74.Generic.BProg.B3.S1FinalDefs CFSG.GH74.Generic.BProg.B3.S1FinalJ1
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J J₁ J₂ : Subgroup G}

@[expose] noncomputable def beta0 (H : JSetup x K A a D J J₁ J₂) : J0 a J :=
  Pi0 H.hJa ⟨x * a, H.hJ₂ H.hb⟩

theorem beta0_eq_sigma2 (H : JSetup x K A a D J J₁ J₂) :
    beta0 H = sigma2 H.hJa H.hJ₂ ⟨x * a, H.hb⟩ := rfl

theorem beta0_mul_self (H : JSetup x K A a D J J₁ J₂) : beta0 H * beta0 H = 1 := by
  rw [beta0_eq_sigma2, ← map_mul]
  have : (⟨x * a, H.hb⟩ : ↥J₂) * ⟨x * a, H.hb⟩ = 1 := Subtype.ext H.hb2
  rw [this, map_one]

theorem beta0_ne_one (H : JSetup x K A a D J J₁ J₂) : beta0 H ≠ 1 := by
  intro h1
  have hz : barJ H.hJa ⟨x * a, H.hJ₂ H.hb⟩ ∈ center ↥(PumpCalc.bar a J) :=
    (QuotientGroup.eq_one_iff _).1 h1
  have hxaC : x * a ∈ centralizer ({a} : Set G) := H.hJa (H.hJ₂ H.hb)
  have hcs : x * a ∈ centralizerSection J (pPrimeCoreOf 2 J) :=
    ObsPump.mem_cSec_of_bar_comm H.hc.obs.comp hxaC (fun l hl => by
      have := Subgroup.mem_center_iff.1 hz ⟨l, hl⟩
      exact (congrArg Subtype.val this).symm)
  have hxs : x ∈ centralizerSection J (pPrimeCoreOf 2 J) := by
    have : x = (x * a) * a⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hcs (Subgroup.inv_mem _ H.haS)
  exact H.hxS hxs

theorem orderOf_beta0 (H : JSetup x K A a D J J₁ J₂) : orderOf (beta0 H) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact beta0_mul_self H) (beta0_ne_one H)

theorem perfect_J₂ (H : JSetup x K A a D J J₁ J₂) : Group.IsPerfect ↥J₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Group.IsPerfect ↥(J₂.subgroupOf (K ⊓ centralizer ({a} : Set G))) :=
    ComponentClassification.CatalogueBHeldSmallCore.pComponent_perfect 2 _ H.hS.comp₂.2
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe H.hJ₂Hg).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe H.hJ₂Hg).surjective

theorem range_sigma2_perfect (H : JSetup x K A a D J J₁ J₂) :
    ⁅(sigma2 H.hJa H.hJ₂).range, (sigma2 H.hJa H.hJ₂).range⁆ = (sigma2 H.hJa H.hJ₂).range := by
  have := perfect_J₂ H
  have h1 : Group.IsPerfect ↥(sigma2 H.hJa H.hJ₂).range :=
    Group.IsPerfect.ofSurjective (sigma2 H.hJa H.hJ₂).rangeRestrict_surjective
  exact Subgroup.isPerfect_iff.mp h1

theorem range_sigma2_le_centralizer (H : JSetup x K A a D J J₁ J₂) :
    (sigma2 H.hJa H.hJ₂).range ≤ centralizer ({beta0 H} : Set (J0 a J)) := by
  rintro _ ⟨k, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, beta0_eq_sigma2, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  show (k : G) * (x * a) = (x * a) * (k : G)
  rw [← mul_assoc, H.hJ₂comm_x k k.2, mul_assoc, H.hJ₂comm_a k k.2, ← mul_assoc]

abbrev Wsub (x a : G) (J : Subgroup G) : Subgroup G :=
  centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G) ⊓ J

@[expose] noncomputable def PiW (H : JSetup x K A a D J J₁ J₂) : ↥(Wsub x a J) →* J0 a J :=
  (Pi0 H.hJa).comp (Subgroup.inclusion (inf_le_right : Wsub x a J ≤ J))

theorem J₂_le_W (H : JSetup x K A a D J J₁ J₂) : J₂ ≤ Wsub x a J := fun _ hk =>
  ⟨⟨(H.hKC (H.hJ₂Hg hk).1), (H.hJ₂Hg hk).2⟩, H.hJ₂ hk⟩

theorem range_PiW (H : JSetup x K A a D J J₁ J₂)
    (hodd : Odd (Nat.card (center ↥(PumpCalc.bar a J)))) :
    (PiW H).range = centralizer ({beta0 H} : Set (J0 a J)) := by
  classical
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    show Pi0 H.hJa (Subgroup.inclusion (inf_le_right : Wsub x a J ≤ J) w) * beta0 H =
      beta0 H * Pi0 H.hJa (Subgroup.inclusion (inf_le_right : Wsub x a J ≤ J) w)
    rw [beta0, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    show (w : G) * (x * a) = (x * a) * (w : G)
    have hwx : (w : G) * x = x * (w : G) := Subgroup.mem_centralizer_singleton_iff.1 w.2.1.1
    have hwa : (w : G) * a = a * (w : G) := Subgroup.mem_centralizer_singleton_iff.1 w.2.1.2
    rw [← mul_assoc, hwx, mul_assoc, hwa, ← mul_assoc]
  · intro y hy
    have hyc : y * beta0 H = beta0 H * y := Subgroup.mem_centralizer_singleton_iff.1 hy
    have hxaJ : x * a ∈ J := H.hJ₂ H.hb
    have hxaN : x * a ∈ NJ a J := S1FinalLift.J_le_NJ H.hJa hxaJ
    have hE : Subgroup.zpowers (x * a) ≤ NJ a J := Subgroup.zpowers_le.2 hxaN
    have hsq : (x * a) ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact H.hb2
    have hE2 : ∀ e ∈ Subgroup.zpowers (x * a), e * e = 1 := by
      intro e he
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      rw [← zpow_add, ← two_mul, zpow_mul, hsq, one_zpow]
    have hy' : ∀ (e : G) (he : e ∈ Subgroup.zpowers (x * a)),
        rho H.hJa ⟨e, hE he⟩ y = y := by
      intro e he
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
      have hkJ : (x * a) ^ k ∈ J := Subgroup.zpow_mem _ hxaJ k
      have h1 := rho_of_mem H.hJa ⟨(x * a) ^ k, hE he⟩ hkJ
      have h2 : Pi0 H.hJa ⟨(x * a) ^ k, hkJ⟩ = (beta0 H) ^ k := by
        have : (⟨(x * a) ^ k, hkJ⟩ : ↥J) = (⟨x * a, hxaJ⟩ : ↥J) ^ k := rfl
        rw [this, map_zpow]
        rfl
      rw [h1, h2, MulAut.conj_apply]
      have hc : Commute y ((beta0 H) ^ k) := (Commute.zpow_right (show Commute y (beta0 H) from hyc) k)
      rw [← hc.eq, mul_inv_cancel_right]
    obtain ⟨g, hg1, hg2⟩ := S1FinalLift.exists_lift_Pi0 H.hJa hodd hE hE2 hy'
    have hgcomm : (x * a) * (g : G) = (g : G) * (x * a) :=
      hg2 (x * a) (Subgroup.mem_zpowers (x * a))
    have hga : (g : G) * a = a * (g : G) := Subgroup.mem_centralizer_singleton_iff.1 (H.hJa g.2)
    have hgx : (g : G) * x = x * (g : G) := by
      have h3 : (g : G) * x * a = x * (g : G) * a := by
        calc (g : G) * x * a = (g : G) * (x * a) := by rw [mul_assoc]
          _ = (x * a) * (g : G) := hgcomm.symm
          _ = x * (a * (g : G)) := by rw [mul_assoc]
          _ = x * ((g : G) * a) := by rw [hga]
          _ = x * (g : G) * a := by rw [mul_assoc]
      exact mul_right_cancel h3
    have hgW : (g : G) ∈ Wsub x a J :=
      ⟨⟨Subgroup.mem_centralizer_singleton_iff.2 hgx, Subgroup.mem_centralizer_singleton_iff.2 hga⟩,
        g.2⟩
    exact ⟨⟨(g : G), hgW⟩, hg1⟩

theorem subnormal_J₂_W (H : JSetup x K A a D J J₁ J₂) :
    (J₂.subgroupOf (Wsub x a J)).IsSubnormal := by
  have h1 : (K.subgroupOf (centralizer ({x} : Set G))).IsSubnormal :=
    B1.isSubnormal_of_isPCompIn H.hc.circ.1.1.1.2.2
  have h2 := B1.isSubnormal_subgroupOf_inf (S := centralizer ({a} : Set G)) h1
  have h3 : (J₂.subgroupOf (K ⊓ centralizer ({a} : Set G))).IsSubnormal :=
    B1.isSubnormal_of_isPCompIn H.hS.comp₂
  have h4 : (J₂.subgroupOf (centralizer ({x} : Set G) ⊓ centralizer ({a} : Set G))).IsSubnormal :=
    B1.isSubnormal_subgroupOf_trans H.hJ₂Hg (inf_le_inf_right _ H.hKC) h3 h2
  have h5 := B1.isSubnormal_subgroupOf_inf (S := J) h4
  rwa [inf_eq_left.2 H.hJ₂] at h5

theorem map_PiW_eq (H : JSetup x K A a D J J₁ J₂) :
    (J₂.subgroupOf (Wsub x a J)).map (PiW H) = (sigma2 H.hJa H.hJ₂).range := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨(w : G), Subgroup.mem_subgroupOf.1 hw⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨⟨(k : G), J₂_le_W H k.2⟩, Subgroup.mem_subgroupOf.2 k.2, rfl⟩

theorem subnormal_range_sigma2 (H : JSetup x K A a D J J₁ J₂)
    (hodd : Odd (Nat.card (center ↥(PumpCalc.bar a J)))) :
    (((sigma2 H.hJa H.hJ₂).range).subgroupOf (centralizer ({beta0 H} : Set (J0 a J)))).IsSubnormal := by
  have hr := range_PiW H hodd
  let f : ↥(Wsub x a J) →* ↥(centralizer ({beta0 H} : Set (J0 a J))) :=
    (PiW H).codRestrict _ (fun w => hr.le ⟨w, rfl⟩)
  have hf : Function.Surjective f := by
    intro c
    have hc : (c : J0 a J) ∈ (PiW H).range := hr.symm.le c.2
    obtain ⟨w, hw⟩ := hc
    exact ⟨w, Subtype.ext hw⟩
  have hsub := (subnormal_J₂_W H).map hf
  have heq : (J₂.subgroupOf (Wsub x a J)).map f =
      ((sigma2 H.hJa H.hJ₂).range).subgroupOf (centralizer ({beta0 H} : Set (J0 a J))) := by
    ext c
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine Subgroup.mem_subgroupOf.2 ?_
      show PiW H w ∈ (sigma2 H.hJa H.hJ₂).range
      rw [← map_PiW_eq H]
      exact ⟨w, hw, rfl⟩
    · intro hc
      have hc' : (c : J0 a J) ∈ (sigma2 H.hJa H.hJ₂).range := Subgroup.mem_subgroupOf.1 hc
      rw [← map_PiW_eq H] at hc'
      obtain ⟨w, hw, hwc⟩ := hc'
      exact ⟨w, hw, Subtype.ext hwc⟩
  rwa [heq] at hsub

theorem exists_identification (hL : B1.QShape3SD (J0 a J)) (H : JSetup x K A a D J J₁ J₂)
    (hodd : Odd (Nat.card (center ↥(PumpCalc.bar a J)))) :
    ∃ (F'' : Type) (_ : Field F'') (_ : Finite F'') (S : Subgroup (J0 a J)),
      Odd (Nat.card F'') ∧ 5 ≤ Nat.card F'' ∧ Nonempty (↥S ≃* SL(2, F'')) ∧ beta0 H ∈ S ∧
      (sigma2 H.hJa H.hJ₂).range = S ∧
      (∀ σ : MulAut (J0 a J), σ * σ = 1 → (∀ s ∈ S, σ s = s) →
        σ = 1 ∨ σ = MulAut.conj (beta0 H)) ∧
      (∀ n ∈ pPrimeCore 2 ↥J₂, sigma2 H.hJa H.hJ₂ n = 1) := by
  classical
  obtain ⟨F'', _, _, S, hodd'', hF'', ⟨eS⟩, hβS, hSC, hcomm, -, hB4⟩ :=
    S3L3KGroup.exists_sl2_component hL.qShape3 H.center_J0 (orderOf_beta0 H)
  have : Fintype F'' := Fintype.ofFinite F''
  have hFc : 5 ≤ Fintype.card F'' := by rw [← Nat.card_eq_fintype_card]; exact hF''
  have hoddc : Odd (Fintype.card F'') := by rw [← Nat.card_eq_fintype_card]; exact hodd''
  have h4 : ∃ s : Finset F'', s.card = 4 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F'')) (n := 4)
      (by rw [Finset.card_univ]; omega)
    exact ⟨t, ht⟩
  have hqS : IsQuasisimple ↥S :=
    LocalCores.isQuasisimple_of_mulEquiv eS.symm (CFSG.RankThree.Classical.isQuasisimple_SL2 h4)
  set Q : Subgroup (J0 a J) := (sigma2 H.hJa H.hJ₂).range with hQ
  have hQS : Q ≤ S := by
    have h1 : ⁅Q, Q⁆ ≤ S := Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ =>
      hcomm g₁ (range_sigma2_le_centralizer H hg₁) g₂ (range_sigma2_le_centralizer H hg₂)
    rw [range_sigma2_perfect H] at h1
    exact h1
  have hsubS : (Q.subgroupOf S).IsSubnormal := by
    have h := B1.isSubnormal_subgroupOf_inf (S := S) (subnormal_range_sigma2 H hodd)
    rwa [inf_eq_left.2 hQS, inf_eq_right.2 hSC] at h
  have hSQ : S ≤ Q := by
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hqS hsubS with htop | hcen
    · intro s hs
      have : (⟨s, hs⟩ : ↥S) ∈ Q.subgroupOf S := by rw [htop]; trivial
      exact Subgroup.mem_subgroupOf.1 this
    · exfalso
      have hQabel : ⁅Q, Q⁆ = ⊥ := by
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro g₁ hg₁ g₂ hg₂
        have hc1 : (⟨g₁, hQS hg₁⟩ : ↥S) ∈ center ↥S := hcen (Subgroup.mem_subgroupOf.2 hg₁)
        have h2 := Subgroup.mem_center_iff.1 hc1 ⟨g₂, hQS hg₂⟩
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.2 (congrArg Subtype.val h2).symm
      rw [range_sigma2_perfect H] at hQabel
      have hβQ : beta0 H ∈ (sigma2 H.hJa H.hJ₂).range := ⟨⟨x * a, H.hb⟩, rfl⟩
      rw [hQabel, Subgroup.mem_bot] at hβQ
      exact beta0_ne_one H hβQ
  have hQeq : Q = S := le_antisymm hQS hSQ
  have hker : ∀ n ∈ pPrimeCore 2 ↥J₂, sigma2 H.hJa H.hJ₂ n = 1 := by
    let σ' : ↥J₂ →* ↥S := (sigma2 H.hJa H.hJ₂).codRestrict S (fun k => hQS ⟨k, rfl⟩)
    let θ : ↥J₂ →* SL(2, F'') := eS.toMonoidHom.comp σ'
    have hθs : Function.Surjective θ := by
      intro m
      obtain ⟨s, rfl⟩ := eS.surjective m
      obtain ⟨k, hk⟩ := hSQ s.2
      exact ⟨k, by
        have : σ' k = s := Subtype.ext hk
        show eS (σ' k) = eS s
        rw [this]⟩
    have hN : Odd (Nat.card (pPrimeCore 2 ↥J₂)) :=
      Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
    have h5 := S1FinalSl2.normal_odd_le_ker hoddc hFc θ hθs (pPrimeCore 2 ↥J₂) hN
    intro n hn
    have h1 : θ n = 1 := h5 hn
    have h2 : σ' n = 1 := eS.injective (by rw [map_one]; exact h1)
    exact congrArg Subtype.val h2
  exact ⟨F'', inferInstance, inferInstance, S, hodd'', hF'', ⟨eS⟩, hβS, hQeq, hB4, hker⟩

end S1FinalJ2


end CFSG.GH74.Generic.BProg.B3
