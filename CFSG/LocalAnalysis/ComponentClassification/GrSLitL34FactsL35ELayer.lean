module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltUniq

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup GrSLit.L34Facts
open scoped commutatorElement Pointwise

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem eq_layerIn_of_hat_le (h : Config G p w v L K)
    (hJL : ∀ J : Subgroup G, IsTwoComponentIn J (K ⊓ centralizer {v}) → hatOf K J ≤ hatOf K L) :
    L = GSThmB.layerIn (K ⊓ centralizer {v}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := K ⊓ centralizer ({v} : Set G) with hCdef
  have hLC := h.compLK
  have hLpc : IsPComponent 2 (L.subgroupOf C) := (isTwoComponentIn_iff hLC.1).mp hLC
  set Y := ↥K ⧸ pPrimeCore 2 ↥K
  set f := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hfdef
  have hodd : ¬ 2 ∣ Nat.card f.ker := by
    rw [hfdef, QuotientGroup.ker_mk']
    exact Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card
  obtain ⟨hbij, -, -⟩ := CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection f
    (QuotientGroup.mk'_surjective _) hodd
  have hObar : pPrimeCore 2 (↥C ⧸ pPrimeCore 2 ↥C) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have key : ∀ J' : Subgroup ↥C, IsPComponent 2 J' → J' ≤ L.subgroupOf C := by
    intro J' hJ'
    set J := J'.map C.subtype with hJdef
    have hJC : J ≤ C := map_subtype_le J'
    have hJsub : J.subgroupOf C = J' := comap_map_eq_self_of_injective C.subtype_injective J'
    have hJ : IsTwoComponentIn J C := (isTwoComponentIn_iff hJC).mpr (hJsub ▸ hJ')
    have hJK : J ≤ K := hJC.trans inf_le_left
    have hhat : hatOf K J ≤ hatOf K L := hJL J hJ
    set Jt := (J.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) with hJt
    set Lt := (L.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) with hLt
    have h1 : Jt ≤ Lt ⊔ center Y := by
      have h0 := Subgroup.comap_map_eq (QuotientGroup.mk' (center Y)) Lt
      rw [QuotientGroup.ker_mk'] at h0
      rw [← h0]
      exact Subgroup.map_le_iff_le_comap.mp hhat
    have hJtperf : ⁅Jt, Jt⁆ = Jt := by
      let g : ↥J →* ↥Jt :=
        { toFun := fun x => ⟨QuotientGroup.mk (⟨x, hJK x.2⟩ : ↥K), ⟨⟨x, hJK x.2⟩, x.2, rfl⟩⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hg : Function.Surjective g := by
        rintro ⟨_, ⟨k, hk, rfl⟩⟩
        exact ⟨⟨k, hk⟩, rfl⟩
      have hJp : Group.IsPerfect ↥J := hJ.2.2.1
      exact commutator_self_of_isPerfect (Group.IsPerfect.ofSurjective (f := g) hg)
    have h2 : Jt ≤ Lt := by
      rw [← hJtperf]
      refine (commutator_mono h1 h1).trans ((commutator_sup_center_le Lt).trans ?_)
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      rw [commutatorElement_def]
      exact Lt.mul_mem (Lt.mul_mem (Lt.mul_mem ha hb) (Lt.inv_mem ha)) (Lt.inv_mem hb)
    have h3 : J.subgroupOf K ≤ L.subgroupOf K ⊔ pPrimeCore 2 ↥K := by
      have h0 := Subgroup.comap_map_eq (QuotientGroup.mk' (pPrimeCore 2 ↥K)) (L.subgroupOf K)
      rw [QuotientGroup.ker_mk'] at h0
      rw [← h0]
      exact Subgroup.map_le_iff_le_comap.mp h2
    set O' : Subgroup ↥C := ((pPrimeCore 2 ↥K).map K.subtype).subgroupOf C with hO'
    have hO'le : O' ≤ pPrimeCore 2 ↥C := by
      refine le_pPrimeCore_of_normal_coprime ⟨fun x hx c => ?_⟩ ?_
      · rw [hO', mem_subgroupOf] at hx ⊢
        obtain ⟨o, ho, hoe⟩ := hx
        refine ⟨⟨c, (c.2).1⟩ * o * ⟨c, (c.2).1⟩⁻¹,
          (inferInstance : (pPrimeCore 2 ↥K).Normal).conj_mem o ho _, ?_⟩
        have hoe' : (o : G) = x := hoe
        change (c : G) * o * (c : G)⁻¹ = ((c * x * c⁻¹ : ↥C) : G)
        rw [hoe']
        rfl
      · let ι : ↥O' →* ↥((pPrimeCore 2 ↥K).map K.subtype) :=
          { toFun := fun x => ⟨((x : ↥C) : G), mem_subgroupOf.mp x.2⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl }
        have hι : Function.Injective ι := fun a b hab =>
          Subtype.ext (Subtype.ext (by have h0 := congrArg Subtype.val hab; exact h0))
        refine Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_injective ι hι) ?_
        rw [Subgroup.card_map_of_injective K.subtype_injective]
        exact pPrimeCore_coprime_card
    have h4 : J' ≤ L.subgroupOf C ⊔ pPrimeCore 2 ↥C := by
      intro x hx
      have hxK : (⟨(x : G), (x.2).1⟩ : ↥K) ∈ J.subgroupOf K := by
        rw [mem_subgroupOf]
        exact ⟨x, hx, rfl⟩
      have hx3 := h3 hxK
      have hset := Subgroup.mul_normal (L.subgroupOf K) (pPrimeCore 2 ↥K)
      have hx4 : (⟨(x : G), (x.2).1⟩ : ↥K) ∈
          ((L.subgroupOf K : Set ↥K) * (pPrimeCore 2 ↥K : Set ↥K)) := hset ▸ hx3
      obtain ⟨l, hl, o, ho, hlo⟩ := hx4
      have hlC : (l : G) ∈ C := hLC.1 (mem_subgroupOf.mp hl)
      have hxo : (o : G) = (l : G)⁻¹ * x := by
        have := congrArg Subtype.val hlo
        simp only [Subgroup.coe_mul] at this
        rw [← this]
        group
      have hoC : (o : G) ∈ C := by
        rw [hxo]
        exact C.mul_mem (C.inv_mem hlC) x.2
      have hxeq : x = ⟨l, hlC⟩ * ⟨o, hoC⟩ := by
        apply Subtype.ext
        have := congrArg Subtype.val hlo
        simpa using this.symm
      rw [hxeq]
      refine mul_mem (mem_sup_left (mem_subgroupOf.mpr (mem_subgroupOf.mp hl)))
        (mem_sup_right (hO'le ?_))
      rw [hO', mem_subgroupOf]
      exact ⟨o, ho, rfl⟩
    have h5 : J'.map f ≤ (L.subgroupOf C).map f := by
      have h6 := map_mono (f := f) h4
      rwa [Subgroup.map_sup, hfdef, QuotientGroup.map_mk'_self, sup_bot_eq] at h6
    have hJm : IsPComponent 2 (J'.map f) := hbij.mapsTo hJ'
    have hLm : IsPComponent 2 ((L.subgroupOf C).map f) := hbij.mapsTo hLpc
    have hJc : IsComponent (J'.map f) :=
      (isTwoComponent_iff_isComponent hObar _).mp ((isTwoComponent_iff_isPComponent _).mpr hJm)
    have hLcm : IsComponent ((L.subgroupOf C).map f) :=
      (isTwoComponent_iff_isComponent hObar _).mp ((isTwoComponent_iff_isPComponent _).mpr hLm)
    have hsub : ((J'.map f).subgroupOf ((L.subgroupOf C).map f)).IsSubnormal :=
      hJc.2.subgroupOf
    have heq : J'.map f = (L.subgroupOf C).map f := by
      rcases LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hLcm.1 hsub with
        ht | hc
      · refine le_antisymm h5 fun y hy => ?_
        have h7 : (⟨y, hy⟩ : ↥((L.subgroupOf C).map f)) ∈
            (J'.map f).subgroupOf ((L.subgroupOf C).map f) := ht ▸ mem_top _
        exact h7
      · exfalso
        have hab : ∀ a b : ↥(J'.map f), a * b = b * a := fun a b => by
          have ha : (⟨a, h5 a.2⟩ : ↥((L.subgroupOf C).map f)) ∈ center _ := hc a.2
          have h8 := mem_center_iff.mp ha ⟨b, h5 b.2⟩
          exact Subtype.ext (congrArg Subtype.val h8).symm
        have hss := subsingleton_of_isPerfect_of_isSolvable hJc.1.1
          (Group.isSolvable_of_comm hab)
        exact (not_nontrivial_iff_subsingleton.mpr hss)
          (LocalCores.isQuasisimple_nontrivial hJc.1)
    exact (hbij.injOn hJ' hLpc heq).le
  apply le_antisymm
  · have hL : L = (L.subgroupOf C).map C.subtype := by
      rw [subgroupOf_map_subtype, inf_eq_left.mpr hLC.1]
    calc L = (L.subgroupOf C).map C.subtype := hL
      _ ≤ (pLayer ↥C 2).map C.subtype := map_mono (le_sSup hLpc)
  · refine Subgroup.map_le_iff_le_comap.mpr (sSup_le fun J' hJ' => ?_)
    exact key J' hJ'

end Config

end CFSG.ComponentClassification.HarrisLit.L35
