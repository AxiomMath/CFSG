module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Lift

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem OddCentralCover.comp_mulEquiv {A A' P : Type*} [Group A] [Group A'] [Group P]
    {f : A →* P} (h : OddCentralCover f) (e : A' ≃* A) :
    OddCentralCover (f.comp e.toMonoidHom) where
  surjective := by
    intro p
    obtain ⟨a, ha⟩ := h.surjective p
    exact ⟨e.symm a, by simpa using ha⟩
  ker_le_center := by
    intro x hx
    have hxe : e x ∈ f.ker := hx
    have hcent : e x ∈ Subgroup.center A := h.ker_le_center hxe
    rw [Subgroup.mem_center_iff]
    intro y
    apply e.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hcent (e y)
  odd_card_ker := by
    have hker : (f.comp e.toMonoidHom).ker = f.ker.comap e.toMonoidHom :=
      (MonoidHom.comap_ker f e.toMonoidHom).symm
    rw [hker, Subgroup.comap_equiv_eq_map_symm' e f.ker]
    have hcard : Nat.card (f.ker.map e.symm.toMonoidHom) = Nat.card f.ker :=
      (Nat.card_congr (Subgroup.equivMapOfInjective f.ker e.symm.toMonoidHom
        e.symm.injective).toEquiv).symm
    rw [hcard]
    exact h.odd_card_ker

private theorem mem_zpowers_eq_one_or_eq {G : Type*} [Group G] {t g : G}
    (ht2 : orderOf t = 2) (hg : g ∈ Subgroup.zpowers t) : g = 1 ∨ g = t := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← hk]
  have hk2 : t ^ k = t ^ (k % (2 : ℤ)) := by
    rw [← zpow_mod_orderOf t k, ht2]
    norm_num
  rw [hk2]
  rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
  · left; rw [hk0]; simp
  · right; rw [hk1]; simp

theorem t5_b5_lift {G H : Type} [Group G] [Finite G] [Group H] {L : Subgroup G}
    (φ : ↥L →* H) (hφ : OddCentralCover φ) {r : G} (hr2 : r * r = 1)
    (hrN : r ∈ normalizer (L : Set G)) (α : MulAut H)
    (hα : ∀ l l' : ↥L, (l' : G) = r * l * r⁻¹ → φ l' = α (φ l))
    {t : G} (htL : t ∈ L) (ht2 : orderOf t = 2) (htz : (⟨t, htL⟩ : ↥L) ∈ center ↥L)
    (K Bb : Subgroup H) (hKP : K ≤ fixSub α)
    (hKn : ∀ p ∈ fixSub α, ∀ k ∈ K, p * k * p⁻¹ ∈ K) (hKq : CFSG.IsQuasisimple ↥K)
    (hBP : Bb ≤ fixSub α) (hB : IsElemAb2 Bb 5) (hπB : φ ⟨t, htL⟩ ∈ Bb)
    (hBK : ∀ b ∈ Bb, b ∈ K ∨ φ ⟨t, htL⟩ * b ∈ K)
    (hπc : (⟨φ ⟨t, htL⟩, hBP hπB⟩ : ↥(fixSub α)) ∉ commutator ↥(fixSub α)) :
    ∃ B : Subgroup G, B ≤ L ⊓ centralizer ({r} : Set G) ∧ IsElemAb2 B 5 ∧ t ∈ B ∧
      zpowers t ⊓ layerCent L r = ⊥ ∧ B = zpowers t ⊔ (B ⊓ layerCent L r) := by
  let C : Subgroup G := L ⊓ centralizer ({r} : Set G)
  let σ : MulAut ↥L := conjAut L hr2 hrN
  have hσ2 : σ * σ = 1 := conjAut_mul_self L hr2 hrN
  have hφσ : ∀ y : ↥L, φ (σ y) = α (φ y) :=
    fun y => hα y (σ y) (coe_conjAut L hr2 hrN y)
  let θ : ↥C →* ↥(fixSub α) :=
    (fixHom φ σ α hφσ).comp (fixConjEquiv L hr2 hrN).symm.toMonoidHom
  have hθ : OddCentralCover θ :=
    (hφ.oddCentralCover_fixHom hσ2 hφσ).comp_mulEquiv (fixConjEquiv L hr2 hrN).symm
  have hθφ : ∀ c : ↥C, ((θ c : ↥(fixSub α)) : H) = φ ⟨c, c.2.1⟩ := by
    intro c
    show ((fixHom φ σ α hφσ ((fixConjEquiv L hr2 hrN).symm c) : ↥(fixSub α)) : H) =
      φ ⟨c, c.2.1⟩
    rw [coe_fixHom (ρ := φ) (σ := σ) (α := α) hφσ ((fixConjEquiv L hr2 hrN).symm c)]
    exact congrArg φ (Subtype.ext rfl)
  let Bb' : Subgroup ↥(fixSub α) := Bb.subgroupOf (fixSub α)
  haveI : IsMulCommutative Bb := hB.1.1
  haveI : IsMulCommutative Bb' := inferInstance
  have hcardBb' : Nat.card Bb' = Nat.card Bb :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv
  let Bhat : Subgroup ↥C :=
    { carrier := {c : ↥C | c * c = 1 ∧ θ c ∈ Bb'}
      one_mem' := by
        refine ⟨one_mul 1, ?_⟩
        rw [map_one]
        exact Bb'.one_mem
      mul_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        have hcomm : a * b = b * a :=
          hθ.commute_of_mul_self_eq_one ha1 hb1 (setLike_mul_comm ha2 hb2)
        refine ⟨?_, ?_⟩
        · calc (a * b) * (a * b) = (a * (b * a)) * b := by group
            _ = (a * (a * b)) * b := by rw [← hcomm]
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [ha1, hb1, one_mul]
        · rw [map_mul]
          exact Bb'.mul_mem ha2 hb2
      inv_mem' := by
        rintro a ⟨ha1, ha2⟩
        have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha1
        refine ⟨?_, ?_⟩
        · rw [hai]; exact ha1
        · rw [hai]; exact ha2 }
  have hcardBhat : Nat.card Bhat = Nat.card Bb' := by
    let f : Bhat → Bb' := fun c => ⟨θ c, c.2.2⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        apply Subtype.ext
        exact hθ.eq_of_mul_self_eq_one a.2.1 b.2.1 (congrArg Subtype.val hab)
      · intro z
        have hzz : (z : ↥(fixSub α)) * (z : ↥(fixSub α)) = 1 := by
          apply Subtype.ext
          change (z : H) * (z : H) = 1
          have hz2 := hB.1.2 (z : H) z.2
          rwa [pow_two] at hz2
        obtain ⟨w, hww, hθw⟩ := hθ.exists_mul_self_eq_one_lift hzz
        refine ⟨⟨w, hww, ?_⟩, ?_⟩
        · rw [hθw]; exact z.2
        · exact Subtype.ext hθw
    exact Nat.card_congr (Equiv.ofBijective f hf)
  let B : Subgroup G := Bhat.map C.subtype
  have hBC : B ≤ C := Subgroup.map_subtype_le Bhat
  have hBcard : Nat.card B = 2 ^ 5 := by
    change Nat.card (Bhat.map C.subtype) = 2 ^ 5
    rw [Subgroup.card_subtype C Bhat, hcardBhat, hcardBb', hB.2]
  have hBcommB : IsMulCommutative B := by
    refine IsMulCommutative.of_setLike_mul_comm ?_
    intro x hx y hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hy
    have hcd : c * d = d * c :=
      hθ.commute_of_mul_self_eq_one hc.1 hd.1 (setLike_mul_comm hc.2 hd.2)
    simpa using congrArg Subtype.val hcd
  have hBexp : ∀ x ∈ B, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    rw [pow_two]
    exact congrArg Subtype.val hc.1
  have hBelem : IsElemAb2 B 5 := ⟨⟨hBcommB, hBexp⟩, hBcard⟩
  have htt : t * t = 1 := by simpa [pow_two, ht2] using pow_orderOf_eq_one t
  set t' : G := r * t * r⁻¹ with ht'def
  have ht'L : t' ∈ L := by
    rw [ht'def]
    exact (Subgroup.mem_set_normalizer_iff.mp hrN t).mp htL
  have ht'2 : t' * t' = 1 := by
    rw [ht'def]
    calc (r * t * r⁻¹) * (r * t * r⁻¹) = r * (t * t) * r⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hφt' : φ ⟨t', ht'L⟩ = φ ⟨t, htL⟩ := by
    have h1 : φ ⟨t', ht'L⟩ = α (φ ⟨t, htL⟩) :=
      hα ⟨t, htL⟩ ⟨t', ht'L⟩ ht'def
    rw [h1]
    exact mem_fixSub_iff.mp (hBP hπB)
  have ht't : (⟨t', ht'L⟩ : ↥L) = ⟨t, htL⟩ :=
    hφ.eq_of_mul_self_eq_one (Subtype.ext ht'2) (Subtype.ext htt) hφt'
  have hconj : r * t * r⁻¹ = t := by
    rw [← ht'def]
    exact congrArg Subtype.val ht't
  have htc : t ∈ centralizer ({r} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hconj).symm
  let tC : ↥C := ⟨t, htL, htc⟩
  have htC2 : tC * tC = 1 := Subtype.ext htt
  have hθtCH : ((θ tC : ↥(fixSub α)) : H) = φ ⟨t, htL⟩ :=
    (hθφ tC).trans (congrArg φ (Subtype.ext rfl))
  have hθtCBb' : θ tC ∈ Bb' := by
    rw [Subgroup.mem_subgroupOf, hθtCH]
    exact hπB
  have htCBhat : tC ∈ Bhat := ⟨htC2, hθtCBb'⟩
  have htB : t ∈ B := Subgroup.mem_map.mpr ⟨tC, htCBhat, rfl⟩
  have ht_not_layer : t ∉ layerCent L r := by
    intro htl
    obtain ⟨y, hyl, hyg⟩ := Subgroup.mem_map.mp htl
    have hyt : y = tC := by
      have h1 : C.subtype y = C.subtype tC := by rw [hyg]; rfl
      exact C.subtype_injective h1
    have hyl' : tC ∈ CFSG.layer ↥C := by rwa [hyt] at hyl
    have hperf : CFSG.layer ↥C = ⁅CFSG.layer ↥C, CFSG.layer ↥C⁆ :=
      (CFSG.LocalCores.layer_perfect (G := ↥C)).symm
    have hmem : θ tC ∈ ⁅(CFSG.layer ↥C).map θ, (CFSG.layer ↥C).map θ⁆ := by
      have h1 : θ tC ∈ (CFSG.layer ↥C).map θ := Subgroup.mem_map.mpr ⟨tC, hyl', rfl⟩
      rwa [hperf, Subgroup.map_commutator] at h1
    have hle : ⁅(CFSG.layer ↥C).map θ, (CFSG.layer ↥C).map θ⁆ ≤
        commutator ↥(fixSub α) := Subgroup.commutator_mono le_top le_top
    have hcon : θ tC ∈ commutator ↥(fixSub α) := hle hmem
    have hθtC_eq : θ tC = (⟨φ ⟨t, htL⟩, hBP hπB⟩ : ↥(fixSub α)) :=
      Subtype.ext hθtCH
    exact hπc (hθtC_eq ▸ hcon)
  have hbot : zpowers t ⊓ layerCent L r = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    rw [Subgroup.mem_bot]
    rcases hg with ⟨hgz, hgl⟩
    rcases mem_zpowers_eq_one_or_eq ht2 hgz with hg1 | hgt
    · exact hg1
    · exact absurd (hgt ▸ hgl) ht_not_layer
  let K' : Subgroup ↥(fixSub α) := K.subgroupOf (fixSub α)
  have hK'normal : K'.Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hKn (g : H) g.2 (n : H) hn⟩
  have hK'q : CFSG.IsQuasisimple ↥K' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hKP).symm hKq
  have hK'comp : CFSG.IsComponent K' := ⟨hK'q, hK'normal.isSubnormal⟩
  have hK'le_layer : K' ≤ CFSG.layer ↥(fixSub α) :=
    CFSG.LocalCores.component_le_layer hK'comp
  have hK'_layer : ∀ c : ↥C, c * c = 1 → θ c ∈ K' → c ∈ CFSG.layer ↥C := by
    intro c hc hcK
    have hcL : θ c ∈ CFSG.layer ↥(fixSub α) := hK'le_layer hcK
    have hθc2 : θ c * θ c = 1 := by rw [← map_mul, hc, map_one]
    obtain ⟨a, haL, haa, hθa⟩ := hθ.exists_involution_layer_lift hcL hθc2
    exact (hθ.eq_of_mul_self_eq_one haa hc hθa) ▸ haL
  have hsplit : B = zpowers t ⊔ (B ⊓ layerCent L r) := by
    apply le_antisymm
    · intro b hb
      obtain ⟨cC, hcCBhat, rfl⟩ := Subgroup.mem_map.mp hb
      have hθcCBb : (θ cC : H) ∈ Bb := Subgroup.mem_subgroupOf.mp hcCBhat.2
      rcases hBK (θ cC : H) hθcCBb with hK | hK
      · have hcCK' : θ cC ∈ K' := Subgroup.mem_subgroupOf.mpr hK
        have hcC_layer : cC ∈ CFSG.layer ↥C := hK'_layer cC hcCBhat.1 hcCK'
        have hbB : (cC : G) ∈ B := Subgroup.mem_map.mpr ⟨cC, hcCBhat, rfl⟩
        have hbL : (cC : G) ∈ layerCent L r :=
          Subgroup.mem_map.mpr ⟨cC, hcC_layer, rfl⟩
        exact Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hbB, hbL⟩)
      · have hθcC'K : θ (tC * cC) ∈ K' := by
          apply Subgroup.mem_subgroupOf.mpr
          have hprod : ((θ (tC * cC) : ↥(fixSub α)) : H) = φ ⟨t, htL⟩ * (θ cC : H) := by
            rw [map_mul]
            change ((θ tC : ↥(fixSub α)) : H) * ((θ cC : ↥(fixSub α)) : H) =
              φ ⟨t, htL⟩ * ((θ cC : ↥(fixSub α)) : H)
            rw [hθtCH]
          rw [hprod]
          exact hK
        have hcC'Bhat : tC * cC ∈ Bhat := Bhat.mul_mem htCBhat hcCBhat
        have hcC'_layer : tC * cC ∈ CFSG.layer ↥C :=
          hK'_layer (tC * cC) hcC'Bhat.1 hθcC'K
        have htbB : t * (cC : G) ∈ B := by
          have h1 : ((tC * cC : ↥C) : G) ∈ B :=
            Subgroup.mem_map.mpr ⟨tC * cC, hcC'Bhat, rfl⟩
          simpa using h1
        have htbL : t * (cC : G) ∈ layerCent L r := by
          have h1 : ((tC * cC : ↥C) : G) ∈ layerCent L r :=
            Subgroup.mem_map.mpr ⟨tC * cC, hcC'_layer, rfl⟩
          simpa using h1
        have htb : t * (cC : G) ∈ B ⊓ layerCent L r :=
          Subgroup.mem_inf.mpr ⟨htbB, htbL⟩
        have hb_eq : C.subtype cC = t * (t * C.subtype cC) := by
          rw [← mul_assoc, htt, one_mul]
        rw [hb_eq]
        exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers t) htb
    · exact sup_le (Subgroup.zpowers_le.mpr htB) inf_le_left
  exact ⟨B, hBC, hBelem, htB, hbot, hsplit⟩

end CFSG.OddStandard.SmallF3.Omega
