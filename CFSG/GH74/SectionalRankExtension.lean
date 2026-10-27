module

public import CFSG.GH74.SectionalRank
public import CFSG.Holt.TwoGroups
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitCentralExtension
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections

public section

namespace CFSG.GH74

open Subgroup

theorem SectionalTwoRankLE.of_normal {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    {a b : ℕ} (hN : SectionalTwoRankLE N a) (hQ : SectionalTwoRankLE (G ⧸ N) b) :
    SectionalTwoRankLE G (a + b) := by
  classical
  intro P hP
  obtain ⟨s, hs, hsP⟩ := hN (P.comap N.subtype) hP.comap_subtype
  obtain ⟨t, ht, htQ⟩ := hQ (P.map (QuotientGroup.mk' N)) (hP.map (QuotientGroup.mk' N))
  let lift : G ⧸ N → G := fun q =>
    if h : q ∈ P.map (QuotientGroup.mk' N) then Classical.choose (Subgroup.mem_map.1 h) else 1
  have hlift_mem : ∀ q (hq : q ∈ P.map (QuotientGroup.mk' N)), lift q ∈ P := by
    intro q hq
    simp only [lift, dif_pos hq]
    exact (Classical.choose_spec (Subgroup.mem_map.1 hq)).1
  have hlift_mk : ∀ q (hq : q ∈ P.map (QuotientGroup.mk' N)),
      (QuotientGroup.mk' N) (lift q) = q := by
    intro q hq
    simp only [lift, dif_pos hq]
    exact (Classical.choose_spec (Subgroup.mem_map.1 hq)).2
  have hPN : Subgroup.closure ((s.image N.subtype : Finset G) : Set G) = P ⊓ N := by
    have h := congrArg (Subgroup.map N.subtype) hsP
    rw [MonoidHom.map_closure, Subgroup.map_comap_eq, Subgroup.range_subtype] at h
    rw [inf_comm, ← h, Finset.coe_image]
  have hmapu : (Subgroup.closure ((t.image lift : Finset G) : Set G)).map
      (QuotientGroup.mk' N) = Subgroup.closure (t : Set (G ⧸ N)) := by
    have hu : (t.image fun x => (QuotientGroup.mk' N) (lift x)) = t := by
      refine Finset.ext fun q => ?_
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [hlift_mk x (htQ ▸ Subgroup.subset_closure hx)]
        exact hx
      · intro hq
        exact ⟨q, hq, hlift_mk q (htQ ▸ Subgroup.subset_closure hq)⟩
    rw [MonoidHom.map_closure]
    have hcoe : (QuotientGroup.mk' N) '' ((t.image lift : Finset G) : Set G) =
        ((t.image fun x => (QuotientGroup.mk' N) (lift x) : Finset (G ⧸ N)) :
          Set (G ⧸ N)) := by
      rw [Finset.coe_image, Set.image_image, ← Finset.coe_image]
    rw [hcoe, hu]
  set H : Subgroup G := Subgroup.closure
    (((s.image N.subtype : Finset G) ∪ t.image lift : Finset G) : Set G) with hH_def
  have hHleP : H ≤ P := by
    refine (Subgroup.closure_le P).2 ?_
    intro x hx
    rw [Finset.coe_union, Set.mem_union] at hx
    rcases hx with hx | hx
    · rw [Finset.coe_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact Subgroup.mem_comap.1 (hsP ▸ Subgroup.subset_closure hy)
    · rw [Finset.coe_image] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      exact hlift_mem q (htQ ▸ Subgroup.subset_closure hq)
  have hPleH : P ≤ H := by
    intro x hx
    have hxq : (QuotientGroup.mk' N) x ∈ (Subgroup.closure
        ((t.image lift : Finset G) : Set G)).map (QuotientGroup.mk' N) := by
      rw [hmapu, htQ]
      exact Subgroup.mem_map_of_mem _ hx
    obtain ⟨h, hh, hhx⟩ := Subgroup.mem_map.1 hxq
    have hhH : h ∈ H :=
      Subgroup.closure_mono (by
        intro y hy
        exact Finset.mem_union_right _ (by simpa using hy)) hh
    have hker : x * h⁻¹ ∈ N := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      have h1 : (QuotientGroup.mk' N) (x * h⁻¹) = 1 := by
        rw [map_mul, map_inv, hhx, mul_inv_cancel]
      simpa only [QuotientGroup.mk'_apply] using h1
    have hmemS : x * h⁻¹ ∈ Subgroup.closure ((s.image N.subtype : Finset G) : Set G) := by
      rw [hPN]
      exact ⟨P.mul_mem hx (P.inv_mem (hHleP hhH)), hker⟩
    have hmem : x * h⁻¹ ∈ H :=
      Subgroup.closure_mono (by
        intro y hy
        exact Finset.mem_union_left _ (by simpa using hy)) hmemS
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using H.mul_mem hmem hhH
  refine ⟨(s.image N.subtype : Finset G) ∪ t.image lift, ?_,
    le_antisymm hHleP hPleH⟩
  calc ((s.image N.subtype : Finset G) ∪ t.image lift).card
      ≤ (s.image N.subtype : Finset G).card + (t.image lift).card := Finset.card_union_le _ _
    _ ≤ s.card + t.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
    _ ≤ a + b := Nat.add_le_add hs ht

theorem SectionalTwoRankLE.quotient_of_sup_eq_top {X : Type*} [Group X] [Finite X]
    (N : Subgroup X) [N.Normal] {T : Subgroup X} {r : ℕ} (hT : SectionalTwoRankLE T r)
    (hsup : T ⊔ N = ⊤) : SectionalTwoRankLE (X ⧸ N) r := by
  haveI : Finite T := inferInstance
  refine SectionalTwoRankLE.of_surjective ((QuotientGroup.mk' N).comp T.subtype) ?_ hT
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
  obtain ⟨t, ht, n, hn, rfl⟩ :=
    Subgroup.mem_sup_of_normal_right.1 (hsup ▸ Subgroup.mem_top x)
  refine ⟨⟨t, ht⟩, ?_⟩
  rw [MonoidHom.comp_apply, Subgroup.coe_subtype]
  show (QuotientGroup.mk' N) t = (QuotientGroup.mk' N) (t * n)
  rw [map_mul, show (QuotientGroup.mk' N) n = 1 from (QuotientGroup.eq_one_iff n).2 hn,
    mul_one]

theorem SectionalTwoRankLE.prod {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {a b : ℕ} (hA : SectionalTwoRankLE A a) (hB : SectionalTwoRankLE B b) :
    SectionalTwoRankLE (A × B) (a + b) := by
  classical
  let N : Subgroup (A × B) := (⊤ : Subgroup A).prod (⊥ : Subgroup B)
  have hN : SectionalTwoRankLE N a := by
    let e : N →* A := (MonoidHom.fst A B).comp N.subtype
    have he : Function.Bijective e := by
      constructor
      · rintro ⟨⟨x, y⟩, hx, hy⟩ ⟨⟨x', y'⟩, hx', hy'⟩ hxy
        have hy1 : y = 1 := by simpa using hy
        have hy'1 : y' = 1 := by simpa using hy'
        have hxx' : x = x' := by simpa [e] using hxy
        subst hxx'
        subst hy1
        subst hy'1
        rfl
      · intro x
        refine ⟨⟨(x, 1), ?_⟩, rfl⟩
        rw [Subgroup.mem_prod]
        exact ⟨Subgroup.mem_top _, Subgroup.mem_bot.2 rfl⟩
    exact SectionalTwoRankLE.of_mulEquiv (MulEquiv.ofBijective e he).symm hA
  have hQ : SectionalTwoRankLE ((A × B) ⧸ N) b := by
    let q : (A × B) →* B := MonoidHom.snd A B
    have hq : N ≤ q.ker := by
      rintro ⟨x, y⟩ hy
      have hy1 : y = 1 := by simpa using hy.2
      rw [MonoidHom.mem_ker]
      show y = 1
      exact hy1
    let e : ((A × B) ⧸ N) →* B := QuotientGroup.lift N q hq
    have he : Function.Bijective e := by
      constructor
      · intro p r hpr
        obtain ⟨⟨x, y⟩, rfl⟩ := QuotientGroup.mk'_surjective N p
        obtain ⟨⟨x', y'⟩, rfl⟩ := QuotientGroup.mk'_surjective N r
        have hpr' : y = y' := by simpa [e, q] using hpr
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hpr',
          Subgroup.mem_prod]
        refine ⟨Subgroup.mem_top _, ?_⟩
        rw [Subgroup.mem_bot]
        simp
      · intro y
        exact ⟨QuotientGroup.mk' N (1, y), by simp [e, q]⟩
    exact SectionalTwoRankLE.of_mulEquiv (MulEquiv.ofBijective e he).symm hB
  simpa using SectionalTwoRankLE.of_normal N hN hQ

theorem SectionalTwoRankLE.of_isCyclic {G : Type*} [Group G] (hG : IsCyclic G) :
    SectionalTwoRankLE G 1 := by
  intro P _
  haveI : IsCyclic P := isCyclic_of_injective P.subtype P.subtype_injective
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp (inferInstance : IsCyclic P)
  refine ⟨{(g : G)}, by simp, ?_⟩
  have h := congrArg (Subgroup.map P.subtype) hg
  rw [MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype] at h
  rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]
  exact h

theorem SectionalTwoRankLE.units (K : Type*) [Field K] [Finite K] :
    SectionalTwoRankLE Kˣ 1 :=
  SectionalTwoRankLE.of_isCyclic inferInstance

theorem SectionalTwoRankLE.specialLinearGroup (K : Type*) [Field K] [Finite K] (h2 : (2 : K) ≠ 0) :
    SectionalTwoRankLE (Matrix.SpecialLinearGroup (Fin 2) K) 2 := by
  classical
  intro P hP
  haveI : Finite P := inferInstance
  have hPinv : CFSG.ComponentClassification.AschbacherToolkit.AtMostOneInvolution P := by
    intro s t hs ht
    have hs2 : ((s : Matrix.SpecialLinearGroup (Fin 2) K)) ^ 2 = 1 := by
      have h : s ^ 2 = 1 := by simpa [hs] using pow_orderOf_eq_one s
      simpa using congrArg Subtype.val h
    have ht2 : ((t : Matrix.SpecialLinearGroup (Fin 2) K)) ^ 2 = 1 := by
      have h : t ^ 2 = 1 := by simpa [ht] using pow_orderOf_eq_one t
      simpa using congrArg Subtype.val h
    have hs1 : (s : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 := by
      intro h
      have hsone : s = 1 := Subtype.ext (by simpa using h)
      rw [hsone, orderOf_one] at hs
      omega
    have ht1 : (t : Matrix.SpecialLinearGroup (Fin 2) K) ≠ 1 := by
      intro h
      have htsone : t = 1 := Subtype.ext (by simpa using h)
      rw [htsone, orderOf_one] at ht
      omega
    exact Subtype.ext (Subtype.ext ((CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 _ hs2 hs1).trans
      (CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 _ ht2 ht1).symm))
  rcases CFSG.Holt.isCyclic_or_quaternion_of_atMostOneInvolution hP hPinv with hcyc | ⟨n, hn, ⟨e⟩⟩
  · obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
    refine ⟨{(g : Matrix.SpecialLinearGroup (Fin 2) K)}, by simp, ?_⟩
    have h := congrArg (Subgroup.map P.subtype) hg
    rw [MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype] at h
    rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure]
    exact h
  · haveI : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
    set g₁ : P := e.symm (QuaternionGroup.a (1 : ZMod (2 * 2 ^ (n - 2)))) with hg₁
    set g₂ : P := e.symm (QuaternionGroup.xa 0) with hg₂
    have hgen := CFSG.ComponentClassification.AschbacherToolkit.quaternion_closure_generators
      (n := 2 ^ (n - 2))
    have hmapP : Subgroup.closure ({g₁, g₂} : Set P) = ⊤ := by
      have hmap := congrArg (Subgroup.map e.symm.toMonoidHom) hgen
      rw [MonoidHom.map_closure, Set.image_pair,
        Subgroup.map_top_of_surjective _ e.symm.surjective] at hmap
      simpa [hg₁, hg₂] using hmap
    refine ⟨{(g₁ : Matrix.SpecialLinearGroup (Fin 2) K),
      (g₂ : Matrix.SpecialLinearGroup (Fin 2) K)}, Finset.card_le_two, ?_⟩
    have h := congrArg (Subgroup.map P.subtype) hmapP
    rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top, Subgroup.range_subtype] at h
    simpa using h

end CFSG.GH74

end
