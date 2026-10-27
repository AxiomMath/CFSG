module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.LocalBalance

variable {G : Type} [Group G]

theorem normalizerMonoidHom_val (K : Subgroup G) (γ : ↥(Subgroup.normalizer (K : Set G)))
    (x : ↥K) : ((K.normalizerMonoidHom γ x : ↥K) : G) = (γ : G) * (x : G) * (γ : G)⁻¹ := rfl

theorem exists_fixed_fibre [Finite G] (K : Subgroup G) (u : G) (hu : u ∈ Subgroup.normalizer (K : Set G))
    (hu3 : u ^ 3 = 1) (q : ↥K ⧸ GLAPPrimeCore 3 ↥K) (hq : barAut 3 K ⟨u, hu⟩ q = q) :
    ∃ y : ↥K, (QuotientGroup.mk y : ↥K ⧸ GLAPPrimeCore 3 ↥K) = q ∧ u * (y : G) = (y : G) * u := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set γ : ↥(Subgroup.normalizer (K : Set G)) := ⟨u, hu⟩ with hγ
  let c : Equiv.Perm ↥K := (K.normalizerMonoidHom γ).toEquiv
  let p : ↥K → Prop := fun x => (QuotientGroup.mk x : ↥K ⧸ GLAPPrimeCore 3 ↥K) = q
  have hc : ∀ x : ↥K, ((c x : ↥K) : G) = u * (x : G) * u⁻¹ := fun x => rfl
  have hiff : ∀ z : ↥K ⧸ GLAPPrimeCore 3 ↥K, barAut 3 K γ z = q ↔ z = q := by
    intro z
    constructor
    · intro h
      apply (barAut 3 K γ).injective
      rw [h]
      exact hq.symm
    · intro h
      rw [h]
      exact hq
  have hp : ∀ x, p (c x) ↔ p x := by
    intro x
    have hmk : (QuotientGroup.mk (c x) : ↥K ⧸ GLAPPrimeCore 3 ↥K) = barAut 3 K γ (QuotientGroup.mk x) := by
      rw [barAut_mk]
      rfl
    show (QuotientGroup.mk (c x) : ↥K ⧸ GLAPPrimeCore 3 ↥K) = q ↔ (QuotientGroup.mk x : ↥K ⧸ GLAPPrimeCore 3 ↥K) = q
    rw [hmk]
    exact hiff _
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective q
  have hfib : Nat.card {x : ↥K // p x} = Nat.card (GLAPPrimeCore 3 ↥K) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x₀⁻¹ * x.1, ?_⟩
        invFun := fun n => ⟨x₀ * n.1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hxq : (QuotientGroup.mk x.1 : ↥K ⧸ GLAPPrimeCore 3 ↥K) = q := x.2
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hx₀, hxq,
        inv_mul_cancel]
    · have hn : (QuotientGroup.mk n.1 : ↥K ⧸ GLAPPrimeCore 3 ↥K) = 1 :=
        (QuotientGroup.eq_one_iff n.1).2 n.2
      show (QuotientGroup.mk (x₀ * n.1) : ↥K ⧸ GLAPPrimeCore 3 ↥K) = q
      rw [QuotientGroup.mk_mul, hx₀, hn, mul_one]
    · intro x
      apply Subtype.ext
      simp
    · intro n
      apply Subtype.ext
      simp
  have hcop : Nat.Coprime 3 (Nat.card {x : ↥K // p x}) := by
    rw [hfib]
    exact CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥K)
  have hc3 : c ^ 3 = 1 := by
    ext x
    have h3' : u * (u * u) = 1 := by rw [← pow_three]; exact hu3
    have hx : ((c (c (c x)) : ↥K) : G) = (x : G) := by
      rw [hc, hc, hc]
      calc u * (u * (u * (x : G) * u⁻¹) * u⁻¹) * u⁻¹ = (u * (u * u)) * (x : G) * (u * (u * u))⁻¹ := by
            group
        _ = (x : G) := by rw [h3']; simp
    simpa [pow_succ, Equiv.Perm.mul_apply] using Subtype.ext hx
  let σ : Equiv.Perm {x : ↥K // p x} := Equiv.Perm.subtypePerm c hp
  have hσ3 : σ ^ 3 = 1 := by
    have hgen : ∀ (f : Equiv.Perm ↥K) (hf : ∀ x, p (f x) ↔ p x), f = 1 → f.subtypePerm hf = 1 := by
      intro f hf hf1
      subst hf1
      rfl
    show (c.subtypePerm hp) ^ 3 = 1
    rw [Equiv.Perm.subtypePerm_pow]
    exact hgen (c ^ 3) _ hc3
  obtain ⟨a, ha⟩ := exists_fixed_of_perm_pow_three σ hσ3 hcop
  refine ⟨a.1, a.2, ?_⟩
  have hfix : c a.1 = a.1 := by
    have := congrArg Subtype.val ha
    simpa [σ, Equiv.Perm.subtypePerm_apply] using this
  have h2 : u * (a.1 : G) * u⁻¹ = (a.1 : G) := by rw [← hc, hfix]
  calc u * (a.1 : G) = (u * (a.1 : G) * u⁻¹) * u := by group
    _ = (a.1 : G) * u := by rw [h2]

theorem map_comap_inf_centralizer_eq [Finite G] {K : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (K : Set G)) (hu3 : u ^ 3 = 1) :
    ((K ⊓ S9.cx u).comap K.subtype).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) =
      u4Fix (barAut 3 K ⟨u, hu⟩) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxc : u * (x : G) = (x : G) * u := by
      have hx' : (x : G) ∈ K ⊓ S9.cx u := hx
      exact (Subgroup.mem_centralizer_iff.1 hx'.2) u (Set.mem_singleton u)
    show barAut 3 K ⟨u, hu⟩ (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [barAut_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_val]
    show u * (x : G) * u⁻¹ = (x : G)
    rw [hxc, mul_inv_cancel_right]
  · intro q hq
    have hq' : barAut 3 K ⟨u, hu⟩ q = q := hq
    obtain ⟨y, hy, hyc⟩ := exists_fixed_fibre K u hu hu3 q hq'
    have hmem : y ∈ (K ⊓ S9.cx u).comap K.subtype :=
      ⟨y.2, Subgroup.mem_centralizer_iff.2 (fun h hh => by
        rw [Set.mem_singleton_iff.1 hh]
        exact hyc)⟩
    exact ⟨y, hmem, hy⟩

theorem pQuot_equiv_of_le [Finite G] {K J : Subgroup G} (hJK : J ≤ K) :
    Nonempty (PQuot 3 J ≃* PQuot 3 (J.comap K.subtype)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let e : ↥J ≃* ↥(J.comap K.subtype) := (Subgroup.subgroupOfEquivOfLe hJK).symm
  have h : (GLAPPrimeCore 3 ↥J).map e.toMonoidHom = GLAPPrimeCore 3 ↥(J.comap K.subtype) :=
    pPrimeCore_map_iso 3 e
  exact ⟨QuotientGroup.congr (GLAPPrimeCore 3 ↥J) (GLAPPrimeCore 3 ↥(J.comap K.subtype)) e h⟩

theorem u4Hyp_of_component [Finite G] {K : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.normalizer (K : Set G)) (hu3 : u ^ 3 = 1) {J : Subgroup G}
    (hJ : GLAPComponent 3 (K ⊓ S9.cx u) J) (hcat : catalogIs (PSimple 3 J) S9.isU4two) :
    U4Hyp (barAut 3 K ⟨u, hu⟩) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hJK : J ≤ K := le_trans hJ.1 inf_le_left
  have hJsub : CFSG.Open.IsSubnormal J (K ⊓ S9.cx u) := hJ.2.1
  have hsub : CFSG.Open.IsSubnormal (J.comap K.subtype) ((K ⊓ S9.cx u).comap K.subtype) :=
    CFSG.Open.IsSubnormal.comap K.subtype hJsub
  have hcov := map_comap_inf_centralizer_eq hu hu3
  refine ⟨(J.comap K.subtype).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)), ?_, ?_, ?_⟩
  · rw [← hcov]
    exact CFSG.Open.IsSubnormal.map _ hsub
  · obtain ⟨e1⟩ := pQuot_equiv_of_le (G := G) hJK
    obtain ⟨e2⟩ := pQuot_equiv_image (J.comap K.subtype)
    exact CFSG.Open.IsQuasisimple.of_mulEquiv (e1.trans e2).symm (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ)
  · obtain ⟨e1⟩ := pQuot_equiv_of_le (G := G) hJK
    obtain ⟨e2⟩ := pQuot_equiv_image (J.comap K.subtype)
    exact u4_catalogIs_of_equiv (psimple_equiv (e1.trans e2)).some hcat

end CFSG.LocalAnalysis.GLTheoremA.CatB

end
