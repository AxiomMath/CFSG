module

public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.GroupTheory.TitsSystem.Parabolic
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.Lie

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

@[expose] def simpleRefl (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) : Set (WeylGroup (borel D H) (weylN n H)) :=
  Set.range fun i => ((⟨n i, n_mem_weylN i⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H))

section TitsSystem

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

include hct hext in
theorem cartan_borel_weylN :
    cartan (borel D H) (weylN n H) = (⨆ i, H i).subgroupOf (weylN n H) := by
  show (borel D H ⊓ weylN n H).subgroupOf (weylN n H) = _
  rw [borel_inf_weylN hct hext]

include hct hext in
theorem cartan_borel_weylN_eq_ker :
    cartan (borel D H) (weylN n H) = (weylNHom hct hext).ker := by
  rw [cartan_borel_weylN hct hext, ker_weylNHom hct hext]

include hct hext in
theorem cartan_borel_weylN_normal : (cartan (borel D H) (weylN n H)).Normal := by
  rw [cartan_borel_weylN hct hext]
  exact iSup_subgroupOf_weylN_normal hct hext

include hct hext in
theorem isBNPair_borel_weylN :
    haveI := cartan_borel_weylN_normal hct hext
    IsBNPair (borel D H) (weylN n H) (simpleRefl D n H) := by
  have := cartan_borel_weylN_normal hct hext
  set B := borel D H with hB
  set N := weylN n H with hN
  set ν := weylNHom hct hext with hν
  have hker := cartan_borel_weylN_eq_ker hct hext
  have hsame : ∀ x y : N, (x : WeylGroup B N) = y → ν x = ν y := by
    intro x y hxy
    have h := QuotientGroup.eq.mp hxy
    rw [hker, MonoidHom.mem_ker, map_mul, map_inv] at h
    exact (inv_mul_eq_one.mp h)
  have hcell : ∀ x : N, bruhatCell hct (ν x) ⊆ dc B N (x : WeylGroup B N) := by
    intro x g hg
    rw [bruhatCell_eq_of_actsAs hct hext x.2 (actsAs_weylNHom hct hext x)] at hg
    obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hg
    exact ⟨x, rfl, Set.mul_mem_mul (Set.mul_mem_mul hb₁ (Set.mem_singleton _)) hb₂⟩
  have hrep : ∀ x : N, (nrep hct (ν x))⁻¹ * (x : K) ∈ ⨆ k, H k := by
    intro x
    refine mem_iSup_of_actsAs_one hct hext
      (mul_mem (inv_mem (nrep_mem_weylN hct (ν x))) x.2) ?_
    have h := (actsAs_nrep hct (ν x)).inv.mul (actsAs_weylNHom hct hext x)
    rwa [inv_mul_cancel] at h
  have hsimple : ∀ (i : Fin D.rank) (x : N),
      ((⟨n i, n_mem_weylN i⟩ : N) : WeylGroup B N) = x →
        (n i)⁻¹ * (x : K) ∈ ⨆ k, H k ∧
          ν x = (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i := by
    intro i x hix
    have h := QuotientGroup.eq.mp hix
    refine ⟨?_, ?_⟩
    · rw [cartan_borel_weylN hct hext, Subgroup.mem_subgroupOf] at h
      simpa using h
    · rw [← hsame _ _ hix]
      exact weylNHom_n hct hext i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [eq_top_iff, ← closure_borel_union_range hct, Subgroup.closure_le]
    rintro x (hx | ⟨i, rfl⟩)
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right (n_mem_weylN i)
  ·
    rintro s ⟨i, rfl⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hker, MonoidHom.mem_ker, map_pow,
        weylNHom_n hct hext i]
      exact (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_sq i
    · intro h1
      rw [QuotientGroup.eq_one_iff, hker, MonoidHom.mem_ker, weylNHom_n hct hext i] at h1
      exact (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple_ne_one i h1
  ·
    rw [eq_top_iff]
    rintro q -
    induction q using QuotientGroup.induction_on with
    | H x =>
      set Q : Subgroup N := (Subgroup.closure (simpleRefl D n H)).comap
        (QuotientGroup.mk' (cartan B N)) with hQ
      have hle : N ≤ Q.map N.subtype := by
        refine sup_le ?_ ?_
        · intro t ht
          refine ⟨⟨t, iSup_le_weylN ht⟩, ?_, rfl⟩
          show QuotientGroup.mk' (cartan B N) ⟨t, iSup_le_weylN ht⟩ ∈
            Subgroup.closure (simpleRefl D n H)
          rw [QuotientGroup.mk'_apply]
          have h1 : ((⟨t, iSup_le_weylN ht⟩ : N) : WeylGroup B N) = 1 := by
            rw [QuotientGroup.eq_one_iff, cartan_borel_weylN hct hext, Subgroup.mem_subgroupOf]
            exact ht
          rw [h1]
          exact one_mem _
        · rw [Subgroup.closure_le]
          rintro _ ⟨i, rfl⟩
          exact ⟨⟨n i, n_mem_weylN i⟩, Subgroup.subset_closure ⟨i, rfl⟩, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hle x.2
      have hyx' : y = x := Subtype.ext hyx
      rw [hyx'] at hy
      exact hy
  ·
    rintro n' m' ⟨i, hi⟩ x hx
    obtain ⟨y, ⟨a, ha, b, hb, rfl⟩, c, hc, rfl⟩ := hx
    rw [Set.mem_singleton_iff] at ha hc
    subst ha hc
    obtain ⟨ht, hνn⟩ := hsimple i n' hi
    have htb : (n i)⁻¹ * (n' : K) * b ∈ B := mul_mem (iSup_le_borel ht) hb
    have ht' := hrep m'
    have e : (n' : K) * b * m' =
        n i * ((n i)⁻¹ * n' * b) * nrep hct (ν m') * ((nrep hct (ν m'))⁻¹ * m') := by group
    show (n' : K) * b * (m' : K) ∈ _
    rw [e]
    rcases n_mul_mul_nrep_mem hct hext (ν m') i htb with h1 | h2
    · exact Or.inl (hcell m' (mul_mem_bruhatCell_right hct h1 (iSup_le_borel ht')))
    · right
      have hνnm : ν (n' * m') = (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i * ν m' := by
        rw [map_mul, hνn]
      have := hcell (n' * m') (by
        rw [hνnm]
        exact mul_mem_bruhatCell_right hct h2 (iSup_le_borel ht'))
      rwa [QuotientGroup.mk_mul] at this
  ·
    rintro n' ⟨i, hi⟩ heq
    apply not_map_conj_n_borel_le hct hext i
    obtain ⟨ht, -⟩ := hsimple i n' hi
    have htB : (n i)⁻¹ * (n' : K) ∈ B := iSup_le_borel ht
    have hsq : ((n i) ^ 2)⁻¹ ∈ B := inv_mem (iSup_le_borel (sq_n_mem_iSup hct i))
    rintro _ ⟨b, hb, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hmem : (n' : K) * (((n i)⁻¹ * n')⁻¹ * b) * n' ∈ (B : Set K) := by
      rw [← heq]
      exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mem_singleton _)
        (mul_mem (inv_mem htB) hb)) (Set.mem_singleton _)
    have e : n i * b * (n i)⁻¹ =
        ((n' : K) * (((n i)⁻¹ * n')⁻¹ * b) * n') * ((n i)⁻¹ * n')⁻¹ * ((n i) ^ 2)⁻¹ := by
      group
    rw [e]
    exact mul_mem (mul_mem hmem (inv_mem htB)) hsq

end TitsSystem

end CFSG.AGLEmbeddingD2.McLaughlin.Lie
