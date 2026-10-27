module

public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.SolvablePrimeCoreLayerLift
public import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped Pointwise

@[expose] def actionFixedSubgroup {A X : Type*} [Group A] [Group X] (α : A →* MulAut X) :
    Subgroup X where
  carrier := {x | ∀ a, α a x = x}
  mul_mem' hx hy a := by rw [map_mul, hx a, hy a]
  one_mem' a := map_one (α a)
  inv_mem' hx a := by rw [map_inv, hx a]

theorem mem_actionFixedSubgroup {A X : Type*} [Group A] [Group X] (α : A →* MulAut X) (x : X) :
    x ∈ actionFixedSubgroup α ↔ ∀ a, α a x = x :=
  Iff.rfl

theorem primeResidual_eq_top_of_eq_closure {G : Type*} [Group G] [Finite G] (p : ℕ)
    [Fact p.Prime] {V : Subgroup G}
    (hV : V = closure {x : G | x ∈ V ∧ ∃ k : ℕ, orderOf x = p ^ k}) :
    CatalogueBPrimeJoin.primeResidual p V = ⊤ := by
  rw [CatalogueBPrimeJoin.closure_pElements_eq_map_primeResidual] at hV
  apply map_injective V.subtype_injective
  rw [← hV, ← MonoidHom.range_eq_map, range_subtype]

theorem core_trivial_fixed_layer_normal_generation {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (N : Subgroup X) [N.Normal] (hN : ¬ p ∣ Nat.card N)
    {A : Type*} [Group A] [Finite A] (hA : IsPGroup p A) (α : A →* MulAut X)
    (hαQ : ∀ (a : A) (x : X), ((α a x : X) : X ⧸ N) = (x : X ⧸ N))
    (hEQ : pLayer (X ⧸ N) p = ⊤) (V : Subgroup X)
    (hV : V = (pLayer (actionFixedSubgroup α) p).map (actionFixedSubgroup α).subtype) :
    V.map (QuotientGroup.mk' N) = ⊤ ∧
    ((actionFixedSubgroup α : Subgroup X) : Set X) =
      (V : Set X) * ((actionFixedSubgroup α ⊓ N : Subgroup X) : Set X) ∧
    V = closure {x : X | x ∈ actionFixedSubgroup α ∧ ∃ k : ℕ, orderOf x = p ^ k} ∧
    (∀ W : Subgroup X, W ≤ actionFixedSubgroup α →
      W = closure {x : X | x ∈ W ∧ ∃ k : ℕ, orderOf x = p ^ k} →
      normalClosure ((W.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)) = ⊤ →
      W ≤ V ∧ normalClosure ((W.subgroupOf V : Subgroup V) : Set V) = ⊤) ∧
    ∃ e : V ⧸ pPrimeCore p V ≃* (X ⧸ N) ⧸ pPrimeCore p (X ⧸ N),
      ∀ v : V, e (v : V ⧸ pPrimeCore p V) =
        (((v : X) : X ⧸ N) : (X ⧸ N) ⧸ pPrimeCore p (X ⧸ N)) := by
  have : Fact p.Prime := ⟨hp⟩
  set C := actionFixedSubgroup α with hCdef
  set π := QuotientGroup.mk' N with hπdef
  have hαN : ∀ a : A, ∀ n ∈ N, α a n ∈ N := by
    intro a n hn
    have h := hαQ a n
    rw [(QuotientGroup.eq_one_iff n).mpr hn, QuotientGroup.eq_one_iff] at h
    exact h
  have hcopN : p.Coprime (Nat.card π.ker) := by
    rw [hπdef, QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hN
  have hCsurj : Function.Surjective (π.domRestrict C) := by
    have hlift := Semidihedral.Principal.coprime_fixed_point_lifting p hA α N hαN hN
    intro q
    have hq : q ∈ {q : X ⧸ N | ∀ a : A,
        Semidihedral.Principal.CoprimeFixedPoint.quotientAction α N hαN a q = q} := by
      intro a
      induction q using QuotientGroup.induction_on with | H x => ?_
      rw [Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk]
      exact hαQ a x
    rw [hlift] at hq
    obtain ⟨c, hc, hcq⟩ := hq
    exact ⟨⟨c, hc⟩, hcq⟩
  have hkerC : p.Coprime (Nat.card (π.domRestrict C).ker) :=
    CatalogueBPrimeJoin.coprime_card_restriction_kernel p π hcopN C
  have hkerC' : ¬ p ∣ Nat.card (π.domRestrict C).ker :=
    (Nat.Prime.coprime_iff_not_dvd hp).mp hkerC
  obtain ⟨hbij, -, -⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection (π.domRestrict C)
      hCsurj hkerC'
  have hlayermap : (pLayer C p).map (π.domRestrict C) = ⊤ := by
    unfold pLayer
    rw [(gc_map_comap (π.domRestrict C)).l_sSup_eq_sSup_image]
    change sSup ((fun L : Subgroup C => L.map (π.domRestrict C)) '' {L | IsPComponent p L}) = ⊤
    rw [hbij.image_eq]
    exact hEQ
  have hVmap : V.map π = ⊤ := by
    rw [hV, map_map]
    exact hlayermap
  have hVC : V ≤ C := by
    rw [hV]
    exact map_subtype_le _
  have hCprod : (C : Set X) = (V : Set X) * ((C ⊓ N : Subgroup X) : Set X) := by
    ext c
    constructor
    · intro hc
      have hmem : π c ∈ V.map π := by rw [hVmap]; exact mem_top _
      obtain ⟨v, hv, hvc⟩ := mem_map.mp hmem
      refine Set.mem_mul.mpr ⟨v, hv, v⁻¹ * c, ?_, mul_inv_cancel_left v c⟩
      refine mem_inf.mpr ⟨mul_mem (inv_mem (hVC hv)) hc, ?_⟩
      rw [← QuotientGroup.eq]
      exact hvc
    · intro hc
      obtain ⟨v, hv, n, hn, rfl⟩ := Set.mem_mul.mp hc
      exact mul_mem (hVC hv) (mem_inf.mp hn).1
  have hcover : Function.Surjective ((π.domRestrict C).domRestrict (pLayer C p)) := by
    intro q
    have hmem : q ∈ (pLayer C p).map (π.domRestrict C) := by rw [hlayermap]; exact mem_top _
    obtain ⟨c, hc, hcq⟩ := mem_map.mp hmem
    exact ⟨⟨c, hc⟩, hcq⟩
  have hindex : p.Coprime (pLayer C p).index :=
    CatalogueBPrimeJoin.coprime_index_of_surjective_restriction p (π.domRestrict C) hCsurj
      hkerC (pLayer C p) hcover
  have hlayerChar : (pLayer C p).Characteristic := CatalogueBPrimeJoin.pLayer_characteristic
  have hres_le : CatalogueBPrimeJoin.primeResidual p C ≤ pLayer C p :=
    CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index p (pLayer C p) hindex
  have hle_res : pLayer C p ≤ CatalogueBPrimeJoin.primeResidual p C := by
    apply sSup_le
    intro L hL
    have htop := CatalogueBPrimeJoin.primeResidual_eq_top_of_pComponent p L hL
    have hmap := CatalogueBPrimeJoin.primeResidual_map_le p L.subtype
    rw [htop, ← MonoidHom.range_eq_map, range_subtype] at hmap
    exact hmap
  have hlayer_eq : pLayer C p = CatalogueBPrimeJoin.primeResidual p C :=
    le_antisymm hle_res hres_le
  have hVgen : V = closure {x : X | x ∈ C ∧ ∃ k : ℕ, orderOf x = p ^ k} := by
    rw [hV, hlayer_eq, CatalogueBPrimeJoin.closure_pElements_eq_map_primeResidual]
  have hVgen' : V = closure {x : X | x ∈ V ∧ ∃ k : ℕ, orderOf x = p ^ k} := by
    have hset : {x : X | x ∈ V ∧ ∃ k : ℕ, orderOf x = p ^ k} =
        {x : X | x ∈ C ∧ ∃ k : ℕ, orderOf x = p ^ k} := by
      ext x
      constructor
      · rintro ⟨hx, hk⟩
        exact ⟨hVC hx, hk⟩
      · rintro ⟨hx, hk⟩
        refine ⟨?_, hk⟩
        rw [hVgen]
        exact subset_closure ⟨hx, hk⟩
    rw [hset]
    exact hVgen
  have hVres : CatalogueBPrimeJoin.primeResidual p V = ⊤ :=
    primeResidual_eq_top_of_eq_closure p hVgen'
  have hVsurj : Function.Surjective (π.domRestrict V) := by
    intro q
    have hmem : q ∈ V.map π := by rw [hVmap]; exact mem_top _
    obtain ⟨v, hv, hvq⟩ := mem_map.mp hmem
    exact ⟨⟨v, hv⟩, hvq⟩
  have hkerV : p.Coprime (Nat.card (π.domRestrict V).ker) :=
    CatalogueBPrimeJoin.coprime_card_restriction_kernel p π hcopN V
  refine ⟨hVmap, hCprod, hVgen, ?_, ?_⟩
  · intro W hWC hWgen hWnormal
    have hWV : W ≤ V := by
      rw [hWgen, hVgen]
      apply Subgroup.closure_mono
      rintro x ⟨hx, hk⟩
      exact ⟨hWC hx, hk⟩
    refine ⟨hWV, ?_⟩
    set R : Subgroup V := normalClosure ((W.subgroupOf V : Subgroup V) : Set V) with hRdef
    have hRnormal : R.Normal := normalClosure_normal
    have hRmap : R.map (π.domRestrict V) = ⊤ := by
      have hn : (R.map (π.domRestrict V)).Normal := hRnormal.map _ hVsurj
      apply top_unique
      rw [← hWnormal]
      apply normalClosure_le_normal
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨⟨w, hWV hw⟩, subset_normalClosure (show (⟨w, hWV hw⟩ : V) ∈ W.subgroupOf V from hw),
        rfl⟩
    have hRcover : Function.Surjective ((π.domRestrict V).domRestrict R) := by
      intro q
      have hmem : q ∈ R.map (π.domRestrict V) := by rw [hRmap]; exact mem_top _
      obtain ⟨r, hr, hrq⟩ := mem_map.mp hmem
      exact ⟨⟨r, hr⟩, hrq⟩
    have hRindex : p.Coprime R.index :=
      CatalogueBPrimeJoin.coprime_index_of_surjective_restriction p (π.domRestrict V) hVsurj
        hkerV R hRcover
    have hle := CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index p R hRindex
    rw [hVres] at hle
    exact top_unique hle
  · have hkerV' : ¬ p ∣ Nat.card (π.domRestrict V).ker :=
      (Nat.Prime.coprime_iff_not_dvd hp).mp hkerV
    obtain ⟨hcomap, -⟩ := prime_complement_kernel_core_preimage (π.domRestrict V) hVsurj hkerV'
    have hφ : Function.Surjective
        ((QuotientGroup.mk' (pPrimeCore p (X ⧸ N))).comp (π.domRestrict V)) :=
      (QuotientGroup.mk'_surjective _).comp hVsurj
    have hφker : pPrimeCore p V =
        ((QuotientGroup.mk' (pPrimeCore p (X ⧸ N))).comp (π.domRestrict V)).ker := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
    exact ⟨QuotientGroup.liftEquiv _ hφ hφker, fun v => rfl⟩

end CFSG.ComponentClassification.UnbalancedGS
