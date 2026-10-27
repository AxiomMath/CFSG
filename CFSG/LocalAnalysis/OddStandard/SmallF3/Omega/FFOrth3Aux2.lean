module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFTransLayerAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem isPGroup_prod {A B : Type} [Group A] [Group B] [Finite A] [Finite B] {p : ℕ}
    (hA : IsPGroup p A) (hB : IsPGroup p B) : IsPGroup p (A × B) := by
  obtain ⟨k, hk⟩ := hA.exists_card_dvd_pow
  obtain ⟨l, hl⟩ := hB.exists_card_dvd_pow
  refine IsPGroup.of_card_dvd_pow (n := k + l) ?_
  rw [Nat.card_prod, pow_add]
  exact mul_dvd_mul hk hl

theorem twoPrimeRes_eq_pCore_of_normal_two {R : Type} [Group R] [Finite R]
    (M : Subgroup R) [M.Normal] (h2 : IsPGroup 2 M)
    (h3 : IsPGroup 3 (R ⧸ M)) :
    twoPrimeRes (⊤ : Subgroup R) = CFSG.pCore 2 R := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine le_antisymm ?_ ?_
  ·
    refine (Subgroup.closure_le (K := CFSG.pCore 2 R)).mpr ?_
    rintro g ⟨-, k, hk⟩
    have hgM : g ∈ M := by
      have hdvd : orderOf (QuotientGroup.mk' M g) ∣ 2 ^ k :=
        hk ▸ orderOf_map_dvd (QuotientGroup.mk' M) g
      obtain ⟨j, hj⟩ := h3.exists_orderOf_eq_pow (QuotientGroup.mk' M g)
      rw [hj] at hdvd
      have hj1 : 3 ^ j = 1 :=
        Nat.eq_one_of_dvd_coprimes
          (Nat.coprime_pow_primes j k Nat.prime_three Nat.prime_two (by decide))
          dvd_rfl hdvd
      have hj0 : j = 0 := by
        by_contra hj
        have h3dvd : 3 ∣ 3 ^ j := dvd_pow_self 3 hj
        rw [hj1] at h3dvd
        exact Nat.prime_three.not_dvd_one h3dvd
      have hone : orderOf (QuotientGroup.mk' M g) = 1 := by rw [hj, hj0, pow_zero]
      exact (QuotientGroup.eq_one_iff (N := M) g).mp (orderOf_eq_one_iff.mp hone)
    have hMmem : M ∈ {K : Subgroup R | K.Normal ∧ IsPGroup 2 K} := ⟨inferInstance, h2⟩
    exact le_sSup hMmem hgM
  ·
    intro x hx
    obtain ⟨k, hk⟩ :=
      (CFSG.pCore_isPGroup (p := 2) (G := R)).exists_orderOf_eq_pow ⟨x, hx⟩
    rw [Subgroup.orderOf_mk x hx] at hk
    exact Subgroup.subset_closure ⟨trivial, k, hk⟩

theorem ff_xTwoCore_of_prod_aux {H₁ H₂ : Type} [Group H₁] [Group H₂] [Finite H₁] [Finite H₂]
    (h₁ : ∃ (N : Subgroup H₁) (_ : N.Normal), IsPGroup 2 N ∧
      IsPGroup 3 ↥(twoRes (⊤ : Subgroup (H₁ ⧸ N))))
    (h₂ : ∃ (N : Subgroup H₂) (_ : N.Normal), IsPGroup 2 N ∧
      IsPGroup 3 ↥(twoRes (⊤ : Subgroup (H₂ ⧸ N))))
    {B : Type} [Group B] (f : B →* H₁ × H₂) (hf : Function.Injective f) : XTwoCore B := by
  classical
  haveI : Finite B := Finite.of_injective f hf
  obtain ⟨N₁, hN₁, hp₁, hq₁⟩ := h₁
  obtain ⟨N₂, hN₂, hp₂, hq₂⟩ := h₂
  let g₁ : B →* H₁ ⧸ N₁ :=
    (QuotientGroup.mk' N₁).comp ((MonoidHom.fst H₁ H₂).comp f)
  let g₂ : B →* H₂ ⧸ N₂ :=
    (QuotientGroup.mk' N₂).comp ((MonoidHom.snd H₁ H₂).comp f)
  let gB : B →* (H₁ ⧸ N₁) × (H₂ ⧸ N₂) := g₁.prod g₂
  let N : Subgroup B := (N₁.prod N₂).comap f
  have hNn : N.Normal := by
    haveI := hN₁
    haveI := hN₂
    exact (inferInstance : (N₁.prod N₂).Normal).comap f
  let R : Subgroup B := twoRes (⊤ : Subgroup B)
  let Q₁ : Subgroup (H₁ ⧸ N₁) := twoRes (⊤ : Subgroup (H₁ ⧸ N₁))
  let Q₂ : Subgroup (H₂ ⧸ N₂) := twoRes (⊤ : Subgroup (H₂ ⧸ N₂))
  have hQ : IsPGroup 3 (Q₁.prod Q₂) :=
    (isPGroup_prod hq₁ hq₂).of_equiv (Subgroup.prodEquiv Q₁ Q₂).symm
  have hRle : R ≤ (Q₁.prod Q₂).comap gB := by
    refine (Subgroup.closure_le (K := (Q₁.prod Q₂).comap gB)).mpr ?_
    rintro x ⟨-, hodd⟩
    change gB x ∈ Q₁.prod Q₂
    refine Subgroup.mem_prod.mpr ⟨?_, ?_⟩
    · show g₁ x ∈ Q₁
      exact Subgroup.subset_closure ⟨trivial, hodd.of_dvd_nat (orderOf_map_dvd g₁ x)⟩
    · show g₂ x ∈ Q₂
      exact Subgroup.subset_closure ⟨trivial, hodd.of_dvd_nat (orderOf_map_dvd g₂ x)⟩
  let g : ↥R →* (H₁ ⧸ N₁) × (H₂ ⧸ N₂) := gB.comp R.subtype
  have hker : MonoidHom.ker g = N.subgroupOf R := by
    ext y
    change gB (y : B) = 1 ↔ f (y : B) ∈ N₁.prod N₂
    rw [Subgroup.mem_prod]
    constructor
    · intro h
      have h1 : g₁ (y : B) = 1 := by
        have hc := congrArg (fun z : (H₁ ⧸ N₁) × (H₂ ⧸ N₂) => z.1) h
        simpa [g, gB, MonoidHom.prod_apply] using hc
      have h2 : g₂ (y : B) = 1 := by
        have hc := congrArg (fun z : (H₁ ⧸ N₁) × (H₂ ⧸ N₂) => z.2) h
        simpa [g, gB, MonoidHom.prod_apply] using hc
      exact ⟨(QuotientGroup.eq_one_iff (N := N₁) ((f (y : B)).1)).mp h1,
        (QuotientGroup.eq_one_iff (N := N₂) ((f (y : B)).2)).mp h2⟩
    · rintro ⟨h1, h2⟩
      have h1' : g₁ (y : B) = 1 :=
        (QuotientGroup.eq_one_iff (N := N₁) ((f (y : B)).1)).mpr h1
      have h2' : g₂ (y : B) = 1 :=
        (QuotientGroup.eq_one_iff (N := N₂) ((f (y : B)).2)).mpr h2
      show gB (y : B) = 1
      simp only [gB, MonoidHom.prod_apply, h1', h2']
      rfl
  have hrange_le : (QuotientGroup.kerLift g).range ≤ Q₁.prod Q₂ := by
    rintro z ⟨y, rfl⟩
    exact Quotient.inductionOn' y (fun r => by
      show gB (r : B) ∈ Q₁.prod Q₂
      exact hRle r.2)
  have hdom3 : IsPGroup 3 (↥R ⧸ N.subgroupOf R) := by
    have hrange3 : IsPGroup 3 (QuotientGroup.kerLift g).range := by
      obtain ⟨k, hk⟩ := hQ.exists_card_dvd_pow
      refine IsPGroup.of_card_dvd_pow (n := k) ?_
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hrange_le).toEquiv]
      exact (Subgroup.card_subgroup_dvd_card _).trans hk
    have hdom3' : IsPGroup 3 (↥R ⧸ MonoidHom.ker g) :=
      hrange3.of_equiv (MonoidHom.ofInjective (QuotientGroup.kerLift_injective g)).symm
    exact hdom3'.of_equiv (QuotientGroup.quotientMulEquivOfEq hker)
  have hMn : (N.subgroupOf R).Normal := hNn.comap R.subtype
  have hNp : IsPGroup 2 ↥N := by
    have hprod : IsPGroup 2 ↥(N₁.prod N₂) :=
      (isPGroup_prod hp₁ hp₂).of_equiv (Subgroup.prodEquiv N₁ N₂).symm
    refine hprod.of_injective ?_ ?_
    · refine
        { toFun := fun x => ⟨f (x : B), x.2⟩
          map_one' := by ext <;> simp
          map_mul' := fun a b => by ext <;> simp }
    · intro a b habs
      exact Subtype.ext (hf (Subtype.ext_iff.mp habs))
  have hMp : IsPGroup 2 (N.subgroupOf R) := by
    refine hNp.of_injective ?_ ?_
    · refine
        { toFun := fun x => ⟨((x : ↥R) : B), x.2⟩
          map_one' := by ext <;> rfl
          map_mul' := fun a b => by ext <;> rfl }
    · intro a b habs
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : ↥N => (z : B)) habs
  haveI := hMn
  have habs := twoPrimeRes_eq_pCore_of_normal_two (N.subgroupOf R) hMp hdom3
  change twoPrimeRes R = CFSG.inSubgroup (CFSG.pCore 2) R
  have hEq : twoPrimeRes R = (twoPrimeRes (⊤ : Subgroup ↥R)).map R.subtype := by
    have hmap := ff_map_twoPrimeRes R.subtype R.subtype_injective (⊤ : Subgroup ↥R)
    have htop : (⊤ : Subgroup ↥R).map R.subtype = R := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [htop] at hmap
    exact hmap.symm
  rw [hEq, habs]
  rfl

end CFSG.OddStandard.SmallF3.Omega
