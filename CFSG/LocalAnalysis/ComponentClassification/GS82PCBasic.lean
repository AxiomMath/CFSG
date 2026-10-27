module

public import CFSG.LocalAnalysis.ComponentClassification.GS82ResidueDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedSimple
public import CFSG.LocalAnalysis.ComponentClassification.Sol78Basic
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.ComponentClassification.GS82PumpInputs

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem typC_of_coreEquiv {A B : Type} [Group A] [Group B]
    (e : A ⧸ pPrimeCore 2 A ≃* B ⧸ pPrimeCore 2 B) (h : TypC A) : TypC B := by
  rcases h with ⟨t, n, p, f, hp, hp2, hadm, hm⟩ | ⟨n, hn, hq, hc, ⟨f⟩⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨t, n, p, f, hp, hp2, hadm,
      Blueprint.LieModel.of_mulEquiv (Sol78.fusionZStarQuotOfCore e) hm⟩
  · refine Or.inr (Or.inl ⟨n, hn, LocalCores.isQuasisimple_of_mulEquiv e hq, ?_,
      ⟨(Sol78.centerQuotCongr e).symm.trans f⟩⟩)
    rw [← Sol78.map_center_eq_of_mulEquiv e, Subgroup.card_map_of_injective e.injective]
    exact hc
  · exact Or.inr (Or.inr ⟨Blueprint.LieModel.of_mulEquiv (Sol78.centerQuotCongr e) h1,
      fun h => h2 (IsElementaryAbelian.of_mulEquiv (Subgroup.centerCongr e).symm h)⟩)

theorem center_ne_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : center A ≠ ⊥) : center B ≠ ⊥ := by
  intro hB
  apply h
  rw [← Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) (center A) e.injective,
    Sol78.map_center_eq_of_mulEquiv e, hB]

theorem exists_coreQuotient_fixed_component {A : Type*} [Group A] [Finite A] (c : MulAut A)
    (hc : ∀ x, c (c x) = x) {T : Subgroup A} (hTC : T ≤ fixedSubgroup c)
    (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup c))) :
    ∃ cbar : MulAut (A ⧸ pPrimeCore 2 A), (∀ y, cbar (cbar y) = y) ∧
      T.map (QuotientGroup.mk' (pPrimeCore 2 A)) ≤ fixedSubgroup cbar ∧
      IsPComponent 2 ((T.map (QuotientGroup.mk' (pPrimeCore 2 A))).subgroupOf
        (fixedSubgroup cbar)) ∧
      Nonempty (↥T ⧸ pPrimeCore 2 ↥T ≃*
        ↥(T.map (QuotientGroup.mk' (pPrimeCore 2 A))) ⧸
          pPrimeCore 2 ↥(T.map (QuotientGroup.mk' (pPrimeCore 2 A)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := pPrimeCore 2 A with hO
  set π := QuotientGroup.mk' O with hπ
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hOmap : O.map c.toMonoidHom = O :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance c
  have hcO : ∀ n ∈ O, c n ∈ O := fun n hn => hOmap ▸ mem_map_of_mem c.toMonoidHom hn
  set cbar : MulAut (A ⧸ O) := QuotientGroup.congr O O c hOmap with hcbardef
  have hcbar : ∀ x, cbar (π x) = π (c x) := fun x => rfl
  have hcbar2 : ∀ y, cbar (cbar y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [hcbar, hcbar, hc]
  set C := fixedSubgroup c with hCdef
  set Cbar := fixedSubgroup cbar with hCbardef
  have hfix : C.map π = Cbar := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change cbar (π x) = π x
      rw [hcbar]
      exact congrArg π hx
    · intro y hy
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective O y
      have hy' : π (c w) = π w := (hcbar w).symm.trans hy
      have hw : w⁻¹ * c w ∈ O := (QuotientGroup.eq (s := O)).mp hy'.symm
      obtain ⟨n, hn, hfixed⟩ := GrSLit.exists_fixed_mul_of_inv_mul_mem c hc hcO hOodd hw
      refine ⟨w * n, hfixed, ?_⟩
      have h1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [map_mul, h1, mul_one]
  set Tbar := T.map π with hTbardef
  have hTbarC : Tbar ≤ Cbar := by
    rw [← hfix]
    exact map_mono hTC
  let r₁ : C →* Cbar := (π.comp C.subtype).codRestrict Cbar fun x => by
    rw [← hfix]
    exact mem_map_of_mem π x.2
  have hr₁s : Function.Surjective r₁ := by
    rintro ⟨y, hy⟩
    rw [← hfix] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hr₁k : Odd (Nat.card r₁.ker) := by
    let g : r₁.ker →* O := (C.subtype.comp r₁.ker.subtype).codRestrict O fun k => by
      have h1 : r₁ (k : C) = 1 := k.2
      have h2 := congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff _).mp h2
    have hg : Function.Injective g := fun k₁ k₂ h => by
      have h' := congrArg (fun x : O => (x : A)) h
      exact Subtype.ext (Subtype.ext h')
    exact hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)
  have hTbar : IsPComponent 2 (Tbar.subgroupOf Cbar) := by
    have h1 := OddKernelTwoComponents.image r₁ hr₁s hr₁k (T.subgroupOf C)
      ((CatalogueBAlternating.pComponent_two_iff _).mp hT)
    have h2 : (T.subgroupOf C).map r₁ = Tbar.subgroupOf Cbar := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · intro hy
        obtain ⟨x, hx, hxy⟩ := mem_subgroupOf.mp hy
        exact ⟨⟨x, hTC hx⟩, hx, Subtype.ext hxy⟩
    rw [← h2]
    exact (CatalogueBAlternating.pComponent_two_iff _).mpr h1
  let f : T →* Tbar := (π.comp T.subtype).codRestrict Tbar fun t => mem_map_of_mem π t.2
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨⟨t, ht⟩, rfl⟩
  have hfk : ¬ 2 ∣ Nat.card f.ker := by
    let g : f.ker →* O := (T.subtype.comp f.ker.subtype).codRestrict O fun k => by
      have h1 : f (k : T) = 1 := k.2
      have h2 := congrArg Subtype.val h1
      exact (QuotientGroup.eq_one_iff _).mp h2
    have hg : Function.Injective g := fun k₁ k₂ h => by
      have h' := congrArg (fun x : O => (x : A)) h
      exact Subtype.ext (Subtype.ext h')
    exact (hOodd.of_dvd_nat (Subgroup.card_dvd_of_injective g hg)).not_two_dvd_nat
  have hcore := (prime_complement_kernel_core_preimage (p := 2) f hf hfk).1
  set φ := (QuotientGroup.mk' (pPrimeCore 2 Tbar)).comp f with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hφk : pPrimeCore 2 T = φ.ker := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcore]
  exact ⟨cbar, hcbar2, hTbarC, hTbar, ⟨QuotientGroup.liftEquiv _ hφs hφk⟩⟩

end CFSG.ComponentClassification.GS82PumpInputs
