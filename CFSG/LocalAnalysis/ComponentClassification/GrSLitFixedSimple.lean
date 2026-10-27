module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitTypeClosure
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrKernelTools

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

theorem exists_fixed_mul_of_inv_mul_mem {A : Type*} [Group A] [Finite A] (c : MulAut A)
    (hc : ∀ x, c (c x) = x) {N : Subgroup A} (hcN : ∀ n ∈ N, c n ∈ N)
    (hodd : Odd (Nat.card N)) {w : A} (hw : w⁻¹ * c w ∈ N) :
    ∃ n ∈ N, c (w * n) = w * n := by
  classical
  let X := {x : A // w⁻¹ * x ∈ N}
  have hmap : ∀ x : X, w⁻¹ * c x.1 ∈ N := fun x => by
    have h1 := hcN _ x.2
    rw [map_mul, map_inv] at h1
    have h2 := mul_mem hw h1
    rwa [show w⁻¹ * c w * ((c w)⁻¹ * c x.1) = w⁻¹ * c x.1 by group] at h2
  let σ : Equiv.Perm X :=
    { toFun := fun x => ⟨c x.1, hmap x⟩
      invFun := fun x => ⟨c x.1, hmap x⟩
      left_inv := fun x => Subtype.ext (hc x.1)
      right_inv := fun x => Subtype.ext (hc x.1) }
  have hσ : σ ^ 2 ^ 1 = 1 := by
    ext x
    simp [σ, sq, hc]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype X := Fintype.ofFinite X
  have hcard : Fintype.card X = Nat.card N := by
    rw [Fintype.card_eq_nat_card]
    exact Nat.card_congr
      { toFun := fun x => ⟨w⁻¹ * x.1, x.2⟩
        invFun := fun n => ⟨w * n.1, by simp⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun n => Subtype.ext (by simp) }
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1)
    (by rw [hcard]; exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)) hσ
  refine ⟨w⁻¹ * x.1, x.2, ?_⟩
  rw [show w * (w⁻¹ * x.1) = x.1 by group]
  exact congrArg Subtype.val hx

theorem map_pPrimeCore_le_pPrimeCore {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) :
    (pPrimeCore 2 X).map f ≤ pPrimeCore 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_sSup
  refine ⟨Subgroup.Normal.map inferInstance f hf, ?_⟩
  have h1 : Nat.card ((pPrimeCore 2 X).map f) ∣ Nat.card (pPrimeCore 2 X) :=
    card_map_dvd _ _
  exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card

theorem comap_fusionZStar_of_surjective' {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    [Group.IsPerfect X] (f : X →* Y) (hf : Function.Surjective f)
    (hX : IsQuasisimple (X ⧸ pPrimeCore 2 X)) (hY : pPrimeCore 2 Y ≠ ⊤) :
    (Open.fusionZStar Y).comap f = Open.fusionZStar X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOmap := map_pPrimeCore_le_pPrimeCore f hf
  set N₁ := (pPrimeCore 2 Y).comap f with hN₁def
  set π := QuotientGroup.mk' (pPrimeCore 2 X) with hπ
  have hN₁ : N₁ ≤ Open.fusionZStar X := by
    have hn : (N₁.map π).Normal :=
      Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
    have hne : N₁.map π ≠ ⊤ := by
      intro htop
      apply hY
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := hf y
      have hx : π x ∈ N₁.map π := htop ▸ mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      have ho : n⁻¹ * x ∈ pPrimeCore 2 X := by
        rw [← QuotientGroup.eq]
        exact hnx
      have h1 : n * (n⁻¹ * x) ∈ N₁ := mul_mem hn (hOmap (mem_map_of_mem f ho))
      rw [mul_inv_cancel_left] at h1
      exact h1
    have hcen := Quasisimple.normal_le_center_of_ne_top
      (CatalogueBAlternating.quasisimple_iff_native.mp hX) (N₁.map π) hne
    intro n hn'
    rw [GSThmB.OddQuot.mem_fusionZStar_iff]
    intro m
    have h1 := mem_center_iff.mp (hcen (mem_map_of_mem π hn')) (π m)
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact h1.symm
  ext x
  rw [mem_comap]
  constructor
  · intro h
    apply UnbalancedCorr.mem_fusionZStar_of_commutator_mem
    intro y
    apply hN₁
    rw [hN₁def, mem_comap]
    have hinv : (f x)⁻¹ ∈ Open.fusionZStar Y := inv_mem h
    rw [GSThmB.OddQuot.mem_fusionZStar_iff] at hinv
    have h2 := hinv (f y)⁻¹
    rwa [commutatorElement_def, show (f x)⁻¹ * (f y)⁻¹ * (f x)⁻¹⁻¹ * (f y)⁻¹⁻¹ =
      f (x⁻¹ * y⁻¹ * x * y) by simp [map_mul, map_inv]] at h2
  · intro h
    rw [GSThmB.OddQuot.mem_fusionZStar_iff] at h ⊢
    intro m
    obtain ⟨m', rfl⟩ := hf m
    have h1 := hOmap (mem_map_of_mem f (h m'))
    rwa [map_commutatorElement] at h1

theorem nonempty_fusionZStar_equiv_of_surjective' {X Y : Type*} [Group X] [Group Y] [Finite X]
    [Finite Y] [Group.IsPerfect X] (f : X →* Y) (hf : Function.Surjective f)
    (hX : IsQuasisimple (X ⧸ pPrimeCore 2 X)) (hY : pPrimeCore 2 Y ≠ ⊤) :
    Nonempty (X ⧸ Open.fusionZStar X ≃* Y ⧸ Open.fusionZStar Y) := by
  set φ := (QuotientGroup.mk' (Open.fusionZStar Y)).comp f with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hf
  have hφk : Open.fusionZStar X = φ.ker := by
    rw [hφ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      comap_fusionZStar_of_surjective' f hf hX hY]
  exact ⟨QuotientGroup.liftEquiv _ hφs hφk⟩

theorem eq_top_of_sup_center_eq_top {Q : Type*} [Group Q] (hQ : commutator Q = ⊤)
    {H : Subgroup Q} (h : H ⊔ center Q = ⊤) : H = ⊤ := by
  rw [eq_top_iff, ← hQ, commutator_def, commutator_le]
  intro g₁ _ g₂ _
  have h₁ : g₁ ∈ H ⊔ center Q := h ▸ mem_top g₁
  have h₂ : g₂ ∈ H ⊔ center Q := h ▸ mem_top g₂
  obtain ⟨x₁, hx₁, z₁, hz₁, rfl⟩ := mem_sup_of_normal_right.mp h₁
  obtain ⟨x₂, hx₂, z₂, hz₂, rfl⟩ := mem_sup_of_normal_right.mp h₂
  have hc : ⁅x₁ * z₁, x₂ * z₂⁆ = ⁅x₁, x₂⁆ := by
    have e1 := mem_center_iff.mp hz₁
    have e2 := mem_center_iff.mp hz₂
    rw [commutatorElement_def, commutatorElement_def]
    calc x₁ * z₁ * (x₂ * z₂) * (x₁ * z₁)⁻¹ * (x₂ * z₂)⁻¹
        = x₁ * (z₁ * (x₂ * z₂)) * (z₁⁻¹ * x₁⁻¹) * (z₂⁻¹ * x₂⁻¹) := by group
      _ = x₁ * ((x₂ * z₂) * z₁) * (z₁⁻¹ * x₁⁻¹) * (z₂⁻¹ * x₂⁻¹) := by rw [e1]
      _ = x₁ * x₂ * (z₂ * x₁⁻¹) * z₂⁻¹ * x₂⁻¹ := by group
      _ = x₁ * x₂ * (x₁⁻¹ * z₂) * z₂⁻¹ * x₂⁻¹ := by rw [(mem_center_iff.mp hz₂ x₁⁻¹)]
      _ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ := by group
  rw [hc, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx₁ hx₂) (inv_mem hx₁)) (inv_mem hx₂)

theorem index_pPrimeCore_le_of_map_eq_top {A : Type*} [Group A] [Finite A] {T : Subgroup A}
    (hT : T.map (QuotientGroup.mk' (pPrimeCore 2 A)) = ⊤) :
    (pPrimeCore 2 A).index ≤ (pPrimeCore 2 T).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 A) with hπ
  set f : T →* A ⧸ pPrimeCore 2 A := π.comp T.subtype with hf
  have hfs : Function.Surjective f := by
    intro q
    have hq : q ∈ T.map π := hT ▸ mem_top q
    obtain ⟨t, ht, rfl⟩ := hq
    exact ⟨⟨t, ht⟩, rfl⟩
  have hOT : pPrimeCore 2 T ≤ f.ker := by
    have h1 : (pPrimeCore 2 T).map f ≤ pPrimeCore 2 (A ⧸ pPrimeCore 2 A) :=
      map_pPrimeCore_le_pPrimeCore f hfs
    rw [pPrimeCore_quotient_pPrimeCore_eq_bot 2, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
    exact h1
  have hidx : f.ker.index = (pPrimeCore 2 A).index := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hfs, card_top, index_eq_card]
  rw [← hidx]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hOT)

theorem exists_simple_fixed_component_image {A : Type*} [Group A] [Finite A]
    (hA : IsQuasisimple (A ⧸ pPrimeCore 2 A)) (c : MulAut A) (hc : ∀ x, c (c x) = x)
    {T : Subgroup A} (hTC : T ≤ fixedSubgroup c)
    (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup c)))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 A).index) :
    ∃ σ : MulAut ((A ⧸ pPrimeCore 2 A) ⧸ center (A ⧸ pPrimeCore 2 A)),
      (∀ x : A,
        σ ((QuotientGroup.mk' (center (A ⧸ pPrimeCore 2 A)))
            ((QuotientGroup.mk' (pPrimeCore 2 A)) x)) =
          (QuotientGroup.mk' (center (A ⧸ pPrimeCore 2 A)))
            ((QuotientGroup.mk' (pPrimeCore 2 A)) (c x))) ∧
      (∀ y, σ (σ y) = y) ∧
      (T.map (QuotientGroup.mk' (pPrimeCore 2 A))).map
          (QuotientGroup.mk' (center (A ⧸ pPrimeCore 2 A))) ≤ fixedSubgroup σ ∧
      IsPComponent 2 (((T.map (QuotientGroup.mk' (pPrimeCore 2 A))).map
          (QuotientGroup.mk' (center (A ⧸ pPrimeCore 2 A)))).subgroupOf (fixedSubgroup σ)) ∧
      (T.map (QuotientGroup.mk' (pPrimeCore 2 A))).map
          (QuotientGroup.mk' (center (A ⧸ pPrimeCore 2 A))) ≠ ⊤ ∧
      Nonempty (T ⧸ Open.fusionZStar T ≃*
        ↥((T.map (QuotientGroup.mk' (pPrimeCore 2 A))).map
          (QuotientGroup.mk' (center (A ⧸ pPrimeCore 2 A)))) ⧸
        Open.fusionZStar ↥((T.map (QuotientGroup.mk' (pPrimeCore 2 A))).map
          (QuotientGroup.mk' (center (A ⧸ pPrimeCore 2 A))))) := by
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
      have hw : w⁻¹ * c w ∈ O := by
        have := (QuotientGroup.eq (s := O)).mp hy'.symm
        exact this
      obtain ⟨n, hn, hfixed⟩ := exists_fixed_mul_of_inv_mul_mem c hc hcO hOodd hw
      refine ⟨w * n, hfixed, ?_⟩
      have h1 : π n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [map_mul, h1, mul_one]
  set Z := center (A ⧸ O) with hZ
  set π₂ := QuotientGroup.mk' Z with hπ₂
  have hZmap : Z.map cbar.toMonoidHom = Z :=
    Subgroup.characteristic_iff_map_eq.mp inferInstance cbar
  set σ : MulAut ((A ⧸ O) ⧸ Z) := QuotientGroup.congr Z Z cbar hZmap with hσdef
  have hσ : ∀ y, σ (π₂ y) = π₂ (cbar y) := fun y => rfl
  have hσ2 : ∀ q, σ (σ q) = q := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z q
    rw [hσ, hσ, hcbar2]
  set F := fixedSubgroup σ with hFdef
  set I := Cbar.map π₂ with hIdef
  have hIF : I ≤ F := by
    rintro _ ⟨y, hy, rfl⟩
    change σ (π₂ y) = π₂ y
    rw [hσ]
    exact congrArg π₂ hy
  have hInormal : (I.subgroupOf F).Normal :=
    LocalAnalysis.ComponentInitial.fixedImage_normal (π := π₂) (a := cbar) (α := σ)
      (by rw [hπ₂, QuotientGroup.ker_mk']) (QuotientGroup.mk'_surjective Z) hcbar2 hσ
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
  set P := Tbar.map π₂ with hPdef
  have hPI : P ≤ I := map_mono hTbarC
  let r₂ : Cbar →* I := (π₂.comp Cbar.subtype).codRestrict I fun y => mem_map_of_mem π₂ y.2
  have hr₂s : Function.Surjective r₂ := by
    rintro ⟨q, hq⟩
    obtain ⟨y, hy, rfl⟩ := hq
    exact ⟨⟨y, hy⟩, rfl⟩
  have hr₂k : r₂.ker ≤ center Cbar := by
    intro y hy
    have h1 : r₂ y = 1 := hy
    have h2 : (y : A ⧸ O) ∈ Z := (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h1)
    rw [mem_center_iff]
    intro w
    exact Subtype.ext (mem_center_iff.mp h2 w)
  have hPI' : IsPComponent 2 (P.subgroupOf I) := by
    have h1 := CatalogueBCentralQuotient.pComponent_map 2 r₂ hr₂s hr₂k _ hTbar
    have h2 : (Tbar.subgroupOf Cbar).map r₂ = P.subgroupOf I := by
      ext q
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · intro hq
        obtain ⟨y, hy, hyq⟩ := mem_subgroupOf.mp hq
        exact ⟨⟨y, hTbarC hy⟩, hy, Subtype.ext hyq⟩
    rwa [h2] at h1
  have hPF : P ≤ F := hPI.trans hIF
  have hP : IsPComponent 2 (P.subgroupOf F) := by
    have h1 := (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := P) hIF 2
      Nat.prime_two).mpr hPI'
    exact (CatalogueBPrimeJoin.pComponent_subnormal_overgroup_iff 2 (P.subgroupOf F)
      (I.subgroupOf F) (fun x hx => hPI hx) hInormal.isSubnormal).mp h1
  have hPne : P ≠ ⊤ := by
    intro htop
    have hsup : Tbar ⊔ Z = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : π₂ y ∈ P := htop ▸ mem_top _
      obtain ⟨t, ht, hty⟩ := hy
      have hz : t⁻¹ * y ∈ Z := (QuotientGroup.eq (s := Z)).mp hty
      have : y = t * (t⁻¹ * y) := by group
      rw [this]
      exact mul_mem (mem_sup_left ht) (mem_sup_right hz)
    have hT' : Tbar = ⊤ := eq_top_of_sup_center_eq_top hA.1.commutator_eq_top hsup
    exact absurd (index_pPrimeCore_le_of_map_eq_top hT') (not_le.mpr hlt)
  obtain ⟨-, -, hTq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 T C hTC).mp hT
  obtain ⟨-, -, hPq⟩ := (CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 P F hPF).mp hP
  have hTperf : Group.IsPerfect T := by
    have h := CatalogueBHeldSmallCore.pComponent_perfect 2 _ hT
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hTC).toMonoidHom)
      (subgroupOfEquivOfLe hTC).surjective
  have hPO : pPrimeCore 2 P ≠ ⊤ := by
    intro htop
    obtain ⟨-, hs, -⟩ := hPq
    have hsub : Subsingleton (P ⧸ pPrimeCore 2 P) := QuotientGroup.subsingleton_iff.mpr htop
    have : Nontrivial ((P ⧸ pPrimeCore 2 P) ⧸ center (P ⧸ pPrimeCore 2 P)) := hs.toNontrivial
    have : Subsingleton ((P ⧸ pPrimeCore 2 P) ⧸ center (P ⧸ pPrimeCore 2 P)) := by
      constructor
      intro x y
      obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
      rw [Subsingleton.elim x' y']
    exact false_of_nontrivial_of_subsingleton ((P ⧸ pPrimeCore 2 P) ⧸ center (P ⧸ pPrimeCore 2 P))
  let f : T →* P := ((π₂.comp π).comp T.subtype).codRestrict P fun t =>
    mem_map_of_mem π₂ (mem_map_of_mem π t.2)
  have hf : Function.Surjective f := by
    rintro ⟨q, hq⟩
    obtain ⟨y, hy, rfl⟩ := hq
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨⟨t, ht⟩, rfl⟩
  refine ⟨σ, ?_, hσ2, hPF, hP, hPne,
    nonempty_fusionZStar_equiv_of_surjective' f hf hTq hPO⟩
  intro x
  rw [hσ, hcbar]

theorem exists_simple_fixed_component {A : Type*} [Group A] [Finite A]
    (hA : IsQuasisimple (A ⧸ pPrimeCore 2 A)) (c : MulAut A) (hc : ∀ x, c (c x) = x)
    {T : Subgroup A} (hTC : T ≤ fixedSubgroup c)
    (hT : IsPComponent 2 (T.subgroupOf (fixedSubgroup c)))
    (hlt : (pPrimeCore 2 T).index < (pPrimeCore 2 A).index) :
    ∃ (σ : MulAut ((A ⧸ pPrimeCore 2 A) ⧸ center (A ⧸ pPrimeCore 2 A)))
      (P : Subgroup ((A ⧸ pPrimeCore 2 A) ⧸ center (A ⧸ pPrimeCore 2 A))),
      (∀ y, σ (σ y) = y) ∧ P ≤ fixedSubgroup σ ∧ IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) ∧
        P ≠ ⊤ ∧ Nonempty (T ⧸ Open.fusionZStar T ≃* P ⧸ Open.fusionZStar P) := by
  obtain ⟨σ, -, hσ, hPF, hP, hPne, he⟩ := exists_simple_fixed_component_image hA c hc hTC hT hlt
  exact ⟨σ, _, hσ, hPF, hP, hPne, he⟩

theorem nonempty_quotient_center_equiv_fusionZStar (A : Type*) [Group A] :
    Nonempty ((A ⧸ pPrimeCore 2 A) ⧸ center (A ⧸ pPrimeCore 2 A) ≃* A ⧸ Open.fusionZStar A) := by
  have hO := UnbalancingLocal.fusionOddCore_eq_pPrimeCore A
  let e₁ : A ⧸ Open.fusionOddCore A ≃* A ⧸ pPrimeCore 2 A := QuotientGroup.quotientMulEquivOfEq hO
  have hc : (center (A ⧸ pPrimeCore 2 A)).map e₁.symm.toMonoidHom =
      center (A ⧸ Open.fusionOddCore A) := by
    ext y
    rw [mem_map_equiv, MulEquiv.symm_symm, mem_center_iff, mem_center_iff]
    constructor
    · intro h z
      apply e₁.injective
      rw [map_mul, map_mul, h (e₁ z)]
    · intro h z
      obtain ⟨z', rfl⟩ := e₁.surjective z
      rw [← map_mul, ← map_mul, h z']
  let e₂ := QuotientGroup.congr _ _ e₁.symm hc
  have hle : Open.fusionOddCore A ≤ Open.fusionZStar A := fun x hx => by
    change QuotientGroup.mk' (Open.fusionOddCore A) x ∈ center (A ⧸ Open.fusionOddCore A)
    have h1 : QuotientGroup.mk' (Open.fusionOddCore A) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact one_mem _
  have hmap : (Open.fusionZStar A).map (QuotientGroup.mk' (Open.fusionOddCore A)) =
      center (A ⧸ Open.fusionOddCore A) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact ⟨e₂.trans ((QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient _ _ hle))⟩

@[expose] def SimpleFixedComponents (τ ρ : ∀ (K : Type) [Group K], Prop) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ x y : S, x * y ≠ y * x) → τ S →
    ∀ σ : MulAut S, (∀ y, σ (σ y) = y) → ∀ P : Subgroup S, P ≤ fixedSubgroup σ →
      IsPComponent 2 (P.subgroupOf (fixedSubgroup σ)) → P ≠ ⊤ → ρ (P ⧸ Open.fusionZStar P)

theorem properFixedComponents_of_simple {τ ρ : ∀ (K : Type) [Group K], Prop}
    (hτ : ∀ (K K' : Type) [Group K] [Group K'], (K ≃* K') → τ K' → τ K)
    (hρ : ∀ (K K' : Type) [Group K] [Group K'], (K ≃* K') → ρ K' → ρ K)
    (h : SimpleFixedComponents τ ρ) : ProperFixedComponents τ ρ := by
  intro G _ _ a b M T ha hb hab hMb hMp hMa hTM hTp hlt hτM
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have haN : a ∈ normalizer (M : Set G) := by
    rw [mem_normalizer_iff]
    intro y
    rw [← UnbalancedLayer.mem_conjugate_iff, hMa]
  set c : MulAut M := M.normalizerMonoidHom ⟨a, haN⟩ with hcdef
  have hcapp : ∀ x : M, ((c x : M) : G) = a * x * a⁻¹ := fun x => rfl
  have hc : ∀ x, c (c x) = x := by
    intro x
    apply Subtype.ext
    rw [hcapp, hcapp]
    calc a * (a * (x : G) * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [haa]; group
  have hfixC : fixedSubgroup c = (M ⊓ centralizer ({a} : Set G)).subgroupOf M := by
    ext x
    rw [LocalAnalysis.ComponentInitial.mem_fixedSubgroup_iff, mem_subgroupOf, mem_inf,
      mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have h1 := congrArg Subtype.val hx
      rw [hcapp] at h1
      refine ⟨x.2, ?_⟩
      calc (x : G) * a = a * x * a⁻¹ * a := by rw [h1]
        _ = a * x := by group
    · rintro ⟨-, hx⟩
      apply Subtype.ext
      rw [hcapp]
      calc a * (x : G) * a⁻¹ = x * a * a⁻¹ := by rw [hx]
        _ = x := by group
  set T' := T.subgroupOf M with hT'def
  have hTM' : T ≤ M := hTM.trans inf_le_left
  have hT'C : T' ≤ fixedSubgroup c := by
    rw [hfixC]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact hTM hx
  have hT'p : IsPComponent 2 (T'.subgroupOf (fixedSubgroup c)) := by
    rw [hfixC]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' (L := T) inf_le_left 2
      Nat.prime_two).mpr hTp
  let eT : T ≃* T' := (subgroupOfEquivOfLe hTM').symm
  have hlt' : (pPrimeCore 2 T').index < (pPrimeCore 2 M).index := by
    rw [index_eq_card, index_eq_card,
      ← UnbalancingLocal.Correspondence.card_quotient_pPrimeCore_congr eT, ← index_eq_card,
      ← index_eq_card]
    exact hlt
  have hMq : IsQuasisimple (M ⧸ pPrimeCore 2 M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMb).1 hMp).2.2
  obtain ⟨σ, P, hσ, hPF, hP, hPne, ⟨e⟩⟩ := exists_simple_fixed_component hMq c hc hT'C hT'p hlt'
  obtain ⟨eS⟩ := nonempty_quotient_center_equiv_fusionZStar M
  obtain ⟨-, hS, hnab⟩ := hMq
  have hρP := h _ hS hnab (hτ _ _ eS hτM) σ hσ P hPF hP hPne
  obtain ⟨eZ⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective eT.toMonoidHom
    eT.surjective (by
      rw [show eT.toMonoidHom.ker = ⊥ from (MonoidHom.ker_eq_bot_iff _).mpr eT.injective,
        card_bot]
      norm_num)
  exact hρ _ _ (eZ.trans e) hρP

end CFSG.ComponentClassification.GrSLit
