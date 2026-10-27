module

public import CFSG.LocalAnalysis.EvenBN.Sp4.BothTrivialClosuresLayer
import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearSplit
import CFSG.LieType.Steinberg.CentralExt.SL2CentrallyClosed
import CFSG.LocalAnalysis.EvenBN.Common.SL2TorusFour
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.LocalAnalysis.EvenBN.GMS.NormalForms
import CFSG.Assembly.ComponentFreeOddCores

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace BothTrivialLayer

open Subgroup CFSG.Blueprint
open scoped MatrixGroups

theorem eq_one_of_isPerfect {G M : Type*} [Group G] [Group.IsPerfect G] [Group M]
    (hM : ∀ a b : M, a * b = b * a) (f : G →* M) (x : G) : f x = 1 := by
  let _ : CommGroup M := { (inferInstance : Group M) with mul_comm := hM }
  have h : commutator G ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [Group.IsPerfect.commutator_eq_top (G := G)] at h
  exact h (mem_top x)

theorem isPerfect_sl2 {k : Type} [Field k] [Fintype k] {n : ℕ} (hn : 2 ≤ n)
    (hk : Fintype.card k = 2 ^ n) : Group.IsPerfect SL(2, k) := by
  have : IsSimpleGroup SL(2, k) := GMSK.sl2_isSimpleGroup (GMSK.two_eq_zero_of_card (by omega) hk)
    (by rw [hk]; calc 4 = 2 ^ 2 := rfl
                    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
  exact ⟨CFSG.Assembly.Dichotomy.commutator_eq_top_of_isSimpleGroup GMSK.sl2_exists_mul_ne⟩

theorem exists_section_prod
    {X : Type*} [Group X] [Finite X] {k : Type} [Field k]
    [Fintype k] {n : ℕ} (hn : 2 ≤ n) (hk : Fintype.card k = 2 ^ n)
    {π : X →* SL(2, k) × SL(2, k)} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ center X) (hodd : Odd (Nat.card π.ker)) :
    ∃ s : SL(2, k) × SL(2, k) →* X, ∀ g, π (s g) = g := by
  have hk' : Nat.card k = 2 ^ n := by rw [Nat.card_eq_fintype_card, hk]
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hk'
  have := isPerfect_sl2 hn hk
  have key : ∀ (ι : SL(2, k) →* SL(2, k) × SL(2, k)) (pr : SL(2, k) × SL(2, k) →* SL(2, k)),
      (∀ a, pr (ι a) = a) → (∀ g, g ∈ ι.range → ι (pr g) = g) →
      ∃ s : SL(2, k) →* X, ∀ a, π (s a) = ι a := by
    intro ι pr hpr hιpr
    set X₁ : Subgroup X := ι.range.comap π with hX₁
    let π₁ : X₁ →* SL(2, k) := pr.comp (π.comp X₁.subtype)
    have hπ₁ : Function.Surjective π₁ := by
      intro a
      obtain ⟨x, hx⟩ := hπ (ι a)
      exact ⟨⟨x, by rw [hX₁, mem_comap, hx]; exact ⟨a, rfl⟩⟩, by
        simp [π₁, hx, hpr]⟩
    have hπ₁x : ∀ x : X₁, π x = ι (π₁ x) := fun x => (hιpr _ x.2).symm
    have hker : π₁.ker = π.ker.subgroupOf X₁ := by
      ext x
      rw [MonoidHom.mem_ker, mem_subgroupOf, MonoidHom.mem_ker, hπ₁x]
      constructor
      · intro h1; rw [h1, map_one]
      · intro h1
        rw [← hpr (π₁ x), h1, map_one]
    have hcen₁ : π₁.ker ≤ center X₁ := by
      rw [hker]
      intro x hx
      rw [mem_subgroupOf] at hx
      exact mem_center_iff.mpr fun y => Subtype.ext ((mem_center_iff.mp (hcen hx)) y)
    have hodd₁ : Odd (Nat.card π₁.ker) := by
      rw [hker, Nat.card_congr (subgroupOfEquivOfLe fun x hx => by
        rw [hX₁, mem_comap, (MonoidHom.mem_ker).mp hx]; exact one_mem _).toEquiv]
      exact hodd
    obtain ⟨s₁, hs₁, -⟩ := CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting
      (le_refl 2) hπ₁ hcen₁ hodd₁
    refine ⟨X₁.subtype.comp s₁, fun a => ?_⟩
    change π (s₁ a : X) = ι a
    rw [hπ₁x, hs₁]
  obtain ⟨s₁, hs₁⟩ := key (MonoidHom.inl _ _) (MonoidHom.fst _ _) (fun a => rfl)
    (fun g ⟨a, ha⟩ => by rw [← ha]; rfl)
  obtain ⟨s₂, hs₂⟩ := key (MonoidHom.inr _ _) (MonoidHom.snd _ _) (fun a => rfl)
    (fun g ⟨a, ha⟩ => by rw [← ha]; rfl)
  have hcomm : ∀ a b, s₁ a * s₂ b = s₂ b * s₁ a := by
    intro a b
    set y := s₂ b
    have hδ : ∀ a, y * s₁ a * y⁻¹ * (s₁ a)⁻¹ ∈ π.ker := fun a => by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hs₁, hs₂]
      ext <;> simp
    let δ : SL(2, k) →* center X :=
      { toFun := fun a => ⟨y * s₁ a * y⁻¹ * (s₁ a)⁻¹, hcen (hδ a)⟩
        map_one' := by ext; simp
        map_mul' := fun a a' => by
          ext
          simp only [map_mul, coe_mul]
          have hc := mem_center_iff.mp (hcen (hδ a')) (s₁ a)
          calc y * (s₁ a * s₁ a') * y⁻¹ * (s₁ a * s₁ a')⁻¹
              = (y * s₁ a * y⁻¹ * (s₁ a)⁻¹) * (s₁ a * (y * s₁ a' * y⁻¹ * (s₁ a')⁻¹)) *
                (s₁ a)⁻¹ := by group
            _ = (y * s₁ a * y⁻¹ * (s₁ a)⁻¹) * ((y * s₁ a' * y⁻¹ * (s₁ a')⁻¹) * s₁ a) *
                (s₁ a)⁻¹ := by rw [hc]
            _ = _ := by group }
    have h1 := eq_one_of_isPerfect (fun u v => Subtype.ext (mem_center_iff.mp v.2 (u : X))) δ a
    have h2 : y * s₁ a * y⁻¹ * (s₁ a)⁻¹ = 1 := congrArg Subtype.val h1
    calc s₁ a * y = (y * s₁ a * y⁻¹ * (s₁ a)⁻¹)⁻¹ * (y * s₁ a) := by group
      _ = y * s₁ a := by rw [h2, inv_one, one_mul]
  refine ⟨{ toFun := fun g => s₁ g.1 * s₂ g.2
            map_one' := by simp
            map_mul' := fun g g' => by
              simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
              calc s₁ g.1 * s₁ g'.1 * (s₂ g.2 * s₂ g'.2)
                  = s₁ g.1 * (s₁ g'.1 * s₂ g.2) * s₂ g'.2 := by group
                _ = s₁ g.1 * (s₂ g.2 * s₁ g'.1) * s₂ g'.2 := by rw [hcomm]
                _ = _ := by group }, fun g => ?_⟩
  change π (s₁ g.1 * s₂ g.2) = g
  rw [map_mul, hs₁, hs₂]
  ext <;> simp

@[expose] def ExactClosure {M : Type} [Group M] (A : Subgroup M) {k : Type} [Field k]
    (α : A ≃* SL(2, k)) (τ : M) (V : Subgroup M) (n : ℕ) : Prop :=
  normalClosure (A : Set M) ⊓ CFSG.Open.standardComponentOddCore M = ⊥ ∧
    centralizer (normalClosure (A : Set M) : Set M) = CFSG.Open.standardComponentOddCore M ∧
    V ≤ normalClosure (A : Set M) ∧
    (∃ P : Sylow 2 (normalClosure (A : Set M)),
      (P : Subgroup (normalClosure (A : Set M))).map (normalClosure (A : Set M)).subtype = V) ∧
    Xor
      (∃ ψ : normalClosure (A : Set M) ≃* SL(2, k) × SL(2, k),
        (∀ (a : A) (x : normalClosure (A : Set M)), (x : M) = a → ψ x = (α a, α a)) ∧
        ∀ x y : normalClosure (A : Set M), (y : M) = τ⁻¹ * x * τ → ψ y = (ψ x).swap)
      (∃ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 ∧
        ∃ ψ : normalClosure (A : Set M) ≃* SL(2, k₂),
          (∀ x y : normalClosure (A : Set M), (y : M) = τ⁻¹ * x * τ →
            ((ψ y : SL(2, k₂)) : Matrix (Fin 2) (Fin 2) k₂) =
              (ψ x : Matrix (Fin 2) (Fin 2) k₂).map (fun c => c ^ 2 ^ n)) ∧
          ∀ g : SL(2, k₂),
            g ∈ (A.subgroupOf (normalClosure (A : Set M))).map ψ.toMonoidHom ↔
              ∀ i j, (g : Matrix (Fin 2) (Fin 2) k₂) i j ^ 2 ^ n =
                (g : Matrix (Fin 2) (Fin 2) k₂) i j)

theorem injective_of_section {N D E : Type*} [Group N] [Group D] [Group E] [Group.IsPerfect N]
    {f : N →* D} (ψ : D ≃* E) (hker : f.ker ≤ center N) (s : E →* N)
    (hs : ∀ g, ψ (f (s g)) = g) : Function.Injective f := by
  have hk : (ψ.toMonoidHom.comp f).ker = f.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have h := CFSG.LieType.Steinberg.CentralExt.SL2Closed.ker_eq_bot_of_section
    (ψ.toMonoidHom.comp f) (hk ▸ hker) s hs
  rw [hk] at h
  exact (MonoidHom.ker_eq_bot_iff f).mp h

theorem ker_comp_mulEquiv {N D E : Type*} [Group N] [Group D] [Group E] (f : N →* D)
    (ψ : D ≃* E) : (ψ.toMonoidHom.comp f).ker = f.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

theorem extension_split_prod
    {N D : Type*} [Group N] [Finite N] [Group D] {k : Type}
    [Field k] [Fintype k] {n : ℕ} (hn : 2 ≤ n) (hk : Fintype.card k = 2 ^ n)
    (ψ : D ≃* SL(2, k) × SL(2, k)) {f : N →* D} (hf : Function.Surjective f)
    (hker : f.ker ≤ center N) (hodd : Odd (Nat.card f.ker)) :
    ∃ s : SL(2, k) × SL(2, k) →* N, ∀ g, ψ (f (s g)) = g :=
  exists_section_prod hn hk (π := ψ.toMonoidHom.comp f) (ψ.surjective.comp hf)
    (by rw [ker_comp_mulEquiv]; exact hker) (by rw [ker_comp_mulEquiv]; exact hodd)

theorem extension_split_sl2
    {N D : Type*} [Group N] [Finite N] [Group D] {k₂ : Type}
    [Field k₂] [Fintype k₂] {n : ℕ} (hn : 2 ≤ n) (hk₂ : Fintype.card k₂ = (2 ^ n) ^ 2)
    (ψ : D ≃* SL(2, k₂)) {f : N →* D} (hf : Function.Surjective f)
    (hker : f.ker ≤ center N) (hodd : Odd (Nat.card f.ker)) :
    ∃ s : SL(2, k₂) →* N, ∀ g, ψ (f (s g)) = g := by
  have hk₂' : Nat.card k₂ = 2 ^ (2 * n) := by
    rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
  have : CharP k₂ 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hk₂'
  obtain ⟨s, hs, -⟩ := CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting
    (le_refl 2) (π := ψ.toMonoidHom.comp f) (ψ.surjective.comp hf)
    (by rw [ker_comp_mulEquiv]; exact hker) (by rw [ker_comp_mulEquiv]; exact hodd)
  exact ⟨s, hs⟩

theorem exactClosure_of_selection
    {M : Type} [Group M] [Finite M] {A : Subgroup M} {n : ℕ}
    (hn : 2 ≤ n) {k : Type} [Field k] [Fintype k] (hk : Fintype.card k = 2 ^ n)
    (α : A ≃* SL(2, k)) {τ : M} {V : Subgroup M} (hsel : ClosureSelection A α τ V n)
    (hperf : Group.IsPerfect (normalClosure (A : Set M)))
    (hcent : ⁅CFSG.Open.standardComponentOddCore M, normalClosure (A : Set M)⁆ = ⊥)
    (hVcard : Nat.card V = (2 ^ n) ^ 2) (hVA : V ≤ normalClosure (A : Set M)) :
    ExactClosure A α τ V n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk' : Nat.card k = 2 ^ n := by rw [Nat.card_eq_fintype_card, hk]
  have : CharP k 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ n) hk'
  obtain ⟨hC, hL, -, -, halt⟩ := hsel
  set N := normalClosure (A : Set M) with hNdef
  set R := CFSG.Open.standardComponentOddCore M with hRdef
  set π : M →* M ⧸ R := QuotientGroup.mk' R with hπ
  set D := CFSG.layer (M ⧸ R) with hD
  have hfm : ∀ x : N, π x ∈ D := fun x => hL ▸ mem_map_of_mem π x.2
  let f : N →* D := (π.comp N.subtype).codRestrict D hfm
  have hf : ∀ x : N, ((f x : D) : M ⧸ R) = π x := fun _ => rfl
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [hL] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hRN : R ≤ centralizer (N : Set M) := commutator_eq_bot_iff_le_centralizer.mp hcent
  have hker : ∀ x : N, f x = 1 ↔ (x : M) ∈ R := fun x => by
    rw [Subtype.ext_iff, hf]
    exact QuotientGroup.eq_one_iff _
  have hkercen : f.ker ≤ center N := by
    intro x hx
    rw [MonoidHom.mem_ker, hker] at hx
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_centralizer_iff.mp (hRN hx) y y.2)
  have hkerodd : Odd (Nat.card f.ker) := by
    have hle : f.ker.map N.subtype ≤ R := by
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hker] at hx
      exact hx
    have hd := card_dvd_of_le hle
    rw [card_map_of_injective N.subtype_injective] at hd
    exact (GMSK.odd_card_standardComponentOddCore M).of_dvd_nat hd
  have hinj : Function.Injective f := by
    rcases halt with ⟨⟨ψ, -, -⟩, -⟩ | ⟨⟨k₂, _, _, hk₂, ψ, -, -⟩, -⟩
    · obtain ⟨s, hs⟩ := extension_split_prod hn hk ψ hfs hkercen hkerodd
      exact injective_of_section ψ hkercen s hs
    · obtain ⟨s, hs⟩ := extension_split_sl2 hn hk₂ ψ hfs hkercen hkerodd
      exact injective_of_section ψ hkercen s hs
  let e : N ≃* D := MulEquiv.ofBijective f ⟨hinj, hfs⟩
  have he : ∀ x : N, ((e x : D) : M ⧸ R) = π x := fun _ => rfl
  have hexcl : ∀ (k₂ : Type) (_ : Field k₂) (_ : Fintype k₂), Fintype.card k₂ = (2 ^ n) ^ 2 →
      (N ≃* SL(2, k) × SL(2, k)) → (N ≃* SL(2, k₂)) → False := by
    intro k₂ _ _ hk₂ ψ₁ ψ₂
    have hk₂' : Nat.card k₂ = 2 ^ (2 * n) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
    exact (GMS.isEmpty_mulEquiv_sl2_prod (k := k) (by omega) hk₂').false (ψ₂.symm.trans ψ₁)
  have hsyl : ∀ c : ℕ, (∀ P : Sylow 2 N, Nat.card P = c) → c = (2 ^ n) ^ 2 →
      ∃ P : Sylow 2 N, (P : Subgroup N).map N.subtype = V := by
    intro c hc hc'
    have hV2 : IsPGroup 2 (V.subgroupOf N) := by
      refine IsPGroup.of_card (n := 2 * n) ?_
      rw [Nat.card_congr (subgroupOfEquivOfLe hVA).toEquiv, hVcard, ← pow_mul, mul_comm]
    obtain ⟨P, hP⟩ := hV2.exists_le_sylow
    refine ⟨P, ?_⟩
    have hPV : V.subgroupOf N = (P : Subgroup N) := eq_of_le_of_card_ge hP (by
      rw [hc P, hc', Nat.card_congr (subgroupOfEquivOfLe hVA).toEquiv, hVcard])
    rw [← hPV, subgroupOf_map_subtype, inf_eq_left.mpr hVA]
  have hcentN : centralizer (N : Set M) = R := by
    refine le_antisymm (fun g hg => ?_) hRN
    have hgD : π g ∈ centralizer (D : Set (M ⧸ R)) := by
      rw [mem_centralizer_iff]
      intro d hd
      rw [hL] at hd
      obtain ⟨x, hx, rfl⟩ := hd
      rw [← map_mul, ← map_mul, mem_centralizer_iff.mp hg x hx]
    rw [hC, mem_bot] at hgD
    exact (QuotientGroup.eq_one_iff _).mp hgD
  have hNR : N ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxN, hxR⟩
    have h1 : f ⟨x, hxN⟩ = 1 := (hker ⟨x, hxN⟩).mpr hxR
    have h2 : (⟨x, hxN⟩ : N) = 1 := hinj (by rw [h1, map_one])
    exact (congrArg Subtype.val h2 : x = 1)
  rcases halt with ⟨⟨ψ, hψa, hψτ⟩, -⟩ | ⟨⟨k₂, _, _, hk₂, ψ, hψτ, hψA⟩, -⟩
  ·
    refine ⟨hNR, hcentN, hVA, hsyl (Fintype.card k ^ 2) (fun P => by
        rw [Common.card_sylow_two_eq_prod (e.trans ψ) P, Nat.card_eq_fintype_card]) (by rw [hk]),
      Or.inl ⟨⟨e.trans ψ, fun a x hxa => ?_, fun x y hyx => ?_⟩, ?_⟩⟩
    · exact hψa a (e x) (by rw [he, hxa])
    · exact hψτ (e x) (e y) (by rw [he, he, hyx, map_mul, map_mul, map_inv])
    · rintro ⟨k₂, _, _, hk₂, ψ₂, -⟩
      exact hexcl k₂ inferInstance inferInstance hk₂ (e.trans ψ) ψ₂
  ·
    have hk₂' : Nat.card k₂ = 2 ^ (2 * n) := by
      rw [Nat.card_eq_fintype_card, hk₂, ← pow_mul, mul_comm]
    have : CharP k₂ 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
        (by omega : 1 ≤ 2 * n) hk₂'
    refine ⟨hNR, hcentN, hVA, hsyl (Fintype.card k₂) (fun P => by
        rw [Common.card_sylow_two_eq (e.trans ψ) P, Nat.card_eq_fintype_card]) hk₂,
      Or.inr ⟨⟨k₂, inferInstance, inferInstance, hk₂, e.trans ψ, fun x y hyx => ?_, fun g => ?_⟩,
        ?_⟩⟩
    · exact hψτ (e x) (e y) (by rw [he, he, hyx, map_mul, map_mul, map_inv])
    · rw [← hψA g]
      have himg : (A.subgroupOf N).map e.toMonoidHom = (A.map π).subgroupOf D := by
        ext d
        constructor
        · rintro ⟨x, hx, rfl⟩
          rw [mem_subgroupOf, MulEquiv.coe_toMonoidHom, he]
          exact mem_map_of_mem π (mem_subgroupOf.mp hx)
        · intro hd
          obtain ⟨a, ha, had⟩ := mem_subgroupOf.mp hd
          have haN : a ∈ N := subset_normalClosure ha
          refine ⟨⟨a, haN⟩, mem_subgroupOf.mpr ha, Subtype.ext ?_⟩
          rw [MulEquiv.coe_toMonoidHom, he]
          exact had
      rw [← himg, Subgroup.map_map]
      rfl
    · rintro ⟨ψ₁, -⟩
      exact hexcl k₂ inferInstance inferInstance hk₂ ψ₁ (e.trans ψ)

end BothTrivialLayer

end CFSG.LocalAnalysis.EvenBN.Sp4
