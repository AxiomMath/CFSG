module

public import CFSG.Holt.H78.KernelSylow
public import CFSG.Holt.H78.SEModelFive
import CFSG.Holt.H78.DataSocle

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

section Split

variable {A : Type*} [Group A] [Finite A] {M : Type*} [Group M]

omit [Finite A] in
private theorem commutator_inf_le_of_exists_compl {O K : Subgroup A} [O.Normal]
    (hcen : K.map (QuotientGroup.mk' O) ≤ Subgroup.center (A ⧸ O))
    (hD : ∃ D : Subgroup (A ⧸ O),
      K.map (QuotientGroup.mk' O) ⊔ D = ⊤ ∧ K.map (QuotientGroup.mk' O) ⊓ D = ⊥) :
    ⁅(⊤ : Subgroup A), ⊤⁆ ⊓ K ≤ O := by
  obtain ⟨D, hsup, hinf⟩ := hD
  have hcomm : ⁅(⊤ : Subgroup (A ⧸ O)), ⊤⁆ ≤ D := Subgroup.commutator_le.mpr
    fun a _ b _ => by
      rw [commutatorElement_def]
      exact L17.commutator_mem_of_sup_eq_top hcen hsup a b
  intro x hx
  obtain ⟨hx, hxK⟩ := Subgroup.mem_inf.mp hx
  have h1 : QuotientGroup.mk' O x ∈ D := by
    refine hcomm ?_
    have h := Subgroup.mem_map_of_mem (QuotientGroup.mk' O) hx
    rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective O)] at h
  have h3 : QuotientGroup.mk' O x ∈ K.map (QuotientGroup.mk' O) ⊓ D :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_map_of_mem _ hxK, h1⟩
  rw [hinf, Subgroup.mem_bot, ← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at h3
  exact h3

omit [Finite A] in
private theorem split_data {f : A →* M} {O : Subgroup A} [O.Normal] (hOK : O ≤ f.ker)
    (hc : ∀ k ∈ f.ker, ∀ a : A, k * a * k⁻¹ * a⁻¹ ∈ O)
    (h2 : ∀ k ∈ f.ker, ∃ n : ℕ, k ^ 2 ^ n ∈ O) {V : Subgroup A} (hVK : V ⊓ f.ker ≤ O) :
    f.ker.map (QuotientGroup.mk' O) ≤ Subgroup.center (A ⧸ O) ∧
      IsPGroup 2 (f.ker.map (QuotientGroup.mk' O)) ∧
        V.map (QuotientGroup.mk' O) ⊓ f.ker.map (QuotientGroup.mk' O) = ⊥ := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro b
    induction b using QuotientGroup.induction_on with
    | H a =>
      have h1 := hc k⁻¹ (f.ker.inv_mem hk) a⁻¹
      rw [inv_inv, inv_inv] at h1
      change ((a : A ⧸ O) * (k : A ⧸ O)) = (k : A ⧸ O) * (a : A ⧸ O)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simpa [mul_assoc] using h1
  · rintro ⟨_, k, hk, rfl⟩
    obtain ⟨n, hn⟩ := h2 k hk
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk']
    exact hn
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨⟨v, hv, rfl⟩, ⟨k, hk, hkv⟩⟩ := Subgroup.mem_inf.mp hx
    have hvk : v⁻¹ * k ∈ O := QuotientGroup.eq.mp (hkv.symm : (v : A ⧸ O) = k)
    have hvK : v ∈ f.ker := by
      have h1 := f.ker.mul_mem hk (f.ker.inv_mem (hOK hvk))
      rwa [mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul] at h1
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact hVK (Subgroup.mem_inf.mpr ⟨hv, hvK⟩)

theorem commutator_inf_le_of_odd_index (f : A →* M) (hf : Function.Surjective f)
    {O : Subgroup A} [O.Normal] (hOK : O ≤ f.ker)
    (hc : ∀ k ∈ f.ker, ∀ a : A, k * a * k⁻¹ * a⁻¹ ∈ O)
    (h2 : ∀ k ∈ f.ker, ∃ n : ℕ, k ^ 2 ^ n ∈ O) {V : Subgroup A} (hVK : V ⊓ f.ker ≤ O)
    (hodd : Odd (V.map f).index) : ⁅(⊤ : Subgroup A), ⊤⁆ ⊓ f.ker ≤ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcen, hK2, hVK'⟩ := split_data hOK hc h2 hVK
  set q := QuotientGroup.mk' O
  set Kb := f.ker.map q
  set fb := QuotientGroup.lift O f hOK
  have hker : fb.ker = Kb := QuotientGroup.ker_lift O f hOK
  have hfbq : ∀ a, fb (q a) = f a := fun a => QuotientGroup.lift_mk _ _ _
  have hcomp : fb.comp q = f := MonoidHom.ext hfbq
  have hfb : Function.Surjective fb := fun m => by
    obtain ⟨a, ha⟩ := hf m
    exact ⟨q a, (hfbq a).trans ha⟩
  have hKn : Kb.Normal := f.normal_ker.map q (QuotientGroup.mk'_surjective O)
  have hKc : IsMulCommutative Kb := isMulCommutative_iff.mpr fun a b =>
    Subtype.ext ((Subgroup.mem_center_iff.mp (hcen a.2) b).symm)
  have hH0 : Kb ⊔ V.map q = (V.map f).comap fb := by
    rw [← hcomp, ← Subgroup.map_map, Subgroup.comap_map_eq, hker, sup_comm]
  have hcop : Nat.Coprime (Kb ⊔ V.map q).index (Nat.card Kb) := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hK2
    rw [hm, hH0, Subgroup.index_comap_of_surjective _ hfb]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hodd)
  obtain ⟨D, -, hD1, hD2⟩ := CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting Kb
    (Kb ⊔ V.map q) (V.map q) hcop (by rw [inf_comm]; exact hVK') rfl
  exact commutator_inf_le_of_exists_compl hcen ⟨D, hD2, hD1⟩

theorem commutator_inf_le_of_benderType (f : A →* M) (hf : Function.Surjective f)
    {O : Subgroup A} [O.Normal] (hOK : O ≤ f.ker)
    (hc : ∀ k ∈ f.ker, ∀ a : A, k * a * k⁻¹ * a⁻¹ ∈ O)
    (h2 : ∀ k ∈ f.ker, ∃ n : ℕ, k ^ 2 ^ n ∈ O) {V : Subgroup A} (hVK : V ⊓ f.ker ≤ O)
    {n i e : ℕ} (hM : BenderType M n i e) (hi : 2 ≤ i) (T₀ : Sylow 2 M)
    (hVT : V.map f = rootCenter (T₀ : Subgroup M))
    (hN : ∀ a : A, f a ∈ Subgroup.normalizer (T₀ : Set M) → ∀ v ∈ V, a * v * a⁻¹ ∈ V ⊔ O) :
    ⁅(⊤ : Subgroup A), ⊤⁆ ⊓ f.ker ≤ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite M := Finite.of_surjective f hf
  obtain ⟨hcen, hK2, hVK'⟩ := split_data hOK hc h2 hVK
  set q := QuotientGroup.mk' O
  set Kb := f.ker.map q
  set fb := QuotientGroup.lift O f hOK
  have hker : fb.ker = Kb := QuotientGroup.ker_lift O f hOK
  have hfbq : ∀ a, fb (q a) = f a := fun a => QuotientGroup.lift_mk _ _ _
  have hcomp : fb.comp q = f := MonoidHom.ext hfbq
  have hfb : Function.Surjective fb := fun m => by
    obtain ⟨a, ha⟩ := hf m
    exact ⟨q a, (hfbq a).trans ha⟩
  have hT2 : IsPGroup 2 ((T₀ : Subgroup M).comap fb) :=
    T₀.isPGroup'.comap_of_ker_isPGroup fb (hker ▸ hK2)
  have hTidx : ¬ 2 ∣ ((T₀ : Subgroup M).comap fb).index := by
    rw [Subgroup.index_comap_of_surjective _ hfb]
    exact T₀.not_dvd_index
  set T : Sylow 2 (A ⧸ O) := hT2.toSylow hTidx
  have hTc : (T : Subgroup (A ⧸ O)) = (T₀ : Subgroup M).comap fb := rfl
  set U := V.map q
  have hUmap : U.map fb = rootCenter (T₀ : Subgroup M) := by
    rw [Subgroup.map_map, hcomp, hVT]
  have hUT : U ≤ T := fun x hx => by
    rw [hTc, Subgroup.mem_comap]
    have h1 : fb x ∈ U.map fb := Subgroup.mem_map_of_mem fb hx
    rw [hUmap] at h1
    exact rootCenter_le _ h1
  have hTmap : (T : Subgroup (A ⧸ O)).map fb = T₀ := by
    rw [hTc]
    exact Subgroup.map_comap_eq_self_of_surjective hfb _
  have hOq : O.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have key : ∀ a : A, q a ∈ Subgroup.normalizer (T : Set (A ⧸ O)) →
      ∀ u ∈ U, q a * u * (q a)⁻¹ ∈ U := by
    intro a ha u hu
    have hfa : f a ∈ Subgroup.normalizer (T₀ : Set M) := by
      have ha' := Subgroup.mem_normalizer_iff.mp ha
      refine Subgroup.mem_normalizer_iff.mpr fun y => ?_
      obtain ⟨z, rfl⟩ := hfb y
      have h1 : z ∈ (T : Subgroup (A ⧸ O)) ↔ q a * z * (q a)⁻¹ ∈ (T : Subgroup (A ⧸ O)) :=
        ha' z
      rw [hTc, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv, hfbq] at h1
      exact h1
    obtain ⟨v, hv, rfl⟩ := hu
    have h1 : q (a * v * a⁻¹) ∈ (V ⊔ O).map q := Subgroup.mem_map_of_mem q (hN a hfa v hv)
    rw [Subgroup.map_sup, hOq, sup_bot_eq, map_mul, map_mul, map_inv] at h1
    exact h1
  have hU : Subgroup.normalizer (T : Set (A ⧸ O)) ≤ Subgroup.normalizer (U : Set (A ⧸ O)) := by
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H a =>
      refine Subgroup.mem_normalizer_iff.mpr fun u => ⟨key a hx u, fun hu => ?_⟩
      change q a * u * (q a)⁻¹ ∈ U at hu
      have hx' : q a⁻¹ ∈ Subgroup.normalizer (T : Set (A ⧸ O)) := by
        rw [map_inv]
        exact inv_mem hx
      have h1 := key a⁻¹ hx' _ hu
      rwa [map_inv, inv_inv, show (q a)⁻¹ * (q a * u * (q a)⁻¹) * q a = u by group] at h1
  have hUZ : U.map fb = rootCenter ((T : Subgroup (A ⧸ O)).map fb) := by rw [hTmap, hUmap]
  obtain ⟨Gs, -, hGs1, hGs2, -⟩ := lemma_1_7_of_benderType fb hfb (hker ▸ hcen) (hker ▸ hK2) hM
    hi T hUT (hker ▸ hVK') hU hUZ
  refine commutator_inf_le_of_exists_compl hcen ⟨Gs, ?_, ?_⟩
  · change Kb ⊔ Gs = ⊤
    rw [← hker, sup_comm]
    exact hGs2
  · change Kb ⊓ Gs = ⊥
    rw [← hker, inf_comm]
    exact hGs1

end Split

section FactorSplit

private theorem exists_sylow_le_stabilizer_of_odd {X Δ : Type*} [Group X]
    [MulAction X Δ] [Finite Δ] [IsPretransitive X Δ] (hΔ : Odd (Nat.card Δ)) (ω : Δ) :
    ∃ Q : Sylow 2 X, (Q : Subgroup X) ≤ stabilizer X ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨ω₀, hω₀⟩ := fixSet_nonempty_of_odd hΔ Q₀.isPGroup'
  obtain ⟨g, rfl⟩ := exists_smul_eq X ω₀ ω
  refine ⟨g • Q₀, fun x hx => ?_⟩
  have hx' : (g⁻¹ * x * g) • ω₀ = ω₀ := hω₀ _ (mem_smul_sylow_iff.mp hx)
  rw [mem_stabilizer_iff, ← inv_smul_eq_iff, ← mul_smul, ← mul_smul]
  exact hx'

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω] {α : Ω} {D' : HoltData (orbitGroup G α) (OddOrbits G α)}

variable (D') in
@[expose] def liftLRho (hG : IsStarGroup G Ω) (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (i : D'.ι) : liftL D' i →* D'.M i :=
  ((D'.ρ i).comp (((orbitRestrict G α).comp (liftL D' i).subtype).codRestrict _ fun l =>
    map_jHull_le hG hint α ⟨l, liftL_le_jHull i l.2, rfl⟩)).codRestrict (D'.M i) fun l =>
      HoltData.rho_mem_M (h := ⟨orbitRestrict G α l, _⟩) (mem_liftL.mp l.2).2

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem coe_liftLRho_apply (hG : IsStarGroup G Ω)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (i : D'.ι) (l : liftL D' i) :
    (liftLRho D' hG hint i l : Equiv.Perm (D'.Ψc i)) =
      D'.ρ i ⟨orbitRestrict G α l, map_jHull_le hG hint α ⟨l, liftL_le_jHull i l.2, rfl⟩⟩ :=
  rfl

theorem liftLRho_surjective (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (i : D'.ι) :
    Function.Surjective (liftLRho D' hG hint i) := by
  rintro ⟨m, hm⟩
  obtain ⟨h, hhL, rfl⟩ := HoltData.mem_M.mp hm
  rw [← map_liftL hG hO hint i] at hhL
  obtain ⟨l, hl, hlh⟩ := hhL
  exact ⟨⟨l, hl⟩, Subtype.ext (by rw [coe_liftLRho_apply]; congr 1; exact Subtype.ext hlh)⟩

theorem mem_ker_liftLRho (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (i : D'.ι) {l : liftL D' i} :
    l ∈ (liftLRho D' hG hint i).ker ↔ (l : G) ∈ jOrbitKernel G Ω := by
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  rw [MonoidHom.mem_ker, Subtype.ext_iff, coe_liftLRho_apply,
    jOrbitKernel_eq_inf_oddOrbitsKernel hG α, Subgroup.mem_inf, ← orbitRestrict_eq_one_iff]
  refine ⟨fun h => ⟨liftL_le_jHull i l.2, ?_⟩, fun h => ?_⟩
  · have h1 := HoltData.mem_jOddCore_of_mem_L (h := ⟨orbitRestrict G α l, _⟩)
      (mem_liftL.mp l.2).2 h
    rw [hOX, Subgroup.mem_bot] at h1
    exact h1
  · rw [show (⟨orbitRestrict G α l, map_jHull_le hG hint α ⟨l, liftL_le_jHull i l.2, rfl⟩⟩ :
      jHull (orbitGroup G α) (OddOrbits G α)) = 1 from Subtype.ext h.2, map_one]
    rfl

omit [Finite G] [Finite Ω] [FaithfulSMul G Ω] in
private theorem conj_mem_fixingSubgroup {Δ : Set Ω} {g x : G} (hg : g ∈ stabilizer G Δ)
    (hx : x ∈ fixingSubgroup G Δ) : g * x * g⁻¹ ∈ fixingSubgroup G Δ := by
  rw [mem_fixingSubgroup_iff] at hx ⊢
  intro δ hδ
  have hδ' : g⁻¹ • δ ∈ Δ := by
    have h1 : g⁻¹ • Δ = Δ := mem_stabilizer_iff.mp (inv_mem hg)
    have h2 : g⁻¹ • δ ∈ g⁻¹ • Δ := Set.smul_mem_smul_set hδ
    rwa [h1] at h2
  rw [mul_smul, mul_smul, hx _ hδ', smul_inv_smul]

omit [Finite Ω] [FaithfulSMul G Ω] in
private theorem map_subgroupOf_liftLRho_eq (hG : IsStarGroup G Ω)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (i : D'.ι) {V : Subgroup G}
    (hVA : V ≤ liftL D' i) {U : Subgroup (D'.M i)}
    (h1 : ∀ v ∈ V, ∀ hv : v ∈ jHull G Ω,
      D'.ρ i ⟨orbitRestrict G α v, map_jHull_le hG hint α ⟨v, hv, rfl⟩⟩ ∈ U.map (D'.M i).subtype)
    (h2 : ∀ u ∈ U.map (D'.M i).subtype, ∃ v ∈ V, ∃ hv : v ∈ jHull G Ω,
      D'.ρ i ⟨orbitRestrict G α v, map_jHull_le hG hint α ⟨v, hv, rfl⟩⟩ = u) :
    (V.subgroupOf (liftL D' i)).map (liftLRho D' hG hint i) = U := by
  ext m
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨u, hu, hum⟩ := h1 l (Subgroup.mem_subgroupOf.mp hl) (liftL_le_jHull i l.2)
    have hlu : liftLRho D' hG hint i l = u := Subtype.ext hum.symm
    rw [hlu]
    exact hu
  · intro hm
    obtain ⟨v, hv, hvH, hvm⟩ := h2 m ⟨m, hm, rfl⟩
    exact ⟨⟨v, hVA hv⟩, Subgroup.mem_subgroupOf.mpr hv, Subtype.ext hvm⟩

theorem commutator_liftL_inf_le (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (i : D'.ι) :
    ⁅liftL D' i, liftL D' i⁆ ⊓ jOrbitKernel G Ω ≤ jOddCore G Ω := by
  have := hG.isPretransitive
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  set A := liftL D' i
  set O : Subgroup A := (jOddCore G Ω).subgroupOf A
  set f := liftLRho D' hG hint i
  have hf := liftLRho_surjective hG hO hint i
  have hKH : ∀ l : A, l ∈ f.ker → (l : G) ∈ jHull G Ω ⊓ oddOrbitsKernel G α := fun l hl => by
    rw [← jOrbitKernel_eq_inf_oddOrbitsKernel hG α]
    exact (mem_ker_liftLRho hG hO hint i).mp hl
  have hOK : O ≤ f.ker := fun l hl =>
    (mem_ker_liftLRho hG hO hint i).mpr (jOddCore_le_jOrbitKernel (Subgroup.mem_subgroupOf.mp hl))
  have hc : ∀ k ∈ f.ker, ∀ a : A, k * a * k⁻¹ * a⁻¹ ∈ O := fun k hk a =>
    Subgroup.mem_subgroupOf.mpr
      (commutator_mem_jOddCore hG hO α (hKH k hk) (liftL_le_jHull i a.2))
  have h2 : ∀ k ∈ f.ker, ∃ n : ℕ, k ^ 2 ^ n ∈ O := fun k hk => by
    obtain ⟨n, hn⟩ := exists_pow_two_pow_mem_jOddCore hG hO α (hKH k hk)
    exact ⟨n, Subgroup.mem_subgroupOf.mpr (by rw [Subgroup.coe_pow]; exact hn)⟩
  have hFK : ∀ l : A, (l : G) ∈ fixingSubgroup G (orbit (CFSG.pPrimeCore 2 G) α) → l ∈ f.ker →
      l ∈ O := fun l hlF hlK => by
    have h1 := hKH l hlK
    have hlN := fixingSubgroup_inf_oddOrbitsKernel_le hG α α
      (Subgroup.mem_inf.mpr ⟨hlF, (Subgroup.mem_inf.mp h1).2⟩)
    rw [Subgroup.mem_subgroupOf, jOddCore_eq_jHull_inf_pPrimeCore]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp h1).1, hlN⟩
  have hVK : ∀ V : Subgroup G, V ≤ fixingSubgroup G (orbit (CFSG.pPrimeCore 2 G) α) →
      V.subgroupOf A ⊓ f.ker ≤ O := fun V hVF v hv =>
    hFK v (hVF (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hv).1)) (Subgroup.mem_inf.mp hv).2
  suffices key : ⁅(⊤ : Subgroup A), ⊤⁆ ⊓ f.ker ≤ O by
    intro x hx
    obtain ⟨hx, hxK⟩ := Subgroup.mem_inf.mp hx
    have e : ⁅A, A⁆ = Subgroup.map A.subtype ⁅(⊤ : Subgroup A), ⊤⁆ := by
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [e] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact Subgroup.mem_subgroupOf.mp
      (key (Subgroup.mem_inf.mpr ⟨hy, (mem_ker_liftLRho hG hO hint i).mpr hxK⟩))
  set B := orbitPoint G α α
  have hodd : Odd (Nat.card (D'.Ψc i)) := by
    rw [Nat.card_eq_fintype_card]
    exact D'.odd_card_Ψc i
  have := (D'.factor i).isPretransitive
  rcases D'.factor i with ⟨hAlt, h7⟩ | hSE
  ·
    obtain ⟨S, hS⟩ := exists_sylow_le_stabilizer_of_odd (X := D'.M i) hodd (D'.coord B i)
    have hUW : (S : Subgroup (D'.M i)).map (D'.M i).subtype ≤ D'.wModel B i := by
      rw [D'.wModel_eq_of_alternatingGroup B hAlt h7]
      rintro _ ⟨s, hs, rfl⟩
      exact ⟨hAlt ▸ s.2, hS hs⟩
    obtain ⟨V, hVA, hVF, -, hV1, hV2⟩ :=
      exists_isPGroup_rho_eq hG hO hint α i (S.isPGroup'.map _) hUW
    refine commutator_inf_le_of_odd_index f hf hOK hc h2 (hVK V hVF) ?_
    rw [map_subgroupOf_liftLRho_eq hG hint i hVA hV1 hV2]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp S.not_dvd_index)
  ·
    obtain ⟨n, i', e, hA⟩ := isNaturalSE_iff.mp hSE
    obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer (D'.coord B i)
    have hW : D'.wModel B i = (rootCenter (Q : Subgroup (D'.M i))).map (D'.M i).subtype := by
      rw [D'.wModel_eq_of_isNaturalSE B hSE, hSE.mulLongInvClosure_eq hQ]
    have hZ2 : IsPGroup 2 (rootCenter (Q : Subgroup (D'.M i))) :=
      Q.isPGroup'.to_le (rootCenter_le _)
    obtain ⟨V, hVA, hVF, -, hV1, hV2⟩ := exists_isPGroup_rho_eq hG hO hint α i (hZ2.map _) hW.ge
    have hVm := map_subgroupOf_liftLRho_eq hG hint i hVA hV1 hV2
    rcases Nat.lt_or_ge i' 2 with hi | hi
    ·
      have hi1 : i' = 1 := by
        have := hA.params
        omega
      subst hi1
      have : Nontrivial (D'.Ψc i) := hA.nontrivial
      obtain ⟨b', hb'⟩ := exists_ne (D'.coord B i)
      obtain ⟨t, ht, htb⟩ := hA.exists_involution_smul_eq hb'.symm
      have hbc := hA.benderCore hQ ht (htb.trans_ne hb')
      have hZQ : rootCenter (Q : Subgroup (D'.M i)) = Q :=
        Subgroup.eq_of_le_of_card_ge (rootCenter_le _)
          (by rw [hbc.card_center, hbc.card_eq, pow_one])
      refine commutator_inf_le_of_odd_index f hf hOK hc h2 (hVK V hVF) ?_
      rw [hVm, hZQ]
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp Q.not_dvd_index)
    ·
      refine commutator_inf_le_of_benderType f hf hOK hc h2 (hVK V hVF) hA.benderType hi Q hVm
        fun a ha v hv => ?_
      have hfa : f a • D'.coord B i = D'.coord B i :=
        (hA.mem_borel_iff hQ).mp (show f a ∈ borel (Q : Subgroup (D'.M i)) from ha)
      have hπa : orbitRestrict G α a • B = B := by
        refine HoltData.coord_injective (D := D') hOX (funext fun j => ?_)
        rw [show orbitRestrict G α a = ((⟨orbitRestrict G α a, map_jHull_le hG hint α
          ⟨a, liftL_le_jHull i a.2, rfl⟩⟩ : jHull (orbitGroup G α) (OddOrbits G α)) :
            orbitGroup G α) from rfl, D'.coord_smul]
        by_cases hj : j = i
        · subst hj
          exact hfa
        · rw [HoltData.rho_eq_one_of_mem_L (D := D') (Ne.symm hj) (mem_liftL.mp a.2).2]
          rfl
      have haB := (orbitRestrict_smul_orbitPoint_eq_iff (α := α)).mp hπa
      have hwF : ((a * v * a⁻¹ : A) : G) ∈ fixingSubgroup G (orbit (CFSG.pPrimeCore 2 G) α) :=
        conj_mem_fixingSubgroup haB (hVF (Subgroup.mem_subgroupOf.mp hv))
      have hfw : f (a * v * a⁻¹) ∈ rootCenter (Q : Subgroup (D'.M i)) := by
        rw [map_mul, map_mul, map_inv]
        exact conj_mem_rootCenter ha (hVm ▸ Subgroup.mem_map_of_mem f hv)
      rw [← hVm] at hfw
      obtain ⟨v', hv', hv'w⟩ := hfw
      have hk : v'⁻¹ * (a * v * a⁻¹) ∈ O := by
        refine hFK _ ?_ ?_
        · exact mul_mem (inv_mem (hVF (Subgroup.mem_subgroupOf.mp hv'))) hwF
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hv'w, inv_mul_cancel]
      rw [show a * v * a⁻¹ = v' * (v'⁻¹ * (a * v * a⁻¹)) by group]
      exact mul_mem (Subgroup.mem_sup_left hv') (Subgroup.mem_sup_right hk)

end FactorSplit

section Components

private theorem mem_normalizer_commutator' {X : Type*} [Group X] {L : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (L : Set X)) :
    g ∈ Subgroup.normalizer ((⁅L, L⁆ : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg]

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω] {α : Ω} {D' : HoltData (orbitGroup G α) (OddOrbits G α)}

variable (D') in
@[expose] def splitL (i : D'.ι) : Subgroup G := jOddCore G Ω ⊔ ⁅liftL D' i, liftL D' i⁆

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem splitL_le_liftL (hG : IsStarGroup G Ω) (i : D'.ι) : splitL D' i ≤ liftL D' i :=
  sup_le (jOddCore_le_jOrbitKernel.trans (jOrbitKernel_le_liftL hG i))
    (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem splitL_le_jHull (hG : IsStarGroup G Ω) (i : D'.ι) : splitL D' i ≤ jHull G Ω :=
  (splitL_le_liftL hG i).trans (liftL_le_jHull i)

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem le_normalizer_splitL (hG : IsStarGroup G Ω)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (i : D'.ι) :
    jHull G Ω ≤ Subgroup.normalizer (splitL D' i : Set G) := fun h hh => by
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (mem_normalizer_commutator' (le_normalizer_liftL hG hint i hh))
  have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.le_normalizer_of_normal (H := jOddCore G Ω) (Subgroup.mem_top h))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, splitL, Subgroup.map_sup, h1, h2]

theorem splitL_inf_jOrbitKernel (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (i : D'.ι) :
    splitL D' i ⊓ jOrbitKernel G Ω ≤ jOddCore G Ω := by
  intro x hx
  obtain ⟨hxL, hxK⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨o, ho, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxL
  have hcK : c ∈ jOrbitKernel G Ω := by
    rw [show c = o⁻¹ * (o * c) by group]
    exact mul_mem (inv_mem (jOddCore_le_jOrbitKernel ho)) hxK
  exact mul_mem ho (commutator_liftL_inf_le hG hO hint i (Subgroup.mem_inf.mpr ⟨hc, hcK⟩))

theorem map_splitL (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (i : D'.ι) :
    (splitL D' i).map (orbitRestrict G α) = D'.L i := by
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  have hOH : (jOddCore G Ω).map (orbitRestrict G α) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, MonoidHom.ker_rangeRestrict]
    exact (jOddCore_le_pPrimeCore).trans (pPrimeCore_le_oddOrbitsKernel α)
  rw [splitL, Subgroup.map_sup, hOH, bot_sup_eq, Subgroup.map_commutator, map_liftL hG hO hint i]
  have hle : ⁅D'.L i, D'.L i⁆ ≤ D'.L i := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  rcases D'.eq_jOddCore_or_eq_L i (N := ⁅D'.L i, D'.L i⁆) (by rw [hOX]; exact bot_le) hle
      (fun l hl => mem_normalizer_commutator' (Subgroup.le_normalizer hl)) with h | h
  · exact absurd (h.le) ((D'.isJComponent_L i).not_commutator_le)
  · exact h

variable (D') in
@[expose] def liftRho (hG : IsStarGroup G Ω) (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (i : D'.ι) : jHull G Ω →* Equiv.Perm (D'.Ψc i) :=
  (D'.ρ i).comp (((orbitRestrict G α).comp (jHull G Ω).subtype).codRestrict _ fun h =>
    map_jHull_le hG hint α ⟨h, h.2, rfl⟩)

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem liftRho_apply (hG : IsStarGroup G Ω) (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (i : D'.ι) (h : jHull G Ω) :
    liftRho D' hG hint i h =
      D'.ρ i ⟨orbitRestrict G α h, map_jHull_le hG hint α ⟨h, h.2, rfl⟩⟩ :=
  rfl

theorem factorImage_splitL (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (i : D'.ι) :
    factorImage G Ω (splitL D' i) (liftRho D' hG hint i) = D'.M i := by
  ext m
  rw [mem_factorImage, HoltData.mem_M]
  constructor
  · rintro ⟨h, hhL, rfl⟩
    exact ⟨_, (mem_liftL.mp (splitL_le_liftL hG i hhL)).2, rfl⟩
  · rintro ⟨h', hh'L, rfl⟩
    rw [← map_splitL hG hO hint i] at hh'L
    obtain ⟨g, hg, hgh⟩ := hh'L
    exact ⟨⟨g, splitL_le_jHull hG i hg⟩, hg, by rw [liftRho_apply]; congr 1; exact Subtype.ext hgh⟩

end Components

section Socle

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω] {α : Ω} {D' : HoltData (orbitGroup G α) (OddOrbits G α)}

theorem map_iSup_splitL (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) :
    (⨆ i, splitL D' i).map (orbitRestrict G α) = ⨆ i, D'.L i := by
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i => map_splitL hG hO hint i

theorem exists_mem_socle_smul_eq (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (ω ω' : Ω) :
    ∃ g ∈ jOddCore G Ω ⊔ ⨆ i, splitL D' i, g • ω = ω' := by
  have := hG.isPretransitive
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  obtain ⟨⟨x, hx⟩, hxω⟩ := (D'.mem_orbit_sup_finsetSup_iff Finset.univ (orbitPoint G α ω)
    (orbitPoint G α ω')).mpr fun j hj => absurd (Finset.mem_univ j) hj
  rw [hOX, bot_sup_eq, Finset.sup_univ_eq_iSup, ← map_iSup_splitL hG hO hint] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  have h1 : orbitPoint G α (g • ω) = orbitPoint G α ω' := by
    rw [orbitPoint_smul]
    exact hxω
  rw [blockCoset_eq_blockCoset_iff, ← orbit_jOddCore_eq hG] at h1
  obtain ⟨⟨o, ho⟩, hoω⟩ := h1
  exact ⟨o * g, mul_mem (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right hg), by
    rw [mul_smul]
    exact hoω⟩

theorem exists_conj_mul_mem_jOddCore (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t u : G} (ht : t ∈ longInv G Ω)
    (hu : u ∈ longInv G Ω) :
    ∃ c ∈ jOddCore G Ω ⊔ ⨆ i, splitL D' i, c * t * c⁻¹ * u ∈ jOddCore G Ω := by
  have := hG.isPretransitive
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  obtain ⟨β, hβ⟩ := exists_mem_longInvAt hu
  obtain ⟨γ, hγ⟩ := exists_mem_longInvAt ht
  obtain ⟨h, hh, hhγ⟩ := exists_mem_socle_smul_eq (D' := D') hG hO hint γ β
  have ht' : h * t * h⁻¹ ∈ longInvAt G Ω β := by
    have h1 := conj_mem_longInvAt hγ h
    rwa [hhγ] at h1
  have ht'X := orbitRestrict_mem_longInvAt hG hint ht' (α := α)
  have huX := orbitRestrict_mem_longInvAt hG hint hβ (α := α)
  obtain ⟨l, hl, -, hly⟩ := D'.exists_conj_rho_eq ht'X Finset.univ
    (fun i => D'.ρ i ⟨orbitRestrict G α u, mem_jHull_of_mem_longInv huX.1⟩)
    (fun i _ => D'.rho_mem_longInvAt huX i) (fun i _ => ⟨_, rfl⟩)
  have heq : (l : orbitGroup G α) * orbitRestrict G α (h * t * h⁻¹) * (l : orbitGroup G α)⁻¹ =
      orbitRestrict G α u := by
    have h1 := HoltData.eq_one_of_forall_rho_eq_one (D := D') hOX
      (h := (l * ⟨_, mem_jHull_of_mem_longInv ht'X.1⟩ * l⁻¹)⁻¹ *
        ⟨orbitRestrict G α u, mem_jHull_of_mem_longInv huX.1⟩)
      fun i => by rw [map_mul, map_inv, hly i (Finset.mem_univ i), inv_mul_cancel]
    exact congrArg Subtype.val (inv_mul_eq_one.mp h1)
  rw [hOX, bot_sup_eq, Finset.sup_univ_eq_iSup, ← map_iSup_splitL hG hO hint] at hl
  obtain ⟨g, hg, hgl⟩ := hl
  refine ⟨g * h, mul_mem (Subgroup.mem_sup_right hg) hh, ?_⟩
  set w := g * h * t * (g * h)⁻¹
  have hwu : orbitRestrict G α w = orbitRestrict G α u := by
    rw [← heq, ← hgl]
    simp only [w, map_mul, map_inv]
    group
  have hwJ : w ∈ longInv G Ω := conj_mem_longInv ht _
  have hwB : w ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β) :=
    (orbitRestrict_smul_orbitPoint_eq_iff (α := α)).mp (by rw [hwu]; exact huX.2)
  have hk : w * u ∈ blockEven G β ⊓ oddOrbitsKernel G α := Subgroup.mem_inf.mpr
    ⟨mul_mem_blockEven hO hwJ hu hwB (mem_stabilizer_orbit_of_mem_longInvAt hβ),
      (orbitRestrict_eq_one_iff α).mp (by
        rw [map_mul, hwu, ← map_mul, mul_self_eq_one_of_mem_longInv hu, map_one])⟩
  rw [jOddCore_eq_jHull_inf_pPrimeCore]
  exact Subgroup.mem_inf.mpr ⟨mul_mem (mem_jHull_of_mem_longInv hwJ) (mem_jHull_of_mem_longInv hu),
    blockEven_inf_oddOrbitsKernel_le hG α β hk⟩

theorem sup_splitL_sup_zpowers (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t : G} (ht : t ∈ longInv G Ω) :
    jOddCore G Ω ⊔ (⨆ i, splitL D' i) ⊔ Subgroup.zpowers t = jHull G Ω := by
  refine le_antisymm (sup_le (sup_le jOddCore_le_jHull (iSup_le fun i => splitL_le_jHull hG i))
    (Subgroup.zpowers_le.mpr (mem_jHull_of_mem_longInv ht))) (jHull_le_iff.mpr fun u hu => ?_)
  obtain ⟨c, hc, hcu⟩ := exists_conj_mul_mem_jOddCore (D' := D') hG hO hint ht hu
  have e : u = c * t⁻¹ * c⁻¹ * (c * t * c⁻¹ * u) := by group
  rw [SetLike.mem_coe, e]
  have hc' : c ∈ jOddCore G Ω ⊔ (⨆ i, splitL D' i) ⊔ Subgroup.zpowers t :=
    Subgroup.mem_sup_left hc
  exact mul_mem (mul_mem (mul_mem hc' (inv_mem (Subgroup.mem_sup_right
    (Subgroup.mem_zpowers t)))) (inv_mem hc')) (Subgroup.mem_sup_left (Subgroup.mem_sup_left hcu))

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem liftRho_eq_one_of_mem_jOddCore (hG : IsStarGroup G Ω)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {h : jHull G Ω}
    (hh : (h : G) ∈ jOddCore G Ω) (j : D'.ι) : liftRho D' hG hint j h = 1 := by
  rw [liftRho_apply, show (⟨orbitRestrict G α h, map_jHull_le hG hint α ⟨h, h.2, rfl⟩⟩ :
    jHull (orbitGroup G α) (OddOrbits G α)) = 1 from Subtype.ext ((orbitRestrict_eq_one_iff α).mpr
      (pPrimeCore_le_oddOrbitsKernel α (jOddCore_le_pPrimeCore hh))), map_one]

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem liftRho_eq_one_of_mem_splitL (hG : IsStarGroup G Ω)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {i j : D'.ι} (hij : i ≠ j)
    {h : jHull G Ω} (hh : (h : G) ∈ splitL D' i) : liftRho D' hG hint j h = 1 :=
  HoltData.rho_eq_one_of_mem_L hij (mem_liftL.mp (splitL_le_liftL hG i hh)).2

theorem mem_jOddCore_of_mem_splitL (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {i : D'.ι} {h : jHull G Ω}
    (hh : (h : G) ∈ splitL D' i) (h1 : liftRho D' hG hint i h = 1) : (h : G) ∈ jOddCore G Ω := by
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  have h2 := HoltData.mem_jOddCore_of_mem_L (D := D') (mem_liftL.mp (splitL_le_liftL hG i hh)).2 h1
  rw [hOX, Subgroup.mem_bot] at h2
  refine splitL_inf_jOrbitKernel hG hO hint i (Subgroup.mem_inf.mpr ⟨hh, ?_⟩)
  rw [jOrbitKernel_eq_inf_oddOrbitsKernel hG α]
  exact Subgroup.mem_inf.mpr ⟨h.2, (orbitRestrict_eq_one_iff α).mp h2⟩

theorem liftRho_eq_one_of_mem_sup_finsetSup (hG : IsStarGroup G Ω)
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (s : Finset D'.ι) {h : jHull G Ω} (hh : (h : G) ∈ jOddCore G Ω ⊔ s.sup (splitL D')) :
    (∀ j ∉ s, liftRho D' hG hint j h = 1) ∧
      ((∀ i ∈ s, liftRho D' hG hint i h = 1) → (h : G) ∈ jOddCore G Ω) := by
  induction s using Finset.induction_on generalizing h with
  | empty =>
    rw [Finset.sup_empty, sup_bot_eq] at hh
    exact ⟨fun j _ => liftRho_eq_one_of_mem_jOddCore hG hint hh j, fun _ => hh⟩
  | insert a s ha ih =>
    have heq : jOddCore G Ω ⊔ (insert a s).sup (splitL D') =
        jOddCore G Ω ⊔ s.sup (splitL D') ⊔ splitL D' a := by
      rw [Finset.sup_insert]
      ac_rfl
    have hP : jOddCore G Ω ⊔ s.sup (splitL D') ≤ jHull G Ω :=
      sup_le jOddCore_le_jHull (Finset.sup_le fun i _ => splitL_le_jHull hG i)
    have hh' : (h : G) ∈ ((jOddCore G Ω ⊔ s.sup (splitL D') ⊔ splitL D' a : Subgroup G) :
        Set G) := heq ▸ hh
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (hP.trans (le_normalizer_splitL hG hint a))] at hh'
    obtain ⟨p, hp, l, hl, hpl⟩ := Set.mem_mul.mp hh'
    obtain ⟨ih1, ih2⟩ := ih (h := ⟨p, hP hp⟩) hp
    obtain rfl : h = ⟨p, hP hp⟩ * ⟨l, splitL_le_jHull hG a hl⟩ := Subtype.ext hpl.symm
    refine ⟨fun j hj => ?_, fun hs => ?_⟩
    · rw [Finset.mem_insert, not_or] at hj
      rw [map_mul, ih1 j hj.2, liftRho_eq_one_of_mem_splitL hG hint (Ne.symm hj.1)
        (h := ⟨l, splitL_le_jHull hG a hl⟩) hl, mul_one]
    · have hla : liftRho D' hG hint a ⟨l, splitL_le_jHull hG a hl⟩ = 1 := by
        have h1 := hs a (Finset.mem_insert_self a s)
        rwa [map_mul, ih1 a ha, one_mul] at h1
      have hlO := mem_jOddCore_of_mem_splitL hG hO hint (h := ⟨l, splitL_le_jHull hG a hl⟩) hl hla
      have hpO : p ∈ jOddCore G Ω := ih2 fun i hi => by
        have h1 := hs i (Finset.mem_insert_of_mem hi)
        rwa [map_mul, liftRho_eq_one_of_mem_jOddCore hG hint (h := ⟨l, _⟩) hlO i, mul_one] at h1
      exact mul_mem hpO hlO

theorem socle_inf_jOrbitKernel (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) :
    (jOddCore G Ω ⊔ ⨆ i, splitL D' i) ⊓ jOrbitKernel G Ω ≤ jOddCore G Ω := by
  intro x hx
  obtain ⟨hxS, hxK⟩ := Subgroup.mem_inf.mp hx
  rw [jOrbitKernel_eq_inf_oddOrbitsKernel hG α] at hxK
  obtain ⟨hxH, hxK⟩ := Subgroup.mem_inf.mp hxK
  rw [← Finset.sup_univ_eq_iSup] at hxS
  refine (liftRho_eq_one_of_mem_sup_finsetSup hG hO hint Finset.univ (h := ⟨x, hxH⟩) hxS).2
    fun i _ => ?_
  rw [liftRho_apply, show (⟨orbitRestrict G α x, map_jHull_le hG hint α ⟨x, hxH, rfl⟩⟩ :
    jHull (orbitGroup G α) (OddOrbits G α)) = 1 from Subtype.ext
      ((orbitRestrict_eq_one_iff α).mpr hxK), map_one]

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem liftRho_eq_one_of_mem_jOrbitKernel (hG : IsStarGroup G Ω)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {h : jHull G Ω}
    (hh : (h : G) ∈ jOrbitKernel G Ω) (j : D'.ι) : liftRho D' hG hint j h = 1 := by
  rw [jOrbitKernel_eq_inf_oddOrbitsKernel hG α] at hh
  rw [liftRho_apply, show (⟨orbitRestrict G α h, map_jHull_le hG hint α ⟨h, h.2, rfl⟩⟩ :
    jHull (orbitGroup G α) (OddOrbits G α)) = 1 from Subtype.ext
      ((orbitRestrict_eq_one_iff α).mpr (Subgroup.mem_inf.mp hh).2), map_one]

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem conj_mem_socle (hG : IsStarGroup G Ω) (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    {g : G} (hg : g ∈ jHull G Ω) {x : G} (hx : x ∈ jOddCore G Ω ⊔ ⨆ i, splitL D' i) :
    g * x * g⁻¹ ∈ jOddCore G Ω ⊔ ⨆ i, splitL D' i := by
  have hle : jOddCore G Ω ⊔ ⨆ i, splitL D' i ≤
      (jOddCore G Ω ⊔ ⨆ i, splitL D' i).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun o ho => Subgroup.mem_sup_left (jOddCore_normal.conj_mem o ho g))
      (iSup_le fun i l hl => Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem i
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_splitL hG hint i hg) l).mp hl)))
  exact hle hx

theorem mem_socle_or_t_mul_mem (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t : G} (ht : t ∈ longInv G Ω) {v : G}
    (hv : v ∈ jHull G Ω) :
    v ∈ jOddCore G Ω ⊔ (⨆ i, splitL D' i) ∨ t * v ∈ jOddCore G Ω ⊔ ⨆ i, splitL D' i := by
  have hN : Subgroup.zpowers t ≤
      Subgroup.normalizer ((jOddCore G Ω ⊔ ⨆ i, splitL D' i : Subgroup G) : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_iff.mpr fun x =>
      ⟨conj_mem_socle hG hint (mem_jHull_of_mem_longInv ht), fun hx => ?_⟩)
    have h := conj_mem_socle (D' := D') hG hint (inv_mem (mem_jHull_of_mem_longInv ht)) hx
    rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at h
  rw [← sup_splitL_sup_zpowers (D' := D') hG hO hint ht, sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hv
  obtain ⟨a, ha, s, hs, rfl⟩ := Set.mem_mul.mp hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  have htt := mul_self_eq_one_of_mem_longInv ht
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, zpow_two, htt, one_zpow, one_mul]
    exact hs
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, htt, one_zpow, one_mul, ← mul_assoc, htt, one_mul]
    exact hs

theorem liftRho_mem_M_of_mem_socle (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {h : jHull G Ω}
    (hh : (h : G) ∈ jOddCore G Ω ⊔ ⨆ i, splitL D' i) (i : D'.ι) :
    liftRho D' hG hint i h ∈ D'.M i := by
  rw [liftRho_apply]
  refine HoltData.rho_mem_M_of_mem_socPre ?_ i
  obtain ⟨o, ho, l, hl, hol⟩ := Subgroup.mem_sup_of_normal_left.mp hh
  have hl' : orbitRestrict G α l ∈ ⨆ i, D'.L i := by
    rw [← map_iSup_splitL hG hO hint]
    exact Subgroup.mem_map_of_mem _ hl
  have hπo : orbitRestrict G α o = 1 := (orbitRestrict_eq_one_iff α).mpr
    (pPrimeCore_le_oddOrbitsKernel α (jOddCore_le_pPrimeCore ho))
  change orbitRestrict G α (h : G) ∈ _
  rw [← hol, map_mul, hπo, one_mul]
  exact Subgroup.mem_sup_right hl'

end Socle

section KernelStatement

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω] {α : Ω} {D' : HoltData (orbitGroup G α) (OddOrbits G α)}

theorem jOrbitKernel_eq_jOddCore_of_isOuterFactor (hG : IsStarGroup G Ω)
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t : G}
    (ht : t ∈ longInv G Ω)
    (hout : ∃ i, IsOuterFactor (D'.M i)) : jOrbitKernel G Ω = jOddCore G Ω := by
  obtain ⟨i, hi⟩ := hout
  refine le_antisymm (fun k hk => ?_) jOddCore_le_jOrbitKernel
  by_contra hkO
  have hkH := jOrbitKernel_le_jHull hk
  have htk := (mem_socle_or_t_mul_mem (D' := D') hG hO hint ht hkH).resolve_left fun hkS =>
    hkO (socle_inf_jOrbitKernel hG hO hint (Subgroup.mem_inf.mpr ⟨hkS, hk⟩))
  have h1 := liftRho_mem_M_of_mem_socle hG hO hint
    (h := ⟨t, mem_jHull_of_mem_longInv ht⟩ * ⟨k, hkH⟩) htk i
  rw [map_mul, liftRho_eq_one_of_mem_jOrbitKernel hG hint (h := ⟨k, hkH⟩) hk, mul_one,
    liftRho_apply] at h1
  exact (D'.rho_mem_M_iff (orbitRestrict_mem_longInv hG hint ht) i).mp h1 hi

theorem mem_socle_sup_jOrbitKernel (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t : G} (ht : t ∈ longInv G Ω)
    (hall : ∀ i, ¬ IsOuterFactor (D'.M i)) :
    t ∈ jOddCore G Ω ⊔ (⨆ i, splitL D' i) ⊔ jOrbitKernel G Ω := by
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  have htX := orbitRestrict_mem_longInv hG hint ht (α := α)
  have h1 : orbitRestrict G α t ∈ ⨆ i, D'.L i :=
    HoltData.mem_iSup_of_forall_rho hOX (V := D'.L) (fun i => le_rfl)
      (h := ⟨_, mem_jHull_of_mem_longInv htX⟩) fun i =>
        HoltData.mem_M.mp ((D'.rho_mem_M_iff htX i).mpr (hall i))
  rw [← map_iSup_splitL hG hO hint] at h1
  obtain ⟨s, hs, hst⟩ := h1
  rw [show t = s * (s⁻¹ * t) by group]
  refine mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_right hs)) (Subgroup.mem_sup_right ?_)
  rw [jOrbitKernel_eq_inf_oddOrbitsKernel hG α]
  exact Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ((iSup_le fun i => splitL_le_jHull hG i) hs))
    (mem_jHull_of_mem_longInv ht), (orbitRestrict_eq_one_iff α).mp (by
      rw [map_mul, map_inv, hst, inv_mul_cancel])⟩

theorem not_jOrbitKernel_le_jOddCore (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (hall : ∀ i, ¬ IsOuterFactor (D'.M i)) :
    ¬ jOrbitKernel G Ω ≤ jOddCore G Ω := by
  intro hle
  have := hG.isPretransitive
  obtain ⟨t, ht⟩ := hG.longInvAt_nonempty α
  obtain ⟨y, hy, hyt⟩ := exists_mem_blockEven_orbitRestrict_eq (D' := D') hG hO hint hall ht
  obtain ⟨hyH, hyE⟩ := Subgroup.mem_inf.mp hy
  replace hyH : y ∈ jHull G Ω := Subgroup.closure_mono (longInvAt_subset_longInv α) hyH
  have hk : y⁻¹ * t ∈ jOrbitKernel G Ω := by
    rw [jOrbitKernel_eq_inf_oddOrbitsKernel hG α]
    exact Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hyH) (mem_jHull_of_mem_longInv ht.1),
      (orbitRestrict_eq_one_iff α).mp (by rw [map_mul, map_inv, hyt, inv_mul_cancel])⟩
  have htE : t ∈ blockEven G α := by
    rw [show t = y * (y⁻¹ * t) by group]
    exact mul_mem hyE (pPrimeCore_le_blockEven α (jOddCore_le_pPrimeCore (hle hk)))
  have htF := mem_fixingSubgroup_of_mem_blockEven htE (n := 1)
    (by rw [pow_one, sq, mul_self_eq_one_of_mem_longInv ht.1])
  have h3 := three_le_card_orbit_pPrimeCore hO α
  rw [Nat.card_coe_set_eq] at h3
  obtain ⟨δ, hδ, hδα⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := orbit (CFSG.pPrimeCore 2 G) α) (by omega) α
  exact hδα ((smul_eq_iff_of_mem_longInvAt ht δ).mp ((mem_fixingSubgroup_iff G).mp htF δ hδ))

theorem relIndex_jOddCore_jOrbitKernel_eq_two' (hG : IsStarGroup G Ω)
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t : G}
    (ht : t ∈ longInv G Ω) (hall : ∀ i, ¬ IsOuterFactor (D'.M i)) :
    (jOddCore G Ω).relIndex (jOrbitKernel G Ω) = 2 := by
  obtain ⟨k₀, hk₀K, hk₀O⟩ := Set.not_subset.mp (not_jOrbitKernel_le_jOddCore (D' := D') hG hO hint
    hall)
  have hout : ∀ k ∈ jOrbitKernel G Ω, k ∉ jOddCore G Ω →
      t * k ∈ jOddCore G Ω ⊔ ⨆ i, splitL D' i := fun k hk hkO =>
    (mem_socle_or_t_mul_mem hG hO hint ht (jOrbitKernel_le_jHull hk)).resolve_left fun hkS =>
      hkO (socle_inf_jOrbitKernel hG hO hint (Subgroup.mem_inf.mpr ⟨hkS, hk⟩))
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨k₀, hk₀K⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hb : (b : G) ∈ jOddCore G Ω
  · refine Or.inr ⟨hb, fun hbk => hk₀O ?_⟩
    rw [show k₀ = (b : G)⁻¹ * (b * k₀) by group]
    exact mul_mem (inv_mem hb) hbk
  · refine Or.inl ⟨?_, hb⟩
    have hbk : (b : G) * k₀ = t * (t * b) * t⁻¹ * (t * k₀) := by
      rw [show t⁻¹ = t from inv_eq_self_of_mem_longInv ht]
      have htt := mul_self_eq_one_of_mem_longInv ht
      calc (b : G) * k₀ = (t * t) * b * (t * t) * k₀ := by rw [htt, one_mul, mul_one]
        _ = t * (t * b) * t * (t * k₀) := by group
    refine socle_inf_jOrbitKernel (D' := D') hG hO hint
      (Subgroup.mem_inf.mpr ⟨?_, mul_mem b.2 hk₀K⟩)
    rw [hbk]
    exact mul_mem (conj_mem_socle hG hint (mem_jHull_of_mem_longInv ht) (hout b b.2 hb))
      (hout k₀ hk₀K hk₀O)

end KernelStatement

section Assembly

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

@[expose] noncomputable def holtDataOfOddOrbits (hG : IsStarGroup G Ω)
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (α : Ω)
    (D' : HoltData (orbitGroup G α) (OddOrbits G α)) {t : G} (ht : t ∈ longInv G Ω) :
    HoltData G Ω :=
  have := hG.isPretransitive
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  { ι := D'.ι
    Ψc := D'.Ψc
    coord := fun ω => D'.coord (orbitPoint G α ω)
    ρ := fun i => liftRho D' hG hint i
    L := fun i => splitL D' i
    t := t
    t_mem := ht
    coord_eq_iff := fun ω ω' => by
      rw [D'.coord_eq_iff, orbit_jOddCore_eq_singleton hOX, Set.mem_singleton_iff, eq_comm,
        blockCoset_eq_blockCoset_iff, orbit_jOddCore_eq hG]
    coord_surjective := fun c => by
      obtain ⟨b, rfl⟩ := D'.coord_surjective c
      obtain ⟨ω, rfl⟩ := blockCoset_surjective (le_sup_left : stabilizer G α ≤ _) b
      exact ⟨ω, rfl⟩
    coord_smul := fun h ω i => by
      rw [orbitPoint_smul, liftRho_apply]
      exact D'.coord_smul ⟨orbitRestrict G α h, _⟩ (orbitPoint G α ω) i
    L_le := fun i => splitL_le_jHull hG i
    oddCore_le := fun i => le_sup_left
    le_normalizer := fun i => le_normalizer_splitL hG hint i
    le_ker := fun i j hij h hh => liftRho_eq_one_of_mem_splitL hG hint hij hh
    inf_ker := fun i => le_antisymm (fun h hh => mem_jOddCore_of_mem_splitL hG hO hint hh.1 hh.2)
      fun h hh => ⟨le_sup_left (a := jOddCore G Ω) hh,
        liftRho_eq_one_of_mem_jOddCore hG hint hh i⟩
    factor := fun i => by
      rw [factorImage_splitL hG hO hint i]
      exact D'.factor i
    sup_eq := sup_splitL_sup_zpowers hG hO hint ht
    inner := fun i hi => by
      rw [factorImage_splitL hG hO hint i] at hi ⊢
      exact (D'.rho_mem_M_iff (orbitRestrict_mem_longInv hG hint ht) i).mpr hi
    ker_outer := fun h => by
      simp only [factorImage_splitL hG hO hint] at h
      exact jOrbitKernel_eq_jOddCore_of_isOuterFactor hG hO hint ht h
    ker_inner := fun h => by
      simp only [factorImage_splitL hG hO hint] at h
      exact ⟨mem_socle_sup_jOrbitKernel hG hO hint ht h,
        fun _ => relIndex_jOddCore_jOrbitKernel_eq_two' hG hO hint ht h⟩ }

theorem holtStructure_of_oddOrbits (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) (α : Ω)
    (hΨ : HoltStructure ↥(toPermHom G (OddOrbits G α)).range (OddOrbits G α)) :
    HoltStructure G Ω := by
  obtain ⟨D'⟩ := hΨ
  obtain ⟨t, ht⟩ := hG.longInv_nonempty
  exact ⟨holtDataOfOddOrbits hG hO hint α D' ht⟩

end Assembly

section Lemma24iv

theorem exists_conj_eq_mul_of_odd_orderOf {X : Type*} [Group X] {o t : X} (ho : Odd (orderOf o))
    (ht : t * t = 1) (hot : o * t * (o * t) = 1) :
    ∃ p ∈ Subgroup.zpowers o, p * t * p⁻¹ = o * t := by
  obtain ⟨k, hk⟩ := ho
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have h1 : t * o * t⁻¹ = o⁻¹ := by
    rw [hti]
    apply eq_inv_of_mul_eq_one_left
    calc t * o * t * o = t * (o * t * (o * t)) * t⁻¹ := by group
      _ = 1 := by rw [hot, mul_one, mul_inv_cancel]
  have h2 : t * o ^ (k + 1) * t⁻¹ = (o ^ (k + 1))⁻¹ := by rw [← conj_pow, h1, inv_pow]
  have h3 : o ^ (k + 1) * o ^ (k + 1) = o := by
    rw [← pow_add, show k + 1 + (k + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  refine ⟨o ^ (k + 1), Subgroup.npow_mem_zpowers o _, ?_⟩
  have h4 : t * (o ^ (k + 1))⁻¹ * t⁻¹ = o ^ (k + 1) := by
    rw [show t * (o ^ (k + 1))⁻¹ * t⁻¹ = (t * o ^ (k + 1) * t⁻¹)⁻¹ by group, h2, inv_inv]
  calc o ^ (k + 1) * t * (o ^ (k + 1))⁻¹ = o ^ (k + 1) * (t * (o ^ (k + 1))⁻¹ * t⁻¹) * t := by
        group
    _ = o * t := by rw [h4, h3]

variable {G : Type*} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω] {α : Ω} {D' : HoltData (orbitGroup G α) (OddOrbits G α)}

theorem not_mem_blockEven_of_mem_longInvAt [IsPretransitive G Ω]
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) {β : Ω} {u : G} (hu : u ∈ longInvAt G Ω β) :
    u ∉ blockEven G β := fun huE => by
  have huF := mem_fixingSubgroup_of_mem_blockEven huE (n := 1)
    (by rw [pow_one, sq, mul_self_eq_one_of_mem_longInv hu.1])
  have h3 := three_le_card_orbit_pPrimeCore hO β
  rw [Nat.card_coe_set_eq] at h3
  obtain ⟨δ, hδ, hδβ⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := orbit (CFSG.pPrimeCore 2 G) β) (by omega) β
  exact hδβ ((smul_eq_iff_of_mem_longInvAt hu δ).mp ((mem_fixingSubgroup_iff G).mp huF δ hδ))

omit [Finite Ω] [FaithfulSMul G Ω] in
theorem exists_smul_eq_self_orbitRestrict_eq (hG : IsStarGroup G Ω) {β : Ω} {g : G}
    (hg : g ∈ jHull G Ω)
    (hgb : orbitRestrict G α g • @orbitPoint G _ Ω _ hG.isPretransitive α β =
      @orbitPoint G _ Ω _ hG.isPretransitive α β) :
    ∃ g' ∈ jHull G Ω, g' • β = β ∧ orbitRestrict G α g' = orbitRestrict G α g := by
  have := hG.isPretransitive
  have hgB := (orbitRestrict_smul_orbitPoint_eq_iff (α := α)).mp hgb
  have hgβ : β ∈ orbit (jOddCore G Ω) (g • β) := by
    rw [orbit_jOddCore_eq hG, orbit_eq_iff.mpr (mem_stabilizer_iff.mp hgB ▸
      Set.smul_mem_smul_set (mem_orbit_self β))]
    exact mem_orbit_self β
  obtain ⟨⟨o, ho⟩, hoβ⟩ := hgβ
  refine ⟨o * g, mul_mem (jOddCore_le_jHull ho) hg, by rw [mul_smul]; exact hoβ, ?_⟩
  rw [map_mul, (orbitRestrict_eq_one_iff α).mpr
    (pPrimeCore_le_oddOrbitsKernel α (jOddCore_le_pPrimeCore ho)), one_mul]

theorem exists_mem_longInvAt_orbitRestrict_eq (D' : HoltData (orbitGroup G α) (OddOrbits G α))
    (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {β : Ω} {s : orbitGroup G α}
    (hs : s ∈ longInvAt (orbitGroup G α) (OddOrbits G α)
      (@orbitPoint G _ Ω _ hG.isPretransitive α β)) :
    ∃ w ∈ longInvAt G Ω β, orbitRestrict G α w = s := by
  have := hG.isPretransitive
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  obtain ⟨x, hx⟩ := hG.longInvAt_nonempty β
  have hxX := orbitRestrict_mem_longInvAt hG hint hx (α := α)
  obtain ⟨l, hl, hlb, hly⟩ := D'.exists_conj_rho_eq hxX Finset.univ
    (fun i => D'.ρ i ⟨s, mem_jHull_of_mem_longInv hs.1⟩) (fun i _ => D'.rho_mem_longInvAt hs i)
    (fun i _ => ⟨_, rfl⟩)
  have heq : (l : orbitGroup G α) * orbitRestrict G α x * (l : orbitGroup G α)⁻¹ = s := by
    have h1 := HoltData.eq_one_of_forall_rho_eq_one (D := D') hOX
      (h := (l * ⟨_, mem_jHull_of_mem_longInv hxX.1⟩ * l⁻¹)⁻¹ *
        ⟨s, mem_jHull_of_mem_longInv hs.1⟩)
      fun i => by rw [map_mul, map_inv, hly i (Finset.mem_univ i), inv_mul_cancel]
    exact congrArg Subtype.val (inv_mul_eq_one.mp h1)
  rw [hOX, bot_sup_eq, Finset.sup_univ_eq_iSup] at hl
  obtain ⟨g, hg, hgl⟩ := (iSup_le fun i => L_le_map_jHull hG hO hint D' i) hl
  obtain ⟨g', hg', hg'β, hg'l⟩ := exists_smul_eq_self_orbitRestrict_eq hG hg
    (α := α) (by rw [hgl]; exact hlb)
  refine ⟨g' * x * g'⁻¹, by have h1 := conj_mem_longInvAt hx g'; rwa [hg'β] at h1, ?_⟩
  rw [map_mul, map_mul, map_inv, hg'l, hgl, heq]

theorem mem_closure_longInvAt_sup_jOrbitKernel (D' : HoltData (orbitGroup G α) (OddOrbits G α))
    (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {β : Ω} {v : G} (hv : v ∈ jHull G Ω)
    (hvB : v ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) β)) (hv2 : v * v = 1) :
    v ∈ Subgroup.closure (longInvAt G Ω β) ⊔ jOrbitKernel G Ω := by
  have := hG.isPretransitive
  have hOX := jOddCore_orbitGroup_eq_bot hG hO hint α
  have hvX : orbitRestrict G α v ∈ jHull (orbitGroup G α) (OddOrbits G α) :=
    map_jHull_le hG hint α ⟨v, hv, rfl⟩
  have h1 := D'.mem_closure_longInv_stabilizer_of_mul_self hOX hvX
    ((orbitRestrict_smul_orbitPoint_eq_iff (α := α)).mpr hvB)
    (by rw [← map_mul, hv2, map_one])
  have hle : Subgroup.closure (longInvAt (orbitGroup G α) (OddOrbits G α) (orbitPoint G α β)) ≤
      (Subgroup.closure (longInvAt G Ω β)).map (orbitRestrict G α) := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨w, hw, hws⟩ := exists_mem_longInvAt_orbitRestrict_eq D' hG hO hint hs
    exact ⟨w, Subgroup.subset_closure hw, hws⟩
  obtain ⟨x, hx, hxv⟩ := hle h1
  rw [show v = x * (x⁻¹ * v) by group]
  refine mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right ?_)
  rw [jOrbitKernel_eq_inf_oddOrbitsKernel hG α]
  exact Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (Subgroup.closure_mono
    (longInvAt_subset_longInv β) hx)) hv,
      (orbitRestrict_eq_one_iff α).mp (by rw [map_mul, map_inv, hxv, inv_mul_cancel])⟩

theorem jOrbitKernel_le_closure_longInvAt_sup (hG : IsStarGroup G Ω)
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω)
    (D' : HoltData (orbitGroup G α) (OddOrbits G α)) (β : Ω) :
    jOrbitKernel G Ω ≤ Subgroup.closure (longInvAt G Ω β) ⊔ jOddCore G Ω := by
  have := hG.isPretransitive
  intro k hk
  by_cases hkO : k ∈ jOddCore G Ω
  · exact Subgroup.mem_sup_right hkO
  obtain ⟨t, ht⟩ := hG.longInv_nonempty
  have hall : ∀ i, ¬ IsOuterFactor (D'.M i) := fun i hi =>
    hkO ((jOrbitKernel_eq_jOddCore_of_isOuterFactor (D' := D') hG hO hint ht ⟨i, hi⟩) ▸ hk)
  obtain ⟨u₀, hu₀⟩ := hG.longInvAt_nonempty β
  obtain ⟨y, hy, hyu⟩ := exists_mem_blockEven_orbitRestrict_eq (D' := D') hG hO hint hall hu₀
  obtain ⟨hyL, hyE⟩ := Subgroup.mem_inf.mp hy
  have hyH : y ∈ jHull G Ω := Subgroup.closure_mono (longInvAt_subset_longInv β) hyL
  have hk₁K : y⁻¹ * u₀ ∈ jOrbitKernel G Ω := by
    rw [jOrbitKernel_eq_inf_oddOrbitsKernel hG α]
    exact Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hyH) (mem_jHull_of_mem_longInv hu₀.1),
      (orbitRestrict_eq_one_iff α).mp (by rw [map_mul, map_inv, hyu, inv_mul_cancel])⟩
  have hk₁O : y⁻¹ * u₀ ∉ jOddCore G Ω := fun h =>
    not_mem_blockEven_of_mem_longInvAt hO hu₀ (by
      rw [show u₀ = y * (y⁻¹ * u₀) by group]
      exact mul_mem hyE (pPrimeCore_le_blockEven β (jOddCore_le_pPrimeCore h)))
  have hout : ∀ k' ∈ jOrbitKernel G Ω, k' ∉ jOddCore G Ω →
      t * k' ∈ jOddCore G Ω ⊔ ⨆ i, splitL D' i := fun k' hk' hk'O =>
    (mem_socle_or_t_mul_mem hG hO hint ht (jOrbitKernel_le_jHull hk')).resolve_left fun hkS =>
      hk'O (socle_inf_jOrbitKernel hG hO hint (Subgroup.mem_inf.mpr ⟨hkS, hk'⟩))
  have hkk : (y⁻¹ * u₀)⁻¹ * k ∈ jOddCore G Ω := by
    refine socle_inf_jOrbitKernel (D' := D') hG hO hint (Subgroup.mem_inf.mpr ⟨?_, mul_mem
      (inv_mem hk₁K) hk⟩)
    rw [show (y⁻¹ * u₀)⁻¹ * k = (t * (y⁻¹ * u₀))⁻¹ * (t * k) by group]
    exact mul_mem (inv_mem (hout _ hk₁K hk₁O)) (hout k hk hkO)
  rw [show k = y⁻¹ * u₀ * ((y⁻¹ * u₀)⁻¹ * k) by group]
  exact mul_mem (Subgroup.mem_sup_left (mul_mem (inv_mem hyL) (Subgroup.subset_closure hu₀)))
    (Subgroup.mem_sup_right hkk)

theorem parity_of_mem_closure_longInvAt_sup (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (D : HoltData G Ω) {β : Ω} {u₀ : G} (hu₀ : u₀ ∈ longInvAt G Ω β) {x : G}
    (hx : x ∈ Subgroup.closure (longInvAt G Ω β) ⊔ jOddCore G Ω) :
    (x ∈ blockEven G β ∧ x ∈ D.socPre) ∨ (x * u₀ ∈ blockEven G β ∧ x * u₀ ∈ D.socPre) := by
  have := hG.isPretransitive
  have hu₀B := mem_stabilizer_orbit_of_mem_longInvAt hu₀
  have hu₀H := mem_jHull_of_mem_longInv hu₀.1
  have huu : u₀ * u₀ = 1 := mul_self_eq_one_of_mem_longInv hu₀.1
  have hcE : ∀ y ∈ blockEven G β, u₀⁻¹ * y * u₀⁻¹⁻¹ ∈ blockEven G β := fun y hy =>
    conj_mem_blockEven (inv_mem hu₀B) hy
  have hcS : ∀ y ∈ D.socPre, u₀⁻¹ * y * u₀⁻¹⁻¹ ∈ D.socPre := fun y hy =>
    D.conj_mem_socPre (inv_mem hu₀H) hy
  have hOE : jOddCore G Ω ≤ blockEven G β :=
    jOddCore_le_pPrimeCore.trans (pPrimeCore_le_blockEven β)
  have hOS : jOddCore G Ω ≤ D.socPre := D.jOddCore_le_socPre
  have e1 : ∀ a b : G, a * b = a * u₀ * (u₀⁻¹ * (b * u₀) * u₀⁻¹⁻¹) := fun a b => by
    calc a * b = a * u₀ * u₀⁻¹ * b * (u₀ * u₀) := by rw [huu]; group
      _ = _ := by group
  have key : ∀ y ∈ Subgroup.closure (longInvAt G Ω β), (y ∈ blockEven G β ∧ y ∈ D.socPre) ∨
      (y * u₀ ∈ blockEven G β ∧ y * u₀ ∈ D.socPre) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem w hw => exact Or.inr ⟨mul_mem_blockEven hO hw.1 hu₀.1
        (mem_stabilizer_orbit_of_mem_longInvAt hw) hu₀B, D.mul_mem_socPre hG hw.1 hu₀.1⟩
    | one => exact Or.inl ⟨one_mem _, one_mem _⟩
    | mul a b _ _ ha hb =>
      rcases ha with ⟨haE, haS⟩ | ⟨haE, haS⟩ <;> rcases hb with ⟨hbE, hbS⟩ | ⟨hbE, hbS⟩
      · exact Or.inl ⟨mul_mem haE hbE, mul_mem haS hbS⟩
      · refine Or.inr ⟨?_, ?_⟩ <;> rw [mul_assoc]
        exacts [mul_mem haE hbE, mul_mem haS hbS]
      · have e : a * b * u₀ = a * u₀ * (u₀⁻¹ * b * u₀⁻¹⁻¹) := by group
        refine Or.inr ⟨?_, ?_⟩ <;> rw [e]
        exacts [mul_mem haE (hcE b hbE), mul_mem haS (hcS b hbS)]
      · refine Or.inl ⟨?_, ?_⟩ <;> rw [e1 a b]
        exacts [mul_mem haE (hcE _ hbE), mul_mem haS (hcS _ hbS)]
    | inv a _ ha =>
      rcases ha with ⟨haE, haS⟩ | ⟨haE, haS⟩
      · exact Or.inl ⟨inv_mem haE, inv_mem haS⟩
      · have e : a⁻¹ * u₀ = (u₀⁻¹ * (a * u₀) * u₀⁻¹⁻¹)⁻¹ := by
          calc a⁻¹ * u₀ = (u₀ * u₀)⁻¹ * a⁻¹ * u₀ := by rw [huu, inv_one, one_mul]
            _ = _ := by group
        refine Or.inr ⟨?_, ?_⟩ <;> rw [e]
        exacts [inv_mem (hcE _ haE), inv_mem (hcS _ haS)]
  obtain ⟨y, hy, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  rcases key y hy with ⟨hyE, hyS⟩ | ⟨hyE, hyS⟩
  · exact Or.inl ⟨mul_mem hyE (hOE ho), mul_mem hyS (hOS ho)⟩
  · have e : y * o * u₀ = y * u₀ * (u₀⁻¹ * o * u₀⁻¹⁻¹) := by group
    have ho' : u₀⁻¹ * o * u₀⁻¹⁻¹ ∈ jOddCore G Ω := jOddCore_normal.conj_mem o ho u₀⁻¹
    refine Or.inr ⟨?_, ?_⟩ <;> rw [e]
    exacts [mul_mem hyE (hOE ho'), mul_mem hyS (hOS ho')]

end Lemma24iv

section Lemma24ivMain

variable {G : Type} [Group G] [Finite G] {Ω : Type} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

omit [FaithfulSMul G Ω] in
theorem holtStructure_orbitGroup (hG : IsStarGroup G Ω) (hO : CFSG.pPrimeCore 2 G ≠ ⊥)
    (hint : ¬ IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {d : ℕ}
    (hB : HoltTheorem1Below (Nat.card G) d) (α : Ω) :
    HoltStructure (orbitGroup G α) (OddOrbits G α) := by
  have := hG.isPretransitive
  have h1 := one_lt_index_oddOrbitsStabilizer (α := α) hint
  have hodd := odd_index_of_le hG.odd_card (le_sup_left : stabilizer G α ≤ oddOrbitsStabilizer G α)
  have h3 : 3 ≤ (oddOrbitsStabilizer G α).index := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm] at h1 ⊢
    omega
  refine hB _ _ (Or.inl ?_) (isStarGroup_range_quotient hG le_sup_left h3)
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (toPermHom G (OddOrbits G α))).toEquiv]
  exact card_quotient_oddOrbitsKernel_lt hO α

theorem holtStructure_of_pPrimeCore_ne_bot_of_below (hG : IsStarGroup G Ω)
    (hO : CFSG.pPrimeCore 2 G ≠ ⊥) {d : ℕ} (hB : HoltTheorem1Below (Nat.card G) d) :
    HoltStructure G Ω := by
  by_cases htr : IsPretransitive (CFSG.pPrimeCore 2 G) Ω
  · exact hG.holtStructure_of_isPretransitive_pPrimeCore htr
  obtain ⟨t, ht⟩ := hG.longInv_nonempty
  obtain ⟨α, -⟩ := exists_mem_longInvAt ht
  exact holtStructure_of_oddOrbits hG hO htr α (holtStructure_orbitGroup hG hO htr hB α)

private theorem mem_longInv_of_isPretransitive
    (htr : IsPretransitive (CFSG.pPrimeCore 2 G) Ω) {t v : G} (ht : t ∈ longInv G Ω)
    (hv : v ∈ jHull G Ω) (hvv : v * v = 1) (hvO : v ∉ jOddCore G Ω) : v ∈ longInv G Ω := by
  have hH := (lemma_2_3_i htr ht).2
  rw [hH] at hv
  obtain ⟨o, ho, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have htt := mul_self_eq_one_of_mem_longInv ht
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · exact absurd (by rw [zpow_mul, zpow_two, htt, one_zpow, mul_one]; exact ho) hvO
  · rw [zpow_add_one, zpow_mul, zpow_two, htt, one_zpow, one_mul] at hvv ⊢
    have hoodd : Odd (orderOf o) :=
      Odd.of_dvd_nat odd_card_jOddCore (Subgroup.orderOf_dvd_natCard _ ho)
    obtain ⟨p, -, hp⟩ := exists_conj_eq_mul_of_odd_orderOf hoodd htt hvv
    rw [← hp]
    exact conj_mem_longInv ht p

theorem HoltData.lemma_2_4_iv (hG : IsStarGroup G Ω)
    (hB : HoltTheorem1Below (Nat.card G) (Nat.card Ω + 1)) (D : HoltData G Ω) {v : G}
    (hv : v ∈ jHull G Ω) (hv2 : orderOf v = 2) {ω : Ω}
    (hvω : v • ω ∈ orbit ↥(jOddCore G Ω) ω) :
    (v ∈ jOddCore G Ω ⊔ ⨆ i, D.L i → ∀ ω' ∈ orbit ↥(jOddCore G Ω) ω, v • ω' = ω') ∧
      (v ∉ jOddCore G Ω ⊔ ⨆ i, D.L i →
        ∃! ω', ω' ∈ orbit ↥(jOddCore G Ω) ω ∧ v • ω' = ω') := by
  have := hG.isPretransitive
  have hvv : v * v = 1 := by rw [← sq, ← hv2, pow_orderOf_eq_one]
  have hvO : v ∉ jOddCore G Ω := fun h => by
    have h1 := Subgroup.orderOf_dvd_natCard _ h
    rw [hv2] at h1
    obtain ⟨m, hm⟩ := odd_card_jOddCore (G := G) (Ω := Ω)
    omega
  by_cases hN : CFSG.pPrimeCore 2 G = ⊥
  · have hO : jOddCore G Ω = ⊥ := le_bot_iff.mp (hN ▸ jOddCore_le_pPrimeCore)
    rw [orbit_jOddCore_eq_singleton hO] at hvω ⊢
    have hvω' : v • ω = ω := hvω
    refine ⟨fun _ ω' hω' => ?_, fun _ => ⟨ω, ⟨rfl, hvω'⟩, fun ω' hω' => hω'.1⟩⟩
    rw [Set.mem_singleton_iff.mp hω', hvω']
  by_cases htr : IsPretransitive (CFSG.pPrimeCore 2 G) Ω
  · have hOt := hG.isPretransitive_jOddCore_iff.mpr htr
    have hS : jOddCore G Ω ⊔ ⨆ i, D.L i = jOddCore G Ω := by
      have := D.isEmpty_ι_iff.mpr hOt
      rw [iSup_of_empty, sup_bot_eq]
    rw [hS]
    refine ⟨fun h => absurd h hvO, fun _ => ?_⟩
    obtain ⟨ω₀, hω₀⟩ := exists_mem_longInvAt
      (mem_longInv_of_isPretransitive htr D.t_mem hv hvv hvO)
    exact ⟨ω₀, ⟨hOt.exists_smul_eq ω ω₀, hω₀.2⟩, fun ω' hω' =>
      (smul_eq_iff_of_mem_longInvAt hω₀ ω').mp hω'.2⟩
  have hO' : jOddCore G Ω ≠ ⊥ := fun h => hN ((Subgroup.eq_bot_iff_forall _).mpr fun n hn =>
    eq_of_smul_eq_smul (α := Ω) fun γ => by
      have h1 : n • γ ∈ orbit (jOddCore G Ω) γ := by
        rw [orbit_jOddCore_eq hG]
        exact ⟨⟨n, hn⟩, rfl⟩
      rw [orbit_jOddCore_eq_singleton h] at h1
      rw [one_smul]
      exact h1)
  obtain ⟨D'⟩ := holtStructure_orbitGroup hG hN htr hB ω
  obtain ⟨u₀, hu₀⟩ := hG.longInvAt_nonempty ω
  have hvB : v ∈ stabilizer G (orbit (CFSG.pPrimeCore 2 G) ω) := by
    have := CFSG.pPrimeCore_normal (p := 2) (G := G)
    rw [orbit_jOddCore_eq hG] at hvω
    rw [mem_stabilizer_iff, smul_orbit_eq_orbit_smul, orbit_eq_iff]
    exact hvω
  have hvC := (sup_le le_sup_left (jOrbitKernel_le_closure_longInvAt_sup hG hN htr D' ω))
    (mem_closure_longInvAt_sup_jOrbitKernel D' hG hN htr hv hvB hvv)
  have hu₀S : u₀ ∉ D.socPre := fun h => by
    obtain ⟨c, hc, hcu⟩ := D.exists_conj_t_mul_mem_jOddCore hG hu₀.1
    refine hO' (D.t_mem_socPre_iff.mp ?_).1
    rw [show D.t = c⁻¹ * (c * D.t * c⁻¹ * u₀ * u₀⁻¹) * c by group]
    exact mul_mem (mul_mem (inv_mem hc) (mul_mem (D.jOddCore_le_socPre hcu) (inv_mem h))) hc
  rcases parity_of_mem_closure_longInvAt_sup hG hN D hu₀ hvC with ⟨hvE, hvS⟩ | ⟨hvE, hvS⟩
  · refine ⟨fun _ ω' hω' => ?_, fun h => absurd hvS h⟩
    have hvF := mem_fixingSubgroup_of_mem_blockEven hvE (n := 1) (by rw [pow_one, sq, hvv])
    rw [orbit_jOddCore_eq hG] at hω'
    exact (mem_fixingSubgroup_iff G).mp hvF ω' hω'
  · have hvS' : v ∉ D.socPre := fun h => hu₀S (by
      rw [show u₀ = v⁻¹ * (v * u₀) by group]
      exact mul_mem (inv_mem h) hvS)
    refine ⟨fun h => absurd h hvS', fun _ => ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨h1, ha⟩ := mem_blockEven.mp hvE
    have hu₀B := mem_stabilizer_orbit_of_mem_longInvAt hu₀
    have huu := mul_self_eq_one_of_mem_longInv hu₀.1
    set a := blockRestrict G ω ⟨v * u₀, h1⟩
    set b := blockRestrict G ω ⟨u₀, hu₀B⟩
    have hab : a * b = blockRestrict G ω ⟨v, hvB⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext (by rw [Subgroup.coe_mul, mul_assoc, huu, mul_one])
    have hbb : b * b = 1 := by
      rw [← map_mul, show (⟨u₀, hu₀B⟩ : stabilizer G (orbit (CFSG.pPrimeCore 2 G) ω)) *
        ⟨u₀, hu₀B⟩ = 1 from Subtype.ext huu, map_one]
    have hab2 : a * b * (a * b) = 1 := by
      rw [hab, ← map_mul, show (⟨v, hvB⟩ : stabilizer G (orbit (CFSG.pPrimeCore 2 G) ω)) *
        ⟨v, hvB⟩ = 1 from Subtype.ext hvv, map_one]
    have haodd : Odd (orderOf a) := Odd.of_dvd_nat
      (Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card) (Subgroup.orderOf_dvd_natCard _ ha)
    obtain ⟨p, -, hp⟩ := exists_conj_eq_mul_of_odd_orderOf haodd hbb hab2
    have key : ∀ δ : orbit (CFSG.pPrimeCore 2 G) ω, v • (δ : Ω) =
        (((a * b : blockGroup G ω) : Equiv.Perm (orbit (CFSG.pPrimeCore 2 G) ω)) δ : Ω) :=
      fun δ => by
      rw [hab]
      rfl
    have hbω : ((b : blockGroup G ω) : Equiv.Perm (orbit (CFSG.pPrimeCore 2 G) ω))
        ⟨ω, mem_orbit_self ω⟩ =
        ⟨ω, mem_orbit_self ω⟩ := Subtype.ext hu₀.2
    refine ⟨(((p : blockGroup G ω) : Equiv.Perm (orbit (CFSG.pPrimeCore 2 G) ω))
      ⟨ω, mem_orbit_self ω⟩ : Ω), ⟨?_, ?_⟩, ?_⟩
    · rw [orbit_jOddCore_eq hG]
      exact Subtype.coe_prop _
    · rw [key, ← hp]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, Equiv.Perm.coe_inv,
        Equiv.symm_apply_apply, hbω]
    · rintro ω' ⟨hω'B, hω'⟩
      rw [orbit_jOddCore_eq hG] at hω'B
      have h2 : ((p * b * p⁻¹ : blockGroup G ω) : Equiv.Perm (orbit (CFSG.pPrimeCore 2 G) ω))
          ⟨ω', hω'B⟩ = ⟨ω', hω'B⟩ := by
        rw [hp]
        exact Subtype.ext ((key ⟨ω', hω'B⟩).symm.trans hω')
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply] at h2
      have h3 := congrArg
        (((p : blockGroup G ω) : Equiv.Perm (orbit (CFSG.pPrimeCore 2 G) ω)).symm) h2
      simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply] at h3
      have h5 := (smul_eq_iff_of_mem_longInvAt hu₀ _).mp (congrArg Subtype.val h3)
      have h6 : ((p : blockGroup G ω) : Equiv.Perm (orbit (CFSG.pPrimeCore 2 G) ω))⁻¹
          ⟨ω', hω'B⟩ = ⟨ω, mem_orbit_self ω⟩ := Subtype.ext h5
      rw [← h6, Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

end Lemma24ivMain

end CFSG.Holt.H78
