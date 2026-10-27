module

public import CFSG.Holt.H78.Sec4LineDiag
public import CFSG.Holt.H78.Sec4LineTheorem
public import CFSG.Holt.H78.Sec4Toolkit
public import CFSG.Holt.H78.Lemma27Real
public import CFSG.Holt.H78.Sec4CCL
public import CFSG.Holt.H78.KernelSylow
public import CFSG.Holt.H78.Sec4KnownKV
public import CFSG.Holt.H78.Sec4U34

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open Equiv Equiv.Perm
open scoped Pointwise

section Klein

variable {Z : Type*} [DecidableEq Z]

theorem mem_map_kleinFour_iff {Y : Type*} [Fintype Y] [DecidableEq Y] (hY : Nat.card Y = 4)
    {σ : Perm Y} : σ ∈ (alternatingGroup.kleinFour Y).map (alternatingGroup Y).subtype ↔
      σ = 1 ∨ (σ * σ = 1 ∧ ∀ y, σ y ≠ y) := by
  have hcard : Fintype.card Y = 4 := by rwa [← Nat.card_eq_fintype_card]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [alternatingGroup.coe_kleinFour_of_card_eq_four hY] at hg
    rcases hg with hg | hg
    · left
      rw [Set.mem_singleton_iff.mp hg]
      rfl
    · right
      have hct : (g : Perm Y).cycleType = {2, 2} := hg
      refine ⟨?_, fun y hy => ?_⟩
      · have h2 : orderOf (g : Perm Y) = 2 := by
          rw [← lcm_cycleType, hct]
          rfl
        show (g : Perm Y) * g = 1
        rw [← pow_two, ← h2, pow_orderOf_eq_one]
      · have hs : (g : Perm Y).support.card = 4 := by
          rw [← sum_cycleType, hct]
          rfl
        have hsupp : (g : Perm Y).support = Finset.univ :=
          Finset.eq_univ_of_card _ (by rw [hs, hcard])
        exact (mem_support.mp (hsupp ▸ Finset.mem_univ y)) hy
  · rintro (rfl | ⟨h2, hf⟩)
    · exact ⟨1, Subgroup.one_mem _, rfl⟩
    · have hc := two_mul_card_cycleType_of_forall_apply_ne h2 hf
      have hct : σ.cycleType = {2, 2} := by
        rw [CFSG.OddStandard.AltStdSec.cycleType_eq_replicate_of_mul_self h2,
          show Multiset.card σ.cycleType = 2 by omega]
        rfl
      have hsign : σ ∈ alternatingGroup Y := by
        rw [mem_alternatingGroup, sign_of_cycleType, hct]
        decide
      refine ⟨⟨σ, hsign⟩, ?_, rfl⟩
      rw [alternatingGroup.coe_kleinFour_of_card_eq_four hY]
      exact Or.inr hct

structure IsKleinOn (S : Set Z) (σ : Perm Z) : Prop where
  mapsTo : ∀ s ∈ S, σ s ∈ S
  cases : (∀ s ∈ S, σ s = s) ∨ ∀ s ∈ S, σ s ≠ s ∧ σ (σ s) = s

omit [DecidableEq Z] in
theorem mem_iff_of_mapsTo {S : Set Z} (hS : S.Finite) {σ : Perm Z} (hσ : ∀ s ∈ S, σ s ∈ S)
    (z : Z) : σ z ∈ S ↔ z ∈ S := by
  refine ⟨fun hz => ?_, hσ z⟩
  have hbij := (hS.injOn_iff_bijOn_of_mapsTo (f := σ) hσ).mp σ.injective.injOn
  obtain ⟨s, hs, hsz⟩ := hbij.surjOn hz
  rwa [← σ.injective hsz]

theorem IsKleinOn.restrict_mem {S : Set Z} [Fintype ↥S] (hS4 : S.ncard = 4) {σ : Perm Z}
    (hσ : IsKleinOn S σ) :
    σ.subtypePerm (mem_iff_of_mapsTo (Set.finite_of_ncard_ne_zero (by omega)) hσ.mapsTo) ∈
      (alternatingGroup.kleinFour ↥S).map (alternatingGroup ↥S).subtype := by
  rw [mem_map_kleinFour_iff (by rw [Nat.card_coe_set_eq, hS4])]
  rcases hσ.cases with h | h
  · left
    ext s
    exact h s s.2
  · right
    refine ⟨Equiv.ext fun s => Subtype.ext ?_, fun s hs => (h s s.2).1 (congrArg Subtype.val hs)⟩
    exact (h s s.2).2

theorem IsKleinOn.mul {S : Set Z} (hS4 : S.ncard = 4) {σ τ : Perm Z} (hσ : IsKleinOn S σ)
    (hτ : IsKleinOn S τ) : IsKleinOn S (σ * τ) := by
  classical
  have hfin : S.Finite := Set.finite_of_ncard_ne_zero (by omega)
  have : Fintype ↥S := hfin.fintype
  have h := Subgroup.mul_mem _ (hσ.restrict_mem hS4) (hτ.restrict_mem hS4)
  rw [subtypePerm_mul, mem_map_kleinFour_iff (by rw [Nat.card_coe_set_eq, hS4])] at h
  refine ⟨fun s hs => hσ.mapsTo _ (hτ.mapsTo s hs), ?_⟩
  rcases h with h | ⟨h2, hf⟩
  · left
    intro s hs
    exact congrArg Subtype.val (congrArg (fun π : Perm ↥S => π ⟨s, hs⟩) h)
  · right
    intro s hs
    refine ⟨fun h' => hf ⟨s, hs⟩ (Subtype.ext h'), ?_⟩
    exact congrArg Subtype.val (congrArg (fun π : Perm ↥S => π ⟨s, hs⟩) h2)

omit [DecidableEq Z] in
theorem isKleinOn_one (S : Set Z) : IsKleinOn S 1 :=
  ⟨fun _ hs => hs, Or.inl fun _ _ => rfl⟩

omit [DecidableEq Z] in
theorem IsKleinOn.apply_apply {S : Set Z} {σ : Perm Z} (hσ : IsKleinOn S σ) {s : Z}
    (hs : s ∈ S) : σ (σ s) = s := by
  rcases hσ.cases with h | h
  · rw [h s hs, h s hs]
  · exact (h s hs).2

omit [DecidableEq Z] in
theorem IsKleinOn.inv {S : Set Z} {σ : Perm Z} (hσ : IsKleinOn S σ) :
    IsKleinOn S σ⁻¹ := by
  have hinv : ∀ s ∈ S, σ⁻¹ s = σ s := fun s hs => by
    rw [Perm.inv_eq_iff_eq, hσ.apply_apply hs]
  refine ⟨fun s hs => by rw [hinv s hs]; exact hσ.mapsTo s hs, ?_⟩
  rcases hσ.cases with h | h
  · exact Or.inl fun s hs => by rw [hinv s hs, h s hs]
  · refine Or.inr fun s hs => ⟨by rw [hinv s hs]; exact (h s hs).1, ?_⟩
    rw [hinv s hs, hinv _ (hσ.mapsTo s hs), (h s hs).2]

theorem IsKleinOn.mul_apply_ne {S : Set Z} (hS4 : S.ncard = 4) {σ τ : Perm Z}
    (hσ : IsKleinOn S σ) (hτ : IsKleinOn S τ) {s₀ : Z} (hs₀ : s₀ ∈ S) (hne : σ s₀ ≠ τ s₀) :
    ∀ s ∈ S, (σ * τ) s ≠ s := by
  rcases (hσ.mul hS4 hτ).cases with h | h
  · exfalso
    apply hne
    have h1 : σ (τ s₀) = s₀ := h s₀ hs₀
    calc σ s₀ = σ (σ (τ s₀)) := by rw [h1]
      _ = τ s₀ := hσ.apply_apply (hτ.mapsTo s₀ hs₀)
  · exact fun s hs => (h s hs).1

omit [DecidableEq Z] in
theorem IsKleinOn.pow_odd_apply {S : Set Z} {σ : Perm Z} (hσ : IsKleinOn S σ) {m : ℕ}
    (hm : Odd m) {s : Z} (hs : s ∈ S) : (σ ^ m) s = σ s := by
  obtain ⟨j, rfl⟩ := hm
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by ring, pow_add, Perm.mul_apply, pow_two,
      Perm.mul_apply, hσ.apply_apply hs, ih]

end Klein

namespace LineDiagData

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  {x : Ω} {L : Set Ω} {Θ : Finset Ω} {V : Subgroup G} {g : G} {y' : Ω}

omit [Finite G] [Fintype Ω] in
theorem isPGroup (hD : LineDiagData G x L Θ V g y') : IsPGroup 2 V := hD.sylow.2.1

omit [Finite G] [Fintype Ω] in
theorem le_closure (hD : LineDiagData G x L Θ V g y') :
    V ≤ Subgroup.closure (longInvAt G Ω x) := hD.sylow.1.trans inf_le_left

omit [Finite G] [Fintype Ω] in
theorem le_fixingSubgroup (hD : LineDiagData G x L Θ V g y') :
    V ≤ fixingSubgroup G (Θ : Set Ω) := hD.sylow.1.trans inf_le_right

omit [Finite G] [Fintype Ω] in
theorem x_mem (hD : LineDiagData G x L Θ V g y') : x ∈ fixSet Ω V := fun _ hv =>
  closure_longInvAt_le_stabilizer_point x (hD.le_closure hv)

omit [Finite G] [Fintype Ω] in
theorem mem_of_mem_Θ (hD : LineDiagData G x L Θ V g y') {θ : Ω} (hθ : θ ∈ Θ) :
    θ ∈ fixSet Ω V := fun _ hv => (mem_fixingSubgroup_iff G).mp (hD.le_fixingSubgroup hv) θ hθ

omit [Finite G] [Fintype Ω] in
theorem y'_mem (hD : LineDiagData G x L Θ V g y') : y' ∈ fixSet Ω V := hD.fix_y'

omit [Finite G] [Fintype Ω] in
theorem eq_or_mem_of_mem (hD : LineDiagData G x L Θ V g y') {y : Ω} (hy : y ∈ L)
    (hyV : y ∈ fixSet Ω V) : y = x ∨ y ∈ Θ := by
  by_cases hyx : y = x
  · exact Or.inl hyx
  · exact Or.inr (hD.mem_Θ_of_fix y hy hyx hyV)

omit [Finite G] in
theorem six_le (hD : LineDiagData G x L Θ V g y') : 6 ≤ Nat.card (fixSet Ω V) := by
  have hy'Θ : y' ∉ Θ := fun h => hD.notMem_y' (hD.mem_Θ y' h).1
  have hxy' : x ≠ y' := fun h => hD.notMem_y' (h ▸ hD.mem)
  have hxΘ : x ∉ Θ := fun h => (hD.mem_Θ x h).2 rfl
  have hcard : (insert x (insert y' Θ)).card = 6 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy', hxΘ]), Finset.card_insert_of_notMem hy'Θ,
      hD.card_Θ]
  have hsub : ((insert x (insert y' Θ) : Finset Ω) : Set Ω) ⊆ fixSet Ω V := by
    intro z hz
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hz
    rcases hz with rfl | rfl | hz
    · exact hD.x_mem
    · exact hD.y'_mem
    · exact hD.mem_of_mem_Θ hz
  rw [Nat.card_coe_set_eq, ← hcard, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

omit [Finite G] in
theorem three_le (hD : LineDiagData G x L Θ V g y') : 3 ≤ Nat.card (fixSet Ω V) := by
  have := hD.six_le
  omega

omit [Finite G] [Fintype Ω] in
theorem ne_bot (hD : LineDiagData G x L Θ V g y') : V ≠ ⊥ := by
  rintro rfl
  obtain ⟨z, hz, hz'⟩ := exists_mem_notMem_of_card_lt_ncard (L := L) (insert x Θ)
    ((Finset.card_insert_le x Θ).trans_lt (by rw [hD.card_Θ]; have := hD.isLine.seven_le; omega))
  simp only [Finset.mem_insert, not_or] at hz'
  exact hz'.2 (hD.mem_Θ_of_fix z hz hz'.1 fun v hv => by
    rw [Subgroup.mem_bot.mp hv, one_smul])

omit [Finite G] [Fintype Ω] in
theorem smul_eq_or_mem (hD : LineDiagData G x L Θ V g y') {p : Ω} (hp : p ∈ L) {c : G}
    (hc : c ∈ longInvAt G Ω p) (hcV : c ∈ Subgroup.centralizer (V : Set G)) {y : Ω}
    (hy : y = x ∨ y ∈ Θ) : c • y = x ∨ c • y ∈ Θ := by
  have hyL : y ∈ L := by
    rcases hy with rfl | hy
    · exact hD.mem
    · exact (hD.mem_Θ y hy).1
  have hyV : y ∈ fixSet Ω V := by
    rcases hy with rfl | hy
    · exact hD.x_mem
    · exact hD.mem_of_mem_Θ hy
  refine hD.eq_or_mem_of_mem ?_ (smul_mem_fixSet_of_mem_normalizer
    (Subgroup.centralizer_le_normalizer _ hcV) hyV)
  rw [← hD.isLine.jClosed p hp c hc]
  exact Set.smul_mem_smul_set hyL

section Section

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {x : Ω} {L : Set Ω} {Θ : Finset Ω} {V : Subgroup G} {g : G} {y' : Ω}

omit [Finite G] [Fintype Ω] [FaithfulSMul G Ω] in
theorem ncard_preimage_Θ (hD : LineDiagData G x L Θ V g y') :
    (((↑) : fixSet Ω V → Ω) ⁻¹' (Θ : Set Ω)).ncard = 4 := by
  rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective, Set.ncard_coe_finset,
    hD.card_Θ]
  intro θ hθ
  exact ⟨⟨θ, hD.mem_of_mem_Θ hθ⟩, rfl⟩

theorem isKleinOn_of_mem_longInvAt (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    {π : centralizerImage Ω V}
    (hπ : π ∈ longInvAt (centralizerImage Ω V) (fixSet Ω V) ⟨x, hD.x_mem⟩) :
    IsKleinOn (((↑) : fixSet Ω V → Ω) ⁻¹' (Θ : Set Ω)) (π : Perm (fixSet Ω V)) := by
  obtain ⟨c, hc, hcV, hcπ⟩ :=
    (hS.mem_longInvAt_centralizerImage_iff hD.isPGroup hD.three_le π).mp hπ
  have hcx : c • x = x := hc.2
  have hfix : ∀ {ω : Ω}, c • ω = ω → ω = x := fun h => hc.1.2.unique h hcx
  have hc2 : c * c = 1 := mul_self_eq_one_of_mem_longInv hc.1
  refine ⟨fun u hu => ?_, Or.inr fun u hu => ⟨fun h => ?_, ?_⟩⟩
  · show ((π : Perm (fixSet Ω V)) u : Ω) ∈ (Θ : Set Ω)
    rw [hcπ]
    rcases hD.smul_eq_or_mem hD.mem hc hcV (Or.inr hu) with h | h
    · exfalso
      have : (u : Ω) = x := by
        rw [← hcx] at h
        exact smul_left_cancel c h
      exact (hD.mem_Θ _ hu).2 this
    · exact h
  · have := congrArg Subtype.val h
    rw [hcπ] at this
    exact (hD.mem_Θ _ hu).2 (hfix this)
  · apply Subtype.ext
    rw [hcπ, hcπ, ← mul_smul, hc2, one_smul]

theorem isKleinOn_of_mem_closure (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    {a : centralizerImage Ω V}
    (ha : a ∈ Subgroup.closure (longInvAt (centralizerImage Ω V) (fixSet Ω V) ⟨x, hD.x_mem⟩)) :
    IsKleinOn (((↑) : fixSet Ω V → Ω) ⁻¹' (Θ : Set Ω)) (a : Perm (fixSet Ω V)) := by
  induction ha using Subgroup.closure_induction with
  | mem π hπ => exact hD.isKleinOn_of_mem_longInvAt hS hπ
  | one => exact isKleinOn_one _
  | mul a b _ _ iha ihb => exact iha.mul hD.ncard_preimage_Θ ihb
  | inv a _ iha => exact iha.inv

theorem exists_lift (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    {a : centralizerImage Ω V}
    (ha : a ∈ Subgroup.closure (longInvAt (centralizerImage Ω V) (fixSet Ω V) ⟨x, hD.x_mem⟩)) :
    ∃ c ∈ Subgroup.closure {c : G | c ∈ longInvAt G Ω x ∧ c ∈ Subgroup.centralizer (V : Set G)},
      ∀ ω : fixSet Ω V, ((a : Perm (fixSet Ω V)) ω : Ω) = c • (ω : Ω) := by
  induction ha using Subgroup.closure_induction with
  | mem π hπ =>
    obtain ⟨c, hc, hcV, hcπ⟩ :=
      (hS.mem_longInvAt_centralizerImage_iff hD.isPGroup hD.three_le π).mp hπ
    exact ⟨c, Subgroup.subset_closure ⟨hc, hcV⟩, hcπ⟩
  | one => exact ⟨1, Subgroup.one_mem _, fun ω => by simp⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨c₁, hc₁, h₁⟩ := iha
    obtain ⟨c₂, hc₂, h₂⟩ := ihb
    refine ⟨c₁ * c₂, Subgroup.mul_mem _ hc₁ hc₂, fun ω => ?_⟩
    rw [Subgroup.coe_mul, Perm.mul_apply, h₁, h₂, mul_smul]
  | inv a _ iha =>
    obtain ⟨c, hc, h⟩ := iha
    refine ⟨c⁻¹, Subgroup.inv_mem _ hc, fun ω => ?_⟩
    rw [eq_inv_smul_iff, ← h, Subgroup.coe_inv, ← Perm.mul_apply, mul_inv_cancel,
      Perm.one_apply]

theorem odd_orderOf_of_mem_closure (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    {a : centralizerImage Ω V}
    (ha : a ∈ Subgroup.closure (longInvAt (centralizerImage Ω V) (fixSet Ω V) ⟨x, hD.x_mem⟩))
    {θ : fixSet Ω V} (hθ : (θ : Ω) ∈ Θ) (hfix : (a : Perm (fixSet Ω V)) θ = θ) :
    Odd (orderOf a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := hD.isKleinOn_of_mem_closure hS ha
  have hΘ : ∀ u : fixSet Ω V, (u : Ω) ∈ Θ → (a : Perm (fixSet Ω V)) u = u := by
    rcases hK.cases with h | h
    · exact fun u hu => h u hu
    · exact absurd hfix (h θ hθ).1
  obtain ⟨c, hc, hca⟩ := hD.exists_lift hS ha
  set AG := Subgroup.closure {c : G | c ∈ longInvAt G Ω x ∧ c ∈ Subgroup.centralizer (V : Set G)}
  have hAGK : AG ≤ Subgroup.closure (longInvAt G Ω x) :=
    (Subgroup.closure_le _).mpr fun c hc => Subgroup.subset_closure hc.1
  have hAGC : AG ≤ Subgroup.centralizer (V : Set G) :=
    (Subgroup.closure_le _).mpr fun c hc => hc.2
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  set c₂ := c ^ m
  have hc₂ : IsPGroup 2 (Subgroup.zpowers c₂) := by
    have h1 : c₂ ^ 2 ^ k = 1 := by
      rw [← pow_mul, mul_comm, ← hkm, pow_orderOf_eq_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  have hpow : ∀ n : ℕ, ∀ ω : fixSet Ω V,
      (((a : Perm (fixSet Ω V)) ^ n) ω : Ω) = c ^ n • (ω : Ω) := by
    intro n
    induction n with
    | zero => intro ω; simp
    | succ n ih => intro ω; rw [pow_succ, Perm.mul_apply, ih, hca, pow_succ, mul_smul]
  have hc₂F : c₂ ∈ fixingSubgroup G (Θ : Set Ω) := by
    refine (mem_fixingSubgroup_iff G).mpr fun θ' hθ' => ?_
    have := hpow m ⟨θ', hD.mem_of_mem_Θ hθ'⟩
    rw [Equiv.Perm.pow_apply_eq_self_of_apply_eq_self (hΘ _ hθ') m] at this
    exact this.symm
  have hc₂K : c₂ ∈ Subgroup.closure (longInvAt G Ω x) := Subgroup.pow_mem _ (hAGK hc) m
  have hc₂C : c₂ ∈ Subgroup.centralizer (V : Set G) := Subgroup.pow_mem _ (hAGC hc) m
  have hsup : IsPGroup 2 (V ⊔ Subgroup.zpowers c₂ : Subgroup G) :=
    hD.isPGroup.to_sup_of_normal_left' hc₂ (Subgroup.zpowers_le.mpr
      (Subgroup.centralizer_le_normalizer _ hc₂C))
  have hle : V ⊔ Subgroup.zpowers c₂ ≤
      Subgroup.closure (longInvAt G Ω x) ⊓ fixingSubgroup G (Θ : Set Ω) :=
    sup_le hD.sylow.1 (Subgroup.zpowers_le.mpr ⟨hc₂K, hc₂F⟩)
  have heq := hD.sylow.2.2 _ hle hsup le_sup_left
  have hc₂V : c₂ ∈ V := heq ▸ (le_sup_right : Subgroup.zpowers c₂ ≤ V ⊔ _)
    (Subgroup.mem_zpowers c₂)
  have ham : a ^ m = 1 := by
    apply Subtype.ext
    ext ω
    rw [Subgroup.coe_pow, hpow m ω]
    exact ω.2 c₂ hc₂V
  exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ham)

end Section

section Orbits

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {x : Ω} {L : Set Ω} {Θ : Finset Ω} {V : Subgroup G} {g : G} {y' : Ω}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_eq_of_mapsTo {Γ : Set Ω} (hΓ : Γ.Finite) {h : G} (hh : ∀ γ ∈ Γ, h • γ ∈ Γ) :
    h • Γ = Γ := by
  refine Set.eq_of_subset_of_ncard_le ?_ (by rw [Set.ncard_smul_set]) hΓ
  rintro _ ⟨γ, hγ, rfl⟩
  exact hh γ hγ

omit [Finite G] [FaithfulSMul G Ω] in
theorem exists_two_longInvAt (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    {θ : Ω} (hθ : θ ∈ Θ) :
    ∃ u ∈ longInvAt G Ω θ, u ∈ Subgroup.centralizer (V : Set G) ∧
      ∃ c ∈ longInvAt G Ω θ, c ∈ Subgroup.centralizer (V : Set G) ∧ c • x ≠ u • x := by
  have hθL := (hD.mem_Θ θ hθ).1
  have hθx := (hD.mem_Θ θ hθ).2
  have hVθ : V ≤ stabilizer G θ := fun v hv => hD.mem_of_mem_Θ hθ v hv
  obtain ⟨u, hu, huV⟩ := hS.star.star θ V hD.isPGroup hVθ hD.three_le
  have hufix : ∀ {ω : Ω}, u • ω = ω → ω = θ := fun h => hu.1.2.unique h hu.2
  set p := u • x with hpdef
  have hpΘ : p ∈ Θ := by
    rcases hD.smul_eq_or_mem hθL hu huV (Or.inl rfl) with h | h
    · exact absurd (hufix h) (Ne.symm hθx)
    · exact h
  have hpθ : p ≠ θ := fun h => hθx (by
    have : u • x = u • θ := by rw [← hpdef, h, hu.2]
    exact (smul_left_cancel u this).symm ▸ rfl)
  have hcard : ((Θ.erase θ).erase p).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpθ, hpΘ⟩),
      Finset.card_erase_of_mem hθ, hD.card_Θ]
  obtain ⟨q, r, hqr, hqr'⟩ := Finset.card_eq_two.mp hcard
  have hq : q ∈ (Θ.erase θ).erase p := by rw [hqr']; exact Finset.mem_insert_self _ _
  have hr : r ∈ (Θ.erase θ).erase p := by rw [hqr']; simp
  simp only [Finset.mem_erase] at hq hr
  obtain ⟨hqp, hqθ, hqΘ⟩ := hq
  obtain ⟨hrp, hrθ, hrΘ⟩ := hr
  have hΘeq : ∀ {z : Ω}, z ∈ Θ → z = θ ∨ z = p ∨ z = q ∨ z = r := fun {z} hz => by
    by_cases hzθ : z = θ
    · exact Or.inl hzθ
    by_cases hzp : z = p
    · exact Or.inr (Or.inl hzp)
    have : z ∈ (Θ.erase θ).erase p := Finset.mem_erase.mpr ⟨hzp, Finset.mem_erase.mpr ⟨hzθ, hz⟩⟩
    rw [hqr', Finset.mem_insert, Finset.mem_singleton] at this
    exact Or.inr (Or.inr this)
  obtain ⟨k, hkK, hk⟩ := hD.isLine.threeCycle θ hθL p (hD.mem_Θ p hpΘ).1 q (hD.mem_Θ q hqΘ).1 r
    (hD.mem_Θ r hrΘ).1 hpθ hqθ hrθ (Ne.symm hqp) (Ne.symm hrp) hqr
  have hkθ : k • θ = θ := closure_longInvAt_le_stabilizer_point θ hkK
  set Γ : Set Ω := insert x (Θ : Set Ω) with hΓdef
  have hΓfin : Γ.Finite := Set.toFinite _
  have hxpqr : x ≠ p ∧ x ≠ q ∧ x ≠ r := ⟨fun h => (hD.mem_Θ p hpΘ).2 h.symm,
    fun h => (hD.mem_Θ q hqΘ).2 h.symm, fun h => (hD.mem_Θ r hrΘ).2 h.symm⟩
  have hkx : k • x = x := by
    rw [hk x hD.mem, cyc3_apply_of_ne hxpqr.1 hxpqr.2.1 hxpqr.2.2]
  have hkΓ : k • Γ = Γ := smul_eq_of_mapsTo hΓfin fun γ hγ => by
    have hγL : γ ∈ L := by
      rcases hγ with rfl | hγ
      · exact hD.mem
      · exact (hD.mem_Θ γ hγ).1
    rw [hk γ hγL]
    rcases hγ with rfl | hγ
    · rw [cyc3_apply_of_ne hxpqr.1 hxpqr.2.1 hxpqr.2.2]
      exact Set.mem_insert _ _
    · right
      rcases hΘeq hγ with rfl | rfl | rfl | rfl
      · rw [cyc3_apply_of_ne (Ne.symm hpθ) (Ne.symm hqθ) (Ne.symm hrθ)]
        exact hγ
      · rw [cyc3_apply_left (Ne.symm hqp) (Ne.symm hrp)]
        exact hqΘ
      · rw [cyc3_apply_mid (Ne.symm hrp) hqr]
        exact hrΘ
      · rw [cyc3_apply_right]
        exact hpΘ
  have huΓ : u • Γ = Γ := smul_eq_of_mapsTo hΓfin fun γ hγ => by
    have := hD.smul_eq_or_mem hθL hu huV (show γ = x ∨ γ ∈ Θ from hγ)
    rcases this with h | h
    · rw [h]; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ h
  set y₀ := k * u * k⁻¹
  have hy₀ : y₀ ∈ longInvAt G Ω θ := by
    have := conj_mem_longInvAt hu k
    rwa [hkθ] at this
  have hy₀Γ : y₀ ∈ stabilizer G Γ := by
    rw [mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff.mpr hkΓ.symm, huΓ, hkΓ]
  have hVΓ : V ≤ fixingSubgroup G Γ := fun v hv => (mem_fixingSubgroup_iff G).mpr
    fun γ hγ => by
      rcases hγ with rfl | hγ
      · exact hD.x_mem v hv
      · exact hD.mem_of_mem_Θ hγ v hv
  have h3 : 3 ≤ Nat.card Γ := by
    have hxΘ : x ∉ Θ := fun h => (hD.mem_Θ x h).2 rfl
    rw [Nat.card_coe_set_eq, hΓdef, Set.ncard_insert_of_notMem hxΘ, Set.ncard_coe_finset,
      hD.card_Θ]
    omega
  obtain ⟨c, hc, hcV, hcy⟩ := hS.frattini h3 hD.isPGroup hVΓ hy₀.1 hy₀Γ
  refine ⟨u, hu, huV, c, ⟨hc, ?_⟩, hcV, ?_⟩
  · rw [hcy θ (Set.mem_insert_of_mem _ hθ), hy₀.2]
  · rw [hcy x (Set.mem_insert _ _), mul_smul, mul_smul,
      show k⁻¹ • x = x by rw [inv_smul_eq_iff, hkx], ← hpdef, hk p (hD.mem_Θ p hpΘ).1,
      cyc3_apply_left (Ne.symm hqp) (Ne.symm hrp)]
    exact hqp

theorem notMem_orbit (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y') {θ₁ θ₂ : Ω}
    (h₁ : θ₁ ∈ Θ) (h₂ : θ₂ ∈ Θ) (h12 : θ₁ ≠ θ₂) :
    (⟨θ₂, hD.mem_of_mem_Θ h₂⟩ : fixSet Ω V) ∉
      orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ⟨θ₁, hD.mem_of_mem_Θ h₁⟩ := by
  intro horb
  obtain ⟨u, hu, huV, c, hc, hcV, hcu⟩ := hD.exists_two_longInvAt hS h₁
  have hstar := hS.star_centralizerImage hD.isPGroup hD.three_le
  have hJ : ∀ {d : G} (hd : d ∈ longInvAt G Ω θ₁) (hdV : d ∈ Subgroup.centralizer (V : Set G)),
      (centralizerImageElt (Ω := Ω) hdV : centralizerImage Ω V) ∈
        longInvAt (centralizerImage Ω V) (fixSet Ω V) ⟨θ₁, hD.mem_of_mem_Θ h₁⟩ :=
    fun {d} hd hdV => (hS.mem_longInvAt_centralizerImage_iff hD.isPGroup hD.three_le _).mpr
      ⟨d, hd, hdV, fun _ => rfl⟩
  obtain ⟨m, hm, hmfix⟩ := exists_odd_pow_smul_eq_of_mem_longInvAt hstar (hJ hu huV) (hJ hc hcV)
  set S₁ : Set (fixSet Ω V) :=
    ((↑) : fixSet Ω V → Ω) ⁻¹' (insert x ((Θ.erase θ₁ : Finset Ω) : Set Ω)) with hS₁def
  have hxΘ : x ∉ Θ := fun h => (hD.mem_Θ x h).2 rfl
  have hθ₁x : θ₁ ≠ x := (hD.mem_Θ θ₁ h₁).2
  have hS₁ : S₁.ncard = 4 := by
    rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective,
      Set.ncard_insert_of_notMem (by simp [hxΘ]), Set.ncard_coe_finset,
      Finset.card_erase_of_mem h₁, hD.card_Θ]
    rintro z (rfl | hz)
    · exact ⟨⟨_, hD.x_mem⟩, rfl⟩
    · exact ⟨⟨z, hD.mem_of_mem_Θ (Finset.mem_of_mem_erase hz)⟩, rfl⟩
  have hmemS₁ : ∀ {ω : fixSet Ω V}, ω ∈ S₁ ↔ (ω : Ω) = x ∨ ((ω : Ω) ≠ θ₁ ∧ (ω : Ω) ∈ Θ) :=
    fun {ω} => by simp [hS₁def, and_comm]
  have hKl : ∀ {d : G} (hd : d ∈ longInvAt G Ω θ₁) (hdV : d ∈ Subgroup.centralizer (V : Set G)),
      IsKleinOn S₁ ((centralizerImageElt (Ω := Ω) hdV : centralizerImage Ω V) :
        Perm (fixSet Ω V)) := by
    intro d hd hdV
    have hdfix : ∀ {ω : Ω}, d • ω = ω → ω = θ₁ := fun h => hd.1.2.unique h hd.2
    have hne : ∀ {ω : fixSet Ω V}, ω ∈ S₁ → (ω : Ω) ≠ θ₁ := fun {ω} hω => by
      rcases hmemS₁.mp hω with h | h
      · rw [h]; exact Ne.symm hθ₁x
      · exact h.1
    refine ⟨fun ω hω => ?_, Or.inr fun ω hω => ⟨fun h => hne hω (hdfix (congrArg Subtype.val h)),
      Subtype.ext ?_⟩⟩
    · have hω' : (ω : Ω) = x ∨ (ω : Ω) ∈ Θ := by
        rcases hmemS₁.mp hω with h | h
        · exact Or.inl h
        · exact Or.inr h.2
      refine hmemS₁.mpr ?_
      show d • (ω : Ω) = x ∨ (d • (ω : Ω) ≠ θ₁ ∧ d • (ω : Ω) ∈ Θ)
      have hdθ : d • (ω : Ω) ≠ θ₁ := fun h => hne hω (by
        rw [← hd.2] at h
        exact smul_left_cancel d h)
      rcases hD.smul_eq_or_mem (hD.mem_Θ θ₁ h₁).1 hd hdV hω' with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hdθ, h⟩
    · show d • d • (ω : Ω) = ω
      rw [← mul_smul, mul_self_eq_one_of_mem_longInv hd.1, one_smul]
  have hx₁ : (⟨x, hD.x_mem⟩ : fixSet Ω V) ∈ S₁ := hmemS₁.mpr (Or.inl rfl)
  have hθ₂ : (⟨θ₂, hD.mem_of_mem_Θ h₂⟩ : fixSet Ω V) ∈ S₁ := hmemS₁.mpr (Or.inr ⟨Ne.symm h12, h₂⟩)
  have hdiff : ((centralizerImageElt (Ω := Ω) hcV : centralizerImage Ω V) : Perm (fixSet Ω V))
      ⟨x, hD.x_mem⟩ ≠ ((centralizerImageElt (Ω := Ω) huV : centralizerImage Ω V) :
        Perm (fixSet Ω V)) ⟨x, hD.x_mem⟩ := fun h => hcu (congrArg Subtype.val h)
  have hmove := (hKl hc hcV).mul_apply_ne hS₁ (hKl hu huV) hx₁ hdiff _ hθ₂
  have h2 := hmfix _ horb
  rw [Subgroup.smul_def, Subgroup.coe_pow, Subgroup.coe_mul, Perm.smul_def,
    ((hKl hc hcV).mul hS₁ (hKl hu huV)).pow_odd_apply hm hθ₂] at h2
  exact hmove h2

end Orbits

end LineDiagData

section Finite

theorem exists_mem_alternatingGroup_inf_stabilizer_pow_four {Δ : Type*} [Fintype Δ]
    [DecidableEq Δ] (h7 : 7 ≤ Fintype.card Δ) (b : Δ) :
    ∃ σ ∈ alternatingGroup Δ ⊓ stabilizer (Perm Δ) b, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := Finset.univ.erase b) (n := 6)
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ]; omega)
  let f : Fin 6 ≃ {y // y ∈ s} :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hcard])).symm
  set σ₀ : Perm (Fin 6) := swap 0 1 * swap 0 2 * swap 0 3 * swap 4 5
  have h4 : σ₀ ^ 4 = 1 := by decide
  have h2 : σ₀ ^ 2 ≠ 1 := by decide
  have hsign : sign σ₀ = 1 := by decide
  refine ⟨σ₀.extendDomain f, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [mem_alternatingGroup, sign_extendDomain, hsign]
  · rw [mem_stabilizer_iff, Perm.smul_def]
    exact Perm.extendDomain_apply_not_subtype _ _ fun hb => by simpa using hs hb
  · have := map_pow (extendDomainHom f) σ₀ 4
    rw [extendDomainHom_apply, extendDomainHom_apply, h4, extendDomain_one] at this
    exact this.symm
  · intro h
    have := map_pow (extendDomainHom f) σ₀ 2
    rw [extendDomainHom_apply, extendDomainHom_apply, h] at this
    exact h2 (extendDomainHom_injective f (by rw [map_one, extendDomainHom_apply, this]))

theorem mem_of_odd_orderOf_of_relIndex_le_two {K : Type*} [Group K] [Finite K]
    {N J : Subgroup K} (h2 : N.relIndex J ≤ 2) {y : K} (hy : y ∈ J) (hodd : Odd (orderOf y)) :
    y ∈ N := by
  have hpos : (N.subgroupOf J).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : (N.subgroupOf J).index ≤ 2 := h2
  have hsq : y ^ 2 ∈ N := by
    rcases (by omega : (N.subgroupOf J).index = 1 ∨ (N.subgroupOf J).index = 2) with h | h
    · rw [Subgroup.index_eq_one] at h
      have : (⟨y ^ 2, J.pow_mem hy 2⟩ : J) ∈ N.subgroupOf J := by rw [h]; exact Subgroup.mem_top _
      exact this
    · exact (Subgroup.sq_mem_of_index_two h ⟨y, hy⟩ : _)
  obtain ⟨k, hk⟩ := hodd
  have : y = (y ^ 2) ^ (k + 1) := by
    rw [← pow_mul, show 2 * (k + 1) = orderOf y + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  rw [this]
  exact N.pow_mem hsq _

end Finite

namespace LineDiagData

section Known

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {x : Ω} {L : Set Ω} {Θ : Finset Ω} {V : Subgroup G} {g : G} {y' : Ω}

theorem card_le_four (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y') {P : Type*}
    [Group P] (f : jHull (centralizerImage Ω V) (fixSet Ω V) →* P) {ι' : Type*} [Finite ι']
    (s : ι' → jHull (centralizerImage Ω V) (fixSet Ω V))
    (hs : ∀ j, (s j : centralizerImage Ω V) ∈
      Subgroup.closure (longInvAt (centralizerImage Ω V) (fixSet Ω V) ⟨x, hD.x_mem⟩))
    (hf : ∀ j j', j ≠ j' → ¬ Odd (orderOf ((f (s j))⁻¹ * f (s j')))) : Nat.card ι' ≤ 4 := by
  obtain ⟨θ₀, hθ₀⟩ : Θ.Nonempty := Finset.card_pos.mp (by rw [hD.card_Θ]; norm_num)
  set Θ' : Set (fixSet Ω V) := ((↑) : fixSet Ω V → Ω) ⁻¹' (Θ : Set Ω)
  have hK := fun j => hD.isKleinOn_of_mem_closure hS (hs j)
  set θ₀' : fixSet Ω V := ⟨θ₀, hD.mem_of_mem_Θ hθ₀⟩
  let φ : ι' → Θ' := fun j => ⟨(s j : Perm (fixSet Ω V)) θ₀', (hK j).mapsTo θ₀' hθ₀⟩
  by_contra hlt
  have : Fintype ι' := Fintype.ofFinite ι'
  have : Fintype Θ' := Fintype.ofFinite Θ'
  obtain ⟨j, j', hjj', heq⟩ := Fintype.exists_ne_map_eq_of_card_lt φ
    (by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
      hD.ncard_preimage_Θ]; omega)
  set w := (s j)⁻¹ * s j'
  have hw : (w : centralizerImage Ω V) ∈
      Subgroup.closure (longInvAt (centralizerImage Ω V) (fixSet Ω V) ⟨x, hD.x_mem⟩) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (hs j)) (hs j')
  have hwfix : ((w : centralizerImage Ω V) : Perm (fixSet Ω V)) θ₀' = θ₀' := by
    have h1 : (s j : Perm (fixSet Ω V)) θ₀' = (s j' : Perm (fixSet Ω V)) θ₀' :=
      congrArg Subtype.val heq
    simp only [w, Subgroup.coe_mul, Subgroup.coe_inv, Perm.mul_apply]
    rw [Perm.inv_eq_iff_eq]
    exact h1.symm
  have hodd := hD.odd_orderOf_of_mem_closure hS hw hθ₀ hwfix
  rw [Subgroup.orderOf_coe] at hodd
  apply hf j j' hjj'
  rw [← map_inv, ← map_mul]
  exact Odd.of_dvd_nat hodd (orderOf_map_dvd f w)

theorem sq_eq_one_of_pow_four (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    {P : Type*} [Group P] (f : jHull (centralizerImage Ω V) (fixSet Ω V) →* P)
    {a : jHull (centralizerImage Ω V) (fixSet Ω V)}
    (ha : (a : centralizerImage Ω V) ∈
      Subgroup.closure (longInvAt (centralizerImage Ω V) (fixSet Ω V) ⟨x, hD.x_mem⟩))
    (h4 : f a ^ 4 = 1) : f a ^ 2 = 1 := by
  obtain ⟨θ₀, hθ₀⟩ : Θ.Nonempty := Finset.card_pos.mp (by rw [hD.card_Θ]; norm_num)
  have ha2 : ((a ^ 2 : jHull (centralizerImage Ω V) (fixSet Ω V)) : centralizerImage Ω V) ∈
      Subgroup.closure (longInvAt (centralizerImage Ω V) (fixSet Ω V) ⟨x, hD.x_mem⟩) := by
    rw [Subgroup.coe_pow]
    exact Subgroup.pow_mem _ ha 2
  have hfix : (((a ^ 2 : jHull (centralizerImage Ω V) (fixSet Ω V)) : centralizerImage Ω V) :
      Perm (fixSet Ω V)) ⟨θ₀, hD.mem_of_mem_Θ hθ₀⟩ = ⟨θ₀, hD.mem_of_mem_Θ hθ₀⟩ := by
    rw [Subgroup.coe_pow, Subgroup.coe_pow, pow_two, Perm.mul_apply]
    exact (hD.isKleinOn_of_mem_closure hS ha).apply_apply hθ₀
  have hodd := hD.odd_orderOf_of_mem_closure hS ha2 hθ₀ hfix
  rw [Subgroup.orderOf_coe] at hodd
  have hdvd := orderOf_map_dvd f (a ^ 2)
  rw [map_pow] at hdvd
  have h2 : orderOf (f a ^ 2) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [← pow_mul]; exact h4)
  have hodd' := Odd.of_dvd_nat hodd hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd'
    exact absurd hodd' (by decide)

theorem exists_mem_longInvAt_x (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y') :
    ∃ s₀ : jHull (centralizerImage Ω V) (fixSet Ω V),
      (s₀ : centralizerImage Ω V) ∈ longInvAt (centralizerImage Ω V) (fixSet Ω V)
        ⟨x, hD.x_mem⟩ := by
  obtain ⟨u, hu, huV⟩ := hS.star.star x V hD.isPGroup (fun v hv => hD.x_mem v hv) hD.three_le
  have hû := (hS.mem_longInvAt_centralizerImage_iff hD.isPGroup hD.three_le
    (centralizerImageElt (Ω := Ω) huV) (a := ⟨x, hD.x_mem⟩)).mpr ⟨u, hu, huV, fun _ => rfl⟩
  exact ⟨⟨_, mem_jHull_of_mem_longInv hû.1⟩, hû⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem not_odd_orderOf_of_sq_eq_one {P : Type*} [Group P] {w : P} (h1 : w ≠ 1)
    (h2 : w ^ 2 = 1) : ¬ Odd (orderOf w) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime h2 h1]
  decide

end Known

section Components

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {x : Ω} {L : Set Ω} {Θ : Finset Ω} {V : Subgroup G} {g : G} {y' : Ω}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem sq_inv_mul_eq_one_of_mem_longInvAt {Δ : Type*} [Fintype Δ] {M : Subgroup (Perm Δ)}
    (hM : IsNaturalSE M) {b : Δ} {z z' : M} (hz : z ∈ longInvAt M Δ b)
    (hz' : z' ∈ longInvAt M Δ b) : ((z : Perm Δ)⁻¹ * z') ^ 2 = 1 := by
  have hzz : (z : Perm Δ) * z = 1 :=
    mul_self_eq_one_of_mem_longInv (mem_longInv_subgroup_perm_iff.mp hz.1)
  have hzz' : (z' : Perm Δ) * z' = 1 :=
    mul_self_eq_one_of_mem_longInv (mem_longInv_subgroup_perm_iff.mp hz'.1)
  have h1 := hM.mem_mulLongInvClosure_of_mul_self z.2 hz.2 hzz
  have h2 := hM.mem_mulLongInvClosure_of_mul_self z'.2 hz'.2 hzz'
  have hc := hM.commute_of_mem_mulLongInvClosure h1 h2
  have hinv : (z : Perm Δ)⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  rw [hinv, pow_two, mul_assoc, ← mul_assoc (z' : Perm Δ), ← hc, mul_assoc, hzz', mul_one,
    hzz]

omit [Finite G] [FaithfulSMul G Ω] in
theorem exists_lift_rho (hD : LineDiagData G x L Θ V g y')
    (D : HoltData (centralizerImage Ω V) (fixSet Ω V))
    {s₀ : jHull (centralizerImage Ω V) (fixSet Ω V)}
    (hs₀ : (s₀ : centralizerImage Ω V) ∈ longInvAt (centralizerImage Ω V) (fixSet Ω V)
      ⟨x, hD.x_mem⟩) (i : D.ι) {z : Perm (D.Ψc i)} (hz : z ∈ (D.ρ i).range)
    (hzJ : z ∈ longInvAt (Perm (D.Ψc i)) (D.Ψc i) (D.coord ⟨x, hD.x_mem⟩ i)) :
    ∃ s : jHull (centralizerImage Ω V) (fixSet Ω V),
      (s : centralizerImage Ω V) ∈ longInvAt (centralizerImage Ω V) (fixSet Ω V)
        ⟨x, hD.x_mem⟩ ∧ D.ρ i s = z := by
  obtain ⟨t, ht, hρ⟩ := D.exists_mem_longInvAt_rho_eq ⟨x, hD.x_mem⟩
    (Function.update (fun j => D.ρ j s₀) i z)
    (fun j => by
      rcases eq_or_ne j i with rfl | hj
      · rw [Function.update_self]; exact hz
      · rw [Function.update_of_ne hj]; exact ⟨s₀, rfl⟩)
    (fun j => by
      rcases eq_or_ne j i with rfl | hj
      · rw [Function.update_self]; exact hzJ
      · rw [Function.update_of_ne hj]; exact D.rho_mem_longInvAt hs₀ j)
  exact ⟨t, ht, by rw [hρ i, Function.update_self]⟩

omit [Finite G] [FaithfulSMul G Ω] in
theorem exists_lift_rho₂ (hD : LineDiagData G x L Θ V g y')
    (D : HoltData (centralizerImage Ω V) (fixSet Ω V))
    {s₀ : jHull (centralizerImage Ω V) (fixSet Ω V)}
    (hs₀ : (s₀ : centralizerImage Ω V) ∈ longInvAt (centralizerImage Ω V) (fixSet Ω V)
      ⟨x, hD.x_mem⟩) {i j : D.ι} (hij : i ≠ j) {z : Perm (D.Ψc i)} (hz : z ∈ (D.ρ i).range)
    (hzJ : z ∈ longInvAt (Perm (D.Ψc i)) (D.Ψc i) (D.coord ⟨x, hD.x_mem⟩ i))
    {z' : Perm (D.Ψc j)} (hz' : z' ∈ (D.ρ j).range)
    (hz'J : z' ∈ longInvAt (Perm (D.Ψc j)) (D.Ψc j) (D.coord ⟨x, hD.x_mem⟩ j)) :
    ∃ s : jHull (centralizerImage Ω V) (fixSet Ω V),
      (s : centralizerImage Ω V) ∈ longInvAt (centralizerImage Ω V) (fixSet Ω V)
        ⟨x, hD.x_mem⟩ ∧ D.ρ i s = z ∧ D.ρ j s = z' := by
  set y := Function.update (Function.update (fun k => D.ρ k s₀) i z) j z'
  have hyi : y i = z := by
    simp only [y]
    rw [Function.update_of_ne hij, Function.update_self]
  have hyj : y j = z' := by simp only [y, Function.update_self]
  have hyk : ∀ k, k ≠ i → k ≠ j → y k = D.ρ k s₀ := fun k hki hkj => by
    simp only [y]
    rw [Function.update_of_ne hkj, Function.update_of_ne hki]
  obtain ⟨t, ht, hρ⟩ := D.exists_mem_longInvAt_rho_eq ⟨x, hD.x_mem⟩ y
    (fun k => by
      by_cases hki : k = i
      · subst hki; rw [hyi]; exact hz
      by_cases hkj : k = j
      · subst hkj; rw [hyj]; exact hz'
      rw [hyk k hki hkj]; exact ⟨s₀, rfl⟩)
    (fun k => by
      by_cases hki : k = i
      · subst hki; rw [hyi]; exact hzJ
      by_cases hkj : k = j
      · subst hkj; rw [hyj]; exact hz'J
      rw [hyk k hki hkj]; exact D.rho_mem_longInvAt hs₀ k)
  exact ⟨t, ht, by rw [hρ i, hyi], by rw [hρ j, hyj]⟩

theorem not_alternating (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    (D : HoltData (centralizerImage Ω V) (fixSet Ω V)) (i : D.ι) :
    ¬ (D.M i = alternatingGroup (D.Ψc i) ∧ 7 ≤ Fintype.card (D.Ψc i)) := by
  rintro ⟨hM, h7⟩
  obtain ⟨s₀, hs₀⟩ := hD.exists_mem_longInvAt_x hS
  set R := (D.ρ i).range
  have hAR : alternatingGroup (D.Ψc i) ≤ R := hM ▸ Subgroup.map_le_range _ _
  set b := D.coord ⟨x, hD.x_mem⟩ i
  have hW := mulLongInvClosure_eq_of_alternatingGroup_le h7 hAR ⟨s₀, rfl⟩
    (D.rho_mem_longInvAt hs₀ i).1 b
  obtain ⟨σ, hσ, hσ4, hσ2⟩ := exists_mem_alternatingGroup_inf_stabilizer_pow_four h7 b
  set A := Subgroup.closure (longInvAt (centralizerImage Ω V) (fixSet Ω V) ⟨x, hD.x_mem⟩)
  have hle : mulLongInvClosure R b ≤
      (A.subgroupOf (jHull (centralizerImage Ω V) (fixSet Ω V))).map (D.ρ i) := by
    rw [mulLongInvClosure, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro _ ⟨u, hu, v, hv, rfl⟩
    obtain ⟨su, hsu, hρu⟩ := hD.exists_lift_rho D hs₀ i u.2
      (mem_longInvAt_subgroup_perm_iff.mp hu)
    obtain ⟨sv, hsv, hρv⟩ := hD.exists_lift_rho D hs₀ i v.2
      (mem_longInvAt_subgroup_perm_iff.mp hv)
    refine ⟨su * sv, Subgroup.mem_subgroupOf.mpr (Subgroup.mul_mem _ (Subgroup.subset_closure hsu)
      (Subgroup.subset_closure hsv)), ?_⟩
    rw [map_mul, hρu, hρv]
    rfl
  obtain ⟨a, ha, haσ⟩ := hle (hW ▸ hσ)
  have h := hD.sq_eq_one_of_pow_four hS (D.ρ i) (a := a) (Subgroup.mem_subgroupOf.mp ha)
    (by rw [haσ]; exact hσ4)
  rw [haσ] at h
  exact hσ2 h

omit [Finite G] [FaithfulSMul G Ω] in
theorem exists_lift_of_isNaturalSE (hD : LineDiagData G x L Θ V g y')
    (D : HoltData (centralizerImage Ω V) (fixSet Ω V))
    {s₀ : jHull (centralizerImage Ω V) (fixSet Ω V)}
    (hs₀ : (s₀ : centralizerImage Ω V) ∈ longInvAt (centralizerImage Ω V) (fixSet Ω V)
      ⟨x, hD.x_mem⟩) {i : D.ι} (hi : IsNaturalSE (D.M i))
    (z : longInvAt (D.M i) (D.Ψc i) (D.coord ⟨x, hD.x_mem⟩ i)) :
    ∃ s : jHull (centralizerImage Ω V) (fixSet Ω V),
      (s : centralizerImage Ω V) ∈ longInvAt (centralizerImage Ω V) (fixSet Ω V)
        ⟨x, hD.x_mem⟩ ∧ D.ρ i s = ((z : D.M i) : Perm (D.Ψc i)) := by
  refine hD.exists_lift_rho D hs₀ i ?_ (mem_longInvAt_subgroup_perm_iff.mp z.2)
  rw [D.range_rho_of_not_isOuterFactor hi.not_isOuterFactor]
  exact (z : D.M i).2

theorem eq_two_of_isBenderAction (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    (D : HoltData (centralizerImage Ω V) (fixSet Ω V)) (i : D.ι) {n i' e : ℕ}
    (hA : IsBenderAction ↥(D.M i) (D.Ψc i) n i' e) : n = 2 := by
  have hnat : IsNaturalSE (D.M i) := isNaturalSE_iff.mpr ⟨n, i', e, hA⟩
  obtain ⟨s₀, hs₀⟩ := hD.exists_mem_longInvAt_x hS
  set b := D.coord ⟨x, hD.x_mem⟩ i
  choose s hs hρs using hD.exists_lift_of_isNaturalSE D hs₀ hnat
  have hcard := hD.card_le_four hS (D.ρ i) s (fun z => Subgroup.subset_closure (hs z))
    fun z z' hzz' => by
      rw [hρs, hρs]
      refine not_odd_orderOf_of_sq_eq_one (fun h => hzz' ?_)
        (sq_inv_mul_eq_one_of_mem_longInvAt hnat z.2 z'.2)
      exact Subtype.ext (Subtype.ext (inv_mul_eq_one.mp h))
  rw [Nat.card_coe_set_eq, hA.ncard_longInvAt b] at hcard
  have h2 := hA.params.2.2
  by_contra hn
  have : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem eq_of_isNaturalSE (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    (D : HoltData (centralizerImage Ω V) (fixSet Ω V)) {i j : D.ι} (hi : IsNaturalSE (D.M i))
    (hj : IsNaturalSE (D.M j)) : i = j := by
  by_contra hij
  obtain ⟨s₀, hs₀⟩ := hD.exists_mem_longInvAt_x hS
  set bi := D.coord ⟨x, hD.x_mem⟩ i
  set bj := D.coord ⟨x, hD.x_mem⟩ j
  have hRi := D.range_rho_of_not_isOuterFactor hi.not_isOuterFactor
  have hRj := D.range_rho_of_not_isOuterFactor hj.not_isOuterFactor
  choose s hs hρi hρj using fun zz : longInvAt (D.M i) (D.Ψc i) bi ×
      longInvAt (D.M j) (D.Ψc j) bj =>
    hD.exists_lift_rho₂ D hs₀ hij (z := ((zz.1 : D.M i) : Perm (D.Ψc i)))
      (by rw [hRi]; exact (zz.1 : D.M i).2) (mem_longInvAt_subgroup_perm_iff.mp zz.1.2)
      (z' := ((zz.2 : D.M j) : Perm (D.Ψc j))) (by rw [hRj]; exact (zz.2 : D.M j).2)
      (mem_longInvAt_subgroup_perm_iff.mp zz.2.2)
  have hcard := hD.card_le_four hS ((D.ρ i).prod (D.ρ j)) s
    (fun zz => Subgroup.subset_closure (hs zz)) fun zz zz' hne => by
      simp only [MonoidHom.prod_apply, hρi, hρj, Prod.inv_mk, Prod.mk_mul_mk]
      refine not_odd_orderOf_of_sq_eq_one (fun h => hne ?_) ?_
      · have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only [Prod.fst_one, Prod.snd_one, inv_mul_eq_one] at h1 h2
        exact Prod.ext (Subtype.ext (Subtype.ext h1)) (Subtype.ext (Subtype.ext h2))
      · rw [Prod.pow_mk, sq_inv_mul_eq_one_of_mem_longInvAt hi zz.1.2 zz'.1.2,
          sq_inv_mul_eq_one_of_mem_longInvAt hj zz.2.2 zz'.2.2, Prod.mk_one_one]
  obtain ⟨n, i', e, hA⟩ := isNaturalSE_iff.mp hi
  obtain ⟨m, j', e', hB⟩ := isNaturalSE_iff.mp hj
  rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_coe_set_eq, hA.ncard_longInvAt bi,
    hB.ncard_longInvAt bj] at hcard
  have h1 := hA.four_le_q
  have h2 := hB.four_le_q
  have : 3 * 3 ≤ (2 ^ n - 1) * (2 ^ m - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem exists_unique_component (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    (D : HoltData (centralizerImage Ω V) (fixSet Ω V)) :
    ∃ i₀ : D.ι, (∀ i, i = i₀) ∧ ∃ i' e : ℕ,
      IsBenderAction ↥(D.M i₀) (D.Ψc i₀) 2 i' e ∧ (i' = 1 ∨ i' = 3) := by
  have hι : Nonempty D.ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have htr := D.isEmpty_ι_iff.mp hne
    obtain ⟨θ₁, h₁, θ₂, h₂, h12⟩ := Finset.one_lt_card.mp (by rw [hD.card_Θ]; norm_num)
    obtain ⟨o, ho⟩ := exists_smul_eq (jOddCore (centralizerImage Ω V) (fixSet Ω V))
      (⟨θ₁, hD.mem_of_mem_Θ h₁⟩ : fixSet Ω V) ⟨θ₂, hD.mem_of_mem_Θ h₂⟩
    exact hD.notMem_orbit hS h₁ h₂ h12 ⟨o, ho⟩
  obtain ⟨i₀⟩ := hι
  have hSE : ∀ i, IsNaturalSE (D.M i) := fun i =>
    (D.factor i).resolve_left (hD.not_alternating hS D i)
  refine ⟨i₀, fun i => hD.eq_of_isNaturalSE hS D (hSE i) (hSE i₀), ?_⟩
  obtain ⟨n, i', e, hA⟩ := isNaturalSE_iff.mp (hSE i₀)
  obtain rfl := hD.eq_two_of_isBenderAction hS D i₀ hA
  refine ⟨i', e, hA, ?_⟩
  rcases hA.benderType.cases' with ⟨rfl, -, -⟩ | ⟨rfl, -, a, -, ha⟩ | ⟨rfl, -, -⟩
  · exact Or.inl rfl
  · omega
  · exact Or.inr rfl

theorem jOddCore_eq_bot (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    (D : HoltData (centralizerImage Ω V) (fixSet Ω V)) :
    jOddCore (centralizerImage Ω V) (fixSet Ω V) = ⊥ := by
  by_contra hO
  obtain ⟨i₀, hi₀, i', e, hA, -⟩ := hD.exists_unique_component hS D
  have hnat : IsNaturalSE (D.M i₀) := isNaturalSE_iff.mpr ⟨2, i', e, hA⟩
  obtain ⟨s₀, hs₀⟩ := hD.exists_mem_longInvAt_x hS
  have hstar := hS.star_centralizerImage hD.isPGroup hD.three_le
  set b := D.coord ⟨x, hD.x_mem⟩ i₀
  obtain ⟨Q, hQ⟩ := hA.exists_sylow_le_stabilizer b
  obtain ⟨z₁, hz₁, z₂, hz₂, h12⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp
    (by rw [hA.ncard_longInvAt b]; norm_num :
      1 < (longInvAt (D.M i₀) (D.Ψc i₀) b).ncard)
  have hz₁₂ : z₁ * z₂ ∈ longInvAt (D.M i₀) (D.Ψc i₀) b := by
    have h1 := (hA.mem_longInvAt_iff hQ).mp hz₁
    have h2 := (hA.mem_longInvAt_iff hQ).mp hz₂
    refine (hA.mem_longInvAt_iff hQ).mpr ⟨Subgroup.mul_mem _ h1.1 h2.1, fun h => h12 ?_⟩
    have hinv : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right (Subtype.ext
      (mul_self_eq_one_of_mem_longInv (mem_longInv_subgroup_perm_iff.mp hz₂.1)))
    rw [← hinv]
    exact eq_inv_of_mul_eq_one_left h
  obtain ⟨u₁, hu₁, hρ₁⟩ := hD.exists_lift_of_isNaturalSE D hs₀ hnat ⟨z₁, hz₁⟩
  obtain ⟨u₂, hu₂, hρ₂⟩ := hD.exists_lift_of_isNaturalSE D hs₀ hnat ⟨z₂, hz₂⟩
  obtain ⟨u₃, hu₃, hρ₃⟩ := hD.exists_lift_of_isNaturalSE D hs₀ hnat ⟨z₁ * z₂, hz₁₂⟩
  have hinv₁ : (z₁ : Perm (D.Ψc i₀))⁻¹ = z₁ := inv_eq_of_mul_eq_one_right
    (mul_self_eq_one_of_mem_longInv (mem_longInv_subgroup_perm_iff.mp hz₁.1))
  have hsq : ((z₁ : Perm (D.Ψc i₀)) * z₂) * ((z₁ : Perm (D.Ψc i₀)) * z₂) = 1 := by
    have := sq_inv_mul_eq_one_of_mem_longInvAt hnat hz₁ hz₂
    rwa [hinv₁, pow_two] at this
  set y := u₁ * u₂ * u₃
  have hyρ : ∀ i, D.ρ i y = 1 := fun i => by
    obtain rfl := hi₀ i
    simp only [y, map_mul, hρ₁, hρ₂, hρ₃, Subgroup.coe_mul]
    rw [← mul_assoc] at hsq
    exact hsq
  have hyK : ((y : centralizerImage Ω V)) ∈ jOrbitKernel (centralizerImage Ω V) (fixSet Ω V) :=
    D.mem_jOrbitKernel_iff_rho.mpr hyρ
  have h12mem : (u₁ : centralizerImage Ω V) * u₂ ∈ D.socPre :=
    HoltData.mul_mem_socPre hstar D hu₁.1 hu₂.1
  have hu₃s : (u₃ : centralizerImage Ω V) ∉ D.socPre := by
    intro h
    obtain ⟨c, hc, hct⟩ := HoltData.exists_conj_t_mul_mem_jOddCore hstar D hu₃.1
    have h1 : c * D.t * c⁻¹ ∈ D.socPre := by
      have := Subgroup.mul_mem _ (D.jOddCore_le_socPre hct) (Subgroup.inv_mem _ h)
      simpa [mul_assoc] using this
    have ht : D.t ∈ D.socPre := by
      have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) h1) hc
      simpa [mul_assoc] using this
    exact hO (D.t_mem_socPre_iff.mp ht).1
  have hyO : (y : centralizerImage Ω V) ∉ jOddCore (centralizerImage Ω V) (fixSet Ω V) := by
    intro h
    apply hu₃s
    have e1 : (u₃ : centralizerImage Ω V) =
        ((u₁ : centralizerImage Ω V) * u₂)⁻¹ * (y : centralizerImage Ω V) := by
      simp only [y, Subgroup.coe_mul]
      group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h12mem) (D.jOddCore_le_socPre h)
  set A := Subgroup.closure (longInvAt (centralizerImage Ω V) (fixSet Ω V) ⟨x, hD.x_mem⟩)
  have hyA : (y : centralizerImage Ω V) ∈ A := by
    simp only [y, Subgroup.coe_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure hu₁)
      (Subgroup.subset_closure hu₂)) (Subgroup.subset_closure hu₃)
  have hK := hD.isKleinOn_of_mem_closure hS hyA
  obtain ⟨θ₀, hθ₀⟩ : Θ.Nonempty := Finset.card_pos.mp (by rw [hD.card_Θ]; norm_num)
  have hfix : ((y : centralizerImage Ω V) : Perm (fixSet Ω V)) ⟨θ₀, hD.mem_of_mem_Θ hθ₀⟩ =
      ⟨θ₀, hD.mem_of_mem_Θ hθ₀⟩ := by
    by_contra hne
    have hmem := hK.mapsTo ⟨θ₀, hD.mem_of_mem_Θ hθ₀⟩ hθ₀
    have horb := (mem_jOrbitKernel.mp hyK).2 ⟨θ₀, hD.mem_of_mem_Θ hθ₀⟩
    have h' : (y : centralizerImage Ω V) • (⟨θ₀, hD.mem_of_mem_Θ hθ₀⟩ : fixSet Ω V) ∈
        orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ⟨θ₀, hD.mem_of_mem_Θ hθ₀⟩ := by
      rw [← horb]
      exact Set.smul_mem_smul_set (mem_orbit_self _)
    exact hD.notMem_orbit hS hθ₀ hmem (fun h => hne (Subtype.ext h.symm)) h'
  have hodd := hD.odd_orderOf_of_mem_closure hS hyA hθ₀ hfix
  exact hyO (mem_of_odd_orderOf_of_relIndex_le_two D.relIndex_jOddCore_jOrbitKernel_le_two
    hyK hodd)

end Components

end LineDiagData

section Normalizer

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {V : Subgroup G}

theorem conj_mem_centralizerImage {k : G} (hk : k ∈ Subgroup.normalizer (V : Set G))
    {π : Perm (fixSet Ω V)} (hπ : π ∈ centralizerImage Ω V) :
    inducedHom (Subgroup.normalizer (V : Set G)) (fixSet Ω V) (normalizer_le_stabilizer_fixSet V)
        ⟨k, hk⟩ * π * (inducedHom (Subgroup.normalizer (V : Set G)) (fixSet Ω V)
          (normalizer_le_stabilizer_fixSet V) ⟨k, hk⟩)⁻¹ ∈ centralizerImage Ω V := by
  obtain ⟨c, hc, hcπ⟩ := mem_centralizerImage.mp hπ
  refine mem_centralizerImage.mpr ⟨k * c * k⁻¹, ?_, fun ω => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hw : k⁻¹ * v * k ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) v).mp hv
      rwa [inv_inv] at this
    have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hw
    calc v * (k * c * k⁻¹) = k * ((k⁻¹ * v * k) * c) * k⁻¹ := by group
      _ = k * (c * (k⁻¹ * v * k)) * k⁻¹ := by rw [hcomm]
      _ = k * c * k⁻¹ * v := by group
  · rw [← map_inv, Perm.mul_apply, Perm.mul_apply, coe_inducedHom_apply, hcπ,
      coe_inducedHom_apply, mul_smul, mul_smul]
    rfl

theorem conj_mem_longInv_centralizerImage {k : G} (hk : k ∈ Subgroup.normalizer (V : Set G))
    {π : centralizerImage Ω V} (hπ : π ∈ longInv (centralizerImage Ω V) (fixSet Ω V)) :
    (⟨_, conj_mem_centralizerImage hk π.2⟩ : centralizerImage Ω V) ∈
      longInv (centralizerImage Ω V) (fixSet Ω V) := by
  rw [mem_longInv_subgroup_perm_iff] at hπ ⊢
  exact conj_mem_longInv hπ _

theorem conj_mem_jHull_centralizerImage {k : G} (hk : k ∈ Subgroup.normalizer (V : Set G))
    {h : centralizerImage Ω V} (hh : h ∈ jHull (centralizerImage Ω V) (fixSet Ω V)) :
    (⟨_, conj_mem_centralizerImage hk h.2⟩ : centralizerImage Ω V) ∈
      jHull (centralizerImage Ω V) (fixSet Ω V) := by
  induction hh using Subgroup.closure_induction with
  | mem π hπ => exact Subgroup.subset_closure (conj_mem_longInv_centralizerImage hk hπ)
  | one =>
    convert Subgroup.one_mem _ using 1
    apply Subtype.ext
    simp
  | mul a b _ _ iha ihb =>
    convert Subgroup.mul_mem _ iha ihb using 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group
  | inv a _ iha =>
    convert Subgroup.inv_mem _ iha using 1
    apply Subtype.ext
    simp only [Subgroup.coe_inv]
    group

end Normalizer

namespace LineDiagData

section Final

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {x : Ω} {L : Set Ω} {Θ : Finset Ω} {V : Subgroup G} {g : G} {y' : Ω}

theorem false_of_jOddCore_eq_bot (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y')
    (D : HoltData (centralizerImage Ω V) (fixSet Ω V))
    (hO : jOddCore (centralizerImage Ω V) (fixSet Ω V) = ⊥) : False := by
  obtain ⟨i₀, hi₀, i', e, hA, hi'⟩ := hD.exists_unique_component hS D
  have hnat : IsNaturalSE (D.M i₀) := isNaturalSE_iff.mpr ⟨2, i', e, hA⟩
  have hbij : Function.Bijective (fun ω : fixSet Ω V => D.coord ω i₀) := by
    refine ⟨fun ω ω' h => (D.coord_bijective hO).1 (funext fun i => ?_), fun b => ?_⟩
    · obtain rfl := hi₀ i
      exact h
    · exact D.exists_coord_apply_eq i₀ b
  set E := Equiv.ofBijective _ hbij with hEdef
  have hE : ∀ ω, E ω = D.coord ω i₀ := fun _ => rfl
  have hcard : Nat.card (fixSet Ω V) = (2 ^ 2) ^ i' + 1 := by
    rw [Nat.card_congr E, hA.card_eq]
  have hi3 : i' = 3 := by
    rcases hi' with rfl | rfl
    · have := hD.six_le
      rw [hcard] at this
      norm_num at this
    · rfl
  subst hi3
  have hρE : ∀ (h : jHull (centralizerImage Ω V) (fixSet Ω V)) (ω : fixSet Ω V),
      D.ρ i₀ h (E ω) = E (((h : centralizerImage Ω V) : Perm (fixSet Ω V)) ω) := fun h ω => by
    rw [hE, hE, ← D.coord_smul]
    rfl
  have hM : D.M i₀ = (D.ρ i₀).range :=
    (D.range_rho_of_not_isOuterFactor hnat.not_isOuterFactor).symm
  have hpinv : ∀ p : Perm (fixSet Ω V), (E.permCongr p)⁻¹ = E.permCongr p⁻¹ := fun p => by
    rw [← Equiv.permCongrHom_coe, map_inv]
  have hconj : ∀ {k : G} (hk : k ∈ Subgroup.normalizer (V : Set G)) {m : Perm (D.Ψc i₀)},
      m ∈ D.M i₀ → E.permCongr (inducedHom (Subgroup.normalizer (V : Set G)) (fixSet Ω V)
        (normalizer_le_stabilizer_fixSet V) ⟨k, hk⟩) * m *
        (E.permCongr (inducedHom (Subgroup.normalizer (V : Set G)) (fixSet Ω V)
          (normalizer_le_stabilizer_fixSet V) ⟨k, hk⟩))⁻¹ ∈ D.M i₀ := by
    intro k hk m hm
    rw [hM] at hm ⊢
    obtain ⟨h, rfl⟩ := hm
    set kX := inducedHom (Subgroup.normalizer (V : Set G)) (fixSet Ω V)
      (normalizer_le_stabilizer_fixSet V) ⟨k, hk⟩
    refine ⟨⟨_, conj_mem_jHull_centralizerImage hk h.2⟩, ?_⟩
    ext b
    obtain ⟨ω, rfl⟩ := E.surjective b
    rw [hρE, hpinv]
    conv_rhs => rw [Perm.mul_apply, Perm.mul_apply, Equiv.permCongr_apply E kX⁻¹,
      Equiv.symm_apply_apply, hρE, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rfl
  set gX := inducedHom (Subgroup.normalizer (V : Set G)) (fixSet Ω V)
    (normalizer_le_stabilizer_fixSet V) ⟨g, hD.mem_normalizer⟩ with hgXdef
  set ĝ := E.permCongr gX with hĝdef
  have hĝN : ĝ ∈ Subgroup.normalizer (D.M i₀ : Set (Perm (D.Ψc i₀))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨hconj hD.mem_normalizer, fun hm => ?_⟩
    have := hconj (Subgroup.inv_mem _ hD.mem_normalizer) hm
    have e1 : inducedHom (Subgroup.normalizer (V : Set G)) (fixSet Ω V)
        (normalizer_le_stabilizer_fixSet V) ⟨g⁻¹, Subgroup.inv_mem _ hD.mem_normalizer⟩ =
          gX⁻¹ := by
      rw [hgXdef, ← map_inv]
      rfl
    rw [e1, ← hpinv, ← hĝdef, inv_inv] at this
    convert this using 1
    group
  obtain ⟨n, hn⟩ := hD.pow_eq_one
  have hĝ3 : ĝ ^ 3 ^ n = 1 := by
    have h1 : gX ^ 3 ^ n = 1 := by
      rw [hgXdef, ← map_pow]
      have : (⟨g, hD.mem_normalizer⟩ : Subgroup.normalizer (V : Set G)) ^ 3 ^ n = 1 :=
        Subtype.ext (by rw [Subgroup.coe_pow, hn]; rfl)
      rw [this, map_one]
    rw [hĝdef, ← Equiv.permCongrHom_coe, ← map_pow, h1, map_one]
  obtain ⟨θ, hθ, hgθ⟩ := hD.exists_fix
  have hθx : θ ≠ x := (hD.mem_Θ θ hθ).2
  have hxy' : x ≠ y' := fun h => hD.notMem_y' (h ▸ hD.mem)
  have hθy' : θ ≠ y' := fun h => hD.notMem_y' (h ▸ (hD.mem_Θ θ hθ).1)
  have hfixĝ : ∀ {ω : Ω} (hω : ω ∈ fixSet Ω V), g • ω = ω → ĝ (E ⟨ω, hω⟩) = E ⟨ω, hω⟩ :=
    fun {ω} hω hgω => by
      rw [hĝdef, Equiv.permCongr_apply, Equiv.symm_apply_apply]
      congr 1
      exact Subtype.ext hgω
  have hĝ1 := hA.eq_one_of_pow_three_pow_eq_one_of_fix_three hĝN hĝ3
    (E.injective.ne (fun h => hθx (congrArg Subtype.val h).symm))
    (E.injective.ne (fun h => hxy' (congrArg Subtype.val h)))
    (E.injective.ne (fun h => hθy' (congrArg Subtype.val h)))
    (hfixĝ hD.x_mem hD.smul_x) (hfixĝ (hD.mem_of_mem_Θ hθ) hgθ) (hfixĝ hD.y'_mem hD.smul_y')
  obtain ⟨θ', hθ', hgθ'⟩ := hD.exists_move
  apply hgθ'
  have h1 := congrArg (fun π : Perm (D.Ψc i₀) => π (E ⟨θ', hD.mem_of_mem_Θ hθ'⟩)) hĝ1
  simp only [hĝdef, Equiv.permCongr_apply, Equiv.symm_apply_apply, Perm.one_apply] at h1
  have h2 := congrArg Subtype.val (E.injective h1)
  exact h2

theorem false_of_lineDiagData (hS : Sec4Setting G Ω) (hD : LineDiagData G x L Θ V g y') :
    False := by
  obtain ⟨D⟩ := hS.holtData_centralizerImage hD.isPGroup hD.ne_bot hD.three_le
  exact hD.false_of_jOddCore_eq_bot hS D (hD.jOddCore_eq_bot hS D)

end Final

end LineDiagData

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω]

theorem Sec4Setting.lineNonDiagonal (hS : Sec4Setting G Ω) {Λ : Set Ω}
    (hΛ : IsLine G Λ) : LineNonDiagonal G Λ := by
  intro x L hL L' hL' hne
  by_contra hND
  have hdiag : ∀ h ∈ Subgroup.closure (longInvAt G Ω x), h ∈ fixingSubgroup G L' →
      ∀ y ∈ L, h • y = y := fun h hh hfix y hy => by
    by_contra hmove
    exact hND ⟨h, hh, hfix, y, hy, hmove⟩
  obtain ⟨Θ, V, g, y', hD⟩ := exists_lineDiagData hΛ hL hL' hne hdiag
  exact hD.false_of_lineDiagData hS

theorem Sec4Setting.lineNonDiagonal_of_jClosed (hS : Sec4Setting G Ω) {α : Ω} {Λ : Set Ω}
    [DecidablePred (· ∈ Λ)]
    (hα : α ∈ Λ) (h7 : 7 ≤ Λ.ncard) (hJ : ∀ x ∈ Λ, ∀ t ∈ longInvAt G Ω x, t • Λ = Λ)
    (hA : alternatingGroup Λ ≤ inducedPerm (stabilizer G Λ) Λ le_rfl) :
    LineNonDiagonal G Λ := by
  by_cases hne : Λ = Set.univ
  · intro x L hL L' hL' hLL'
    obtain ⟨⟨g₁, rfl⟩, -⟩ := hL
    obtain ⟨⟨g₂, rfl⟩, -⟩ := hL'
    exact absurd (by rw [hne, Set.smul_set_univ, Set.smul_set_univ]) hLL'
  · exact hS.lineNonDiagonal (hS.isLine hα h7 hJ hA hne)

theorem Sec4Setting.alternatingGroup_le_of_jClosed (hS : Sec4Setting G Ω)
    {α : Ω} {Λ : Set Ω} [DecidablePred (· ∈ Λ)]
    (hα : α ∈ Λ) (h7 : 7 ≤ Λ.ncard) (hJ : ∀ x ∈ Λ, ∀ t ∈ longInvAt G Ω x, t • Λ = Λ)
    (hA : alternatingGroup Λ ≤ inducedPerm (stabilizer G Λ) Λ le_rfl) :
    alternatingGroup Ω ≤ (MulAction.toPermHom G Ω).range := by
  exact hS.alternatingGroup_le_of_jClosed_of_lineNonDiagonal hα h7 hJ hA
    (hS.lineNonDiagonal_of_jClosed hα h7 hJ hA)

end Main

end CFSG.Holt.H78
