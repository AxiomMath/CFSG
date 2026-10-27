module

public import CFSG.Holt.H78.Sec4Prop43B
public import CFSG.Holt.H78.Sec4CCL
import CFSG.Holt.H78.Lemma27Real
public import CFSG.Holt.H78.Lemma27Blocks
public import CFSG.Holt.H78.Sec4Prop46A2

public section

namespace CFSG.Holt.H78

namespace CaseAD

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section Dir

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α β : Ω}

@[expose] def MapsDir (A : CaseAData G Ω α β) (g : G) (j k : A.D.ι) : Prop :=
  ∀ δ₁ δ₂ δ₁' δ₂' : holtDelta G Ω α β, (δ₁' : Ω) = g • (δ₁ : Ω) → (δ₂' : Ω) = g • (δ₂ : Ω) →
    (A.D.coord δ₁' k = A.D.coord δ₂' k ↔ A.D.coord δ₁ j = A.D.coord δ₂ j)

variable (A : CaseAData G Ω α β)

theorem mapsDir_one (j : A.D.ι) : MapsDir A 1 j j := by
  intro δ₁ δ₂ δ₁' δ₂' h₁ h₂
  rw [one_smul] at h₁ h₂
  rw [(Subtype.ext h₁ : δ₁' = δ₁), (Subtype.ext h₂ : δ₂' = δ₂)]

theorem MapsDir.mul {g h : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) {j k l : A.D.ι}
    (h₁ : MapsDir A g j k) (h₂ : MapsDir A h k l) : MapsDir A (h * g) j l := by
  intro δ₁ δ₂ δ₁'' δ₂'' e₁ e₂
  rw [h₂ (twoPointElt hg • δ₁) (twoPointElt hg • δ₂) δ₁'' δ₂'' (by rw [e₁, mul_smul]; rfl)
    (by rw [e₂, mul_smul]; rfl)]
  exact h₁ δ₁ δ₂ _ _ rfl rfl

theorem MapsDir.inv {g : G} {j k : A.D.ι} (h : MapsDir A g j k) : MapsDir A g⁻¹ k j := by
  intro δ₁ δ₂ δ₁' δ₂' e₁ e₂
  refine (h δ₁' δ₂' δ₁ δ₂ ?_ ?_).symm
  · rw [e₁, smul_inv_smul]
  · rw [e₂, smul_inv_smul]


theorem exists_mapsDir {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) :
    ∃ σ : A.D.ι ≃ A.D.ι, ∀ j, MapsDir A g j (σ j) := by
  obtain ⟨σ, hσ⟩ := A.D.conj_L (twoPointElt hg)
  refine ⟨σ, fun j δ₁ δ₂ δ₁' δ₂' e₁ e₂ => ?_⟩
  rw [(Subtype.ext e₁ : δ₁' = twoPointElt hg • δ₁), (Subtype.ext e₂ : δ₂' = twoPointElt hg • δ₂)]
  exact A.D.coord_smul_eq_iff_of_conj A.oddCore_eq_bot hσ j δ₁ δ₂

theorem exists_pair_update (γ : holtDelta G Ω α β) (j : A.D.ι) :
    ∃ δ : holtDelta G Ω α β, A.D.coord δ j ≠ A.D.coord γ j ∧
      ∀ k, k ≠ j → A.D.coord δ k = A.D.coord γ k := by
  classical
  have : Nontrivial (A.D.Ψc j) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by have := A.D.five_le_card j; omega)
  obtain ⟨c, hc⟩ := exists_ne (A.D.coord γ j)
  obtain ⟨δ, hδ⟩ := A.D.coord_surjective (Function.update (A.D.coord γ) j c)
  exact ⟨δ, by rw [hδ, Function.update_self]; exact hc, fun k hk => by
    rw [hδ, Function.update_of_ne hk]⟩

theorem MapsDir.eq {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω)) (γ : holtDelta G Ω α β)
    {j k k' : A.D.ι} (h : MapsDir A g j k) (h' : MapsDir A g j k') : k = k' := by
  obtain ⟨σ, hσ⟩ := exists_mapsDir A hg
  have key : ∀ {k}, MapsDir A g j k → k = σ j := fun {k} hk => by
    by_contra hne
    set m := σ.symm k
    have hm : m ≠ j := fun hmj => hne (by rw [← hmj, Equiv.apply_symm_apply])
    have hmk : MapsDir A g m k := by
      have := hσ m
      rwa [Equiv.apply_symm_apply] at this
    obtain ⟨δ, hδj, hδo⟩ := exists_pair_update A γ j
    have h1 := (hmk γ δ (twoPointElt hg • γ) (twoPointElt hg • δ) rfl rfl).mpr (hδo m hm).symm
    exact hδj ((hk γ δ (twoPointElt hg • γ) (twoPointElt hg • δ) rfl rfl).mp h1).symm
  rw [key h, key h']

end Dir

section Orbits

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α β : Ω} (A : CaseAData G Ω α β)
  (V : Subgroup G)

@[expose] def VRel (j k : A.D.ι) : Prop := ∃ g ∈ V, MapsDir A g j k

@[expose] def proj (j : A.D.ι) : Set (A.D.Ψc j) :=
  {c | ∃ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V ∧ A.D.coord δ j = c}

variable {A V}

theorem VRel.refl (j : A.D.ι) : VRel A V j j := ⟨1, V.one_mem, mapsDir_one A j⟩

theorem VRel.symm {j k : A.D.ι} (h : VRel A V j k) : VRel A V k j := by
  obtain ⟨g, hg, h⟩ := h
  exact ⟨g⁻¹, V.inv_mem hg, h.inv⟩

theorem VRel.trans (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β) {j k l : A.D.ι}
    (h₁ : VRel A V j k) (h₂ : VRel A V k l) : VRel A V j l := by
  obtain ⟨g, hg, h₁⟩ := h₁
  obtain ⟨h, hh, h₂⟩ := h₂
  exact ⟨h * g, V.mul_mem hh hg,
    h₁.mul A (stabilizer_inf_le_stabilizer_pair α β (hVαβ hg)) h₂⟩

theorem VRel.coord_eq_iff {j k : A.D.ι} (h : VRel A V j k) {δ δ' : holtDelta G Ω α β}
    (hδ : (δ : Ω) ∈ fixSet Ω V) (hδ' : (δ' : Ω) ∈ fixSet Ω V) :
    A.D.coord δ j = A.D.coord δ' j ↔ A.D.coord δ k = A.D.coord δ' k := by
  obtain ⟨g, hg, hgjk⟩ := h
  exact (hgjk δ δ' δ δ' (hδ g hg).symm (hδ' g hg).symm).symm


theorem exists_splice (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β) (j : A.D.ι)
    [DecidablePred (VRel A V j)] {δ δ' : holtDelta G Ω α β} (hδ : (δ : Ω) ∈ fixSet Ω V)
    (hδ' : (δ' : Ω) ∈ fixSet Ω V) :
    ∃ ε : holtDelta G Ω α β, (ε : Ω) ∈ fixSet Ω V ∧
      ∀ i, A.D.coord ε i = if VRel A V j i then A.D.coord δ' i else A.D.coord δ i := by
  obtain ⟨ε, hε⟩ := A.D.coord_surjective
    (fun i => if VRel A V j i then A.D.coord δ' i else A.D.coord δ i)
  refine ⟨ε, fun g hg => ?_, fun i => by rw [hε]⟩
  have hg2 := stabilizer_inf_le_stabilizer_pair α β (hVαβ hg)
  obtain ⟨σ, hσ⟩ := exists_mapsDir A hg2
  have key : twoPointElt hg2 • ε = ε := CaseAData.coord_injective A (funext fun k => by
    obtain ⟨i, rfl⟩ := σ.surjective k
    have hrel : VRel A V j i ↔ VRel A V j (σ i) :=
      ⟨fun h => h.trans hVαβ ⟨g, hg, hσ i⟩, fun h => h.trans hVαβ (VRel.symm ⟨g, hg, hσ i⟩)⟩
    by_cases hj : VRel A V j i
    · have h1 := (hσ i ε δ' (twoPointElt hg2 • ε) δ' rfl (hδ' g hg).symm).mpr
        (by rw [congrFun hε i, ite_eq_left hj])
      rw [h1, congrFun hε, ite_eq_left (hrel.mp hj)]
    · have h1 := (hσ i ε δ (twoPointElt hg2 • ε) δ rfl (hδ g hg).symm).mpr
        (by rw [congrFun hε i, ite_eq_right hj])
      rw [h1, congrFun hε, ite_eq_right (fun h => hj (hrel.mpr h))])
  exact congrArg Subtype.val key

theorem smul_mem_holtDelta_of_mem {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    (δ : holtDelta G Ω α β) : g • (δ : Ω) ∈ holtDelta G Ω α β :=
  ((twoPointElt hg • δ : holtDelta G Ω α β)).2

theorem pow_six_smul_eq {g : G} (hg : g ∈ stabilizer G ({α, β} : Set Ω))
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) (hgk : ∀ k, MapsDir A g k k)
    (hsmall : ∀ k, (proj A V k).ncard ≤ 3) {δ : holtDelta G Ω α β}
    (hδ : (δ : Ω) ∈ fixSet Ω V) : g ^ 6 • (δ : Ω) = δ := by
  classical
  have hpow : ∀ n : ℕ, g ^ n ∈ stabilizer G ({α, β} : Set Ω) := fun n => pow_mem hg n
  have hpowV : ∀ n : ℕ, g ^ n ∈ Subgroup.normalizer (V : Set G) := fun n => pow_mem hgV n
  set pt : ℕ → holtDelta G Ω α β := fun n => ⟨g ^ n • (δ : Ω), smul_mem_holtDelta_of_mem
    (hpow n) δ⟩ with hpt
  have hptV : ∀ n, ((pt n : holtDelta G Ω α β) : Ω) ∈ fixSet Ω V := fun n =>
    smul_mem_fixSet_of_mem_normalizer (hpowV n) hδ
  have hgV' : ∀ ε : holtDelta G Ω α β, (ε : Ω) ∈ fixSet Ω V →
      ((twoPointElt hg • ε : holtDelta G Ω α β) : Ω) ∈ fixSet Ω V := fun ε hε =>
    smul_mem_fixSet_of_mem_normalizer hgV hε
  refine congrArg Subtype.val (CaseAData.coord_injective A (funext fun k => ?_) :
    pt 6 = δ)
  let S := proj A V k
  let φ : S → S := fun c => ⟨A.D.coord (twoPointElt hg • Classical.choose c.2) k,
    _, hgV' _ (Classical.choose_spec c.2).1, rfl⟩
  have hφ : ∀ (ε : holtDelta G Ω α β) (hε : (ε : Ω) ∈ fixSet Ω V),
      φ ⟨A.D.coord ε k, ε, hε, rfl⟩ =
        ⟨A.D.coord (twoPointElt hg • ε) k, _, hgV' ε hε, rfl⟩ := by
    intro ε hε
    apply Subtype.ext
    show A.D.coord (twoPointElt hg • Classical.choose (⟨ε, hε, rfl⟩ :
      A.D.coord ε k ∈ proj A V k)) k = _
    exact (hgk k _ ε _ _ rfl rfl).mpr (Classical.choose_spec (⟨ε, hε, rfl⟩ :
      A.D.coord ε k ∈ proj A V k)).2
  have hφinj : Function.Injective φ := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have h1 := congrArg Subtype.val h
    simp only [φ] at h1
    have h2 := (hgk k _ _ _ _ rfl rfl).mp h1
    rw [(Classical.choose_spec hc).2, (Classical.choose_spec hc').2] at h2
    exact Subtype.ext h2
  let e : Equiv.Perm S := Equiv.ofBijective φ (Finite.injective_iff_bijective.mp hφinj)
  have hiter : ∀ n : ℕ, (e ^ n) ⟨A.D.coord δ k, δ, hδ, rfl⟩ =
      ⟨A.D.coord (pt n) k, _, hptV n, rfl⟩ := by
    intro n
    induction n with
    | zero => exact Subtype.ext (by simp [pt])
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      show φ _ = _
      rw [hφ (pt n) (hptV n)]
      apply Subtype.ext
      show A.D.coord (twoPointElt hg • pt n) k = A.D.coord (pt (n + 1)) k
      congr 2
      exact Subtype.ext (by simp only [pt, pow_succ', mul_smul]; rfl)
  have hcard : Fintype.card S ≤ 3 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]; exact hsmall k
  have he6 : e ^ 6 = 1 := by
    have hdvd : orderOf e ∣ 6 := (orderOf_dvd_card).trans (by
      rw [Fintype.card_perm]
      interval_cases (Fintype.card S) <;> decide)
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have := hiter 6
  rw [he6, Equiv.Perm.one_apply] at this
  exact (congrArg Subtype.val this).symm

end Orbits

section ClaimA

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_mem_ne_ne_ne {Ψ : Type*} {s : Set Ψ} (hs : 4 ≤ s.ncard) (a b c : Ψ) :
    ∃ e ∈ s, e ≠ a ∧ e ≠ b ∧ e ≠ c := by
  have h3 : ({a, b, c} : Set Ψ).ncard ≤ 3 := by
    refine (Set.ncard_insert_le a _).trans ?_
    have := (Set.ncard_insert_le b ({c} : Set Ψ)).trans (by rw [Set.ncard_singleton])
    omega
  have hlt : ({a, b, c} : Set Ψ).ncard < s.ncard := by omega
  obtain ⟨e, he, hne⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  exact ⟨e, he, hne⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem coe_mul_pow_smul {V : Subgroup G} {c c' : G}
    (hc : c ∈ Subgroup.centralizer (V : Set G)) (hc' : c' ∈ Subgroup.centralizer (V : Set G))
    (m : ℕ) (ω : fixSet Ω V) :
    (((centralizerImageElt (Ω := Ω) hc' * centralizerImageElt (Ω := Ω) hc) ^ m • ω :
      fixSet Ω V) : Ω) = (c' * c) ^ m • (ω : Ω) := by
  induction m generalizing ω with
  | zero => rw [pow_zero, pow_zero, one_smul, one_smul]
  | succ m ih =>
    rw [pow_succ, pow_succ, mul_smul, mul_smul, ih, mul_smul, mul_smul]
    rfl


theorem coord_eq_of_mem_orbit (hS : Sec4Setting G Ω) {α β : Ω} (hαβ : α ≠ β)
    (A : CaseAData G Ω α β) {V : Subgroup G} (hV : IsPGroup 2 V)
    (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β) (h3 : 3 ≤ Nat.card (fixSet Ω V))
    {j : A.D.ι} (hj : 4 ≤ (proj A V j).ncard) {x y : holtDelta G Ω α β}
    (hx : (x : Ω) ∈ fixSet Ω V) (hy : (y : Ω) ∈ fixSet Ω V)
    (horb : (⟨y, hy⟩ : fixSet Ω V) ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V))
      ⟨x, hx⟩) :
    A.D.coord x j = A.D.coord y j := by
  classical
  by_contra hxy
  obtain ⟨u, hu, hux, huV⟩ := hS.exists_mem_longInvSwap_centralizer_of_mem_holtDelta hαβ x.2 hV
    hVαβ (mem_fixSet_iff_le_stabilizer.mp hx)
  have hu2 := closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hu)
  set uΔ : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    ⟨twoPointElt hu2, twoPointElt_mem_jHull hS.star (Subgroup.subset_closure hu)⟩
  set z : ∀ k, Equiv.Perm (A.D.Ψc k) := fun k => A.D.ρ k uΔ with hz
  have hzc : ∀ δ k, A.D.coord (twoPointElt hu2 • δ) k = z k (A.D.coord δ k) :=
    fun δ k => A.D.coord_smul uΔ δ k
  have h3Δ := three_le_card_holtDelta_of_holtData hS.star A.D
  have huJ : (twoPointElt hu2 : twoPointSection G Ω α β) ∈
      longInv (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    (hS.mem_longInv_twoPointSection_iff hαβ h3Δ _).mpr ⟨u, hu, fun _ => rfl⟩
  have hzx : twoPointElt hu2 • x = x := Subtype.ext hux
  have hzJ : ∀ k, z k ∈ longInvAt (Equiv.Perm (A.D.Ψc k)) (A.D.Ψc k) (A.D.coord x k) :=
    fun k => ⟨A.D.rho_mem_longInv huJ k, by
      show z k (A.D.coord x k) = A.D.coord x k
      rw [← hzc, hzx]⟩
  have hzz : ∀ k c, z k (z k c) = c := fun k c => CCL.apply_apply_of_mem_longInv (hzJ k).1 c
  have hzfix : ∀ k c, z k c = c ↔ c = A.D.coord x k := fun k c =>
    apply_eq_self_iff_of_mem_longInvAt_perm (hzJ k)
  have hFu : ∀ δ : holtDelta G Ω α β, (δ : Ω) ∈ fixSet Ω V →
      ((twoPointElt hu2 • δ : holtDelta G Ω α β) : Ω) ∈ fixSet Ω V := fun δ hδ =>
    smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ huV) hδ
  obtain ⟨c₀, ⟨q₀, hq₀V, hq₀j⟩, hc₀x, hc₀y, hc₀z⟩ :=
    exists_mem_ne_ne_ne hj (A.D.coord x j) (A.D.coord y j) (z j (A.D.coord y j))
  obtain ⟨q, hqV, hq⟩ := exists_splice hVαβ j hy hq₀V
  set uy := twoPointElt hu2 • y with huy
  set uq := twoPointElt hu2 • q with huq
  have huyV := hFu y hy
  have huqV := hFu q hqV
  have hqj : A.D.coord q j = c₀ := by rw [hq j, ite_eq_left (VRel.refl j), hq₀j]
  have hoff : ∀ k, ¬ VRel A V j k → A.D.coord q k = A.D.coord y k := fun k hk => by
    rw [hq k, ite_eq_right hk]
  have hon : ∀ k, VRel A V j k → A.D.coord y k ≠ A.D.coord x k ∧
      A.D.coord q k ≠ A.D.coord x k ∧ A.D.coord q k ≠ A.D.coord y k ∧
      A.D.coord q k ≠ z k (A.D.coord y k) := fun k hk => by
    refine ⟨fun h => hxy ((hk.coord_eq_iff hy hx).mpr h).symm, fun h => hc₀x ?_,
      fun h => hc₀y ?_, fun h => hc₀z ?_⟩
    · rw [← hqj]; exact (hk.coord_eq_iff hqV hx).mpr h
    · rw [← hqj]; exact (hk.coord_eq_iff hqV hy).mpr h
    · rw [← hqj, ← hzc]; exact (hk.coord_eq_iff hqV huyV).mpr (by rw [hzc]; exact h)
  set sw : ∀ k, Equiv.Perm (A.D.Ψc k) := fun k => Equiv.swap (A.D.coord y k) (A.D.coord q k)
  set w : ∀ k, Equiv.Perm (A.D.Ψc k) := fun k => sw k * z k * (sw k)⁻¹ with hw
  have hswx : ∀ k, sw k (A.D.coord x k) = A.D.coord x k := fun k => by
    by_cases hk : VRel A V j k
    · obtain ⟨h1, h2, -, -⟩ := hon k hk
      exact Equiv.swap_apply_of_ne_of_ne h1.symm h2.symm
    · show Equiv.swap _ _ _ = _
      rw [hoff k hk, Equiv.swap_self, Equiv.refl_apply]
  have hwJ : ∀ k, w k ∈ longInvAt (Equiv.Perm (A.D.Ψc k)) (A.D.Ψc k) (A.D.coord x k) :=
    fun k => by
      have := conj_mem_longInvAt_perm (hzJ k) (sw k)
      rwa [hswx k] at this
  have hwr : ∀ k, w k ∈ (A.D.ρ k).range := fun k => by
    have hzr : z k ∈ (A.D.ρ k).range := ⟨uΔ, rfl⟩
    have halt : sw k * z k * (sw k)⁻¹ * (z k)⁻¹ ∈ (A.D.ρ k).range := by
      have hle : alternatingGroup (A.D.Ψc k) ≤ (A.D.ρ k).range := by
        rw [← A.alt k]; exact Subgroup.map_le_range _ _
      refine hle ?_
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul, map_mul, map_inv, map_inv,
        mul_comm (Equiv.Perm.sign (sw k)) (Equiv.Perm.sign (z k)), mul_inv_cancel_right,
        mul_inv_cancel]
    have := mul_mem halt hzr
    rwa [inv_mul_cancel_right] at this
  have hval : ∀ k, w k (A.D.coord y k) = z k (A.D.coord q k) ∧
      w k (A.D.coord q k) = z k (A.D.coord y k) ∧
      w k (z k (A.D.coord y k)) = A.D.coord q k ∧ w k (z k (A.D.coord q k)) = A.D.coord y k := by
    intro k
    by_cases hk : VRel A V j k
    · obtain ⟨h1, h2, h3', h4⟩ := hon k hk
      have hzy : z k (A.D.coord y k) ≠ A.D.coord y k := fun h => h1 ((hzfix k _).mp h)
      have hzq : z k (A.D.coord q k) ≠ A.D.coord q k := fun h => h2 ((hzfix k _).mp h)
      have hzqy : z k (A.D.coord q k) ≠ A.D.coord y k := fun h => h4 (by rw [← h, hzz])
      have hzyq : z k (A.D.coord y k) ≠ A.D.coord q k := fun h => h4 h.symm
      simp only [hw, sw, Equiv.swap_inv, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_right]
      refine ⟨Equiv.swap_apply_of_ne_of_ne hzqy hzq, Equiv.swap_apply_of_ne_of_ne hzy hzyq,
        ?_, ?_⟩
      · rw [Equiv.swap_apply_of_ne_of_ne hzy hzyq, hzz, Equiv.swap_apply_left]
      · rw [Equiv.swap_apply_of_ne_of_ne hzqy hzq, hzz, Equiv.swap_apply_right]
    · have hqy := hoff k hk
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [hw, sw, hqy, hzz]
  obtain ⟨t, ht, htw⟩ := A.D.exists_mem_longInvAt_rho_eq x w hwr hwJ
  obtain ⟨c₁, hc₁, hc₁x, hc₁t⟩ := (hS.mem_longInvAt_twoPointSection_iff hαβ h3Δ _).mp ht
  have hc₁act : ∀ δ δ' : holtDelta G Ω α β, (∀ k, w k (A.D.coord δ k) = A.D.coord δ' k) →
      c₁ • (δ : Ω) = δ' := fun δ δ' h => by
    rw [← hc₁t δ]
    refine congrArg Subtype.val (A.coord_injective (funext fun k => ?_))
    show A.D.coord ((t : twoPointSection G Ω α β) • δ) k = _
    rw [A.D.coord_smul t δ k, htw k, h k]
  have e1 : c₁ • (y : Ω) = uq := hc₁act y uq fun k => by rw [(hval k).1, hzc]
  have e2 : c₁ • (q : Ω) = uy := hc₁act q uy fun k => by rw [(hval k).2.1, hzc]
  have e3 : c₁ • (uy : Ω) = q := hc₁act uy q fun k => by rw [hzc, (hval k).2.2.1]
  have e4 : c₁ • (uq : Ω) = y := hc₁act uq y fun k => by rw [hzc, (hval k).2.2.2]
  set ℓ : Set Ω := {(x : Ω), (y : Ω), (q : Ω), (uy : Ω), (uq : Ω)} with hℓ
  have hℓV : ℓ ⊆ fixSet Ω V := by
    intro ω hω
    simp only [hℓ, Set.mem_insert_iff, Set.mem_singleton_iff] at hω
    rcases hω with rfl | rfl | rfl | rfl | rfl
    exacts [hx, hy, hqV, huyV, huqV]
  have hmapsto : ∀ ω ∈ ℓ, c₁ • ω ∈ ℓ := by
    intro ω hω
    simp only [hℓ, Set.mem_insert_iff, Set.mem_singleton_iff] at hω ⊢
    rcases hω with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl hc₁x
    · exact Or.inr (Or.inr (Or.inr (Or.inr e1)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e2)))
    · exact Or.inr (Or.inr (Or.inl e3))
    · exact Or.inr (Or.inl e4)
  have hc₁ℓ : c₁ ∈ stabilizer G ℓ := by
    rw [mem_stabilizer_set]
    intro ω
    refine ⟨fun h => ?_, hmapsto ω⟩
    have := hmapsto _ h
    rwa [smul_smul, mul_self_eq_one_of_mem_longInv hc₁.1, one_smul] at this
  obtain ⟨c, hc, hcV, hcℓ⟩ := hS.exists_mem_longInvSwap_centralizer_eqOn hαβ hV hVαβ
    ⟨(x : Ω), Or.inl rfl⟩ hℓV hc₁ hc₁ℓ
  have hcx : c • (x : Ω) = x := (hcℓ _ (Or.inl rfl)).trans hc₁x
  have hcuy : c • (uy : Ω) = q := (hcℓ _ (by simp [hℓ])).trans e3
  have hcuq : c • (uq : Ω) = y := (hcℓ _ (by simp [hℓ])).trans e4
  have hu' := (hS.mem_longInvAt_centralizerImage_iff hV h3 (a := ⟨x, hx⟩)
    (centralizerImageElt (Ω := Ω) huV)).mpr ⟨u, ⟨hu.1, hux⟩, huV, fun _ => rfl⟩
  have hc' := (hS.mem_longInvAt_centralizerImage_iff hV h3 (a := ⟨x, hx⟩)
    (centralizerImageElt (Ω := Ω) hcV)).mpr ⟨c, ⟨hc.1, hcx⟩, hcV, fun _ => rfl⟩
  obtain ⟨m, hm, hmfix⟩ := exists_odd_pow_smul_eq_of_mem_longInvAt
    (hS.star_centralizerImage hV h3) hu' hc'
  have h1 := congrArg Subtype.val (hmfix _ horb)
  rw [coe_mul_pow_smul huV hcV] at h1
  have hcu1 : (c * u) • (y : Ω) = q := by rw [mul_smul]; exact hcuy
  have hcu2 : (c * u) • (q : Ω) = y := by rw [mul_smul]; exact hcuq
  obtain ⟨n, rfl⟩ := hm
  have hpow : ∀ n : ℕ, (c * u) ^ (2 * n + 1) • (y : Ω) = q := by
    intro n
    induction n with
    | zero => simpa using hcu1
    | succ n ih =>
      rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by ring, pow_add, mul_smul, ih, sq, mul_smul,
        hcu2, hcu1]
  rw [hpow n] at h1
  apply hc₀y
  rw [← hqj, show q = y from Subtype.ext h1]

end ClaimA

section PermAux

variable {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]

omit [Fintype Ψ] in
theorem extend_mem_longInv {a b : Ψ} (hab : a ≠ b)
    {y : Equiv.Perm {p : Ψ // p ≠ a ∧ p ≠ b}}
    (hy : y ∈ longInv (Equiv.Perm {p : Ψ // p ≠ a ∧ p ≠ b}) {p : Ψ // p ≠ a ∧ p ≠ b}) :
    Equiv.Perm.ofSubtype y * Equiv.swap a b ∈ longInv (Equiv.Perm Ψ) Ψ ∧
      (Equiv.Perm.ofSubtype y * Equiv.swap a b) a = b ∧
      ∀ p : {p : Ψ // p ≠ a ∧ p ≠ b}, (Equiv.Perm.ofSubtype y * Equiv.swap a b) p = y p := by
  set ŷ := Equiv.Perm.ofSubtype y * Equiv.swap a b with hŷ
  have hpt : ∀ p : {p : Ψ // p ≠ a ∧ p ≠ b}, ŷ p = y p := fun p => by
    rw [hŷ, Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne p.2.1 p.2.2,
      Equiv.Perm.ofSubtype_apply_coe]
  have hna : ¬ (a ≠ a ∧ a ≠ b) := fun h => h.1 rfl
  have hnb : ¬ (b ≠ a ∧ b ≠ b) := fun h => h.2 rfl
  have hya : ŷ a = b := by
    rw [hŷ, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun x => x ≠ a ∧ x ≠ b) y hnb]
  have hyb : ŷ b = a := by
    rw [hŷ, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.Perm.ofSubtype_apply_of_not_mem (p := fun x => x ≠ a ∧ x ≠ b) y hna]
  have hyy : ∀ p : {p : Ψ // p ≠ a ∧ p ≠ b}, y (y p) = p := fun p =>
    CCL.apply_apply_of_mem_longInv hy p
  have hsq : ŷ * ŷ = 1 := Equiv.ext fun x => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    by_cases hx : x ≠ a ∧ x ≠ b
    · have h1 := hpt ⟨x, hx⟩
      rw [show x = ((⟨x, hx⟩ : {p : Ψ // p ≠ a ∧ p ≠ b}) : Ψ) from rfl, h1, hpt, hyy]
    · rcases not_and_or.mp hx with h | h
      · rw [not_not.mp h, hya, hyb]
      · rw [not_not.mp h, hyb, hya]
  obtain ⟨-, c, hc, hcu⟩ := hy
  have hfix : ∀ x, ŷ x = x ↔ x = c := fun x => by
    constructor
    · intro hx
      by_cases hx' : x ≠ a ∧ x ≠ b
      · have h1 := hpt ⟨x, hx'⟩
        rw [show ((⟨x, hx'⟩ : {p : Ψ // p ≠ a ∧ p ≠ b}) : Ψ) = x from rfl, hx] at h1
        have := hcu ⟨x, hx'⟩ (Subtype.ext h1.symm)
        rw [← this]
      · rcases not_and_or.mp hx' with h | h
        · rw [not_not.mp h, hya] at hx; exact absurd hx.symm hab
        · rw [not_not.mp h, hyb] at hx; exact absurd hx hab
    · rintro rfl
      rw [hpt]
      exact congrArg Subtype.val hc
  refine ⟨⟨?_, c, (hfix c).mpr rfl, fun x hx => (hfix x).mp hx⟩, hya, hpt⟩
  have hne : ŷ ≠ 1 := fun h => hab (by rw [← hya, h, Equiv.Perm.one_apply])
  exact orderOf_eq_prime (by rw [sq]; exact hsq) hne

theorem alternatingGroup_le_of_longInv_subset (h5 : 5 ≤ Fintype.card Ψ)
    (hodd : Odd (Fintype.card Ψ)) {H : Subgroup (Equiv.Perm Ψ)}
    (hH : longInv (Equiv.Perm Ψ) Ψ ⊆ H) : alternatingGroup Ψ ≤ H := by
  have hconj : Subgroup.normalClosure (longInv (Equiv.Perm Ψ) Ψ) ≤ H := by
    refine (Subgroup.closure_le _).mpr fun g hg => ?_
    obtain ⟨σ, hσ, hσg⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    obtain ⟨c, rfl⟩ := isConj_iff.mp hσg
    obtain ⟨p, hp, -⟩ := hσ.2
    exact hH (conj_mem_longInvAt_perm ⟨hσ, hp⟩ c).1
  obtain ⟨σ, hσ⟩ := exists_mem_longInv_perm hodd (by omega)
  have hnt : Nontrivial (Subgroup.normalClosure (longInv (Equiv.Perm Ψ) Ψ)) := by
    refine ⟨⟨⟨σ, Subgroup.subset_normalClosure hσ⟩, 1, fun h => ?_⟩⟩
    have h1 : σ = 1 := congrArg Subtype.val h
    have := hσ.1
    rw [h1, orderOf_one] at this
    exact absurd this (by norm_num)
  exact (Equiv.Perm.alternatingGroup_le_of_normal (by rwa [Nat.card_eq_fintype_card]) (N :=
    Subgroup.normalClosure (longInv (Equiv.Perm Ψ) Ψ))) hnt |>.trans hconj

theorem card_compl_pair {a b : Ψ} (hab : a ≠ b) :
    Fintype.card {p : Ψ // p ≠ a ∧ p ≠ b} = Fintype.card Ψ - 2 := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun p : Ψ => p ≠ a ∧ p ≠ b) = Finset.univ \ {a, b} := by
    ext p; simp [not_or]
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_pair hab]

omit [Fintype Ψ] [DecidableEq Ψ] in
theorem injective_vec_two {a b : Ψ} (h : a ≠ b) : Function.Injective ![a, b] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem exists_mul_pow_six_ne (h7 : 7 ≤ Fintype.card Ψ) {a b : Ψ} (hab : a ≠ b)
    {y : Equiv.Perm Ψ} (hy : y ∈ longInv (Equiv.Perm Ψ) Ψ) (hyab : y a = b) :
    ∃ y' ∈ longInv (Equiv.Perm Ψ) Ψ, y' a = b ∧
      ∃ p, p ≠ a ∧ p ≠ b ∧ ((y * y') ^ 6) p ≠ p := by
  have hyy := CCL.apply_apply_of_mem_longInv hy
  obtain ⟨p₅, hp₅s, hp₅u⟩ := hy.2
  have hp₅ : y p₅ = p₅ := hp₅s
  have hfix : ∀ x, y x = x ↔ x = p₅ := fun x =>
    ⟨fun h => hp₅u x h, fun h => h ▸ hp₅⟩
  have hyba : y b = a := by rw [← hyab, hyy]
  have hp₅a : p₅ ≠ a := fun h => hab (by rw [← hyab, ← h, hp₅])
  have hp₅b : p₅ ≠ b := fun h => hab (by rw [← hyba, ← h, hp₅])
  obtain ⟨p₁, hp₁a, hp₁b, hp₁5⟩ := CCL.exists_ne_ne_ne_of_four_le (by omega) a b p₅
  set p₂ := y p₁ with hp₂
  have hp₂1 : p₂ ≠ p₁ := fun h => hp₁5 ((hfix p₁).mp h)
  have hp₂a : p₂ ≠ a := fun h => hp₁b (by rw [← hyy p₁, ← hp₂, h, hyab])
  have hp₂b : p₂ ≠ b := fun h => hp₁a (by rw [← hyy p₁, ← hp₂, h, hyba])
  have hp₂5 : p₂ ≠ p₅ := fun h => hp₁5 (by rw [← hyy p₁, ← hp₂, h, hp₅])
  have hc5 : ({a, b, p₅, p₁, p₂} : Finset Ψ).card ≤ 5 := by
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    rw [Finset.card_singleton]
  obtain ⟨p₃, -, hp₃⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, p₅, p₁, p₂} : Finset Ψ)) (t := Finset.univ) (by rw [Finset.card_univ]; omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp₃
  obtain ⟨hp₃a, hp₃b, hp₃5, hp₃1, hp₃2⟩ := hp₃
  set p₄ := y p₃ with hp₄
  have hp₄3 : p₄ ≠ p₃ := fun h => hp₃5 ((hfix p₃).mp h)
  have hp₄a : p₄ ≠ a := fun h => hp₃b (by rw [← hyy p₃, ← hp₄, h, hyab])
  have hp₄b : p₄ ≠ b := fun h => hp₃a (by rw [← hyy p₃, ← hp₄, h, hyba])
  have hp₄5 : p₄ ≠ p₅ := fun h => hp₃5 (by rw [← hyy p₃, ← hp₄, h, hp₅])
  have hp₄1 : p₄ ≠ p₁ := fun h => hp₃2 (by rw [← hyy p₃, ← hp₄, h])
  have hp₄2 : p₄ ≠ p₂ := fun h => hp₃1 (by rw [← hyy p₃, ← hp₄, h, hp₂, hyy])
  set g := Equiv.swap p₂ p₅ * Equiv.swap p₂ p₃ with hg
  have g2 : g p₂ = p₃ := by
    simp only [hg, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hp₃2 hp₃5
  have g3 : g p₃ = p₅ := by
    simp only [hg, Equiv.Perm.mul_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  have g5 : g p₅ = p₂ := by
    simp only [hg, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hp₂5) (fun h => hp₃5 h.symm),
      Equiv.swap_apply_right]
  have gfix : ∀ x, x ≠ p₂ → x ≠ p₃ → x ≠ p₅ → g x = x := fun x h2 h3 h5 => by
    simp only [hg, Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne h2 h3, Equiv.swap_apply_of_ne_of_ne h2 h5]
  have gi : ∀ x z, g z = x → g⁻¹ x = z := fun x z h => by
    rw [Equiv.Perm.inv_eq_iff_eq, h]
  set y' := g * y * g⁻¹ with hy'
  have hy'J : y' ∈ longInvAt (Equiv.Perm Ψ) Ψ (g p₅) := conj_mem_longInvAt_perm ⟨hy, hp₅s⟩ g
  have hga : g a = a := gfix a (Ne.symm hp₂a) (Ne.symm hp₃a) hp₅a.symm
  have hgb : g b = b := gfix b (Ne.symm hp₂b) (Ne.symm hp₃b) hp₅b.symm
  have hy'a : y' a = b := by
    simp only [hy', Equiv.Perm.mul_apply, gi a a hga, hyab, hgb]
  set σ := y * y' with hσ
  have hσx : ∀ x, σ x = y (g (y (g⁻¹ x))) := fun x => rfl
  have s1 : σ p₁ = p₄ := by
    rw [hσx, gi p₁ p₁ (gfix p₁ hp₂1.symm (Ne.symm hp₃1) hp₁5), ← hp₂, g2]
  have s4 : σ p₄ = p₅ := by
    rw [hσx, gi p₄ p₄ (gfix p₄ hp₄2 hp₄3 hp₄5), hp₄, hyy, g3, hp₅]
  have s5 : σ p₅ = p₃ := by
    rw [hσx, gi p₅ p₃ g3, ← hp₄, gfix p₄ hp₄2 hp₄3 hp₄5, hp₄, hyy]
  have s3 : σ p₃ = p₂ := by
    rw [hσx, gi p₃ p₂ g2, hp₂, hyy, gfix p₁ hp₂1.symm (Ne.symm hp₃1) hp₁5]
  have s2 : σ p₂ = p₁ := by
    rw [hσx, gi p₂ p₅ g5, hp₅, g5, hp₂, hyy]
  refine ⟨y', hy'J.1, hy'a, p₁, hp₁a, hp₁b, ?_⟩
  have h5 : (σ ^ 5) p₁ = p₁ := by
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, s1, s4, s5, s3, s2]
  rw [show (6 : ℕ) = 1 + 5 from rfl, pow_add, pow_one, Equiv.Perm.mul_apply, h5, s1]
  exact hp₄1

end PermAux

section KSec

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]

structure KSec (V : Subgroup G) (α β : Ω) where
  D : HoltData (centralizerImage Ω V) (fixSet Ω V)
  c₀ : D.ι
  eq_c₀ : ∀ k, k = c₀
  alt : D.M c₀ = alternatingGroup (D.Ψc c₀)
  surj : Function.Surjective (D.ρ c₀)
  a : fixSet Ω V
  b : fixSet Ω V
  ha : (a : Ω) = α
  hb : (b : Ω) = β
  hab : D.coord a c₀ ≠ D.coord b c₀

namespace KSec

variable {V : Subgroup G} {α β : Ω} (K : KSec V α β)

abbrev κ (ω : fixSet Ω V) : K.D.Ψc K.c₀ := K.D.coord ω K.c₀

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_orbit_of_κ_eq {ω ω' : fixSet Ω V} (h : K.κ ω = K.κ ω') :
    ω' ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) ω :=
  (K.D.coord_eq_iff ω ω').mp (funext fun k => by obtain rfl := K.eq_c₀ k; exact h)


theorem κ_holtDelta (hS : Sec4Setting G Ω) (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V))
    (p : K.D.Ψc K.c₀) :
    (∃ ω : fixSet Ω V, (ω : Ω) ∈ holtDelta G Ω α β ∧ K.κ ω = p) ↔
      p ≠ K.κ K.a ∧ p ≠ K.κ K.b := by
  have hab' : K.a ≠ K.b := fun h => K.hab (by rw [h])
  have hmem : ∀ ω : fixSet Ω V, ω ∈ holtDelta (centralizerImage Ω V) (fixSet Ω V) K.a K.b ↔
      (ω : Ω) ∈ holtDelta G Ω α β := fun ω => by
    rw [hS.mem_holtDelta_centralizerImage_iff hV h3 hab', K.ha, K.hb]
  have hcompl := K.D.holtDelta_range_rho_eq_compl K.alt K.hab
  constructor
  · rintro ⟨ω, hω, rfl⟩
    have := K.D.coord_mem_holtDelta ((hmem ω).mpr hω) K.c₀
    rw [hcompl] at this
    simpa [not_or] using this
  · rintro ⟨hpa, hpb⟩
    obtain ⟨y, hy⟩ := K.D.coord_surjective (Function.update (K.D.coord K.a) K.c₀ p)
    have hpi : K.D.coord y ∈ Set.univ.pi fun i => holtDelta (K.D.ρ i).range (K.D.Ψc i)
        (K.D.coord K.a i) (K.D.coord K.b i) := fun i _ => by
      obtain rfl := K.eq_c₀ i
      show K.D.coord y K.c₀ ∈ holtDelta (K.D.ρ K.c₀).range (K.D.Ψc K.c₀) _ _
      rw [hy, Function.update_self, hcompl]
      simp [hpa, hpb]
    rw [← K.D.coord_holtDelta_eq] at hpi
    obtain ⟨ω, hω, hωy⟩ := hpi
    refine ⟨ω, (hmem ω).mp hω, ?_⟩
    show K.D.coord ω K.c₀ = p
    rw [hωy, hy, Function.update_self]

theorem exists_realize (hS : Sec4Setting G Ω) (hV : IsPGroup 2 V) (h3 : 3 ≤ Nat.card (fixSet Ω V))
    {y : Equiv.Perm (K.D.Ψc K.c₀)} (hy : y ∈ longInv (Equiv.Perm (K.D.Ψc K.c₀)) (K.D.Ψc K.c₀))
    (hyab : y (K.κ K.a) = K.κ K.b) :
    ∃ (c : G) (hcV : c ∈ Subgroup.centralizer (V : Set G)), c ∈ longInvSwap G Ω α β ∧
      ∀ ω : fixSet Ω V, K.κ ((centralizerImageElt (Ω := Ω) hcV : centralizerImage Ω V) • ω) =
        y (K.κ ω) := by
  classical
  set y' : ∀ i, Equiv.Perm (K.D.Ψc i) := Function.update (fun _ => 1) K.c₀ y with hy'
  obtain ⟨u, hu, hρu⟩ := K.D.exists_mem_longInvSwap_rho_eq (α := K.a) (β := K.b) y'
    (fun i => by obtain rfl := K.eq_c₀ i; rw [hy', Function.update_self]; exact K.surj y)
    (fun i => by obtain rfl := K.eq_c₀ i; rw [hy', Function.update_self]; exact hy)
    (fun i => by obtain rfl := K.eq_c₀ i; rw [hy', Function.update_self]; exact hyab)
  obtain ⟨c, hc, hcV, hcu⟩ :=
    (hS.mem_longInvSwap_centralizerImage_iff hV h3 (u : centralizerImage Ω V)).mp hu
  rw [K.ha, K.hb] at hc
  refine ⟨c, hcV, hc, fun ω => ?_⟩
  have he : (centralizerImageElt (Ω := Ω) hcV : centralizerImage Ω V) • ω =
      ((u : centralizerImage Ω V)) • ω := Subtype.ext (hcu ω).symm
  rw [he]
  show K.D.coord (((u : centralizerImage Ω V)) • ω) K.c₀ = _
  rw [K.D.coord_smul u ω K.c₀, hρu K.c₀, hy', Function.update_self]

omit [FaithfulSMul G Ω] in
theorem coord_smul_eq_iff_of_mem_longInvSwap (hS : Sec4Setting G Ω) {α β : Ω}
    (A : CaseAData G Ω α β) {c : G} (hc : c ∈ longInvSwap G Ω α β) (j : A.D.ι)
    (δ δ' : holtDelta G Ω α β) :
    A.D.coord (twoPointElt (closure_longInvSwap_le_stabilizer_pair α β
        (Subgroup.subset_closure hc)) • δ) j =
      A.D.coord (twoPointElt (closure_longInvSwap_le_stabilizer_pair α β
        (Subgroup.subset_closure hc)) • δ') j ↔ A.D.coord δ j = A.D.coord δ' j := by
  set cΔ : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    ⟨twoPointElt _, twoPointElt_mem_jHull hS.star (Subgroup.subset_closure hc)⟩
  rw [A.D.coord_smul cΔ δ j, A.D.coord_smul cΔ δ' j]
  exact (A.D.ρ j cΔ).injective.eq_iff

theorem κ_eq_of_coord_eq (hS : Sec4Setting G Ω) (hαβ : α ≠ β) (A : CaseAData G Ω α β)
    (hV : IsPGroup 2 V) (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β)
    (h3 : 3 ≤ Nat.card (fixSet Ω V)) (h7 : 7 ≤ Fintype.card (K.D.Ψc K.c₀))
    (hodd : Odd (Fintype.card (K.D.Ψc K.c₀))) {j : A.D.ι} (hj : 4 ≤ (proj A V j).ncard)
    {δ δ' : holtDelta G Ω α β} (hδ : (δ : Ω) ∈ fixSet Ω V) (hδ' : (δ' : Ω) ∈ fixSet Ω V)
    (hjj : A.D.coord δ j = A.D.coord δ' j) : K.κ ⟨δ, hδ⟩ = K.κ ⟨δ', hδ'⟩ := by
  classical
  by_contra hne
  set aΨ := K.κ K.a with haΨ
  set bΨ := K.κ K.b with hbΨ
  have hκΛ : ∀ (ε : holtDelta G Ω α β) (hε : (ε : Ω) ∈ fixSet Ω V),
      K.κ ⟨ε, hε⟩ ≠ aΨ ∧ K.κ ⟨ε, hε⟩ ≠ bΨ := fun ε hε =>
    (K.κ_holtDelta hS hV h3 _).mp ⟨⟨ε, hε⟩, ε.2, rfl⟩
  have hA : ∀ (ε ε' : holtDelta G Ω α β) (hε : (ε : Ω) ∈ fixSet Ω V)
      (hε' : (ε' : Ω) ∈ fixSet Ω V), K.κ ⟨ε, hε⟩ = K.κ ⟨ε', hε'⟩ →
      A.D.coord ε j = A.D.coord ε' j := fun ε ε' hε hε' h =>
    coord_eq_of_mem_orbit hS hαβ A hV hVαβ h3 hj hε hε' (K.mem_orbit_of_κ_eq h)
  let Ψ' := {p : K.D.Ψc K.c₀ // p ≠ aΨ ∧ p ≠ bΨ}
  let R : Ψ' → Ψ' → Prop := fun e e' => ∃ (ε ε' : holtDelta G Ω α β)
    (hε : (ε : Ω) ∈ fixSet Ω V) (hε' : (ε' : Ω) ∈ fixSet Ω V),
    K.κ ⟨ε, hε⟩ = (e : K.D.Ψc K.c₀) ∧ K.κ ⟨ε', hε'⟩ = (e' : K.D.Ψc K.c₀) ∧
      A.D.coord ε j = A.D.coord ε' j
  have hR : ∀ e e', R e e' → ∀ (ε ε' : holtDelta G Ω α β) (hε : (ε : Ω) ∈ fixSet Ω V)
      (hε' : (ε' : Ω) ∈ fixSet Ω V), K.κ ⟨ε, hε⟩ = (e : K.D.Ψc K.c₀) →
      K.κ ⟨ε', hε'⟩ = (e' : K.D.Ψc K.c₀) → A.D.coord ε j = A.D.coord ε' j := by
    rintro e e' ⟨η, η', hη, hη', he, he', hηη'⟩ ε ε' hε hε' h1 h2
    rw [hA ε η hε hη (h1.trans he.symm), hηη', hA η' ε' hη' hε' (he'.trans h2.symm)]
  let H : Subgroup (Equiv.Perm Ψ') :=
    { carrier := {σ | ∀ e e', R e e' ↔ R (σ e) (σ e')}
      mul_mem' := fun {σ τ} hσ hτ e e' => (hτ e e').trans (hσ _ _)
      one_mem' := fun e e' => Iff.rfl
      inv_mem' := fun {σ} hσ e e' => by
        have := hσ (σ⁻¹ e) (σ⁻¹ e')
        simpa using this.symm }
  have hJH : longInv (Equiv.Perm Ψ') Ψ' ⊆ H := by
    intro y hy
    obtain ⟨hŷ, hŷa, hŷp⟩ := extend_mem_longInv K.hab hy
    obtain ⟨c, hcV, hc, hcκ⟩ := K.exists_realize hS hV h3 hŷ hŷa
    have hc2 := closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hc)
    have hstep : ∀ e e', R e e' → R (y e) (y e') := by
      rintro e e' ⟨ε, ε', hε, hε', he, he', hεε'⟩
      have hcε : ((twoPointElt hc2 • ε : holtDelta G Ω α β) : Ω) ∈ fixSet Ω V :=
        smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hcV) hε
      have hcε' : ((twoPointElt hc2 • ε' : holtDelta G Ω α β) : Ω) ∈ fixSet Ω V :=
        smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hcV) hε'
      refine ⟨_, _, hcε, hcε', ?_, ?_,
        (coord_smul_eq_iff_of_mem_longInvSwap hS A hc j ε ε').mpr hεε'⟩
      · have := hcκ ⟨ε, hε⟩
        rw [he, hŷp] at this
        exact this
      · have := hcκ ⟨ε', hε'⟩
        rw [he', hŷp] at this
        exact this
    intro e e'
    refine ⟨hstep e e', fun h => ?_⟩
    have := hstep _ _ h
    rwa [CCL.apply_apply_of_mem_longInv hy, CCL.apply_apply_of_mem_longInv hy] at this
  have hcard' : Fintype.card Ψ' = Fintype.card (K.D.Ψc K.c₀) - 2 := card_compl_pair K.hab
  have hAlt : alternatingGroup Ψ' ≤ H := alternatingGroup_le_of_longInv_subset
    (by omega) (by rw [hcard']; exact Nat.Odd.sub_even (by omega) hodd even_two) hJH
  have := alternatingGroup.isMultiplyPretransitive Ψ'
  have : IsMultiplyPretransitive (alternatingGroup Ψ') Ψ' 2 :=
    isMultiplyPretransitive_of_le (n := Nat.card Ψ' - 2) (by
      rw [Nat.card_eq_fintype_card]; omega) (by omega)
  set P : Ψ' := ⟨K.κ ⟨δ, hδ⟩, hκΛ δ hδ⟩
  set P' : Ψ' := ⟨K.κ ⟨δ', hδ'⟩, hκΛ δ' hδ'⟩
  have hPP' : P ≠ P' := fun h => hne (congrArg Subtype.val h)
  have hRPP' : R P P' := ⟨δ, δ', hδ, hδ', rfl, rfl, hjj⟩
  have hall : ∀ e : Ψ', e ≠ P → R P e := by
    intro e he
    let f : Fin 2 ↪ Ψ' := ⟨![P, P'], injective_vec_two hPP'⟩
    let g : Fin 2 ↪ Ψ' := ⟨![P, e], injective_vec_two (Ne.symm he)⟩
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (alternatingGroup Ψ') f g
    have h0 : (σ : Equiv.Perm Ψ') P = P := congrArg (fun F : Fin 2 ↪ Ψ' => F 0) hσ
    have h1 : (σ : Equiv.Perm Ψ') P' = e := congrArg (fun F : Fin 2 ↪ Ψ' => F 1) hσ
    have := (hAlt σ.2 P P').mp hRPP'
    rwa [h0, h1] at this
  have hconst : ∀ c ∈ proj A V j, c = A.D.coord δ j := by
    rintro c ⟨ε, hε, rfl⟩
    by_cases he : K.κ ⟨ε, hε⟩ = K.κ ⟨δ, hδ⟩
    · exact hA ε δ hε hδ he
    · exact (hR P ⟨_, hκΛ ε hε⟩ (hall _ fun h => he (congrArg Subtype.val h)) δ ε hδ hε rfl
        rfl).symm
  have hle : (proj A V j).ncard ≤ 1 := by
    refine (Set.ncard_le_ncard (t := {A.D.coord δ j}) (fun c hc => hconst c hc)
      (Set.toFinite _)).trans ?_
    rw [Set.ncard_singleton]
  omega

theorem vRel_of_four_le (hS : Sec4Setting G Ω) (hαβ : α ≠ β) (A : CaseAData G Ω α β)
    (hV : IsPGroup 2 V) (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β)
    (h3 : 3 ≤ Nat.card (fixSet Ω V)) (h7 : 7 ≤ Fintype.card (K.D.Ψc K.c₀))
    (hodd : Odd (Fintype.card (K.D.Ψc K.c₀))) {j k : A.D.ι} (hj : 4 ≤ (proj A V j).ncard)
    (hk : 4 ≤ (proj A V k).ncard) : VRel A V j k := by
  classical
  by_contra hjk
  obtain ⟨c₁, ⟨x, hx, rfl⟩, c₂, ⟨y, hy, rfl⟩, hne⟩ :=
    (Set.one_lt_ncard (Set.toFinite _)).mp (by omega : 1 < (proj A V j).ncard)
  obtain ⟨z, hz, hzc⟩ := exists_splice hVαβ j hx hy
  have hzj : A.D.coord z j = A.D.coord y j := by rw [hzc j, ite_eq_left (VRel.refl j)]
  have hzk : A.D.coord z k = A.D.coord x k := by rw [hzc k, ite_eq_right hjk]
  have h1 := K.κ_eq_of_coord_eq hS hαβ A hV hVαβ h3 h7 hodd hk hz hx hzk
  have h2 := coord_eq_of_mem_orbit hS hαβ A hV hVαβ h3 hj hz hx (K.mem_orbit_of_κ_eq h1)
  exact hne (h2.symm.trans hzj)

end KSec

end KSec

end CaseAD

end CFSG.Holt.H78
