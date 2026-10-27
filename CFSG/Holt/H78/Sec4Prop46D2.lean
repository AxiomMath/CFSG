module

public import CFSG.Holt.H78.Sec4Prop46D
public import CFSG.Holt.H78.Sec4Prop46A3

public section

namespace CFSG.Holt.H78

namespace CaseAD

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section KSec

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]

namespace KSec

variable {V : Subgroup G} {α β : Ω} (K : KSec V α β)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem ncard_range_eq_of_iff {T X Y : Type*} (f : T → X) (g : T → Y)
    (h : ∀ t t', f t = f t' ↔ g t = g t') : (Set.range f).ncard = (Set.range g).ncard := by
  classical
  refine Set.ncard_congr (fun x hx => g (Classical.choose hx)) (fun x hx => ⟨_, rfl⟩)
    (fun x x' hx hx' hxx' => ?_) (fun y ⟨t, ht⟩ => ⟨f t, ⟨t, rfl⟩, ?_⟩)
  · rw [← Classical.choose_spec hx, ← Classical.choose_spec hx']
    exact (h _ _).mpr hxx'
  · rw [← ht]
    exact (h _ _).mp (Classical.choose_spec (⟨t, rfl⟩ : f t ∈ Set.range f))

theorem ncard_proj_add_two (hS : Sec4Setting G Ω) (hαβ : α ≠ β) (A : CaseAData G Ω α β)
    (hV : IsPGroup 2 V) (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β)
    (h3 : 3 ≤ Nat.card (fixSet Ω V)) (h7 : 7 ≤ Fintype.card (K.D.Ψc K.c₀))
    (hodd : Odd (Fintype.card (K.D.Ψc K.c₀))) {j : A.D.ι} (hj : 4 ≤ (proj A V j).ncard) :
    (proj A V j).ncard + 2 = Fintype.card (K.D.Ψc K.c₀) := by
  classical
  let T := {δ : holtDelta G Ω α β // (δ : Ω) ∈ fixSet Ω V}
  let f : T → A.D.Ψc j := fun t => A.D.coord t.1 j
  let g : T → K.D.Ψc K.c₀ := fun t => K.κ ⟨t.1, t.2⟩
  have hf : Set.range f = proj A V j := by
    ext c
    exact ⟨fun ⟨t, ht⟩ => ⟨t.1, t.2, ht⟩, fun ⟨δ, hδ, hc⟩ => ⟨⟨δ, hδ⟩, hc⟩⟩
  have hg : Set.range g = {p | p ≠ K.κ K.a ∧ p ≠ K.κ K.b} := by
    ext p
    refine ⟨fun ⟨t, ht⟩ => ht ▸ (K.κ_holtDelta hS hV h3 _).mp ⟨⟨t.1, t.2⟩, t.1.2, rfl⟩,
      fun hp => ?_⟩
    obtain ⟨ω, hω, hωp⟩ := (K.κ_holtDelta hS hV h3 p).mpr hp
    exact ⟨⟨⟨ω, hω⟩, ω.2⟩, hωp⟩
  have hfg : ∀ t t', f t = f t' ↔ g t = g t' := fun t t' =>
    ⟨fun h => K.κ_eq_of_coord_eq hS hαβ A hV hVαβ h3 h7 hodd hj t.2 t'.2 h,
      fun h => coord_eq_of_mem_orbit hS hαβ A hV hVαβ h3 hj t.2 t'.2 (K.mem_orbit_of_κ_eq h)⟩
  have h1 := ncard_range_eq_of_iff f g hfg
  rw [hf, hg] at h1
  have h2 : ({p | p ≠ K.κ K.a ∧ p ≠ K.κ K.b} : Set (K.D.Ψc K.c₀)).ncard =
      Fintype.card (K.D.Ψc K.c₀) - 2 := by
    rw [← card_compl_pair K.hab, ← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    rfl
  omega

omit [FaithfulSMul G Ω] in
theorem mapsDir_of_mem_longInvSwap (hS : Sec4Setting G Ω) {α β : Ω} (A : CaseAData G Ω α β)
    {c : G} (hc : c ∈ longInvSwap G Ω α β) (k : A.D.ι) : MapsDir A c k k := by
  intro δ₁ δ₂ δ₁' δ₂' e₁ e₂
  have hc2 := closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hc)
  rw [(Subtype.ext e₁ : δ₁' = twoPointElt hc2 • δ₁), (Subtype.ext e₂ : δ₂' = twoPointElt hc2 • δ₂)]
  exact coord_smul_eq_iff_of_mem_longInvSwap hS A hc k δ₁ δ₂

theorem exists_four_le_proj (hS : Sec4Setting G Ω) (hαβ : α ≠ β) (A : CaseAData G Ω α β)
    (hV : IsPGroup 2 V) (hVαβ : V ≤ stabilizer G α ⊓ stabilizer G β)
    (h3 : 3 ≤ Nat.card (fixSet Ω V)) (h7 : 7 ≤ Fintype.card (K.D.Ψc K.c₀)) :
    ∃ j, 4 ≤ (proj A V j).ncard := by
  classical
  by_contra hcon
  push Not at hcon
  have hsmall : ∀ k, (proj A V k).ncard ≤ 3 := fun k => by have := hcon k; omega
  obtain ⟨u, hu, huV⟩ := hS.exists_mem_longInvSwap_centralizer hαβ hV hVαβ
  have hu' : u ∈ longInvSwap G Ω (K.a : Ω) (K.b : Ω) := by rw [K.ha, K.hb]; exact hu
  have huK : (centralizerImageElt (Ω := Ω) huV : centralizerImage Ω V) ∈
      longInvSwap (centralizerImage Ω V) (fixSet Ω V) K.a K.b :=
    (hS.mem_longInvSwap_centralizerImage_iff hV h3 _).mpr ⟨u, hu', huV, fun _ => rfl⟩
  set uJ : jHull (centralizerImage Ω V) (fixSet Ω V) := ⟨_, mem_jHull_of_mem_longInv huK.1⟩
  have hy₁ := K.D.rho_mem_longInv huK.1 K.c₀
  have hy₁ab : K.D.ρ K.c₀ uJ (K.κ K.a) = K.κ K.b := by
    rw [← K.D.coord_smul uJ K.a K.c₀]
    exact congrArg (K.D.coord · K.c₀) huK.2
  have hκu : ∀ ω, K.κ ((centralizerImageElt (Ω := Ω) huV : centralizerImage Ω V) • ω) =
      K.D.ρ K.c₀ uJ (K.κ ω) := fun ω => K.D.coord_smul uJ ω K.c₀
  obtain ⟨y₂, hy₂, hy₂ab, p, hpa, hpb, hp6⟩ := exists_mul_pow_six_ne h7 K.hab hy₁ hy₁ab
  obtain ⟨c, hcV, hc, hcκ⟩ := K.exists_realize hS hV h3 hy₂ hy₂ab
  set g := u * c with hgdef
  have hgC : g ∈ Subgroup.centralizer (V : Set G) := mul_mem huV hcV
  have hu2 := closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hu)
  have hc2 := closure_longInvSwap_le_stabilizer_pair α β (Subgroup.subset_closure hc)
  have hg2 : g ∈ stabilizer G ({α, β} : Set Ω) := mul_mem hu2 hc2
  have hgk : ∀ k, MapsDir A g k k := fun k =>
    (mapsDir_of_mem_longInvSwap hS A hc k).mul A hc2 (mapsDir_of_mem_longInvSwap hS A hu k)
  have hκg : ∀ (n : ℕ) (ω : fixSet Ω V),
      K.κ ((centralizerImageElt (Ω := Ω) (pow_mem hgC n) : centralizerImage Ω V) • ω) =
        ((K.D.ρ K.c₀ uJ * y₂) ^ n) (K.κ ω) := by
    intro n
    induction n with
    | zero =>
      intro ω
      have he : (centralizerImageElt (Ω := Ω) (pow_mem hgC 0) : centralizerImage Ω V) • ω = ω :=
        Subtype.ext (by show g ^ 0 • (ω : Ω) = ω; rw [pow_zero, one_smul])
      rw [he, pow_zero, Equiv.Perm.one_apply]
    | succ n ih =>
      intro ω
      have he : (centralizerImageElt (Ω := Ω) (pow_mem hgC (n + 1)) : centralizerImage Ω V) •
          ω = (centralizerImageElt (Ω := Ω) huV : centralizerImage Ω V) •
            ((centralizerImageElt (Ω := Ω) hcV : centralizerImage Ω V) •
              ((centralizerImageElt (Ω := Ω) (pow_mem hgC n) : centralizerImage Ω V) • ω)) :=
        Subtype.ext (by
          show g ^ (n + 1) • (ω : Ω) = u • c • g ^ n • (ω : Ω)
          rw [pow_succ', mul_smul, hgdef, mul_smul])
      rw [he, hκu, hcκ, ih, pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  obtain ⟨ω, hωΔ, hωp⟩ := (K.κ_holtDelta hS hV h3 p).mpr ⟨hpa, hpb⟩
  have h6 := pow_six_smul_eq hg2 (Subgroup.centralizer_le_normalizer _ hgC) hgk hsmall
    (δ := ⟨ω, hωΔ⟩) ω.2
  have h6' : (centralizerImageElt (Ω := Ω) (pow_mem hgC 6) : centralizerImage Ω V) • ω = ω :=
    Subtype.ext h6
  have := hκg 6 ω
  rw [h6', hωp] at this
  exact hp6 this.symm

end KSec

end KSec

section Reduction

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω] [FaithfulSMul G Ω]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mem_twoPointNormalizer_of_mapsDir {α β : Ω} (A : CaseAData G Ω α β) {g : G}
    (hg : g ∈ stabilizer G ({α, β} : Set Ω)) (γ : holtDelta G Ω α β) {j : A.D.ι}
    (hj : MapsDir A g j j) : g ∈ twoPointNormalizer G Ω α β (A.D.L j) := by
  obtain ⟨σ, hσ⟩ := A.D.conj_L (twoPointElt hg)
  have hσj : MapsDir A g j (σ j) := fun δ₁ δ₂ δ₁' δ₂' e₁ e₂ => by
    rw [(Subtype.ext e₁ : δ₁' = twoPointElt hg • δ₁),
      (Subtype.ext e₂ : δ₂' = twoPointElt hg • δ₂)]
    exact A.D.coord_smul_eq_iff_of_conj A.oddCore_eq_bot hσ j δ₁ δ₂
  have h := MapsDir.eq A hg γ hσj hj
  rw [mem_twoPointNormalizer]
  refine ⟨hg, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have := hσ j
  rw [h] at this
  exact this.symm

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem ncard_proj_eq_of_mapsDir {α β : Ω} (A : CaseAData G Ω α β) {V : Subgroup G} {g : G}
    (hg : g ∈ stabilizer G ({α, β} : Set Ω)) (hgV : g ∈ Subgroup.normalizer (V : Set G))
    {j k : A.D.ι} (hjk : MapsDir A g j k) : (proj A V k).ncard = (proj A V j).ncard := by
  classical
  let T := {δ : holtDelta G Ω α β // (δ : Ω) ∈ fixSet Ω V}
  let f : T → A.D.Ψc j := fun t => A.D.coord t.1 j
  let f' : T → A.D.Ψc k := fun t => A.D.coord (twoPointElt hg • t.1) k
  have hff : ∀ t t', f t = f t' ↔ f' t = f' t' := fun t t' =>
    (hjk t.1 t'.1 _ _ rfl rfl).symm
  have hf : Set.range f = proj A V j := by
    ext c
    exact ⟨fun ⟨t, ht⟩ => ⟨t.1, t.2, ht⟩, fun ⟨δ, hδ, hc⟩ => ⟨⟨δ, hδ⟩, hc⟩⟩
  have hf' : Set.range f' = proj A V k := by
    ext c
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, smul_mem_fixSet_of_mem_normalizer hgV t.2, rfl⟩
    · rintro ⟨δ, hδ, rfl⟩
      have hginv : g⁻¹ ∈ stabilizer G ({α, β} : Set Ω) := inv_mem hg
      refine ⟨⟨twoPointElt hginv • δ, smul_mem_fixSet_of_mem_normalizer (inv_mem hgV) hδ⟩, ?_⟩
      show A.D.coord (twoPointElt hg • twoPointElt hginv • δ) k = _
      congr 2
      exact Subtype.ext (smul_inv_smul g (δ : Ω))
  have := KSec.ncard_range_eq_of_iff f f' hff
  rw [hf, hf'] at this
  exact this.symm

@[expose] def KSec.ofSection {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}
    {X : CaseAStart G Ω α v P} {V : Subgroup G} {τ : G} (S : CaseASection X V τ)
    (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) {β₁ : Ω} (hb₁ : β₁ ∈ fixSet Ω V)
    (horb : (⟨β₁, hb₁⟩ : fixSet Ω V) ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V))
      S.ptβ) : KSec V α β₁ where
  D := S.D
  c₀ := S.c₀
  eq_c₀ := S.eq_c₀ hS hP
  alt := S.alt
  surj := S.rho_surjective
  a := S.ptα
  b := ⟨β₁, hb₁⟩
  ha := rfl
  hb := rfl
  hab := by
    rw [(S.mem_orbit_iff hS hP _ _).mp horb]
    exact S.coord_ne_three.1

variable {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)}

structure DCase (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P) where
  X : CaseAStart G Ω α v P
  V : Subgroup G
  sylow : fusionIsSylowIn 2 V (caseACentralizer G Ω α X.β v X.Λ)
  w_mem : X.w ∈ Subgroup.normalizer (V : Set G)
  kappa : IsKappaMaximal X V
  r : G
  β₁ : Ω
  γ₁ : Ω
  r_two : IsPGroup 2 (Subgroup.zpowers r)
  r_mem : r ∈ Subgroup.centralizer (V : Set G)
  r_comm : Commute r v
  r_α : r • α = α
  fixSet_eq : fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r) = {α, β₁, γ₁}
  mem_β₁ : β₁ ∈ p46Orbit G Ω v P α
  mem_γ₁ : γ₁ ∈ p46Orbit G Ω v P α
  γ₁_mem : γ₁ ∈ holtDelta G Ω α β₁
  v_γ₁ : v • γ₁ = γ₁
  β₁_fix : β₁ ∈ fixSet Ω V
  γ₁_fix : γ₁ ∈ fixSet Ω V
  S : CaseASection X V 1
  orb_β : (⟨β₁, β₁_fix⟩ : fixSet Ω V) ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptβ
  orb_γ : (⟨γ₁, γ₁_fix⟩ : fixSet Ω V) ∈ orbit (jOddCore (centralizerImage Ω V) (fixSet Ω V)) S.ptγ
  A₁ : CaseAData G Ω α β₁
  two_le : 2 ≤ Fintype.card A₁.D.ι
  i₀ : A₁.D.ι
  k₀ : A₁.D.ι
  ne : k₀ ≠ i₀
  big_i₀ : 4 ≤ (proj A₁ V i₀).ncard
  big_k₀ : 4 ≤ (proj A₁ V k₀).ncard

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem sup_le_normalizer {V : Subgroup G} {r : G} (hvV : v ∈ Subgroup.centralizer (V : Set G))
    (hrV : r ∈ Subgroup.centralizer (V : Set G)) :
    V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r ≤ Subgroup.normalizer (V : Set G) :=
  sup_le (sup_le Subgroup.le_normalizer
    (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hvV)))
    (Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hrV))

theorem caseAStepA7_of_false (hS : Sec4Setting G Ω) (hP : Prop46Setup G Ω α v P)
    (hfalse : DCase hS hP → False) : CaseAStepA7 G Ω α v P := by
  classical
  intro X V hVs hVw hκ r β₁ γ₁ hr2 hrV hrv hrα hfix hβ₁ hγ₁C hγ₁ hvγ₁ h5 horb A₁ h2
  obtain ⟨hb, hb₁, hc, hc₁, horbβ, horbγ⟩ := horb
  obtain ⟨S⟩ := X.exists_section hS hP hVs hVw isPGroup_zpowers_one (Subgroup.one_mem _)
    (Commute.one_left v)
  have hαβ₁ : α ≠ β₁ := fun h => by
    subst h
    have h1 : (holtDelta G Ω α α ∩ fixSet Ω V).ncard ≤ 1 :=
      (Set.ncard_le_ncard (Set.inter_subset_left.trans (holtDelta_self_subset α))
        (Set.toFinite _)).trans (by rw [Set.ncard_singleton])
    omega
  have hmemX : ∀ ω ∈ ({α, β₁, γ₁} : Set Ω),
      ω ∈ fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r) := fun ω hω => by
    rw [hfix]; exact hω
  have hfixV : fixSet Ω (V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers r) ⊆ fixSet Ω V :=
    fixSet_anti (le_sup_left.trans le_sup_left)
  have hVαβ₁ : V ≤ stabilizer G α ⊓ stabilizer G β₁ := fun g hg =>
    ⟨hfixV (hmemX α (by simp)) g hg, hfixV (hmemX β₁ (by simp)) g hg⟩
  have h3 := X.three_le_card_fixSet S.sylow.1
  set K := KSec.ofSection S hS hP hb₁ horbβ with hK
  have h7 : 7 ≤ Fintype.card (K.D.Ψc K.c₀) := S.seven_le_card
  obtain ⟨j, hj⟩ := K.exists_four_le_proj hS hαβ₁ A₁ S.sylow.2.1 hVαβ₁ h3 h7
  by_cases hD : ∃ k, k ≠ j ∧ 4 ≤ (proj A₁ V k).ncard
  · obtain ⟨k, hkj, hk⟩ := hD
    exact (hfalse ⟨X, V, hVs, hVw, hκ, r, β₁, γ₁, hr2, hrV, hrv, hrα, hfix, hβ₁, hγ₁C, hγ₁,
      hvγ₁, hb₁, hc₁, S, horbβ, horbγ, A₁, h2, j, k, hkj, hj, hk⟩).elim
  · push Not at hD
    refine ⟨j, fun g hg => ?_⟩
    have hg2 : g ∈ stabilizer G ({α, β₁} : Set Ω) :=
      stabilizer_inf_le_stabilizer_pair α β₁ ⟨hmemX α (by simp) g hg, hmemX β₁ (by simp) g hg⟩
    have hvV : v ∈ Subgroup.centralizer (V : Set G) := S.v_mem
    have hgV := sup_le_normalizer hvV hrV hg
    obtain ⟨σ, hσ⟩ := exists_mapsDir A₁ hg2
    have hσj : σ j = j := by
      by_contra hne
      have := ncard_proj_eq_of_mapsDir A₁ hg2 hgV (hσ j)
      have h4 := hD (σ j) hne
      omega
    have hjj := hσ j
    rw [hσj] at hjj
    exact mem_twoPointNormalizer_of_mapsDir A₁ hg2 ⟨γ₁, hγ₁⟩ hjj

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem mapsDir_of_mem_twoPointNormalizer {α β : Ω} (A : CaseAData G Ω α β) {g : G} {j : A.D.ι}
    (hg : g ∈ twoPointNormalizer G Ω α β (A.D.L j)) : MapsDir A g j j := by
  obtain ⟨hg', hN⟩ := mem_twoPointNormalizer.mp hg
  intro δ₁ δ₂ δ₁' δ₂' e₁ e₂
  rw [(Subtype.ext e₁ : δ₁' = twoPointElt hg' • δ₁), (Subtype.ext e₂ : δ₂' = twoPointElt hg' • δ₂)]
  exact (A.D.normalizer_L_preserves_fibres hN δ₁ δ₂).1

end Reduction

section CoordPerm

variable {G : Type} [Group G] {Ω : Type} [MulAction G Ω] {α β : Ω} (A : CaseAData G Ω α β)

@[expose] noncomputable def coordEquiv : holtDelta G Ω α β ≃ ∀ i, A.D.Ψc i :=
  Equiv.ofBijective A.D.coord ⟨CaseAData.coord_injective A, A.D.coord_surjective⟩

@[expose] noncomputable def coordPerm (m : ∀ k, Equiv.Perm (A.D.Ψc k)) :
    Equiv.Perm (holtDelta G Ω α β) :=
  (coordEquiv A).trans ((Equiv.piCongrRight m).trans (coordEquiv A).symm)

theorem coord_coordPerm (m : ∀ k, Equiv.Perm (A.D.Ψc k)) (δ : holtDelta G Ω α β) (k : A.D.ι) :
    A.D.coord (coordPerm A m δ) k = m k (A.D.coord δ k) := by
  show coordEquiv A ((coordEquiv A).symm _) k = _
  rw [Equiv.apply_symm_apply, Equiv.piCongrRight_apply]
  rfl

theorem coordPerm_mul (m m' : ∀ k, Equiv.Perm (A.D.Ψc k)) :
    coordPerm A (m * m') = coordPerm A m * coordPerm A m' :=
  Equiv.ext fun δ => CaseAData.coord_injective A (funext fun k => by
    rw [Equiv.Perm.mul_apply, coord_coordPerm, coord_coordPerm, coord_coordPerm, Pi.mul_apply,
      Equiv.Perm.mul_apply])

theorem coordPerm_one : coordPerm A 1 = 1 :=
  Equiv.ext fun δ => CaseAData.coord_injective A (funext fun k => by
    rw [coord_coordPerm, Equiv.Perm.one_apply, Pi.one_apply, Equiv.Perm.one_apply])

theorem coordPerm_eq_iff (m m' : ∀ k, Equiv.Perm (A.D.Ψc k)) :
    coordPerm A m = coordPerm A m' ↔ m = m' := by
  refine ⟨fun h => funext fun k => Equiv.ext fun c => ?_, fun h => h ▸ rfl⟩
  obtain ⟨δ, rfl⟩ := A.D.exists_coord_apply_eq k c
  rw [← coord_coordPerm, ← coord_coordPerm, h]

end CoordPerm

namespace DCase

variable {G : Type} [Group G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  {α : Ω} {v : G} {P : Subgroup (typeLSection G Ω v)} {hS : Sec4Setting G Ω}
  {hP : Prop46Setup G Ω α v P} (H : DCase hS hP)

abbrev 𝔛 : Subgroup G := H.V ⊔ Subgroup.zpowers v ⊔ Subgroup.zpowers H.r

theorem mem_fix_𝔛 {ω : Ω} (hω : ω ∈ ({α, H.β₁, H.γ₁} : Set Ω)) : ω ∈ fixSet Ω H.𝔛 := by
  rw [H.fixSet_eq]; exact hω

theorem fix_𝔛_subset : fixSet Ω H.𝔛 ⊆ fixSet Ω H.V :=
  fixSet_anti (le_sup_left.trans le_sup_left)

theorem V_le : H.V ≤ stabilizer G α ⊓ stabilizer G H.β₁ := fun g hg =>
  ⟨H.fix_𝔛_subset (H.mem_fix_𝔛 (by simp)) g hg, H.fix_𝔛_subset (H.mem_fix_𝔛 (by simp)) g hg⟩

theorem αβ₁ : α ≠ H.β₁ := fun h => by
  have h4 := H.big_i₀
  have hsub : proj H.A₁ H.V H.i₀ ⊆ Set.range (fun δ : holtDelta G Ω α H.β₁ =>
      H.A₁.D.coord δ H.i₀) := fun c ⟨δ, _, hc⟩ => ⟨δ, hc⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hrange : (Set.range (fun δ : holtDelta G Ω α H.β₁ => H.A₁.D.coord δ H.i₀)).ncard ≤ 1 := by
    rw [Set.ncard_le_one_iff_subsingleton]
    rintro _ ⟨⟨x, hx⟩, rfl⟩ _ ⟨⟨x', hx'⟩, rfl⟩
    have e1 := hx
    have e2 := hx'
    rw [← h] at e1 e2
    have hδ := holtDelta_self_subset α e1
    have hδ' := holtDelta_self_subset α e2
    rw [Set.mem_singleton_iff] at hδ hδ'
    subst hδ hδ'
    rfl
  omega

variable [Finite G] [FaithfulSMul G Ω]

@[expose] def K : KSec H.V α H.β₁ := KSec.ofSection H.S hS hP H.β₁_fix H.orb_β

omit [Finite G] [FaithfulSMul G Ω] in
theorem three_le : 3 ≤ Nat.card (fixSet Ω H.V) := H.X.three_le_card_fixSet H.sylow.1

theorem seven_le : 7 ≤ Fintype.card (H.K.D.Ψc H.K.c₀) := H.S.seven_le_card

theorem odd_card : Odd (Fintype.card (H.K.D.Ψc H.K.c₀)) := by
  have := H.S.card_mod_four
  exact Nat.odd_iff.mpr (by change Fintype.card (H.S.D.Ψc H.S.c₀) % 2 = 1; omega)

theorem card_Ψ : Fintype.card (H.K.D.Ψc H.K.c₀) = H.X.Λ.ncard + 2 := H.S.card

theorem ncard_proj {j : H.A₁.D.ι} (hj : 4 ≤ (proj H.A₁ H.V j).ncard) :
    (proj H.A₁ H.V j).ncard = H.X.Λ.ncard := by
  have := H.K.ncard_proj_add_two hS H.αβ₁ H.A₁ H.sylow.2.1 H.V_le H.three_le H.seven_le
    H.odd_card hj
  have h2 := H.card_Ψ
  omega

theorem vRel {j k : H.A₁.D.ι} (hj : 4 ≤ (proj H.A₁ H.V j).ncard)
    (hk : 4 ≤ (proj H.A₁ H.V k).ncard) : VRel H.A₁ H.V j k :=
  H.K.vRel_of_four_le hS H.αβ₁ H.A₁ H.sylow.2.1 H.V_le H.three_le H.seven_le H.odd_card hj hk

omit [Finite G] [FaithfulSMul G Ω] in
theorem exists_w : ∃ w ∈ longInvSwap G Ω α H.β₁, Commute w v ∧ w * v ∈ longInv G Ω :=
  hP.exists_w H.β₁ H.mem_β₁ H.αβ₁.symm

abbrev γ₁Δ : holtDelta G Ω α H.β₁ := ⟨H.γ₁, H.γ₁_mem⟩

@[expose] def line (j : H.A₁.D.ι) : Set Ω :=
  (↑) '' {δ : holtDelta G Ω α H.β₁ | ∀ k, k ≠ j → H.A₁.D.coord δ k = H.A₁.D.coord H.γ₁Δ k}

@[expose] noncomputable def lineStart (j : H.A₁.D.ι) : CaseAStart G Ω α v P where
  β := H.β₁
  mem := H.mem_β₁
  ne := H.αβ₁.symm
  A := H.A₁
  w := Classical.choose H.exists_w
  w_mem := (Classical.choose_spec H.exists_w).1
  w_comm := (Classical.choose_spec H.exists_w).2.1
  wv_mem := (Classical.choose_spec H.exists_w).2.2
  γ := H.γ₁Δ
  v_fix := H.v_γ₁
  Λ := H.line j
  admissible := Or.inl ⟨H.two_le, j, rfl⟩

omit [Finite G] [FaithfulSMul G Ω] in
theorem ncard_line (j : H.A₁.D.ι) : (H.line j).ncard = Fintype.card (H.A₁.D.Ψc j) :=
  CaseAData.ncard_line H.A₁ H.γ₁Δ j

omit [Finite G] [FaithfulSMul G Ω] in
theorem card_Ψc_le (j : H.A₁.D.ι) : Fintype.card (H.A₁.D.Ψc j) ≤ H.X.Λ.ncard := by
  rcases H.kappa (H.lineStart j) ⊥ bot_le IsPGroup.of_bot with h | h
  · have := H.ncard_line j
    change (H.line j).ncard < _ at h
    omega
  · have := H.ncard_line j
    have h' : (H.line j).ncard = H.X.Λ.ncard := h.1
    omega

omit [Finite G] [FaithfulSMul G Ω] in
theorem card_le_of_line {j : H.A₁.D.ι} (hj : Fintype.card (H.A₁.D.Ψc j) = H.X.Λ.ncard)
    {W : Subgroup G} (hW : W ≤ caseACentralizer G Ω α H.β₁ v (H.line j))
    (hW2 : IsPGroup 2 W) : Nat.card W ≤ Nat.card H.V := by
  rcases H.kappa (H.lineStart j) W hW hW2 with h | h
  · have := H.ncard_line j
    change (H.line j).ncard < _ at h
    omega
  · exact h.2

theorem proj_eq_univ {j : H.A₁.D.ι} (hj : 4 ≤ (proj H.A₁ H.V j).ncard) :
    Fintype.card (H.A₁.D.Ψc j) = H.X.Λ.ncard ∧ proj H.A₁ H.V j = Set.univ := by
  have h1 := H.ncard_proj hj
  have h2 := H.card_Ψc_le j
  have h3 : (proj H.A₁ H.V j).ncard ≤ Fintype.card (H.A₁.D.Ψc j) := by
    rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  refine ⟨by omega, Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)⟩
  rw [Set.ncard_univ, Nat.card_eq_fintype_card]
  omega

theorem coord_smul_eq {j : H.A₁.D.ι} (hj : 4 ≤ (proj H.A₁ H.V j).ncard) {g : G}
    (hgV : g ∈ H.V) (hgj : MapsDir H.A₁ g j j) (δ δ' : holtDelta G Ω α H.β₁)
    (hδ' : (δ' : Ω) = g • (δ : Ω)) : H.A₁.D.coord δ' j = H.A₁.D.coord δ j := by
  have hc : H.A₁.D.coord δ j ∈ proj H.A₁ H.V j := by
    rw [(H.proj_eq_univ hj).2]; exact Set.mem_univ _
  obtain ⟨ε, hε, hεj⟩ := hc
  have h1 := (hgj δ ε δ' ε hδ' (hε g hgV).symm).mpr hεj.symm
  rw [h1, hεj]

abbrev Vdir (j : H.A₁.D.ι) : Subgroup G := H.V ⊓ twoPointNormalizer G Ω α H.β₁ (H.A₁.D.L j)

omit [Finite G] [FaithfulSMul G Ω] in
theorem V_le_pair {g : G} (hg : g ∈ H.V) : g ∈ stabilizer G ({α, H.β₁} : Set Ω) :=
  stabilizer_inf_le_stabilizer_pair α H.β₁ (H.V_le hg)

omit [Finite G] [FaithfulSMul G Ω] in
theorem γ₁_fixV {g : G} (hg : g ∈ H.V) : g • H.γ₁ = H.γ₁ := H.γ₁_fix g hg

theorem Vdir_le {j : H.A₁.D.ι} (hj : 4 ≤ (proj H.A₁ H.V j).ncard) :
    H.Vdir j ≤ caseACentralizer G Ω α H.β₁ v (H.line j) := by
  intro g hg
  obtain ⟨hgV, hgN⟩ := Subgroup.mem_inf.mp hg
  have hgj := mapsDir_of_mem_twoPointNormalizer H.A₁ hgN
  have hg2 := H.V_le_pair hgV
  refine ⟨⟨?_, H.V_le hgV⟩, (mem_fixingSubgroup_iff G).mpr ?_⟩
  · have := (H.sylow.1 hgV).1.1
    exact this
  rintro _ ⟨δ, hδ, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_mapsDir H.A₁ hg2
  have hσj : σ j = j := (MapsDir.eq H.A₁ hg2 H.γ₁Δ (hσ j) hgj)
  refine congrArg Subtype.val (CaseAData.coord_injective H.A₁ (funext fun k => ?_) :
    twoPointElt hg2 • δ = δ)
  by_cases hk : k = j
  · subst hk
    exact H.coord_smul_eq hj hgV hgj δ _ rfl
  · obtain ⟨k', rfl⟩ := σ.surjective k
    have hk' : k' ≠ j := fun h => hk (by rw [h, hσj])
    have h1 := (hσ k' δ H.γ₁Δ (twoPointElt hg2 • δ) H.γ₁Δ rfl (H.γ₁_fixV hgV).symm).mpr
      (hδ k' hk')
    rw [h1, hδ (σ k') hk]

omit [Finite G] [FaithfulSMul G Ω] in
theorem card_V_le {j : H.A₁.D.ι} (hj : 4 ≤ (proj H.A₁ H.V j).ncard) :
    Nat.card H.V ≤ Nat.card (H.Vdir j) *
      (Finset.univ.filter fun k => 4 ≤ (proj H.A₁ H.V k).ncard).card := by
  classical
  set B := Finset.univ.filter fun k => 4 ≤ (proj H.A₁ H.V k).ncard
  set H' := (H.Vdir j).subgroupOf H.V
  let d : H.V → H.A₁.D.ι := fun g => Classical.choose (exists_mapsDir H.A₁ (H.V_le_pair g.2)) j
  have hd : ∀ g : H.V, MapsDir H.A₁ g j (d g) := fun g =>
    Classical.choose_spec (exists_mapsDir H.A₁ (H.V_le_pair g.2)) j
  have hdB : ∀ g : H.V, d g ∈ B := fun g => by
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ncard_proj_eq_of_mapsDir H.A₁ (H.V_le_pair g.2)
      (Subgroup.le_normalizer g.2) (hd g)]
    exact hj
  have hiff : ∀ g g' : H.V, d g = d g' ↔ g⁻¹ * g' ∈ H' := by
    intro g g'
    constructor
    · intro h
      have h1 : MapsDir H.A₁ ((g : G)⁻¹ * g') j j := (hd g').mul H.A₁ (H.V_le_pair g'.2)
        (h ▸ hd g).inv
      refine Subgroup.mem_subgroupOf.mpr ⟨(g⁻¹ * g').2, ?_⟩
      exact mem_twoPointNormalizer_of_mapsDir H.A₁ (H.V_le_pair (g⁻¹ * g').2) H.γ₁Δ h1
    · intro h
      have hh : MapsDir H.A₁ ((g : G)⁻¹ * g') j j :=
        mapsDir_of_mem_twoPointNormalizer H.A₁ (Subgroup.mem_inf.mp
          (Subgroup.mem_subgroupOf.mp h)).2
      have h2 : MapsDir H.A₁ ((g : G) * ((g : G)⁻¹ * g')) j (d g) :=
        hh.mul H.A₁ (H.V_le_pair (g⁻¹ * g').2) (hd g)
      rw [mul_inv_cancel_left] at h2
      exact MapsDir.eq H.A₁ (H.V_le_pair g'.2) H.γ₁Δ h2 (hd g')
  let F : H.V ⧸ H' → B := Quotient.lift (s := QuotientGroup.leftRel H')
    (fun g => ⟨d g, hdB g⟩) fun g g' hgg' =>
      Subtype.ext ((hiff g g').mpr (QuotientGroup.leftRel_apply.mp hgg'))
  have hF : Function.Injective F := by
    intro x y hxy
    induction x using Quotient.inductionOn
    induction y using Quotient.inductionOn
    exact Quotient.sound (QuotientGroup.leftRel_apply.mpr ((hiff _ _).mp
      (congrArg Subtype.val hxy)))
  have hidx : H'.index ≤ B.card := by
    have := Nat.card_le_card_of_injective F hF
    rw [Nat.card_eq_fintype_card (α := B), Fintype.card_coe] at this
    exact this
  have hcard : Nat.card H' = Nat.card (H.Vdir j) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [← Subgroup.card_mul_index H', hcard]
  exact Nat.mul_le_mul_left _ hidx

noncomputable abbrev X₀ : CaseAStart G Ω α v P := H.lineStart H.i₀

@[expose] noncomputable def vk (k : H.A₁.D.ι) : Equiv.Perm (H.A₁.D.Ψc k) :=
  H.A₁.D.ρ k ⟨_, H.X₀.A.D.socPre_le_jHull (H.X₀.vDelta_mem_socPre hS hP)⟩

omit [FaithfulSMul G Ω] in
theorem coord_v {δ δ' : holtDelta G Ω α H.β₁} (h : (δ' : Ω) = v • (δ : Ω)) (k : H.A₁.D.ι) :
    H.A₁.D.coord δ' k = H.vk k (H.A₁.D.coord δ k) := by
  have := (H.X₀.coord_v hS hP).1 δ k
  rw [show δ' = ⟨v • (δ : Ω), H.X₀.smul_mem_holtDelta (H.X₀.v_mem_pair hP) δ.2⟩ from
    Subtype.ext h]
  exact this

omit [FaithfulSMul G Ω] in
theorem vk_fix {k : H.A₁.D.ι} {c : H.A₁.D.Ψc k} (hc : H.vk k c = c) :
    c = H.A₁.D.coord H.γ₁Δ k :=
  (H.X₀.coord_v hS hP).2 k c hc

omit [FaithfulSMul G Ω] in
theorem vk_vk (k : H.A₁.D.ι) (c : H.A₁.D.Ψc k) : H.vk k (H.vk k c) = c := by
  obtain ⟨δ, rfl⟩ := H.A₁.D.exists_coord_apply_eq k c
  have hv2 : v * v = 1 := by rw [← sq, ← hP.typeL.orderOf_eq_two, pow_orderOf_eq_one]
  have hm : ∀ ε : holtDelta G Ω α H.β₁, v • (ε : Ω) ∈ holtDelta G Ω α H.β₁ := fun ε =>
    H.X₀.smul_mem_holtDelta (H.X₀.v_mem_pair hP) ε.2
  set δ₁ : holtDelta G Ω α H.β₁ := ⟨v • (δ : Ω), hm δ⟩
  set δ₂ : holtDelta G Ω α H.β₁ := ⟨v • (δ₁ : Ω), hm δ₁⟩
  have h2 : δ₂ = δ := Subtype.ext (by
    show v • v • (δ : Ω) = δ
    rw [smul_smul, hv2, one_smul])
  rw [← H.coord_v (δ := δ) (δ' := δ₁) rfl, ← H.coord_v (δ := δ₁) (δ' := δ₂) rfl, h2]

@[expose] noncomputable def eS (S : Finset H.A₁.D.ι) : Equiv.Perm (holtDelta G Ω α H.β₁) :=
  coordPerm H.A₁ fun k => if k ∈ S then H.vk k else 1

omit [FaithfulSMul G Ω] in
theorem coord_eS (S : Finset H.A₁.D.ι) (δ : holtDelta G Ω α H.β₁) (k : H.A₁.D.ι) :
    H.A₁.D.coord (H.eS S δ) k =
      if k ∈ S then H.vk k (H.A₁.D.coord δ k) else H.A₁.D.coord δ k := by
  rw [eS, coord_coordPerm]
  split_ifs <;> rfl

omit [FaithfulSMul G Ω] in
theorem eS_mul (S S' : Finset H.A₁.D.ι) : H.eS S * H.eS S' = H.eS (symmDiff S S') := by
  classical
  refine Equiv.ext fun δ => CaseAData.coord_injective H.A₁ (funext fun k => ?_)
  rw [Equiv.Perm.mul_apply, coord_eS, coord_eS, coord_eS]
  by_cases h : k ∈ S <;> by_cases h' : k ∈ S' <;>
    simp only [h, h', Finset.mem_symmDiff, ite_true, ite_false, not_true, not_false_eq_true,
      and_true, and_false, or_false, false_or, vk_vk]

omit [FaithfulSMul G Ω] in
theorem eS_empty : H.eS ∅ = 1 := by
  rw [eS]
  simp only [Finset.notMem_empty, ite_false]
  exact coordPerm_one H.A₁

omit [FaithfulSMul G Ω] in
theorem eS_mul_self (S : Finset H.A₁.D.ι) : H.eS S * H.eS S = 1 := by
  rw [eS_mul, symmDiff_self, Finset.bot_eq_empty, eS_empty]

omit [FaithfulSMul G Ω] in
theorem eS_map_mul {g : G} (hg : g ∈ H.V) {σ : H.A₁.D.ι ≃ H.A₁.D.ι}
    (hσ : ∀ j, MapsDir H.A₁ g j (σ j)) (S : Finset H.A₁.D.ι) :
    H.eS (S.map σ.toEmbedding) *
        ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
          Equiv.Perm (holtDelta G Ω α H.β₁)) =
      ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
          Equiv.Perm (holtDelta G Ω α H.β₁)) * H.eS S := by
  classical
  have hgv : Commute g v :=
    (Subgroup.mem_centralizer_iff.mp (H.sylow.1 hg).1.1 v (Subgroup.mem_zpowers v)).symm
  have hm : ∀ ε : holtDelta G Ω α H.β₁, v • (ε : Ω) ∈ holtDelta G Ω α H.β₁ := fun ε =>
    H.X₀.smul_mem_holtDelta (H.X₀.v_mem_pair hP) ε.2
  refine Equiv.ext fun δ => CaseAData.coord_injective H.A₁ (funext fun m => ?_)
  obtain ⟨m', rfl⟩ := σ.surjective m
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, coord_eS]
  by_cases hm' : m' ∈ S
  · have hmem : σ m' ∈ S.map σ.toEmbedding := Finset.mem_map_of_mem _ hm'
    rw [ite_eq_left hmem]
    set vδ : holtDelta G Ω α H.β₁ := ⟨v • (δ : Ω), hm δ⟩
    have h1 := (hσ m' (H.eS S δ) vδ (twoPointElt (H.V_le_pair hg) • H.eS S δ)
      (twoPointElt (H.V_le_pair hg) • vδ) rfl rfl).mpr
      (by rw [coord_eS, ite_eq_left hm', H.coord_v (δ := δ) (δ' := vδ) rfl])
    change _ = H.A₁.D.coord (twoPointElt (H.V_le_pair hg) • H.eS S δ) (σ m')
    rw [h1]
    refine (H.coord_v (δ := twoPointElt (H.V_le_pair hg) • δ) ?_ (σ m')).symm
    show g • v • (δ : Ω) = v • g • (δ : Ω)
    rw [smul_smul, smul_smul, hgv.eq]
  · have hmem : σ m' ∉ S.map σ.toEmbedding := fun h => by
      obtain ⟨x, hx, hxe⟩ := Finset.mem_map.mp h
      exact hm' (σ.injective hxe ▸ hx)
    rw [ite_eq_right hmem]
    exact ((hσ m' (H.eS S δ) δ _ _ rfl rfl).mpr (by rw [coord_eS, ite_eq_right hm'])).symm

theorem eq_empty_of_eS {g : G} (hg : g ∈ H.V) {U : Finset H.A₁.D.ι}
    (hU : ∀ k ∈ U, 4 ≤ (proj H.A₁ H.V k).ncard)
    (hgU : ((twoPointElt (H.V_le_pair hg) : twoPointSection G Ω α H.β₁) :
      Equiv.Perm (holtDelta G Ω α H.β₁)) = H.eS U) : U = ∅ := by
  classical
  by_contra hne
  obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hgk : MapsDir H.A₁ g k k := by
    intro δ₁ δ₂ δ₁' δ₂' e₁ e₂
    have h1 : δ₁' = H.eS U δ₁ := by rw [← hgU]; exact Subtype.ext e₁
    have h2 : δ₂' = H.eS U δ₂ := by rw [← hgU]; exact Subtype.ext e₂
    rw [h1, h2, coord_eS, coord_eS, ite_eq_left hk, ite_eq_left hk]
    exact (H.vk k).injective.eq_iff
  obtain ⟨δ, hδk, -⟩ := exists_pair_update H.A₁ H.γ₁Δ k
  have h1 := H.coord_smul_eq (hU k hk) hg hgk δ (H.eS U δ) (by
    rw [← hgU]; rfl)
  rw [coord_eS, ite_eq_left hk] at h1
  exact hδk (H.vk_fix h1)

@[expose] noncomputable def RT (T : Finset H.A₁.D.ι) :
    Subgroup (Equiv.Perm (holtDelta G Ω α H.β₁)) where
  carrier := {π | ∃ S ⊆ T, π = H.eS S}
  mul_mem' := by
    classical
    rintro _ _ ⟨S, hS, rfl⟩ ⟨S', hS', rfl⟩
    exact ⟨symmDiff S S', fun x hx => by
      rcases Finset.mem_symmDiff.mp hx with ⟨h, -⟩ | ⟨h, -⟩
      exacts [hS h, hS' h], H.eS_mul S S'⟩
  one_mem' := ⟨∅, Finset.empty_subset _, H.eS_empty.symm⟩
  inv_mem' := by
    rintro _ ⟨S, hS, rfl⟩
    exact ⟨S, hS, inv_eq_of_mul_eq_one_right (H.eS_mul_self S)⟩

omit [FaithfulSMul G Ω] in
theorem isPGroup_RT (T : Finset H.A₁.D.ι) : IsPGroup 2 (H.RT T) :=
  isPGroup_of_mul_self fun q hq => by
    obtain ⟨S, -, rfl⟩ := hq
    exact H.eS_mul_self S

@[expose] noncomputable def Tbig : Finset H.A₁.D.ι :=
  (Finset.univ.filter fun k => 4 ≤ (proj H.A₁ H.V k).ncard).erase H.i₀

omit [Finite G] [FaithfulSMul G Ω] in
theorem Vdir_le_stab (j : H.A₁.D.ι) : H.Vdir j ≤ stabilizer G (holtDelta G Ω α H.β₁) :=
  fun _ hg => stabilizer_pair_le α H.β₁ (H.V_le_pair (Subgroup.mem_inf.mp hg).1)

omit [FaithfulSMul G Ω] in
theorem Vdir_le_normalizer_RT :
    inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁) (H.Vdir_le_stab H.i₀) ≤
      Subgroup.normalizer (H.RT H.Tbig : Set (Equiv.Perm (holtDelta G Ω α H.β₁))) := by
  classical
  have key : ∀ π ∈ inducedPerm (H.Vdir H.i₀) (holtDelta G Ω α H.β₁) (H.Vdir_le_stab H.i₀),
      ∀ x ∈ H.RT H.Tbig, π * x * π⁻¹ ∈ H.RT H.Tbig := by
    intro π hπ x hx
    obtain ⟨S, hS, rfl⟩ := hx
    obtain ⟨g, hg, hgπ⟩ := mem_inducedPerm.mp hπ
    obtain ⟨hgV, hgN⟩ := Subgroup.mem_inf.mp hg
    have hπg : π = ((twoPointElt (H.V_le_pair hgV) : twoPointSection G Ω α H.β₁) :
        Equiv.Perm (holtDelta G Ω α H.β₁)) := Equiv.ext fun δ => Subtype.ext (hgπ δ)
    obtain ⟨σ, hσ⟩ := exists_mapsDir H.A₁ (H.V_le_pair hgV)
    have hσi₀ : σ H.i₀ = H.i₀ := MapsDir.eq H.A₁ (H.V_le_pair hgV) H.γ₁Δ (hσ H.i₀)
      (mapsDir_of_mem_twoPointNormalizer H.A₁ hgN)
    refine ⟨S.map σ.toEmbedding, fun x hx => ?_, ?_⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      have hyT := hS hy
      simp only [Tbig, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and] at hyT ⊢
      refine ⟨fun h => hyT.1 (σ.injective (h.trans hσi₀.symm)), ?_⟩
      show 4 ≤ (proj H.A₁ H.V (σ y)).ncard
      rw [ncard_proj_eq_of_mapsDir H.A₁ (H.V_le_pair hgV) (Subgroup.le_normalizer hgV) (hσ y)]
      exact hyT.2
    · rw [hπg, ← H.eS_map_mul hgV hσ S, mul_inv_cancel_right]
  intro π hπ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key π hπ x, fun h => ?_⟩
  have := key π⁻¹ (inv_mem hπ) _ h
  rwa [inv_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
    mul_one] at this

end DCase

end CaseAD

end CFSG.Holt.H78
