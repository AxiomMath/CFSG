module

public import CFSG.Holt.H78.Sec4Prop49S5d
import CFSG.Holt.H78.Sec4KnownKV

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open scoped Pointwise

namespace P49Config

section Gen

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

namespace P95Data

variable (P : C.P95Data)

theorem exists_mem_J0_eqOn (h : C.P95) {s : G} (hs : s ∈ longInvAt G Ω α) :
    ∃ s' ∈ P.E, s' ∈ longInvAt G Ω α ∧ ∀ γ ∈ C.Γ, s' • γ = s • γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsK : s ∈ C.K := Subgroup.subset_closure hs
  obtain ⟨S', hsS', hS'⟩ := exists_fusionIsSylowIn_ge (isPGroup_zpowers_of_orderOf_eq_two hs.1.1)
    (Subgroup.zpowers_le.mpr hsK)
  obtain ⟨c, hc, hcS⟩ := exists_mem_conj_of_fusionIsSylowIn P.sylow hS'
  have hcα := K_le_stabilizer C hc
  refine ⟨c⁻¹ * s * c, (hcS s).mp (hsS' (Subgroup.mem_zpowers s)), ?_, fun γ hγ => ?_⟩
  · have := conj_mem_longInvAt hs c⁻¹
    rwa [inv_inv, inv_smul_eq_iff.mpr (mem_stabilizer_iff.mp hcα).symm] at this
  · have hcγ : c • γ ∈ C.Γ := by
      rw [← mem_stabilizer_iff.mp (K_le_stabilizer_Γ hc)]
      exact Set.smul_mem_smul_set hγ
    have e := (h.smul_mul_comm hsK hc hγ).1
    rw [mul_smul, mul_smul] at e
    rw [mul_smul, mul_smul, inv_smul_eq_iff]
    exact e

theorem mem_closure_J0 (h : C.P95) {e : G} (he : e ∈ P.E) :
    e ∈ Subgroup.closure {s | s ∈ P.E ∧ s ∈ longInvAt G Ω α} := by
  set J0 := Subgroup.closure {s | s ∈ P.E ∧ s ∈ longInvAt G Ω α}
  have hJ0E : J0 ≤ P.E := (Subgroup.closure_le _).mpr fun s hs => hs.1
  have key : ∀ k ∈ C.K, ∃ e' ∈ J0, ∀ γ ∈ C.Γ, e' • γ = k • γ := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨s', hs'E, hs'J, hs'γ⟩ := P.exists_mem_J0_eqOn h hs
      exact ⟨s', Subgroup.subset_closure ⟨hs'E, hs'J⟩, hs'γ⟩
    | one => exact ⟨1, one_mem _, fun γ _ => rfl⟩
    | mul k k' hk hk' ih ih' =>
      obtain ⟨e₁, he₁, h₁⟩ := ih
      obtain ⟨e₂, he₂, h₂⟩ := ih'
      refine ⟨e₁ * e₂, mul_mem he₁ he₂, fun γ hγ => ?_⟩
      have hγ' : k' • γ ∈ C.Γ := by
        rw [← mem_stabilizer_iff.mp (K_le_stabilizer_Γ hk')]
        exact Set.smul_mem_smul_set hγ
      rw [mul_smul, mul_smul, h₂ γ hγ, h₁ _ hγ']
    | inv k hk ih =>
      obtain ⟨e₁, he₁, h₁⟩ := ih
      refine ⟨e₁⁻¹, inv_mem he₁, fun γ hγ => ?_⟩
      have hγ' : k⁻¹ • γ ∈ C.Γ := by
        rw [← mem_stabilizer_iff.mp (K_le_stabilizer_Γ (inv_mem hk))]
        exact Set.smul_mem_smul_set hγ
      rw [inv_smul_eq_iff, h₁ _ hγ', smul_inv_smul]
  obtain ⟨e', he', heγ⟩ := key e (P.E_le_K he)
  have h1 := P.eq_one_of_forall_smul_Γ h (mul_mem (inv_mem (hJ0E he')) he) fun γ hγ => by
    rw [mul_smul, inv_smul_eq_iff, heγ γ hγ]
  rwa [inv_mul_eq_one.mp h1] at he'

end P95Data

end Gen

section OddCore

theorem _root_.CFSG.Holt.H78.HoltData.mul_mem_socPre_of_notMem {K X : Type*} [Group K]
    [MulAction K X]
    (D : HoltData K X) {h₁ h₂ : K} (h₁H : h₁ ∈ jHull K X) (h₂H : h₂ ∈ jHull K X)
    (h₁S : h₁ ∉ D.socPre) (h₂S : h₂ ∉ D.socPre) : h₁ * h₂ ∈ D.socPre := by
  have hdvd := D.relIndex_socPre_jHull_dvd_two
  rw [Subgroup.relIndex] at hdvd
  have hidx : (D.socPre.subgroupOf (jHull K X)).index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exfalso
      rw [Subgroup.index_eq_one] at h1
      have : (⟨h₁, h₁H⟩ : jHull K X) ∈ D.socPre.subgroupOf (jHull K X) := h1 ▸ Subgroup.mem_top _
      exact h₁S this
    · exact h1
  have := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨h₁, h₁H⟩) (b := ⟨h₂, h₂H⟩)).mpr
    (iff_of_false h₁S h₂S)
  exact this

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

namespace P95Data

variable (P : C.P95Data) {X : Subgroup G}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem isPGroup_of_le_W (hXW : X ≤ P.W) : IsPGroup 2 X :=
  P.isPGroup_E.to_le (hXW.trans inf_le_left)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem line_subset_fixSet_of_le_W (hXW : X ≤ P.W) : C.line ⊆ fixSet Ω X :=
  fun _ hy _ hx => (P.mem_W.mp (hXW hx)).2 _ hy

omit [Finite G] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem three_le_card_fixSet_of_le_W (hXW : X ≤ P.W) : 3 ≤ Nat.card (fixSet Ω X) := by
  have h3 := C.three_le_card_line
  have := Nat.card_mono (Set.toFinite _) (P.line_subset_fixSet_of_le_W hXW)
  omega

theorem E_le_centralizer_of_le_W (h : C.P95) (hXW : X ≤ P.W) :
    P.E ≤ Subgroup.centralizer (X : Set G) := fun _ he =>
  Subgroup.mem_centralizer_iff.mpr fun _ hx => P.commute_E h ((hXW hx).1) he

theorem centralizerImageElt_mem_jHull (h : C.P95) (hXW : X ≤ P.W) {e : G} (he : e ∈ P.E) :
    centralizerImageElt (Ω := Ω) (P.E_le_centralizer_of_le_W h hXW he) ∈
      jHull (centralizerImage Ω X) (fixSet Ω X) := by
  have hS := h.setting
  have key : ∀ e ∈ Subgroup.closure {s | s ∈ P.E ∧ s ∈ longInvAt G Ω α},
      ∀ hc : e ∈ Subgroup.centralizer (X : Set G),
        centralizerImageElt (Ω := Ω) hc ∈ jHull (centralizerImage Ω X) (fixSet Ω X) := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem s hs =>
      intro hc
      exact mem_jHull_of_mem_longInv ((hS.mem_longInv_centralizerImage_iff
        (P.isPGroup_of_le_W hXW) (P.three_le_card_fixSet_of_le_W hXW) _).mpr
          ⟨s, hs.2.1, hc, fun _ => rfl⟩)
    | one =>
      intro hc
      have : centralizerImageElt (Ω := Ω) hc = 1 := Subtype.ext (map_one _)
      rw [this]
      exact one_mem _
    | mul x y hx hy ihx ihy =>
      intro hc
      have hxC := (P.E_le_centralizer_of_le_W h hXW
        ((Subgroup.closure_le _).mpr (fun s hs => hs.1) hx))
      have hyC := (P.E_le_centralizer_of_le_W h hXW
        ((Subgroup.closure_le _).mpr (fun s hs => hs.1) hy))
      have : centralizerImageElt (Ω := Ω) hc =
          centralizerImageElt (Ω := Ω) hxC * centralizerImageElt (Ω := Ω) hyC :=
        Subtype.ext (map_mul (MulAction.toPermHom (Subgroup.centralizer (X : Set G))
          (fixSet Ω X)) ⟨x, hxC⟩ ⟨y, hyC⟩)
      rw [this]
      exact mul_mem (ihx hxC) (ihy hyC)
    | inv x hx ihx =>
      intro hc
      have hxC := (P.E_le_centralizer_of_le_W h hXW
        ((Subgroup.closure_le _).mpr (fun s hs => hs.1) hx))
      have : centralizerImageElt (Ω := Ω) hc = (centralizerImageElt (Ω := Ω) hxC)⁻¹ :=
        Subtype.ext (map_inv (MulAction.toPermHom (Subgroup.centralizer (X : Set G))
          (fixSet Ω X)) ⟨x, hxC⟩)
      rw [this]
      exact inv_mem (ihx hxC)
  exact key e (P.mem_closure_J0 h he) _

theorem jOddCore_eq_bot (h : C.P95) (hXW : X ≤ P.W) (hX1 : X ≠ ⊥) :
    jOddCore (centralizerImage Ω X) (fixSet Ω X) = ⊥ := by
  have hS := h.setting
  have hXp := P.isPGroup_of_le_W hXW
  have h3 := P.three_le_card_fixSet_of_le_W hXW
  obtain ⟨D⟩ := hS.holtData_centralizerImage hXp hX1 h3
  have hEC := P.E_le_centralizer_of_le_W h hXW
  set αX : fixSet Ω X := ⟨α, P.line_subset_fixSet_of_le_W hXW C.α_mem_line⟩
  have hfix : ∀ {e} (he : e ∈ P.E), centralizerImageElt (Ω := Ω) (hEC he) ∈ D.socPre →
      ∀ x ∈ orbit (jOddCore (centralizerImage Ω X) (fixSet Ω X)) αX, e • (x : Ω) = x := by
    intro e he hsoc x hx
    set π := centralizerImageElt (Ω := Ω) (hEC he)
    by_cases hπ1 : π = 1
    · have := congrArg (fun σ : centralizerImage Ω X => ((σ : Equiv.Perm (fixSet Ω X)) x : Ω)) hπ1
      simpa [π] using this
    have hπ2 : orderOf π = 2 := by
      refine orderOf_eq_prime ?_ hπ1
      have h1 : centralizerImageElt (Ω := Ω) (hEC (mul_mem he he)) = 1 := by
        refine Subtype.ext (Equiv.ext fun y => Subtype.ext ?_)
        show (e * e) • (y : Ω) = y
        rw [P.mul_self_E h he, one_smul]
      rw [sq, ← h1]
      exact Subtype.ext (map_mul (MulAction.toPermHom (Subgroup.centralizer (X : Set G))
        (fixSet Ω X)) ⟨e, hEC he⟩ ⟨e, hEC he⟩).symm
    have hπα : π • αX ∈ orbit (jOddCore (centralizerImage Ω X) (fixSet Ω X)) αX := by
      have : π • αX = αX := Subtype.ext (mem_stabilizer_iff.mp (P.E_le_stabilizer he))
      rw [this]
      exact mem_orbit_self _
    exact congrArg Subtype.val ((hS.lemma_2_4_iv_centralizerImage hXp hX1 h3 D
      (P.centralizerImageElt_mem_jHull h hXW he) hπ2 hπα).1 hsoc x hx)
  have hJX : ∀ {s} (hs : s ∈ P.E), s ∈ longInvAt G Ω α →
      centralizerImageElt (Ω := Ω) (hEC hs) ∈
        longInv (centralizerImage Ω X) (fixSet Ω X) := fun {s} hs hsJ =>
    (hS.mem_longInv_centralizerImage_iff hXp h3 _).mpr ⟨s, hsJ.1, hEC hs, fun _ => rfl⟩
  have hmulπ : ∀ {e e'} (he : e ∈ P.E) (he' : e' ∈ P.E),
      centralizerImageElt (Ω := Ω) (hEC (mul_mem he he')) =
        centralizerImageElt (Ω := Ω) (hEC he) * centralizerImageElt (Ω := Ω) (hEC he') :=
    fun {e e'} he he' => Subtype.ext (map_mul (MulAction.toPermHom
      (Subgroup.centralizer (X : Set G)) (fixSet Ω X)) ⟨e, hEC he⟩ ⟨e', hEC he'⟩)
  have key : ∀ x ∈ orbit (jOddCore (centralizerImage Ω X) (fixSet Ω X)) αX, x = αX := by
    intro x hx
    by_contra hxα
    have htu := mul_mem P.t_mem_E P.u_mem_E
    have hvsoc : centralizerImageElt (Ω := Ω) (hEC htu) ∈ D.socPre := by
      rw [hmulπ P.t_mem_E P.u_mem_E]
      exact hS.mul_mem_socPre_centralizerImage hXp h3 D (hJX P.t_mem_E P.t_mem)
        (hJX P.u_mem_E P.u_mem)
    have hxv := hfix htu hvsoc x hx
    rw [P.mul_eq] at hxv
    set xΦ : fixSet Ω (Subgroup.zpowers v) := ⟨x, mem_fixSet_zpowers_iff.mpr hxv⟩
    have hxa : xΦ ≠ C.a := fun h1 => hxα (Subtype.ext (by
      have := congrArg Subtype.val h1
      simp only [xΦ] at this
      rw [this, C.coe_a]))
    obtain ⟨k, hk⟩ : ∃ k, C.D.coord xΦ k ≠ C.D.coord C.a k := by
      by_contra hne
      exact hxa (C.coord_injective (funext fun k => by_contra fun h1 => hne ⟨k, h1⟩))
    obtain ⟨nk, ik, ek, hA⟩ := (C.isNaturalSE k).exists_isBenderAction
    have hcard := hA.card_rootCenter_seRadical (C.D.coord C.a k)
    have hq := hA.four_le_q
    set R := CFSG.GH74.Uniqueness.Bender.rootCenter (seRadical (C.D.M k) (C.D.coord C.a k))
    obtain ⟨z₁, hz₁, hz₁1⟩ : ∃ z ∈ R, z ≠ 1 := by
      obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
        ((Subgroup.one_lt_card_iff_ne_bot R).mp (by rw [hcard]; omega))
      exact ⟨z, z.2, fun h1 => hz (Subtype.ext h1)⟩
    obtain ⟨z₂, hz₂, hz₂1, hz₁₂⟩ : ∃ z ∈ R, z ≠ 1 ∧ z ≠ z₁ := by
      by_contra hne
      have hsub : (R : Set (Equiv.Perm (C.D.Ψc k))) ⊆ {1, z₁} := fun z hz => by
        by_cases h1 : z = 1
        · exact Or.inl h1
        · exact Or.inr (by_contra fun h2 => hne ⟨z, hz, h1, h2⟩)
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      have h2 := Set.ncard_insert_le (1 : Equiv.Perm (C.D.Ψc k)) {z₁}
      rw [Set.ncard_singleton] at h2
      rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hcard] at h1
      omega
    have hmoves : ∀ z ∈ R, z ≠ 1 → ∀ e : G, (∀ y y' : fixSet Ω (Subgroup.zpowers v),
        C.D.coord y' = Function.update (C.D.coord y) k (z (C.D.coord y k)) → e • (y : Ω) = y') →
        e • (x : Ω) ≠ x := by
      intro z hz hz1 e he hex
      obtain ⟨x', hx'⟩ := C.D.coord_surjective
        (Function.update (C.D.coord xΦ) k (z (C.D.coord xΦ k)))
      have h1 := he xΦ x' hx'
      rw [hex] at h1
      have h2 : C.D.coord xΦ k = z (C.D.coord xΦ k) := by
        have := congrFun hx' k
        rwa [Function.update_self, ← show xΦ = x' from Subtype.ext h1] at this
      exact hz1 ((C.isNaturalSE k).eq_one_of_mem_seRadical
        (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ hz) hk h2.symm)
    obtain ⟨e₁, he₁, h₁⟩ := P.exists_mem_E_coord h k hz₁
    obtain ⟨e₂, he₂, h₂⟩ := P.exists_mem_E_coord h k hz₂
    have h₁₂ : ∀ y y' : fixSet Ω (Subgroup.zpowers v), C.D.coord y' =
        Function.update (C.D.coord y) k ((z₁ * z₂) (C.D.coord y k)) →
          (e₁ * e₂) • (y : Ω) = y' := by
      intro y y' hy'
      obtain ⟨y₂, hy₂⟩ := C.D.coord_surjective
        (Function.update (C.D.coord y) k (z₂ (C.D.coord y k)))
      rw [mul_smul, h₂ y y₂ hy₂]
      refine h₁ y₂ y' ?_
      rw [hy', hy₂, Function.update_idem, Function.update_self, Equiv.Perm.mul_apply]
    have hz12 : z₁ * z₂ ≠ 1 := fun h1 => hz₁₂ (by
      have := eq_inv_of_mul_eq_one_right h1
      rwa [inv_eq_of_mul_eq_one_right ((C.isNaturalSE k).mul_self_eq_one_of_mem_rootCenter
        hz₁)] at this)
    by_cases hs₁ : centralizerImageElt (Ω := Ω) (hEC he₁) ∈ D.socPre
    · exact hmoves z₁ hz₁ hz₁1 e₁ h₁ (hfix he₁ hs₁ x hx)
    by_cases hs₂ : centralizerImageElt (Ω := Ω) (hEC he₂) ∈ D.socPre
    · exact hmoves z₂ hz₂ hz₂1 e₂ h₂ (hfix he₂ hs₂ x hx)
    have hs₁₂ := D.mul_mem_socPre_of_notMem (P.centralizerImageElt_mem_jHull h hXW he₁)
      (P.centralizerImageElt_mem_jHull h hXW he₂) hs₁ hs₂
    rw [← hmulπ he₁ he₂] at hs₁₂
    exact hmoves _ (mul_mem hz₁ hz₂) hz12 _ h₁₂ (hfix (mul_mem he₁ he₂) hs₁₂ x hx)
  have hle : jOddCore (centralizerImage Ω X) (fixSet Ω X) ≤
      stabilizer (centralizerImage Ω X) αX := fun o ho =>
    mem_stabilizer_iff.mpr (key _ ⟨⟨o, ho⟩, rfl⟩)
  have := (hS.star_centralizerImage hXp h3).isPretransitive
  exact eq_bot_of_normal_of_le_stabilizer jOddCore_normal hle

end P95Data

end OddCore

section Pattern


theorem _root_.CFSG.Holt.H78.HoltData.exists_longInvAt_apply_ne {K Y : Type*} [Group K]
    [Finite K] [MulAction K Y] (D : HoltData K Y) (c : D.ι) {a b : D.Ψc c} (hab : a ≠ b) :
    ∃ y₁ ∈ (D.ρ c).range, ∃ y₂ ∈ (D.ρ c).range,
      y₁ ∈ longInvAt (Equiv.Perm (D.Ψc c)) (D.Ψc c) a ∧
        y₂ ∈ longInvAt (Equiv.Perm (D.Ψc c)) (D.Ψc c) a ∧ y₁ b ≠ y₂ b := by
  suffices h1 : 1 < (holtDelta' (D.ρ c).range (D.Ψc c) a b).ncard by
    obtain ⟨γ₁, γ₂, ⟨s₁, hs₁, rfl⟩, ⟨s₂, hs₂, rfl⟩, hne⟩ :=
      (Set.one_lt_ncard_iff (Set.toFinite _)).mp h1
    exact ⟨s₁, s₁.2, s₂, s₂.2, mem_longInvAt_subgroup_iff.mp hs₁,
      mem_longInvAt_subgroup_iff.mp hs₂, hne⟩
  rcases D.factor c with ⟨hAlt, h7⟩ | hSE
  · have hM : alternatingGroup (D.Ψc c) ≤ (D.ρ c).range := by
      rw [D.range_rho, ← hAlt]
      exact le_sup_left
    have hρt := D.rho_mem_longInv D.t_mem c
    rw [holtDelta'_eq_compl_of_alternatingGroup_le hM ⟨D.tHull, rfl⟩ hρt hab,
      Set.ncard_compl, Set.ncard_pair hab, Nat.card_eq_fintype_card]
    omega
  · rw [D.range_rho_of_not_isOuterFactor hSE.not_isOuterFactor]
    obtain ⟨n, k, e, hA⟩ := hSE.exists_isBenderAction
    rw [hA.ncard_holtDelta' hab]
    have := hA.four_le_q
    omega

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

theorem _root_.CFSG.Holt.H78.Sec4Setting.centralizerImageElt_mem_jHull_of_mem_closure
    (hS : Sec4Setting G Ω) {X : Subgroup G} (hXp : IsPGroup 2 X)
    (h3 : 3 ≤ Nat.card (fixSet Ω X)) {g : G}
    (hg : g ∈ Subgroup.closure {c | c ∈ longInv G Ω ∧ c ∈ Subgroup.centralizer (X : Set G)}) :
    ∃ hgC : g ∈ Subgroup.centralizer (X : Set G),
      centralizerImageElt (Ω := Ω) hgC ∈ jHull (centralizerImage Ω X) (fixSet Ω X) := by
  induction hg using Subgroup.closure_induction with
  | mem c hc =>
    exact ⟨hc.2, mem_jHull_of_mem_longInv ((hS.mem_longInv_centralizerImage_iff hXp h3 _).mpr
      ⟨c, hc.1, hc.2, fun _ => rfl⟩)⟩
  | one =>
    refine ⟨one_mem _, ?_⟩
    have : centralizerImageElt (Ω := Ω) (one_mem (Subgroup.centralizer (X : Set G))) = 1 :=
      Subtype.ext (map_one _)
    rw [this]
    exact one_mem _
  | mul x y _ _ ihx ihy =>
    obtain ⟨hxC, hx⟩ := ihx
    obtain ⟨hyC, hy⟩ := ihy
    refine ⟨mul_mem hxC hyC, ?_⟩
    have : centralizerImageElt (Ω := Ω) (mul_mem hxC hyC) =
        centralizerImageElt (Ω := Ω) hxC * centralizerImageElt (Ω := Ω) hyC :=
      Subtype.ext (map_mul (MulAction.toPermHom (Subgroup.centralizer (X : Set G))
        (fixSet Ω X)) ⟨x, hxC⟩ ⟨y, hyC⟩)
    rw [this]
    exact mul_mem hx hy
  | inv x _ ihx =>
    obtain ⟨hxC, hx⟩ := ihx
    refine ⟨inv_mem hxC, ?_⟩
    have : centralizerImageElt (Ω := Ω) (inv_mem hxC) = (centralizerImageElt (Ω := Ω) hxC)⁻¹ :=
      Subtype.ext (map_inv (MulAction.toPermHom (Subgroup.centralizer (X : Set G))
        (fixSet Ω X)) ⟨x, hxC⟩)
    rw [this]
    exact inv_mem hx

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem exists_mem_M_apply_eq₂ (C : P49Config G Ω α v) {ψ₁ ψ₂ ψ₃ ψ₄ : C.D.Ψc C.i}
    (h₁₂ : ψ₁ ≠ ψ₂) (h₃₄ : ψ₃ ≠ ψ₄) :
    ∃ m ∈ C.D.M C.i, m ψ₁ = ψ₃ ∧ m ψ₂ = ψ₄ := by
  obtain ⟨m₁, hm₁, hm₁ψ⟩ := C.exists_mem_M_apply_eq' ψ₁ ψ₃
  have hne : m₁ ψ₂ ≠ ψ₃ := fun h1 => h₁₂ (m₁.injective (h1.trans hm₁ψ.symm)).symm
  obtain ⟨m₂, hm₂, hm₂ψ, hm₂fix⟩ := C.exists_mem_M_fix_apply_eq hne (Ne.symm h₃₄)
  exact ⟨m₂ * m₁, mul_mem hm₂ hm₁, by rw [Equiv.Perm.mul_apply, hm₁ψ, hm₂fix],
    by rw [Equiv.Perm.mul_apply, hm₂ψ]⟩

namespace P95Data

variable (P : C.P95Data) {X : Subgroup G}

theorem exists_closure_smul_eq (h : C.P95) (hXW : X ≤ P.W) {ℓ : Set Ω}
    (hℓ : ℓ ∈ linesThrough G C.line α) (hXℓ : X ≤ P.Wl ℓ) {y₁ y₂ y₃ y₄ : Ω} (h₁ : y₁ ∈ ℓ)
    (h₂ : y₂ ∈ ℓ) (h₃ : y₃ ∈ ℓ) (h₄ : y₄ ∈ ℓ) (h₁₂ : y₁ ≠ y₂) (h₃₄ : y₃ ≠ y₄) :
    ∃ g ∈ Subgroup.closure {c | c ∈ longInv G Ω ∧ c ∈ Subgroup.centralizer (X : Set G)},
      g • y₁ = y₃ ∧ g • y₂ = y₄ := by
  obtain ⟨n, -, -, rfl⟩ := P.exists_mem_normalizer_smul_line h hℓ
  obtain ⟨_, ⟨ψ₁, rfl⟩, rfl⟩ := h₁
  obtain ⟨_, ⟨ψ₂, rfl⟩, rfl⟩ := h₂
  obtain ⟨_, ⟨ψ₃, rfl⟩, rfl⟩ := h₃
  obtain ⟨_, ⟨ψ₄, rfl⟩, rfl⟩ := h₄
  have hψ₁₂ : ψ₁ ≠ ψ₂ := fun h1 => h₁₂ (by rw [h1])
  have hψ₃₄ : ψ₃ ≠ ψ₄ := fun h1 => h₃₄ (by rw [h1])
  obtain ⟨m, hm, hm₁, hm₂⟩ := exists_mem_M_apply_eq₂ C hψ₁₂ hψ₃₄
  set V := X.map (MulAut.conj n⁻¹).toMonoidHom
  have hVp : IsPGroup 2 V := (P.isPGroup_of_le_W hXW).map _
  have hVL : V ≤ fixingSubgroup G C.line := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_fixingSubgroup_iff]
    rintro _ ⟨ψ, rfl⟩
    have h1 := (P.mem_Wl.mp (hXℓ hx)).2 _ (Set.smul_mem_smul_set (a := n) (C.lpt_mem_line ψ))
    show (n⁻¹ * x * n⁻¹⁻¹) • (C.lpt ψ : Ω) = C.lpt ψ
    rw [inv_inv, mul_smul, mul_smul, h1, inv_smul_smul]
  obtain ⟨g, hg, hgm⟩ := C.exists_lineActs_closure h.setting h.transitive hVp hVL hm
  refine ⟨n * g * n⁻¹, ?_, ?_, ?_⟩
  · have hle : (Subgroup.closure {c | c ∈ longInv G Ω ∧ c ∈ Subgroup.centralizer (V : Set G) ∧
        c • C.line = C.line}).map (MulAut.conj n).toMonoidHom ≤
          Subgroup.closure {c | c ∈ longInv G Ω ∧ c ∈ Subgroup.centralizer (X : Set G)} := by
      rw [MonoidHom.map_closure]
      refine Subgroup.closure_mono ?_
      rintro _ ⟨c, ⟨hcJ, hcV, -⟩, rfl⟩
      refine ⟨conj_mem_longInv hcJ n, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hcV (n⁻¹ * x * n⁻¹⁻¹) ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc x * (n * c * n⁻¹) = n * ((n⁻¹ * x * n⁻¹⁻¹) * c) * n⁻¹ := by group
        _ = n * (c * (n⁻¹ * x * n⁻¹⁻¹)) * n⁻¹ := by rw [h1]
        _ = n * c * n⁻¹ * x := by group
    exact hle ⟨g, hg, rfl⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, hgm, hm₁]
  · rw [mul_smul, mul_smul, inv_smul_smul, hgm, hm₂]

theorem exists_coord_of_le_Wl (h : C.P95) (hXW : X ≤ P.W) (hX1 : X ≠ ⊥)
    (D : HoltData (centralizerImage Ω X) (fixSet Ω X)) {ℓ : Set Ω}
    (hℓ : ℓ ∈ linesThrough G C.line α) (hXℓ : X ≤ P.Wl ℓ) :
    ∃ c : D.ι, ∀ y : fixSet Ω X, (y : Ω) ∈ ℓ → ∀ j, j ≠ c →
      D.coord y j = D.coord ⟨α, P.line_subset_fixSet_of_le_W hXW C.α_mem_line⟩ j := by
  have hS := h.setting
  have hXp := P.isPGroup_of_le_W hXW
  have h3 := P.three_le_card_fixSet_of_le_W hXW
  have hinj := D.coord_injective (P.jOddCore_eq_bot h hXW hX1)
  set αX : fixSet Ω X := ⟨α, P.line_subset_fixSet_of_le_W hXW C.α_mem_line⟩
  have hℓX : ∀ y ∈ ℓ, y ∈ fixSet Ω X := fun y hy x hx => (P.mem_Wl.mp (hXℓ hx)).2 y hy
  obtain ⟨y₀, hy₀, hy₀α⟩ := exists_mem_ne_of_mem_linesThrough (C := C) hℓ
  set y₀X : fixSet Ω X := ⟨y₀, hℓX y₀ hy₀⟩
  obtain ⟨c, hc⟩ : ∃ c, D.coord y₀X c ≠ D.coord αX c := by
    by_contra hne
    exact hy₀α (congrArg Subtype.val (hinj (funext fun j => by_contra fun h1 => hne ⟨j, h1⟩)))
  obtain ⟨y₁, hy₁, y₂, hy₂, hy₁J, hy₂J, hy₁₂⟩ := D.exists_longInvAt_apply_ne c (Ne.symm hc)
  obtain ⟨t₀, ht₀⟩ := D.longInvAt_nonempty αX
  set t₀H : jHull (centralizerImage Ω X) (fixSet Ω X) := ⟨t₀, mem_jHull_of_mem_longInv ht₀.1⟩
  have hreal : ∀ w ∈ (D.ρ c).range,
      w ∈ longInvAt (Equiv.Perm (D.Ψc c)) (D.Ψc c) (D.coord αX c) →
      ∃ π : jHull (centralizerImage Ω X) (fixSet Ω X),
        (π : centralizerImage Ω X) ∈ longInvAt (centralizerImage Ω X) (fixSet Ω X) αX ∧
          ∀ j, D.ρ j π = Function.update (fun j => D.ρ j t₀H) c w j := by
    intro w hw hwJ
    refine D.exists_mem_longInvAt_rho_eq αX _ (fun j => ?_) (fun j => ?_)
    · rcases eq_or_ne j c with rfl | hj
      · rw [Function.update_self]; exact hw
      · rw [Function.update_of_ne hj]; exact ⟨t₀H, rfl⟩
    · rcases eq_or_ne j c with rfl | hj
      · rw [Function.update_self]; exact hwJ
      · rw [Function.update_of_ne hj]; exact D.rho_mem_longInvAt ht₀ j
  obtain ⟨π₁, hπ₁, hρ₁⟩ := hreal y₁ hy₁ hy₁J
  obtain ⟨π₂, hπ₂, hρ₂⟩ := hreal y₂ hy₂ hy₂J
  obtain ⟨s₁, hs₁, -, hs₁π⟩ :=
    (hS.mem_longInvAt_centralizerImage_iff hXp h3 (π₁ : centralizerImage Ω X)).mp hπ₁
  obtain ⟨s₂, hs₂, -, hs₂π⟩ :=
    (hS.mem_longInvAt_centralizerImage_iff hXp h3 (π₂ : centralizerImage Ω X)).mp hπ₂
  set z₁ := (π₁ : centralizerImage Ω X) • y₀X
  set z₂ := (π₂ : centralizerImage Ω X) • y₀X
  have hzℓ : ∀ {s : G}, s ∈ longInvAt G Ω α → s • y₀ ∈ ℓ := fun {s} hs => by
    rw [← h.smul_eq_of_mem_K (Subgroup.subset_closure hs) hℓ]
    exact Set.smul_mem_smul_set hy₀
  have hz₁ℓ : (z₁ : Ω) ∈ ℓ := by
    rw [show (z₁ : Ω) = s₁ • y₀ from hs₁π y₀X]
    exact hzℓ hs₁
  have hz₂ℓ : (z₂ : Ω) ∈ ℓ := by
    rw [show (z₂ : Ω) = s₂ • y₀ from hs₂π y₀X]
    exact hzℓ hs₂
  have hcz : ∀ j, j ≠ c → D.coord z₁ j = D.coord z₂ j := fun j hj => by
    rw [show z₁ = ((π₁ : centralizerImage Ω X)) • y₀X from rfl, D.coord_smul, D.coord_smul, hρ₁,
      hρ₂, Function.update_of_ne hj, Function.update_of_ne hj]
  have hz₁₂ : (z₁ : Ω) ≠ z₂ := fun h1 => hy₁₂ (by
    have := congrArg (fun z => D.coord z c) (Subtype.ext h1 : z₁ = z₂)
    simp only [z₁, z₂, D.coord_smul, hρ₁, hρ₂, Function.update_self] at this
    exact this)
  refine ⟨c, fun y hy j hj => ?_⟩
  by_cases hyα : (y : Ω) = α
  · rw [show y = αX from Subtype.ext hyα]
  obtain ⟨g, hg, hg₁, hg₂⟩ := P.exists_closure_smul_eq h hXW hℓ hXℓ hz₁ℓ hz₂ℓ hℓ.2 hy hz₁₂
    (Ne.symm hyα)
  obtain ⟨hgC, hgH⟩ := hS.centralizerImageElt_mem_jHull_of_mem_closure hXp h3 hg
  set gH : jHull (centralizerImage Ω X) (fixSet Ω X) := ⟨_, hgH⟩
  have e₁ : (gH : centralizerImage Ω X) • z₁ = αX := Subtype.ext hg₁
  have e₂ : (gH : centralizerImage Ω X) • z₂ = y := Subtype.ext hg₂
  rw [← e₁, ← e₂, D.coord_smul gH z₂ j, D.coord_smul gH z₁ j, hcz j hj]

theorem false_of_coord_eq (h : C.P95) (hXW : X ≤ P.W) (hX1 : X ≠ ⊥)
    (D : HoltData (centralizerImage Ω X) (fixSet Ω X)) {ℓ : Set Ω}
    (hℓ : ℓ ∈ linesThrough G C.line α) (hXℓ : X ≤ P.Wl ℓ) (hℓL : ℓ ≠ C.line) {c : D.ι}
    (hcL : ∀ y : fixSet Ω X, (y : Ω) ∈ C.line → ∀ j, j ≠ c →
      D.coord y j = D.coord ⟨α, P.line_subset_fixSet_of_le_W hXW C.α_mem_line⟩ j)
    (hcℓ : ∀ y : fixSet Ω X, (y : Ω) ∈ ℓ → ∀ j, j ≠ c →
      D.coord y j = D.coord ⟨α, P.line_subset_fixSet_of_le_W hXW C.α_mem_line⟩ j) : False := by
  have hS := h.setting
  have hXp := P.isPGroup_of_le_W hXW
  have h3 := P.three_le_card_fixSet_of_le_W hXW
  have hinj := D.coord_injective (P.jOddCore_eq_bot h hXW hX1)
  set αX : fixSet Ω X := ⟨α, P.line_subset_fixSet_of_le_W hXW C.α_mem_line⟩
  set βX : fixSet Ω X := ⟨C.β, P.line_subset_fixSet_of_le_W hXW C.β_mem_line⟩
  have hℓX : ∀ y ∈ ℓ, y ∈ fixSet Ω X := fun y hy x hx => (P.mem_Wl.mp (hXℓ hx)).2 y hy
  obtain ⟨y₀, hy₀, hy₀α⟩ := exists_mem_ne_of_mem_linesThrough (C := C) hℓ
  set y₀X : fixSet Ω X := ⟨y₀, hℓX y₀ hy₀⟩
  have hLl := line_mem_linesThrough C
  have hβc : D.coord βX c ≠ D.coord αX c := fun h1 => C.ne (congrArg Subtype.val (hinj (funext
    fun j => by
      rcases eq_or_ne j c with rfl | hj
      · exact h1.symm
      · exact (hcL βX C.β_mem_line j hj).symm)))
  have hy₀c : D.coord y₀X c ≠ D.coord αX c := fun h1 => hy₀α (congrArg Subtype.val (hinj (funext
    fun j => by
      rcases eq_or_ne j c with rfl | hj
      · exact h1
      · exact hcℓ y₀X hy₀ j hj)))
  rcases D.factor c with ⟨hAlt, h7⟩ | hSE
  ·
    refine hℓL (h.eq_of_mem_of_mem hℓ hLl ?_ C.β_mem_line (Ne.symm C.ne))
    by_cases hβy : D.coord βX c = D.coord y₀X c
    · have : βX = y₀X := hinj (funext fun j => by
        rcases eq_or_ne j c with rfl | hj
        · exact hβy
        · rw [hcL βX C.β_mem_line j hj, hcℓ y₀X hy₀ j hj])
      rw [show C.β = y₀ from congrArg Subtype.val this]
      exact hy₀
    have hM : alternatingGroup (D.Ψc c) ≤ (D.ρ c).range := by
      rw [D.range_rho, ← hAlt]
      exact le_sup_left
    have hΔ' := holtDelta'_eq_compl_of_alternatingGroup_le hM ⟨D.tHull, rfl⟩
      (D.rho_mem_longInv D.t_mem c) (Ne.symm hy₀c)
    have hmem : D.coord βX c ∈ holtDelta' (D.ρ c).range (D.Ψc c) (D.coord αX c)
        (D.coord y₀X c) := by
      rw [hΔ']
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hβc, hβy⟩
    obtain ⟨w, hw, hwβ⟩ := hmem
    obtain ⟨t₀, ht₀⟩ := D.longInvAt_nonempty αX
    set t₀H : jHull (centralizerImage Ω X) (fixSet Ω X) := ⟨t₀, mem_jHull_of_mem_longInv ht₀.1⟩
    obtain ⟨π, hπ, hρ⟩ := D.exists_mem_longInvAt_rho_eq αX
      (Function.update (fun j => D.ρ j t₀H) c (w : Equiv.Perm (D.Ψc c))) (fun j => by
        rcases eq_or_ne j c with rfl | hj
        · rw [Function.update_self]; exact w.2
        · rw [Function.update_of_ne hj]; exact ⟨t₀H, rfl⟩) (fun j => by
        rcases eq_or_ne j c with rfl | hj
        · rw [Function.update_self]; exact mem_longInvAt_subgroup_iff.mp hw
        · rw [Function.update_of_ne hj]; exact D.rho_mem_longInvAt ht₀ j)
    obtain ⟨s, hs, -, hsπ⟩ :=
      (hS.mem_longInvAt_centralizerImage_iff hXp h3 (π : centralizerImage Ω X)).mp hπ
    have hsy : (π : centralizerImage Ω X) • y₀X = βX := hinj (funext fun j => by
      rw [D.coord_smul, hρ]
      rcases eq_or_ne j c with rfl | hj
      · rw [Function.update_self]; exact hwβ
      · rw [Function.update_of_ne hj, hcℓ y₀X hy₀ j hj, hcL βX C.β_mem_line j hj]
        exact (D.rho_mem_longInvAt ht₀ j).2)
    have h1 : s • y₀ = C.β := (hsπ y₀X).symm.trans (congrArg Subtype.val hsy)
    rw [← h1, ← h.smul_eq_of_mem_K (Subgroup.subset_closure hs) hℓ]
    exact Set.smul_mem_smul_set hy₀
  ·
    have hEC := P.E_le_centralizer_of_le_W h hXW
    have hy₀L : y₀ ∈ C.line := P.mem_line_of_forall h fun e he heL => by
      set πH : jHull (centralizerImage Ω X) (fixSet Ω X) :=
        ⟨_, P.centralizerImageElt_mem_jHull h hXW he⟩
      have hπα : (πH : centralizerImage Ω X) • αX = αX :=
        Subtype.ext (heL α C.α_mem_line)
      have hπβ : (πH : centralizerImage Ω X) • βX = βX := Subtype.ext (heL _ C.β_mem_line)
      have hρa : D.ρ c πH (D.coord αX c) = D.coord αX c := by
        rw [← D.coord_smul, hπα]
      have hρb : D.ρ c πH (D.coord βX c) = D.coord βX c := by
        rw [← D.coord_smul, hπβ]
      have hρ1 : D.ρ c πH = 1 := by
        by_contra hne
        have h2 : D.ρ c πH * D.ρ c πH = 1 := by
          rw [← map_mul]
          have : πH * πH = 1 := Subtype.ext (Subtype.ext (Equiv.ext fun y => Subtype.ext (by
            show e • e • (y : Ω) = y
            rw [smul_smul, P.mul_self_E h he, one_smul])))
          rw [this, map_one]
        have hord : orderOf (⟨D.ρ c πH, D.rho_mem_M_of_isNaturalSE hSE πH⟩ : D.M c) = 2 := by
          rw [Subgroup.orderOf_mk]
          exact orderOf_eq_prime (by rw [sq]; exact h2) hne
        obtain ⟨δ, -, hδ⟩ := hSE.existsUnique_fixed hord
        exact hβc ((hδ _ hρb).trans (hδ _ hρa).symm)
      have hfixy : (πH : centralizerImage Ω X) • y₀X = y₀X := hinj (funext fun j => by
        rw [D.coord_smul]
        rcases eq_or_ne j c with rfl | hj
        · rw [hρ1, Equiv.Perm.one_apply]
        · rw [hcℓ y₀X hy₀ j hj, ← D.coord_smul, hπα])
      exact congrArg Subtype.val hfixy
    exact hℓL (h.eq_of_mem_of_mem hℓ hLl hy₀ hy₀L hy₀α)

end P95Data

end Pattern

section Lemma52

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G} {C : P49Config G Ω α v}

namespace P95Data

variable (P : C.P95Data) {X : Subgroup G}

theorem exists_mem_E_of_le_W (h : C.P95) (hXW : X ≤ P.W) (hX1 : X ≠ ⊥) :
    ∃ e ∈ P.E, (∀ ℓ' ∈ linesThrough G C.line α, ℓ' ≠ C.line → X ≤ P.Wl ℓ' →
      ∀ y ∈ ℓ', e • y = y) ∧ e • C.β ≠ C.β := by
  have hS := h.setting
  have hXp := P.isPGroup_of_le_W hXW
  have h3 := P.three_le_card_fixSet_of_le_W hXW
  obtain ⟨D⟩ := hS.holtData_centralizerImage hXp hX1 h3
  have hinj := D.coord_injective (P.jOddCore_eq_bot h hXW hX1)
  set αX : fixSet Ω X := ⟨α, P.line_subset_fixSet_of_le_W hXW C.α_mem_line⟩
  set βX : fixSet Ω X := ⟨C.β, P.line_subset_fixSet_of_le_W hXW C.β_mem_line⟩
  have hLl := line_mem_linesThrough C
  obtain ⟨c, hcL⟩ := P.exists_coord_of_le_Wl h hXW hX1 D hLl (le_of_le_of_eq hXW rfl)
  have hβc : D.coord βX c ≠ D.coord αX c := fun h1 => C.ne (congrArg Subtype.val (hinj (funext
    fun j => by
      rcases eq_or_ne j c with rfl | hj
      · exact h1.symm
      · exact (hcL βX C.β_mem_line j hj).symm)))
  obtain ⟨t₀, ht₀⟩ := D.longInvAt_nonempty αX
  set t₀H : jHull (centralizerImage Ω X) (fixSet Ω X) := ⟨t₀, mem_jHull_of_mem_longInv ht₀.1⟩
  obtain ⟨y', hy', hy'J, hy'β⟩ : ∃ y' ∈ (D.ρ c).range,
      y' ∈ longInvAt (Equiv.Perm (D.Ψc c)) (D.Ψc c) (D.coord αX c) ∧
        y' (D.coord βX c) ≠ D.ρ c t₀H (D.coord βX c) := by
    obtain ⟨y₁, hy₁, y₂, hy₂, hy₁J, hy₂J, hy₁₂⟩ := D.exists_longInvAt_apply_ne c (Ne.symm hβc)
    by_cases h1 : y₁ (D.coord βX c) = D.ρ c t₀H (D.coord βX c)
    · exact ⟨y₂, hy₂, hy₂J, fun h2 => hy₁₂ (h1.trans h2.symm)⟩
    · exact ⟨y₁, hy₁, hy₁J, h1⟩
  obtain ⟨π, hπ, hρ⟩ := D.exists_mem_longInvAt_rho_eq αX
    (Function.update (fun j => D.ρ j t₀H) c y') (fun j => by
      rcases eq_or_ne j c with rfl | hj
      · rw [Function.update_self]; exact hy'
      · rw [Function.update_of_ne hj]; exact ⟨t₀H, rfl⟩) (fun j => by
      rcases eq_or_ne j c with rfl | hj
      · rw [Function.update_self]; exact hy'J
      · rw [Function.update_of_ne hj]; exact D.rho_mem_longInvAt ht₀ j)
  obtain ⟨s₁, hs₁, -, hs₁t⟩ := (hS.mem_longInvAt_centralizerImage_iff hXp h3
    (t₀ : centralizerImage Ω X)).mp ht₀
  obtain ⟨s₂, hs₂, -, hs₂π⟩ := (hS.mem_longInvAt_centralizerImage_iff hXp h3
    (π : centralizerImage Ω X)).mp hπ
  have hs₁K : s₁ ∈ C.K := Subgroup.subset_closure hs₁
  have hs₂K : s₂ ∈ C.K := Subgroup.subset_closure hs₂
  obtain ⟨e, he, heγ⟩ := P.exists_mem_E_eqOn h (mul_mem hs₁K hs₂K)
  have hs₁s₁ := mul_self_eq_one_of_mem_longInv hs₁.1
  refine ⟨e, he, fun ℓ' hℓ' hℓ'L hXℓ' y hy => ?_, ?_⟩
  · obtain ⟨c', hc'⟩ := P.exists_coord_of_le_Wl h hXW hX1 D hℓ' hXℓ'
    have hcc' : c ≠ c' := fun hcc => P.false_of_coord_eq h hXW hX1 D hℓ' hXℓ' hℓ'L hcL
      (hcc ▸ hc')
    have hyX : y ∈ fixSet Ω X := fun x hx => (P.mem_Wl.mp (hXℓ' hx)).2 y hy
    have hsy : s₂ • y = s₁ • y := by
      have e1 : (π : centralizerImage Ω X) • (⟨y, hyX⟩ : fixSet Ω X) =
          (t₀H : centralizerImage Ω X) • ⟨y, hyX⟩ := hinj (funext fun j => by
        rw [D.coord_smul, D.coord_smul, hρ]
        rcases eq_or_ne j c with rfl | hj
        · rw [Function.update_self, hc' ⟨y, hyX⟩ hy j hcc']
          exact hy'J.2.trans (D.rho_mem_longInvAt ht₀ j).2.symm
        · rw [Function.update_of_ne hj])
      have h1 := hs₂π ⟨y, hyX⟩
      have h2 := hs₁t ⟨y, hyX⟩
      simp only at h1 h2
      rw [← h1, ← h2]
      exact congrArg Subtype.val e1
    rcases eq_or_ne y α with rfl | hyα
    · exact mem_stabilizer_iff.mp (P.E_le_stabilizer he)
    · rw [heγ y (?_), mul_smul, hsy, smul_smul, hs₁s₁, one_smul]
      obtain ⟨n, hnα, -, rfl⟩ := P.exists_mem_normalizer_smul_line h hℓ'
      obtain ⟨w, hw, rfl⟩ := hy
      have hwα : w ≠ α := fun h1 => hyα (by rw [h1]; exact mem_stabilizer_iff.mp hnα)
      rw [← smul_Γ hnα]
      exact Set.smul_mem_smul_set (mem_Γ_of_mem_line C hw hwα)
  · rw [heγ _ C.β_mem_Γ, mul_smul]
    intro h1
    have h2 : s₂ • C.β = s₁ • C.β := by
      conv_rhs => rw [← h1]
      rw [smul_smul, hs₁s₁, one_smul]
    have e1 : D.coord ((π : centralizerImage Ω X) • βX) c =
        D.coord ((t₀H : centralizerImage Ω X) • βX) c := by
      congr 1
      exact Subtype.ext ((hs₂π βX).trans (h2.trans (hs₁t βX).symm))
    rw [D.coord_smul, D.coord_smul, hρ, Function.update_self] at e1
    exact hy'β e1

theorem Torus.V_le_Wl_of_le (h : C.P95) (T : P.Torus) (hXW : X ≤ P.W) (hX1 : X ≠ ⊥)
    {ℓ : Set Ω} (hℓ : ℓ ∈ linesThrough G C.line α) (hℓL : ℓ ≠ C.line) (hXℓ : X ≤ P.Wl ℓ) :
    T.V ≤ P.Wl ℓ := by
  set E' : Subgroup G := P.E ⊓ ⨅ (ℓ' : Set Ω) (_ : ℓ' ∈ linesThrough G C.line α ∧
    ℓ' ≠ C.line ∧ X ≤ P.Wl ℓ'), fixingSubgroup G ℓ'
  have hmemE' : ∀ {e}, e ∈ E' ↔ e ∈ P.E ∧ ∀ ℓ' ∈ linesThrough G C.line α, ℓ' ≠ C.line →
      X ≤ P.Wl ℓ' → ∀ y ∈ ℓ', e • y = y := fun {e} => by
    simp only [E', Subgroup.mem_inf, Subgroup.mem_iInf, mem_fixingSubgroup_iff, and_imp]
  have hE'E : E' ≤ P.E := inf_le_left
  have hnL : T.n • C.line = C.line := T.lineActs.smul_line
  have hinv : ∀ e ∈ E', T.n * e * T.n⁻¹ ∈ E' := by
    intro e he
    obtain ⟨heE, hefix⟩ := hmemE'.mp he
    refine hmemE'.mpr ⟨T.conj_mem_E heE, fun ℓ' hℓ' hℓ'L hXℓ' y hy => ?_⟩
    have hℓ'' : T.n⁻¹ • ℓ' ∈ linesThrough G C.line α := by
      have := smul_mem_linesThrough hℓ' T.n⁻¹
      rwa [mem_stabilizer_iff.mp (inv_mem T.mem_stabilizer)] at this
    have hℓ''L : T.n⁻¹ • ℓ' ≠ C.line := fun h1 => hℓ'L (by
      rw [← smul_inv_smul T.n ℓ', h1, hnL])
    have hXℓ'' : X ≤ P.Wl (T.n⁻¹ • ℓ') := fun x hx => by
      refine P.mem_Wl.mpr ⟨(hXW hx).1, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      have hc := T.comm x (hXW hx)
      have hc' : x * T.n⁻¹ = T.n⁻¹ * x := by
        calc x * T.n⁻¹ = T.n⁻¹ * (T.n * x) * T.n⁻¹ := by group
          _ = T.n⁻¹ * (x * T.n) * T.n⁻¹ := by rw [hc]
          _ = T.n⁻¹ * x := by group
      rw [show x • T.n⁻¹ • z = T.n⁻¹ • x • z by rw [smul_smul, smul_smul, hc'],
        (P.mem_Wl.mp (hXℓ' hx)).2 z hz]
    rw [mul_smul, mul_smul, hefix _ hℓ'' hℓ''L hXℓ'' _ (Set.smul_mem_smul_set hy),
      smul_inv_smul]
  obtain ⟨e, he, hefix, heβ⟩ := P.exists_mem_E_of_le_W h hXW hX1
  have heE' : e ∈ E' := hmemE'.mpr ⟨he, hefix⟩
  rcases T.trivial_or_surj h hE'E hinv with htriv | hsurj
  · exact absurd (htriv e heE' _ C.β_mem_line) heβ
  · refine (T.V_le h hE'E hinv hsurj).trans fun x hx => ?_
    exact P.mem_Wl.mpr ⟨(hmemE'.mp hx).1, (hmemE'.mp hx).2 ℓ hℓ hℓL hXℓ⟩

end P95Data

end Lemma52

end P49Config

end CFSG.Holt.H78
