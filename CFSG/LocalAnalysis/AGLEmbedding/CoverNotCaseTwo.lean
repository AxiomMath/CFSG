module

public import CFSG.LocalAnalysis.AGLEmbedding.LemmaJStarAux
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedQuotient
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAZNAux

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

variable {L : Type*} [Group L] [Finite L] {p : ℕ} [hp : Fact p.Prime]

section Core

open CFSG.Open CFSG.AGLEmbedding CFSG.ComponentClassification.OuterAutomorphisms

variable {Y : Type} [Group Y] [Finite Y]

theorem false_of_surjective_core {J : Type*} [Group J] [Finite J] {L : Type*} [Group L]
    (ι : J →* Y) (hι : Function.Injective ι) (φ : J →* L) (hcop : p.Coprime (Nat.card φ.ker))
    (hdich : ∀ V : Subgroup J, V.Normal → V = ⊤ ∨ V ≤ φ.ker)
    (X : Subgroup J) (hX : IsPGroup p X) (hXnc : ¬ IsCyclic X)
    {K : Subgroup Y} [K.Normal] (hZ : Subgroup.center K = ⊥)
    (hJK : ∀ j : J, ∃ k ∈ K, ∃ c ∈ Subgroup.centralizer (K : Set Y), ι j = k * c)
    (hKcyc : ∀ A : Subgroup Y, IsPGroup p A → A ≤ K → IsCyclic A)
    (hCcyc : ∀ A : Subgroup Y, IsPGroup p A → A ≤ Subgroup.centralizer (K : Set Y) →
      IsCyclic A) : False := by
  set Xt := X.map ι with hXtdef
  have hXt : IsPGroup p Xt := hX.map ι
  have hXtnc : ¬ IsCyclic Xt := fun hc =>
    hXnc (isCyclic_of_surjective (X.equivMapOfInjective ι hι).symm.toMonoidHom
      (X.equivMapOfInjective ι hι).symm.surjective)
  rcases hdich (K.comap ι) inferInstance with htop | hker
  · refine hXtnc (hKcyc Xt hXt ?_)
    rintro _ ⟨x, -, rfl⟩
    have : x ∈ K.comap ι := htop ▸ Subgroup.mem_top x
    exact this
  have hXK : Xt ⊓ K = ⊥ := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hX
    have hdisj : Disjoint X φ.ker := by
      refine Subgroup.disjoint_of_coprime_natCard ?_
      rw [hm]
      exact hcop.pow_left m
    rw [eq_bot_iff]
    rintro _ ⟨⟨x, hx, rfl⟩, hxK⟩
    have h1 : x = 1 := Subgroup.disjoint_def.mp hdisj hx (hker hxK)
    rw [h1, map_one]
    exact Subgroup.one_mem _
  have hXle : Xt ≤ K ⊔ Subgroup.centralizer (K : Set Y) := by
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨k, hk, c, hc, he⟩ := hJK x
    rw [he]
    exact Subgroup.mul_mem_sup hk hc
  exact hXtnc (isCyclic_of_inf_eq_bot_of_le_sup hZ hXt hXK hXle fun A hA hAC => hCcyc A hA hAC)

theorem false_of_surjective_of_normal_cyclic {L : Type} [Group L] [Finite L]
    (hL : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a) {Jt Xt : Subgroup Y}
    (φ : Jt →* L) (hφ : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker))
    (hX : IsPGroup p Xt) (hncl : nclIn Jt Xt = Jt) (hXJ : Xt ≤ Jt) (hXnc : ¬ IsCyclic Xt)
    {K : Subgroup Y} [K.Normal] (hZ : Subgroup.center K = ⊥)
    (hKcyc : ∀ A : Subgroup Y, IsPGroup p A → A ≤ K → IsCyclic A)
    (hCcyc : ∀ A : Subgroup Y, IsPGroup p A → A ≤ Subgroup.centralizer (K : Set Y) → IsCyclic A)
    (hout : Group.IsSolvable (Outer K)) : False := by
  have hJ : Group.IsPerfect Jt := isPerfect_of_nclIn_eq hL hLnab hX hncl φ hφ hcop
  have hsup := le_sup_centralizer_of_isPerfect hJ hout
  refine false_of_surjective_core Jt.subtype Jt.subtype_injective φ hcop
    (fun V hV => eq_top_or_le_ker_of_nclIn_eq hL hX hncl φ hφ hcop V) (Xt.subgroupOf Jt)
    hX.comap_subtype (fun hc => hXnc (isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe hXJ).toMonoidHom (MulEquiv.surjective _))) hZ ?_ hKcyc hCcyc
  intro j
  obtain ⟨k, hk, c, hc, he⟩ := Subgroup.mem_sup_of_normal_left.mp (hsup j.2)
  exact ⟨k, hk, c, hc, he.symm⟩

theorem ReducedNongeneration.false_of_surjective_of_cyclic_normal {Rb : Sylow p Y}
    {Y₀ : Subgroup Y} (h : ReducedNongeneration p Y Rb Y₀) {L : Type} [Group L] [Finite L]
    (hL : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a) {Jt Xt : Subgroup Y}
    (φ : Jt →* L) (hφ : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker))
    (hXR : Xt ≤ Rb) (hncl : nclIn Jt Xt = Jt) (hXJ : Xt ≤ Jt) (hXnc : ¬ IsCyclic Xt)
    {K : Subgroup Y} [hKn : K.Normal] (hK : IsComponentOf K ⊤)
    (hCcyc : ∀ A : Subgroup Y, IsPGroup p A → A ≤ Subgroup.centralizer (K : Set Y) → IsCyclic A)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y))
    (hout : Group.IsSolvable (Outer K)) : False := by
  have hZ := h.center_eq_bot_of_isCyclic hK hcyc
  refine false_of_surjective_of_normal_cyclic hL hLnab φ hφ hcop (Rb.isPGroup'.to_le hXR) hncl
    hXJ hXnc hZ ?_ hCcyc hout
  intro A hA hAK
  obtain ⟨S, hAS⟩ := hA.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Y Rb S
  set f := (MulAut.conj g⁻¹).toMonoidHom
  have hle : A.map f ≤ (Rb : Subgroup Y) ⊓ K := by
    rintro _ ⟨a, ha, rfl⟩
    have haS : a ∈ ((g • Rb : Sylow p Y) : Subgroup Y) := hAS ha
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      ← map_inv, MulAut.conj_apply, inv_inv] at haS
    refine ⟨?_, ?_⟩
    · change (MulAut.conj g⁻¹) a ∈ (Rb : Subgroup Y)
      rw [MulAut.conj_apply, inv_inv]
      exact haS
    · change (MulAut.conj g⁻¹) a ∈ K
      rw [MulAut.conj_apply]
      exact hKn.conj_mem _ (hAK ha) _
  have : IsCyclic (A.map f) := Subgroup.isCyclic_of_le hle
  exact isCyclic_of_surjective ((A.equivMapOfInjective f (MulAut.conj g⁻¹).injective).symm :
    A.map f →* A) (MulEquiv.surjective _)

theorem ReducedNongeneration.false_of_surjective_of_cyclic_component {Rb : Sylow p Y}
    {Y₀ : Subgroup Y} (h : ReducedNongeneration p Y Rb Y₀) {L : Type} [Group L] [Finite L]
    (hL : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a) {Jt Xt : Subgroup Y}
    (φ : Jt →* L) (hφ : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker))
    (hXR : Xt ≤ Rb) (hncl : nclIn Jt Xt = Jt) (hXJ : Xt ≤ Jt) (hXnc : ¬ IsCyclic Xt)
    {K : Subgroup Y} [hKn : K.Normal] (hK : IsComponentOf K ⊤) (hKY₀ : ¬ K ≤ Y₀)
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y))
    (hout : Group.IsSolvable (Outer K)) : False :=
  Hyp111.ReducedNongeneration.false_of_surjective_of_cyclic_normal h hL hLnab φ hφ hcop hXR hncl
    hXJ hXnc hK (fun _ hA hAC => h.isCyclic_of_le_centralizer hK hKY₀ hA hAC) hcyc hout

theorem isCyclic_of_le_component {L : Subgroup Y} (hL : IsComponentOf L ⊤) {Rb : Sylow p Y}
    (hcyc : IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)) {A : Subgroup Y} (hA : IsPGroup p A)
    (hAL : A ≤ L) : IsCyclic A := by
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rb
    (ComponentClassification.Components.mathlib_subnormal_of_chain hL.2.1
      Subgroup.IsSubnormal.top)
  rw [← hP] at hcyc
  have hPc : IsCyclic (P : Subgroup L) :=
    isCyclic_of_surjective (Subgroup.equivMapOfInjective _ _ L.subtype_injective).symm
      (MulEquiv.surjective _)
  obtain ⟨T, hT⟩ := (hA.comap_subtype (K := L)).exists_le_sylow
  have hTc : IsCyclic (T : Subgroup L) :=
    isCyclic_of_surjective (Sylow.equiv P T).toMonoidHom (Sylow.equiv P T).surjective
  have : IsCyclic (A.subgroupOf L) := Subgroup.isCyclic_of_le hT
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hAL).toMonoidHom
    (MulEquiv.surjective _)

theorem normal_iInf_normalizer_components :
    (⨅ (L : Subgroup Y) (_ : IsComponentOf L ⊤), Subgroup.normalizer (L : Set Y)).Normal := by
  refine ⟨fun n hn y => ?_⟩
  simp only [Subgroup.mem_iInf] at hn ⊢
  intro L hL
  set L' := L.map (MulAut.conj y⁻¹).toMonoidHom
  have hL' : IsComponentOf L' ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj y⁻¹) L).mpr hL
  have hnL' := hn L' hL'
  have hmem : ∀ x : Y, x ∈ L' ↔ y * x * y⁻¹ ∈ L := by
    intro x
    constructor
    · rintro ⟨l, hl, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hl
    · intro hx
      exact ⟨y * x * y⁻¹, hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [Subgroup.mem_normalizer_iff] at hnL' ⊢
  intro x
  rw [show x = y * (y⁻¹ * x * y) * y⁻¹ by group, ← hmem, hnL', hmem]
  constructor <;> intro hx <;> simpa [mul_assoc] using hx

theorem ReducedNongeneration.isCyclic_of_le_centralizer_of_conj {Rb : Sylow p Y}
    {Y₀ : Subgroup Y} (h : ReducedNongeneration p Y Rb Y₀) {K : Subgroup Y}
    (hK : IsComponentOf K ⊤)
    (hconj : ∀ g : Y, ¬ K.map (MulAut.conj g).toMonoidHom ≤ Y₀) {A : Subgroup Y}
    (hA : IsPGroup p A) (hAC : A ≤ Subgroup.centralizer (K : Set Y)) : IsCyclic A := by
  have hp := h.prime
  by_contra hnc
  obtain ⟨S, hAS⟩ := hA.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq Y Rb S
  set A' := A.map (MulAut.conj g⁻¹).toMonoidHom
  set K' := K.map (MulAut.conj g⁻¹).toMonoidHom
  have hK' : IsComponentOf K' ⊤ :=
    (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g⁻¹) K).mpr hK
  have hA'le : A' ≤ (Rb : Subgroup Y) ⊓ Subgroup.centralizer (K' : Set Y) := by
    rintro _ ⟨a, ha, rfl⟩
    have haS : a ∈ ((g • Rb : Sylow p Y) : Subgroup Y) := hAS ha
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      ← map_inv, MulAut.conj_apply, inv_inv] at haS
    refine ⟨?_, ?_⟩
    · change (MulAut.conj g⁻¹) a ∈ (Rb : Subgroup Y)
      rw [MulAut.conj_apply, inv_inv]
      exact haS
    · show _ ∈ Subgroup.centralizer (K' : Set Y)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, hk, rfl⟩
      change (MulAut.conj g⁻¹) k * (MulAut.conj g⁻¹) a = (MulAut.conj g⁻¹) a * (MulAut.conj g⁻¹) k
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp (hAC ha) k hk]
  have hncA' : ¬ IsCyclic A' := fun hc =>
    let e := A.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    hnc (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  have h2 : 2 ≤ Open.pRank p A' :=
    two_le_pRank_of_isPGroup_not_isCyclic hp h.ne_two (hA.map _) hncA'
  have h1 := h.pRank_inf_centralizer_le_one_of_not_le hK' (hconj g⁻¹)
  have h3 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hA'le
  omega

theorem ReducedNongeneration.false_of_surjective_of_cyclic_product {Rb : Sylow p Y}
    {Y₀ : Subgroup Y} (h : ReducedNongeneration p Y Rb Y₀) {L : Type} [Group L] [Finite L]
    (hL : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a) {Jt Xt : Subgroup Y}
    (φ : Jt →* L) (hφ : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker))
    (hXR : Xt ≤ Rb) (hncl : nclIn Jt Xt = Jt) (hXJ : Xt ≤ Jt) (hXnc : ¬ IsCyclic Xt)
    {L₁ L₂ : Subgroup Y} (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂)
    (hL₁ : ¬ L₁ ≤ Y₀) (hL₂ : ¬ L₂ ≤ Y₀) (hcyc₁ : IsCyclic ((Rb : Subgroup Y) ⊓ L₁ : Subgroup Y))
    (hout : Group.IsSolvable (Outer L₁)) : False := by
  have hp := h.prime
  have hX : IsPGroup p Xt := Rb.isPGroup'.to_le hXR
  set N₁ := ⨅ (L : Subgroup Y) (_ : IsComponentOf L ⊤), Subgroup.normalizer (L : Set Y)
  haveI : N₁.Normal := normal_iInf_normalizer_components
  have hXN : Xt ≤ N₁ := by
    intro x hx
    simp only [N₁, Subgroup.mem_iInf]
    exact fun L hL => h.sylow_le_normalizer_component hL (hXR hx)
  have hJN₁ : Jt ≤ N₁ := by
    rw [← hncl]
    unfold nclIn
    rintro _ ⟨j, hj, rfl⟩
    have hle : Subgroup.normalClosure ((Xt.subgroupOf Jt : Subgroup Jt) : Set Jt) ≤
        N₁.subgroupOf Jt :=
      Subgroup.normalClosure_le_normal fun x hx => Subgroup.mem_subgroupOf.mpr (hXN hx)
    exact Subgroup.mem_subgroupOf.mp (hle hj)
  have hJN : Jt ≤ Subgroup.normalizer (L₁ : Set Y) := fun j hj => by
    have := hJN₁ hj
    simp only [N₁, Subgroup.mem_iInf] at this
    exact this L₁ h₁
  have hJ : Group.IsPerfect Jt := isPerfect_of_nclIn_eq hL hLnab hX hncl φ hφ hcop
  set W := Subgroup.normalizer (L₁ : Set Y) with hW
  have hLW : L₁ ≤ W := Subgroup.le_normalizer
  set K' := L₁.subgroupOf W with hK'
  haveI hK'n : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLW).mpr le_rfl
  set e : K' ≃* L₁ := Subgroup.subgroupOfEquivOfLe hLW
  have hZ₁ := h.center_eq_bot_of_isCyclic h₁ hcyc₁
  have hZ' : Subgroup.center K' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hez : e z ∈ Subgroup.center L₁ := Subgroup.mem_center_iff.mpr fun g => by
      obtain ⟨g', rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz g']
    rw [hZ₁, Subgroup.mem_bot] at hez
    exact Subgroup.mem_bot.mpr (e.injective (hez.trans e.map_one.symm))
  have hJK : ∀ j : Jt, ∃ k ∈ K', ∃ c ∈ Subgroup.centralizer (K' : Set W),
      Subgroup.inclusion hJN j = k * c := by
    intro j
    haveI := hJ
    haveI := hout
    obtain ⟨l, hl⟩ :=
      ComponentClassification.OuterAutomorphisms.perfect_action_inner
        (L₁.normalizerMonoidHom.comp (Subgroup.inclusion hJN)) j
    have hc : (l : Y)⁻¹ * j ∈ Subgroup.centralizer (L₁ : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have h1 : (j : Y) * y * (j : Y)⁻¹ = l * y * (l : Y)⁻¹ := by
        have := congrArg (fun a : MulAut L₁ => ((a ⟨y, hy⟩ : L₁) : Y)) hl
        simpa [MulAut.conj_apply] using this
      calc y * ((l : Y)⁻¹ * j) = (l : Y)⁻¹ * (l * y * (l : Y)⁻¹) * j := by group
        _ = (l : Y)⁻¹ * ((j : Y) * y * (j : Y)⁻¹) * j := by rw [h1]
        _ = (l : Y)⁻¹ * j * y := by group
    refine ⟨⟨l, hLW l.2⟩, Subgroup.mem_subgroupOf.mpr l.2,
      ⟨(l : Y)⁻¹ * j, Subgroup.centralizer_le_normalizer _ hc⟩, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro w hw
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc w (Subgroup.mem_subgroupOf.mp hw))
    · apply Subtype.ext
      change (j : Y) = l * ((l : Y)⁻¹ * j)
      group
  have hKcyc : ∀ A : Subgroup W, IsPGroup p A → A ≤ K' → IsCyclic A := by
    intro A hA hAK
    have hB : IsCyclic (A.map W.subtype) := isCyclic_of_le_component h₁ hcyc₁ (hA.map _)
      (by rintro _ ⟨a, ha, rfl⟩; exact Subgroup.mem_subgroupOf.mp (hAK ha))
    exact isCyclic_of_surjective (A.equivMapOfInjective _ W.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hconj : ∀ g : Y, ¬ L₁.map (MulAut.conj g).toMonoidHom ≤ Y₀ := by
    intro g
    have hc := (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L₁).mpr h₁
    rcases h.eq_or_eq_of_isComponentOf h₁ h₂ hne hc with heq | heq <;> rw [heq] <;> assumption
  have hCcyc : ∀ A : Subgroup W, IsPGroup p A → A ≤ Subgroup.centralizer (K' : Set W) →
      IsCyclic A := by
    intro A hA hAC
    have hB : IsCyclic (A.map W.subtype) := by
      refine Hyp111.ReducedNongeneration.isCyclic_of_le_centralizer_of_conj h h₁ hconj (hA.map _) ?_
      rintro _ ⟨a, ha, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have := Subgroup.mem_centralizer_iff.mp (hAC ha) ⟨y, hLW hy⟩
        (Subgroup.mem_subgroupOf.mpr hy)
      exact congrArg Subtype.val this
    exact isCyclic_of_surjective (A.equivMapOfInjective _ W.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  exact false_of_surjective_core (Y := W) (Subgroup.inclusion hJN)
    (Subgroup.inclusion_injective hJN)
    φ hcop (fun V hV => eq_top_or_le_ker_of_nclIn_eq hL hX hncl φ hφ hcop V) (Xt.subgroupOf Jt)
    hX.comap_subtype (fun hc => hXnc (isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe hXJ).toMonoidHom (MulEquiv.surjective _))) hZ' hJK hKcyc hCcyc

theorem ReducedNongeneration.false_of_surjective_of_cyclic {Rb : Sylow p Y}
    {Y₀ : Subgroup Y} (h : ReducedNongeneration p Y Rb Y₀)
    (hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ → IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y))
    (hex : ∃ K : Subgroup Y, IsComponentOf K ⊤)
    (hout : ∀ L : Subgroup Y, IsComponentOf L ⊤ → Group.IsSolvable (Outer L))
    {L : Type} [Group L] [Finite L]
    (hL : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a) {Jt Xt : Subgroup Y}
    (φ : Jt →* L) (hφ : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker))
    (hXR : Xt ≤ Rb) (hncl : nclIn Jt Xt = Jt) (hXJ : Xt ≤ Jt) (hXnc : ¬ IsCyclic Xt) : False := by
  by_cases hout₀ : ∃ L₁ : Subgroup Y, IsComponentOf L₁ ⊤ ∧ ¬ L₁ ≤ Y₀
  · obtain ⟨L₁, h₁, hL₁⟩ := hout₀
    by_cases htwo : ∃ L₂ : Subgroup Y, IsComponentOf L₂ ⊤ ∧ L₂ ≠ L₁
    · obtain ⟨L₂, h₂, hne⟩ := htwo
      by_cases hL₂ : L₂ ≤ Y₀
      · haveI := (h.normal_of_two_components hcyc h₁ h₂ hL₁ hL₂).1
        exact Hyp111.ReducedNongeneration.false_of_surjective_of_cyclic_component h hL hLnab φ hφ
          hcop hXR hncl hXJ hXnc h₁ hL₁ (hcyc L₁ h₁) (hout L₁ h₁)
      · exact Hyp111.ReducedNongeneration.false_of_surjective_of_cyclic_product h hL hLnab φ hφ
          hcop hXR hncl hXJ hXnc h₁ h₂ (Ne.symm hne) hL₁ hL₂ (hcyc L₁ h₁) (hout L₁ h₁)
    · push Not at htwo
      haveI := normal_of_forall_isComponentOf_eq h₁ htwo
      exact Hyp111.ReducedNongeneration.false_of_surjective_of_cyclic_component h hL hLnab φ hφ
        hcop hXR hncl hXJ hXnc h₁ hL₁ (hcyc L₁ h₁) (hout L₁ h₁)
  push Not at hout₀
  obtain ⟨K, hK⟩ := hex
  by_cases htwo : ∃ L₂ : Subgroup Y, IsComponentOf L₂ ⊤ ∧ L₂ ≠ K
  · obtain ⟨L₂, h₂, hne⟩ := htwo
    exact h.false_of_two_components hK h₂ (Ne.symm hne) hcyc hout₀
  push Not at htwo
  by_cases hO : CFSG.pCore p Y = ⊥
  · haveI := normal_of_forall_isComponentOf_eq hK htwo
    have hC := h.centralizer_eq_bot_of_unique_component htwo
      (h.center_eq_bot_of_isCyclic hK (hcyc K hK)) hO
    refine Hyp111.ReducedNongeneration.false_of_surjective_of_cyclic_normal h hL hLnab φ hφ hcop
      hXR hncl hXJ hXnc hK (fun A _ hAC => ?_) (hcyc K hK) (hout K hK)
    rw [hC, le_bot_iff] at hAC
    subst hAC
    infer_instance
  · exact h.false_of_unique_component_of_pCore_ne_bot hK htwo (hcyc K hK) (hout₀ K hK) hO

omit [Finite Y] in
theorem coprime_card_ker_comp_inclusion {L : Type*} [Group L] {Jt J : Subgroup Y} (φ : Jt →* L)
    (hcop : p.Coprime (Nat.card φ.ker)) (h : J ≤ Jt) :
    p.Coprime (Nat.card (φ.comp (Subgroup.inclusion h)).ker) := by
  rw [← MonoidHom.comap_ker]
  exact hcop.coprime_dvd_right
    (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective h))

end Core

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
