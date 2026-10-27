module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Pieces
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.AltOn
public import
  CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour.ShortBlockCommutator
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Star
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub

open Equiv Equiv.Perm CFSG.AGLEmbedding CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open scoped commutatorElement

namespace Short

section Generic

theorem eq_bot_of_perfect_of_isPGroup {H : Type*} [Group H] {P : Subgroup H} [Finite P]
    (hperf : ⁅P, P⁆ = P) (h2 : IsPGroup 2 P) : P = ⊥ := by
  have hnil : Group.IsNilpotent ↥P := h2.isNilpotent
  have hperfP : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.mpr hperf
  by_contra hne
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
  exact Group.IsPerfect.not_isNilpotent ↥P hnil

theorem le_of_perfect_of_le_sup {H : Type*} [Group H] [Finite H] (C : Subgroup H) [C.Normal]
    {L' K : Subgroup H} (hL : ⁅L', L'⁆ = L') (hK : IsPGroup 2 K) (h : L' ≤ C ⊔ K) : L' ≤ C := by
  set ψ : H →* H ⧸ C := QuotientGroup.mk' C
  have hC : C.map ψ = ⊥ := (Subgroup.map_eq_bot_iff C).mpr (by rw [QuotientGroup.ker_mk'])
  have h1 : L'.map ψ ≤ K.map ψ := by
    have := Subgroup.map_mono (f := ψ) h
    rwa [Subgroup.map_sup, hC, bot_sup_eq] at this
  have hperf : ⁅L'.map ψ, L'.map ψ⁆ = L'.map ψ := by rw [← Subgroup.map_commutator, hL]
  have hbot : L'.map ψ = ⊥ := eq_bot_of_perfect_of_isPGroup hperf ((hK.map ψ).to_le h1)
  intro x hx
  have hx' : ψ x ∈ L'.map ψ := ⟨x, hx, rfl⟩
  rwa [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'

theorem map_le_alternatingGroup_of_perfect {H : Type*} [Group H] {N : ℕ} (θ : H →* Perm (Fin N))
    {L' : Subgroup H} (hL : ⁅L', L'⁆ = L') : L'.map θ ≤ alternatingGroup (Fin N) := by
  have h : ⁅L'.map θ, L'.map θ⁆ = L'.map θ := by rw [← Subgroup.map_commutator, hL]
  rw [← h]
  exact (Subgroup.commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le

theorem alternatingGroup_le_map {H : Type*} [Group H] {N : ℕ} (hN : 5 ≤ N)
    (θ : H →* Perm (Fin N)) (C : Subgroup H) [C.Normal]
    (hsurj : ∀ σ ∈ alternatingGroup (Fin N), ∃ h : H, θ h = σ) {x : Perm (Fin N)}
    (hx : x ∈ C.map θ) (hxA : x ∈ alternatingGroup (Fin N)) (hx1 : x ≠ 1) :
    alternatingGroup (Fin N) ≤ C.map θ := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin N)) :=
    alternatingGroup.isSimpleGroup (by simpa using hN)
  have hnorm : ((C.map θ).subgroupOf (alternatingGroup (Fin N))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨c, hc, hcn⟩ := Subgroup.mem_subgroupOf.mp hn
    obtain ⟨m, hm⟩ := hsurj g g.2
    refine Subgroup.mem_subgroupOf.mpr ⟨m * c * m⁻¹, Subgroup.Normal.conj_mem inferInstance c hc m,
      ?_⟩
    simp [hm, hcn]
  haveI := hnorm
  rcases hsimple.eq_bot_or_eq_top_of_normal ((C.map θ).subgroupOf (alternatingGroup (Fin N)))
    with h | h
  · exfalso
    have hx' : (⟨x, hxA⟩ : alternatingGroup (Fin N)) ∈
        (C.map θ).subgroupOf (alternatingGroup (Fin N)) := hx
    rw [h, Subgroup.mem_bot] at hx'
    exact hx1 (congrArg Subtype.val hx')
  · intro σ hσ
    have : (⟨σ, hσ⟩ : alternatingGroup (Fin N)) ∈
        (C.map θ).subgroupOf (alternatingGroup (Fin N)) := by rw [h]; trivial
    exact this

theorem perfect_le_normal_of_map {H : Type*} [Group H] [Finite H] {N : ℕ} (hN : 5 ≤ N)
    (θ : H →* Perm (Fin N)) (hsurj : ∀ σ ∈ alternatingGroup (Fin N), ∃ h : H, θ h = σ)
    (hK : IsPGroup 2 θ.ker) (C : Subgroup H) [C.Normal] {L' : Subgroup H} (hL : ⁅L', L'⁆ = L')
    {x : Perm (Fin N)} (hx : x ∈ C.map θ) (hxA : x ∈ alternatingGroup (Fin N)) (hx1 : x ≠ 1) :
    L' ≤ C := by
  have hAC := alternatingGroup_le_map hN θ C hsurj hx hxA hx1
  refine le_of_perfect_of_le_sup C hL hK fun m hm => ?_
  obtain ⟨c, hc, hcm⟩ := hAC (map_le_alternatingGroup_of_perfect θ hL ⟨m, hm, rfl⟩)
  have hk : c⁻¹ * m ∈ θ.ker := by simp [MonoidHom.mem_ker, hcm]
  have : m = c * (c⁻¹ * m) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hc hk

end Generic

section CommKer

variable {G : Type} [Group G]

@[expose] def commKerSub (M Q V : Subgroup G) (hV : M ≤ Subgroup.normalizer (V : Set G)) :
    Subgroup ↥M where
  carrier := {g | ∀ q ∈ Q, ⁅q, (g : G)⁆ ∈ V}
  one_mem' := fun q _ => by simp [V.one_mem]
  mul_mem' := by
    intro a b ha hb q hq
    have e : ⁅q, (a : G) * b⁆ = ⁅q, (a : G)⁆ * ((a : G) * ⁅q, (b : G)⁆ * (a : G)⁻¹) := by
      simp only [commutatorElement_def]; group
    have h1 : (a : G) * ⁅q, (b : G)⁆ * (a : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hV a.2) _).mp (hb q hq)
    show ⁅q, (a : G) * b⁆ ∈ V
    rw [e]
    exact V.mul_mem (ha q hq) h1
  inv_mem' := by
    intro a ha q hq
    have e : ⁅q, (a : G)⁻¹⁆ = (a : G)⁻¹ * ⁅q, (a : G)⁆⁻¹ * (a : G)⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    have h1 : (a : G)⁻¹ * ⁅q, (a : G)⁆⁻¹ * (a : G)⁻¹⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hV (a⁻¹).2) _).mp (V.inv_mem (ha q hq))
    show ⁅q, (a : G)⁻¹⁆ ∈ V
    rw [e]
    exact h1

theorem normal_commKerSub {M Q V : Subgroup G} (hQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hV : M ≤ Subgroup.normalizer (V : Set G)) : (commKerSub M Q V hV).Normal := by
  refine ⟨fun n hn g q hq => ?_⟩
  have e : ⁅q, (g : G) * n * (g : G)⁻¹⁆ = (g : G) * ⁅(g : G)⁻¹ * q * (g : G)⁻¹⁻¹, (n : G)⁆ *
      (g : G)⁻¹ := by
    simp only [commutatorElement_def]; group
  have h1 : (g : G)⁻¹ * q * (g : G)⁻¹⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hQ (g⁻¹).2) q).mp hq
  show ⁅q, (g : G) * n * (g : G)⁻¹⁆ ∈ V
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hV g.2) _).mp (hn _ h1)

end CommKer

section Config

variable {G : Type} [Group G]

theorem altOn_ne_bot {N : ℕ} {Ω₁ : Finset (Fin N)} (hΩ : Ω₁.card = 6) : altOn Ω₁ ≠ ⊥ := by
  intro h
  have := card_altOn hΩ
  rw [h, Subgroup.card_bot] at this
  omega

theorem map_ker_le_pCore {S L : Subgroup G} {N : ℕ} {θ : ↥(L ⊔ S) →* Perm (Fin N)}
    (hS : IsPGroup 2 S) (hker : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S) :
    θ.ker.map (L ⊔ S).subtype ≤ pCoreOf 2 (L ⊔ S) := by
  have hKS : θ.ker.map (L ⊔ S).subtype ≤ S := by
    rintro _ ⟨k, hk, rfl⟩
    exact hker k hk
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _
    (Subgroup.map_subtype_le _) ?_ (hS.to_le hKS)
  have : (θ.ker.map (L ⊔ S).subtype).subgroupOf (L ⊔ S) = θ.ker :=
    Subgroup.comap_map_eq_self_of_injective (L ⊔ S).subtype_injective _
  rw [this]
  exact θ.normal_ker

theorem pCoreOf_le_of_map_eq_altOn {M L₁ : Subgroup G} (hL₁M : L₁ ≤ M) {N : ℕ}
    {θ : ↥M →* Perm (Fin N)} {Ω₁ : Finset (Fin N)} (hΩ : Ω₁.card = 6)
    (hθ₁ : (L₁.subgroupOf M).map θ = altOn Ω₁) (hK : θ.ker.map M.subtype ≤ pCoreOf 2 M) :
    pCoreOf 2 L₁ ≤ pCoreOf 2 M := by
  set R := pCoreOf 2 L₁ with hR
  have hRL : R ≤ L₁ := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L₁
  have hRM : R ≤ M := hRL.trans hL₁M
  have hsimple : IsSimpleGroup (altOn Ω₁) := isSimpleGroup_altOn (by omega)
  set T : Subgroup (Perm (Fin N)) := (R.subgroupOf M).map θ with hTdef
  have hR2 : IsPGroup 2 ↥(R.subgroupOf M) :=
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 L₁).comap_subtype
  have hT2 : IsPGroup 2 T := hR2.map θ
  have hTle : T ≤ altOn Ω₁ := by
    rw [← hθ₁]
    exact Subgroup.map_mono (fun x hx => hRL hx)
  have hTnorm : (T.subgroupOf (altOn Ω₁)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨r, hr, hrn⟩ := Subgroup.mem_subgroupOf.mp hn
    have hg : (g : Perm (Fin N)) ∈ (L₁.subgroupOf M).map θ := by rw [hθ₁]; exact g.2
    obtain ⟨y, hy, hyg⟩ := hg
    refine Subgroup.mem_subgroupOf.mpr ⟨y * r * y⁻¹, ?_, ?_⟩
    · show (y : G) * (r : G) * (y : G)⁻¹ ∈ R
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 L₁ hy) _).mp hr
    · simp [hyg, hrn]
  haveI := hTnorm
  have hT : T = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (T.subgroupOf (altOn Ω₁)) with h | h
    · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
      have hx' : (⟨x, hTle hx⟩ : altOn Ω₁) ∈ T.subgroupOf (altOn Ω₁) := hx
      rw [h, Subgroup.mem_bot] at hx'
      exact congrArg Subtype.val hx'
    · exfalso
      have hle : altOn Ω₁ ≤ T := fun x hx => by
        have : (⟨x, hx⟩ : altOn Ω₁) ∈ T.subgroupOf (altOn Ω₁) := by rw [h]; trivial
        exact this
      exact altOn_ne_bot hΩ (eq_bot_of_perfect_of_isPGroup (commutator_altOn (by omega))
        (hT2.to_le hle))
  intro r hr
  have h1 : θ ⟨r, hRM hr⟩ = 1 := by
    have : θ ⟨r, hRM hr⟩ ∈ T := ⟨⟨r, hRM hr⟩, hr, rfl⟩
    rwa [hT, Subgroup.mem_bot] at this
  exact hK ⟨⟨r, hRM hr⟩, h1, rfl⟩

theorem inf_pCoreOf_eq {M L₁ : Subgroup G} (hL₁M : L₁ ≤ M)
    (hcore : pCoreOf 2 L₁ ≤ pCoreOf 2 M) : L₁ ⊓ pCoreOf 2 M = pCoreOf 2 L₁ := by
  refine le_antisymm ?_ (le_inf (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 L₁) hcore)
  refine CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 _ _ inf_le_left ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro l hl
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
      CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M (hL₁M hl)⟩
  · exact (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_le inf_le_right

theorem commutator_blockV_ne_bot {S L L₁ : Subgroup G} {N : ℕ} (hN : 5 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hnat : NaturalSectionTheta S L N θ)
    {Ω₁ : Finset (Fin N)} (hΩ : Ω₁.card = 6) (hθ₁ : (L₁.subgroupOf (L ⊔ S)).map θ = altOn Ω₁) :
    ⁅blockV S L, L₁⁆ ≠ ⊥ := by
  intro h
  obtain ⟨π, hπ, -, -, hequiv, hker⟩ := hnat
  have hLV : L ≤ Subgroup.normalizer (blockV S L : Set G) :=
    le_sup_left.trans (CFSG.HardMathSupport.Cooperstein.Coordinator.sup_le_normalizer_blockV S L)
  have hUV : ⁅blockV S L, L⁆ ≤ blockV S L := Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hC : L₁ ≤ Subgroup.centralizer (blockV S L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact h)
  have h1 : (L₁.subgroupOf (L ⊔ S)).map θ = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr ?_
    rintro _ ⟨m, hm, rfl⟩
    exact (theta_eq_one_iff hN hπ hequiv hUV hker m).mpr (hC hm)
  rw [hθ₁] at h1
  exact altOn_ne_bot hΩ h1

end Config

end Short

section Main

open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.EightTenFour
  (commutator_eq_of_short)

theorem shortCommSubLStmt_holds : ShortCommSubLStmt := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁ hN hshort
  have hLle : L₁ ≤ L := hL₁ ▸ subL_le S L θ _
  have hperf : ⁅L₁, L₁⁆ = L₁ := hL₁ ▸ subL_perfect S L θ _
  have hΩ : (omegaOne Δ₀ ω a).card = 6 := hE.toE0Data.card_omegaOne ha
  have hL₁M : L₁ ≤ L ⊔ S := hLle.trans le_sup_left
  have hQS : pCoreOf 2 (L ⊔ S) ≤ S := twoCore_sup_le hE.asc hE.block hE.normalizes
  have hMQ := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)
  have hMV := sup_le_normalizer_blockV S L
  have hVQ : blockV S L ≤ pCoreOf 2 (L ⊔ S) := CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le _
  have hcore := Short.inf_pCoreOf_eq hL₁M (Short.pCoreOf_le_of_map_eq_altOn hL₁M hΩ hθ₁
    (Short.map_ker_le_pCore hE.asc.twoRadical.isPGroup hE.ker_le))
  have hne : ⁅blockV S L, L₁⁆ ≠ ⊥ :=
    Short.commutator_blockV_ne_bot (by have := hE.six_le; omega) hE.natural hΩ hθ₁
  rw [commutator_eq_of_short hshort hperf (hQS.trans hN) (fun l hl => hMQ (hL₁M hl)) hcore hVQ
    (fun l hl => hMV (hL₁M hl)) hne]
  exact Subgroup.le_normalizer_iff_commutator_le_left.mp fun l hl => hMV (hL₁M hl)

theorem normalClosureSubLStmt_holds : NormalClosureSubLStmt := by
  intro G _ _ X S L N θ Δ₀ P ω hE a ha L₁ hL₁ hθ₁ hQL₁
  have hΩ : (omegaOne Δ₀ ω a).card = 6 := hE.toE0Data.card_omegaOne ha
  have hLM : L ≤ L ⊔ S := le_sup_left
  have hMQ := CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 (L ⊔ S)
  have hMV : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) := sup_le_normalizer_blockV S L
  haveI hCn : (Short.commKerSub (L ⊔ S) (pCoreOf 2 (L ⊔ S)) (blockV S L) hMV).Normal :=
    Short.normal_commKerSub hMQ hMV
  set C := Short.commKerSub (L ⊔ S) (pCoreOf 2 (L ⊔ S)) (blockV S L) hMV with hC
  have hL₁C : L₁.subgroupOf (L ⊔ S) ≤ C := fun l hl q hq =>
    hQL₁ (Subgroup.commutator_mem_commutator hq hl)
  obtain ⟨-, -, -, hAd, -, -⟩ := hE.natural
  have hsurj : ∀ σ ∈ alternatingGroup (Fin N), ∃ h : ↥(L ⊔ S), θ h = σ := fun σ hσ => by
    obtain ⟨l, hl⟩ := hAd σ hσ
    exact ⟨_, hl⟩
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp (Short.altOn_ne_bot hΩ)
  have hxL : (x : Perm (Fin N)) ∈ (L₁.subgroupOf (L ⊔ S)).map θ := by rw [hθ₁]; exact x.2
  have hLperf : ⁅L.subgroupOf (L ⊔ S), L.subgroupOf (L ⊔ S)⁆ = L.subgroupOf (L ⊔ S) := by
    apply Subgroup.map_injective (L ⊔ S).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLM, hE.block.perfect]
  have hK2 : IsPGroup 2 θ.ker := by
    have h1 : IsPGroup 2 ↥(S.subgroupOf (L ⊔ S)) := hE.asc.twoRadical.isPGroup.comap_subtype
    exact h1.to_le fun k hk => hE.ker_le k (MonoidHom.mem_ker.mp hk)
  have hLC : L.subgroupOf (L ⊔ S) ≤ C :=
    Short.perfect_le_normal_of_map (by have := hE.six_le; omega) θ hsurj hK2 C hLperf
      (Subgroup.map_mono hL₁C hxL) (mem_altOn_iff.mp x.2).1 (fun h => hx1 (Subtype.ext h))
  exact Subgroup.commutator_le.mpr fun q hq l hl => hLC (show (⟨l, hLM hl⟩ : ↥(L ⊔ S)) ∈
    L.subgroupOf (L ⊔ S) from hl) q hq

end Main

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub
