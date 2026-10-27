module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PC
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21a
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bRed
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515C
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515F
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1521PB

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open KFactsSmall

variable {X : Type} [Group X] [Finite X]

theorem false_of_centralProd_aux_k21a {Y : Type} [Group Y] [Finite Y] {K B P : Subgroup Y}
    (hK : CFSG.Open.IsQuasisimple ↥K)
    (hty : Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) ∨
      IsLThreeTwo (↥K ⧸ Subgroup.center ↥K))
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P (Subgroup.normalizer (K : Set Y)))
    (hB : B ≤ Subgroup.normalizer (K : Set Y)) (hB9 : Nat.card B = 9) (hperm : Permutable B P)
    (hBK : B ⊓ Subgroup.centralizer (K : Set Y) = ⊥) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup Y := Subgroup.normalizer (K : Set Y) with hN
  have hPN : P ≤ N := hP.le
  have hKN : K ≤ N := Subgroup.le_normalizer
  let ρ : ↥N →* MulAut ↥K := K.normalizerMonoidHom
  have hker : B.subgroupOf N ⊓ ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    have hb' := Subgroup.mem_inf.1 hb
    have hb1 : (b : Y) ∈ B := hb'.1
    have hb2 : ρ b = 1 := MonoidHom.mem_ker.1 hb'.2
    have hb3 : (b : Y) ∈ B ⊓ Subgroup.centralizer (K : Set Y) := by
      refine Subgroup.mem_inf.2 ⟨hb1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨k, hk⟩ : ↥K) : Y)) hb2
      have h2 : (b : Y) * k * (b : Y)⁻¹ = k := h1
      calc k * (b : Y) = ((b : Y) * k * (b : Y)⁻¹) * (b : Y) := by rw [h2]
        _ = (b : Y) * k := by group
    rw [hBK, Subgroup.mem_bot] at hb3
    exact Subgroup.mem_bot.2 (Subtype.ext hb3)
  obtain ⟨e, -⟩ := autData_conjNormal_aux_equiv ρ hker
  refine K21a_holds ↥K hK hty ((B.subgroupOf N).map ρ) ((P.subgroupOf N).map ρ) ?_ ?_ ?_
  · rw [← Nat.card_congr e.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hB9]
  · have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (P.subgroupOf N) ⊤ :=
      K21bRedProof.isSylowOf_subgroupOf_top hP
    have hmap := autData_conjNormal_aux_isSylowOf_map ρ hSyl
    haveI := K21bRedProof.finite_mulAut ↥K
    haveI := K21bRedProof.innAut_normal ↥K
    refine CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hmap ?_ ?_
    · rintro _ ⟨k, rfl⟩
      refine ⟨⟨k, hKN k.2⟩, trivial, ?_⟩
      ext x
      show (k : Y) * x * (k : Y)⁻¹ = (MulAut.conj k x : ↥K)
      rfl
    · rw [Subgroup.normalizer_eq_top (H := innAut ↥K)]
      exact le_top
  · exact permutable_map ρ (K21bRedProof.permutable_subgroupOf hB hPN hperm)

theorem false_of_centralProd_aux_card {S : Type} [Group S] [Finite S] (h : IsAltSixCoverThree S) :
    Nat.card S = 1080 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center S)
  rw [Nat.card_congr e.toEquiv, card_alternatingGroup_six, hc] at h1
  omega

theorem false_of_centralProd_aux_normal {G : Type} [Group G] {K₁ K₂ : Subgroup G}
    (hsup : K₁ ⊔ K₂ = ⊤) (hcomm : K₁ ≤ Subgroup.centralizer (K₂ : Set G)) : K₂.Normal := by
  have h1 : Subgroup.normalizer (K₂ : Set G) = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le (hcomm.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  exact Subgroup.normalizer_eq_top_iff.1 h1

theorem false_of_centralProd_aux_centralizes_sup {Y : Type} [Group Y] {K₁ K₂ : Subgroup Y} {z : Y}
    (h₁ : z ∈ Subgroup.centralizer (K₁ : Set Y)) (h₂ : z ∈ Subgroup.centralizer (K₂ : Set Y)) :
    z ∈ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup Y) : Set Y) := by
  have hle : K₁ ⊔ K₂ ≤ Subgroup.centralizer ({z} : Set Y) := by
    refine sup_le (fun k hk => ?_) (fun k hk => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact ((Subgroup.mem_centralizer_iff.1 h₁) k hk).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact ((Subgroup.mem_centralizer_iff.1 h₂) k hk).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact ((Subgroup.mem_centralizer_iff.1 (hle hy)) z rfl).symm

theorem false_of_centralProd_aux_swap {G : Type} [Group G] [Finite G] {K₁ K₂ : Subgroup G}
    (hK₁ : IsAltSixCoverThree ↥K₁) (hK₂ : IsAltSixCoverThree ↥K₂) (hsup : K₁ ⊔ K₂ = ⊤)
    (hcomm : K₁ ≤ Subgroup.centralizer (K₂ : Set G)) (σ : G ≃* G) :
    K₁.map σ.toMonoidHom = K₁ ∨ K₁.map σ.toMonoidHom = K₂ := by
  have hn₂ : K₂.Normal := false_of_centralProd_aux_normal hsup hcomm
  have hn₁ : K₁.Normal :=
    false_of_centralProd_aux_normal (K₁ := K₂) (K₂ := K₁) (by rw [sup_comm]; exact hsup)
      (Subgroup.le_centralizer_iff.1 hcomm)
  have hcomp : CFSG.Open.IsComponentOf K₁ ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.step le_top (Subgroup.Normal.subgroupOf hn₁ ⊤)
      (CFSG.Open.IsSubnormal.refl ⊤), hK₁.1⟩
  have hcomp' := liftOf_conj_aux3 hcomp σ
  have hcard : Nat.card (K₁.map σ.toMonoidHom) = 1080 := by
    rw [Subgroup.card_map_of_injective σ.injective]
    exact false_of_centralProd_aux_card hK₁
  rcases kComp_holds.2 G (K₁.map σ.toMonoidHom) K₁ hn₁ hcomp' with h1 | h1
  · left
    exact Subgroup.eq_of_le_of_card_ge h1 (by rw [hcard, false_of_centralProd_aux_card hK₁])
  rcases kComp_holds.2 G (K₁.map σ.toMonoidHom) K₂ hn₂ hcomp' with h2 | h2
  · right
    exact Subgroup.eq_of_le_of_card_ge h2 (by rw [hcard, false_of_centralProd_aux_card hK₂])
  exfalso
  apply liftOf_unique_aux1 hcomp'
  have hc1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1
  have hc2 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h2
  refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 (fun x hx => ?_)
  have hx' := false_of_centralProd_aux_centralizes_sup (hc1 hx) (hc2 hx)
  rw [hsup] at hx'
  rw [Subgroup.mem_centralizer_iff]
  intro y _
  exact (Subgroup.mem_centralizer_iff.1 hx') y (Subgroup.mem_top y)

theorem false_of_centralProd_aux_mem_conj {Y : Type} [Group Y] (g : Y) (K : Subgroup Y) (x : Y) :
    x ∈ conjSub g K ↔ g⁻¹ * x * g ∈ K := by
  unfold conjSub
  constructor
  · rintro ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hk
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem false_of_centralProd_aux_conj_mul {Y : Type} [Group Y] (g h : Y) (K : Subgroup Y) :
    conjSub (g * h) K = conjSub g (conjSub h K) := by
  ext x
  rw [false_of_centralProd_aux_mem_conj, false_of_centralProd_aux_mem_conj,
    false_of_centralProd_aux_mem_conj]
  simp [mul_assoc]

theorem false_of_centralProd_aux_conj_one {Y : Type} [Group Y] (K : Subgroup Y) :
    conjSub 1 K = K := by
  ext x
  rw [false_of_centralProd_aux_mem_conj]
  simp

theorem false_of_centralProd_aux_mem_normalizer {Y : Type} [Group Y] (g : Y) (K : Subgroup Y) :
    g ∈ Subgroup.normalizer (K : Set Y) ↔ conjSub g K = K := by
  constructor
  · intro h
    exact liftOf_conj_aux1 h
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 : g * x * g⁻¹ ∈ K ↔ g * x * g⁻¹ ∈ conjSub g K := by rw [h]
    rw [h1, false_of_centralProd_aux_mem_conj]
    have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [e]

theorem false_of_centralProd_aux_odd {Y : Type} [Group Y] {K₁ K₂ : Subgroup Y} (hne : K₁ ≠ K₂)
    {g : Y} {m : ℕ} (hm : Odd m) (hg : g ^ m = 1)
    (h1 : conjSub g K₁ = K₁ ∨ conjSub g K₁ = K₂) (h2 : conjSub g K₂ = K₁ ∨ conjSub g K₂ = K₂) :
    conjSub g K₁ = K₁ := by
  by_contra hc
  have hK : conjSub g K₁ = K₂ := h1.resolve_left hc
  have hK' : conjSub g K₂ = K₁ := by
    rcases h2 with h | h
    · exact h
    · exfalso
      apply hne
      exact Subgroup.map_injective (MulAut.conj g).injective (hK.trans h.symm)
  have key : ∀ n : ℕ, conjSub (g ^ (2 * n + 1)) K₁ = K₂ := by
    intro n
    induction n with
    | zero => simpa using hK
    | succ n ih =>
      have e : g ^ (2 * (n + 1) + 1) = g * (g * g ^ (2 * n + 1)) := by
        rw [show 2 * (n + 1) + 1 = 1 + (1 + (2 * n + 1)) by ring, pow_add, pow_add, pow_one]
      rw [e, false_of_centralProd_aux_conj_mul, false_of_centralProd_aux_conj_mul, ih, hK', hK]
  obtain ⟨n, rfl⟩ := hm
  have := key n
  rw [hg, false_of_centralProd_aux_conj_one] at this
  exact hne this

theorem false_of_centralProd_aux_normalizer {Y : Type} [Group Y] {K₁ K₂ : Subgroup Y} (hne : K₁ ≠ K₂)
    (h1 : ∀ g : Y, conjSub g K₁ = K₁ ∨ conjSub g K₁ = K₂)
    (h2 : ∀ g : Y, conjSub g K₂ = K₁ ∨ conjSub g K₂ = K₂) :
    Subgroup.normalizer (K₁ : Set Y) = Subgroup.normalizer (K₂ : Set Y) ∧
      (Subgroup.normalizer (K₁ : Set Y)).Normal := by
  have hinj : ∀ g : Y, Function.Injective (fun K : Subgroup Y => conjSub g K) :=
    fun g => Subgroup.map_injective (MulAut.conj g).injective
  have h12 : ∀ g : Y, g ∈ Subgroup.normalizer (K₁ : Set Y) → g ∈ Subgroup.normalizer (K₂ : Set Y) := by
    intro g hg
    rw [false_of_centralProd_aux_mem_normalizer] at hg ⊢
    rcases h2 g with h | h
    · exact absurd (hinj g (hg.trans h.symm)) hne
    · exact h
  have h21 : ∀ g : Y, g ∈ Subgroup.normalizer (K₂ : Set Y) → g ∈ Subgroup.normalizer (K₁ : Set Y) := by
    intro g hg
    rw [false_of_centralProd_aux_mem_normalizer] at hg ⊢
    rcases h1 g with h | h
    · exact h
    · exact absurd (hinj g (h.trans hg.symm)) hne
  have heq : Subgroup.normalizer (K₁ : Set Y) = Subgroup.normalizer (K₂ : Set Y) :=
    le_antisymm (fun g hg => h12 g hg) (fun g hg => h21 g hg)
  refine ⟨heq, ⟨fun n hn g => ?_⟩⟩
  have hn2 := (false_of_centralProd_aux_mem_normalizer n K₂).1 (h12 n hn)
  rw [false_of_centralProd_aux_mem_normalizer] at hn ⊢
  have hK' : conjSub n (conjSub g⁻¹ K₁) = conjSub g⁻¹ K₁ := by
    rcases h1 g⁻¹ with h | h
    · rw [h]; exact hn
    · rw [h]; exact hn2
  calc conjSub (g * n * g⁻¹) K₁ = conjSub g (conjSub n (conjSub g⁻¹ K₁)) := by
        rw [false_of_centralProd_aux_conj_mul, false_of_centralProd_aux_conj_mul]
    _ = conjSub g (conjSub g⁻¹ K₁) := by rw [hK']
    _ = conjSub (g * g⁻¹) K₁ := by rw [false_of_centralProd_aux_conj_mul]
    _ = K₁ := by rw [mul_inv_cancel, false_of_centralProd_aux_conj_one]

theorem false_of_centralProd_aux_swapY {Y : Type} [Group Y] [Finite Y] {Jb : Subgroup Y} [Jb.Normal]
    {K₁ K₂ : Subgroup ↥Jb} (hK₁ : IsAltSixCoverThree ↥K₁) (hK₂ : IsAltSixCoverThree ↥K₂)
    (hsup : K₁ ⊔ K₂ = ⊤) (hcomm : K₁ ≤ Subgroup.centralizer (K₂ : Set ↥Jb)) (g : Y) :
    conjSub g (K₁.map Jb.subtype) = K₁.map Jb.subtype ∨
      conjSub g (K₁.map Jb.subtype) = K₂.map Jb.subtype := by
  have h := false_of_centralProd_aux_swap hK₁ hK₂ hsup hcomm (MulAut.conjNormal g)
  have key : ∀ K : Subgroup ↥Jb, conjSub g (K.map Jb.subtype) =
      (K.map (MulAut.conjNormal g).toMonoidHom).map Jb.subtype := by
    intro K
    unfold conjSub
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [key]
  rcases h with h | h
  · left; rw [h]
  · right; rw [h]

theorem false_of_centralProd_aux_conj_centralizes {Y : Type} [Group Y] {K : Subgroup Y} {c y : Y}
    (h : ∀ k ∈ K, k * y = y * k) : ∀ k ∈ conjSub c K, k * (c * y * c⁻¹) = (c * y * c⁻¹) * k := by
  intro k hk
  rw [false_of_centralProd_aux_mem_conj] at hk
  have h1 := h _ hk
  calc k * (c * y * c⁻¹) = c * ((c⁻¹ * k * c) * y) * c⁻¹ := by group
    _ = c * (y * (c⁻¹ * k * c)) * c⁻¹ := by rw [h1]
    _ = (c * y * c⁻¹) * k := by group

theorem false_of_centralProd {T R A J : Subgroup X} (hA : AConfig T R A)
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hJ : J.Normal)
    (hcp : IsCentralProdA6Z3 ↥(barO2 J)) (hnc : ⁅barO2 J, barO2 A⁆ ≠ ⊥) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : X →* X ⧸ CFSG.pCore 2 X := QuotientGroup.mk' (CFSG.pCore 2 X) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  haveI hJb : (barO2 J).Normal := hJ.map π hπs
  obtain ⟨K₁, K₂, hK₁, hK₂, hsup, hcomm, hi1, hi2⟩ := hcp
  have hcomm' : K₂ ≤ Subgroup.centralizer (K₁ : Set ↥(barO2 J)) := Subgroup.le_centralizer_iff.1 hcomm
  set Kb₁ : Subgroup (X ⧸ CFSG.pCore 2 X) := K₁.map (barO2 J).subtype with hKb₁def
  set Kb₂ : Subgroup (X ⧸ CFSG.pCore 2 X) := K₂.map (barO2 J).subtype with hKb₂def
  have hswap₁ : ∀ g : X ⧸ CFSG.pCore 2 X, conjSub g Kb₁ = Kb₁ ∨ conjSub g Kb₁ = Kb₂ :=
    fun g => false_of_centralProd_aux_swapY hK₁ hK₂ hsup hcomm g
  have hswap₂ : ∀ g : X ⧸ CFSG.pCore 2 X, conjSub g Kb₂ = Kb₁ ∨ conjSub g Kb₂ = Kb₂ := fun g =>
    (false_of_centralProd_aux_swapY hK₂ hK₁ (by rw [sup_comm]; exact hsup) hcomm' g).symm
  have hne : Kb₁ ≠ Kb₂ := by
    intro h
    have h12 : K₁ = K₂ := Subgroup.map_injective (barO2 J).subtype_injective h
    rw [← h12, inf_idem, ← centerIn_eq_cfsg] at hi1
    have h3 : Nat.card ↥K₁ = Nat.card ↥(KFactsPair.centerIn K₁) :=
      congrArg (fun H : Subgroup ↥(barO2 J) => Nat.card ↥H) hi1
    rw [false_of_centralProd_aux_card hK₁, card_centerIn_s15, hK₁.2.1] at h3
    omega
  obtain ⟨hNeq, hNnorm⟩ := false_of_centralProd_aux_normalizer hne hswap₁ hswap₂
  haveI := hNnorm
  have hKb₁ : IsAltSixCoverThree ↥Kb₁ :=
    isAltSixCoverThree_of_mulEquiv (K₁.equivMapOfInjective _ (barO2 J).subtype_injective).symm hK₁
  have hKb₂ : IsAltSixCoverThree ↥Kb₂ :=
    isAltSixCoverThree_of_mulEquiv (K₂.equivMapOfInjective _ (barO2 J).subtype_injective).symm hK₂
  have hKsup : Kb₁ ⊔ Kb₂ = barO2 J := by
    rw [hKb₁def, hKb₂def, ← Subgroup.map_sup, hsup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hT.1, hT.2.1, hT.2.2⟩
  have hTb : CFSG.ABGLocalTools.IsSylowOf 2 (T.map π) ⊤ := by
    have h := autData_conjNormal_aux_isSylowOf_map π hTsyl
    rwa [Subgroup.map_top_of_surjective π hπs] at h
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 2
      (T.map π ⊓ Subgroup.normalizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X)))
      (Subgroup.normalizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X))) :=
    CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer hTb le_top
      (by rw [Subgroup.normalizer_eq_top (H := Subgroup.normalizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X)))])
  have hA9 : ∀ a ∈ A, a ^ 9 = 1 := by
    intro a ha
    have h := pow_card_eq_one' (G := ↥A) (x := ⟨a, ha⟩)
    rw [hA.card_eq] at h
    simpa using congrArg Subtype.val h
  have hBle : A.map π ≤ Subgroup.normalizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X)) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [false_of_centralProd_aux_mem_normalizer]
    exact false_of_centralProd_aux_odd hne (m := 9) ⟨4, by norm_num⟩
      (by rw [← map_pow, hA9 a ha, map_one]) (hswap₁ _) (hswap₂ _)
  have hker := ker_conjNormal_comp π (K := barO2 J)
  set ρ : X →* MulAut ↥(barO2 J) :=
    (MulAut.conjNormal : (X ⧸ CFSG.pCore 2 X) →* MulAut ↥(barO2 J)).comp π with hρ
  have hkerN : T ≤ Subgroup.normalizer (ρ.ker : Set X) := by
    rw [Subgroup.normalizer_eq_top (H := ρ.ker)]
    exact le_top
  have hinf : A ⊓ ρ.ker = ⊥ := by
    rcases hA.inf_eq_bot_or_le hkerN with h | h
    · exact h
    · exfalso
      apply hnc
      have h1 : A.map π ≤ Subgroup.centralizer
          ((barO2 J : Subgroup (X ⧸ CFSG.pCore 2 X)) : Set (X ⧸ CFSG.pCore 2 X)) := by
        rw [Subgroup.map_le_iff_le_comap, ← hker]
        exact h
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 h1
  have hAker : A ⊓ π.ker = ⊥ := by
    refine eq_bot_iff.2 (fun x hx => ?_)
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    have h1 : x ∈ A ⊓ ρ.ker := Subgroup.mem_inf.2 ⟨hx1, by
      rw [hρ, MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hx2, map_one]⟩
    rw [hinf] at h1
    exact h1
  obtain ⟨eA, -⟩ := autData_conjNormal_aux_equiv π hAker
  have hB9 : Nat.card (A.map π) = 9 := by
    rw [← Nat.card_congr eA.toEquiv]
    exact hA.card_eq
  have hK21 : ∀ Kb : Subgroup (X ⧸ CFSG.pCore 2 X), (Kb = Kb₁ ∨ Kb = Kb₂) → IsAltSixCoverThree ↥Kb →
      ∃ a ∈ A, a ≠ 1 ∧ π a ∈ Subgroup.centralizer (Kb : Set (X ⧸ CFSG.pCore 2 X)) := by
    intro Kb hKb hqs
    have hNKb : Subgroup.normalizer (Kb : Set (X ⧸ CFSG.pCore 2 X)) =
        Subgroup.normalizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X)) := by
      rcases hKb with rfl | rfl
      · rfl
      · exact hNeq.symm
    by_contra hcon
    push Not at hcon
    refine false_of_centralProd_aux_k21a (K := Kb) (B := A.map π)
      (P := T.map π ⊓ Subgroup.normalizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X))) hqs.1
      (Or.inl hqs.2.2) ?_ ?_ hB9 ?_ ?_
    · rw [hNKb]
      exact hPsyl
    · rw [hNKb]
      exact hBle
    · exact K21bRedProof.permutable_inf_of_le hBle (permutable_map π hA.perm)
    · rw [eq_bot_iff]
      intro b hb
      obtain ⟨hb1, hb2⟩ := Subgroup.mem_inf.1 hb
      obtain ⟨a, ha, rfl⟩ := hb1
      by_cases ha1 : a = 1
      · rw [ha1, map_one]
        exact Subgroup.one_mem _
      · exact absurd hb2 (hcon a ha ha1)
  obtain ⟨a₁, ha₁A, ha₁1, ha₁c⟩ := hK21 Kb₁ (Or.inl rfl) hKb₁
  obtain ⟨a₂, ha₂A, ha₂1, ha₂c⟩ := hK21 Kb₂ (Or.inr rfl) hKb₂
  have hD : ∀ x ∈ A, π x ∈ Subgroup.centralizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X)) →
      π x ∈ Subgroup.centralizer (Kb₂ : Set (X ⧸ CFSG.pCore 2 X)) → x = 1 := by
    intro x hx h1 h2
    have h3 : π x ∈ Subgroup.centralizer
        ((barO2 J : Subgroup (X ⧸ CFSG.pCore 2 X)) : Set (X ⧸ CFSG.pCore 2 X)) := by
      rw [← hKsup]
      exact false_of_centralProd_aux_centralizes_sup h1 h2
    have h4 : x ∈ A ⊓ ρ.ker := Subgroup.mem_inf.2 ⟨hx, by
      rw [hρ, hker]
      exact h3⟩
    rw [hinf] at h4
    exact Subgroup.mem_bot.1 h4
  obtain ⟨b, hbA, hb1, hb2⟩ : ∃ b ∈ A,
      π b ∉ Subgroup.centralizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X)) ∧
      π b ∉ Subgroup.centralizer (Kb₂ : Set (X ⧸ CFSG.pCore 2 X)) := by
    by_contra hcon
    have hcon' : ∀ b ∈ A, π b ∈ Subgroup.centralizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X)) ∨
        π b ∈ Subgroup.centralizer (Kb₂ : Set (X ⧸ CFSG.pCore 2 X)) := by
      intro b hb
      by_contra hh
      push Not at hh
      exact hcon ⟨b, hb, hh.1, hh.2⟩
    have ha₁n : π a₁ ∉ Subgroup.centralizer (Kb₂ : Set (X ⧸ CFSG.pCore 2 X)) :=
      fun h => ha₁1 (hD a₁ ha₁A ha₁c h)
    have ha₂n : π a₂ ∉ Subgroup.centralizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X)) :=
      fun h => ha₂1 (hD a₂ ha₂A h ha₂c)
    rcases hcon' (a₁ * a₂) (A.mul_mem ha₁A ha₂A) with h | h
    · rw [map_mul] at h
      exact ha₂n (by
        have := (Subgroup.centralizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X))).mul_mem
          ((Subgroup.centralizer (Kb₁ : Set (X ⧸ CFSG.pCore 2 X))).inv_mem ha₁c) h
        simpa using this)
    · rw [map_mul] at h
      exact ha₁n (by
        have := (Subgroup.centralizer (Kb₂ : Set (X ⧸ CFSG.pCore 2 X))).mul_mem h
          ((Subgroup.centralizer (Kb₂ : Set (X ⧸ CFSG.pCore 2 X))).inv_mem ha₂c)
        simpa using this)
  have hb1' : b ≠ 1 := fun h => hb1 (by rw [h, map_one]; exact Subgroup.one_mem _)
  obtain ⟨t, -, htab⟩ := hA.transitive a₁ ha₁A ha₁1 b hbA hb1'
  have hπb : π b = π t * π a₁ * (π t)⁻¹ := by
    rw [← htab]
    simp [map_mul, map_inv]
  have hcl := false_of_centralProd_aux_conj_centralizes (K := Kb₁) (c := π t) (y := π a₁)
    (fun k hk => (Subgroup.mem_centralizer_iff.1 ha₁c) k hk)
  rcases hswap₁ (π t) with h | h
  · rw [h] at hcl
    exact hb1 (by rw [hπb]; exact Subgroup.mem_centralizer_iff.2 hcl)
  · rw [h] at hcl
    exact hb2 (by rw [hπb]; exact Subgroup.mem_centralizer_iff.2 hcl)

theorem isLThreeTwoProd_gnImg_aux_indep {G : Type} [Group G] {ι : Type} (H : ι → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ H i, ∀ b ∈ H j, a * b = b * a)
    (hz : ∀ i, ∀ z ∈ H i, (∀ g ∈ H i, g * z = z * g) → z = 1) : iSupIndep H := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  apply hz i x hx
  intro g hg
  have hle : (⨆ j, ⨆ (_ : j ≠ i), H j) ≤ Subgroup.centralizer (H i : Set G) := by
    refine iSup₂_le (fun j hj => ?_)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hcomm i j (Ne.symm hj) h hh y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx')) g hg

theorem isLThreeTwoProd_gnImg_aux_inj_gen {T T₁ T₂ : Subgroup X} {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L)
    (hZ : Subgroup.center ↥(barO2 (Subgroup.normalClosure (L : Set X))) = ⊥)
    (φ : X ⧸ CFSG.pCore 2 X →* X ⧸ gnC T)
    (hφ : ∀ y : X, φ (QuotientGroup.mk y) = QuotientGroup.mk y)
    (z : X ⧸ CFSG.pCore 2 X) (hz : z ∈ barO2 (Subgroup.normalClosure (L : Set X))) (h1 : φ z = 1) :
    z = 1 := by
  obtain ⟨y, hyJ, rfl⟩ := hz
  have hy : (QuotientGroup.mk y : X ⧸ gnC T) = 1 := by
    have := hφ y
    rw [← this]
    exact h1
  have hyC : y ∈ gnC T := (QuotientGroup.eq_one_iff y).1 hy
  haveI : (Subgroup.normalClosure (L : Set X) ⊓ gnC T).Normal := inferInstance
  have hcent := commute_barO2_of_commute_star_aux_centralizes_gen hl
    (Subgroup.normalClosure (L : Set X) ⊓ gnC T) inf_le_right
  have hz2 : (QuotientGroup.mk' (CFSG.pCore 2 X)) y ∈
      barO2 (Subgroup.normalClosure (L : Set X) ⊓ gnC T) :=
    Subgroup.mem_map_of_mem _ ⟨hyJ, hyC⟩
  have hmem : (⟨(QuotientGroup.mk' (CFSG.pCore 2 X)) y, Subgroup.mem_map_of_mem _ hyJ⟩ :
      ↥(barO2 (Subgroup.normalClosure (L : Set X)))) ∈
      Subgroup.center ↥(barO2 (Subgroup.normalClosure (L : Set X))) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.1 (hcent g.2)) _ hz2).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem isLThreeTwoProd_gnImg_gen (hKSML3 : KSML3) {T T₁ T₂ : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)}
    {L : Subgroup X} (hl : LiftCtxGen X T T₁ T₂ Ls L)
    (hne : L ≠ Subgroup.normalClosure (L : Set X))
    (hL3 : IsLThreeOfExp 1 ↥(barO2 L))
    (hk : Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ Subgroup.normalClosure (L : Set X)} ≤ 3) :
    IsLThreeTwoProd 2 ↥(gnImg T (Subgroup.normalClosure (L : Set X))) ∨
      IsLThreeTwoProd 3 ↥(gnImg T (Subgroup.normalClosure (L : Set X))) := by
  classical
  clear hKSML3
  set J : Subgroup X := Subgroup.normalClosure (L : Set X) with hJdef
  have hL : IsC2 L := hl.lift.1
  have hZ : Subgroup.center ↥(barO2 L) = ⊥ := by
    rcases hL3 with ⟨-, d, q, hq, hd, ⟨e⟩⟩ | ⟨h, -⟩
    · exact R1515F.center_eq_bot_of_equiv_derivedCentralQuotient hl.lift.1.component.2.2.1 e
    · omega
  have hZJ : Subgroup.center ↥(barO2 J) = ⊥ :=
    pRank_centre_barO2_normalClosure_le_one_aux_threecase hL hZ
  have hS : IsLThreeTwo ↥(barO2 L) := isLThreeTwo_iff_isLThreeOfExp_one.2 hL3
  have hfin : {L' : Subgroup X | IsC2 L' ∧ L' ≤ J}.Finite := Set.toFinite _
  have h2 : 2 ≤ Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ J} :=
    two_le_ncard_of_ne_normalClosure hL hne
  obtain ⟨k, hk2, hk3, g, hginj, hgmem, hgsurj⟩ : ∃ k : ℕ, 2 ≤ k ∧ k ≤ 3 ∧
      ∃ g : Fin k → Subgroup X, Function.Injective g ∧ (∀ i, IsC2 (g i) ∧ g i ≤ J) ∧
        ∀ L', IsC2 L' → L' ≤ J → ∃ i, g i = L' := by
    have hcard : hfin.toFinset.card = Set.ncard {L' : Subgroup X | IsC2 L' ∧ L' ≤ J} :=
      (Set.ncard_eq_toFinset_card _ hfin).symm
    refine ⟨hfin.toFinset.card, by omega, by omega,
      fun i => ((hfin.toFinset.equivFin.symm i : hfin.toFinset) : Subgroup X), ?_, ?_, ?_⟩
    · intro i j hij
      exact hfin.toFinset.equivFin.symm.injective (Subtype.ext hij)
    · intro i
      exact hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm i).2
    · intro L' hL' hle
      exact ⟨hfin.toFinset.equivFin ⟨L', hfin.mem_toFinset.2 ⟨hL', hle⟩⟩, by simp⟩
  have hconj : ∀ i, ∃ x : X, g i = L.map (MulAut.conj x).toMonoidHom := fun i =>
    isC2_le_normalClosure_conj hL (hgmem i).1 (hgmem i).2
  choose x hx using hconj
  have hHcomm : ∀ i j, i ≠ j → ∀ a ∈ barO2 (g i), ∀ b ∈ barO2 (g j), a * b = b * a := by
    intro i j hij a ha b hb
    have hcomm := isC2_commute_of_ne (hgmem i).1 (hgmem j).1 (fun h => hij (hginj h))
    have ha' := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm ha
    exact ((Subgroup.mem_centralizer_iff.1 ha') b hb).symm
  have hHz : ∀ i, ∀ w ∈ barO2 (g i), (∀ v ∈ barO2 (g i), v * w = w * v) → w = 1 := by
    intro i w hw hwc
    have hcen : KFactsPair.centerIn (barO2 (g i)) = ⊥ := by
      rw [hx i]
      have h0 : KFactsPair.centerIn (barO2 L) = ⊥ := by
        unfold KFactsPair.centerIn
        rw [hZ, Subgroup.map_bot]
      rw [barO2_map_conj, centerIn_map_conj, h0, Subgroup.map_bot]
    have hw' := (mem_centerIn_iff_s15 _ w).2 ⟨hw, hwc⟩
    rw [hcen] at hw'
    exact Subgroup.mem_bot.1 hw'
  have hindep : iSupIndep (fun i => barO2 (g i)) :=
    isLThreeTwoProd_gnImg_aux_indep _ hHcomm hHz
  have hcommP : Pairwise fun i j : Fin k => ∀ a b : X ⧸ CFSG.pCore 2 X,
      a ∈ barO2 (g i) → b ∈ barO2 (g j) → Commute a b :=
    fun i j hij a b ha hb => hHcomm i j hij a ha b hb
  have hΦinj : Function.Injective (Subgroup.noncommPiCoprod hcommP) :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep hindep
  have hΦrange : (Subgroup.noncommPiCoprod hcommP).range = barO2 J := by
    rw [Subgroup.noncommPiCoprod_range]
    apply le_antisymm
    · exact iSup_le (fun i => Subgroup.map_mono (hgmem i).2)
    · refine commute_barO2_of_commute_star_aux_normalClosure (fun x' => ?_)
      obtain ⟨i, hi⟩ := hgsurj (L.map (MulAut.conj x').toMonoidHom) (liftOf_conj_aux4 hL x')
        (commute_barO2_of_commute_star_aux_le x')
      rw [← hi]
      exact le_iSup (fun i => barO2 (g i)) i
  let φ : X ⧸ CFSG.pCore 2 X →* X ⧸ gnC T :=
    QuotientGroup.map (CFSG.pCore 2 X) (gnC T) (MonoidHom.id X)
      (by rw [Subgroup.comap_id]; exact pCore_le_gnC hl.gn)
  have hφmk : ∀ y : X, φ (QuotientGroup.mk y) = QuotientGroup.mk y := fun y => rfl
  have hφB : (barO2 J).map φ = gnImg T J := by
    unfold barO2 gnImg
    rw [Subgroup.map_map]
    congr 1
  have hψinj : Function.Injective (φ.comp (Subgroup.noncommPiCoprod hcommP)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have hu1 : φ (Subgroup.noncommPiCoprod hcommP u) = 1 := hu
    have hΦu : Subgroup.noncommPiCoprod hcommP u ∈ barO2 J := hΦrange ▸ ⟨u, rfl⟩
    have h3 := isLThreeTwoProd_gnImg_aux_inj_gen hl hZJ φ hφmk _ hΦu hu1
    exact hΦinj (h3.trans (map_one _).symm)
  have hψrange : (φ.comp (Subgroup.noncommPiCoprod hcommP)).range = gnImg T J := by
    rw [MonoidHom.range_comp, hΦrange, hφB]
  have hε : ∀ i, Nonempty (↥(barO2 L) ≃* ↥(barO2 (g i))) := by
    intro i
    refine ⟨((barO2 L).equivMapOfInjective
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 X) (x i))).toMonoidHom
      (MulAut.conj _).injective).trans (MulEquiv.subgroupCongr ?_)⟩
    rw [hx i, barO2_map_conj]
  have hiso : Nonempty (↥(gnImg T J) ≃* (Fin k → ↥(barO2 L))) :=
    ⟨((MulEquiv.piCongrRight (fun i => (hε i).some)).trans
      ((MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hψrange))).symm⟩
  obtain ⟨e⟩ := hiso
  rcases (by omega : k = 2 ∨ k = 3) with rfl | rfl
  · exact Or.inl ⟨_, _, hS, ⟨e⟩⟩
  · exact Or.inr ⟨_, _, hS, ⟨e⟩⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
