module

public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs7

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem closureIn_eq_iSup_gLBConj (I H : Subgroup G) :
    closureIn I H = ⨆ g ∈ H, GLBConj g I := by
  unfold closureIn
  apply le_antisymm
  · refine iSup₂_le fun a ha => ?_
    have h : I.map (MulAut.conj a).toMonoidHom = GLBConj a⁻¹ I := by
      unfold GLBConj
      rw [inv_inv]
    rw [h]
    exact le_biSup (fun g => GLBConj g I) (H.inv_mem ha)
  · refine iSup₂_le fun g hg => ?_
    exact le_biSup (fun a => I.map (MulAut.conj a).toMonoidHom) (H.inv_mem hg)

theorem closureIn_eq_self {K B : Subgroup G} (hBK : B ≤ Subgroup.normalizer (K : Set G)) :
    closureIn K B = K := by
  rw [closureIn_eq_iSup_gLBConj]
  apply le_antisymm
  · refine iSup₂_le fun b hb => ?_
    rw [mem_normalizer_iff_gLBConj_eq.1 (hBK hb)]
  · have := le_biSup (fun b => GLBConj b K) (Subgroup.one_mem B)
    simpa [gLBConj_one] using this

theorem glaPComponent_ne_bot' {p : ℕ} {X L : Subgroup G} (h : GLAPComponent p X L) : L ≠ ⊥ := by
  intro hL
  have h3 := h.2.2.1
  subst hL
  have hbot : ((⊥ : Subgroup G).subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) = ⊥ := by
    rw [Subgroup.bot_subgroupOf, Subgroup.map_bot]
  rw [hbot] at h3
  obtain ⟨-, hsimple⟩ := h3.2.2
  have := hsimple.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) ⧸
      Subgroup.center ↥(⊥ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X))) := inferInstance
  exact (not_subsingleton_iff_nontrivial.2 inferInstance) hss

theorem centralizer_ne_top_of_ne_one (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {a : G} (ha : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
  intro htop
  have hZ : a ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({a} : Set G) := htop ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_singleton_iff.1 this)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hZ
    exact ha hZ
  · obtain ⟨u, v, huv⟩ := hnonab
    apply huv
    have hu : u ∈ Subgroup.center G := h ▸ Subgroup.mem_top u
    exact ((Subgroup.mem_center_iff.1 hu) v).symm

theorem isElemAbelian_zpowers_of_mem {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {x : G}
    (hx : x ∈ E) : IsElemAbelian p (Subgroup.zpowers x) :=
  isElemAbelian_mono hE (Subgroup.zpowers_le.2 hx)

theorem isPGroup_zpowers_of_mem {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) {x : G}
    (hx : x ∈ E) : IsPGroup p (Subgroup.zpowers x) :=
  isPGroup_of_isElemAbelian (isElemAbelian_zpowers_of_mem hE hx)

theorem pump_step (h183 : Input18_3_4) {p : ℕ} (hp : p.Prime) (hS4 : Stage4Order G p)
    (hKP : CFSG.Open.IsKProper G) (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    {B A L : Subgroup G} {x a : G}
    (hBxL : IsSMax p B x L) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hA : GLAIsBmax p A) (hxA : x ∈ A)
    (hAdec : ∀ b ∈ A, ∃ u ∈ B ⊓ A, ∃ v ∈ A, CentMod p L v ∧ b = u * v)
    (ha : IsEssential p A a) (haL : CentMod p L a) :
    ∃ K : Subgroup G,
      K = closureIn (GLAPLayer p (L ⊓ Subgroup.centralizer ({a} : Set G)))
        (GLAPLayer p (Subgroup.centralizer ({a} : Set G))) ∧
      GLAPComponent p (Subgroup.centralizer ({a} : Set G)) K ∧
      PumpRel p (B, x, L) (A, a, K) ∧ IsSMax p A a K ∧
      A ≤ Subgroup.normalizer (K : Set G) ∧ Nonempty (PQuot p L ≃* PQuot p K) ∧
      GLAPLayer p (L ⊓ Subgroup.centralizer ({a} : Set G)) ≤ K ∧
      GLAPLayer p (L ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ GLAPPrimeCoreOf p K = K ∧
      CentMod p K x ∧
      (∀ d ∈ A, CentMod p L d → CentMod p K d) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set Cx := Subgroup.centralizer ({x} : Set G) with hCx
  set Ca := Subgroup.centralizer ({a} : Set G) with hCa
  have hxL : GLAPComponent p Cx L := hBxL.1.2.2
  have haA : a ∈ A := ha.1
  have hap : IsPGroup p (Subgroup.zpowers a) := isPGroup_zpowers_of_mem hA.1 haA
  have hxp : IsPGroup p (Subgroup.zpowers x) := isPGroup_zpowers_of_mem hA.1 hxA
  have hACa : A ≤ Ca := isElemAbelian_le_centralizer hA.1 haA
  have hACx : A ≤ Cx := isElemAbelian_le_centralizer hA.1 hxA
  obtain ⟨hIc, hIall, hInorm, -, hIsupL, ⟨eIL⟩⟩ := glaPLayer_inf_centralizer hp hxL hap haL
  set I := GLAPLayer p (L ⊓ Ca) with hIdef
  have hIL : I ≤ L := hIc.1.trans inf_le_left
  have hCzx : Subgroup.centralizer (Subgroup.zpowers x : Set G) = Cx := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hI2 : GLAPComponent p (Ca ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) I := by
    rw [hCzx, inf_comm]
    exact glaPComponent_of_isSubnormal' hp (hxL.2.1.inf Ca) hIc
  have hKa : CFSG.Open.IsKGroup ↥Ca :=
    isKGroup_of_isKProper hKP (centralizer_ne_top_of_ne_one hsimple hnonab ha.2.1)
  have hxCa : Subgroup.zpowers x ≤ Ca := Subgroup.zpowers_le.2 (hACa hxA)
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ := h183 G Ca hKa p hp (Subgroup.zpowers x) hxCa
    (isElemAbelian_zpowers_of_mem hA.1 hxA) I hI2
  set K₀ := closureIn I (GLAPLayer p Ca) with hK₀def
  have hK₀ : K₀ = ⨆ K' ∈ 𝒞, K' := (closureIn_eq_iSup_gLBConj I _).trans h𝒞sup.symm
  have hK'K₀ : ∀ K' ∈ 𝒞, K' ≤ K₀ := fun K' hK' => hK₀ ▸ le_biSup (fun K => K) hK'
  have hK₀Ca : K₀ ≤ Ca := hK₀ ▸ iSup₂_le fun K' hK' => (h𝒞c K' hK').1
  have hrel : ∀ K' ∈ 𝒞, PumpRel p (B, x, L) (A, a, K') := fun K' hK' =>
    ⟨hBxL.1, ⟨hA, ha, h𝒞c K' hK'⟩, hxA, hAdec, haA, haL,
      glaPComponent_of_le hp (h𝒞c K' hK') (hK'K₀ K' hK') hK₀Ca⟩
  have hfacts : ∀ K' ∈ 𝒞, Nonempty (PQuot p L ≃* PQuot p K') ∧ IsSMax p A a K' ∧
      A ≤ Subgroup.normalizer (K' : Set G) := fun K' hK' => by
    obtain ⟨h1, h2, h3⟩ := hS4.2.1 (B, x, L) (A, a, K')
      (pumpLe_of_reflTransGen hBxL.1 (Relation.ReflTransGen.single (hrel K' hK'))) hBxL
    exact ⟨h1, h2, h3 hBL⟩
  have hIK₀ : I ≤ K₀ := by
    rw [hK₀def, closureIn_eq_iSup_gLBConj]
    have := le_biSup (fun g => GLBConj g I) (Subgroup.one_mem (GLAPLayer p Ca))
    simpa [gLBConj_one] using this
  obtain ⟨K, hK𝒞⟩ : 𝒞.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hbot : K₀ = ⊥ := by
      rw [hK₀, h]
      simp
    exact glaPComponent_ne_bot' hIc (eq_bot_iff.2 (hbot ▸ hIK₀))
  have huniq : ∀ K' ∈ 𝒞, K' = K := by
    intro K' hK'
    obtain ⟨e, he, hee⟩ := h𝒞tr K' hK' K hK𝒞
    have hnorm := (hfacts K' hK').2.2 (Subgroup.zpowers_le.2 hxA he)
    rw [← hee, mem_normalizer_iff_gLBConj_eq.1 hnorm]
  have hK₀K : K₀ = K := by
    rw [hK₀]
    exact le_antisymm (iSup₂_le fun K' hK' => (huniq K' hK').le) (le_biSup (fun K => K) hK𝒞)
  obtain ⟨⟨eLK⟩, hSmax, hAK⟩ := hfacts K hK𝒞
  have hKc : GLAPComponent p Ca K := h𝒞c K hK𝒞
  have hIK : I ≤ K := hK₀K ▸ hIK₀
  have hxK : CentMod p K x := by
    by_contra hnot
    exact hBxL.2 ⟨(A, a, K), (B, x, L), (A, a, K), Relation.ReflTransGen.refl, hrel K hK𝒞,
      hnot, Relation.ReflTransGen.refl⟩
  obtain ⟨hJc, hJall, -, -, hJsup, -⟩ := glaPLayer_inf_centralizer hp hKc hxp hxK
  have hIKx : GLAPComponent p (K ⊓ Cx) I := by
    refine glaPComponent_of_le hp hI2 (le_inf hIK (hIL.trans hxL.1)) ?_
    rw [hCzx]
    exact le_inf (inf_le_left.trans hKc.1) inf_le_right
  have hIJ : I = GLAPLayer p (K ⊓ Cx) := hJall I hIKx
  have hIsupK : I ⊔ GLAPPrimeCoreOf p K = K := by rw [hIJ]; exact hJsup
  obtain ⟨hOI_K, ⟨eIK⟩⟩ := cover_facts hp hIK hIsupK
  obtain ⟨hOI_L, -⟩ := cover_facts hp hIL hIsupL
  refine ⟨K, hK₀K.symm, hKc, hrel K hK𝒞, hSmax, hAK, ⟨eLK⟩, hIK, hIsupK, hxK, ?_⟩
  intro d hdA hdL
  rw [centMod_iff] at hdL ⊢
  have hdK : d ∈ Subgroup.normalizer (K : Set G) := hAK hdA
  refine ⟨hdK, fun k hk => ?_⟩
  set OK := GLAPPrimeCoreOf p K with hOK
  have hdOK : d ∈ Subgroup.normalizer (OK : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p K hdK
  have hdCa : d ∈ Ca := hACa hdA
  have hdLCa : d ∈ Subgroup.normalizer ((L ⊓ Ca : Subgroup G) : Set G) := by
    have hdCaN : d ∈ Subgroup.normalizer (Ca : Set G) := Subgroup.le_normalizer hdCa
    rw [mem_normalizer_iff_gLBConj_eq] at hdCaN ⊢
    rw [gLBConj_inf, mem_normalizer_iff_gLBConj_eq.1 hdL.1, hdCaN]
  have hdI : d ∈ Subgroup.normalizer (I : Set G) := by
    rw [mem_normalizer_iff_gLBConj_eq]
    have := glaPComponent_gLBConj hIc d
    rw [mem_normalizer_iff_gLBConj_eq.1 hdLCa] at this
    exact hIall _ this
  have hiI : ∀ i ∈ I, ⁅i, d⁆ ∈ OK := by
    intro i hi
    have h1 : ⁅i, d⁆ ∈ GLAPPrimeCoreOf p L := hdL.2 i (hIL hi)
    have h2 : ⁅i, d⁆ ∈ I := by
      have : d * i⁻¹ * d⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.1 hdI i⁻¹).1 (I.inv_mem hi)
      have e : ⁅i, d⁆ = i * (d * i⁻¹ * d⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact I.mul_mem hi this
    have h3 : ⁅i, d⁆ ∈ GLAPPrimeCoreOf p I := hOI_L ▸ ⟨h2, h1⟩
    rw [hOI_K] at h3
    exact h3.2
  have hIOK : I ≤ Subgroup.normalizer (OK : Set G) := hIK.trans (le_normalizer_glaPPrimeCoreOf p K)
  have hk' : k ∈ (I ⊔ OK : Subgroup G) := hIsupK.symm ▸ hk
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I _ hIOK] at hk'
  obtain ⟨i, hi, o, ho, rfl⟩ := Set.mem_mul.mp hk'
  have hod : ⁅o, d⁆ ∈ OK := by
    have h1 : d * o⁻¹ * d⁻¹ ∈ OK := (Subgroup.mem_normalizer_iff.1 hdOK o⁻¹).1 (OK.inv_mem ho)
    have e : ⁅o, d⁆ = o * (d * o⁻¹ * d⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact OK.mul_mem ho h1
  have e : ⁅i * o, d⁆ = (i * ⁅o, d⁆ * i⁻¹) * ⁅i, d⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact OK.mul_mem ((Subgroup.mem_normalizer_iff.1 (hIOK hi) _).1 hod) (hiI i hi)

end CFSG.LocalAnalysis.GLTheoremA
