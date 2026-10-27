module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Steps

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace S8.L84

variable {G : Type} [Group G] [Finite G]

theorem stageJ (hc : S3Ctx G 3) (h183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4)
    (h112 : I112At G) (ha6 : A6FactsAt G) (h1430 : I1430At G) (hlb : LBalanceAt G 3)
    {B L D₀ I : Subgroup G} {x : G}
    (hB : GLAIsBmax 3 B) (hrk : GLATwoLocalRank 3 G = 4) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hL : GLAPComponent 3 (cx x) L) (hLuniq : ∀ J' : Subgroup G, GLAPComponent 3 (cx x) J' → J' = L)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hxL : x ∉ L)
    (hD₀ : D₀ ≤ B ⊓ L) (hD₀c : Nat.card D₀ = 3 ^ 2)
    (hI : GLAPComponent 3 (L ⊓ Subgroup.centralizer (D₀ : Set G)) I)
    (hIuniq : ∀ I' : Subgroup G, GLAPComponent 3 (L ⊓ Subgroup.centralizer (D₀ : Set G)) I' → I' = I)
    (hIt : IsTypeWithCenter 3 I isA6 1) (hIc : Nat.card (PQuot 3 I) = 360)
    (hUa : ∀ d ∈ D₀, d ≠ 1 → UniqA6 (L ⊓ cx d)) :
    ∃ D J : Subgroup G, D ≤ D₀ ⊔ Subgroup.zpowers x ∧ IsElemAbelian 3 D ∧ Nat.card D = 3 ^ 2 ∧
      x ∉ D ∧ GLAPComponent 3 (Subgroup.centralizer (D : Set G)) J ∧
      B ≤ Subgroup.normalizer (J : Set G) ∧ I ≤ J ∧ ¬ J ≤ I ⊔ GLAPPrimeCoreOf 3 J ∧
      T1430 J (D₀ ⊔ Subgroup.zpowers x) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  set E : Subgroup G := D₀ ⊔ Subgroup.zpowers x with hEdef
  obtain ⟨hEB, hEe, hEc, hLE, hEdec⟩ := E_facts hB.1 hxB hL.1 hD₀ hD₀c hxL
  have hxE : x ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hLn : cx x ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_unique_glaPComponent hL hLuniq
  have hEnc : ¬ IsCyclic E := S3.not_isCyclic_of_card hp3 hEe (by rw [hEc]; norm_num)
  obtain ⟨D, R, hDE, hDidx, hR2, hR1, hRD, hBR, hRE⟩ :=
    exists_inv_two hp3 (by norm_num) hc.charTwo hB hEB hEnc
  have hDc : Nat.card D = 3 ^ 2 := by rw [hEc] at hDidx; omega
  have hDe : IsElemAbelian 3 D := CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hEe hDE
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hDc
    norm_num at hDc
  set X : Subgroup G := Subgroup.centralizer (D : Set G) with hXdef
  have hX : CFSG.Open.IsKGroup ↥X := S3.isKGroup_cen hc.simple hc.nonabelian hc.kProper hD1
  have hEX : E ≤ X := fun e he =>
    Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_commute hEe (hDE hd) he
  have hBX : B ≤ X := fun b hb =>
    Subgroup.mem_centralizer_iff.2 fun d hd => isElemAbelian_commute hB.1 (hEB (hDE hd)) hb
  have hDX : D ≤ X := hDE.trans hEX
  have hrankX := rank_cond hp3 hB X
  obtain ⟨hICE, hIXE⟩ := I_comp_CE hLn hxE hDE hLE hI
  have hI1 : I ≠ ⊥ := glaPComponent_ne_bot' hI
  have hBI : B ≤ Subgroup.normalizer (I : Set G) := by
    intro b hb
    have hbC : b ∈ Subgroup.normalizer ((Subgroup.centralizer (D₀ : Set G) : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_iff.2 fun d hd =>
        isElemAbelian_commute hB.1 (hD₀ hd).1 hb)
    exact mem_normalizer_of_uniq hI hIuniq (mem_normalizer_inf (hBN hb) hbC)
  obtain ⟨𝒞, h𝒞, hsup, hstab, htr⟩ := h183 G X hX 3 hp3 E hEX hEe I hIXE
  have hall : ∀ K₁ ∈ 𝒞, ∀ K₂ ∈ 𝒞, K₁ = K₂ := by
    intro K₁ h1 K₂ h2
    by_contra hne
    obtain ⟨e, he, h1', h1'', hne1, hne2, hne3⟩ := three_members hEe hstab htr h1 h2 hne
    have hA6 : ∀ K ∈ 𝒞, ∀ K' ∈ 𝒞, K ≠ K' → catalogIs (PSimple 3 K) isA6 := by
      intro K hK K' hK' hKK'
      obtain ⟨-, ⟨iso⟩⟩ := diag_iso h112 hX rfl hBX hB.1 hrankX hEB hDE hDidx hICE h𝒞 hsup htr
        hK hK' hKK'
      exact (catalogIs_congr iso).1 (catalogIs_pQuot_of_center hIt.2 hIt.1)
    obtain ⟨W', T', hW', hW'c, hT'1, hT'2, hWT⟩ := three_A6_quot ha6 hDe hDc hDX le_rfl
      (h𝒞 K₁ h1) (h𝒞 _ h1') (h𝒞 _ h1'') hne1 hne2 hne3 (hA6 K₁ h1 _ h1' hne1)
      (hA6 _ h1' K₁ h1 (Ne.symm hne1)) (hA6 _ h1'' K₁ h1 (Ne.symm hne2))
    obtain ⟨W, U, -, hW, hWc, -, hU1, hU2, hWU⟩ := lift_quot hp3 (by norm_num) hW' hT'2 hT'1 hWT
    have h1 := card_le_pow_glaTwoLocalRank hp3 hW hU1 hU2 hWU
    rw [hWc, hW'c, hrk] at h1
    norm_num at h1
  obtain ⟨J, hJ𝒞, hIJ⟩ := single_of_family hsup hI1 hall
  have hJ : GLAPComponent 3 X J := h𝒞 J hJ𝒞
  have hBJ : B ≤ Subgroup.normalizer (J : Set G) := B_inv_of_contains hJ hBX hI hIJ hBI
  have hEJ : E ≤ Subgroup.normalizer (J : Set G) := hEB.trans hBJ
  have hIE : I ≤ Subgroup.centralizer (E : Set G) := hICE.1
  have hlt : ¬ J ≤ I ⊔ GLAPPrimeCoreOf 3 J := by
    intro hcov
    have hJeq : I ⊔ GLAPPrimeCoreOf 3 J = J :=
      le_antisymm (sup_le hIJ (Subgroup.map_subtype_le _)) hcov
    have hJt : IsTypeWithCenter 3 J isA6 1 :=
      (isTypeWithCenter_congr (S3.nonempty_pQuot_of_cover hp3 hJ hIJ hJeq)).1 hIt
    have hconj : ∀ r ∈ R, B ≤ Subgroup.normalizer ((GLBConj r J : Subgroup G) : Set G) := by
      intro r hr
      have hrX : r ∈ X := hRD hr
      have hcomp : GLAPComponent 3 X (GLBConj r J) := by
        have h1 := glaPComponent_gLBConj hJ r
        rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hrX)] at h1
      by_contra hnB
      exact (h112 X B (GLBConj r J) hX hBX hB.1 hrankX hcomp hnB).1 (isTypeWithCenter_conj r hJt)
    have hEcent : ∀ e ∈ E, CentMod 3 J e := by
      intro e he
      have heI : I ≤ cx e := fun i hi =>
        Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 (hIE hi) e he).symm
      exact S3.centMod_of_cover_le hp3 hJ hIJ hJeq (hEJ he) (centMod_of_comm (p := 3) heI).1 (centMod_of_comm heI)
    obtain ⟨hRJ, hRc⟩ := pump_normalizes hEB hconj (hRE.symm ▸ le_rfl) hEcent
    obtain ⟨W, hWJE, hW, hWc⟩ := W_A6 ha6 hJ hJt hEe hEc hEcent
    have hN := le_normalizer_sup_core hp3 hJ hRD hRc hEX (hEB.trans hBR)
    have h1 := pump_contra hp3 (by norm_num) hRD hR2 hR1 hW (hWJE.trans hN)
    rw [hWc, hrk] at h1
    norm_num at h1
  have hxD : x ∉ D := x_not_mem_D hlb hx1 (hB.1.2 x hxB) (isKGroup_cx hc hx1) hL hLuniq hDe hDc
    (fun e he => hEdec e (hDE he)) hUa hIc hIJ hJ hlt
  have hIJE : GLAPComponent 3 (J ⊓ Subgroup.centralizer (E : Set G)) I :=
    glaPComponent_of_le hp3 hICE (le_inf hIJ hIE) inf_le_right
  have hT : T1430 J E := h1430 X E D J I hX hEX hEe hEc hDE hDc le_rfl hJ hEJ hIJE hIt hlt hrk.le
  exact ⟨D, J, hDE, hDe, hDc, hxD, hJ, hBJ, hIJ, hlt, hT⟩

theorem stageK (hc : S3Ctx G 3) (h183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4)
    (h112 : I112At G) (h106 : I106T1430At G) (h1431 : I1431At G) (hlb : LBalanceAt G 3)
    {B L D₀ I D J : Subgroup G} {x : G}
    (hB : GLAIsBmax 3 B) (hrk : GLATwoLocalRank 3 G = 4) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hL : GLAPComponent 3 (cx x) L) (hLuniq : ∀ J' : Subgroup G, GLAPComponent 3 (cx x) J' → J' = L)
    (hxL : x ∉ L) (hD₀ : D₀ ≤ B ⊓ L) (hD₀c : Nat.card D₀ = 3 ^ 2)
    (hI : GLAPComponent 3 (L ⊓ Subgroup.centralizer (D₀ : Set G)) I)
    (hUa : ∀ d ∈ D₀, d ≠ 1 → UniqA6 (L ⊓ cx d))
    (hDE : D ≤ D₀ ⊔ Subgroup.zpowers x) (hDe : IsElemAbelian 3 D) (hDc : Nat.card D = 3 ^ 2)
    (hxD : x ∉ D) (hJ : GLAPComponent 3 (Subgroup.centralizer (D : Set G)) J)
    (hBJ : B ≤ Subgroup.normalizer (J : Set G)) (hIJ : I ≤ J)
    (hT : T1430 J (D₀ ⊔ Subgroup.zpowers x)) :
    ∃ (a : G) (K : Subgroup G), a ∈ D ∧ a ≠ 1 ∧ GLAPComponent 3 (cx a) K ∧ SpA12Type K := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  set E : Subgroup G := D₀ ⊔ Subgroup.zpowers x with hEdef
  obtain ⟨hEB, hEe, hEc, hLE, hEdec⟩ := E_facts hB.1 hxB hL.1 hD₀ hD₀c hxL
  have hxE : x ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hLn : cx x ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_unique_glaPComponent hL hLuniq
  have hICE : GLAPComponent 3 (Subgroup.centralizer (E : Set G)) I := (I_comp_CE hLn hxE hDE hLE hI).1
  have hDB : D ≤ B := hDE.trans hEB
  have hDnc : ¬ IsCyclic D := S3.not_isCyclic_of_card hp3 hDe (by rw [hDc])
  obtain ⟨A', S, hA'D, hA'idx, hS2, hS1, hSA', hBS, hSD⟩ :=
    exists_inv_two hp3 (by norm_num) hc.charTwo hB hDB hDnc
  have hA'c : Nat.card A' = 3 := by rw [hDc] at hA'idx; omega
  obtain ⟨a, haA', ha1⟩ : ∃ a ∈ A', a ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one A' with h | h
    · rw [h, Subgroup.card_bot] at hA'c; norm_num at hA'c
    · exact h
  have haD : a ∈ D := hA'D haA'
  have haB : a ∈ B := hDB haD
  have ha3 : a ^ 3 = 1 := hDe.2 a haD
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hza : Subgroup.zpowers a = A' :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 haA') (by rw [Nat.card_zpowers, hao, hA'c])
  have hSa : S ≤ cx a := by
    have h := hSA'
    rw [← hza, S3.centralizer_zpowers a] at h
    exact h
  have hcxa : cx a = Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
    (S3.centralizer_zpowers a).symm
  obtain ⟨d, hdD, hda⟩ : ∃ d ∈ D, d ∉ Subgroup.zpowers a := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (h : D ≤ Subgroup.zpowers a)
    rw [Nat.card_zpowers, hao, hDc] at h1
    norm_num at h1
  have hdB : d ∈ B := hDB hdD
  have hCD : Subgroup.centralizer (D : Set G) = cx a ⊓ cx d :=
    centralizer_eq_inf hDe hDc haD ha1 hdD hda
  have hXa : CFSG.Open.IsKGroup ↥(cx a) := isKGroup_cx hc ha1
  have hDXa : D ≤ cx a := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hDe he haD)
  have hBXa : B ≤ cx a := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hB.1 he haB)
  have hEXa : E ≤ cx a := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hB.1 (hEB he) haB)
  have hCDa : Subgroup.centralizer (D : Set G) ≤ cx a :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 haD)
  have hJ' : GLAPComponent 3 (cx a ⊓ Subgroup.centralizer (D : Set G)) J := by
    rw [inf_eq_right.2 hCDa]; exact hJ
  have hrank := rank_cond hp3 hB (cx a)
  obtain ⟨𝒞, h𝒞, hsup, hstab, htr⟩ := h183 G (cx a) hXa 3 hp3 D hDXa hDe J hJ'
  have hYE : Subgroup.zpowers a ≤ D := (Subgroup.zpowers_le).2 haD
  have hYidx : Nat.card (Subgroup.zpowers a) * 3 = Nat.card D := by
    rw [Nat.card_zpowers, hao, hDc]; norm_num
  have hall : ∀ K₁ ∈ 𝒞, ∀ K₂ ∈ 𝒞, K₁ = K₂ := by
    intro K₁ h1 K₂ h2
    by_contra hne
    obtain ⟨hnB, hiso⟩ := diag_iso h112 hXa hcxa hBXa hB.1 hrank hDB hYE hYidx hJ h𝒞 hsup htr h1 h2 hne
    obtain ⟨iso'⟩ := pSimple_of_iso hp3 (h𝒞 K₁ h1) hiso
    exact (h112 (cx a) B K₁ hXa hBXa hB.1 hrank (h𝒞 K₁ h1) hnB).2.1 ((catalogIs_congr iso').1 hT.1)
  obtain ⟨K, hK𝒞, hJK⟩ := single_of_family hsup (glaPComponent_ne_bot' hJ) hall
  have hK : GLAPComponent 3 (cx a) K := h𝒞 K hK𝒞
  have hBK : B ≤ Subgroup.normalizer (K : Set G) := B_inv_of_contains hK hBXa hJ hJK hBJ
  have hlt : ¬ K ≤ J ⊔ GLAPPrimeCoreOf 3 K := by
    intro hcov
    have hKeq : J ⊔ GLAPPrimeCoreOf 3 K = K :=
      le_antisymm (sup_le hJK (Subgroup.map_subtype_le _)) hcov
    obtain ⟨e⟩ := S3.nonempty_pQuot_of_cover hp3 hK hJK hKeq
    obtain ⟨f⟩ := nonempty_pSimple_congr e
    have hKT : catalogIs (PSimple 3 K) isType1430 := (catalogIs_congr f).1 hT.1
    have hconj : ∀ s ∈ S, B ≤ Subgroup.normalizer ((GLBConj s K : Subgroup G) : Set G) := by
      intro s hs
      have hcomp : GLAPComponent 3 (cx a) (GLBConj s K) := by
        have h1 := glaPComponent_gLBConj hK s
        rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hSa hs))] at h1
      by_contra hnB
      exact (h112 (cx a) B (GLBConj s K) hXa hBXa hB.1 hrank hcomp hnB).2.1
        (catalogIs_pSimple_conj s hKT)
    have hDcent : ∀ d' ∈ D, CentMod 3 K d' := by
      intro d' hd'
      have hJd : J ≤ cx d' := hJ.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hd'))
      exact S3.centMod_of_cover_le hp3 hK hJK hKeq (hBK (hDB hd')) (centMod_of_comm (p := 3) hJd).1
        (centMod_of_comm hJd)
    obtain ⟨hSK, hSc⟩ := pump_normalizes hDB hconj (hSD.symm ▸ le_rfl) hDcent
    obtain ⟨W, hWJE, hW, hWc⟩ := W_1430 h106 hJ hT hDe hDc hDE hEe hJ.1 (hEB.trans hBJ)
    have hN := le_normalizer_sup_core hp3 hK hSa hSc hEXa (hEB.trans hBS)
    have hWKE : W ≤ K ⊔ E := hWJE.trans (sup_le_sup_right hJK _)
    have h1 := pump_contra hp3 (by norm_num) hSa hS2 hS1 hW (hWKE.trans hN)
    rw [hWc, hrk] at h1
    norm_num at h1
  obtain ⟨d₀, hd₀, i, hai⟩ := hEdec a (hDE haD)
  have hd₀1 : d₀ ≠ 1 := by
    intro h
    rw [h, one_mul] at hai
    apply hxD
    have hxo : orderOf x = 3 := orderOf_eq_prime (hB.1.2 x hxB) hx1
    have hzz : Subgroup.zpowers a = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 (hai ▸ Subgroup.npow_mem_zpowers x i))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hao, hxo])
    exact hYE (hzz ▸ Subgroup.mem_zpowers x)
  have hLa : L ⊓ cx a = L ⊓ cx d₀ := by rw [hai]; exact inf_cx_mul_pow hL.1 d₀ i
  have hD₀x : D₀ ≤ cx x := fun g hg => hL.1 (hD₀ hg).2
  have hD₀p : IsPGroup 3 D₀ :=
    isPGroup_of_isElemAbelian (CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hB.1
      (fun g hg => (hD₀ hg).1))
  have hax : a ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hB.1 haB hxB)
  have hD₀K : D₀ ≤ Subgroup.normalizer (K : Set G) := fun g hg => hBK (hD₀ hg).1
  have hCE : Subgroup.centralizer (E : Set G) = Subgroup.centralizer (D₀ : Set G) ⊓ cx x :=
    centralizer_sup_zpowers D₀ x
  have hI'' : GLAPComponent 3 ((K ⊓ cx x) ⊓ Subgroup.centralizer (D₀ : Set G)) I := by
    have hIE : I ≤ Subgroup.centralizer (D₀ : Set G) ⊓ cx x := hCE ▸ hICE.1
    refine glaPComponent_of_le hp3 hICE ?_ ?_
    · exact le_inf (le_inf (hIJ.trans hJK) (hIE.trans inf_le_right)) (hIE.trans inf_le_left)
    · rw [hCE]
      exact fun g hg => ⟨hg.2, hg.1.2⟩
  obtain ⟨Ia, hIa, hIat⟩ := Ka_comp hlb (isKGroup_cx hc hx1) hL hLuniq hD₀x hD₀p ha3 hax hLa
    (hUa d₀ hd₀ hd₀1) hK (hBK hxB) hD₀K hI''
  have hJKd : GLAPComponent 3 (K ⊓ cx d) J := by
    have hJd : J ≤ cx d := hJ.1.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hdD))
    refine glaPComponent_of_le hp3 hJ (le_inf hJK hJd) ?_
    rw [hCD]
    exact fun g hg => ⟨hK.1 hg.1, hg.2⟩
  have hTB : T1430 J B := ⟨hT.1, fun h => by
    obtain ⟨e, he, hne⟩ := hT.2 h
    exact ⟨e, hEB he, hne⟩⟩
  have hSpA := h1431 (cx a) B K J d x hXa hBXa hB.1 hrk.le hK hBK
    ⟨a, haB, ha1, centMod_of_comm hK.1⟩ hdB hJKd hTB hlt hxB ⟨Ia, hIa, hIat⟩
  exact ⟨a, K, haD, ha1, hK, hSpA⟩

theorem stageF (h112 : I112At G) (hk : KFactsAt G) (hon : ONFactsAt G) {B L K : Subgroup G} {x a : G}
    (hB : GLAIsBmax 3 B) (hrk : GLATwoLocalRank 3 G = 4) (hxB : x ∈ B)
    (hL : GLAPComponent 3 (cx x) L) (hLuniq : ∀ J' : Subgroup G, GLAPComponent 3 (cx x) J' → J' = L)
    (hLt : IsTypeWithCenter 3 L (sporIs .ONan) 1) (hxL : x ∉ L)
    (hBL : B ≤ (B ⊓ L) ⊔ Subgroup.zpowers x) (haB : a ∈ B) (ha1 : a ≠ 1)
    (hXa : CFSG.Open.IsKGroup ↥(cx a)) (hK : GLAPComponent 3 (cx a) K) (hKt : SpA12Type K) : False := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hLn : cx x ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_unique_glaPComponent hL hLuniq
  obtain ⟨hon1, hon2⟩ := hon (cx x) L hL hLt
  obtain ⟨H, hFH, hHL, hHe, hHc⟩ := hon1 (B ⊓ L) inf_le_right
    (isPGroup_of_isElemAbelian (CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hB.1 inf_le_left))
  obtain ⟨hAe, hAc, hBA, hAx, hAL, hxH⟩ := A_facts hB.1 hxB hL.1 hxL hBL hHL hHe hHc hFH
  set A : Subgroup G := H ⊔ Subgroup.zpowers x with hAdef
  obtain ⟨htrans, hcentH⟩ := hon2 H hHL hHe hHc
  have haA : a ∈ A := hBA haB
  have h3 : ∀ g ∈ Subgroup.normalizer (A : Set G), g ∈ cx x → (∃ k : ℕ, g ^ (3 ^ k) = 1) →
      g ∈ Subgroup.centralizer (A : Set G) := by
    intro g hgA hgx hg3
    have hgH : g ∈ Subgroup.normalizer (H : Set G) := by
      have h := mem_normalizer_inf hgA (hLn hgx)
      rwa [hAL] at h
    have hgcH := hcentH g (hLn hgx) hgH hg3
    refine mem_centralizer_sup hgcH ?_
    rw [S3.centralizer_zpowers x]
    exact hgx
  have hU : ∀ h ∈ H, h ≠ 1 → ∀ h' ∈ H, h' ≠ 1 → ∃ u ∈ Subgroup.normalizer (A : Set G),
      u ∈ cx x ∧ u ∈ Subgroup.normalizer (H : Set G) ∧ u * h * u⁻¹ = h' := by
    intro h hh h1 h' hh' h1'
    obtain ⟨n, hnL, hnH, hn⟩ := htrans h hh h1 h' hh' h1'
    have hnx : n ∈ cx x := hL.1 hnL
    have hnZ : n ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      apply Subgroup.centralizer_le_normalizer
      rw [S3.centralizer_zpowers x]
      exact hnx
    exact ⟨n, mem_normalizer_sup hnH hnZ, hnx, hnH, hn⟩
  obtain ⟨hk5, hk1, hk2, hk3, hk4⟩ := hk (cx a) K hK hKt
  have hcen := cen_rank_le hk hK hKt hrk.le
  have hAa : A ≤ cx a := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hAe hg haA)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    by_contra hnA
    have hrankA : ∀ W U : Subgroup G, W ≤ cx a → IsElemAbelian 3 W → U ≤ cx a → U ≠ ⊥ →
        IsPGroup 2 U → W ≤ Subgroup.normalizer (U : Set G) → Nat.card W ≤ Nat.card A := by
      intro W U _ hW _ hU1 hU2 hWU
      have h1 := card_le_pow_glaTwoLocalRank hp3 hW hU1 hU2 hWU
      rw [hrk] at h1
      rw [hAc]
      exact h1.trans (by norm_num)
    obtain ⟨-, -, hc4, -⟩ := h112 (cx a) A K hXa hAa hAe hrankA hK hnA
    obtain ⟨F, T, hFK, hFe, hFc, -⟩ := hk2 K le_rfl (sup_eq_left.2 (Subgroup.map_subtype_le _))
    have h1 := hc4 F hFK hFe
    rw [hFc] at h1
    norm_num at h1
  have haK : CentMod 3 K a := centMod_of_comm hK.1
  obtain ⟨hAK81, hAsplit⟩ := A_split hk hK hKt hAe hAc haA ha1 haK hAK hcen
  have hAeq : (A ⊓ K) ⊔ Subgroup.zpowers a = A :=
    le_antisymm (sup_le inf_le_left ((Subgroup.zpowers_le).2 haA)) hAsplit
  have hza : ∀ g ∈ cx a, g ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    intro g hg
    rw [S3.centralizer_zpowers a]
    exact hg
  obtain ⟨⟨n, hnK, hnN, hn3, hnC⟩, hQb⟩ := hk4 (A ⊓ K) inf_le_right
    (CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hAe inf_le_left) hAK81
  have hna : n ∈ cx a := hK.1 hnK
  have hnA : n ∈ Subgroup.normalizer (A : Set G) := by
    rw [← hAeq]
    exact mem_normalizer_sup hnN (Subgroup.centralizer_le_normalizer _ (hza n hna))
  have hnCA : n ∉ Subgroup.centralizer (A : Set G) := fun h =>
    hnC (Subgroup.centralizer_le (inf_le_left : A ⊓ K ≤ A) h)
  have h9 : ¬ 9 ∣ (Subgroup.centralizer (A : Set G)).relIndex
      (Subgroup.normalizer (A : Set G) ⊓ cx a) := by
    intro h9
    have hCN : Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (A : Set G) ⊓ cx a :=
      le_inf (Subgroup.centralizer_le_normalizer _)
        (Subgroup.centralizer_le (Set.singleton_subset_iff.2 haA))
    have hNC : Subgroup.normalizer (A : Set G) ⊓ cx a ≤
        Subgroup.normalizer ((Subgroup.centralizer (A : Set G) : Subgroup G) : Set G) :=
      inf_le_left.trans (normalizer_le_normalizer_centralizer A)
    obtain ⟨Q, hQN, hQ3, hQ9⟩ := exists_pSubgroup_relIndex hp3 hCN hNC (k := 2) (by norm_num; exact h9)
    have hQK : Q ≤ Subgroup.normalizer (K : Set G) :=
      hQN.trans (NA_le_NK hK hKt.2 hAe hAc hAK81)
    have hQAK : Q ≤ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := fun q hq =>
      mem_normalizer_inf (hQN hq).1 (hQK hq)
    have hb := hQb Q hQ3 hQK hQAK
    have heq : (Subgroup.centralizer (A : Set G)).relIndex Q =
        (Subgroup.centralizer ((A ⊓ K : Subgroup G) : Set G)).relIndex Q := by
      rw [← Subgroup.inf_relIndex_right (Subgroup.centralizer (A : Set G)),
        ← Subgroup.inf_relIndex_right (Subgroup.centralizer ((A ⊓ K : Subgroup G) : Set G))]
      congr 1
      ext g
      constructor
      · rintro ⟨hgA, hgQ⟩
        exact ⟨Subgroup.centralizer_le (inf_le_left : A ⊓ K ≤ A) hgA, hgQ⟩
      · rintro ⟨hgAK, hgQ⟩
        refine ⟨?_, hgQ⟩
        rw [← hAeq]
        exact mem_centralizer_sup hgAK (hza g (hQN hgQ).2)
    have hpos : (Subgroup.centralizer (A : Set G)).relIndex Q ≠ 0 := Subgroup.index_ne_zero_of_finite
    rw [heq] at hQ9 hpos
    obtain ⟨c, hc⟩ := hQ9
    rcases c with _ | c
    · exact hpos (by simpa using hc)
    · rw [hc] at hb
      norm_num at hb
      omega
  have hax : ∀ g ∈ Subgroup.normalizer (A : Set G), g * x * g⁻¹ ≠ a ∧ g * x⁻¹ * g⁻¹ ≠ a :=
    fun g _ => a_not_conj hk hLuniq hLt.1 hK hKt g
  exact fusion_contra hAe le_sup_left hHc hAc (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) hxH le_rfl
    h3 hU ⟨n, hnA, hn3, hnCA⟩ haA ha1 hax h9

theorem lemma84_of {p : ℕ} (hc : S8Ctx G p) (h1016 : I1016ONAt G) (h1425 : I1425At G)
    (h183 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input18_3_4) (h112 : I112At G)
    (ha6 : A6FactsAt G) (h1430 : I1430At G) (h106 : I106T1430At G) (h1431 : I1431At G)
    (hk : KFactsAt G) (hon : ONFactsAt G) (hlb : LBalanceAt G 3) {B L : Subgroup G} {x : G}
    (hB : GLAIsBmax p B) (hxB : x ∈ B) (hx1 : x ≠ 1) (hL : GLAPComponent p (cx x) L)
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hcyc : CycModSylow p L)
    (huniq : ∀ J : Subgroup G, GLAPComponent p (cx x) J → J = L)
    (hBL : B ≤ (B ⊓ L) ⊔ Subgroup.zpowers x)
    (hT : ∃ T : Subgroup G, T ≤ L ∧ IsPGroup 2 T ∧ B ≤ Subgroup.normalizer (T : Set G) ∧
      (⁅T, B⁆ : Subgroup G) = T ∧ ¬ T ≤ GLAPPrimeCoreOf p L) :
    ¬ catalogIs (PSimple p L) (sporIs .ONan) := by
  intro hON
  obtain ⟨hp3, hrk, hxL, hF27⟩ :=
    step1 h1016 hc.ctx.prime hc.ctx.odd hc.ctx.rank_ge hB hxB hL hBL hT hON
  subst hp3
  have hZ := center_trivial Nat.prime_three (hB.1.2 x hxB) hx1 hL hcyc hxL
  have hLt : IsTypeWithCenter 3 L (sporIs .ONan) 1 := ⟨hON, hZ⟩
  obtain ⟨D₀, hD₀F, hD₀c, ⟨I, hI, hIuniq, hIt, hIc⟩, hUa⟩ := h1425 (cx x) L hL hLt (B ⊓ L) inf_le_right
    (CFSG.LocalAnalysis.GLTheoremA.isElemAbelian_mono hB.1 inf_le_left) hF27
  have hD₀ : D₀ ≤ B ⊓ L := hD₀F
  obtain ⟨D, J, hDE, hDe, hDc, hxD, hJ, hBJ, hIJ, -, hTJ⟩ := stageJ hc.ctx h183 h112 ha6 h1430 hlb hB hrk
    hxB hx1 hL huniq hBN hxL hD₀ hD₀c hI hIuniq hIt hIc hUa
  obtain ⟨a, K, haD, ha1, hK, hKt⟩ := stageK hc.ctx h183 h112 h106 h1431 hlb hB hrk hxB hx1 hL huniq hxL
    hD₀ hD₀c hI hUa hDE hDe hDc hxD hJ hBJ hIJ hTJ
  have haB : a ∈ B := (E_facts hB.1 hxB hL.1 hD₀ hD₀c hxL).1 (hDE haD)
  exact stageF h112 hk hon hB hrk hxB hL huniq hLt hxL hBL haB ha1 (isKGroup_cx hc.ctx ha1) hK hKt

end S8.L84

end CFSG.LocalAnalysis.GLTheoremA
