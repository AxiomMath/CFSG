module

public import CFSG.LocalAnalysis.GLTheoremA.Lemma45
public import CFSG.LocalAnalysis.GLTheoremA.ExcClubList

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem sup_glaPPrimeCoreOf_eq_of_card_eq {p : ℕ} (hp : p.Prime) {I K : Subgroup G} (hIK : I ≤ K)
    (h : Nat.card (PQuot p I) = Nat.card (PQuot p K)) : I ⊔ GLAPPrimeCoreOf p K = K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set ψ : ↥I →* PQuot p K :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hIK) with hψ
  have hcop : Nat.Coprime p (Nat.card ψ.ker) := by
    have hle : ψ.ker.map (Subgroup.inclusion hIK) ≤ GLAPPrimeCore p ↥K := by
      rintro _ ⟨y, hy, rfl⟩
      have : ψ y = 1 := hy
      rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    have hcard : Nat.card (ψ.ker.map (Subgroup.inclusion hIK)) = Nat.card ψ.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hIK)
    rw [← hcard]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      CFSG.pPrimeCore_coprime_card
  have hker : ψ.ker ≤ GLAPPrimeCore p ↥I := le_sSup ⟨inferInstance, hcop⟩
  have h1 : Nat.card (PQuot p I) ≤ Nat.card (↥I ⧸ ψ.ker) := by
    have hd := Subgroup.index_dvd_of_le hker
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) hd
  have h2 : Nat.card (↥I ⧸ ψ.ker) = Nat.card ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
  have hrange : ψ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h3 : Nat.card ψ.range ≤ Nat.card (PQuot p K) := Subgroup.card_le_card_group _
    omega
  refine le_antisymm (sup_le hIK (Subgroup.map_subtype_le _)) fun k hk => ?_
  obtain ⟨i, hi⟩ := hrange ▸ Subgroup.mem_top (QuotientGroup.mk' (GLAPPrimeCore p ↥K) ⟨k, hk⟩)
  rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hi
  have hmem : (i : G)⁻¹ * k ∈ GLAPPrimeCoreOf p K := ⟨_, hi, rfl⟩
  have e : k = (i : G) * ((i : G)⁻¹ * k) := by group
  rw [e]
  exact Subgroup.mul_mem_sup i.2 hmem

theorem centMod_of_sup_eq {p : ℕ} {I K : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hIx : I ≤ Subgroup.centralizer ({x} : Set G))
    (hIK : I ≤ K) (hsup : I ⊔ GLAPPrimeCoreOf p K = K) : CentMod p K x := by
  rw [centMod_iff]
  refine ⟨hxN, fun k hk => ?_⟩
  have hON : x ∈ Subgroup.normalizer (GLAPPrimeCoreOf p K : Set G) :=
    normalizer_le_normalizer_glaPPrimeCoreOf p K hxN
  have hk' : k ∈ (I ⊔ GLAPPrimeCoreOf p K : Subgroup G) := hsup.symm ▸ hk
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right I _
    (hIK.trans (le_normalizer_glaPPrimeCoreOf p K))] at hk'
  obtain ⟨i, hi, o, ho, rfl⟩ := Set.mem_mul.mp hk'
  have hix : i * x = x * i := Subgroup.mem_centralizer_singleton_iff.1 (hIx hi)
  have hox : x * o⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p K :=
    (Subgroup.mem_normalizer_iff.1 hON o⁻¹).1 (Subgroup.inv_mem _ ho)
  have hiO : i * (o * (x * o⁻¹ * x⁻¹)) * i⁻¹ ∈ GLAPPrimeCoreOf p K :=
    (Subgroup.mem_normalizer_iff.1 ((hIK.trans (le_normalizer_glaPPrimeCoreOf p K)) hi) _).1
      (Subgroup.mul_mem _ ho hox)
  have e : ⁅i * o, x⁆ = i * (o * (x * o⁻¹ * x⁻¹)) * i⁻¹ := by
    rw [commutatorElement_def]
    calc i * o * x * (i * o)⁻¹ * x⁻¹ = i * (o * x * o⁻¹ * x⁻¹) * (x * i⁻¹ * x⁻¹) := by group
      _ = i * (o * x * o⁻¹ * x⁻¹) * i⁻¹ := by
        rw [show x * i⁻¹ * x⁻¹ = i⁻¹ by
          rw [show x * i⁻¹ = i⁻¹ * x by
            rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hix, inv_mul_cancel_left]]
          group]
      _ = i * (o * (x * o⁻¹ * x⁻¹)) * i⁻¹ := by group
  rw [e]
  exact hiO

theorem pumpRel_step {p : ℕ} (hp : p.Prime) (h183 : Input18_3_4) (hKP : CFSG.Open.IsKProper G)
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a)
    (h1131 : I1131At G p) (h1122 : I1122IsoAt G p) {t t' : Triple G} (hrel : PumpRel p t t') :
    Nat.card (PQuot p t.2.2) ≤ Nat.card (PQuot p t'.2.2) ∧
    (CentMod p t'.2.2 t.2.1 ↔ Nat.card (PQuot p t.2.2) = Nat.card (PQuot p t'.2.2)) ∧
    (CentMod p t'.2.2 t.2.1 → Nonempty (PQuot p t.2.2 ≃* PQuot p t'.2.2) ∧
      closureIn (GLAPLayer p (t.2.2 ⊓ Subgroup.centralizer ({t'.2.1} : Set G)))
        (GLAPLayer p (Subgroup.centralizer ({t'.2.1} : Set G))) = t'.2.2) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨-, hx, hL⟩, ⟨hB', hx', hL'c⟩, hxB', -, hx'B', hx'L, hL'⟩ := hrel
  set L := t.2.2
  set L' := t'.2.2
  set x := t.2.1
  set x' := t'.2.1
  set B' := t'.1
  set Cx := Subgroup.centralizer ({x} : Set G)
  set Cx' := Subgroup.centralizer ({x'} : Set G)
  have hB'Cx' : B' ≤ Cx' := isElemAbelian_le_centralizer hB'.1 hx'B'
  have hx'p : IsPGroup p (Subgroup.zpowers x') := isPGroup_zpowers_of_mem hB'.1 hx'B'
  obtain ⟨hIc, -, -, -, -, ⟨eIL⟩⟩ := glaPLayer_inf_centralizer hp hL hx'p hx'L
  set I := GLAPLayer p (L ⊓ Cx')
  have hIL : I ≤ L := hIc.1.trans inf_le_left
  have hICx : I ≤ Cx := hIL.trans hL.1
  have hCzx : Subgroup.centralizer (Subgroup.zpowers x : Set G) = Cx := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hI2 : GLAPComponent p (Cx' ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) I := by
    rw [hCzx, inf_comm]
    exact glaPComponent_of_isSubnormal' hp (hL.2.1.inf Cx') hIc
  have hKx' : CFSG.Open.IsKGroup ↥Cx' :=
    isKGroup_of_isKProper hKP (centralizer_ne_top_of_ne_one hsimple hnonab hx'.2.1)
  have hxCx' : Subgroup.zpowers x ≤ Cx' := Subgroup.zpowers_le.2 (hB'Cx' hxB')
  obtain ⟨𝒞, h𝒞c, h𝒞sup, -, h𝒞tr⟩ := h183 G Cx' hKx' p hp (Subgroup.zpowers x) hxCx'
    (isElemAbelian_zpowers_of_mem hB'.1 hxB') I hI2
  set J := closureIn I (GLAPLayer p Cx')
  have hJ : J = ⨆ K ∈ 𝒞, K := (closureIn_eq_iSup_gLBConj I _).trans h𝒞sup.symm
  have hKJ : ∀ K ∈ 𝒞, K ≤ J := fun K hK => hJ ▸ le_biSup (fun K => K) hK
  have hJCx' : J ≤ Cx' := hJ ▸ iSup₂_le fun K hK => (h𝒞c K hK).1
  have hIJ : I ≤ J := le_closureIn_self I _
  have h𝒞J : ∀ K ∈ 𝒞, GLAPComponent p J K := fun K hK =>
    glaPComponent_of_le hp (h𝒞c K hK) (hKJ K hK) hJCx'
  have hL'𝒞 : L' ∈ 𝒞 := by
    refine mem_of_le_sSup_glaPComponent hp 𝒞 h𝒞J hL' ?_
    rw [sSup_eq_iSup, ← hJ]
    exact hL'.1
  have hPI : Nat.card (PQuot p L) = Nat.card (PQuot p I) := Nat.card_congr eIL.symm.toEquiv
  by_cases hxN : x ∈ Subgroup.normalizer (L' : Set G)
  ·
    have huniq : ∀ K ∈ 𝒞, K = L' := fun K hK => by
      obtain ⟨e, he, hee⟩ := h𝒞tr L' hL'𝒞 K hK
      have heN : e ∈ Subgroup.normalizer (L' : Set G) := Subgroup.zpowers_le.2 hxN he
      rw [← hee, mem_normalizer_iff_gLBConj_eq.1 heN]
    have hJL' : J = L' := by
      rw [hJ]
      exact le_antisymm (iSup₂_le fun K hK => (huniq K hK).le) (le_biSup (fun K => K) hL'𝒞)
    have hIL' : I ≤ L' := hJL' ▸ hIJ
    have hIL'x : GLAPComponent p (L' ⊓ Cx) I := by
      refine glaPComponent_of_le hp hI2 (le_inf hIL' hICx) ?_
      rw [hCzx]
      exact inf_le_inf_right _ hL'c.1
    have hcov : CentMod p L' x ↔ I ⊔ GLAPPrimeCoreOf p L' = L' := by
      constructor
      · intro hcm
        obtain ⟨-, hJall, -, -, hJsup, -⟩ := glaPLayer_inf_centralizer hp hL'c
          (isPGroup_zpowers_of_mem hB'.1 hxB') hcm
        rw [hJall I hIL'x]
        exact hJsup
      · exact fun h => centMod_of_sup_eq hxN
          (hICx.trans le_rfl) hIL' h
    have hcard : I ⊔ GLAPPrimeCoreOf p L' = L' ↔
        Nat.card (PQuot p I) = Nat.card (PQuot p L') := by
      constructor
      · intro h
        obtain ⟨-, ⟨e⟩⟩ := cover_facts hp hIL' h
        exact Nat.card_congr e.toEquiv
      · exact sup_glaPPrimeCoreOf_eq_of_card_eq hp hIL'
    have hle : Nat.card (PQuot p I) ≤ Nat.card (PQuot p L') :=
      card_pQuot_le_of_cover hp le_rfl (sup_eq_left.2 (Subgroup.map_subtype_le _)) hIL'
    refine ⟨le_of_eq_of_le hPI hle, ?_, fun hcm => ?_⟩
    · rw [hcov, hcard, hPI]
    · obtain ⟨-, ⟨eIL'⟩⟩ := cover_facts hp hIL' (hcov.1 hcm)
      exact ⟨⟨eIL.symm.trans eIL'⟩, hJL'⟩
  ·
    have hncm : ¬ CentMod p L' x := fun h => hxN h.1
    have hExc := h1131 B' x' L' hB' hx' hL'c fun h => hxN (h hxB')
    have hZ : Nat.card (Subgroup.center (PQuot p L')) = p := card_center_of_isExcType hExc
    have hJcl : J ≤ closureIn L' B' := by
      rw [hJ]
      refine iSup₂_le fun K hK => ?_
      obtain ⟨e, he, rfl⟩ := h𝒞tr L' hL'𝒞 K hK
      rw [closureIn_eq_iSup_gLBConj]
      exact le_biSup (fun b => GLBConj b L') (Subgroup.zpowers_le.2 hxB' he)
    have hclN : closureIn L' B' ≤ Subgroup.normalizer (J : Set G) := by
      rw [closureIn_eq_iSup_gLBConj]
      refine iSup₂_le fun b hb => ?_
      have hbC : GLAPComponent p Cx' (GLBConj b L') := by
        have := glaPComponent_gLBConj hL'c b
        rwa [mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer (hB'Cx' hb))] at this
      intro k hk
      rw [hJ, ← sSup_eq_iSup]
      refine mem_normalizer_sSup fun K hK => ?_
      by_cases hKb : K = GLBConj b L'
      · rw [hKb]
        exact Subgroup.le_normalizer hk
      · exact CFSG.HardMathSupport.Solomon.LocalBalance.mem_normalizer_of_ne hp (h𝒞c K hK) hbC
          hKb hk
    have hIJx : GLAPComponent p (J ⊓ Cx) I := by
      refine glaPComponent_of_le hp hI2 (le_inf hIJ hICx) ?_
      rw [hCzx]
      exact inf_le_inf_right _ hJCx'
    have hJxle : J ⊓ Cx ≤ closureIn L' B' ⊓ Cx := inf_le_inf_right _ hJcl
    have hsn : IsSubnormal (J ⊓ Cx) (closureIn L' B' ⊓ Cx) := by
      refine IsSubnormal.step hJxle ((Subgroup.normal_subgroupOf_iff_le_normalizer hJxle).2 ?_)
        (IsSubnormal.refl _)
      intro g hg
      have h1 : GLBConj g J = J := mem_normalizer_iff_gLBConj_eq.1 (hclN hg.1)
      have h2 : GLBConj g Cx = Cx := mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg.2)
      rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, h1, h2]
    have hIdiag : GLAPComponent p (closureIn L' B' ⊓ Cx) I :=
      glaPComponent_of_isSubnormal' hp hsn hIJx
    obtain ⟨e⟩ := h1122 B' x' L' x hB' hx' hL'c hxB' hxN I hIdiag
    have hcardS : Nat.card (PQuot p L') =
        Nat.card (PSimple p L') * Nat.card (Subgroup.center (PQuot p L')) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hlt : Nat.card (PQuot p I) < Nat.card (PQuot p L') := by
      rw [Nat.card_congr e.toEquiv, hcardS, hZ]
      exact lt_mul_of_one_lt_right Nat.card_pos hp.one_lt
    refine ⟨(lt_of_eq_of_lt hPI hlt).le, ⟨fun h => absurd h hncm, fun h => ?_⟩,
      fun h => absurd h hncm⟩
    exact absurd (hPI.symm.trans h) hlt.ne

end CFSG.LocalAnalysis.GLTheoremA
