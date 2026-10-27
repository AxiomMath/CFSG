module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.EightNineSplit
public import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseBound
import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseKey
import CFSG.HardMathSupport.Cooperstein.StructureLie.BotCaseRep
import CFSG.LocalAnalysis.AGLEmbedding.ResidualToolsAux
import CFSG.HardMathSupport.Cooperstein.StructureLie.Transvection

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding
open CFSG.HardMathSupport.Cooperstein.Coordinator
open scoped commutatorElement

@[expose] def GF2Thm1311Classical : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H L : Subgroup (MulAut V), FFHyp H L →
      IsClassicalTwoOrG2 (↥L ⧸ Subgroup.center ↥L) →
      ∀ A : Subgroup (MulAut V), A ≤ H → IsElemAbelian2 A → Nat.card A = 4 →
        Nat.card V ≤ 4 * Nat.card {v : V | ∀ a ∈ A, a v = v} → A ⊓ L ≠ ⊥

theorem isClassicalTwoOrG2_of_mulEquiv {Y₀ Y : Type} [Group Y₀] [Group Y] (e : Y₀ ≃* Y)
    (h : IsClassicalTwoOrG2 Y₀) : IsClassicalTwoOrG2 Y := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩)

section Offender

variable {G : Type} [Group G] [Finite G] {X S L : Subgroup G}

theorem exists_transvection_of_1311
    (h1311 : GF2Thm1311Classical)
    (hX : CFSG.Open.IsKGroup ↥X) (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hc : IsClassicalTwoOrG2 (↥(barM X L) ⧸ Subgroup.center ↥(barM X L)))
    (h0 : S ⊓ L ≤ pCoreOf 2 X) :
    ∃ a ∈ S, a ^ 2 = 1 ∧ a ∉ Subgroup.centralizer (blockV S L : Set G) ∧
      Nat.card ↥⁅blockV S L, Subgroup.zpowers a⁆ = 2 := by
  have hSL := le_normalizer_of_isWeakSBlock hX hA hL
  obtain ⟨A, hAmax, hAQ⟩ := exists_isMaxElemAbelian_not_le hA hL hSL
  have hAS : A ≤ S := hAmax.1
  have hA1 := not_le_centralizer_blockV_of_not_le hA hL hSL hAS hAQ
  have hV : IsElemAbelian 2 (blockV S L) :=
    CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))
  have hVS := blockV_le hA hL hSL
  have hVN : L ⊔ S ≤ Subgroup.normalizer (blockV S L : Set G) := sup_le_normalizer_blockV S L
  have hAn : A ≤ Subgroup.normalizer (blockV S L : Set G) := (hAS.trans le_sup_right).trans hVN
  obtain ⟨-, hbound⟩ := sstar_out_bound hX hA hL hc h0
  have hE2 := isElemAbelian2_autOn hV hAmax.2.1 hAn
  have hES : autOn A (blockV S L) ≤ autOn S (blockV S L) := autOn_le_autOn _ hAS
  have hE4 : Nat.card (autOn A (blockV S L)) ≤ 4 := hbound _ hES hE2.2
  have hE1 : autOn A (blockV S L) ≠ ⊥ := autOn_ne_bot_of_not_le_centralizer hAn hA1
  have hrel := card_autOn_eq_relIndex hAn
  have hfix := card_fixV_autOn_eq hV hAn
  have hoff := CFSG.Quasithin.card_le_relIndex_mul_card hV hVS hAmax
  have h24 : Nat.card (autOn A (blockV S L)) = 2 ∨ Nat.card (autOn A (blockV S L)) = 4 := by
    have hp : IsPGroup 2 (autOn A (blockV S L)) := fun g => ⟨1, Subtype.ext (by simpa using hE2.2 g g.2)⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
    have h1 : 1 < Nat.card (autOn A (blockV S L)) := Subgroup.one_lt_card_iff_ne_bot _ |>.mpr hE1
    rw [hn] at h1 hE4 ⊢
    rcases n with _ | _ | _ | n
    · simp at h1
    · left; norm_num
    · right; norm_num
    · exfalso
      have : 2 ^ 3 ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rcases h24 with h2 | h4
  ·
    obtain ⟨a, haA, hanc⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (blockV S L : Set G) := by
      by_contra h
      push Not at h
      exact hA1 h
    refine ⟨a, hAS haA, hAmax.2.1.2 a haA, hanc, ?_⟩
    have hsub : (blockV S L ⊓ Subgroup.centralizer (A : Set G) : Subgroup G) ≤
        blockV S L ⊓ Subgroup.centralizer ({a} : Set G) :=
      inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA))
    have hcard : Nat.card (blockV S L) ≤ 2 * Nat.card ↥(blockV S L ⊓
        Subgroup.centralizer ({a} : Set G)) := by
      refine hoff.trans ?_
      rw [← hrel, h2]
      exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hsub)
    have ha2 : a ^ 2 = 1 := hAmax.2.1.2 a haA
    have hCle : ∀ v ∈ blockV S L, a ^ 2 * v = v * a ^ 2 := by
      intro v _; rw [ha2]; simp
    have hns : ∃ v ∈ blockV S L, a * v ≠ v * a := by
      by_contra h
      push Not at h
      exact hanc (Subgroup.mem_centralizer_iff.mpr fun v hv => (h v hv).symm)
    have := hV.1
    exact card_commutator_zpowers_eq_two (blockV S L) a
      (fun v hv w hw => setLike_mul_comm hv hw)
      (fun v hv => (Subgroup.mem_normalizer_iff.mp (hVN (Subgroup.mem_sup_right (hAS haA))) v).mp hv)
      hCle hns hcard
  ·
    exfalso
    have hff := ffHyp_autOn hA hL hSL hX
    have hsq : ∀ v : ↥(blockV S L), v ^ 2 = 1 := fun v =>
      Subtype.ext (by simpa using hV.2 v v.2)
    have hineq : Nat.card ↥(blockV S L) ≤ 4 * Nat.card
        {v : ↥(blockV S L) | ∀ a ∈ autOn A (blockV S L), a v = v} := by
      refine hoff.trans ?_
      rw [← hrel, h4, ← hfix]
      exact le_of_eq rfl
    obtain ⟨e⟩ := nonempty_autOnCenterQuotientEquiv hA hL hSL
    have hcL := isClassicalTwoOrG2_of_mulEquiv e.symm hc
    have hne := @h1311 ↥(blockV S L) (blockVCommGroup S L) inferInstance hsq
      (autOn (L ⊔ S) (blockV S L)) (autOn L (blockV S L)) hff hcL (autOn A (blockV S L))
      (autOn_le_autOn _ (hAS.trans le_sup_right)) hE2 h4 hineq
    apply hne
    refine eq_bot_iff.mpr ?_
    rw [← autOn_inf_autOn_eq_bot hA hL hSL h0]
    exact inf_le_inf_right _ hES

end Offender

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_centralizer_of_le_normalizer {M L : Subgroup G}
    (hM : M ≤ Subgroup.normalizer (L : Set G)) :
    M ≤ Subgroup.normalizer ((Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  apply TransvIrr.le_normalizer_of_conj_mem
  intro g hg x hx
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro l hl
  have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L := TransvIrr.conj_mem_of_le_normalizer hM (M.inv_mem hg) hl
  have := hx _ hl'
  calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g⁻¹⁻¹) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * l * g⁻¹⁻¹)) * g⁻¹ := by rw [this]
    _ = g * x * g⁻¹ * l := by group

theorem eightNineBotCase_of_1311
    (h1311 : GF2Thm1311Classical) : EightNineBotCase := by
  intro G _ _ X S L hX hA hL hc hbot
  have hSL := Coordinator.le_normalizer_of_isWeakSBlock hX hA hL
  have h0 : S ⊓ L ≤ pCoreOf 2 X := by
    rintro x ⟨hxS, hxL⟩
    have hxX : x ∈ X := hA.twoRadical.1 hxS
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨x, hxX⟩ : ↥X) ∈ barM X (S ⊓ L) :=
      Subgroup.mem_map.mpr ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.mpr ⟨hxS, hxL⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact coe_mem_pCoreOf_two_of_mk_eq_one _ hmem
  obtain ⟨a, haS, ha2, hanc, hcard⟩ := exists_transvection_of_1311 h1311 hX hA hL hc h0
  have hMV := sup_le_normalizer_blockV S L
  have hMN : L ⊔ S ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hSL
  have hanL : a ∉ L ⊔ (L ⊔ S) ⊓ Subgroup.centralizer (blockV S L : Set G) := fun h =>
    hanc (inf_sup_centralizer_le hA hL hSL h0 haS h).2
  have hset := TransvIrr.setting_of_transvection hX hA hL haS hcard hanL
  set V := blockV S L with hV
  set M := L ⊔ S with hM
  set C := M ⊓ Subgroup.centralizer (V : Set G) with hC
  set M₀ := L ⊔ Subgroup.zpowers a ⊔ C with hM₀
  have haM : a ∈ M := Subgroup.mem_sup_right haS
  have hM₀M : M₀ ≤ M := sup_le (sup_le le_sup_left (Subgroup.zpowers_le.mpr haM)) inf_le_left
  have hM₀C : M₀ ⊓ Subgroup.centralizer (V : Set G) = C :=
    le_antisymm (fun x hx => ⟨hM₀M hx.1, hx.2⟩) (le_inf le_sup_right inf_le_right)
  have hLM₀ : L ≤ M₀ := le_sup_left.trans le_sup_left
  have hCN : M ≤ Subgroup.normalizer (C : Set G) := le_normalizer_inf_centralizer hMV
  obtain ⟨hSab, -⟩ := sstar_out_bound hX hA hL hc h0
  have hcomm : ∀ b ∈ S, b * a * b⁻¹ * a⁻¹ ∈ C := by
    intro b hb
    have hbM : b ∈ M := Subgroup.mem_sup_right hb
    let b' : ↥M := ⟨b, hbM⟩
    let a' : ↥M := ⟨a, haM⟩
    have h1 := hSab _ ((Setup.mem_autOn_iff_rho hMV le_sup_right).mpr ⟨b', hb, rfl⟩) _
      ((Setup.mem_autOn_iff_rho hMV le_sup_right).mpr ⟨a', haS, rfl⟩)
    have h2 : Setup.rho V M hMV (b' * a' * b'⁻¹ * a'⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      calc _ = (Setup.rho V M hMV a' * Setup.rho V M hMV b') * (Setup.rho V M hMV b')⁻¹ *
            (Setup.rho V M hMV a')⁻¹ := by rw [h1]
        _ = 1 := by group
    exact ⟨(b' * a' * b'⁻¹ * a'⁻¹).2, (Setup.rho_eq_one_iff hMV _).mp h2⟩
  have hconj : ∀ b ∈ S, ∀ m ∈ M₀, b * m * b⁻¹ ∈ M₀ := by
    intro b hb
    have hbM : b ∈ M := Subgroup.mem_sup_right hb
    have hle : M₀ ≤ M₀.comap (MulAut.conj b).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro l hl
        exact hLM₀ ((Subgroup.mem_normalizer_iff.mp (hSL hb) l).mp hl)
      · rw [Subgroup.zpowers_le]
        show b * a * b⁻¹ ∈ M₀
        have e : b * a * b⁻¹ = (b * a * b⁻¹ * a⁻¹) * a := by group
        rw [e]
        exact M₀.mul_mem ((show C ≤ M₀ from le_sup_right) (hcomm b hb))
          (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))
      · intro c hc'
        exact (show C ≤ M₀ from le_sup_right) ((Subgroup.mem_normalizer_iff.mp (hCN hbM) c).mp hc')
    intro m hm
    exact hle hm
  have hnormb : ∀ b ∈ S, b ∈ Subgroup.normalizer (M₀ : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨fun hm => hconj b hb m hm, fun hm => ?_⟩
    have := hconj b⁻¹ (S.inv_mem hb) _ hm
    have e : b⁻¹ * (b * m * b⁻¹) * b⁻¹⁻¹ = m := by group
    rwa [e] at this
  have hV2 : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := (CFSG.AGLEmbedding.isElemAbelian_omegaOneCenterOf (pCoreOf 2 (L ⊔ S))).2 v hv
    simpa [pow_two] using this
  have hMU : M ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g hg =>
    TransvIrr.mem_normalizer_commutator (hMV hg) (hMN hg)
  have hMCl : M ≤ Subgroup.normalizer ((⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :
      Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hMU hg, le_normalizer_centralizer_of_le_normalizer hMN hg⟩
  have hmain : ∀ b ∈ S, b ∈ M₀ := fun b hb =>
    inf_normalizer_le_of_key keyNormalizer hset hV2 (by rw [hM₀C]; exact hanL)
      (fun T hTM hMT hCT x hx hxn => TransvIrr.normal_gen' hX hA hL hLM₀ hM₀M hTM hMT hCT hx hxn)
      hM₀M hMU hMCl
      (fun T hTM hMT hCT x hx hxn => TransvIrr.normal_gen' hX hA hL (M' := M) le_sup_left le_rfl hTM hMT hCT hx hxn)
      le_sup_right (Subgroup.mem_sup_right hb) (hnormb b hb)
  have haN : Subgroup.zpowers a ≤ Subgroup.normalizer ((L ⊔ C : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _
      ⟨(hMN haM), hCN haM⟩
  refine ⟨a, haS, ?_, ?_, hanL⟩
  · intro b hb
    have hbM₀ := hmain b hb
    have hb' : b ∈ ((Subgroup.zpowers a ⊔ (L ⊔ C) : Subgroup G) : Set G) := by
      have : M₀ = Subgroup.zpowers a ⊔ (L ⊔ C) := by
        rw [hM₀]; ac_rfl
      rw [← this]; exact hbM₀
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ haN] at hb'
    obtain ⟨z, hz, n, hn, rfl⟩ := hb'
    have hzS : z ∈ S := Subgroup.zpowers_le.mpr haS hz
    have hnS : n ∈ S := by
      have := S.mul_mem (S.inv_mem hzS) hb
      simpa using this
    exact Subgroup.mul_mem_sup hz (inf_sup_centralizer_le hA hL hSL h0 hnS hn)
  · rw [ha2]; exact C.one_mem

end Main

end CFSG.HardMathSupport.Cooperstein.StructureLie
