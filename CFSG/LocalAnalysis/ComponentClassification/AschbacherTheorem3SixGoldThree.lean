module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixGoldTwo
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open
open scoped Pointwise commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem le_normalizer_component {Y : Type} [Group Y] [Finite Y] {Gb Zb Pb Tb : Subgroup Y}
    (hlay : CFSG.layer Gb = ⊤) (hcen : Subgroup.center Gb = ⊥) (hO : CFSG.oddCore Gb = ⊥)
    (hPb : IsSylowOf 2 Pb Gb) (hZ : omegaOne Pb ≤ Zb)
    (hTN : Tb ≤ Subgroup.normalizer (Gb : Set Y))
    (hTZ : ∀ t ∈ Tb, ∀ z ∈ Zb, t * z = z * t) {K : Subgroup Gb} (hK : IsComponentOf K ⊤) :
    Tb ≤ Subgroup.normalizer ((K.map Gb.subtype : Subgroup Y) : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : CFSG.IsComponent K := (CFSG.isComponent_iff_open K).mpr hK
  have hKn : K.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hlay hK'
  obtain ⟨Q, hQ⟩ := hPb
  have hQtop : IsSylowOf 2 (Q : Subgroup Gb) ⊤ := by
    rw [isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, Q.isPGroup', Q.not_dvd_index⟩
  have hQK : IsSylowOf 2 ((Q : Subgroup Gb) ⊓ K) K :=
    hQtop.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  have hQKne : (Q : Subgroup Gb) ⊓ K ≠ ⊥ := by
    intro hbot
    have hodd : Odd (Nat.card K) := by
      have h1 := (isSylowOf_iff.mp hQK).2.2
      rw [hbot, Subgroup.relIndex_bot_left] at h1
      exact Nat.not_even_iff_odd.mp fun h => h1 (even_iff_two_dvd.mp h)
    have hle : K ≤ CFSG.oddCore Gb := by
      unfold CFSG.oddCore
      exact le_sSup ⟨hKn, hodd⟩
    rw [hO, le_bot_iff] at hle
    have := CFSG.LocalCores.isQuasisimple_nontrivial hK'.1
    rw [hle] at this
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) this
  have hQK2 : IsPGroup 2 ((Q : Subgroup Gb) ⊓ K : Subgroup Gb) := Q.isPGroup'.to_le inf_le_left
  have hdvd : 2 ∣ Nat.card ((Q : Subgroup Gb) ⊓ K : Subgroup Gb) := by
    rcases hQK2.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hQKne
    · exact h1
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hzK : (z : Gb) ∈ K := z.2.2
  have hzQ : (z : Gb) ∈ (Q : Subgroup Gb) := z.2.1
  have hzo : orderOf ((z : Gb) : Y) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hzZ : ((z : Gb) : Y) ∈ Zb := by
    apply hZ
    refine mem_omegaOne ?_ (by have h := pow_orderOf_eq_one ((z : Gb) : Y); rwa [hzo] at h)
    rw [← hQ]
    exact Subgroup.mem_map_of_mem _ hzQ
  have hz1 : ((z : Gb) : Y) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzo
    omega
  have hmain : ∀ s ∈ Tb, ∀ y ∈ K.map Gb.subtype, s * y * s⁻¹ ∈ K.map Gb.subtype := by
    intro s hs y hy
    set φ := Gb.normalizerMonoidHom ⟨s, hTN hs⟩ with hφ
    have hφapp : ∀ x : Gb, ((φ x : Gb) : Y) = s * x * s⁻¹ := fun x => rfl
    have hK'c : CFSG.IsComponent (K.map φ.toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv φ hK'
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    rcases CFSG.LocalCores.distinct_components_commute hK' hK'c with heq | hcomm
    · have hφk : φ k ∈ K.map φ.toMonoidHom := Subgroup.mem_map_of_mem _ hk
      rw [← heq] at hφk
      have : s * Gb.subtype k * s⁻¹ = ((φ k : Gb) : Y) := (hφapp k).symm
      rw [this]
      exact Subgroup.mem_map_of_mem _ hφk
    · exfalso
      have hφz : φ (z : Gb) = z := Subtype.ext (by
        rw [hφapp]
        rw [hTZ s hs _ hzZ, mul_inv_cancel_right])
      have hzK' : (z : Gb) ∈ K.map φ.toMonoidHom := by
        rw [← hφz]
        exact Subgroup.mem_map_of_mem _ hzK
      have hzc : (z : Gb) ∈ (Subgroup.center K).map K.subtype := by
        rw [CFSG.LocalCores.mem_map_center_iff]
        refine ⟨hzK, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
        have h1 : ⁅x, (z : Gb)⁆ ∈ ⁅K, K.map φ.toMonoidHom⁆ :=
          Subgroup.commutator_mem_commutator hx hzK'
        rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
        exact h1
      have hzC := CFSG.LocalCores.center_component_le_centralizer_layer hK' hzc
      rw [hlay, Subgroup.coe_top, Subgroup.centralizer_univ, hcen, Subgroup.mem_bot] at hzC
      exact hz1 (by rw [hzC]; rfl)
  intro t ht
  exact mem_normalizer_of_conj_le (hmain t ht) (by simpa using hmain t⁻¹ (Tb.inv_mem ht))

omit [Finite X] in
theorem isSimpleGroup_of_center_eq_bot {Q : Type*} [Group Q] (hc : Subgroup.center Q = ⊥)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) : IsSimpleGroup Q :=
  ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.isSimpleGroup

omit [Finite X] in
theorem mem_normalizer_omegaOne {P : Subgroup X} {s : X}
    (hs : s ∈ Subgroup.normalizer (P : Set X)) : s ∈ Subgroup.normalizer (omegaOne P : Set X) := by
  rw [← rightConjugate_eq_self_iff, rightConjugate_omegaOne,
    (rightConjugate_eq_self_iff P s).mpr hs]

namespace Conf46

variable {G T S Q H : Subgroup X} {g : X}

theorem goldschmidt_two (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    (hG : CFSG.Goldschmidt.TopStatement)
    (hMG : Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) = G)
    {C : Subgroup X} [C.Normal] (hC : C = pCoreOf 2 G) :
    CFSG.oddCore (G.map (QuotientGroup.mk' C)) = ⊥ ∧
    CFSG.layer (G.map (QuotientGroup.mk' C)) = ⊤ ∧
    Subgroup.center (G.map (QuotientGroup.mk' C)) = ⊥ ∧
    (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)).map (QuotientGroup.mk' C) =
      omegaOne (S.map (QuotientGroup.mk' C) ⊓ G.map (QuotientGroup.mk' C)) ∧
    ∀ K : Subgroup (G.map (QuotientGroup.mk' C)), IsComponentOf K ⊤ →
      goldschmidtSimpleType (K ⧸ Subgroup.center K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hcen, hZeq, -⟩ := c.goldschmidt_one htop hO IH hnn hG hMG
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set π := QuotientGroup.mk' C with hπ
  set Gb := G.map π with hGb
  set Zb := Z₁.map π with hZb
  set Sb := S.map π with hSb
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  have hCG : C ≤ G := hC ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 G
  have hC2 : IsPGroup 2 C := hC ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hCZ : C ≤ Z₁ := by
    rw [hC, hZeq]
    exact le_sup_left
  have hCS : C ≤ S := hCZ.trans ((omegaOne_le _).trans (inf_le_left.trans c.W_le_S))
  have hObar : CFSG.oddCore Gb = ⊥ := oddCore_map_eq_bot hGn hCG hC2 (hC ▸ hcen) hO
  have hPbar : CFSG.Open.pCore 2 Gb = ⊥ := pCore_map_eq_bot hC hGn
  have hSX : IsSylowOf 2 S ⊤ := htop ▸ c.sylowFrame.sylow
  have hSbX : IsSylowOf 2 Sb ⊤ := by
    have h1 := IsSylowOf.map hSX π
    rwa [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective C)] at h1
  obtain ⟨-, hSb2, hidx⟩ := isSylowOf_iff.mp hSbX
  rw [Subgroup.relIndex_top_right] at hidx
  set SY : Sylow 2 (X ⧸ C) := hSb2.toSylow hidx with hSYdef
  have hSYc : (SY : Subgroup (X ⧸ C)) = Sb := IsPGroup.toSylow_coe hSb2 hidx
  have hZab : IsMulCommutative Z₁ :=
    isMulCommutative_of_le ((omegaOne_le _).trans inf_le_left) c.isMulCommutative_W
  have hZbab : IsMulCommutative Zb := by
    have := hZab
    exact inferInstance
  have hZS : Z₁ ≤ S := (omegaOne_le _).trans (inf_le_left.trans c.W_le_S)
  have hZbS : Zb ≤ (SY : Subgroup (X ⧸ C)) := hSYc ▸ Subgroup.map_mono hZS
  have hcl : ∀ a ∈ Zb, ∀ x : X ⧸ C, x⁻¹ * a * x ∈ (SY : Subgroup (X ⧸ C)) →
      x⁻¹ * a * x ∈ Zb := by
    rintro _ ⟨a, ha, rfl⟩ x hx
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective C x
    rw [hSYc] at hx
    have h1 : π (y⁻¹ * a * y) ∈ Sb := by
      rw [map_mul, map_mul, map_inv]
      exact hx
    have h2 : y⁻¹ * a * y ∈ S := by
      have h3 := mk_mem_map_iff.mp h1
      rwa [sup_eq_left.mpr hCS] at h3
    have h4 := c.stronglyClosed_omegaOne_top htop IH hnn ha h2
    have h5 : π (y⁻¹ * a * y) ∈ Zb := Subgroup.mem_map_of_mem π h4
    rwa [map_mul, map_mul, map_inv] at h5
  have hMb : Subgroup.normalClosure (Zb : Set (X ⧸ C)) = Gb := by
    rw [hZb, Subgroup.coe_map, ← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective C),
      hMG]
  obtain ⟨ha, hb, hcomp⟩ := goldschmidt_subgroup hG SY hZbS hZbab hcl hMb hObar
  rw [hSYc] at hb
  rw [hPbar, bot_sup_eq] at ha hb
  have hlay : CFSG.layer Gb = ⊤ := by rw [← goldschmidtLayer_eq_layer]; exact ha
  refine ⟨hObar, hlay, center_eq_bot_of_cores hObar hPbar, ?_, hcomp⟩
  have hZbG : Zb ≤ Gb := Subgroup.map_mono ((omegaOne_le _).trans inf_le_right)
  have h1 := congrArg (Subgroup.map Gb.subtype) hb
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZbG, MonoidHom.map_closure] at h1
  rw [h1, omegaOne]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨⟨hyS, -⟩, hy2⟩, rfl⟩
    exact ⟨⟨Subgroup.mem_subgroupOf.mp hyS, y.2⟩, by simpa using congrArg Subtype.val hy2⟩
  · rintro ⟨⟨hxS, hxG⟩, hx2⟩
    refine ⟨⟨x, hxG⟩, ⟨⟨Subgroup.mem_subgroupOf.mpr hxS, ?_⟩, ?_⟩, rfl⟩
    · rw [ha]; exact Subgroup.mem_top _
    · exact Subtype.ext (by simpa using hx2)

theorem simple_bar (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    (hG : CFSG.Goldschmidt.TopStatement)
    (hMG : Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) = G)
    {C : Subgroup X} [C.Normal] (hC : C = pCoreOf 2 G) :
    IsSimpleGroup (G.map (QuotientGroup.mk' C)) ∧
    goldschmidtSimpleType
      (G.map (QuotientGroup.mk' C) ⧸ Subgroup.center (G.map (QuotientGroup.mk' C))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hObar, hlay, hcenb, hZbeq, hcomp⟩ := c.goldschmidt_two htop hO IH hnn hG hMG hC
  obtain ⟨-, hperf, hcen, -, -⟩ := c.goldschmidt_one htop hO IH hnn hG hMG
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set π := QuotientGroup.mk' C with hπ
  set Gb := G.map π with hGb
  set Tb := T.map π with hTb
  set Zb := Z₁.map π with hZbdef
  set Sb := S.map π with hSb
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective C
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  have hGbn : Gb.Normal := hGn.map π hsurj
  have hSX : IsSylowOf 2 S ⊤ := htop ▸ c.sylowFrame.sylow
  have hSbX : IsSylowOf 2 Sb ⊤ := by
    have h1 := IsSylowOf.map hSX π
    rwa [Subgroup.map_top_of_surjective _ hsurj] at h1
  have hPb : IsSylowOf 2 (Sb ⊓ Gb) Gb :=
    hSbX.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  have hTN : Tb ≤ Subgroup.normalizer (Gb : Set (X ⧸ C)) := fun _ _ => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _
  have hTZ : ∀ t ∈ Tb, ∀ z ∈ Zb, t * z = z * t := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, c.commute_omegaOne_Z ht hz]
  have hnorm : ∀ K : Subgroup Gb, IsComponentOf K ⊤ →
      Tb ≤ Subgroup.normalizer ((K.map Gb.subtype : Subgroup (X ⧸ C)) : Set (X ⧸ C)) :=
    fun K hK => le_normalizer_component hlay hcenb hObar hPb hZbeq.symm.le hTN hTZ hK
  have hGT : Gb ⊔ Tb = ⊤ := by
    rw [← Subgroup.map_sup, htop, Subgroup.map_top_of_surjective _ hsurj]
  have hex : IsComponentOf (⊤ : Subgroup Gb) ⊤ := by
    by_contra hnot
    have hcent : ∀ K : Subgroup Gb, IsComponentOf K ⊤ → ⁅K.map Gb.subtype, Tb⁆ = ⊥ := by
      intro K hK
      have hKne : K ≠ ⊤ := fun h => hnot (h ▸ hK)
      have hKn : K.Normal := CFSG.LocalCores.component_normal_of_layer_eq_top hlay
        ((CFSG.isComponent_iff_open K).mpr hK)
      set Kt := K.map Gb.subtype with hKt
      have hKtG : Kt ≤ Gb := Subgroup.map_subtype_le _
      have hKtn : Kt.Normal := by
        rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hGT]
        refine sup_le ?_ (hnorm K hK)
        have hconj : ∀ x ∈ Gb, ∀ y ∈ Kt, x * y * x⁻¹ ∈ Kt := by
          rintro x hx _ ⟨k, hk, rfl⟩
          exact ⟨⟨x, hx⟩ * k * ⟨x, hx⟩⁻¹, hKn.conj_mem k hk _, rfl⟩
        intro x hx
        exact mem_normalizer_of_conj_le (hconj x hx) (by simpa using hconj x⁻¹ (Gb.inv_mem hx))
      set Kh := Kt.comap π with hKh
      have hKhn : Kh.Normal := hKtn.comap π
      have hCG : C ≤ G := hC ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 G
      have hKhG : Kh ≤ G := by
        intro x hx
        have h2 := mk_mem_map_iff.mp (hKtG hx)
        rwa [sup_eq_left.mpr hCG] at h2
      have hKhmap : Kh.map π = Kt := Subgroup.map_comap_eq_self_of_surjective hsurj Kt
      have hKhlt : Kh < G := by
        refine lt_of_le_of_ne hKhG fun heq => hKne ?_
        apply Subgroup.map_injective Gb.subtype_injective
        rw [← hKt, ← hKhmap, heq, map_subtype_top]
      have h1 := c.commutator_eq_bot_of_lt htop hO IH hnn hMG hKhn hKhlt
      have h2 := congrArg (Subgroup.map π) h1
      rwa [Subgroup.map_commutator, hKhmap, Subgroup.map_bot] at h2
    have hGbC : Gb ≤ Subgroup.centralizer (Tb : Set (X ⧸ C)) := by
      have hle : (⊤ : Subgroup Gb) ≤
          (Subgroup.centralizer (Tb : Set (X ⧸ C))).comap Gb.subtype := by
        rw [← hlay]
        apply sSup_le
        intro K hK
        rw [← Subgroup.map_le_iff_le_comap]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (hcent K ((CFSG.isComponent_iff_open K).mp hK))
      intro x hx
      exact hle (Subgroup.mem_top ⟨x, hx⟩)
    have hGTC : ⁅G, T⁆ ≤ C := by
      rw [Subgroup.commutator_le]
      intro x hx t ht
      apply (QuotientGroup.eq_one_iff _).mp
      show π ⁅x, t⁆ = 1
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hGbC (Subgroup.mem_map_of_mem π hx)) _
        (Subgroup.mem_map_of_mem π ht)).symm
    have hGT1 : ⁅G, T⁆ = ⊥ := by
      apply CFSG.LocalCores.perfect_double_commutator (Subgroup.isPerfect_iff.mpr hperf)
      rw [eq_bot_iff]
      calc ⁅⁅G, T⁆, G⁆ ≤ ⁅C, G⁆ := Subgroup.commutator_mono hGTC le_rfl
        _ = ⊥ := by
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
            (Subgroup.le_centralizer_iff.mp (hC ▸ hcen))
    apply c.ne
    rw [rightConjugate_eq_self_iff]
    have hgC : g ∈ Subgroup.centralizer (T : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have h1 : ⁅g, t⁆ ∈ ⁅G, T⁆ := Subgroup.commutator_mem_commutator c.mem ht
      rw [hGT1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    exact Subgroup.centralizer_le_normalizer _ hgC
  have hctop : Subgroup.center (⊤ : Subgroup Gb) = ⊥ := by
    have h1 := Subgroup.map_center_eq (Subgroup.topEquiv (G := Gb))
    rw [hcenb] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.topEquiv (G := Gb)).injective).mp h1
  have hstop : IsSimpleGroup (⊤ : Subgroup Gb) := isSimpleGroup_of_center_eq_bot hctop hex.2.2.2
  refine ⟨(Subgroup.topEquiv (G := Gb)).symm.isSimpleGroup, ?_⟩
  exact goldschmidtSimpleType_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center Gb) (Subgroup.center (⊤ : Subgroup Gb))
      (Subgroup.topEquiv (G := Gb)).symm (Subgroup.map_center_eq _)) (hcomp ⊤ hex)

theorem card_omegaOne_Z (c : Conf46 G T S Q H g) :
    Nat.card (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) = Nat.card (omegaOne T) := by
  have hN : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤
      Subgroup.normalizer (omegaOne T : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact c.commute_omegaOne_Z (omegaOne_le T hu) hz
  have hinf : omegaOne T ⊓ omegaOne ((T ⊔ rightConjugate T g) ⊓ G) = ⊥ := by
    rw [eq_bot_iff, ← c.frame.inf_eq_bot]
    exact inf_le_inf (omegaOne_le T) ((omegaOne_le _).trans inf_le_right)
  have h1 := card_sup_of_le_normalizer hN hinf
  rw [← c.omegaOne_W, c.card_omegaOne_W] at h1
  exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm

theorem commutator_mem_omegaOne_W (c : Conf46 G T S Q H g) {v s : X}
    (hv : v ∈ omegaOne (T ⊔ rightConjugate T g)) (hs : s ∈ S) :
    v⁻¹ * s⁻¹ * v * s ∈ omegaOne ((T ⊔ rightConjugate T g) ⊓ G) := by
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  have hVeq : omegaOne (T ⊔ rightConjugate T g) = omegaOne T ⊔ Z₁ := c.omegaOne_W
  have hZN : Z₁ ≤ Subgroup.normalizer (omegaOne T : Set X) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact c.commute_omegaOne_Z (omegaOne_le T hu) hz
  have hvm : v ∈ (omegaOne T : Set X) * (Z₁ : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZN, ← hVeq]
    exact hv
  obtain ⟨u, hu, z, hz, rfl⟩ := Set.mem_mul.mp hvm
  have hSZ : s ∈ Subgroup.normalizer (Z₁ : Set X) := by
    have hSN : s ∈ Subgroup.normalizer (((T ⊔ rightConjugate T g) ⊓ G : Subgroup X) : Set X) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨c.le_normalizer_W hs,
        (sup_le Subgroup.le_normalizer c.frame.le_normalizer) (c.le_sup hs)⟩
    exact mem_normalizer_omegaOne hSN
  have hcomm := c.commutator_mem_omegaOne (S.inv_mem hs) hu
  have h1 : u⁻¹ * s⁻¹ * u * s ∈ Z₁ := by
    have h2 : u * (s⁻¹ * u * s⁻¹⁻¹ * u⁻¹) = (s⁻¹ * u * s⁻¹⁻¹ * u⁻¹) * u :=
      c.commute_omegaOne_Z (omegaOne_le T hu) hcomm
    have h3 : u⁻¹ * s⁻¹ * u * s = s⁻¹ * u * s⁻¹⁻¹ * u⁻¹ := by
      calc u⁻¹ * s⁻¹ * u * s = u⁻¹ * ((s⁻¹ * u * s⁻¹⁻¹ * u⁻¹) * u) := by group
        _ = u⁻¹ * (u * (s⁻¹ * u * s⁻¹⁻¹ * u⁻¹)) := by rw [← h2]
        _ = s⁻¹ * u * s⁻¹⁻¹ * u⁻¹ := by group
    rw [h3]
    exact hcomm
  have h4 : s⁻¹ * z * s ∈ Z₁ := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hSZ) z).mp hz
    simpa using this
  have h5 : (u * z)⁻¹ * s⁻¹ * (u * z) * s = z⁻¹ * (u⁻¹ * s⁻¹ * u * s) * (s⁻¹ * z * s) := by group
  rw [h5]
  exact Z₁.mul_mem (Z₁.mul_mem (Z₁.inv_mem hz) h1) h4

theorem eq_one_of_commutator_le (c : Conf46 G T S Q H g) {C : Subgroup X}
    (hperf : ⁅G, G⁆ = G) (hcen : C ≤ Subgroup.centralizer (G : Set X)) {u : X} (hu : u ∈ T)
    (hle : ⁅G, Subgroup.zpowers u⁆ ≤ C) : u = 1 := by
  have h1 : ⁅G, Subgroup.zpowers u⁆ = ⊥ := by
    apply CFSG.LocalCores.perfect_double_commutator (Subgroup.isPerfect_iff.mpr hperf)
    rw [eq_bot_iff]
    calc ⁅⁅G, Subgroup.zpowers u⁆, G⁆ ≤ ⁅C, G⁆ := Subgroup.commutator_mono hle le_rfl
      _ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (Subgroup.le_centralizer_iff.mp hcen)
  by_contra hu1
  apply c.hyp45.facts.1
  apply c.hyp43.centralizer_le c.frame hu hu1
  refine ⟨Subgroup.mem_sup_left c.mem, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  have h2 : ⁅g, u⁆ ∈ ⁅G, Subgroup.zpowers u⁆ :=
    Subgroup.commutator_mem_commutator c.mem (Subgroup.mem_zpowers u)
  rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2

theorem pCoreOf_eq_bot (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    (hG : CFSG.Goldschmidt.TopStatement) (hK : GoldschmidtTypeAutomorphisms)
    (hMG : Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) = G) :
    pCoreOf 2 G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hGn : G.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
    exact sup_le Subgroup.le_normalizer c.frame.le_normalizer
  set C := pCoreOf 2 G with hCdef
  have hCn : C.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
    exact (Subgroup.normalizer_eq_top_iff.mpr hGn).symm.le.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 G)
  obtain ⟨hsimp, htype⟩ := c.simple_bar htop hO IH hnn hG hMG hCdef
  obtain ⟨-, -, -, hZbeq, -⟩ := c.goldschmidt_two htop hO IH hnn hG hMG hCdef
  obtain ⟨-, hperf, hcen, hZeq, -⟩ := c.goldschmidt_one htop hO IH hnn hG hMG
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  set U := omegaOne T with hUdef
  set V := omegaOne (T ⊔ rightConjugate T g) with hVdef
  set π := QuotientGroup.mk' C with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective C
  have hkerπ : π.ker = C := QuotientGroup.ker_mk' C
  set Gb := G.map π with hGb
  set Sb := S.map π with hSb
  set E := V.map π with hEdef
  set Ub := U.map π with hUb
  set Zb := Z₁.map π with hZb
  have hGbn : Gb.Normal := hGn.map π hsurj
  have hCZ : C ≤ Z₁ := by rw [hZeq]; exact le_sup_left
  have hVeq : V = U ⊔ Z₁ := c.omegaOne_W
  have hSX : IsSylowOf 2 S ⊤ := htop ▸ c.sylowFrame.sylow
  have hSbX : IsSylowOf 2 Sb ⊤ := by
    have h1 := IsSylowOf.map hSX π
    rwa [Subgroup.map_top_of_surjective _ hsurj] at h1
  have hPb : IsSylowOf 2 (Sb ⊓ Gb) Gb :=
    hSbX.inf_of_le_normalizer le_top (by rw [Subgroup.normalizer_eq_top])
  have hVab : IsMulCommutative V := isMulCommutative_of_le (omegaOne_le _) c.isMulCommutative_W
  have hEab : IsMulCommutative E := by
    have := hVab
    exact inferInstance
  have hEel : IsElemAbelian 2 E := by
    refine ⟨hEab, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_pow, ((mem_omegaOne_iff c.isMulCommutative_W).mp hv).2, map_one]
  have hVS : V ≤ S := (omegaOne_le _).trans c.W_le_S
  have hEN : E ≤ Subgroup.normalizer (Gb : Set (X ⧸ C)) := fun _ _ => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _
  have hEP : E ≤ Subgroup.normalizer ((Sb ⊓ Gb : Subgroup (X ⧸ C)) : Set (X ⧸ C)) :=
    fun e he => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (Subgroup.map_mono hVS he), hEN he⟩
  have hZbE : Zb ≤ E := Subgroup.map_mono (by rw [hVeq]; exact le_sup_right)
  have hUbE : Ub ≤ E := Subgroup.map_mono (by rw [hVeq]; exact le_sup_left)
  have hEc : ∀ e ∈ E, ∀ x ∈ omegaOne (Sb ⊓ Gb), e * x = x * e := by
    intro e he x hx
    rw [← hZbeq] at hx
    exact congrArg Subtype.val (hEab.is_comm.comm ⟨e, he⟩ ⟨x, hZbE hx⟩)
  have hEcomm : ∀ e ∈ E, ∀ p ∈ Sb ⊓ Gb, e⁻¹ * p⁻¹ * e * p ∈ omegaOne (Sb ⊓ Gb) := by
    rintro _ ⟨v, hv, rfl⟩ p ⟨⟨s, hs, rfl⟩, -⟩
    rw [← hZbeq]
    have h1 : π (v⁻¹ * s⁻¹ * v * s) ∈ Zb :=
      Subgroup.mem_map_of_mem π (c.commutator_mem_omegaOne_W hv hs)
    rwa [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have hbound := hK (X ⧸ C) Gb (Sb ⊓ Gb) E hsimp htype hPb hEel hEN hEP hEc hEcomm
  rw [← hZbeq] at hbound
  set Cen := E ⊓ Subgroup.centralizer (Gb : Set (X ⧸ C)) with hCen
  have hUinj : ∀ u ∈ U, π u = 1 → u = 1 := by
    intro u hu h1
    have huC : u ∈ C := (QuotientGroup.eq_one_iff u).mp h1
    have hu' : u ∈ T ⊓ G := ⟨omegaOne_le T hu, CFSG.LieType.BorelTits.pCoreOf_le 2 G huC⟩
    rw [c.frame.inf_eq_bot] at hu'
    exact hu'
  have hUbcard : Nat.card Ub = Nat.card U := card_map_eq_of_ker π hUinj
  have hUbCen : Ub ⊓ Cen = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨u, hu, rfl⟩, -, hc⟩
    rw [Subgroup.mem_bot]
    have hle : ⁅G, Subgroup.zpowers u⁆ ≤ C := by
      rw [← hkerπ, ← Subgroup.map_eq_bot_iff, Subgroup.map_commutator, MonoidHom.map_zpowers,
        Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
        Subgroup.zpowers_le]
      exact hc
    rw [c.eq_one_of_commutator_le hperf hcen (omegaOne_le T hu) hle, map_one]
  have hCenN : Cen ≤ Subgroup.normalizer (Ub : Set (X ⧸ C)) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (hEab.is_comm.comm ⟨y, hUbE hy⟩ ⟨x, hx.1⟩)
  have hcardUC := card_sup_of_le_normalizer hCenN hUbCen
  have hle1 : Nat.card (Ub ⊔ Cen : Subgroup (X ⧸ C)) ≤ Nat.card E :=
    Subgroup.card_le_of_le (sup_le hUbE inf_le_left)
  have hZbC : Nat.card Zb * Nat.card C = Nat.card Z₁ := by
    have h1 := Subgroup.relIndex_mul_card C Z₁
    have h2 := Subgroup.relIndex_ker (K := Z₁) π
    rw [hkerπ] at h2
    rwa [h2, inf_eq_left.mpr hCZ] at h1
  have hZU : Nat.card Z₁ = Nat.card U := c.card_omegaOne_Z
  have hCen0 : 0 < Nat.card Cen := Nat.card_pos
  have hUZb : Nat.card U ≤ Nat.card Zb := by
    have h1 : Nat.card U * Nat.card Cen ≤ Nat.card Zb * Nat.card Cen := by
      calc Nat.card U * Nat.card Cen = Nat.card (Ub ⊔ Cen : Subgroup (X ⧸ C)) := by
            rw [hcardUC, hUbcard]
        _ ≤ Nat.card E := hle1
        _ ≤ Nat.card Zb * Nat.card Cen := hbound
    exact Nat.le_of_mul_le_mul_right h1 hCen0
  have hC1 : Nat.card C ≤ 1 := by
    have hZb0 : 0 < Nat.card Zb := Nat.card_pos
    have h1 : Nat.card Zb * Nat.card C ≤ Nat.card Zb * 1 := by
      rw [hZbC, hZU, mul_one]
      exact hUZb
    exact Nat.le_of_mul_le_mul_left h1 hZb0
  exact Subgroup.card_eq_one.mp (le_antisymm hC1 Nat.card_pos)

end Conf46

end CFSG.ComponentClassification.AschbacherTheorem3
