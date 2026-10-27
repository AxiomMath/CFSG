module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transfer
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentActionBasic
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Sylow

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.ComponentClassification
open CFSG.RankTwoShapes
open scoped Pointwise commutatorElement

variable {X : Type} [Group X]

theorem mem_normalizer_map_of_characteristic {G : Subgroup X} (A : Subgroup G)
    [hA : A.Characteristic] {t : X} (ht : t ∈ Subgroup.normalizer (G : Set X)) :
    t ∈ Subgroup.normalizer ((A.map G.subtype : Subgroup X) : Set X) := by
  have hG := Subgroup.mem_normalizer_iff_map_conj_eq.mp ht
  let φ : G ≃* G := ((MulAut.conj t).subgroupMap G).trans (MulEquiv.subgroupCongr hG)
  have hAφ : A.map φ.toMonoidHom = A := Subgroup.characteristic_iff_map_eq.mp hA φ
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
  have hcomp : (MulAut.conj t : X →* X).comp G.subtype = G.subtype.comp φ.toMonoidHom := by
    ext g
    rfl
  rw [hcomp, ← Subgroup.map_map, hAφ]

theorem isSylowOf_sup_of_frame [Finite X] {G T P : Subgroup X} (hF : Frame G T)
    (hP : IsSylowOf 2 P G) (hTP : T ≤ Subgroup.normalizer (P : Set X)) :
    IsSylowOf 2 (T ⊔ P) (G ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPG, hP2, hdvd⟩ := isSylowOf_iff.mp hP
  have hle : T ⊔ P ≤ G ⊔ T := sup_le le_sup_right (hPG.trans le_sup_left)
  rw [isSylowOf_iff]
  refine ⟨hle, IsPGroup.to_sup_of_normal_right' hF.isPGroup hP2 hTP, ?_⟩
  have hTG : T ⊓ G = ⊥ := hF.inf_eq_bot
  have hPT : P ⊓ T = ⊥ := le_bot_iff.mp (by
    rw [inf_comm, ← hTG]
    exact inf_le_inf_left T hPG)
  have hcTP : Nat.card (T ⊔ P : Subgroup X) = Nat.card P * Nat.card T := by
    rw [sup_comm]
    exact card_sup_of_le_normalizer hTP hPT
  have hcGT : Nat.card (G ⊔ T : Subgroup X) = Nat.card G * Nat.card T :=
    card_sup_of_le_normalizer hF.le_normalizer (by rw [inf_comm]; exact hTG)
  have h1 := Subgroup.relIndex_mul_card (T ⊔ P) (G ⊔ T)
  rw [inf_eq_left.mpr hle, hcTP, hcGT] at h1
  have h2 := Subgroup.relIndex_mul_card P G
  rw [inf_eq_left.mpr hPG] at h2
  have hpos : 0 < Nat.card P * Nat.card T := Nat.mul_pos Nat.card_pos Nat.card_pos
  have heq : (T ⊔ P).relIndex (G ⊔ T) = P.relIndex G := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← mul_assoc, h2]
  rw [heq]
  exact hdvd

theorem exists_center_involution [Finite X] {T : Subgroup X} (hT : IsPGroup 2 T) (hne : T ≠ ⊥) :
    ∃ z ∈ T, orderOf z = 2 ∧ T ≤ Subgroup.centralizer {z} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hne
  have hZ : Nontrivial (Subgroup.center T) := hT.center_nontrivial
  have h2 : 2 ∣ Nat.card (Subgroup.center T) := by
    rcases (hT.to_subgroup (Subgroup.center T)).card_eq_or_dvd with h1 | h1
    · exact absurd h1 (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne'
    · exact h1
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨((x : T) : X), (x : T).2, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
  · intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp x.2 ⟨t, ht⟩)

theorem card_sup_lt [Finite X] {G G₁ T : Subgroup X} (hF : Frame G T) (hlt : G₁ < G)
    (hT₁ : T ≤ Subgroup.normalizer (G₁ : Set X)) :
    Nat.card (G₁ ⊔ T : Subgroup X) < Nat.card (G ⊔ T : Subgroup X) := by
  have hTG : T ⊓ G = ⊥ := hF.inf_eq_bot
  have h1 : G₁ ⊓ T = ⊥ := le_bot_iff.mp (by
    rw [inf_comm, ← hTG]
    exact inf_le_inf_left T hlt.le)
  rw [card_sup_of_le_normalizer hT₁ h1,
    card_sup_of_le_normalizer hF.le_normalizer (by rw [inf_comm]; exact hTG)]
  exact Nat.mul_lt_mul_of_pos_right (Subgroup.card_lt_of_lt hlt) Nat.card_pos

namespace Hyp42

variable {G T S : Subgroup X}

theorem le_normalizer (h : Hyp42 G T S) : S ≤ Subgroup.normalizer (T : Set X) := by
  intro s hs
  obtain ⟨t, ht, g, hg, -, hrc⟩ := h.frame.exists_rightConjugate_eq (h.sylow.le hs)
  rw [← rightConjugate_eq_self_iff, hrc]
  apply h.closed g hg
  rw [← hrc, ← rightConjugate_eq_of_mem hs]
  exact rightConjugate_le_rightConjugate h.le s

theorem le_centralizer (h : Hyp42 G T S) :
    T ≤ Subgroup.centralizer ((S ⊓ G : Subgroup X) : Set X) := by
  obtain ⟨-, -, hc⟩ := lemma_4_1 h.frame h.sylow.le h.le
  rw [inf_eq_left.mpr h.le_normalizer] at hc
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc

theorem sylow_inf [Finite X] (h : Hyp42 G T S) : IsSylowOf 2 (S ⊓ G) G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.sylow.inf_of_le_normalizer le_sup_left
    (sup_le Subgroup.le_normalizer h.frame.le_normalizer)

end Hyp42

theorem commutator_eq_bot_of_layer_commutator [Finite X] {G T S : Subgroup X}
    (h : Hyp42 G T S) (hO : CFSG.oddCore G = ⊥)
    (hE : ⁅(Layer.subgroup G).map G.subtype, T⁆ = ⊥) : ⁅G, T⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (GeneralizedFitting.subgroup G).Characteristic := GeneralizedFitting.characteristic G
  have : (Fitting.subgroup G).Normal := Fitting.normal G
  set F := (Fitting.subgroup G).map G.subtype with hFdef
  set E := (Layer.subgroup G).map G.subtype with hEdef
  set FS := (GeneralizedFitting.subgroup G).map G.subtype with hFSdef
  have hF2 : IsPGroup 2 (Fitting.subgroup G) := by
    rw [PrimeCore.fitting_eq_two_of_odd_corefree hO]
    exact PrimeCore.isPGroup 2 G
  have hFS : F ≤ S ⊓ G := by
    obtain ⟨P, hP⟩ := h.sylow_inf.exists_sylow_eq_subgroupOf
    have hle := hF2.le_sylow_of_normal P
    rintro _ ⟨y, hy, rfl⟩
    have hmem := hle hy
    rw [hP] at hmem
    exact hmem
  have hTF : T ≤ Subgroup.centralizer (F : Set X) :=
    h.le_centralizer.trans (Subgroup.centralizer_le hFS)
  have hTE : T ≤ Subgroup.centralizer (E : Set X) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hE
  have hFSeq : FS = F ⊔ E := by
    rw [hFSdef, GeneralizedFitting.subgroup, Subgroup.map_sup]
  have hTFS : T ≤ Subgroup.centralizer (FS : Set X) := by
    rw [Subgroup.le_centralizer_iff, hFSeq]
    exact sup_le (Subgroup.le_centralizer_iff.mp hTF) (Subgroup.le_centralizer_iff.mp hTE)
  have hGFS : G ≤ Subgroup.normalizer (FS : Set X) := fun g hg =>
    mem_normalizer_map_of_characteristic (GeneralizedFitting.subgroup G)
      (Subgroup.le_normalizer hg)
  have hTG : ⁅T, G⁆ ≤ F := by
    rw [Subgroup.commutator_le]
    intro t ht g hg
    have hcG : ⁅t, g⁆ ∈ G := by
      rw [commutatorElement_def]
      have h1 : t * g * t⁻¹ ∈ G :=
        (Subgroup.mem_normalizer_iff.mp (h.frame.le_normalizer ht) g).mp hg
      exact G.mul_mem h1 (G.inv_mem hg)
    have hcC : ⁅t, g⁆ ∈ Subgroup.centralizer (FS : Set X) := by
      rw [commutatorElement_def]
      have h1 : t ∈ Subgroup.centralizer (FS : Set X) := hTFS ht
      have hgN : g ∈ Subgroup.normalizer (Subgroup.centralizer (FS : Set X) : Set X) :=
        normalizer_le_normalizer_centralizer FS (hGFS hg)
      have h2 : g * t⁻¹ * g⁻¹ ∈ Subgroup.centralizer (FS : Set X) :=
        (Subgroup.mem_normalizer_iff.mp hgN _).mp (Subgroup.inv_mem _ h1)
      simpa [mul_assoc] using Subgroup.mul_mem _ h1 h2
    have hc' : (⟨⁅t, g⁆, hcG⟩ : G) ∈
        Subgroup.centralizer (GeneralizedFitting.subgroup G : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hcC (y : X) ⟨y, hy, rfl⟩
    exact ⟨⟨⁅t, g⁆, hcG⟩, GeneralizedFitting.centralizer_le_fitting G hc', rfl⟩
  have hGN : G ≤ Subgroup.normalizer (T : Set X) := by
    intro g hg
    rw [← rightConjugate_eq_self_iff]
    apply h.closed g hg
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have hxeq : x = (g * x * g⁻¹) * ⁅(g * x * g⁻¹)⁻¹, g⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [hxeq]
    exact S.mul_mem (h.le hx) (hFS (hTG (Subgroup.commutator_mem_commutator (T.inv_mem hx)
      (G.inv_mem hg)))).1
  rw [eq_bot_iff, ← h.frame.inf_eq_bot, Subgroup.commutator_le]
  intro g hg t ht
  rw [commutatorElement_def]
  refine ⟨?_, ?_⟩
  · have h1 : g * t * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hGN hg) t).mp ht
    exact T.mul_mem h1 (T.inv_mem ht)
  · have h1 : t * g⁻¹ * t⁻¹ ∈ G :=
      (Subgroup.mem_normalizer_iff.mp (h.frame.le_normalizer ht) _).mp (G.inv_mem hg)
    simpa [mul_assoc] using G.mul_mem hg h1

theorem hyp42_layer [Finite X] {G T S : Subgroup X} (h : Hyp42 G T S) :
    Hyp42 ((Layer.subgroup G).map G.subtype) T
      (T ⊔ (S ⊓ (Layer.subgroup G).map G.subtype)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (Layer.subgroup G).Characteristic := Layer.characteristic G
  set E := (Layer.subgroup G).map G.subtype
  have hEG : E ≤ G := Subgroup.map_subtype_le _
  have hTE : T ≤ Subgroup.normalizer (E : Set X) := fun t ht =>
    mem_normalizer_map_of_characteristic (Layer.subgroup G) (h.frame.le_normalizer ht)
  have hGE : G ≤ Subgroup.normalizer (E : Set X) := fun g hg =>
    mem_normalizer_map_of_characteristic (Layer.subgroup G) (Subgroup.le_normalizer hg)
  have hFE : Frame E T :=
    ⟨hTE, le_bot_iff.mp ((inf_le_inf_left T hEG).trans h.frame.inf_eq_bot.le), h.frame.isPGroup⟩
  have hSE : IsSylowOf 2 (S ⊓ E) E :=
    h.sylow.inf_of_le_normalizer (hEG.trans le_sup_left) (sup_le hGE hTE)
  have hTSE : T ≤ Subgroup.normalizer ((S ⊓ E : Subgroup X) : Set X) :=
    (h.le_centralizer.trans (Subgroup.centralizer_le (inf_le_inf_left S hEG))).trans
      (Subgroup.centralizer_le_normalizer _)
  exact
    { frame := hFE
      sylow := isSylowOf_sup_of_frame hFE hSE hTSE
      le := le_sup_left
      closed := fun g hg hle => h.closed g (hEG hg) (hle.trans (sup_le h.le inf_le_left)) }

theorem oddCore_layer_eq_bot [Finite X] {G : Subgroup X} (hO : CFSG.oddCore G = ⊥) :
    CFSG.oddCore ((Layer.subgroup G).map G.subtype) = ⊥ := by
  have : (Layer.subgroup G).Characteristic := Layer.characteristic G
  set E := (Layer.subgroup G).map G.subtype
  have hEG : E ≤ G := Subgroup.map_subtype_le _
  have hGE : G ≤ Subgroup.normalizer (E : Set X) := fun g hg =>
    mem_normalizer_map_of_characteristic (Layer.subgroup G) (Subgroup.le_normalizer hg)
  have : (CFSG.oddCore E).Characteristic := OddCore.characteristic E
  have hOG : (CFSG.oddCore E).map E.subtype ≤ G := (Subgroup.map_subtype_le _).trans hEG
  have hGO : G ≤ Subgroup.normalizer (((CFSG.oddCore E).map E.subtype : Subgroup X) : Set X) :=
    fun g hg => mem_normalizer_map_of_characteristic (CFSG.oddCore E) (hGE hg)
  have hodd : Odd (Nat.card ((CFSG.oddCore E).map E.subtype)) := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact odd_card_oddCore E
  have hle := le_map_oddCore hOG hGO hodd
  rw [hO, Subgroup.map_bot, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ E.subtype_injective).mp hle

theorem centralizes_of_layer_eq_top [Finite X] {G T S : Subgroup X} (h : Hyp42 G T S)
    (hO : CFSG.oddCore G = ⊥) (hEG : Layer.subgroup G = ⊤)
    (hIH : ∀ G₁ S₁ : Subgroup X, G₁ < G → Hyp42 G₁ T S₁ →
      ⁅G₁, T⁆ ≤ (CFSG.oddCore G₁).map G₁.subtype)
    {z : X} (hzT : z ∈ T) (hz2 : orderOf z = 2) (hzC : T ≤ Subgroup.centralizer {z}) :
    G ≤ Subgroup.centralizer {z} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzz : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  set Z := Subgroup.zpowers z with hZdef
  have hZT : Z ≤ T := Subgroup.zpowers_le.mpr hzT
  have hFZ : Frame G Z :=
    ⟨hZT.trans h.frame.le_normalizer,
      le_bot_iff.mp ((inf_le_inf_right G hZT).trans h.frame.inf_eq_bot.le),
      h.frame.isPGroup.to_le hZT⟩
  set K := G ⊔ Z with hKdef
  set R := Z ⊔ (S ⊓ G) with hRdef
  have hzCT : z ∈ Subgroup.centralizer (T : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hzC ht))
  have hTR : T ≤ Subgroup.centralizer (R : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le (Subgroup.zpowers_le.mpr hzCT) ?_
    rw [← Subgroup.le_centralizer_iff]
    exact h.le_centralizer
  have hRS : R ≤ S := sup_le (hZT.trans h.le) inf_le_left
  have hR : IsSylowOf 2 R K := isSylowOf_sup_of_frame hFZ h.sylow_inf
    ((hZT.trans h.le_centralizer).trans (Subgroup.centralizer_le_normalizer _))
  have hKN : K ≤ Subgroup.normalizer (G : Set X) := sup_le Subgroup.le_normalizer hFZ.le_normalizer
  have hRK : R ≤ K := hR.le
  have hKGT : K ≤ G ⊔ T := sup_le le_sup_left (hZT.trans le_sup_right)
  obtain ⟨RS, hRSeq⟩ := hR.exists_sylow_eq_subgroupOf
  set z' : K := ⟨z, Subgroup.mem_sup_right (Subgroup.mem_zpowers z)⟩ with hz'def
  have hz'RS : z' ∈ (RS : Subgroup K) := by
    rw [hRSeq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
  have hzR : ∀ r ∈ R, r * z = z * r := fun r hr =>
    Subgroup.mem_centralizer_iff.mp (hTR hzT) r hr
  have hperfect : Group.IsPerfect G := ⟨by
    rw [eq_top_iff, ← hEG]
    exact Layer.le_derived G⟩
  have key : ∀ Q' : Subgroup K, IsAlperinSubgroup 2 (RS : Subgroup K) Q' →
      ∀ n ∈ Subgroup.normalizer (Q' : Set K), z' ∈ Q' → n⁻¹ * z' * n = z' := by
    intro Q' hQ n hn hzQ
    set Q := Q'.map K.subtype with hQdef
    have hQR : Q ≤ R := by
      have hmap := Subgroup.map_mono (f := K.subtype) hQ.1
      rwa [hRSeq, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRK] at hmap
    have hQK : Q ≤ K := Subgroup.map_subtype_le _
    have hQ2 : IsPGroup 2 Q := h.sylow.isPGroup.to_le (hQR.trans hRS)
    have hzQmem : z ∈ Q := ⟨z', hzQ, rfl⟩
    have hnQ : (n : X) ∈ Subgroup.normalizer (Q : Set X) :=
      Subgroup.le_normalizer_map K.subtype ⟨n, hn, rfl⟩
    have hnK : (n : X) ∈ (G : Set X) * (Z : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left G Z hFZ.le_normalizer]
      exact n.2
    obtain ⟨g, hg, w, hw, hgw⟩ := Set.mem_mul.mp hnK
    have hwN : w ∈ Subgroup.normalizer (Q : Set X) :=
      ((Subgroup.centralizer_le hQR).trans (Subgroup.centralizer_le_normalizer _)) (hTR (hZT hw))
    have hwz : w * z = z * w := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_left (Commute.refl z) k).eq
    have hgN : g ∈ Subgroup.normalizer (Q : Set X) := by
      have hgeq : g = (n : X) * w⁻¹ := by rw [← hgw]; group
      rw [hgeq]
      exact Subgroup.mul_mem _ hnQ (Subgroup.inv_mem _ hwN)
    have hgz : g⁻¹ * z * g = z := by
      by_cases hGQ : G ≤ Subgroup.normalizer (Q : Set X)
      ·
        have hPG : Q ⊓ G ≤ G := inf_le_right
        have hGP : G ≤ Subgroup.normalizer ((Q ⊓ G : Subgroup X) : Set X) := fun x hx =>
          Subgroup.inf_normalizer_le_normalizer_inf ⟨hGQ hx, Subgroup.le_normalizer hx⟩
        have hnorm : ((Q ⊓ G).subgroupOf G).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hPG).mpr hGP
        have hP2 : IsPGroup 2 ((Q ⊓ G).subgroupOf G) := hQ2.to_inf_left.comap_subtype
        have : Group.IsNilpotent ((Q ⊓ G).subgroupOf G) := hP2.isNilpotent
        have hcomm := Layer.commutes_with_solvable_subnormal ((Q ⊓ G).subgroupOf G)
          (Components.chain_of_mathlib_subnormal hnorm.isSubnormal)
        rw [hEG] at hcomm
        have hcommX : ⁅G, Q ⊓ G⁆ = ⊥ := by
          have hmap := congrArg (Subgroup.map G.subtype) hcomm
          rwa [Subgroup.map_commutator, Subgroup.map_bot, ← MonoidHom.range_eq_map,
            Subgroup.range_subtype, Subgroup.subgroupOf_map_subtype,
            inf_eq_left.mpr hPG] at hmap
        have hQG : ⁅Q, G⁆ ≤ Q ⊓ G := by
          rw [Subgroup.commutator_le]
          intro q hq x hx
          rw [commutatorElement_def]
          refine ⟨?_, ?_⟩
          · have h1 : x * q⁻¹ * x⁻¹ ∈ Q :=
              (Subgroup.mem_normalizer_iff.mp (hGQ hx) _).mp (Q.inv_mem hq)
            simpa [mul_assoc] using Q.mul_mem hq h1
          · have h1 : q * x * q⁻¹ ∈ G :=
              (Subgroup.mem_normalizer_iff.mp (hKN (hQK hq)) x).mp hx
            exact G.mul_mem h1 (G.inv_mem hx)
        have h3 : ⁅⁅Q, G⁆, G⁆ = ⊥ := by
          rw [eq_bot_iff, ← hcommX, Subgroup.commutator_comm G]
          exact Subgroup.commutator_mono hQG le_rfl
        have hQGbot := AschbacherComponentAction.perfect_three_subgroup_action G Q h3
        rw [Subgroup.commutator_comm] at hQGbot
        have hgC : g ∈ Subgroup.centralizer (Q : Set X) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQGbot hg
        have hzg := Subgroup.mem_centralizer_iff.mp hgC z hzQmem
        calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
          _ = g⁻¹ * (g * z) := by rw [hzg]
          _ = z := by group
      ·
        set N := G ⊓ Subgroup.normalizer (Q : Set X) with hNdef
        have hNlt : N < G := lt_of_le_of_ne inf_le_left fun heq => hGQ (heq ▸ inf_le_right)
        have hsylK : IsSylowOf 2 (R ⊓ (Subgroup.normalizer (Q : Set X) ⊓ K))
            (Subgroup.normalizer (Q : Set X) ⊓ K) := by
          have h1 : IsSylowOf 2 ((RS : Subgroup K) ⊓ Subgroup.normalizer (Q' : Set K))
              (Subgroup.normalizer (Q' : Set K)) := by
            rw [isSylowOf_iff]
            exact ⟨inf_le_right, RS.isPGroup'.to_inf_left,
              (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hQ.2.1⟩
          rw [← isSylowOf_map_subtype_iff K] at h1
          have hQ'eq : Q' = Q.subgroupOf K := by
            rw [hQdef, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
              K.subtype_injective]
          have hNmap : (Subgroup.normalizer (Q' : Set K)).map K.subtype =
              Subgroup.normalizer (Q : Set X) ⊓ K := by
            rw [hQ'eq, ← Subgroup.subgroupOf_normalizer_eq hQK, Subgroup.subgroupOf_map_subtype]
          rwa [Subgroup.map_inf _ _ _ K.subtype_injective, hNmap, hRSeq,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hRK] at h1
        have hsylN : IsSylowOf 2 (R ⊓ (Subgroup.normalizer (Q : Set X) ⊓ K) ⊓ N) N :=
          hsylK.inf_of_le_normalizer (le_inf inf_le_right (inf_le_left.trans le_sup_left))
            fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
              ⟨hKN hx.2, Subgroup.le_normalizer hx.1⟩
        set PQ := R ⊓ (Subgroup.normalizer (Q : Set X) ⊓ K) ⊓ N with hPQdef
        have hTQ : T ≤ Subgroup.normalizer (Q : Set X) :=
          (hTR.trans (Subgroup.centralizer_le hQR)).trans (Subgroup.centralizer_le_normalizer _)
        have hFN : Frame N T :=
          ⟨fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
              ⟨h.frame.le_normalizer ht, Subgroup.le_normalizer (hTQ ht)⟩,
            le_bot_iff.mp ((inf_le_inf_left T inf_le_left).trans h.frame.inf_eq_bot.le),
            h.frame.isPGroup⟩
        have hTPQ : T ≤ Subgroup.normalizer (PQ : Set X) :=
          (hTR.trans (Subgroup.centralizer_le (inf_le_left.trans inf_le_left))).trans
            (Subgroup.centralizer_le_normalizer _)
        have hPQS : PQ ≤ S := inf_le_left.trans (inf_le_left.trans hRS)
        have h42N : Hyp42 N T (T ⊔ PQ) :=
          { frame := hFN
            sylow := isSylowOf_sup_of_frame hFN hsylN hTPQ
            le := le_sup_left
            closed := fun x hx hle => h.closed x hx.1 (hle.trans (sup_le h.le hPQS)) }
        have hcomm := hIH N (T ⊔ PQ) hNlt h42N
        have hgN' : g⁻¹ ∈ N := ⟨G.inv_mem hg, Subgroup.inv_mem _ hgN⟩
        have hmem := hcomm (Subgroup.commutator_mem_commutator hgN' hzT)
        have hmemQ : ⁅g⁻¹, z⁆ ∈ Q := by
          rw [commutatorElement_def, inv_inv]
          have h1 : g⁻¹ * z * g⁻¹⁻¹ ∈ Q :=
            (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) z).mp hzQmem
          rw [inv_inv] at h1
          exact Q.mul_mem h1 (Q.inv_mem hzQmem)
        have hO' : Odd (Nat.card ((CFSG.oddCore N).map N.subtype)) := by
          rw [Subgroup.card_map_of_injective N.subtype_injective]
          exact odd_card_oddCore N
        have hbot := two_subgroup_of_odd_eq_bot (Q ⊓ (CFSG.oddCore N).map N.subtype) _
          hQ2.to_inf_left hO' inf_le_right
        have h1 : ⁅g⁻¹, z⁆ = 1 := by
          have hmem' : ⁅g⁻¹, z⁆ ∈ Q ⊓ (CFSG.oddCore N).map N.subtype := ⟨hmemQ, hmem⟩
          rw [hbot, Subgroup.mem_bot] at hmem'
          exact hmem'
        rw [commutatorElement_def, inv_inv] at h1
        exact mul_inv_eq_one.mp h1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hgw]
    calc (g * w)⁻¹ * z * (g * w) = w⁻¹ * (g⁻¹ * z * g) * w := by group
      _ = w⁻¹ * (z * w) := by rw [hgz, mul_assoc]
      _ = z := by rw [← hwz]; group
  have hdec : ∀ c : K, AlperinDecomposition 2 (RS : Subgroup K) (Subgroup.zpowers z') c →
      c⁻¹ * z' * c = z' := by
    intro c hc
    induction hc with
    | one => group
    | @step c n Q' _ hQ hPQ hn ih =>
      have hzQ : z' ∈ Q' := by
        apply hPQ
        refine ⟨z', Subgroup.mem_zpowers z', ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        exact ih
      calc (c * n)⁻¹ * z' * (c * n) = n⁻¹ * (c⁻¹ * z' * c) * n := by group
        _ = n⁻¹ * z' * n := by rw [ih]
        _ = z' := key Q' hQ n hn hzQ
  have hwc : ∀ x : K, x⁻¹ * z' * x ∈ (RS : Subgroup K) → x⁻¹ * z' * x = z' := by
    intro x hx
    have hP : Subgroup.zpowers z' ≤ (RS : Subgroup K) := Subgroup.zpowers_le.mpr hz'RS
    have hPx : (Subgroup.zpowers z').map (MulAut.conj x⁻¹).toMonoidHom ≤ (RS : Subgroup K) := by
      rw [MonoidHom.map_zpowers]
      refine Subgroup.zpowers_le.mpr ?_
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact hx
    obtain ⟨c, hc, hcx⟩ := alperin_centric_radical_fusion RS hP hPx
    rw [← hcx z' (Subgroup.mem_zpowers z')]
    exact hdec c hc
  have hzZ : (⟨z', hz'RS⟩ : (RS : Subgroup K)) ∈ Subgroup.center (RS : Subgroup K) := by
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    apply Subtype.ext
    have hr : ((r : K) : X) ∈ R := (SetLike.ext_iff.mp hRSeq (r : K)).mp r.2
    exact hzR _ hr
  have hzord : orderOf (⟨z', hz'RS⟩ : (RS : Subgroup K)) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hz2
  obtain ⟨hcent, -⟩ :=
    CFSG.Milestones.glauberman_zStar_central_sylow_involution RS ⟨z', hz'RS⟩ hzZ hzord hwc
  have hsq : ∀ y ∈ K, y ^ 2 ∈ G := by
    intro y hy
    have hy' : y ∈ (G : Set X) * (Z : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left G Z hFZ.le_normalizer]
      exact hy
    obtain ⟨g, hg, w, hw, rfl⟩ := Set.mem_mul.mp hy'
    have hw2 : w * w = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← zpow_add, ← two_mul, zpow_mul]
      rw [zpow_two, ← pow_two, hzz, one_zpow]
    have h1 : w * g * w⁻¹ ∈ G :=
      (Subgroup.mem_normalizer_iff.mp (hFZ.le_normalizer hw) g).mp hg
    have heq : (g * w) ^ 2 = g * (w * g * w⁻¹) := by
      rw [pow_two]
      calc g * w * (g * w) = g * (w * g * w⁻¹) * (w * w) := by group
        _ = g * (w * g * w⁻¹) := by rw [hw2, mul_one]
    rw [heq]
    exact G.mul_mem hg h1
  have hOK : CFSG.oddCore K = ⊥ := by
    have : (CFSG.oddCore K).Characteristic := OddCore.characteristic K
    have hOG : (CFSG.oddCore K).map K.subtype ≤ G := by
      rintro _ ⟨y, hy, rfl⟩
      show (y : X) ∈ G
      have hodd : Odd (orderOf y) :=
        (odd_card_oddCore K).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hy)
      obtain ⟨m, hm⟩ := hodd
      have hy2 := hsq (y : X) y.2
      have hyeq : (y : X) = ((y : X) ^ 2) ^ (m + 1) := by
        rw [← pow_mul, show 2 * (m + 1) = orderOf y + 1 by omega, pow_succ,
          ← Subgroup.orderOf_coe, pow_orderOf_eq_one, one_mul]
      rw [hyeq]
      exact G.pow_mem hy2 _
    have hGO : G ≤ Subgroup.normalizer (((CFSG.oddCore K).map K.subtype : Subgroup X) :
        Set X) := fun g hg =>
      mem_normalizer_map_of_characteristic (CFSG.oddCore K)
        (Subgroup.le_normalizer (Subgroup.mem_sup_left hg))
    have hodd : Odd (Nat.card ((CFSG.oddCore K).map K.subtype)) := by
      rw [Subgroup.card_map_of_injective K.subtype_injective]
      exact odd_card_oddCore K
    have hle := le_map_oddCore hOG hGO hodd
    rw [hO, Subgroup.map_bot, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hle
  intro g hg
  obtain ⟨c, hc, k, hk, hgck⟩ := hcent ⟨g, Subgroup.mem_sup_left hg⟩
  rw [hOK, Subgroup.mem_bot] at hk
  rw [hk, mul_one] at hgck
  rw [← hgck] at hc
  have hc' := Subgroup.mem_centralizer_singleton_iff.mp hc
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val hc'

theorem commutator_le_of_oddCore_ne_bot [Finite X] {G T S : Subgroup X} (h : Hyp42 G T S)
    (hO : CFSG.oddCore G ≠ ⊥)
    (IH : ∀ (Y : Type) [Group Y] [Finite Y] (G' T' S' : Subgroup Y),
      Nat.card (G' ⊔ T' : Subgroup Y) < Nat.card (G ⊔ T : Subgroup X) → Hyp42 G' T' S' →
        ⁅G', T'⁆ ≤ (CFSG.oddCore G').map G'.subtype) :
    ⁅G, T⁆ ≤ (CFSG.oddCore G).map G.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply commutator_le_oddCore_of_restrict
  set L := G ⊔ T with hLdef
  have h₀ := h.restrict
  have htop : G.subgroupOf L ⊔ T.subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hG₀n : (G.subgroupOf L).Normal := ⟨fun x hx g => by
    have hg : g ∈ Subgroup.normalizer ((G.subgroupOf L : Subgroup L) : Set L) :=
      (htop ▸ sup_le Subgroup.le_normalizer h₀.frame.le_normalizer : (⊤ : Subgroup L) ≤ _)
        (Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp hx⟩
  have : (CFSG.oddCore (G.subgroupOf L)).Characteristic := OddCore.characteristic _
  set N := (CFSG.oddCore (G.subgroupOf L)).map (G.subgroupOf L).subtype with hNdef
  have hNn : N.Normal := ConjAct.normal_of_characteristic_of_normal
  have hNG : N ≤ G.subgroupOf L := Subgroup.map_subtype_le _
  have hNodd : Odd (Nat.card N) := by
    rw [hNdef, Subgroup.card_map_of_injective (G.subgroupOf L).subtype_injective]
    exact odd_card_oddCore _
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hO
    have h1 : CFSG.oddCore (G.subgroupOf L) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective _ (G.subgroupOf L).subtype_injective).mp hbot
    have h2 := map_oddCore_equiv (Subgroup.subgroupOfEquivOfLe (le_sup_left : G ≤ L))
    rw [h1, Subgroup.map_bot] at h2
    exact h2.symm
  have h₁ := h₀.quotient htop N ?_ ?_
  · have hcardq : Nat.card ((G.subgroupOf L).map (QuotientGroup.mk' N) ⊔
        (T.subgroupOf L).map (QuotientGroup.mk' N) : Subgroup (L ⧸ N)) <
        Nat.card (G ⊔ T : Subgroup X) := by
      rw [← Subgroup.map_sup, htop,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), Subgroup.card_top]
      exact card_quotient_lt hNne
    exact commutator_le_oddCore_of_quotient h₀.frame N (by rw [inf_eq_left.mpr hNG]; exact hNodd)
      (IH (L ⧸ N) _ _ _ hcardq h₁)
  · intro t ht g hg hgt
    have htG : t ∈ G.subgroupOf L := by
      have heq : t = g * (g⁻¹ * t) := by group
      rw [heq]
      exact (G.subgroupOf L).mul_mem hg (hNG hgt)
    have ht1 : t = 1 := by
      have hmem : t ∈ T.subgroupOf L ⊓ G.subgroupOf L := ⟨ht, htG⟩
      rw [h₀.frame.inf_eq_bot, Subgroup.mem_bot] at hmem
      exact hmem
    rw [ht1, mul_one] at hgt
    exact (Subgroup.inv_mem_iff N).mp hgt
  · intro g hg hle
    have hsyl : IsSylowOf 2 (S.subgroupOf L) (S.subgroupOf L ⊔ N) :=
      h₀.sylow.of_le le_sup_left (by rw [htop]; exact le_top)
    obtain ⟨c, hc, hcle⟩ := exists_rightConjugate_le_of_isSylowOf hsyl
      (isPGroup_rightConjugate h₀.frame.isPGroup g) hle
    have hc' : c ∈ (N : Set L) * ((S.subgroupOf L : Subgroup L) : Set L) := by
      rw [← Subgroup.normal_mul N (S.subgroupOf L), sup_comm]
      exact hc
    obtain ⟨m, hm, s, hs, rfl⟩ := Set.mem_mul.mp hc'
    have hle' : rightConjugate (T.subgroupOf L) (g * m) ≤ S.subgroupOf L := by
      have h1 := rightConjugate_le_rightConjugate hcle s⁻¹
      rw [rightConjugate_mul, rightConjugate_mul, rightConjugate_eq_of_mem (Subgroup.inv_mem _ hs),
        show g * (m * s * s⁻¹) = g * m by group] at h1
      exact h1
    have heq := h₀.closed (g * m) ((G.subgroupOf L).mul_mem hg (hNG hm)) hle'
    refine ⟨m⁻¹, N.inv_mem hm, ?_⟩
    have h2 := congrArg (fun P => rightConjugate P m⁻¹) heq
    simp only [rightConjugate_mul, mul_inv_cancel_right] at h2
    exact h2

theorem commutator_le_of_central [Finite X] {G T S : Subgroup X} (h : Hyp42 G T S) {z : X}
    (hzT : z ∈ T) (hz1 : z ≠ 1) (hzC : G ⊔ T ≤ Subgroup.centralizer {z})
    (IH : ∀ (Y : Type) [Group Y] [Finite Y] (G' T' S' : Subgroup Y),
      Nat.card (G' ⊔ T' : Subgroup Y) < Nat.card (G ⊔ T : Subgroup X) → Hyp42 G' T' S' →
        ⁅G', T'⁆ ≤ (CFSG.oddCore G').map G'.subtype) :
    ⁅G, T⁆ ≤ (CFSG.oddCore G).map G.subtype := by
  apply commutator_le_oddCore_of_restrict
  set L := G ⊔ T with hLdef
  have h₀ := h.restrict
  have htop : G.subgroupOf L ⊔ T.subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  set z₀ : L := ⟨z, Subgroup.mem_sup_right hzT⟩ with hz₀def
  have hz₀T : z₀ ∈ T.subgroupOf L := hzT
  have hz₀C : z₀ ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hzC y.2)
  set N := Subgroup.zpowers z₀ with hNdef
  have hNn : N.Normal := Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz₀C)
  have hNT : N ≤ T.subgroupOf L := Subgroup.zpowers_le.mpr hz₀T
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply hz1
    have hmem : z₀ ∈ N := Subgroup.mem_zpowers z₀
    rw [hbot, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hNG : N ⊓ G.subgroupOf L = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hNT).trans h₀.frame.inf_eq_bot.le)
  have h₁ := h₀.quotient htop N ?_ ?_
  · have hcardq : Nat.card ((G.subgroupOf L).map (QuotientGroup.mk' N) ⊔
        (T.subgroupOf L).map (QuotientGroup.mk' N) : Subgroup (L ⧸ N)) <
        Nat.card (G ⊔ T : Subgroup X) := by
      rw [← Subgroup.map_sup, htop,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N), Subgroup.card_top]
      exact card_quotient_lt hNne
    exact commutator_le_oddCore_of_quotient h₀.frame N
      (by rw [hNG, Subgroup.card_bot]; exact odd_one) (IH (L ⧸ N) _ _ _ hcardq h₁)
  · intro t ht g hg hgt
    have hgT : g ∈ T.subgroupOf L := by
      have heq : g = t * (g⁻¹ * t)⁻¹ := by group
      rw [heq]
      exact (T.subgroupOf L).mul_mem ht ((T.subgroupOf L).inv_mem (hNT hgt))
    have hmem : g ∈ T.subgroupOf L ⊓ G.subgroupOf L := ⟨hgT, hg⟩
    rw [h₀.frame.inf_eq_bot, Subgroup.mem_bot] at hmem
    rw [hmem]
    exact N.one_mem
  · intro g hg hle
    refine ⟨1, N.one_mem, ?_⟩
    rw [rightConjugate_one]
    exact h₀.closed g hg (hle.trans (sup_le le_rfl (hNT.trans h₀.le)))

theorem lemma_4_2_le (n : ℕ) :
    ∀ (X : Type) [Group X] [Finite X] (G T S : Subgroup X),
      Nat.card (G ⊔ T : Subgroup X) ≤ n → Hyp42 G T S →
        ⁅G, T⁆ ≤ (CFSG.oddCore G).map G.subtype := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ G T S hcard h
  have IH : ∀ (Y : Type) [Group Y] [Finite Y] (G' T' S' : Subgroup Y),
      Nat.card (G' ⊔ T' : Subgroup Y) < Nat.card (G ⊔ T : Subgroup X) → Hyp42 G' T' S' →
        ⁅G', T'⁆ ≤ (CFSG.oddCore G').map G'.subtype :=
    fun Y _ _ G' T' S' hlt h' => ih _ (lt_of_lt_of_le hlt hcard) Y G' T' S' le_rfl h'
  by_cases hO : CFSG.oddCore G = ⊥
  swap
  · exact commutator_le_of_oddCore_ne_bot h hO IH
  suffices hbot : ⁅G, T⁆ = ⊥ by
    rw [hbot]
    exact bot_le
  by_cases hE : ⁅(Layer.subgroup G).map G.subtype, T⁆ = ⊥
  · exact commutator_eq_bot_of_layer_commutator h hO hE
  by_cases hEG : Layer.subgroup G = ⊤
  swap
  · exfalso
    apply hE
    have hlt : (Layer.subgroup G).map G.subtype < G := by
      refine lt_of_le_of_ne (Subgroup.map_subtype_le _) fun heq => hEG ?_
      apply Subgroup.map_injective G.subtype_injective
      rw [heq, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hE42 := hyp42_layer h
    have hcomm := IH X _ _ _ (card_sup_lt h.frame hlt hE42.frame.le_normalizer) hE42
    rwa [oddCore_layer_eq_bot hO, Subgroup.map_bot, le_bot_iff] at hcomm
  by_cases hT : T = ⊥
  · rw [hT, Subgroup.commutator_bot_right]
  obtain ⟨z, hzT, hz2, hzC⟩ := exists_center_involution h.frame.isPGroup hT
  have hGz := centralizes_of_layer_eq_top h hO hEG
    (fun G₁ S₁ hlt h₁ => IH X G₁ T S₁ (card_sup_lt h.frame hlt h₁.frame.le_normalizer) h₁)
    hzT hz2 hzC
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    omega
  have hle := commutator_le_of_central h hzT hz1 (sup_le hGz hzC) IH
  rwa [hO, Subgroup.map_bot, le_bot_iff] at hle

theorem lemma_4_2_oddCore [Finite X] {G T S : Subgroup X} (h : Hyp42 G T S) :
    ⁅G, T⁆ ≤ (CFSG.oddCore G).map G.subtype :=
  lemma_4_2_le _ X G T S le_rfl h

theorem lemma_4_2 [Finite X] {G T S : Subgroup X} (h : SylowFrame G T S)
    (hwc : ∀ g ∈ G, rightConjugate T g ≤ S → rightConjugate T g = T)
    (hO : CFSG.oddCore G = ⊥) : ⁅G, T⁆ = ⊥ := by
  have hle := lemma_4_2_oddCore (⟨h.toFrame, h.sylow, h.le, hwc⟩ : Hyp42 G T S)
  rwa [hO, Subgroup.map_bot, le_bot_iff] at hle

end CFSG.ComponentClassification.AschbacherTheorem3
