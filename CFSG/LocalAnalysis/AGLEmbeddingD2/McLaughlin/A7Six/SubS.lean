module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.A7Six.Baum
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.HA7
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.A7Six

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open Equiv Equiv.Perm

variable {X : Type} [Group X] [Finite X] {T : Subgroup X} {L : Subgroup (X ⧸ gnC T)}

namespace SixCtx

variable (c : SixCtx T L) (pd : PermData)

@[expose] def subS : Subgroup X := T ⊓ (pd.E.comap c.θ).map (nL T L).subtype

theorem mem_subS (hTL : T ≤ nL T L) {t : X} :
    t ∈ c.subS pd ↔ ∃ ht : t ∈ T, c.θ ⟨t, hTL ht⟩ ∈ pd.E := by
  constructor
  · rintro ⟨ht, ⟨⟨g, hg⟩, hgE, rfl⟩⟩
    exact ⟨ht, hgE⟩
  · rintro ⟨ht, hE⟩
    exact ⟨ht, ⟨⟨t, hTL ht⟩, hE, rfl⟩⟩

theorem subS_le : c.subS pd ≤ T := inf_le_left

theorem theta_eq_one_of_mem_gnC {g : X} (hg : g ∈ nL T L) (hgC : g ∈ gnC T) :
    c.θ ⟨g, hg⟩ = 1 := by
  rw [c.hθ1]
  intro l _
  rw [show QuotientGroup.mk' (gnC T) g = 1 from (QuotientGroup.eq_one_iff g).2 hgC]
  group

include c in
theorem eq_one_of_mem_center {z : X ⧸ gnC T} (hz : z ∈ L) (hc : ∀ l ∈ L, z * l = l * z) :
    z = 1 := by
  have hsimp : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hZ : Subgroup.center (alternatingGroup (Fin 7)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (alternatingGroup (Fin 7)))
      with h | h
    · exact h
    · exfalso
      have hcomm : ∀ a b : alternatingGroup (Fin 7), a * b = b * a := fun a b =>
        (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
      have h1 : (⟨swap 0 1 * swap 1 2, by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
            Equiv.Perm.sign_swap (by decide)]; decide⟩ : alternatingGroup (Fin 7)) *
          ⟨swap 0 1 * swap 2 3, by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
            Equiv.Perm.sign_swap (by decide)]; decide⟩ ≠
          ⟨swap 0 1 * swap 2 3, by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
            Equiv.Perm.sign_swap (by decide)]; decide⟩ *
          ⟨swap 0 1 * swap 1 2, by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
            Equiv.Perm.sign_swap (by decide)]; decide⟩ := by
        intro h
        have := congrArg Subtype.val h
        revert this
        decide
      exact h1 (hcomm _ _)
  have h1 : c.eL ⟨z, hz⟩ ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro b
    obtain ⟨l, rfl⟩ := c.eL.surjective b
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc l l.2).symm
  rw [hZ, Subgroup.mem_bot] at h1
  have h2 : (⟨z, hz⟩ : ↥L) = 1 := c.eL.injective (h1.trans (map_one c.eL).symm)
  exact congrArg Subtype.val h2

theorem theta_eq_one_of_mem_pCore (hX : GNSetting X T) (hTL : T ≤ nL T L) {q : X}
    (hq : q ∈ pCoreOf 2 (⊤ : Subgroup X)) :
    c.θ ⟨q, hTL (B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow hq)⟩ = 1 := by
  rw [c.hθ1]
  intro l hl
  set π := QuotientGroup.mk' (gnC T)
  have hqT := B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow hq
  have hQn : (pCoreOf 2 (⊤ : Subgroup X)).Normal := CFSG.AGLEmbeddingD2.GN.normal_pCoreOf_top
  set Qs : Subgroup (X ⧸ gnC T) := (pCoreOf 2 (⊤ : Subgroup X)).map π
  have hQsn : Qs.Normal := hQn.map π (QuotientGroup.mk'_surjective _)
  have hQs2 : IsPGroup 2 Qs := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤).map π
  set x := π q * l * (π q)⁻¹ * l⁻¹ with hx
  have hxQ : x ∈ Qs := by
    have h1 : l * (π q)⁻¹ * l⁻¹ ∈ Qs := hQsn.conj_mem _ (Qs.inv_mem ⟨q, hq, rfl⟩) l
    have := Qs.mul_mem ⟨q, hq, rfl⟩ h1
    simpa [hx, mul_assoc] using this
  have hqL : π q * l * (π q)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (hTL hqT) l).1 hl
  have hxL : x ∈ L := L.mul_mem hqL (L.inv_mem hl)
  have hsimp : IsSimpleGroup ↥L := c.eL.isSimpleGroup
  have hN : ((Qs ⊓ L).subgroupOf L).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨hQsn.conj_mem _ hn.1 g, L.mul_mem (L.mul_mem g.2 hn.2) (L.inv_mem g.2)⟩
  have hcard : Nat.card ↥L = 2520 := by
    rw [Nat.card_congr c.eL.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Qs ⊓ L).subgroupOf L) with h | h
  · have : (⟨x, hxL⟩ : ↥L) ∈ (Qs ⊓ L).subgroupOf L := ⟨hxQ, hxL⟩
    rw [h, Subgroup.mem_bot] at this
    have hx1 : x = 1 := congrArg Subtype.val this
    rw [hx] at hx1
    calc π q * l * (π q)⁻¹ = π q * l * (π q)⁻¹ * l⁻¹ * l := by group
      _ = l := by rw [hx1, one_mul]
  · exfalso
    have hLQ : L ≤ Qs := fun y hy => by
      have : (⟨y, hy⟩ : ↥L) ∈ (Qs ⊓ L).subgroupOf L := h ▸ Subgroup.mem_top _
      exact this.1
    have h2 : IsPGroup 2 ↥L := hQs2.to_le hLQ
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
    rw [hcard] at hk
    have h3 : (2 : ℕ) ^ k % 9 = 0 := by rw [← hk]
    have h4 : ¬ (3 : ℕ) ∣ 2 ^ k := by
      intro h3'
      exact absurd ((Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3')) (by decide)
    exact h4 (by rw [← hk]; decide)

theorem inf_gnC_le_subS (hTL : T ≤ nL T L) : T ⊓ gnC T ≤ c.subS pd := by
  rintro t ⟨ht, htC⟩
  refine (c.mem_subS pd hTL).2 ⟨ht, ?_⟩
  rw [c.theta_eq_one_of_mem_gnC (hTL ht) htC]
  exact pd.E.one_mem

theorem pCoreOf_le_subS (hX : GNSetting X T) (hTL : T ≤ nL T L) :
    pCoreOf 2 (⊤ : Subgroup X) ≤ c.subS pd := by
  intro q hq
  refine (c.mem_subS pd hTL).2 ⟨B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow hq, ?_⟩
  rw [c.theta_eq_one_of_mem_pCore hX hTL hq]
  exact pd.E.one_mem

theorem baum_le_subS (hX : GNSetting X T) (hTL : T ≤ nL T L) (hD : c.img T = pd.D) :
    baum T ≤ c.subS pd := fun g hg =>
  (c.mem_subS pd hTL).2 ⟨hg.1, c.theta_mem_E_of_mem_baum pd hX hTL hD hg⟩

theorem baum_subS (hX : GNSetting X T) (hTL : T ≤ nL T L) (hD : c.img T = pd.D) :
    baum (c.subS pd) = baum T :=
  (baum_eq_of_le (c.baum_le_subS pd hX hTL hD) (c.subS_le pd)).symm

theorem omegaOneCenterOf_le_subS (hX : GNSetting X T) (hTL : T ≤ nL T L) (hD : c.img T = pd.D) :
    omegaOneCenterOf T ≤ omegaOneCenterOf (c.subS pd) := by
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hZS : centerOf T ≤ c.subS pd := by
    intro z hz
    refine c.baum_le_subS pd hX hTL hD (Subgroup.mem_inf.2 ⟨hz.1,
      Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩)
    have hyT : y ∈ T := hJT ((Subgroup.closure_le _).mpr (fun x hx => hx.1.1) hy)
    exact (Subgroup.mem_centralizer_iff.1 hz.2 y hyT)
  refine (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure
    ⟨Subgroup.mem_inf.2 ⟨hZS hx.1, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩, hx.2⟩
  exact Subgroup.mem_centralizer_iff.1 hx.1.2 y (c.subS_le pd hy)

theorem img_subS (hTL : T ≤ nL T L) (hD : c.img T = pd.D) : c.img (c.subS pd) = pd.E := by
  apply le_antisymm
  · rintro _ ⟨⟨t, ht'⟩, ht, rfl⟩
    exact ((c.mem_subS pd hTL).1 ht).2
  · intro σ hσ
    have hσD : σ ∈ c.img T := hD ▸ pd.E_le_D hσ
    obtain ⟨⟨t, ht'⟩, ht, rfl⟩ := hσD
    exact ⟨⟨t, ht'⟩, (c.mem_subS pd hTL).2 ⟨ht, hσ⟩, rfl⟩

theorem exists_preimage_of_mem_D (hX : GNSetting X T) (hTL : T ≤ nL T L) (hL : IsComponentOf L ⊤)
    (hD : c.img T = pd.D) {σ : Perm (Fin 7)} (hσ : σ ∈ pd.D ⊓ alternatingGroup (Fin 7)) :
    ∃ (t : X) (ht : t ∈ T), QuotientGroup.mk' (gnC T) t ∈ L ∧ c.θ ⟨t, hTL ht⟩ = σ := by
  classical
  have hD8 : Nat.card (pd.D ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) = 8 := by
    have hrel : (alternatingGroup (Fin 7)).relIndex pd.D = 2 := by
      have hdvd : (alternatingGroup (Fin 7)).relIndex pd.D ∣ 2 := by
        rw [← alternatingGroup.index_eq_two (α := Fin 7)]
        exact Subgroup.relIndex_dvd_index_of_normal (H := alternatingGroup (Fin 7)) (K := pd.D)
      have hne1 : (alternatingGroup (Fin 7)).relIndex pd.D ≠ 1 := by
        rw [Ne, Subgroup.relIndex_eq_one]
        intro hle
        have := Equiv.Perm.mem_alternatingGroup.mp (hle (pd.E_le_D pd.swap_mem_E))
        rw [Equiv.Perm.sign_swap (by decide)] at this
        exact absurd this (by decide)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd h hne1
      · exact h
    have hmul := Subgroup.relIndex_mul_card (alternatingGroup (Fin 7)) pd.D
    rw [hrel, pd.card_D, inf_comm] at hmul
    omega
  have hmem : ∀ y : ↥(gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)),
      ((c.eL ⟨y, y.2.2⟩ : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈
        pd.D ⊓ alternatingGroup (Fin 7) := by
    rintro ⟨y, ⟨t, ht, rfl⟩, hy⟩
    refine ⟨hD ▸ ⟨⟨t, hTL ht⟩, ht, ?_⟩, (c.eL ⟨_, hy⟩).2⟩
    exact c.hθL ⟨t, hTL ht⟩ ⟨_, hy⟩ rfl
  let f : ↥(gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) →
      ↥(pd.D ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) := fun y => ⟨_, hmem y⟩
  have hf : Function.Injective f := by
    intro y y' h
    have h0 := congrArg Subtype.val h
    have h1 : c.eL ⟨y, y.2.2⟩ = c.eL ⟨y', y'.2.2⟩ := Subtype.ext h0
    have h2 := congrArg Subtype.val (c.eL.injective h1)
    exact Subtype.ext h2
  have h8 : 8 ≤ Nat.card (gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) := by
    have := c.eight_le_card_img_T_inf hX hTL hL
    rw [hD] at this
    have hSyl := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.GNQuotient.isSylowTwoOf_gnImg_inf
      hX.sylow hL.2.1
    have hcardL : Nat.card ↥L = 2520 := by
      rw [Nat.card_congr c.eL.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide
    have hmul := Subgroup.relIndex_mul_card (gnImg T T ⊓ L) L
    rw [inf_eq_left.mpr hSyl.1, hcardL] at hmul
    have hodd : ¬ 2 ∣ (gnImg T T ⊓ L).relIndex L := hSyl.2.2
    have hcop : Nat.Coprime (2 ^ 3) ((gnImg T T ⊓ L).relIndex L) :=
      Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    have h1 : 2 ^ 3 ∣ Nat.card (gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) *
        (gnImg T T ⊓ L).relIndex L := by
      rw [mul_comm, hmul]; norm_num
    exact Nat.le_of_dvd Nat.card_pos (hcop.dvd_of_dvd_mul_right h1)
  have hbij : Function.Bijective f := by
    refine ⟨hf, ?_⟩
    have hle := Nat.card_le_card_of_injective f hf
    rw [hD8] at hle
    have heq : Nat.card (gnImg T T ⊓ L : Subgroup (X ⧸ gnC T)) =
        Nat.card (pd.D ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) := by
      rw [hD8]; omega
    exact (Function.Injective.bijective_of_nat_card_le hf heq.ge).2
  obtain ⟨⟨y, ⟨t, ht, rfl⟩, hy⟩, hyσ⟩ := hbij.2 ⟨σ, hσ⟩
  refine ⟨t, ht, hy, ?_⟩
  have h1 := congrArg Subtype.val hyσ
  rw [c.hθL ⟨t, hTL ht⟩ ⟨_, hy⟩ rfl]
  exact h1

end SixCtx

end CFSG.AGLEmbeddingD2.McLaughlin.A7Six
