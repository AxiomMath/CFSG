module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

variable {X : Type} [Group X]

structure Frame (G T : Subgroup X) : Prop where
  le_normalizer : T ≤ Subgroup.normalizer (G : Set X)
  inf_eq_bot : T ⊓ G = ⊥
  isPGroup : IsPGroup 2 T

structure SylowFrame (G T S : Subgroup X) : Prop extends Frame G T where
  sylow : IsSylowOf 2 S (G ⊔ T)
  sylow_normalizer : IsSylowOf 2 (S ⊓ Subgroup.normalizer (T : Set X))
    ((G ⊔ T) ⊓ Subgroup.normalizer (T : Set X))

structure Hyp43 (G T Q H : Subgroup X) : Prop where
  le : Q ≤ H
  le_normalizer : H ≤ Subgroup.normalizer (Q : Set X)
  le_sup : H ≤ G ⊔ T
  sylow : IsSylowOf 2 T Q
  inf_eq_bot : ∀ g ∈ G, g ∉ H → T ⊓ rightConjugate T g = ⊥

theorem conj_mem_rightConjugate {Q : Subgroup X} {x : X} (hx : x ∈ Q) (g : X) :
    g⁻¹ * x * g ∈ rightConjugate Q g := by
  rw [mem_rightConjugate_iff]
  simpa [mul_assoc] using hx

theorem rightConjugate_le_rightConjugate {A B : Subgroup X} (h : A ≤ B) (g : X) :
    rightConjugate A g ≤ rightConjugate B g :=
  Subgroup.map_mono h

theorem rightConjugate_inf (A B : Subgroup X) (g : X) :
    rightConjugate (A ⊓ B) g = rightConjugate A g ⊓ rightConjugate B g :=
  Subgroup.map_inf_eq A B _ (MulAut.conj g⁻¹).injective

theorem rightConjugate_bot (g : X) : rightConjugate (⊥ : Subgroup X) g = ⊥ :=
  Subgroup.map_bot _

theorem rightConjugate_eq_bot_iff {A : Subgroup X} {g : X} :
    rightConjugate A g = ⊥ ↔ A = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective A (MulAut.conj g⁻¹).injective

theorem rightConjugate_le_normalizer {A B : Subgroup X}
    (h : A ≤ Subgroup.normalizer (B : Set X)) (g : X) :
    rightConjugate A g ≤ Subgroup.normalizer (rightConjugate B g : Set X) :=
  (Subgroup.map_mono h).trans (Subgroup.le_normalizer_map _)

theorem rightConjugate_eq_of_mem {A : Subgroup X} {g : X} (hg : g ∈ A) :
    rightConjugate A g = A :=
  (rightConjugate_eq_self_iff A g).mpr (Subgroup.le_normalizer hg)

theorem rightConjugate_le_of_mem {A K : Subgroup X} (hA : A ≤ K) {g : X} (hg : g ∈ K) :
    rightConjugate A g ≤ K := by
  rw [← rightConjugate_eq_of_mem hg]
  exact rightConjugate_le_rightConjugate hA g

theorem isPGroup_rightConjugate {A : Subgroup X} (hA : IsPGroup 2 A) (g : X) :
    IsPGroup 2 (rightConjugate A g) :=
  hA.map _

theorem isSylowOf_rightConjugate [Finite X] {P K : Subgroup X} (h : IsSylowOf 2 P K) (g : X) :
    IsSylowOf 2 (rightConjugate P g) (rightConjugate K g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [isSylowOf_iff] at h ⊢
  obtain ⟨hle, hP, hdvd⟩ := h
  refine ⟨Subgroup.map_mono hle, hP.map _, ?_⟩
  unfold rightConjugate
  rw [Subgroup.relIndex_map_map, ((MonoidHom.ker_eq_bot_iff _).mpr (MulAut.conj g⁻¹).injective),
    sup_bot_eq, sup_bot_eq]
  exact hdvd

theorem relIndex_sup_of_le_normalizer {A B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer (A : Set X)) : A.relIndex (A ⊔ B) = A.relIndex B := by
  have hA : A ≤ A ⊔ B := le_sup_left
  have hBL : B ≤ A ⊔ B := le_sup_right
  have : (A.subgroupOf (A ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA).mpr (sup_le Subgroup.le_normalizer hB)
  have h1 := Subgroup.relIndex_sup_left (B.subgroupOf (A ⊔ B)) (A.subgroupOf (A ⊔ B))
  rw [← Subgroup.subgroupOf_sup hA hBL, Subgroup.subgroupOf_self, Subgroup.relIndex_top_right,
    Subgroup.relIndex_subgroupOf hBL] at h1
  exact h1

theorem card_sup_of_le_normalizer [Finite X] {A B : Subgroup X}
    (hB : B ≤ Subgroup.normalizer (A : Set X)) (hAB : A ⊓ B = ⊥) :
    Nat.card (A ⊔ B : Subgroup X) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card A (A ⊔ B)
  rw [inf_eq_left.mpr le_sup_left, relIndex_sup_of_le_normalizer hB, ← Subgroup.inf_relIndex_right,
    hAB, Subgroup.relIndex_bot_left] at h1
  rw [← h1, mul_comm]

namespace Frame

variable {G T : Subgroup X}

theorem mem_sup_iff (hF : Frame G T) {x : X} :
    x ∈ G ⊔ T ↔ ∃ t ∈ T, ∃ g ∈ G, t * g = x := by
  rw [sup_comm, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right T G hF.le_normalizer]
  exact Set.mem_mul

theorem exists_rightConjugate_eq (hF : Frame G T) {x : X} (hx : x ∈ G ⊔ T) :
    ∃ t ∈ T, ∃ g ∈ G, t * g = x ∧ rightConjugate T x = rightConjugate T g := by
  obtain ⟨t, ht, g, hg, rfl⟩ := hF.mem_sup_iff.mp hx
  refine ⟨t, ht, g, hg, rfl, ?_⟩
  rw [← rightConjugate_mul, rightConjugate_eq_of_mem ht]

theorem rightConjugate_frame (hF : Frame G T) {g : X} (hg : g ∈ G) :
    Frame G (rightConjugate T g) where
  le_normalizer := by
    rw [← rightConjugate_eq_of_mem hg]
    exact rightConjugate_le_normalizer hF.le_normalizer g
  inf_eq_bot := by
    rw [← rightConjugate_eq_of_mem hg, ← rightConjugate_inf, hF.inf_eq_bot, rightConjugate_bot]
  isPGroup := isPGroup_rightConjugate hF.isPGroup g

end Frame

theorem sup_rightConjugate {G T : Subgroup X} {g : X} (hg : g ∈ G) :
    G ⊔ rightConjugate T g = G ⊔ T := by
  have hgGT : g ∈ G ⊔ T := Subgroup.mem_sup_left hg
  apply le_antisymm
  · exact sup_le le_sup_left (rightConjugate_le_of_mem le_sup_right hgGT)
  · apply sup_le le_sup_left
    intro t ht
    have heq : t = g * (g⁻¹ * t * g) * g⁻¹ := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hg)
      (Subgroup.mem_sup_right (conj_mem_rightConjugate ht g)))
      (Subgroup.mem_sup_left (G.inv_mem hg))

theorem SylowFrame.le [Finite X] {G T S : Subgroup X} (h : SylowFrame G T S) : T ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := (G ⊔ T) ⊓ Subgroup.normalizer (T : Set X)
  have hTM : T ≤ M := le_inf le_sup_right Subgroup.le_normalizer
  have : (T.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTM).mpr inf_le_right
  obtain ⟨P, hP⟩ := h.sylow_normalizer.exists_sylow_eq_subgroupOf
  have hT2 : IsPGroup 2 (T.subgroupOf M) := h.isPGroup.comap_subtype
  have hTP : T.subgroupOf M ≤ P := hT2.le_sylow_of_normal P
  intro t ht
  have hmem : (⟨t, hTM ht⟩ : M) ∈ (P : Subgroup M) := hTP ht
  rw [hP] at hmem
  exact hmem.1

theorem lemma_4_1 {G T S : Subgroup X} (hF : Frame G T) (hSGT : S ≤ G ⊔ T) (hTS : T ≤ S) :
    S ⊓ Subgroup.normalizer (T : Set X) = T ⊔ (S ⊓ Subgroup.normalizer (T : Set X) ⊓ G) ∧
      T ⊓ (S ⊓ Subgroup.normalizer (T : Set X) ⊓ G) = ⊥ ∧
      ⁅T, S ⊓ Subgroup.normalizer (T : Set X) ⊓ G⁆ = ⊥ := by
  refine ⟨le_antisymm ?_ (sup_le (le_inf hTS Subgroup.le_normalizer) inf_le_left), ?_, ?_⟩
  · rintro x ⟨hxS, hxN⟩
    obtain ⟨t, ht, g, hg, rfl⟩ := hF.mem_sup_iff.mp (hSGT hxS)
    have htN : t ∈ Subgroup.normalizer (T : Set X) := Subgroup.le_normalizer ht
    have hgS : g ∈ S := by simpa using S.mul_mem (S.inv_mem (hTS ht)) hxS
    have hgN : g ∈ Subgroup.normalizer (T : Set X) := by
      simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ htN) hxN
    exact Subgroup.mul_mem_sup ht ⟨⟨hgS, hgN⟩, hg⟩
  · exact le_bot_iff.mp ((inf_le_inf_left T inf_le_right).trans hF.inf_eq_bot.le)
  · rw [eq_bot_iff, ← hF.inf_eq_bot, Subgroup.commutator_le]
    rintro a ha b ⟨⟨-, hbN⟩, hbG⟩
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · have h1 : b * a⁻¹ * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hbN _).mp (T.inv_mem ha)
      simpa [mul_assoc] using T.mul_mem ha h1
    · have h1 : a * b * a⁻¹ ∈ G := (Subgroup.mem_normalizer_iff.mp (hF.le_normalizer ha) _).mp hbG
      exact G.mul_mem h1 (G.inv_mem hbG)

namespace Hyp43

variable {G T Q H : Subgroup X}

theorem le_Q (h : Hyp43 G T Q H) : T ≤ Q := h.sylow.le

theorem le_H (h : Hyp43 G T Q H) : T ≤ H := h.sylow.le.trans h.le

theorem inf_eq [Finite X] (h : Hyp43 G T Q H) {P : Subgroup X} (hP : IsPGroup 2 P)
    (hTP : T ≤ P) : P ⊓ Q = T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact h.sylow.eq_of_le (le_inf hTP h.le_Q) inf_le_right hP.to_inf_left

theorem le_normalizer_of_le [Finite X] (h : Hyp43 G T Q H) {P : Subgroup X}
    (hP : IsPGroup 2 P) (hTP : T ≤ P) (hPH : P ≤ H) :
    P ≤ Subgroup.normalizer (T : Set X) := by
  intro x hx
  rw [← h.inf_eq hP hTP]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hx, h.le_normalizer (hPH hx)⟩

theorem mem_of_inf_ne_bot (h : Hyp43 G T Q H) {g : X} (hg : g ∈ G)
    (hne : T ⊓ rightConjugate T g ≠ ⊥) : g ∈ H := by
  by_contra hgH
  exact hne (h.inf_eq_bot g hg hgH)

theorem mem_of_inf_ne_bot_sup (hF : Frame G T) (h : Hyp43 G T Q H) {x : X} (hx : x ∈ G ⊔ T)
    (hne : T ⊓ rightConjugate T x ≠ ⊥) : x ∈ H := by
  obtain ⟨t, ht, g, hg, rfl, hrc⟩ := hF.exists_rightConjugate_eq hx
  rw [hrc] at hne
  exact H.mul_mem (h.le_H ht) (h.mem_of_inf_ne_bot hg hne)

theorem normalizer_le (hF : Frame G T) (h : Hyp43 G T Q H) (hT : T ≠ ⊥) :
    (G ⊔ T) ⊓ Subgroup.normalizer (T : Set X) ≤ H := by
  rintro x ⟨hx, hxN⟩
  apply h.mem_of_inf_ne_bot_sup hF hx
  rw [(rightConjugate_eq_self_iff T x).mpr hxN, inf_idem]
  exact hT

theorem centralizer_le (hF : Frame G T) (h : Hyp43 G T Q H) {t : X} (ht : t ∈ T)
    (ht1 : t ≠ 1) : (G ⊔ T) ⊓ Subgroup.centralizer {t} ≤ H := by
  rintro x ⟨hx, hxC⟩
  apply h.mem_of_inf_ne_bot_sup hF hx
  intro hbot
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hmem : t ∈ T ⊓ rightConjugate T x := by
    refine Subgroup.mem_inf.mpr ⟨ht, ?_⟩
    rw [mem_rightConjugate_iff, hxt, mul_assoc, mul_inv_cancel, mul_one]
    exact ht
  rw [hbot, Subgroup.mem_bot] at hmem
  exact ht1 hmem

theorem not_mem_of_rightConjugate_le [Finite X] (h : Hyp43 G T Q H) {P : Subgroup X}
    (hP : IsPGroup 2 P) (hTP : T ≤ P) {g : X} (hgP : rightConjugate T g ≤ P)
    (hne : rightConjugate T g ≠ T) : g ∉ H := by
  intro hgH
  have hQ : rightConjugate Q g = Q :=
    (rightConjugate_eq_self_iff Q g).mpr (h.le_normalizer hgH)
  have hle : rightConjugate T g ≤ T :=
    (le_inf hgP (hQ ▸ rightConjugate_le_rightConjugate h.le_Q g)).trans (h.inf_eq hP hTP).le
  exact hne (Subgroup.eq_of_le_of_card_ge hle (rightConjugate_card T g).ge)

theorem rightConjugate_hyp [Finite X] (h : Hyp43 G T Q H) {g : X} (hg : g ∈ G) :
    Hyp43 G (rightConjugate T g) (rightConjugate Q g) (rightConjugate H g) where
  le := rightConjugate_le_rightConjugate h.le g
  le_normalizer := rightConjugate_le_normalizer h.le_normalizer g
  le_sup := by
    rw [sup_rightConjugate hg, ← rightConjugate_eq_of_mem (Subgroup.mem_sup_left hg :
      g ∈ G ⊔ T)]
    exact rightConjugate_le_rightConjugate h.le_sup g
  sylow := isSylowOf_rightConjugate h.sylow g
  inf_eq_bot := by
    intro k hk hkH
    have hk' : g * k * g⁻¹ ∈ G := G.mul_mem (G.mul_mem hg hk) (G.inv_mem hg)
    have hkH' : g * k * g⁻¹ ∉ H := fun hmem => hkH ((mem_rightConjugate_iff H g k).mpr hmem)
    have hrc : rightConjugate (rightConjugate T g) k =
        rightConjugate (rightConjugate T (g * k * g⁻¹)) g := by
      rw [rightConjugate_mul, rightConjugate_mul]
      congr 1
      group
    rw [hrc, ← rightConjugate_inf, h.inf_eq_bot _ hk' hkH', rightConjugate_bot]

end Hyp43

theorem lemma_4_4_one [Finite X] {G T Q H : Subgroup X} (hF : Frame G T)
    (h43 : Hyp43 G T Q H) {P : Subgroup X} (hP : IsPGroup 2 P) (hPGT : P ≤ G ⊔ T)
    (hTP : T ≤ P) (hidx : T.relIndex P ≤ Nat.card T) :
    P ≤ Subgroup.normalizer (T : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  let M : Subgroup P := (Subgroup.normalizer (T : Set X)).subgroupOf P
  have hMtop : M < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun hM => hcon fun x hx => ?_
    have hmem : (⟨x, hx⟩ : P) ∈ M := hM ▸ Subgroup.mem_top _
    exact hmem
  have : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨x, hxN, hxM⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent M hMtop)
  have hxN' : (x : X) ∉ Subgroup.normalizer (T : Set X) := hxM
  have hKle : rightConjugate T x ≤ P ⊓ Subgroup.normalizer (T : Set X) := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    have hyeq : y = (x : X)⁻¹ * ((x : X) * y * (x : X)⁻¹) * x := by group
    have htM : (⟨(x : X) * y * (x : X)⁻¹, hTP hy⟩ : P) ∈ M := Subgroup.le_normalizer hy
    have hconj := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp htM
    rw [hyeq]
    have hconj' := Subgroup.mem_subgroupOf.mp hconj
    exact ⟨P.mul_mem (P.mul_mem (P.inv_mem x.2) (hTP hy)) x.2, by simpa using hconj'⟩
  obtain ⟨t, ht, g, hg, htg, hrc⟩ := hF.exists_rightConjugate_eq (hPGT x.2)
  rw [hrc] at hKle
  have hne : rightConjugate T g ≠ T := by
    rw [← hrc]
    exact fun heq => hxN' ((rightConjugate_eq_self_iff T x).mp heq)
  have hgH : g ∉ H := h43.not_mem_of_rightConjugate_le hP hTP (hKle.trans inf_le_left) hne
  have hinf : T ⊓ rightConjugate T g = ⊥ := h43.inf_eq_bot g hg hgH
  set K := rightConjugate T g
  have hKN : K ≤ Subgroup.normalizer (T : Set X) := hKle.trans inf_le_right
  have hTKP : T ⊔ K ≤ P := sup_le hTP (hKle.trans inf_le_left)
  have hidx1 : T.relIndex (T ⊔ K) = Nat.card T := by
    rw [relIndex_sup_of_le_normalizer hKN, ← Subgroup.inf_relIndex_right, hinf,
      Subgroup.relIndex_bot_left, rightConjugate_card]
  have hmul := Subgroup.relIndex_mul_relIndex T (T ⊔ K) P le_sup_left hTKP
  rw [hidx1] at hmul
  have hpos : 0 < Nat.card T := Nat.card_pos
  have hr : (T ⊔ K).relIndex P ≠ 0 := by
    intro h0
    have hc := Subgroup.relIndex_mul_card (T ⊔ K) P
    rw [h0, zero_mul] at hc
    exact (Nat.card_pos (α := P)).ne hc
  have hr1 : (T ⊔ K).relIndex P = 1 := by
    have : Nat.card T * (T ⊔ K).relIndex P ≤ Nat.card T * 1 := by rw [mul_one, hmul]; exact hidx
    have := Nat.le_of_mul_le_mul_left this hpos
    omega
  exact hcon ((Subgroup.relIndex_eq_one.mp hr1).trans (sup_le Subgroup.le_normalizer hKN))

theorem lemma_4_4_two [Finite X] {G T Q H S : Subgroup X} (hF : Frame G T)
    (h43 : Hyp43 G T Q H) (hS : IsPGroup 2 S) (hTS : T ≤ S) {g : X} (hg : g ∈ G)
    (hgSH : rightConjugate T g ≤ S ⊓ H) (hne : rightConjugate T g ≠ T) :
    g ∉ H ∧ T ⊓ rightConjugate T g = ⊥ ∧ ⁅T, rightConjugate T g⁆ = ⊥ ∧
      IsMulCommutative (T ⊔ rightConjugate T g : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := rightConjugate T g
  have hgH : g ∉ H := h43.not_mem_of_rightConjugate_le hS hTS (hgSH.trans inf_le_left) hne
  have hinf : T ⊓ K = ⊥ := h43.inf_eq_bot g hg hgH
  have hKN : K ≤ Subgroup.normalizer (T : Set X) :=
    hgSH.trans (h43.le_normalizer_of_le hS.to_inf_left (le_inf hTS h43.le_H) inf_le_right)
  set P := T ⊔ K
  have hK2 : IsPGroup 2 K := isPGroup_rightConjugate hF.isPGroup g
  have hP2 : IsPGroup 2 P := IsPGroup.to_sup_of_normal_left' hF.isPGroup hK2 hKN
  have hgGT : g ∈ G ⊔ T := Subgroup.mem_sup_left hg
  have hPGT : P ≤ G ⊔ T := sup_le le_sup_right (rightConjugate_le_of_mem le_sup_right hgGT)
  have hKP : K ≤ P := le_sup_right
  have hcardP : Nat.card P = Nat.card T * Nat.card K := card_sup_of_le_normalizer hKN hinf
  have hFK := hF.rightConjugate_frame hg
  have h43K := h43.rightConjugate_hyp hg
  have hidxK : K.relIndex P ≤ Nat.card K := by
    have hc := Subgroup.relIndex_mul_card K P
    rw [inf_eq_left.mpr hKP, hcardP] at hc
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have : K.relIndex P = Nat.card T := Nat.eq_of_mul_eq_mul_right hKpos hc
    rw [this, rightConjugate_card]
  have hPNK : P ≤ Subgroup.normalizer (K : Set X) :=
    lemma_4_4_one hFK h43K hP2 (by rw [sup_rightConjugate hg]; exact hPGT) hKP hidxK
  have hPNT : P ≤ Subgroup.normalizer (T : Set X) := sup_le Subgroup.le_normalizer hKN
  have hcomm : ⁅T, K⁆ = ⊥ := by
    rw [eq_bot_iff, ← hinf, Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    refine ⟨?_, ?_⟩
    · have h1 : b * a⁻¹ * b⁻¹ ∈ T :=
        (Subgroup.mem_normalizer_iff.mp (hKN hb) _).mp (T.inv_mem ha)
      simpa [mul_assoc] using T.mul_mem ha h1
    · have h1 : a * b * a⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hPNK (Subgroup.mem_sup_left ha)) _).mp hb
      exact K.mul_mem h1 (K.inv_mem hb)
  obtain ⟨hPT, -, hcT⟩ := lemma_4_1 hF hPGT le_sup_left
  obtain ⟨hPK, -, hcK⟩ := lemma_4_1 hFK (by rw [sup_rightConjugate hg]; exact hPGT) hKP
  rw [inf_eq_left.mpr hPNT] at hPT hcT
  rw [inf_eq_left.mpr hPNK] at hPK hcK
  have hTC : P ≤ Subgroup.centralizer (T : Set X) := by
    rw [hPK]
    refine sup_le ?_ ?_
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcT
  have hKC : P ≤ Subgroup.centralizer (K : Set X) := by
    rw [hPT]
    refine sup_le ?_ ?_
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hcomm
    · rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcK
  refine ⟨hgH, hinf, hcomm, ?_⟩
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  rw [Subgroup.le_centralizer_iff] at hTC hKC
  exact sup_le hTC hKC

end CFSG.ComponentClassification.AschbacherTheorem3
