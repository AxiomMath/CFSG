module

public import CFSG.GH74.Generic.BProg.B1.PilotS3Facts

public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS3
open scoped MatrixGroups commutatorElement

section SplitAt

variable {X : Type} [Group X]

structure SplitAt (F : Type) [Field F] [Finite F] (Y : Subgroup X) (z u : X) (J₁ J₂ : Subgroup X) : Prop where
  ord : orderOf u = 2
  le₁ : J₁ ≤ centralizer ({u} : Set X) ⊓ Y
  le₂ : J₂ ≤ centralizer ({u} : Set X) ⊓ Y
  comm : ∀ a ∈ Y, ∀ b ∈ Y, a * u = u * a → b * u = u * b → ⁅a, b⁆ ∈ J₁ ⊔ J₂
  norm₁ : ∀ a ∈ Y, a * u = u * a → ∀ j ∈ J₁, a * j * a⁻¹ ∈ J₁
  norm₂ : ∀ a ∈ Y, a * u = u * a → ∀ j ∈ J₂, a * j * a⁻¹ ∈ J₂
  commute : ∀ a ∈ J₁, ∀ b ∈ J₂, a * b = b * a
  disj : Disjoint J₁ J₂
  u_mem : u ∈ J₁
  zu_mem : z * u ∈ J₂
  equiv₁ : Nonempty (↥J₁ ≃* SL(2, F))
  equiv₂ : Nonempty (↥J₂ ≃* SL(2, F))
  invol : ∀ d ∈ Y, d * d = 1 → (∀ j ∈ J₁, d * j = j * d) → d = 1 ∨ d = z ∨ d = u ∨ d = z * u
  sq_mem : Nat.card F < 4 → ∀ a ∈ Y, a * u = u * a → a * a ∈ J₁ ⊔ J₂

namespace SplitAt

variable {F : Type} [Field F] [Finite F] {Y : Subgroup X} {z u : X} {J₁ J₂ : Subgroup X}

theorem map {X' : Type} [Group X'] (ι : X →* X') (hι : Function.Injective ι)
    (h : SplitAt F Y z u J₁ J₂) : SplitAt F (Y.map ι) (ι z) (ι u) (J₁.map ι) (J₂.map ι) := by
  have hcomm : ∀ a b : X, ι a * ι b = ι b * ι a ↔ a * b = b * a := fun a b => by
    rw [← map_mul, ← map_mul]
    exact ⟨fun h => hι h, fun h => by rw [h]⟩
  have hcentι : ∀ a : X, ι a * ι u = ι u * ι a ↔ a * u = u * a := fun a => hcomm a u
  have hle : ∀ J : Subgroup X, J ≤ centralizer ({u} : Set X) ⊓ Y →
      J.map ι ≤ centralizer ({ι u} : Set X') ⊓ Y.map ι := by
    rintro J hJ _ ⟨j, hj, rfl⟩
    obtain ⟨hj1, hj2⟩ := hJ hj
    refine ⟨?_, j, hj2, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hj1
    exact Subgroup.mem_centralizer_singleton_iff.2 ((hcentι j).2 h1)
  have hcl : ∀ (a b : X) , ⁅ι a, ι b⁆ = ι ⁅a, b⁆ := fun a b => (map_commutatorElement ι a b).symm
  refine ⟨?_, hle J₁ h.le₁, hle J₂ h.le₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [orderOf_injective ι hι u]
    exact h.ord
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hau hbu
    rw [hcentι] at hau hbu
    rw [hcl, ← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem ι (h.comm a ha b hb hau hbu)
  · rintro _ ⟨a, ha, rfl⟩ hau _ ⟨j, hj, rfl⟩
    rw [hcentι] at hau
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem ι (h.norm₁ a ha hau j hj)
  · rintro _ ⟨a, ha, rfl⟩ hau _ ⟨j, hj, rfl⟩
    rw [hcentι] at hau
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem ι (h.norm₂ a ha hau j hj)
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.commute a ha b hb]
  · exact Subgroup.disjoint_map hι h.disj
  · exact Subgroup.mem_map_of_mem ι h.u_mem
  · rw [← map_mul]
    exact Subgroup.mem_map_of_mem ι h.zu_mem
  · obtain ⟨e⟩ := h.equiv₁
    exact ⟨((J₁.equivMapOfInjective ι hι).symm).trans e⟩
  · obtain ⟨e⟩ := h.equiv₂
    exact ⟨((J₂.equivMapOfInjective ι hι).symm).trans e⟩
  · rintro _ ⟨d, hd, rfl⟩ hdd hdj
    have hdd' : d * d = 1 := hι (by rw [map_mul, hdd, map_one])
    have hdj' : ∀ j ∈ J₁, d * j = j * d := fun j hj =>
      hι (by rw [map_mul, map_mul]; exact hdj (ι j) (Subgroup.mem_map_of_mem ι hj))
    rcases h.invol d hd hdd' hdj' with h1 | h1 | h1 | h1
    · left; rw [h1, map_one]
    · right; left; rw [h1]
    · right; right; left; rw [h1]
    · right; right; right; rw [h1, map_mul]
  · rintro hF _ ⟨a, ha, rfl⟩ hau
    rw [hcentι] at hau
    rw [← map_mul, ← Subgroup.map_sup]
    exact Subgroup.mem_map_of_mem ι (h.sq_mem hF a ha hau)

theorem normal₁ (h : SplitAt F Y z u J₁ J₂) :
    (J₁.subgroupOf (centralizer ({u} : Set X) ⊓ Y)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff h.le₁).2 fun a b ha hb => ?_
  exact h.norm₁ b hb.2 (Subgroup.mem_centralizer_singleton_iff.1 hb.1) a ha

theorem normal₂ (h : SplitAt F Y z u J₁ J₂) :
    (J₂.subgroupOf (centralizer ({u} : Set X) ⊓ Y)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff h.le₂).2 fun a b ha hb => ?_
  exact h.norm₂ b hb.2 (Subgroup.mem_centralizer_singleton_iff.1 hb.1) a ha

theorem card_eq (h : SplitAt F Y z u J₁ J₂) : Nat.card ↥J₁ = Nat.card ↥J₂ := by
  obtain ⟨e₁⟩ := h.equiv₁
  obtain ⟨e₂⟩ := h.equiv₂
  exact Nat.card_congr (e₁.toEquiv.trans e₂.toEquiv.symm)

variable [Finite X]

theorem isPCompIn₁ (hodd : Odd (Nat.card F)) (hbig : 4 ≤ Nat.card F) (h : SplitAt F Y z u J₁ J₂) :
    IsPCompIn 2 (centralizer ({u} : Set X) ⊓ Y) J₁ := by
  obtain ⟨e⟩ := h.equiv₁
  exact isPCompIn_of_normal_sl2 h.le₁ h.normal₁ e hodd hbig

theorem isPCompIn₂ (hodd : Odd (Nat.card F)) (hbig : 4 ≤ Nat.card F) (h : SplitAt F Y z u J₁ J₂) :
    IsPCompIn 2 (centralizer ({u} : Set X) ⊓ Y) J₂ := by
  obtain ⟨e⟩ := h.equiv₂
  exact isPCompIn_of_normal_sl2 h.le₂ h.normal₂ e hodd hbig

theorem isPCompIn_self₁ (hodd : Odd (Nat.card F)) (hbig : 4 ≤ Nat.card F)
    (h : SplitAt F Y z u J₁ J₂) : IsPCompIn 2 J₁ J₁ := by
  obtain ⟨e⟩ := h.equiv₁
  refine isPCompIn_of_normal_sl2 le_rfl ?_ e hodd hbig
  rw [Subgroup.subgroupOf_self]
  infer_instance

theorem pLayerOf_ne_bot (hodd : Odd (Nat.card F)) (hbig : 4 ≤ Nat.card F)
    (h : SplitAt F Y z u J₁ J₂) : pLayerOf 2 (centralizer ({u} : Set X) ⊓ Y) ≠ ⊥ := by
  intro hbot
  have h1 : J₁ ≤ pLayerOf 2 (centralizer ({u} : Set X) ⊓ Y) := le_sSup (h.isPCompIn₁ hodd hbig)
  rw [hbot, le_bot_iff] at h1
  have h2 : Nat.card ↥J₁ = 1 := by rw [h1]; exact Subgroup.card_bot
  obtain ⟨e⟩ := h.equiv₁
  have h3 : Nat.card ↥J₁ = Nat.card SL(2, F) := Nat.card_congr e.toEquiv
  have h4 : Nat.card ↥(center SL(2, F)) = 2 := CFSG.ClassicalInvolution.sl2_natCard_center hodd
  have h5 := Subgroup.card_le_card_group (center SL(2, F))
  omega

theorem card_le_of_isPCompIn (hodd : Odd (Nat.card F)) (hbig : 4 ≤ Nat.card F)
    (h : SplitAt F Y z u J₁ J₂) {L' : Subgroup X}
    (hL' : IsPCompIn 2 (centralizer ({u} : Set X) ⊓ Y) L') : Nat.card ↥L' ≤ Nat.card ↥J₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup X := centralizer ({u} : Set X) ⊓ Y with hH
  have hJ₁H : J₁ ≤ H := h.le₁
  have hJ₂H : J₂ ≤ H := h.le₂
  set A₁ : Subgroup ↥H := J₁.subgroupOf H with hA₁
  set A₂ : Subgroup ↥H := J₂.subgroupOf H with hA₂
  set O : Subgroup ↥H := pPrimeCore 2 ↥H with hO
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπ
  obtain ⟨e₁⟩ := h.equiv₁
  obtain ⟨e₂⟩ := h.equiv₂
  have e₁' : ↥A₁ ≃* SL(2, F) := (Subgroup.subgroupOfEquivOfLe hJ₁H).trans e₁
  have e₂' : ↥A₂ ≃* SL(2, F) := (Subgroup.subgroupOfEquivOfLe hJ₂H).trans e₂
  have hq₁ : IsQuasisimple ↥A₁ := isQuasisimple_of_equiv_sl2 hbig e₁'
  have hq₂ : IsQuasisimple ↥A₂ := isQuasisimple_of_equiv_sl2 hbig e₂'
  have hZ₁ : Nat.card ↥(center ↥A₁) = 2 := CFSG.ClassicalInvolution.natCard_center_of_equiv_sl2 hodd e₁'
  have hZ₂ : Nat.card ↥(center ↥A₂) = 2 := CFSG.ClassicalInvolution.natCard_center_of_equiv_sl2 hodd e₂'
  have hO₁ : ∀ m ∈ A₁, m ∈ O → m = 1 := inf_pPrimeCore_eq_one hq₁ hZ₁
  have hO₂ : ∀ m ∈ A₂, m ∈ O → m = 1 := inf_pPrimeCore_eq_one hq₂ hZ₂
  have hA₁n : A₁.Normal := h.normal₁
  have hA₂n : A₂.Normal := h.normal₂
  have hA₁₂ : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := fun a ha b hb =>
    Subtype.ext (h.commute a ha b hb)
  have hdisj : Disjoint A₁ A₂ := by
    rw [Subgroup.disjoint_def]
    intro a ha₁ ha₂
    exact Subtype.ext (Subgroup.disjoint_def.1 h.disj ha₁ ha₂)
  have hsq : ∀ (A : Subgroup ↥H), Nat.card ↥(center ↥A) = 2 → ∀ a ∈ A,
      (∀ b ∈ A, a * b = b * a) → a ^ 2 = 1 := by
    intro A hZ a ha hac
    have hz : (⟨a, ha⟩ : ↥A) ∈ center ↥A := Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (hac g g.2).symm
    have := pow_card_eq_one' (G := ↥(center ↥A)) (x := ⟨⟨a, ha⟩, hz⟩)
    rw [hZ] at this
    have h2 := congrArg (fun t : ↥(center ↥A) => (((t : ↥A) : ↥H) : H)) this
    simpa using h2
  have hYO : ∀ m ∈ A₁ ⊔ A₂, m ∈ O → m = 1 := by
    intro m hm hmO
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hA₁₂ hm
    have hc12 : Commute a₁ a₂ := hA₁₂ a₁ ha₁ a₂ ha₂
    have hconj : ∀ a : ↥H, ⁅a, a₁ * a₂⁆ ∈ O := by
      intro a
      rw [commutatorElement_def]
      exact O.mul_mem (Subgroup.Normal.conj_mem inferInstance _ hmO a) (O.inv_mem hmO)
    have hcomm_mem : ∀ (A : Subgroup ↥H) (a b : ↥H), a ∈ A → b ∈ A → ⁅a, b⁆ ∈ A := by
      intro A a b ha hb
      rw [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)
    have hc₁ : ∀ a ∈ A₁, a₁ * a = a * a₁ := by
      intro a ha
      have h2 : ⁅a, a₁ * a₂⁆ = ⁅a, a₁⁆ := by
        rw [hc12.eq]
        exact commutator_mul_right_of_commute hc12.symm (hA₁₂ a ha a₂ ha₂).symm
      have h3 : ⁅a, a₁⁆ = 1 := hO₁ _ (hcomm_mem A₁ a a₁ ha ha₁) (h2 ▸ hconj a)
      exact ((commutatorElement_eq_one_iff_mul_comm.1 h3).symm)
    have hc₂ : ∀ a ∈ A₂, a₂ * a = a * a₂ := by
      intro a ha
      have h2 : ⁅a, a₁ * a₂⁆ = ⁅a, a₂⁆ :=
        commutator_mul_right_of_commute hc12 (hA₁₂ a₁ ha₁ a ha)
      have h3 : ⁅a, a₂⁆ = 1 := hO₂ _ (hcomm_mem A₂ a a₂ ha ha₂) (h2 ▸ hconj a)
      exact ((commutatorElement_eq_one_iff_mul_comm.1 h3).symm)
    have h1 : a₁ ^ 2 = 1 := hsq A₁ hZ₁ a₁ ha₁ hc₁
    have h2 : a₂ ^ 2 = 1 := hsq A₂ hZ₂ a₂ ha₂ hc₂
    have hm2 : (a₁ * a₂) ^ 2 = 1 := by rw [hc12.mul_pow, h1, h2, one_mul]
    have hodd' := odd_orderOf_of_mem_pPrimeCore hmO
    have hdvd : orderOf (a₁ * a₂) ∣ 2 := orderOf_dvd_of_pow_eq_one hm2
    have : orderOf (a₁ * a₂) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h' | h'
      · exact h'
      · rw [h'] at hodd'; exact absurd hodd' (by decide)
    exact orderOf_eq_one_iff.1 this
  have hLH : L' ≤ H := hL'.1
  have hcomp : IsPComponent 2 (L'.subgroupOf H) := hL'.2
  set Lg : Subgroup ↥H := L'.subgroupOf H with hLg
  have hperf : ⁅Lg, Lg⁆ = Lg :=
    Subgroup.isPerfect_iff.1
      (CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect hcomp)
  obtain ⟨Kb, hKb, -, hmap, -⟩ := hcomp
  have hLY : Lg ≤ A₁ ⊔ A₂ := by
    have h2 : ⁅Lg, Lg⁆ ≤ A₁ ⊔ A₂ := by
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      obtain ⟨j₁, hj₁, j₂, hj₂, hjj⟩ := mem_sup_of_commute h.commute
        (h.comm (g₁ : X) g₁.2.2 (g₂ : X) g₂.2.2 (Subgroup.mem_centralizer_singleton_iff.1 g₁.2.1)
          (Subgroup.mem_centralizer_singleton_iff.1 g₂.2.1))
      have : ⁅g₁, g₂⁆ = (⟨j₁, hJ₁H hj₁⟩ : ↥H) * ⟨j₂, hJ₂H hj₂⟩ := Subtype.ext hjj
      rw [this]
      exact Subgroup.mul_mem_sup hj₁ hj₂
    rwa [hperf] at h2
  have key : ∀ (A B : Subgroup ↥H), (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → Disjoint A B →
      (∀ m ∈ A ⊔ B, m ∈ O → m = 1) → Lg ≤ A ⊔ B → Lg.map π ≤ A.map π → Lg ≤ A := by
    intro A B hAB hdj hAB1 hLAB hKA ℓ hℓ
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hAB (hLAB hℓ)
    obtain ⟨a, ha, haπ⟩ := hKA ⟨_, hℓ, rfl⟩
    have h2 : (a⁻¹ * a₁) * a₂ ∈ O := by
      have h2' : π (a⁻¹ * (a₁ * a₂)) = 1 := by
        rw [map_mul, map_inv, ← haπ, inv_mul_cancel]
      rw [mul_assoc]
      exact (QuotientGroup.eq_one_iff _).1 h2'
    have h3 : (a⁻¹ * a₁) * a₂ = 1 :=
      hAB1 _ (Subgroup.mul_mem_sup (A.mul_mem (A.inv_mem ha) ha₁) ha₂) h2
    have h4 : a₂ ∈ A := by
      have : a₂ = (a⁻¹ * a₁)⁻¹ := eq_inv_of_mul_eq_one_right h3
      rw [this]
      exact A.inv_mem (A.mul_mem (A.inv_mem ha) ha₁)
    have h5 : a₂ = 1 := Subgroup.disjoint_def.1 hdj h4 ha₂
    rw [h5, mul_one]
    exact ha₁
  have hN₁ : (A₁.map π).Normal := hA₁n.map π (QuotientGroup.mk'_surjective O)
  have hN₂ : (A₂.map π).Normal := hA₂n.map π (QuotientGroup.mk'_surjective O)
  have hLle : ∀ (J : Subgroup X), Lg ≤ J.subgroupOf H → Nat.card ↥L' ≤ Nat.card ↥J := by
    intro J hJ
    refine Subgroup.card_le_of_le (fun g hg => ?_)
    exact Subgroup.mem_subgroupOf.1 (hJ (Subgroup.mem_subgroupOf.2 hg : (⟨g, hLH hg⟩ : ↥H) ∈ Lg))
  rcases CFSG.LocalCores.component_normal_subgroup hKb hN₁ with hK1 | hK1
  · exact hLle J₁ (key A₁ A₂ hA₁₂ hdisj hYO hLY (hmap ▸ hK1))
  rcases CFSG.LocalCores.component_normal_subgroup hKb hN₂ with hK2 | hK2
  · have := key A₂ A₁ (fun a ha b hb => (hA₁₂ b hb a ha).symm) hdisj.symm
      (by rw [sup_comm]; exact hYO) (by rw [sup_comm]; exact hLY) (hmap ▸ hK2)
    exact (hLle J₂ this).trans_eq h.card_eq.symm
  exfalso
  have hc₁ : ∀ k ∈ Kb, ∀ g ∈ A₁.map π, k * g = g * k := fun k hk g hg =>
    (commutatorElement_eq_one_iff_mul_comm.1
      (Subgroup.mem_bot.1 (hK1 ▸ Subgroup.commutator_mem_commutator hk hg)))
  have hc₂ : ∀ k ∈ Kb, ∀ g ∈ A₂.map π, k * g = g * k := fun k hk g hg =>
    (commutatorElement_eq_one_iff_mul_comm.1
      (Subgroup.mem_bot.1 (hK2 ▸ Subgroup.commutator_mem_commutator hk hg)))
  have hab : ∀ k ∈ Kb, ∀ k' ∈ Kb, k * k' = k' * k := by
    intro k hk k' hk'
    rw [← hmap] at hk'
    obtain ⟨ℓ, hℓ, rfl⟩ := hk'
    obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := mem_sup_of_commute hA₁₂ (hLY hℓ)
    have e1 := hc₁ k hk (π a₁) ⟨a₁, ha₁, rfl⟩
    have e2 := hc₂ k hk (π a₂) ⟨a₂, ha₂, rfl⟩
    rw [map_mul, ← mul_assoc, e1, mul_assoc, e2, mul_assoc]
  obtain ⟨-, -, a', b', hab'⟩ := hKb.1
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
  have hba : a * b = b * a := Subtype.ext (hab a a.2 b b.2)
  exact hab' (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hba])

end SplitAt

structure Split1Like (F : Type) [Field F] [Finite F] (Y : Subgroup X) (z : X) : Prop where
  z_mem : z ∈ Y
  z_ord : orderOf z = 2
  z_central : ∀ g ∈ Y, g * z = z * g
  split : ∀ u ∈ Y, orderOf u = 2 → u ≠ z → ∃ J₁ J₂ : Subgroup X, SplitAt F Y z u J₁ J₂

variable {F : Type} [Field F] [Finite F] {Y : Subgroup X} {z : X}

theorem Split1Like.map {X' : Type} [Group X'] (ι : X →* X') (hι : Function.Injective ι)
    (h : Split1Like F Y z) : Split1Like F (Y.map ι) (ι z) := by
  refine ⟨Subgroup.mem_map_of_mem ι h.z_mem, ?_, ?_, ?_⟩
  · rw [orderOf_injective ι hι z]
    exact h.z_ord
  · rintro _ ⟨g, hg, rfl⟩
    rw [← map_mul, ← map_mul, h.z_central g hg]
  · rintro _ ⟨u, hu, rfl⟩ hu2 huz
    have hu2' : orderOf u = 2 := by rwa [orderOf_injective ι hι u] at hu2
    obtain ⟨J₁, J₂, hS⟩ := h.split u hu hu2' (fun h' => huz (by rw [h']))
    exact ⟨J₁.map ι, J₂.map ι, hS.map ι hι⟩

theorem Split1Like.z_mem_centralizer (hY : Split1Like F Y z) : z ∈ centralizer (Y : Set X) :=
  Subgroup.mem_centralizer_iff.2 fun g hg => hY.z_central g hg

theorem Split1Like.centralizer_mul_eq (hY : Split1Like F Y z) (u : X) :
    centralizer ({z * u} : Set X) ⊓ Y = centralizer ({u} : Set X) ⊓ Y := by
  have hz1 : ∀ g ∈ Y, g * z = z * g := hY.z_central
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h2, hg⟩
    refine ⟨?_, hg⟩
    have h3 : z * (g * u) = z * (u * g) := by
      calc z * (g * u) = (z * g) * u := by rw [mul_assoc]
        _ = (g * z) * u := by rw [hz1 g hg]
        _ = g * (z * u) := by rw [mul_assoc]
        _ = z * u * g := h2
        _ = z * (u * g) := by rw [mul_assoc]
    exact mul_left_cancel h3
  · rintro ⟨h2, hg⟩
    refine ⟨?_, hg⟩
    calc g * (z * u) = (g * z) * u := by rw [mul_assoc]
      _ = (z * g) * u := by rw [hz1 g hg]
      _ = z * (g * u) := by rw [mul_assoc]
      _ = z * (u * g) := by rw [h2]
      _ = z * u * g := by rw [mul_assoc]

theorem Split1Like.cases_of_mem (hY : Split1Like F Y z)
    (hCY : ∀ w ∈ centralizer (Y : Set X), w = 1 ∨ w = z) {u : X} (hu : u ∈ Y)
    {J₁ J₂ : Subgroup X} (hS : SplitAt F Y z u J₁ J₂) {z' : X}
    (hz' : z' ∈ (centralizer (J₁ : Set X) ⊓ (Y ⊔ zpowers u)) ⊔ centralizer (Y : Set X))
    (hz'2 : orderOf z' = 2) : z' = z ∨ z' = u ∨ z' = z * u := by
  have hYu : Y ⊔ zpowers u = Y := sup_eq_left.2 (Subgroup.zpowers_le.2 hu)
  rw [hYu] at hz'
  have hcomm : ∀ a ∈ centralizer (J₁ : Set X) ⊓ Y, ∀ b ∈ centralizer (Y : Set X), a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.1 hb a ha.2
  obtain ⟨d, hd, w, hw, rfl⟩ := mem_sup_of_commute hcomm hz'
  have hz1 : ∀ g ∈ Y, g * z = z * g := hY.z_central
  have hzJ : ∀ j ∈ J₁, j * z = z * j := fun j hj => hz1 j (hS.le₁ hj).2
  have hdY : d ∈ Y := hd.2
  have hdJ : ∀ j ∈ J₁, d * j = j * d := fun j hj => (Subgroup.mem_centralizer_iff.1 hd.1 j hj).symm
  have hwY : w ∈ Y := by
    rcases hCY w hw with h1 | h1
    · rw [h1]; exact Y.one_mem
    · rw [h1]; exact hY.z_mem
  have hdwY : d * w ∈ Y := Y.mul_mem hdY hwY
  have hdw2 : (d * w) * (d * w) = 1 := by rw [← pow_two]; exact hz'2 ▸ pow_orderOf_eq_one _
  have hdwJ : ∀ j ∈ J₁, d * w * j = j * (d * w) := by
    intro j hj
    rcases hCY w hw with h1 | h1
    · rw [h1, mul_one]; exact hdJ j hj
    · rw [h1, mul_assoc, ← hzJ j hj, ← mul_assoc, hdJ j hj, mul_assoc]
  rcases hS.invol (d * w) hdwY hdw2 hdwJ with h1 | h1 | h1 | h1
  · exfalso
    rw [h1, orderOf_one] at hz'2
    exact absurd hz'2 (by norm_num)
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h1)

theorem Split1Like.subtermRel [Finite X] (hodd : Odd (Nat.card F)) (hbig : 4 ≤ Nat.card F)
    (hY : Split1Like F Y z) (hCY : ∀ w ∈ centralizer (Y : Set X), w = 1 ∨ w = z) {u : X} (hu : u ∈ Y)
    {J₁ J₂ : Subgroup X} (hS : SplitAt F Y z u J₁ J₂) : SubtermRel Y u J₁ := by
  refine ⟨hS.ord, Subgroup.le_normalizer hu, Or.inl ⟨hS.isPCompIn₁ hodd hbig, ?_⟩⟩
  intro z' hz' hz'2
  rcases hY.cases_of_mem hCY hu hS hz' hz'2 with h1 | h1 | h1
  · right; rw [h1]; exact hY.z_mem_centralizer
  · left; rw [h1]; exact hS.isPCompIn₁ hodd hbig
  · left; rw [h1, hY.centralizer_mul_eq]; exact hS.isPCompIn₁ hodd hbig

end SplitAt

section Models

variable {X : Type} [Group X] {F : Type} [Field F] [Finite F]

structure GrpS1 (F : Type) [Field F] [Finite F] (P : Type) [Group P] (z : P) : Prop where
  center : ∀ g : P, g ∈ Subgroup.center P ↔ g = 1 ∨ g = z
  like : Split1Like F (⊤ : Subgroup P) z
  e8 : ∀ E : Subgroup P, CFSG.IsElementaryAbelian 2 ↥E → Nat.card ↥E = 8 → z ∈ E
  exists_e8 : ∃ E : Subgroup P, CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 8

@[expose] def GrpS1.incl {Y : Subgroup X} {P : Type} [Group P] (e : ↥Y ≃* P) : P →* X :=
  Y.subtype.comp e.symm.toMonoidHom

theorem GrpS1.incl_injective {Y : Subgroup X} {P : Type} [Group P] (e : ↥Y ≃* P) :
    Function.Injective (GrpS1.incl e) :=
  Y.subtype_injective.comp e.symm.injective

theorem GrpS1.map_incl_top {Y : Subgroup X} {P : Type} [Group P] (e : ↥Y ≃* P) :
    (⊤ : Subgroup P).map (GrpS1.incl e) = Y := by
  ext g
  constructor
  · rintro ⟨p, -, rfl⟩
    exact (e.symm p).2
  · intro hg
    exact ⟨e ⟨g, hg⟩, trivial, by simp [GrpS1.incl]⟩

theorem GrpS1.equiv_central {Y : Subgroup X} {P : Type} [Group P] {z₀ : P} (hP : GrpS1 F P z₀)
    (e : ↥Y ≃* P) {z : X} (hz : z ∈ Y) (hzc : ∀ g ∈ Y, g * z = z * g) (hz2 : orderOf z = 2) :
    e ⟨z, hz⟩ = z₀ := by
  have hcen : e ⟨z, hz⟩ ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hzc g' g'.2)
  rcases (hP.center _).1 hcen with h | h
  · exfalso
    have h1 : (⟨z, hz⟩ : ↥Y) = 1 := e.injective (by rw [h, map_one])
    have h2 : z = 1 := congrArg Subtype.val h1
    rw [h2, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  · exact h

theorem GrpS1.split1Like {Y : Subgroup X} {P : Type} [Group P] {z₀ : P} (hP : GrpS1 F P z₀)
    (e : ↥Y ≃* P) {z : X} (hz : z ∈ Y) (hez : e ⟨z, hz⟩ = z₀) : Split1Like F Y z := by
  have h := hP.like.map (GrpS1.incl e) (GrpS1.incl_injective e)
  rw [GrpS1.map_incl_top e] at h
  have : GrpS1.incl e z₀ = z := by simp [GrpS1.incl, ← hez]
  rwa [this] at h

theorem GrpS1.e8_of_equiv {Y : Subgroup X} {P : Type} [Group P] {z₀ : P} (hP : GrpS1 F P z₀)
    (e : ↥Y ≃* P) {z : X} (hz : z ∈ Y) (hez : e ⟨z, hz⟩ = z₀) (E : Subgroup X) (hEY : E ≤ Y)
    (hE : CFSG.IsElementaryAbelian 2 ↥E) (hcard : Nat.card ↥E = 8) : z ∈ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E₁ : Subgroup ↥Y := E.subgroupOf Y with hE₁
  have hE₁el : CFSG.IsElementaryAbelian 2 ↥E₁ := IsElementaryAbelian.subgroupOf hEY
  set E₂ : Subgroup P := E₁.map e.toMonoidHom with hE₂
  have hE₂el : CFSG.IsElementaryAbelian 2 ↥E₂ := IsElementaryAbelian.map e.toMonoidHom
  have hE₂card : Nat.card ↥E₂ = 8 := by
    rw [hE₂, Subgroup.card_map_of_injective e.injective, hE₁,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv, hcard]
  have hz₀ := hP.e8 E₂ hE₂el hE₂card
  rw [← hez] at hz₀
  obtain ⟨g, hg, hge⟩ := hz₀
  have : g = ⟨z, hz⟩ := e.injective hge
  rw [this] at hg
  exact hg

end Models

end CFSG.GH74.Generic.BProg.B1.PilotS1
