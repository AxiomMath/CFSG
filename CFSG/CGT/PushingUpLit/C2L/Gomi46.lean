module

public import CFSG.CGT.PushingUpLit.C2L.Gomi43

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2KSW
open CFSG.RankThree.PartOne (omegaOneCenterIn)
open scoped commutatorElement

section Counting

theorem card_sup_mul_card_inf {K : Type*} [Group K] [Finite K] (H N : Subgroup K) [N.Normal] :
    Nat.card ↥(H ⊔ N) * Nat.card ↥(H ⊓ N) = Nat.card H * Nat.card N := by
  have h1 := Subgroup.relIndex_sup_right H N
  have h2 := Subgroup.relIndex_mul_card N (H ⊔ N)
  have h3 := Subgroup.relIndex_mul_card N H
  rw [inf_eq_left.2 (le_sup_right : N ≤ H ⊔ N), h1] at h2
  rw [← h2, inf_comm H N, ← h3]
  ring

variable {G : Type} [Group G] [Finite G]

theorem card_mul_card_le_of_normalizer {Q Y B : Subgroup G} (hYQ : Y ≤ Q) (hBQ : B ≤ Q)
    (hn : Q ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card Y * Nat.card B ≤ Nat.card Q * Nat.card ↥(Y ⊓ B) ∧
      (Nat.card Y * Nat.card B = Nat.card Q * Nat.card ↥(Y ⊓ B) →
        ∀ q ∈ Q, ∃ y ∈ Y, ∃ b ∈ B, q = y * b) := by
  have hnorm : (B.subgroupOf Q).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hBQ).2 hn
  have hprod := card_sup_mul_card_inf (Y.subgroupOf Q) (B.subgroupOf Q)
  have cY : Nat.card ↥(Y.subgroupOf Q) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYQ).toEquiv
  have cB : Nat.card ↥(B.subgroupOf Q) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv
  have cI : Nat.card ↥(Y.subgroupOf Q ⊓ B.subgroupOf Q) = Nat.card ↥(Y ⊓ B) := by
    have e : (Y ⊓ B).subgroupOf Q = Y.subgroupOf Q ⊓ B.subgroupOf Q := Subgroup.comap_inf _ _ _
    rw [← e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hYQ)).toEquiv
  rw [cY, cB, cI] at hprod
  have hle : Nat.card ↥(Y.subgroupOf Q ⊔ B.subgroupOf Q) ≤ Nat.card ↥Q :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _)
  have hpos : 0 < Nat.card ↥(Y ⊓ B) := Nat.card_pos
  refine ⟨?_, fun heq => ?_⟩
  · rw [← hprod]
    exact Nat.mul_le_mul_right _ hle
  · have hcard : Nat.card ↥(Y.subgroupOf Q ⊔ B.subgroupOf Q) = Nat.card ↥Q := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [hprod, heq]
    have htop := Subgroup.eq_top_of_card_eq _ hcard
    intro q hq
    have hq' : (⟨q, hq⟩ : ↥Q) ∈ Y.subgroupOf Q ⊔ B.subgroupOf Q := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, b, hb, hyb⟩ := Subgroup.mem_sup_of_normal_right.1 hq'
    exact ⟨y, hy, b, hb, (congrArg Subtype.val hyb).symm⟩

theorem card_mul_card_le_of_inf_eq_bot {A C Y : Subgroup G} (hA : A ≤ Y) (hC : C ≤ Y)
    (h : A ⊓ C = ⊥) : Nat.card A * Nat.card C ≤ Nat.card Y := by
  have hinj : Function.Injective (fun p : A × C =>
      (⟨(p.1 : G) * p.2, Y.mul_mem (hA p.1.2) (hC p.2.2)⟩ : Y)) := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ heq
    have h1 : (a : G) * c = a' * c' := congrArg Subtype.val heq
    have h2 : (a' : G)⁻¹ * a = c' * (c : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * c) * (c : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * c') * (c : G)⁻¹ := by rw [h1]
        _ = c' * (c : G)⁻¹ := by group
    have hmem : (a' : G)⁻¹ * a ∈ A ⊓ C :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, h2 ▸ C.mul_mem c'.2 (C.inv_mem c.2)⟩
    rw [h] at hmem
    have h3 : (a' : G)⁻¹ * a = 1 := Subgroup.mem_bot.1 hmem
    have ha : a' = a := Subtype.ext (inv_mul_eq_one.1 h3)
    subst ha
    have : (c : G) = c' := mul_left_cancel h1
    exact Prod.ext rfl (Subtype.ext this)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod] at this

end Counting

section Omega

variable {G : Type} [Group G]

theorem omegaOneCenterIn_map_conj_eq (Q : Subgroup G) (n : G) :
    omegaOneCenterIn (Q.map (MulAut.conj n).toMonoidHom) =
      (omegaOneCenterIn Q).map (MulAut.conj n).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨hxQ, hxc, hx2⟩ := mem_omegaOneCenterIn_iff.1 hx
    obtain ⟨y, hy, rfl⟩ := hxQ
    refine ⟨y, mem_omegaOneCenterIn_iff.2 ⟨hy, fun q hq => ?_, ?_⟩, rfl⟩
    · have h1 : n * q * n⁻¹ * (n * y * n⁻¹) = n * y * n⁻¹ * (n * q * n⁻¹) :=
        hxc ((MulAut.conj n).toMonoidHom q) ⟨q, hq, rfl⟩
      have e : n * (q * y) * n⁻¹ = n * (y * q) * n⁻¹ := by
        calc n * (q * y) * n⁻¹ = n * q * n⁻¹ * (n * y * n⁻¹) := by group
          _ = n * y * n⁻¹ * (n * q * n⁻¹) := h1
          _ = n * (y * q) * n⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e)
    · have h1 : n * y * n⁻¹ * (n * y * n⁻¹) = 1 := hx2
      have e : n * (y * y) * n⁻¹ = n * 1 * n⁻¹ := by
        calc n * (y * y) * n⁻¹ = n * y * n⁻¹ * (n * y * n⁻¹) := by group
          _ = 1 := h1
          _ = n * 1 * n⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e)
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyQ, hyc, hy2⟩ := mem_omegaOneCenterIn_iff.1 hy
    refine mem_omegaOneCenterIn_iff.2 ⟨⟨y, hyQ, rfl⟩, ?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      show n * q * n⁻¹ * (n * y * n⁻¹) = n * y * n⁻¹ * (n * q * n⁻¹)
      calc n * q * n⁻¹ * (n * y * n⁻¹) = n * (q * y) * n⁻¹ := by group
        _ = n * (y * q) * n⁻¹ := by rw [hyc q hq]
        _ = n * y * n⁻¹ * (n * q * n⁻¹) := by group
    · show n * y * n⁻¹ * (n * y * n⁻¹) = 1
      calc n * y * n⁻¹ * (n * y * n⁻¹) = n * (y * y) * n⁻¹ := by group
        _ = 1 := by rw [hy2]; group

theorem card_omegaOneCenterIn_map_conj (Q : Subgroup G) (n : G) :
    Nat.card ↥(omegaOneCenterIn (Q.map (MulAut.conj n).toMonoidHom)) =
      Nat.card ↥(omegaOneCenterIn Q) := by
  rw [omegaOneCenterIn_map_conj_eq]
  exact Subgroup.card_map_of_injective (MulAut.conj n).injective

@[expose] def sqSub (A : Subgroup G) : Subgroup G := Subgroup.closure {z | ∃ a ∈ A, z = a * a}

theorem sqSub_le (A : Subgroup G) : sqSub A ≤ A := by
  refine (Subgroup.closure_le A).2 ?_
  rintro _ ⟨a, ha, rfl⟩
  exact A.mul_mem ha ha

theorem sqSub_eq_bot_iff {A : Subgroup G} : sqSub A = ⊥ ↔ ∀ a ∈ A, a * a = 1 := by
  constructor
  · intro h a ha
    have : a * a ∈ sqSub A := Subgroup.subset_closure ⟨a, ha, rfl⟩
    rw [h] at this
    exact Subgroup.mem_bot.1 this
  · intro h
    refine le_bot_iff.1 ((Subgroup.closure_le ⊥).2 ?_)
    rintro _ ⟨a, ha, rfl⟩
    rw [SetLike.mem_coe, h a ha]
    exact Subgroup.one_mem _

theorem normalizer_le_normalizer_sqSub (A : Subgroup G) :
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (sqSub A : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ z ∈ sqSub A, g * z * g⁻¹ ∈ sqSub A := by
    intro g hg z hz
    refine Subgroup.closure_induction (p := fun z _ => g * z * g⁻¹ ∈ sqSub A) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨a, ha, rfl⟩
      have ha' : g * a * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hg a).1 ha
      have : g * (a * a) * g⁻¹ = (g * a * g⁻¹) * (g * a * g⁻¹) := by group
      rw [this]
      exact Subgroup.subset_closure ⟨_, ha', rfl⟩
    · simp
    · intro x y _ _ hx hy
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact mul_mem hx hy
    · intro x _ hx
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key g hg z, fun hz => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hz
  simpa [mul_assoc] using this

end Omega

namespace Side

variable {G : Type} [Group G] [Finite G] {P P' D : Subgroup G}

theorem card_inf_mul_le (hA : GomiAmbient G) (h : Side P P' D) :
    Nat.card ↥(P ⊓ Subgroup.normalizer (D : Set G)) *
        Nat.card ↥(omegaOneCenterIn (P' ⊓ Subgroup.normalizer (D : Set G)) ⊓
          omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G))) ≤
      Nat.card D * Nat.card ↥(omegaOneCenterIn (P' ⊓ Subgroup.normalizer (D : Set G))) := by
  have hQs := h.isSylowOf_inf_normalizer
  have hQ's := h.symm.isSylowOf_inf_normalizer
  obtain ⟨x, hx, hx'⟩ := IsConcreteLE.not_le_iff_exists.1 (h.not_omega_le hA)
  obtain ⟨f, hf, hfr, hfk⟩ := h.exists_commHom hA hx hx'
  have hR : f.range ⊓ (omegaOneCenterIn (P' ⊓ Subgroup.normalizer (D : Set G)) ⊓
      omegaOneCenterIn (P ⊓ Subgroup.normalizer (D : Set G))) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun r hr => ?_
    obtain ⟨hrR, -, hrX⟩ := hr
    obtain ⟨y, rfl⟩ := hrR
    rw [hf y] at hrX ⊢
    exact h.comm_eq_one hA hx hx' y.2 hrX
  have h1 := card_mul_card_le_of_inf_eq_bot hfr inf_le_left hR
  have h2 : Nat.card ↥(P' ⊓ Subgroup.normalizer (D : Set G)) = Nat.card D * Nat.card f.range := by
    have := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hfk] at this
    have hc : Nat.card ↥(D.subgroupOf (P' ⊓ Subgroup.normalizer (D : Set G))) = Nat.card D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.symm.le_inf_normalizer).toEquiv
    rw [hc] at this
    exact this.symm
  have h3 : Nat.card ↥(P ⊓ Subgroup.normalizer (D : Set G)) =
      Nat.card ↥(P' ⊓ Subgroup.normalizer (D : Set G)) := by
    rw [hQs.card_eq, hQ's.card_eq]
  rw [h3, h2, mul_assoc]
  exact Nat.mul_le_mul_left _ h1

end Side

namespace Hyp42

variable {G : Type} [Group G] [Finite G] {P D₁ D₂ Q₁ Q₂ P₁ P₂ : Subgroup G}

theorem card_half (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hE₂ : ¬ omegaOneCenterIn Q₂ ≤ D₁) :
    Nat.card ↥(omegaOneCenterIn Q₁) * Nat.card D₂ ≤
        Nat.card ↥(P ⊓ Subgroup.normalizer (D₁ : Set G)) *
          Nat.card ↥(omegaOneCenterIn Q₁ ⊓
            omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) ∧
      Nat.card ↥(P ⊓ Subgroup.normalizer (D₁ : Set G)) *
          Nat.card ↥(omegaOneCenterIn Q₁ ⊓
            omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) ≤
        Nat.card D₁ * Nat.card ↥(omegaOneCenterIn Q₁) ∧
      (Nat.card ↥(omegaOneCenterIn Q₁) * Nat.card D₂ =
          Nat.card ↥(P ⊓ Subgroup.normalizer (D₁ : Set G)) *
            Nat.card ↥(omegaOneCenterIn Q₁ ⊓
              omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) →
        ∀ q ∈ P ⊓ Subgroup.normalizer (D₁ : Set G),
          ∃ x ∈ omegaOneCenterIn Q₁, ∃ d ∈ D₂, q = x * d) := by
  have h1 := h.side₁.side
  have h2 := h.side₂.side
  have e1 := h.side₁.eq_inf
  have hN := h.inf_normalizer_eq
  have hX₁D₁ : omegaOneCenterIn Q₁ ≤ D₁ := by
    refine h1.omega_le hA (R := Q₁) ?_
    rw [e1]
    exact h1.symm.le_inf_normalizer
  have hYQ : omegaOneCenterIn Q₁ ≤ P ⊓ Subgroup.normalizer (D₁ : Set G) :=
    hX₁D₁.trans h1.le_inf_normalizer
  have hBQ : D₂ ≤ P ⊓ Subgroup.normalizer (D₁ : Set G) := by
    rw [hN]
    exact h2.le_inf_normalizer
  have hn : P ⊓ Subgroup.normalizer (D₁ : Set G) ≤ Subgroup.normalizer (D₂ : Set G) := by
    rw [hN]
    exact inf_le_right
  obtain ⟨c1, c2⟩ := card_mul_card_le_of_normalizer hYQ hBQ hn
  rw [lemma45_one hA h hE₂] at c1 c2
  have i1 := h1.card_inf_mul_le hA
  rw [← e1] at i1
  exact ⟨c1, i1, c2⟩

theorem card_and_prod (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hE₁ : ¬ omegaOneCenterIn Q₁ ≤ D₂) (hE₂ : ¬ omegaOneCenterIn Q₂ ≤ D₁) :
    Nat.card D₁ = Nat.card D₂ ∧
      (∀ q ∈ P ⊓ Subgroup.normalizer (D₁ : Set G),
        ∃ x ∈ omegaOneCenterIn Q₁, ∃ d ∈ D₂, q = x * d) ∧
      (∀ q ∈ P ⊓ Subgroup.normalizer (D₁ : Set G),
        ∃ x ∈ omegaOneCenterIn Q₂, ∃ d ∈ D₁, q = x * d) ∧
      Nat.card ↥(P ⊓ Subgroup.normalizer (D₁ : Set G)) *
          Nat.card ↥(omegaOneCenterIn Q₁ ⊓
            omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) =
        Nat.card D₁ * Nat.card ↥(omegaOneCenterIn Q₁) ∧
      Nat.card ↥(P ⊓ Subgroup.normalizer (D₁ : Set G)) *
          Nat.card ↥(omegaOneCenterIn Q₂ ⊓
            omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) =
        Nat.card D₂ * Nat.card ↥(omegaOneCenterIn Q₂) := by
  obtain ⟨a1, a2, a3⟩ := card_half hA h hE₂
  obtain ⟨b1, b2, b3⟩ := card_half hA h.swap hE₁
  rw [← h.inf_normalizer_eq] at b1 b2 b3
  have hpos₁ : 0 < Nat.card ↥(omegaOneCenterIn Q₁) := Nat.card_pos
  have hpos₂ : 0 < Nat.card ↥(omegaOneCenterIn Q₂) := Nat.card_pos
  have hd₂₁ : Nat.card D₂ ≤ Nat.card D₁ := by
    have : Nat.card ↥(omegaOneCenterIn Q₁) * Nat.card D₂ ≤
        Nat.card ↥(omegaOneCenterIn Q₁) * Nat.card D₁ := by
      calc _ ≤ _ := a1
        _ ≤ Nat.card D₁ * Nat.card ↥(omegaOneCenterIn Q₁) := a2
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hpos₁
  have hd₁₂ : Nat.card D₁ ≤ Nat.card D₂ := by
    have : Nat.card ↥(omegaOneCenterIn Q₂) * Nat.card D₁ ≤
        Nat.card ↥(omegaOneCenterIn Q₂) * Nat.card D₂ := by
      calc _ ≤ _ := b1
        _ ≤ Nat.card D₂ * Nat.card ↥(omegaOneCenterIn Q₂) := b2
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left this hpos₂
  have hd : Nat.card D₁ = Nat.card D₂ := le_antisymm hd₁₂ hd₂₁
  have e₁ : Nat.card ↥(omegaOneCenterIn Q₁) * Nat.card D₂ =
      Nat.card ↥(P ⊓ Subgroup.normalizer (D₁ : Set G)) *
        Nat.card ↥(omegaOneCenterIn Q₁ ⊓
          omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) := by
    refine le_antisymm a1 (a2.trans (le_of_eq ?_))
    rw [hd]
    ring
  have e₂ : Nat.card ↥(omegaOneCenterIn Q₂) * Nat.card D₁ =
      Nat.card ↥(P ⊓ Subgroup.normalizer (D₁ : Set G)) *
        Nat.card ↥(omegaOneCenterIn Q₂ ⊓
          omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) := by
    refine le_antisymm b1 (b2.trans (le_of_eq ?_))
    rw [← hd]
    ring
  refine ⟨hd, a3 e₁, b3 e₂, ?_, ?_⟩
  · refine le_antisymm a2 ?_
    rw [← e₁, hd]
    ring_nf
    exact le_refl _
  · refine le_antisymm b2 ?_
    rw [← e₂, ← hd]
    ring_nf
    exact le_refl _

theorem omega₁_le (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂) :
    omegaOneCenterIn Q₁ ≤ D₁ := by
  refine h.side₁.side.omega_le hA (R := Q₁) ?_
  rw [h.side₁.eq_inf]
  exact h.side₁.side.symm.le_inf_normalizer

theorem omega_le_D₁ (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂) :
    omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) ≤ D₁ :=
  h.side₁.side.omega_le hA h.side₁.side.le_inf_normalizer

theorem omega_le_D₂ (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂) :
    omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) ≤ D₂ := by
  refine h.side₂.side.omega_le hA ?_
  rw [h.inf_normalizer_eq]
  exact h.side₂.side.le_inf_normalizer

theorem exists_mul_D₁ (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hprod₁ : ∀ q ∈ P ⊓ Subgroup.normalizer (D₁ : Set G),
      ∃ x ∈ omegaOneCenterIn Q₁, ∃ d ∈ D₂, q = x * d) :
    ∀ d ∈ D₁, ∃ x ∈ omegaOneCenterIn Q₁, ∃ δ ∈ D₁ ⊓ D₂, d = x * δ := by
  intro d hd
  obtain ⟨x, hx, d₂, hd₂, hq⟩ := hprod₁ d (h.side₁.side.le_inf_normalizer hd)
  have hd₂' : d₂ = x⁻¹ * d := by rw [hq]; group
  refine ⟨x, hx, d₂, ⟨?_, hd₂⟩, hq⟩
  rw [hd₂']
  exact D₁.mul_mem (D₁.inv_mem (h.omega₁_le hA hx)) hd

theorem sq_mem₁ (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hprod₁ : ∀ q ∈ P ⊓ Subgroup.normalizer (D₁ : Set G),
      ∃ x ∈ omegaOneCenterIn Q₁, ∃ d ∈ D₂, q = x * d) :
    ∀ d ∈ D₁, ∃ δ ∈ D₁ ⊓ D₂, d * d = δ * δ := by
  intro d hd
  obtain ⟨x, hx, δ, hδ, rfl⟩ := h.exists_mul_D₁ hA hprod₁ d hd
  refine ⟨δ, hδ, ?_⟩
  obtain ⟨-, hxc, hx2⟩ := mem_omegaOneCenterIn_iff.1 hx
  have hδQ₁ : δ ∈ Q₁ := by
    rw [h.side₁.eq_inf]
    exact h.side₁.side.symm.le_inf_normalizer hδ.1
  have hcomm : δ * x = x * δ := hxc δ hδQ₁
  calc x * δ * (x * δ) = x * (δ * x) * δ := by group
    _ = x * (x * δ) * δ := by rw [hcomm]
    _ = (x * x) * (δ * δ) := by group
    _ = δ * δ := by rw [hx2, one_mul]

theorem lemma46_sq₁ (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hE₁ : ¬ omegaOneCenterIn Q₁ ≤ D₂) (hE₂ : ¬ omegaOneCenterIn Q₂ ≤ D₁) :
    ∀ d ∈ D₁, d * d = 1 := by
  obtain ⟨-, hprod₁, hprod₂, -⟩ := card_and_prod hA h hE₁ hE₂
  have hprod₂' : ∀ q ∈ P ⊓ Subgroup.normalizer (D₂ : Set G),
      ∃ x ∈ omegaOneCenterIn Q₂, ∃ d ∈ D₁, q = x * d := by
    rw [← h.inf_normalizer_eq]
    exact hprod₂
  have h1 := h.side₁.side
  have h2 := h.side₂.side
  have e1 := h.side₁.eq_inf
  have hsq : sqSub D₁ = sqSub D₂ := by
    unfold sqSub
    congr 1
    ext z
    constructor
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨δ, hδ, hdd⟩ := h.sq_mem₁ hA hprod₁ d hd
      exact ⟨δ, hδ.2, hdd⟩
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨δ, hδ, hdd⟩ := h.swap.sq_mem₁ hA hprod₂' d hd
      exact ⟨δ, hδ.2, hdd⟩
  by_contra hcon
  have hne : sqSub D₁ ≠ ⊥ := fun hb => hcon (sqSub_eq_bot_iff.1 hb)
  obtain ⟨S, hS⟩ : ∃ S, S = sqSub D₁ := ⟨_, rfl⟩
  rw [← hS] at hne hsq
  have hSD : S ≤ D₁ := by rw [hS]; exact sqSub_le D₁
  have hn1 : Subgroup.normalizer (D₁ : Set G) ≤ Subgroup.normalizer (S : Set G) := by
    rw [hS]; exact normalizer_le_normalizer_sqSub D₁
  have hn2 : Subgroup.normalizer (D₂ : Set G) ≤ Subgroup.normalizer (S : Set G) := by
    rw [hsq]; exact normalizer_le_normalizer_sqSub D₂
  have hK : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (S : Set G)) :=
    ⟨S, hne, h1.hH.isPGroup.to_le hSD, rfl⟩
  obtain ⟨hs₁, hs₁', hle₁, hle₁'⟩ := h1.inf_le_normalizer hA hK
    (h1.lt_normalizer.trans_le (inf_le_inf_left P hn1))
    (h1.symm.lt_normalizer.trans_le (inf_le_inf_left P₁ hn1))
  obtain ⟨hs₂, hs₂', hle₂, hle₂'⟩ := h2.inf_le_normalizer hA hK
    (h2.lt_normalizer.trans_le (inf_le_inf_left P hn2))
    (h2.symm.lt_normalizer.trans_le (inf_le_inf_left P₂ hn2))
  have hOP : oTwoIn (Subgroup.normalizer (S : Set G)) ≤ P :=
    (oTwoIn_le_of_isSylowOf hs₁).trans inf_le_left
  have hOP₂ : oTwoIn (Subgroup.normalizer (S : Set G)) ≤ P₂ :=
    (oTwoIn_le_of_isSylowOf hs₂').trans inf_le_left
  have hOD₂ : oTwoIn (Subgroup.normalizer (S : Set G)) ≤ D₂ :=
    (le_inf hOP hOP₂).trans h2.inf_eq.le
  have hOQ₁ : oTwoIn (Subgroup.normalizer (S : Set G)) ≤ Q₁ := by
    rw [e1]
    exact (oTwoIn_le_of_isSylowOf hs₁').trans hle₁'
  refine hE₁ fun z hz => ?_
  obtain ⟨hzQ, hzc, -⟩ := mem_omegaOneCenterIn_iff.1 hz
  have hzK : z ∈ Subgroup.normalizer (S : Set G) := by
    rw [e1] at hzQ
    exact hn1 hzQ.2
  have hc := hA.charTwo _ hK
  rw [assembly_pCoreOf_two_eq_oTwoIn] at hc
  exact hOD₂ (hc ⟨hzK, Subgroup.mem_centralizer_iff.2 fun o ho => hzc o (hOQ₁ ho)⟩)

theorem lemma46_sq₂ (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hE₁ : ¬ omegaOneCenterIn Q₁ ≤ D₂) (hE₂ : ¬ omegaOneCenterIn Q₂ ≤ D₁) :
    ∀ d ∈ D₂, d * d = 1 :=
  lemma46_sq₁ hA h.swap hE₂ hE₁

end Hyp42

theorem abelian_of_sq {G : Type} [Group G] {A : Subgroup G} (h : ∀ a ∈ A, a * a = 1) :
    ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
  intro a ha b hb
  have hab := h (a * b) (A.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b hb)
  have := (inv_eq_of_mul_eq_one_right hab).symm
  rwa [mul_inv_rev, ha', hb'] at this

namespace Hyp42

variable {G : Type} [Group G] [Finite G] {P D₁ D₂ Q₁ Q₂ P₁ P₂ : Subgroup G}

theorem lemma46_abelian₁ (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hE₁ : ¬ omegaOneCenterIn Q₁ ≤ D₂) (hE₂ : ¬ omegaOneCenterIn Q₂ ≤ D₁) :
    ∀ a ∈ D₁, ∀ b ∈ D₁, a * b = b * a :=
  abelian_of_sq (lemma46_sq₁ hA h hE₁ hE₂)

theorem lemma46_abelian₂ (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hE₁ : ¬ omegaOneCenterIn Q₁ ≤ D₂) (hE₂ : ¬ omegaOneCenterIn Q₂ ≤ D₁) :
    ∀ a ∈ D₂, ∀ b ∈ D₂, a * b = b * a :=
  abelian_of_sq (lemma46_sq₂ hA h hE₁ hE₂)

theorem lemma46_inf (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hE₁ : ¬ omegaOneCenterIn Q₁ ≤ D₂) (hE₂ : ¬ omegaOneCenterIn Q₂ ≤ D₁) :
    D₁ ⊓ D₂ = omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) := by
  obtain ⟨-, hprod₁, -⟩ := card_and_prod hA h hE₁ hE₂
  have hs₁ := lemma46_sq₁ hA h hE₁ hE₂
  have ha₁ := lemma46_abelian₁ hA h hE₁ hE₂
  have ha₂ := lemma46_abelian₂ hA h hE₁ hE₂
  refine le_antisymm (fun δ hδ => ?_) (le_inf (h.omega_le_D₁ hA) (h.omega_le_D₂ hA))
  refine mem_omegaOneCenterIn_iff.2 ⟨h.side₁.side.le_inf_normalizer hδ.1, fun q hq => ?_,
    hs₁ δ hδ.1⟩
  obtain ⟨x, hx, d, hd, rfl⟩ := hprod₁ q hq
  have hxD₁ : x ∈ D₁ := h.omega₁_le hA hx
  calc x * d * δ = x * (d * δ) := by group
    _ = x * (δ * d) := by rw [ha₂ d hd δ hδ.2]
    _ = (x * δ) * d := by group
    _ = (δ * x) * d := by rw [ha₁ x hxD₁ δ hδ.1]
    _ = δ * (x * d) := by group

theorem lemma46_two₁' (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hE₁ : ¬ omegaOneCenterIn Q₁ ≤ D₂) (hE₂ : ¬ omegaOneCenterIn Q₂ ≤ D₁) :
    ∀ d ∈ D₁, ∃ x ∈ omegaOneCenterIn Q₁,
      ∃ y ∈ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)), d = x * y := by
  obtain ⟨-, hprod₁, -⟩ := card_and_prod hA h hE₁ hE₂
  intro d hd
  obtain ⟨x, hx, δ, hδ, hd'⟩ := h.exists_mul_D₁ hA hprod₁ d hd
  refine ⟨x, hx, δ, ?_, hd'⟩
  rw [← lemma46_inf hA h hE₁ hE₂]
  exact hδ

theorem lemma46_two₁ (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hE₁ : ¬ omegaOneCenterIn Q₁ ≤ D₂) (hE₂ : ¬ omegaOneCenterIn Q₂ ≤ D₁) :
    D₁ = omegaOneCenterIn Q₁ ⊔ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) := by
  refine le_antisymm (fun d hd => ?_) (sup_le (h.omega₁_le hA) (h.omega_le_D₁ hA))
  obtain ⟨x, hx, y, hy, rfl⟩ := lemma46_two₁' hA h hE₁ hE₂ d hd
  exact Subgroup.mul_mem_sup hx hy

theorem lemma46_four (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hE₁ : ¬ omegaOneCenterIn Q₁ ≤ D₂) (hE₂ : ¬ omegaOneCenterIn Q₂ ≤ D₁)
    {B : Subgroup G} (hB : B ≤ P ⊓ Subgroup.normalizer (D₁ : Set G))
    (hB2 : ∀ b ∈ B, b * b = 1) : B ≤ D₁ ∨ B ≤ D₂ := by
  obtain ⟨-, hprod₁, -⟩ := card_and_prod hA h hE₁ hE₂
  have hs₁ := lemma46_sq₁ hA h hE₁ hE₂
  have hs₂ := lemma46_sq₂ hA h hE₁ hE₂
  have hinf := lemma46_inf hA h hE₁ hE₂
  have h1 := h.side₁.side
  have e1 := h.side₁.eq_inf
  have hXD₂ := h.omega_le_D₂ hA
  have hC₁ : ∀ d ∈ D₁, d ∉ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) →
      ∀ q ∈ P ⊓ Subgroup.normalizer (D₁ : Set G), q * d = d * q → q ∈ D₁ := by
    intro d hd hdX q hq hqd
    obtain ⟨x₁, hx₁, δ, hδ, rfl⟩ := h.exists_mul_D₁ hA hprod₁ d hd
    have hδX : δ ∈ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) := by
      rw [← hinf]
      exact hδ
    have hx₁X : x₁ ∉ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) :=
      fun hx => hdX (mul_mem hx hδX)
    have hC : P ⊓ Subgroup.centralizer ({x₁} : Set G) = D₁ :=
      h1.symm.inf_centralizer_eq hA (by rw [← e1]; exact hx₁) hx₁X
    have hqδ : q * δ = δ * q := (mem_omegaOneCenterIn_iff.1 hδX).2.1 q hq
    have hqx₁ : q * x₁ = x₁ * q := by
      calc q * x₁ = (q * (x₁ * δ)) * δ⁻¹ := by group
        _ = ((x₁ * δ) * q) * δ⁻¹ := by rw [hqd]
        _ = x₁ * (δ * q) * δ⁻¹ := by group
        _ = x₁ * (q * δ) * δ⁻¹ := by rw [hqδ]
        _ = x₁ * q := by group
    have hmem : q ∈ P ⊓ Subgroup.centralizer ({x₁} : Set G) := by
      refine ⟨hq.1, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
      rw [Set.mem_singleton_iff.1 hz]
      exact hqx₁.symm
    rw [hC] at hmem
    exact hmem
  have hinv : ∀ t ∈ P ⊓ Subgroup.normalizer (D₁ : Set G), t * t = 1 → t ∈ D₁ ∨ t ∈ D₂ := by
    intro t ht htt
    obtain ⟨x₁, hx₁, d₂, hd₂, rfl⟩ := hprod₁ t ht
    have hx₁D₁ : x₁ ∈ D₁ := h.omega₁_le hA hx₁
    have h1' : x₁ * x₁ = 1 := hs₁ x₁ hx₁D₁
    have h2' : d₂ * d₂ = 1 := hs₂ d₂ hd₂
    have hcomm : d₂ * x₁ = x₁ * d₂ := by
      have := (inv_eq_of_mul_eq_one_right htt).symm
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h1', inv_eq_of_mul_eq_one_right h2'] at this
      exact this.symm
    by_cases hx₁X : x₁ ∈ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))
    · exact Or.inr (D₂.mul_mem (hXD₂ hx₁X) hd₂)
    · have hd₂Q : d₂ ∈ P ⊓ Subgroup.normalizer (D₁ : Set G) := by
        rw [h.inf_normalizer_eq]
        exact h.side₂.side.le_inf_normalizer hd₂
      have hd₂D₁ : d₂ ∈ D₁ := hC₁ x₁ hx₁D₁ hx₁X d₂ hd₂Q hcomm
      exact Or.inl (D₁.mul_mem hx₁D₁ hd₂D₁)
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨b₁, hb₁B, hb₁D₁⟩ := IsConcreteLE.not_le_iff_exists.1 hcon.1
  obtain ⟨b₂, hb₂B, hb₂D₂⟩ := IsConcreteLE.not_le_iff_exists.1 hcon.2
  have hb₁D₂ : b₁ ∈ D₂ := (hinv b₁ (hB hb₁B) (hB2 b₁ hb₁B)).resolve_left hb₁D₁
  have hb₂D₁ : b₂ ∈ D₁ := (hinv b₂ (hB hb₂B) (hB2 b₂ hb₂B)).resolve_right hb₂D₂
  have hb₁₂ := B.mul_mem hb₁B hb₂B
  rcases hinv (b₁ * b₂) (hB hb₁₂) (hB2 _ hb₁₂) with hm | hm
  · apply hb₁D₁
    have := D₁.mul_mem hm (D₁.inv_mem hb₂D₁)
    simpa using this
  · apply hb₂D₂
    have := D₂.mul_mem (D₂.inv_mem hb₁D₂) hm
    simpa using this

theorem card_omega₁_eq (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂) :
    Nat.card ↥(omegaOneCenterIn Q₁) =
      Nat.card ↥(omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) := by
  obtain ⟨n, -, hn⟩ := exists_eq_map_conj_of_isSylowOf h.side₁.side.isSylowOf_inf_normalizer
    h.side₁.side.symm.isSylowOf_inf_normalizer
  rw [h.side₁.eq_inf, hn]
  exact card_omegaOneCenterIn_map_conj _ n

theorem card_omega₂_eq (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂) :
    Nat.card ↥(omegaOneCenterIn Q₂) =
      Nat.card ↥(omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) := by
  have := h.swap.card_omega₁_eq
  rwa [← h.inf_normalizer_eq] at this

theorem lemma46_card (hA : GomiAmbient G) (h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂)
    (hE₁ : ¬ omegaOneCenterIn Q₁ ≤ D₂) (hE₂ : ¬ omegaOneCenterIn Q₂ ≤ D₁) :
    Nat.card D₁ = Nat.card D₂ ∧
      Nat.card ↥(P ⊓ Subgroup.normalizer (D₁ : Set G)) *
          Nat.card ↥(omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) ⊓
            omegaOneCenterIn Q₁) =
        Nat.card D₁ * Nat.card ↥(omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) ∧
      Nat.card ↥(P ⊓ Subgroup.normalizer (D₁ : Set G)) *
          Nat.card ↥(omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) ⊓
            omegaOneCenterIn Q₂) =
        Nat.card D₂ * Nat.card ↥(omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) := by
  obtain ⟨hd, -, -, hc₁, hc₂⟩ := card_and_prod hA h hE₁ hE₂
  refine ⟨hd, ?_, ?_⟩
  · rw [inf_comm (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) (omegaOneCenterIn Q₁),
      hc₁, h.card_omega₁_eq]
  · rw [inf_comm (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) (omegaOneCenterIn Q₂),
      hc₂, h.card_omega₂_eq]

end Hyp42

theorem eq_of_card_relations {rX rQ a c d e : ℕ} (hd : 0 < d) (hc : 0 < c) (hX : rX * c = a)
    (hQ : rQ * d = e) (h : e * c = d * a) : rX = rQ := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hd hc)
  calc rX * (d * c) = d * (rX * c) := by ring
    _ = d * a := by rw [hX]
    _ = e * c := h.symm
    _ = rQ * d * c := by rw [hQ]
    _ = rQ * (d * c) := by ring

section Pair

variable {G : Type} [Group G] [Finite G] {P D₁ D₂ : Subgroup G}

theorem exists_isOtherSylow {D : Subgroup G} (hD : GomiD P D) : ∃ Q, IsOtherSylow P D Q := by
  have hnc := hD.1.1.not_twoClosed
  rw [twoClosed_iff_forall_eq] at hnc
  push Not at hnc
  obtain ⟨S₁, S₂, hS₁, hS₂, hne⟩ := hnc
  by_cases h1 : S₁ = P ⊓ Subgroup.normalizer (D : Set G)
  · exact ⟨S₂, hS₂, fun h2 => hne (h1.trans h2.symm)⟩
  · exact ⟨S₁, hS₁, h1⟩

theorem exists_hyp42 (hP : IsSylowOf 2 P ⊤) (hE : GomiE P D₁ D₂) :
    ∃ Q₁ Q₂ P₁ P₂ : Subgroup G, Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂ := by
  obtain ⟨Q₁, hQ₁⟩ := exists_isOtherSylow hE.1
  obtain ⟨Q₂, hQ₂⟩ := exists_isOtherSylow hE.2.1
  obtain ⟨P₁, hP₁, hQP₁⟩ := exists_isSylowOf_ge (le_top : Q₁ ≤ ⊤) hQ₁.1.isPGroup
  obtain ⟨P₂, hP₂, hQP₂⟩ := exists_isSylowOf_ge (le_top : Q₂ ≤ ⊤) hQ₂.1.isPGroup
  exact ⟨Q₁, Q₂, P₁, P₂, ⟨hP, hE, hQ₁, hQ₂, hP₁, hQP₁, hP₂, hQP₂⟩⟩

theorem GomiE'.isElemAbelian₁ (hA : GomiAmbient G) (hP : IsSylowOf 2 P ⊤)
    (hE : GomiE' P D₁ D₂) : CFSG.Open.IsElemAbelian 2 D₁ := by
  obtain ⟨Q₁, Q₂, P₁, P₂, h⟩ := exists_hyp42 hP hE.1
  obtain ⟨h1, h2⟩ := hE.2 Q₁ Q₂ h.other₁ h.other₂
  have hs := h.lemma46_sq₁ hA h1 h2
  have hab := h.lemma46_abelian₁ hA h1 h2
  refine ⟨⟨⟨fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact hs x hx

theorem GomiE'.sup_eq (hA : GomiAmbient G) (hP : IsSylowOf 2 P ⊤) (hE : GomiE' P D₁ D₂) :
    D₁ ⊔ D₂ = P ⊓ Subgroup.normalizer (D₁ : Set G) := by
  obtain ⟨Q₁, Q₂, P₁, P₂, h⟩ := exists_hyp42 hP hE.1
  obtain ⟨h1, h2⟩ := hE.2 Q₁ Q₂ h.other₁ h.other₂
  obtain ⟨-, hprod₁, -⟩ := h.card_and_prod hA h1 h2
  refine le_antisymm (sup_le h.side₁.side.le_inf_normalizer ?_) (fun q hq => ?_)
  · rw [h.inf_normalizer_eq]
    exact h.side₂.side.le_inf_normalizer
  · obtain ⟨x, hx, d, hd, rfl⟩ := hprod₁ q hq
    exact (D₁ ⊔ D₂).mul_mem ((le_sup_left : D₁ ≤ D₁ ⊔ D₂) (h.omega₁_le hA hx))
      ((le_sup_right : D₂ ≤ D₁ ⊔ D₂) hd)

theorem GomiE'.two₁ (hA : GomiAmbient G) (hP : IsSylowOf 2 P ⊤) (hE : GomiE' P D₁ D₂)
    {Q₁ : Subgroup G} (hQ₁ : IsOtherSylow P D₁ Q₁) :
    D₁ = omegaOneCenterIn Q₁ ⊔ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) := by
  obtain ⟨Q₂, hQ₂⟩ := exists_isOtherSylow hE.1.2.1
  obtain ⟨P₁, hP₁, hQP₁⟩ := exists_isSylowOf_ge (le_top : Q₁ ≤ ⊤) hQ₁.1.isPGroup
  obtain ⟨P₂, hP₂, hQP₂⟩ := exists_isSylowOf_ge (le_top : Q₂ ≤ ⊤) hQ₂.1.isPGroup
  have h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂ := ⟨hP, hE.1, hQ₁, hQ₂, hP₁, hQP₁, hP₂, hQP₂⟩
  obtain ⟨h1, h2⟩ := hE.2 Q₁ Q₂ hQ₁ hQ₂
  exact h.lemma46_two₁ hA h1 h2

theorem GomiE'.relIndex₁ (hA : GomiAmbient G) (hP : IsSylowOf 2 P ⊤) (hE : GomiE' P D₁ D₂)
    {Q₁ : Subgroup G} (hQ₁ : IsOtherSylow P D₁ Q₁) :
    (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) ⊓ omegaOneCenterIn Q₁).relIndex
        (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G))) =
      D₁.relIndex (P ⊓ Subgroup.normalizer (D₁ : Set G)) := by
  obtain ⟨Q₂, hQ₂⟩ := exists_isOtherSylow hE.1.2.1
  obtain ⟨P₁, hP₁, hQP₁⟩ := exists_isSylowOf_ge (le_top : Q₁ ≤ ⊤) hQ₁.1.isPGroup
  obtain ⟨P₂, hP₂, hQP₂⟩ := exists_isSylowOf_ge (le_top : Q₂ ≤ ⊤) hQ₂.1.isPGroup
  have h : Hyp42 P D₁ D₂ Q₁ Q₂ P₁ P₂ := ⟨hP, hE.1, hQ₁, hQ₂, hP₁, hQP₁, hP₂, hQP₂⟩
  obtain ⟨h1, h2⟩ := hE.2 Q₁ Q₂ hQ₁ hQ₂
  obtain ⟨-, hc, -⟩ := h.lemma46_card hA h1 h2
  have hX := Subgroup.relIndex_mul_card
    (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) ⊓ omegaOneCenterIn Q₁)
    (omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)))
  have hQ := Subgroup.relIndex_mul_card D₁ (P ⊓ Subgroup.normalizer (D₁ : Set G))
  rw [inf_of_le_left (inf_le_left : omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) ⊓
    omegaOneCenterIn Q₁ ≤ omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)))] at hX
  rw [inf_of_le_left h.side₁.side.le_inf_normalizer] at hQ
  have hd : 0 < Nat.card D₁ := Nat.card_pos
  have hcpos : 0 < Nat.card ↥(omegaOneCenterIn (P ⊓ Subgroup.normalizer (D₁ : Set G)) ⊓
    omegaOneCenterIn Q₁) := Nat.card_pos
  exact eq_of_card_relations hd hcpos hX hQ hc

theorem GomiE'.four (hA : GomiAmbient G) (hP : IsSylowOf 2 P ⊤) (hE : GomiE' P D₁ D₂)
    {B : Subgroup G} (hB : B ≤ P ⊓ Subgroup.normalizer (D₁ : Set G))
    (hB2 : ∀ b ∈ B, b * b = 1) : B ≤ D₁ ∨ B ≤ D₂ := by
  obtain ⟨Q₁, Q₂, P₁, P₂, h⟩ := exists_hyp42 hP hE.1
  obtain ⟨h1, h2⟩ := hE.2 Q₁ Q₂ h.other₁ h.other₂
  exact h.lemma46_four hA h1 h2 hB hB2

end Pair

end CFSG.CGT.PushingUpLit.C2L
