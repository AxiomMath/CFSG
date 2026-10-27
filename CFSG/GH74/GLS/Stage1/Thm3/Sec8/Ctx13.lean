module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx12

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem lemma83b (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (h16 : 16 ≤ Nat.card ↥(Pof S K₁)) :
    (Pz S z).relIndex (S1 S K₁) = 2 ∧ Qof S K₁ = Pof S K₂ ∧ Qof S K₂ = Pof S K₁ := by
  obtain ⟨e, he, hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have he1 : e = 1 := by
    rcases he with rfl | rfl
    · rfl
    · exfalso
      obtain ⟨k, hk2, hk⟩ := hs.exists_k hII hq
      obtain ⟨hk', -, -⟩ := hs.k_eq_two_of_e2 hII hq hrec hq2 hk2 hk
      subst hk'
      have h1 := hs.card_V₁ hII hq
      omega
  subst he1
  refine ⟨by omega, ?_, (hs.Q₂_eq_P₁_of_e_one hII hq2).symm⟩
  exact (Subgroup.eq_of_le_of_card_ge (hs.P₂_le_Q₁ hII) (by rw [hq1, one_mul])).symm

theorem lemma83a₂ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hne : Qof S K₂ ≠ Pof S K₁) :
    S ⊓ centralizer (W₂ : Set G) = W₂ ⊔ Pof S K₂ := by
  obtain ⟨e, he, hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have he2 : e = 2 := by
    rcases he with rfl | rfl
    · exact absurd (hs.Q₂_eq_P₁_of_e_one hII hq2).symm hne
    · rfl
  subst he2
  obtain ⟨k, hk2, hk⟩ := hs.exists_k hII hq
  obtain ⟨hk', hEq, hC16⟩ := hs.k_eq_two_of_e2 hII hq hrec hq2 hk2 hk
  subst hk'
  have hcomm : ∀ a ∈ W₂, ∀ b ∈ Pof S K₂, a * b = b * a :=
    fun a ha b hb => hs.Q_comm_P hII (Or.inr rfl) a (hs.W₂_le_Q₂ ha) b hb
  have hle : W₂ ⊔ Pof S K₂ ≤ S ⊓ centralizer (W₂ : Set G) := by
    apply sup_le
    · intro a ha
      exact Subgroup.mem_inf.2 ⟨(hs.W₂_le_Q₂ ha).1,
        Subgroup.mem_centralizer_iff.2 (fun y hy => Basic.cyclic_comm hs.W₂_max.2.1 y hy a ha)⟩
    · intro b hb
      exact Subgroup.mem_inf.2 ⟨hb.1,
        Subgroup.mem_centralizer_iff.2 (fun y hy => hcomm y hy b hb)⟩
  have h1 := M.card_sup_mul_card_inf (A := W₂) (B := Pof S K₂) (M.le_normalizer_of_commute hcomm)
  have hle2 : W₂ ⊓ Pof S K₂ ≤ zpowers z := by
    intro x hx
    have : x ∈ Qof S K₁ ⊓ Qof S K₂ := ⟨hs.P₂_le_Q₁ hII hx.2, hs.W₂_le_Q₂ hx.1⟩
    rwa [hs.Q_inf_Q hII] at this
  have h2 : Nat.card ↥(W₂ ⊓ Pof S K₂) ≤ 2 := by
    have := Subgroup.card_le_of_le hle2
    rwa [M.card_zpowers_of_sq hs.z_sq hs.z_ne] at this
  have hV := hs.card_V₁ hII hq
  have hW := hs.card_W₂ hII
  have hP : Nat.card ↥(Pof S K₁) = 8 := by omega
  have hW8 : Nat.card ↥W₂ = 8 := by omega
  have hP₂ : Nat.card ↥(Pof S K₂) = 8 := by omega
  rw [hW8, hP₂] at h1
  have h3 : 32 ≤ Nat.card ↥(W₂ ⊔ Pof S K₂) := by
    have := Nat.mul_le_mul_left (Nat.card ↥(W₂ ⊔ Pof S K₂)) h2
    omega
  have hD₂S : S ⊓ centralizer (W₂ : Set G) ≤ S := inf_le_left
  have hC₂ : Wsub S U ⊓ (S ⊓ centralizer (W₂ : Set G)) = Wsub S U ⊓ centralizer (W₂ : Set G) := by
    ext x
    constructor
    · intro hx; exact ⟨hx.1, hx.2.2⟩
    · intro hx; exact ⟨hx.1, hx.1.1, hx.2⟩
  have h4 := Basic.card_mul_relIndex_of_le (A := Wsub S U ⊓ (S ⊓ centralizer (W₂ : Set G)))
    (B := S ⊓ centralizer (W₂ : Set G)) inf_le_right
  have h5 : (Wsub S U ⊓ (S ⊓ centralizer (W₂ : Set G))).relIndex (S ⊓ centralizer (W₂ : Set G)) =
      (Wsub S U).relIndex (S ⊓ centralizer (W₂ : Set G)) := Subgroup.inf_relIndex_right _ _
  have h6 : (Wsub S U).relIndex (S ⊓ centralizer (W₂ : Set G)) ≤ (Wsub S U).relIndex S :=
    Subgroup.relIndex_le_of_le_right hD₂S (Basic.relIndex_ne_zero' _ _)
  have h7 := hs.relIndex_W_le_two hII
  rw [h5, hC₂] at h4
  have h8 : Nat.card ↥(S ⊓ centralizer (W₂ : Set G)) ≤ 32 := by
    calc Nat.card ↥(S ⊓ centralizer (W₂ : Set G))
        = Nat.card ↥(Wsub S U ⊓ centralizer (W₂ : Set G)) *
            (Wsub S U).relIndex (S ⊓ centralizer (W₂ : Set G)) := h4.symm
      _ ≤ 16 * 2 := Nat.mul_le_mul hC16 (h6.trans h7)
      _ = 32 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

theorem lemma83a₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hne : Qof S K₂ ≠ Pof S K₁) :
    S ⊓ centralizer (W₁ : Set G) = W₁ ⊔ Pof S K₁ := by
  have hS2 := hs.lemma83a₂ hII hq hrec hne
  obtain ⟨t, htS, htn⟩ : ∃ t ∈ S, t ∉ S1 S K₁ := by
    by_contra hcon
    push Not at hcon
    exact hs.S_ne_S1 hII hq hrec hne (le_antisymm (fun x hx => hcon x hx) S1_le_S)
  obtain ⟨e, he, hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have he2 : e = 2 := by
    rcases he with rfl | rfl
    · exact absurd (hs.Q₂_eq_P₁_of_e_one hII hq2).symm hne
    · rfl
  subst he2
  obtain ⟨k, hk2, hk⟩ := hs.exists_k hII hq
  obtain ⟨hk', -, -⟩ := hs.k_eq_two_of_e2 hII hq hrec hq2 hk2 hk
  subst hk'
  have hV := hs.card_V₁ hII hq
  have h16 : 16 ≤ Nat.card ↥(Qof S K₁) := by omega
  have hD := hs.conj_W₂_eq_W₁ hII hq hrec h16 htS htn
  have hcomm : ∀ a ∈ W₂, ∀ b ∈ Pof S K₂, a * b = b * a :=
    fun a ha b hb => hs.Q_comm_P hII (Or.inr rfl) a (hs.W₂_le_Q₂ ha) b hb
  apply le_antisymm
  · intro x hx
    have hxS : x ∈ S := hx.1
    have hxc : ∀ y ∈ W₁, y * x = x * y := fun y hy => (Subgroup.mem_centralizer_iff.1 hx.2) y hy
    have hx' : t⁻¹ * x * t ∈ S ⊓ centralizer (W₂ : Set G) := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem htS) hxS) htS,
        Subgroup.mem_centralizer_iff.2 (fun y hy => ?_)⟩
      have hty : t * y * t⁻¹ ∈ W₁ := by
        rw [← hD, mem_conjugate_iff]
        have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
        rw [e]; exact hy
      have key := hxc _ hty
      calc y * (t⁻¹ * x * t) = t⁻¹ * ((t * y * t⁻¹) * x) * t := by group
        _ = t⁻¹ * (x * (t * y * t⁻¹)) * t := by rw [key]
        _ = (t⁻¹ * x * t) * y := by group
    rw [hS2] at hx'
    obtain ⟨a, ha, b, hb, hab⟩ := Basic.mem_sup_of_commute' hcomm hx'
    have hxe : x = (t * a * t⁻¹) * (t * b * t⁻¹) := by
      have e1 : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
      rw [e1, hab]; group
    rw [hxe]
    refine Subgroup.mul_mem_sup ?_ (hs.swap_P₂ hII htS htn hb)
    rw [← hD, mem_conjugate_iff]
    have e : t⁻¹ * (t * a * t⁻¹) * t⁻¹⁻¹ = a := by group
    rw [e]; exact ha
  · apply sup_le
    · intro a ha
      exact Subgroup.mem_inf.2 ⟨(hs.W₁_le_Q₁ ha).1,
        Subgroup.mem_centralizer_iff.2 (fun y hy => Basic.cyclic_comm hs.W₁_max.2.1 y hy a ha)⟩
    · intro b hb
      exact Subgroup.mem_inf.2 ⟨hb.1, Subgroup.mem_centralizer_iff.2
        (fun y hy => hs.Q_comm_P hII (Or.inl rfl) y (hs.W₁_le_Q₁ hy) b hb)⟩

theorem lemma83a (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hne : Qof S K₂ ≠ Pof S K₁) :
    S ⊓ centralizer (W₁ : Set G) = W₁ ⊔ Pof S K₁ ∧
      S ⊓ centralizer (W₂ : Set G) = W₂ ⊔ Pof S K₂ :=
  ⟨hs.lemma83a₁ hII hq hrec hne, hs.lemma83a₂ hII hq hrec hne⟩

end Setup8

theorem lemma_8_3 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G),
      Setup8 G z S K₁ K₂ W₁ W₂ U u h →
        (Qof S K₂ ≠ Pof S K₁ →
          S ⊓ centralizer (W₁ : Set G) = W₁ ⊔ Pof S K₁ ∧ S ⊓ centralizer (W₂ : Set G) = W₂ ⊔ Pof S K₂) ∧
        (16 ≤ Nat.card ↥(Pof S K₁) →
          (Pz S z).relIndex (S1 S K₁) = 2 ∧ Qof S K₁ = Pof S K₂ ∧ Qof S K₂ = Pof S K₁) := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h hs
  exact ⟨fun hne => Setup8.lemma83a hII hq hrec hs hne, fun h16 => Setup8.lemma83b hII hq hrec hs h16⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
