module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic5
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Statements
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx19

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem S_normalizes_Pz (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {x : G}
    (hxS : x ∈ S) : ∀ p ∈ Pz S z, x * p * x⁻¹ ∈ Pz S z := by
  intro p hp
  rw [hs.Pz_eq_sup hII] at hp ⊢
  let φ : G →* G := MonoidHom.mk' (fun g => x * g * x⁻¹) (by intro a b; group)
  have hle : Pof S K₁ ⊔ Pof S K₂ ≤ (Pof S K₁ ⊔ Pof S K₂).comap φ := by
    by_cases hx1 : x ∈ S1 S K₁
    · apply sup_le
      · intro q hq
        exact Subgroup.mem_sup_left (hs.S1_normalizes_P hII (Or.inl rfl) x hx1 q hq)
      · intro q hq
        exact Subgroup.mem_sup_right (hs.S1_normalizes_P hII (Or.inr rfl) x hx1 q hq)
    · obtain ⟨h1, h2⟩ := hs.swap_of_not_mem hII hxS hx1
      apply sup_le
      · intro q hq
        have hq1 : q ∈ K₁ := hq.2
        rw [← h2] at hq1
        have hP₂ : x * q * x⁻¹ ∈ Pof S K₂ :=
          Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hxS hq.1) (inv_mem hxS), mem_conjugate_iff.1 hq1⟩
        exact Subgroup.mem_sup_right hP₂
      · intro q hq
        have hq2 : q ∈ K₂ := hq.2
        rw [← h1] at hq2
        have hP₁ : x * q * x⁻¹ ∈ Pof S K₁ :=
          Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hxS hq.1) (inv_mem hxS), mem_conjugate_iff.1 hq2⟩
        exact Subgroup.mem_sup_left hP₁
  exact hle hp

theorem U_le_Pz (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    U ≤ Pz S z := by
  obtain ⟨v₁, hv₁, v₂, hv₂, huv, -, -⟩ := hs.u_decomp hII hq
  have hzP : z ∈ Pz S z := by
    rw [hs.Pz_eq_sup hII]
    exact Subgroup.mem_sup_left (hs.z_mem_P hII (Or.inl rfl))
  have huP : u ∈ Pz S z := by
    rw [hs.Pz_eq_sup hII, huv]
    exact Subgroup.mul_mem_sup hv₁.2 hv₂.2
  intro x hx
  rcases hs.U_elems x hx with h1 | h1 | h1 | h1
  · rw [h1]; exact one_mem _
  · rw [h1]; exact hzP
  · rw [h1]; exact huP
  · rw [h1]; exact mul_mem huP hzP

theorem CP_cent_U (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ c ∈ Pz S z ⊓ centralizer ({u} : Set G), ∀ x ∈ U, c * x = x * c := by
  intro c hc x hx
  have hcu : u * c = c * u := (Subgroup.mem_centralizer_iff.1 hc.2) u (Set.mem_singleton u)
  have hcz : z * c = c * z := hs.z_comm hII hc.1.1
  rcases hs.U_elems x hx with h1 | h1 | h1 | h1
  · rw [h1]; group
  · rw [h1]; exact hcz.symm
  · rw [h1]; exact hcu.symm
  · rw [h1]
    calc c * (u * z) = (c * u) * z := by group
      _ = (u * c) * z := by rw [hcu]
      _ = u * (c * z) := by group
      _ = u * (z * c) := by rw [hcz]
      _ = u * z * c := by group

theorem card_CP_u (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8) :
    Nat.card ↥(Pz S z ⊓ centralizer ({u} : Set G)) = 16 := by
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  obtain ⟨y₁, hy₁P, -, hy₁inv, -⟩ := hs.exists_y₁ hII hq hk
  have hy₁u := hs.y₁_conj_u hII hq hy₁P hy₁inv
  have hPz : Pof S K₁ ≤ Pz S z := by
    rw [hs.Pz_eq_sup hII]
    exact le_sup_left
  have hy₁Pz : y₁ ∈ Pz S z := hPz hy₁P
  have hrel : (Pz S z ⊓ centralizer ({u} : Set G)).relIndex (Pz S z) = 2 := by
    refine Basic.relIndex_eq_two_of_mul hy₁Pz ?_ ?_
    · intro h'
      have h1 : u * y₁ = y₁ * u := (Subgroup.mem_centralizer_iff.1 h'.2) u (Set.mem_singleton u)
      have h2 : y₁ * u * y₁⁻¹ = u := by
        calc y₁ * u * y₁⁻¹ = (y₁ * u) * y₁⁻¹ := rfl
          _ = (u * y₁) * y₁⁻¹ := by rw [h1]
          _ = u := by group
      rw [h2] at hy₁u
      apply hs.z_ne
      have := mul_left_cancel (a := u) (by simpa using hy₁u : u * 1 = u * z)
      exact this.symm
    · intro b hb hbn
      have hbS : b ∈ S := hb.1
      have hbu : b * u * b⁻¹ = u * z := by
        rcases hs.conj_u hII hbS with h1 | h1
        · exfalso
          apply hbn
          refine Subgroup.mem_inf.2 ⟨hb, Subgroup.mem_centralizer_iff.2 (fun x hx => ?_)⟩
          rw [Set.mem_singleton_iff] at hx
          rw [hx]
          calc u * b = (b * u * b⁻¹) * b := by rw [h1]
            _ = b * u := by group
        · exact h1
      have hbz : b * z * b⁻¹ = z := by
        rw [← hs.z_comm hII hbS]
        group
      have hy₁S : y₁ ∈ S := hy₁P.1
      have hy₁z : y₁ * z * y₁⁻¹ = z := by
        rw [← hs.z_comm hII hy₁S]
        group
      refine Subgroup.mem_inf.2 ⟨mul_mem hb hy₁Pz, Subgroup.mem_centralizer_iff.2 (fun x hx => ?_)⟩
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have h3 : (b * y₁) * u * (b * y₁)⁻¹ = u := by
        calc (b * y₁) * u * (b * y₁)⁻¹ = b * (y₁ * u * y₁⁻¹) * b⁻¹ := by group
          _ = b * (u * z) * b⁻¹ := by rw [hy₁u]
          _ = (b * u * b⁻¹) * (b * z * b⁻¹) := by group
          _ = (u * z) * z := by rw [hbu, hbz]
          _ = u := by rw [mul_assoc, hs.z_sq, mul_one]
      have h4 : (b * y₁) * u = u * (b * y₁) := by
        calc (b * y₁) * u = ((b * y₁) * u * (b * y₁)⁻¹) * (b * y₁) := by group
          _ = u * (b * y₁) := by rw [h3]
      exact h4.symm
  have hmul := Basic.card_mul_relIndex_of_le
    (inf_le_left : Pz S z ⊓ centralizer ({u} : Set G) ≤ Pz S z)
  rw [hrel] at hmul
  have hP := hs.card_P hII
  obtain ⟨e, -, -, hNN, -⟩ := hs.lemma82_core hII hq hrec
  rw [← hNN, hP8] at hP
  omega

end Setup8

theorem lemma_8_7 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ W₁ W₂ U : Subgroup G) (u h : G) (Y D : Subgroup G)
      (t w : G), Setup8 G z S K₁ K₂ W₁ W₂ U u h → Nat.card ↥(Pof S K₁) = 8 → 2 ^ 7 ≤ Nat.card ↥S →
        Concl86 z S K₁ W₂ U u h Y D t w → ∀ E₁ E₂ : Subgroup G, EData Y U E₁ E₂ →
          ∀ s ∈ Pz S z, orderOf s = 2 → s⁻¹ * u * s = u * z →
            conjugate E₁ s = E₁ ∧ conjugate E₂ s = E₂ := by
  intro G _ _ z S K₁ K₂ W₁ W₂ U u h Y D t w hs hP8 hS7 hC E₁ E₂ hE s hsP hs2 hsu
  have hsS : s ∈ S := hsP.1
  have hsq : s * s = 1 := mul_self_eq_one_of_orderOf_eq_two hs2
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hsq
  have hYS : Y ≤ S := by
    rw [hC.2.1]
    exact le_sup_left
  have hYN : ∀ x ∈ S, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := fun x hx y hy =>
    hC.2.2.1.2.2.1 x ((le_sup_left : S ≤ S ⊔ zpowers h) hx) y hy
  have hE₁sq : ∀ e ∈ E₁, e * e = 1 := fun e he => by
    have := hE.elem₁.2 e he
    simpa [pow_two] using this
  have hE₂sq : ∀ f ∈ E₂, f * f = 1 := fun f hf => by
    have := hE.elem₂.2 f hf
    simpa [pow_two] using this
  have hUE₁ : U ≤ E₁ := hE.inter ▸ inf_le_left
  have hUE₂ : U ≤ E₂ := hE.inter ▸ inf_le_right
  have hinvol : ∀ x ∈ Y, x * x = 1 → x ∈ E₁ ∨ x ∈ E₂ := by
    intro x hx hx2
    by_cases hx1 : x = 1
    · left
      rw [hx1]
      exact one_mem _
    · exact hE.invol x hx (orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1)
  have hconjY : ∀ E : Subgroup G, E ≤ Y → conjugate E s ≤ Y := by
    intro E hEY x hx
    have h1 : s * x * s⁻¹ ∈ E := mem_conjugate_iff.1 hx
    have h2 := hYN s⁻¹ (inv_mem hsS) _ (hEY h1)
    have e : s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x := by group
    rwa [e] at h2
  have hconjsq : ∀ E : Subgroup G, (∀ e ∈ E, e * e = 1) → ∀ x ∈ conjugate E s, x * x = 1 := by
    intro E hE' x hx
    have h1 := hE' _ (mem_conjugate_iff.1 hx)
    have h2 : s * (x * x) * s⁻¹ = 1 := by
      rw [show s * (x * x) * s⁻¹ = (s * x * s⁻¹) * (s * x * s⁻¹) by group]
      exact h1
    calc x * x = s⁻¹ * (s * (x * x) * s⁻¹) * s := by group
      _ = 1 := by rw [h2]; group
  have hc₁ := Basic.elem_eq_or_of_le (hconjY E₁ hE.le₁) (hconjsq E₁ hE₁sq) hinvol hE.card₁ hE.card₂
    (by rw [conjugate_card]; exact hE.card₁)
  have hc₂ := Basic.elem_eq_or_of_le (hconjY E₂ hE.le₂) (hconjsq E₂ hE₂sq) hinvol hE.card₁ hE.card₂
    (by rw [conjugate_card]; exact hE.card₂)
  have hne : E₁ ≠ E₂ := by
    intro h12
    have h1 := hE.inter
    rw [← h12, inf_idem] at h1
    have h2 := hs.U_four.2
    rw [← h1, hE.card₁] at h2
    omega
  have hinj : conjugate E₁ s ≠ conjugate E₂ s := by
    intro h12
    apply hne
    ext x
    have h1 : x ∈ E₁ ↔ s⁻¹ * x * s ∈ conjugate E₁ s := by
      rw [mem_conjugate_iff]
      have : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
      rw [this]
    have h2 : x ∈ E₂ ↔ s⁻¹ * x * s ∈ conjugate E₂ s := by
      rw [mem_conjugate_iff]
      have : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
      rw [this]
    rw [h1, h2, h12]
  have hswapcase : conjugate E₁ s = E₂ → False := by
    intro h12
    have hhm := hs.card_V₁ hII hq
    have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
    obtain ⟨y₁, hy₁P, hy₁sq, hy₁inv, -⟩ := hs.exists_y₁ hII hq hk
    obtain ⟨y₂, hy₂P, hy₂sq, hy₂inv, -⟩ := hs.exists_y₂ hII hq hrec hk
    have hyW : y₁ * y₂ ∈ Wsub S U := hs.y_mem_W hII hq hy₁P hy₂P hy₁inv hy₂inv
    have hyV₁ := hs.y_inv_V₁ hII hy₂P hy₁inv
    have hyA : y₁ * y₂ ∉ Aof S K₁ W₂ h := hs.not_mem_A_of_inv hII hq hrec hyV₁
    have hy2 : (y₁ * y₂) * (y₁ * y₂) = 1 := hs.y_sq hII hy₁P hy₂P hy₁sq hy₂sq
    have hP₁z : Pof S K₁ ≤ Pz S z := by
      rw [hs.Pz_eq_sup hII]
      exact le_sup_left
    have hP₂z : Pof S K₂ ≤ Pz S z := by
      rw [hs.Pz_eq_sup hII]
      exact le_sup_right
    have hyC : y₁ * y₂ ∈ Pz S z ⊓ centralizer ({u} : Set G) := by
      refine Subgroup.mem_inf.2 ⟨mul_mem (hP₁z hy₁P) (hP₂z hy₂P),
        Subgroup.mem_centralizer_iff.2 (fun v hv => ?_)⟩
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact ((hs.mem_W_iff hII).1 hyW).2.symm
    have hUC : U ≤ Pz S z ⊓ centralizer ({u} : Set G) := by
      refine le_inf (hs.U_le_Pz hII hq) (fun x hx => Subgroup.mem_centralizer_iff.2 (fun v hv => ?_))
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact hs.four_comm u hs.u_mem x hx
    have hswap : ∀ x, x ∈ E₂ ↔ s * x * s⁻¹ ∈ E₁ := fun x => by
      rw [← h12]
      exact mem_conjugate_iff
    have he' : ∀ e ∈ E₁, s⁻¹ * e * s ∈ E₂ := by
      intro e he
      rw [hswap]
      have : s * (s⁻¹ * e * s) * s⁻¹ = e := by group
      rw [this]
      exact he
    refine Basic.swap_contradiction (Y := Y) (E₁ := E₁) (E₂ := E₂) (U := U)
      (C := Pz S z ⊓ centralizer ({u} : Set G)) (s := s) (y := y₁ * y₂) hE.le₁ hE.le₂ hE₁sq
      hE.elem₁.1 hE.elem₂.1 hE.inter hinvol hE.comm hsq hswap
      (fun c hc => hs.U_norm s hsS c hc) hUC (hs.CP_cent_U hII) ?_ ?_ hE.card₁ hs.U_four.2
      hyC hy2 ?_
    · intro e he
      have heS : e ∈ S := hYS (hE.le₁ he)
      have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right (hE₁sq e he)
      refine Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_iff.2 (fun v hv => ?_)⟩
      · have h1 : e * (s⁻¹ * e * s) = (e * s⁻¹ * e⁻¹) * s := by
          calc e * (s⁻¹ * e * s) = (e * s⁻¹ * e) * s := by group
            _ = (e * s⁻¹ * e⁻¹) * s := by rw [heinv]
        rw [h1]
        exact mul_mem (hs.S_normalizes_Pz hII heS s⁻¹ (inv_mem hsP)) hsP
      · rw [Set.mem_singleton_iff] at hv
        rw [hv]
        have h1 := hE.elem₁.1 u (hUE₁ hs.u_mem) e he
        have h2 := hE.elem₂.1 u (hUE₂ hs.u_mem) _ (he' e he)
        calc u * (e * (s⁻¹ * e * s)) = (u * e) * (s⁻¹ * e * s) := by group
          _ = (e * u) * (s⁻¹ * e * s) := by rw [h1]
          _ = e * (u * (s⁻¹ * e * s)) := by group
          _ = e * ((s⁻¹ * e * s) * u) := by rw [h2]
          _ = (e * (s⁻¹ * e * s)) * u := by group
    · have := hs.card_CP_u hII hq hrec hP8
      omega
    · intro hyU
      apply hyA
      exact (hs.U_le_A hII hq hrec (le_refl 2) hk) hyU
  rcases hc₁ with h1 | h1
  · rcases hc₂ with h2 | h2
    · exact absurd (h1.trans h2.symm) hinj
    · exact ⟨h1, h2⟩
  · exact absurd h1 (fun h => hswapcase h)

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
