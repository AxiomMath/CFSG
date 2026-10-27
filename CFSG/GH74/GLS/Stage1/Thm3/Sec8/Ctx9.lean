module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx8

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem U_le_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) : U ≤ Aof S K₁ W₂ h := by
  have hz1 : z ∈ Vof S K₁ W₂ := hs.z_mem_V₁ hII hq hk2 hk
  have hzA : z ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_left hz1
  have hz' : h⁻¹ * z * h ∈ conjugate (Vof S K₁ W₂) h := by
    rw [mem_conjugate_iff]
    have e : h * (h⁻¹ * z * h) * h⁻¹ = z := by group
    rw [e]; exact hz1
  have hz'A : h⁻¹ * z * h ∈ Aof S K₁ W₂ h := Subgroup.mem_sup_right hz'
  have hz'U : h⁻¹ * z * h ∈ U := hs.hz_inv_mem_U
  have hz'1 : h⁻¹ * z * h ≠ 1 := by
    intro h1
    apply hs.z_ne
    have e : z = h * (h⁻¹ * z * h) * h⁻¹ := by group
    rw [e, h1]; group
  have hz₁ : h⁻¹ * z * h = u ∨ h⁻¹ * z * h = u * z := by
    rcases hs.U_elems _ hz'U with h1 | h1 | h1 | h1
    · exact absurd h1 hz'1
    · exact absurd h1 hs.h_move
    · exact Or.inl h1
    · exact Or.inr h1
  intro y hy
  rcases hs.U_elems y hy with h' | h' | h' | h'
  · rw [h']; exact one_mem _
  · rw [h']; exact hzA
  · rcases hz₁ with h1 | h1
    · rw [h', ← h1]; exact hz'A
    · have e : u = (h⁻¹ * z * h) * z := by rw [h1]; simp [mul_assoc, hs.z_sq]
      rw [h', e]; exact mul_mem hz'A hzA
  · rcases hz₁ with h1 | h1
    · rw [h', ← h1]; exact mul_mem hz'A hzA
    · rw [h', ← h1]; exact hz'A

theorem cent_le_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {x : G} (hxS : x ∈ S)
    (hxc : ∀ a ∈ Aof S K₁ W₂ h, x * a = a * x) : x ∈ Aof S K₁ W₂ h := by
  have hUA := hs.U_le_A hII hq hrec hk2 hk
  have hxW : x ∈ Wsub S U :=
    ⟨hxS, Subgroup.mem_centralizer_iff.2 (fun y hy => (hxc y (hUA hy)).symm)⟩
  have hx'W : h⁻¹ * x * h ∈ Wsub S U := by
    have h1 : h * (h⁻¹ * x * h) * h⁻¹ ∈ Wsub S U := by
      have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
      rw [e]; exact hxW
    exact ((Subgroup.mem_normalizer_iff.1 hs.h_W) _).2 h1
  have hx'c : ∀ a ∈ Aof S K₁ W₂ h, (h⁻¹ * x * h) * a = a * (h⁻¹ * x * h) := by
    intro a ha
    have h1 := hxc (h * a * h⁻¹) (hs.A_conj hII hq hrec hk ha).1
    calc h⁻¹ * x * h * a = h⁻¹ * (x * (h * a * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * a * h⁻¹) * x) * h := by rw [h1]
      _ = a * (h⁻¹ * x * h) := by group
  have hp1 := hs.cent_pow hII hq hrec hk hxS hxc
  have hp2 := hs.cent_pow hII hq hrec hk hx'W.1 hx'c
  have hconj : (h⁻¹ * x * h) ^ (2 ^ k) = h⁻¹ * x ^ (2 ^ k) * h := by
    have := conj_pow (a := h⁻¹) (b := x) (i := 2 ^ k)
    rwa [inv_inv] at this
  rcases hp1 with h1 | h1
  · exact hs.cent_mem_A hII hq hrec hk hxS hxc h1
  · exfalso
    rw [hconj, h1] at hp2
    rcases hp2 with h2 | h2
    · apply hs.z_ne
      have e : z = h * (h⁻¹ * z * h) * h⁻¹ := by group
      rw [e, h2]; group
    · exact hs.h_move h2

theorem cent_eq (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    S ⊓ centralizer (Aof S K₁ W₂ h : Set G) = Aof S K₁ W₂ h := by
  obtain ⟨k, hk2, hk⟩ := hs.exists_k hII hq
  apply le_antisymm
  · rintro x ⟨hxS, hxc⟩
    exact hs.cent_le_A hII hq hrec hk2 hk hxS
      (fun a ha => ((Subgroup.mem_centralizer_iff.1 hxc) a ha).symm)
  · intro a ha
    exact ⟨hs.A_le_S hII hq hrec ha,
      Subgroup.mem_centralizer_iff.2 (fun b hb => hs.A_comm hII hq hrec b hb a ha)⟩

theorem V_conj_mem_A (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {s v : G} (hs1 : s ∈ S1 S K₁)
    (hv : v ∈ conjugate (Vof S K₁ W₂) h) : s * v * s⁻¹ ∈ Aof S K₁ W₂ h := by
  have hcard := hs.card_S1_eq hII hq hrec
  obtain ⟨hN, -⟩ := hs.nc_quot (K := K₂) (Or.inr rfl)
  obtain ⟨v', hv'V, q, hqQ, hy⟩ := Basic.conj_mem_sup (S₁ := S1 S K₁) (Q := Qof S K₂)
    (V := conjugate (Vof S K₁ W₂) h) (hs.Q₂_le_S1 hII) (hs.V₁h_le_S1 hII hq hrec)
    (hs.V₁h_inf_Q hII hq (Or.inr rfl)) hcard hs1 hv
  have hv'S1 : v' ∈ S1 S K₁ := hs.V₁h_le_S1 hII hq hrec hv'V
  have hyc : ∀ a ∈ Vof S K₁ W₂, (s * v * s⁻¹) * a = a * (s * v * s⁻¹) := by
    intro a ha
    have ha' : s⁻¹ * a * s ∈ Vof S K₁ W₂ := by
      have := hs.V₁_normal hII s⁻¹ (inv_mem hs1) a ha
      rwa [inv_inv] at this
    have key := hs.V₁V_comm hII hq hrec _ ha' v hv
    calc s * v * s⁻¹ * a = s * (v * (s⁻¹ * a * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * a * s) * v) * s⁻¹ := by rw [key]
      _ = a * (s * v * s⁻¹) := by group
  have hqeq : q = v'⁻¹ * (s * v * s⁻¹) := by rw [hy]; group
  have hqV₁ : ∀ a ∈ Vof S K₁ W₂, q * a = a * q := by
    intro a ha
    have h1 : a * v' = v' * a := hs.V₁V_comm hII hq hrec a ha v' hv'V
    have h2 := hyc a ha
    have h3 : a * v'⁻¹ = v'⁻¹ * a := (Commute.inv_right (show Commute a v' from h1)).eq
    rw [hqeq]
    calc v'⁻¹ * (s * v * s⁻¹) * a = v'⁻¹ * ((s * v * s⁻¹) * a) := by group
      _ = v'⁻¹ * (a * (s * v * s⁻¹)) := by rw [h2]
      _ = (v'⁻¹ * a) * (s * v * s⁻¹) := by group
      _ = (a * v'⁻¹) * (s * v * s⁻¹) := by rw [h3]
      _ = a * (v'⁻¹ * (s * v * s⁻¹)) := by group
  have hqW : q ∈ W₂ := hs.cent_Q₂_le_W₂ hII hq hqQ hqV₁
  have hq'W : v' * q * v'⁻¹ ∈ W₂ := hs.W₂_norm v' hv'S1 q hqW
  have hyeq : s * v * s⁻¹ = (v' * q * v'⁻¹) * v' := by rw [hy]; group
  have hyk : (s * v * s⁻¹) ^ (2 ^ k) = 1 := by
    rw [conj_pow, hs.V_pow hk v hv]; group
  have hq'V₁ : v' * q * v'⁻¹ ∈ Vof S K₁ W₂ := by
    refine Basic.mem_of_pow_mul_eq_one (z := z) (W := W₂) (V₁ := Vof S K₁ W₂)
      (V := conjugate (Vof S K₁ W₂) h) hk2 hs.W₂_max.2.1 inf_le_left hk
      (hs.W₂_sq_mem hII hq hrec hk) (hs.z_mem_V₁ hII hq hk2 hk) hs.z_sq ?_ ?_ ?_ (hs.V_pow hk)
      hq'W hv'V ?_
    · exact fun c hc hc2 => (hs.gq_Q₂ hII).uniq c (hs.W₂_le_Q₂ hc) hc2
    · exact fun v hv a ha => (hs.V₁V_comm hII hq hrec a ha v hv).symm
    · exact fun v hv w hw => hs.W₂_norm v (hs.V₁h_le_S1 hII hq hrec hv) w hw
    · rw [← hyeq]; exact hyk
  rw [hyeq]
  exact Subgroup.mul_mem_sup hq'V₁ hv'V

theorem A_normedBy_S1 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) : NormedBy (Aof S K₁ W₂ h) (S1 S K₁) := by
  intro s hs1 a ha
  obtain ⟨a₁, ha₁, a₂, ha₂, rfl⟩ := hs.A_mem hII hq hrec ha
  have e : s * (a₁ * a₂) * s⁻¹ = (s * a₁ * s⁻¹) * (s * a₂ * s⁻¹) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left (hs.V₁_normal hII s hs1 a₁ ha₁))
    (hs.V_conj_mem_A hII hq hrec hk2 hk hs1 ha₂)

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
