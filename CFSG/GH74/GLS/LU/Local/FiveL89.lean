module

public import CFSG.GH74.GLS.LU.Local.FiveL89a
public import CFSG.GH74.GLS.LU.Local.FiveLeaves
public import CFSG.GH74.GLS.LU.Local.FiveUtil

public section

open Subgroup CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS CFSG.GH74.GLS.LU
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

variable {G : Type} [Group G]

theorem cj_inv_eq_cjL (A : Subgroup G) (g : G) : cj A g⁻¹ = cjL g A := by
  simp [cj, cjL]

section Lemmas

variable {z t u : G} {H X₁ Y : Subgroup G} {w₁ v : G}

theorem X4_le_Y (b84 : Five84 z t u H X₁ Y v) : X4 v t X₁ ≤ Y := by
  have : cjL v (XB t X₁) ≤ cjL v (XX t X₁) := Subgroup.map_mono le_sup_right
  rwa [b84.v_X] at this

theorem EE_le_RR {K₁ K₂ : Subgroup G} (b84 : Five84 z t u H X₁ Y v)
    (b85 : Five85 z t u K₁ K₂ H w₁ X₁ Y v) : EE v t w₁ X₁ ≤ RR t X₁ := by
  have hR := b85.R_eq
  have h2 : XB t X₁ ≤ RR t X₁ := by rw [hR]; exact le_sup_left.trans le_sup_left
  have h4 : X4 v t X₁ ≤ RR t X₁ := by
    rw [hR]; exact (X4_le_Y b84).trans (le_sup_right.trans le_sup_left)
  have h6 : X6 v t w₁ X₁ ≤ RR t X₁ := by
    rw [hR]
    exact (Subgroup.map_mono (X4_le_Y b84)).trans le_sup_right
  exact sup_le (sup_le h2 h4) h6

theorem CE_z {K₁ K₂ : Subgroup G} (b84 : Five84 z t u H X₁ Y v)
    (b85 : Five85 z t u K₁ K₂ H w₁ X₁ Y v) (b87 : Five87 t H w₁ X₁ v) {e : G}
    (he : e ∈ EE v t w₁ X₁) (hz : z * e * z⁻¹ = e) : e ∈ XB t X₁ := by
  have h1 := b85.z_inv e (EE_le_RR b84 b85 he)
  rw [hz] at h1
  have h5 : e ^ 5 = 1 := b87.E_ab.2 e he
  have h3 : (e * e) ^ 3 = e := by
    calc (e * e) ^ 3 = (e ^ 2) ^ 3 := by rw [pow_two]
      _ = e ^ 5 * e := by rw [← pow_mul, show 2 * 3 = 5 + 1 from rfl, pow_succ]
      _ = e := by rw [h5, one_mul]
  rw [← h3]
  exact Subgroup.pow_mem _ h1 3

theorem CE_u {K₁ K₂ : Subgroup G} (b83 : Five83 z t u H X₁ Y) (b84 : Five84 z t u H X₁ Y v)
    (b85 : Five85 z t u K₁ K₂ H w₁ X₁ Y v) (b87 : Five87 t H w₁ X₁ v) {e : G}
    (he : e ∈ EE v t w₁ X₁) (hu : u * e * u⁻¹ = e) : e ∈ X6 v t w₁ X₁ := by
  have hX2E : XB t X₁ ≤ EE v t w₁ X₁ := le_sup_left.trans le_sup_left
  have hX4E : X4 v t X₁ ≤ EE v t w₁ X₁ := le_sup_right.trans le_sup_left
  have hcomm : ∀ a ∈ XB t X₁ ⊔ X4 v t X₁, ∀ b ∈ X6 v t w₁ X₁, a * b = b * a := by
    intro a ha b hb
    exact b87.E_ab.1 a (sup_le hX2E hX4E ha) b
      ((le_sup_right : X6 v t w₁ X₁ ≤ EE v t w₁ X₁) hb)
  obtain ⟨c, hc, x, hx, rfl⟩ := (mem_sup_of_commute hcomm).mp he
  have hcW : c ∈ XX t X₁ ⊔ Y :=
    (sup_le (le_sup_right.trans le_sup_left) ((X4_le_Y b84).trans le_sup_right)) hc
  have hxu : u * x = x * u := by
    have : x ∈ cjL w₁ Y := (by
      have h6 : X6 v t w₁ X₁ ≤ cjL w₁ Y := Subgroup.map_mono (X4_le_Y b84)
      exact h6 hx)
    rw [b85.Yw_eq] at this
    exact (Subgroup.mem_centralizer_singleton_iff.mp this.1).symm
  have h1 : u * (c * x) * u⁻¹ = c⁻¹ * x := by
    calc u * (c * x) * u⁻¹ = (u * c * u⁻¹) * (u * x * u⁻¹) := by group
      _ = c⁻¹ * x := by rw [b83.u_inv c hcW, hxu]; group
  have h2 : c⁻¹ * x = c * x := by rw [← h1, hu]
  have h3 : c⁻¹ = c := mul_right_cancel h2
  have hcE : c ∈ EE v t w₁ X₁ := (le_sup_left : XB t X₁ ⊔ X4 v t X₁ ≤ EE v t w₁ X₁) hc
  have hc5 : c ^ 5 = 1 := b87.E_ab.2 c hcE
  have hsq : c * c = 1 := mul_eq_one_iff_eq_inv.mpr h3.symm
  have hc2 : c ^ 2 = 1 := by rw [pow_two]; exact hsq
  have hc1 : c = 1 := by
    calc c = c ^ 5 * (c ^ 2)⁻¹ * (c ^ 2)⁻¹ := by group
      _ = 1 := by rw [hc5, hc2]; simp
  rw [hc1, one_mul]
  exact hx

end Lemmas

theorem leaf89 : Leaf89 := by
  intro G _ _ p f z S K₁ K₂ t u ctx H w₁ b66 X₁ b82 Y b83 v b84 b85 b86 b87 L' b88
  have hc : LUComps G (p ^ f) z K₁ K₂ := ctx.hyp.1
  have hs : LUSyl G z S K₁ K₂ t u := ctx.hyp.2.1
  have hq5 : p ^ f = 5 := ctx.pf
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard : Nat.card (ZMod 5) = p ^ f := by rw [Nat.card_zmod, hq5]
  obtain ⟨g, hg, hplace⟩ := b85.place
  obtain ⟨A, A', hAA', hX5, hX6⟩ : ∃ A A' : Subgroup G, ((A = K₁ ∧ A' = K₂) ∨ (A = K₂ ∧ A' = K₁)) ∧
      X5 v w₁ X₁ ≤ cjL g A ∧ X6 v t w₁ X₁ ≤ cjL g A' := by
    rcases hplace with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨K₁, K₂, Or.inl ⟨rfl, rfl⟩, h1, h2⟩
    · exact ⟨K₂, K₁, Or.inr ⟨rfl, rfl⟩, h1, h2⟩
  have hAsel : A = K₁ ∨ A = K₂ := hAA'.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hAp : ⁅A, A⁆ = A := by
    rcases hAA' with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hc.perfect₁
    · exact hc.perfect₂
  have hAz : ∀ a ∈ A, a * z = z * a := by
    rcases hAA' with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact fun a ha => hc.cz₁ ha
    · exact fun a ha => hc.cz₂ ha
  have hcommAA' : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a := by
    rcases hAA' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hc.comm
    · intro a ha b hb
      exact (hc.comm b hb a ha).symm
  have eA : Nonempty (SL(2, ZMod 5) ≃* ↥A) := by
    rcases hAA' with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact exists_mulEquiv_SL2 hc.sl₁ (ZMod 5) hcard
    · exact exists_mulEquiv_SL2 hc.sl₂ (ZMod 5) hcard
  have e₁ : Nonempty (SL(2, ZMod 5) ≃* ↥K₁) := exists_mulEquiv_SL2 hc.sl₁ (ZMod 5) hcard
  set L := cjL g A with hLdef
  have eL : Nonempty (SL(2, ZMod 5) ≃* ↥L) := ⟨eA.some.trans ((MulAut.conj g).subgroupMap A)⟩
  set E := EE v t w₁ X₁ with hE
  have hnorm : ∀ l ∈ L', ∀ e ∈ E, l * e * l⁻¹ ∈ E := by
    intro l hl e he
    exact ((Subgroup.mem_normalizer_iff.mp (b88.L'_N hl)) e).mp he
  have hdisj : ∀ x ∈ E, x ∈ L' → x = 1 := by
    intro x hx hx'
    have : x ∈ E ⊓ L' := ⟨hx, hx'⟩
    rw [b88.L'_disj] at this
    exact Subgroup.mem_bot.mp this
  have hzL' : z ∈ L' := b88.U_le (Subgroup.mem_sup_left (mem_zpowers z))
  have huL' : u ∈ L' := b88.U_le (Subgroup.mem_sup_right (mem_zpowers u))
  have hKN : K₁ ≤ E ⊔ L' := by rw [b88.L'_sup]; exact b88.K₁_N
  have hLN : L ≤ E ⊔ L' := by rw [b88.L'_sup]; exact b88.L_N g hg A hAsel hX5
  have hX2E : XB t X₁ ≤ E := le_sup_left.trans le_sup_left
  have hX6E : X6 v t w₁ X₁ ≤ E := le_sup_right
  have hX2K₂ : XB t X₁ ≤ K₂ := by
    have := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) b82.X₁_syl.1
    rwa [hs.t_swap] at this
  have hK₁L' : K₁ ≤ L' :=
    perfect_le_complement hnorm hdisj hKN hc.perfect₁ hzL' (fun m hm => hc.cz₁ hm)
      (fun e he hze => CE_z b84 b85 b87 he hze)
      (fun b hb b' hb' => b87.E_ab.1 b (hX2E hb) b' (hX2E hb'))
      (fun b hb m hm => (hc.comm m hm b (hX2K₂ hb)).symm)
  have hLp : ⁅L, L⁆ = L := by
    rw [hLdef]; unfold cjL
    rw [← Subgroup.map_commutator, hAp]
  have hLu : ∀ m ∈ L, m * u = u * m := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hm
    have h1 := hAz a ha
    have : (MulAut.conj g).toMonoidHom a * u = u * (MulAut.conj g).toMonoidHom a := by
      show g * a * g⁻¹ * u = u * (g * a * g⁻¹)
      rw [← hg]
      calc g * a * g⁻¹ * (g * z * g⁻¹) = g * (a * z) * g⁻¹ := by group
        _ = g * (z * a) * g⁻¹ := by rw [h1]
        _ = g * z * g⁻¹ * (g * a * g⁻¹) := by group
    exact this
  have hLL' : L ≤ L' :=
    perfect_le_complement hnorm hdisj hLN hLp huL' hLu
      (fun e he hue => CE_u b83 b84 b85 b87 he hue)
      (fun b hb b' hb' => b87.E_ab.1 b (hX6E hb) b' (hX6E hb'))
      (fun b hb m hm => by
        obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp (hX6 hb)
        obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hm
        show g * a' * g⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * (g * a' * g⁻¹)
        calc g * a' * g⁻¹ * (g * a * g⁻¹) = g * (a' * a) * g⁻¹ := by group
          _ = g * (a * a') * g⁻¹ := by rw [hcommAA' a ha a' ha']
          _ = g * a * g⁻¹ * (g * a' * g⁻¹) := by group)
  have hgen : L' ≤ K₁ ⊔ L :=
    sl3_gen b88.L'_iso hzL' huL' hs.z_inv hs.u_ord hs.u_ne.symm (hs.comm_z hs.u_mem).symm hK₁L'
      hLL' hc.perfect₁ hLp (fun m hm => hc.cz₁ hm) hLu (ZMod 5) (ZMod 5) (Nat.card_zmod 5)
      (Nat.card_zmod 5) e₁.some eL.some
  have heq : K₁ ⊔ L = L' := le_antisymm (sup_le hK₁L' hLL') hgen
  refine ⟨g⁻¹, L, ?_, ?_, ?_, ⟨b88.L'_iso.some.trans (MulEquiv.subgroupCongr heq.symm)⟩⟩
  · simpa using hg
  · rcases hAsel with h | h
    · left; rw [hLdef, h, cj_inv_eq_cjL]
    · right; rw [hLdef, h, cj_inv_eq_cjL]
  · rcases hAsel with h | h
    · rw [hLdef, h]; exact (b66.t_normL g hg).1
    · rw [hLdef, h]; exact (b66.t_normL g hg).2

end CFSG.GH74.GLS.LU.Local.Five
