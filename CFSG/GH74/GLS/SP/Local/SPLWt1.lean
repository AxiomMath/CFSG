module

public import CFSG.GH74.GLS.SP.Local.SPLRoot1
public import CFSG.GH74.GLS.SP.Local.SPLBasic
public import CFSG.GH74.GLS.SP.Local.SPLSetBasic
public import CFSG.GH74.GLS.SP.Local.SPLY1

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

section Generic

@[expose] def IrredUnder (H X : Subgroup G) : Prop :=
  ∀ V : Subgroup G, V ≤ X → Normalizes H V → V = ⊥ ∨ V = X

theorem IrredUnder.mono {H H' X : Subgroup G} (hH : H' ≤ H) (h : IrredUnder H' X) :
    IrredUnder H X := fun V hV hN => h V hV (fun g hg v hv => hN g (hH hg) v hv)

theorem irredUnder_conjBy {H H' A : Subgroup G} (g : G) (hA : IrredUnder H' A)
    (hg : ∀ h ∈ H', g⁻¹ * h * g ∈ H) : IrredUnder H (conjBy g A) := by
  intro V hV hN
  have key : conjBy g (conjBy g⁻¹ V) = V := by
    rw [conjBy_conjBy]
    ext x
    simp [mem_conjBy_iff]
  have hV' : conjBy g⁻¹ V ≤ A := by
    intro x hx
    rw [mem_conjBy_iff] at hx
    have := hV hx
    rw [mem_conjBy_iff] at this
    have e : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
    rwa [e] at this
  have hN' : Normalizes H' (conjBy g⁻¹ V) := by
    intro h hh x hx
    rw [mem_conjBy_iff] at hx ⊢
    have e : g⁻¹ * (h * x * h⁻¹) * (g⁻¹)⁻¹ = (g⁻¹ * h * g) * (g⁻¹ * x * (g⁻¹)⁻¹) * (g⁻¹ * h * g)⁻¹ := by
      group
    rw [e]
    exact hN _ (hg h hh) _ hx
  rcases hA _ hV' hN' with h | h
  · left
    rw [← key, h]
    ext x
    simp [mem_conjBy_iff]
  · right
    rw [← key, h]

theorem isEAb_conjBy {p : ℕ} {A : Subgroup G} (h : IsEAb p A) (g : G) : IsEAb p (conjBy g A) := by
  constructor
  · intro x hx y hy
    rw [mem_conjBy_iff] at hx hy
    have := h.1 _ hx _ hy
    have e1 : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
    have e2 : g * (y * x) * g⁻¹ = (g * y * g⁻¹) * (g * x * g⁻¹) := by group
    have h3 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by rw [e1, e2, this]
    exact mul_left_cancel (mul_right_cancel h3)
  · intro x hx
    rw [mem_conjBy_iff] at hx
    have := h.2 _ hx
    have e : (g * x * g⁻¹) ^ p = g * x ^ p * g⁻¹ := conj_pow
    rw [e] at this
    have h2 : g * x ^ p * g⁻¹ = 1 := this
    have h3 : x ^ p = 1 := by
      have : x ^ p = g⁻¹ * (g * x ^ p * g⁻¹) * g := by group
      rw [this, h2]; group
    exact h3

theorem Normalizes.commutator {H A B : Subgroup G} (hA : Normalizes H A) (hB : Normalizes H B) :
    Normalizes H ⁅A, B⁆ := by
  intro h hh x hx
  have hmap : ∀ C : Subgroup G, Normalizes H C → C.map (MulAut.conj h).toMonoidHom = C := by
    intro C hC
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using hC h hh y hy
    · intro y hy
      refine ⟨h⁻¹ * y * h, ?_, by simp [MulAut.conj_apply]; group⟩
      simpa using hC h⁻¹ (H.inv_mem hh) y hy
  have : ⁅A, B⁆.map (MulAut.conj h).toMonoidHom = ⁅A, B⁆ := by
    rw [Subgroup.map_commutator, hmap A hA, hmap B hB]
  rw [← this]
  exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

end Generic

theorem SPLNot1.H₀_le_H (D : SPLNot1 G) : D.H₀ ≤ D.H := by
  show zpowers (D.h₁ * D.h₂) ≤ D.H₁ ⊔ D.H₂
  rw [Subgroup.zpowers_le]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers _))
    (Subgroup.mem_sup_right (mem_zpowers _))

section IrredX

variable [Finite G] (D : SPLNot3 G)

omit [Finite G] in
theorem w₁_inv_conj_H₁ (h1 : SPL2Set D.toSPLNot1) :
    ∀ h ∈ D.H₁, D.w₁⁻¹ * h * D.w₁ ∈ D.H₁ := by
  intro h hh
  have e : D.w₁⁻¹ * h * D.w₁ = D.w₁ * (D.z⁻¹ * h * D.z) * D.w₁⁻¹ := by
    have h0 : D.w₁⁻¹ = D.w₁ * D.z⁻¹ := w₁_inv_eq D h1
    have hz : D.w₁ * D.w₁ = D.z := h1.w₁_sq
    have hw : D.w₁ = D.z * D.w₁⁻¹ := by rw [← hz]; group
    calc D.w₁⁻¹ * h * D.w₁ = (D.w₁ * D.z⁻¹) * h * (D.z * D.w₁⁻¹) := by rw [← h0, ← hw]
      _ = _ := by group
  rw [e]
  have hz1 : D.z ∈ D.H₁ := z_mem_H₁ D h1
  have : D.z⁻¹ * h * D.z = h := by
    have := H₁_comm D D.z⁻¹ (Subgroup.inv_mem _ hz1) h hh
    calc D.z⁻¹ * h * D.z = h * D.z⁻¹ * D.z := by rw [this]
      _ = h := by group
  rw [this, h1.w₁_inv _ hh]
  exact Subgroup.inv_mem _ hh

theorem irred_X₁_H₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    IrredUnder (zpowers D.h₁) D.X₁ := by
  obtain ⟨X, hXK, hXc, hXe, hXn, hXne, hKX, htwo, hirr, hcen⟩ :=
    sl2_rootGroups D.K₁ D.q D.p hs.prime hs.comps.sl₁ hs.odd_q hs.q_ge hs.q_pow D.z
      hs.comps.cen₁ D.h₁ D.w₁ h1.h₁_mem h1.w₁_mem h1.h₁_ord h1.w₁_sq h1.w₁_inv h1.nbhd
  have hP : IsPGroup D.p ↥D.X₁ := fun g =>
    ⟨1, by simpa using Subtype.ext (h3.X₁_eab.2 g g.2)⟩
  have hX₁ : D.X₁ = X ∨ D.X₁ = conjBy D.w₁ X :=
    htwo D.X₁ h3.X₁_le hP h3.X₁_card (fun g hg x hx => h3.H_X₁ g (H₁_le_H D hg) x hx)
  rcases hX₁ with h | h
  · rw [h]; exact hirr
  · rw [h]
    exact irredUnder_conjBy D.w₁ hirr (w₁_inv_conj_H₁ D h1)

theorem irred_X₁ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    IrredUnder D.H D.X₁ := (irred_X₁_H₁ D hs h1 h3).mono (H₁_le_H D)

theorem irred_X₂ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    IrredUnder D.H D.X₂ := by
  refine irredUnder_conjBy D.t (irred_X₁ D hs h1 h3) ?_
  intro h hh
  have := t_norm_H D hs h1 h hh
  rw [t_inv D hs] at this ⊢
  exact this


theorem irred_Y₁_H₀ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    IrredUnder D.H₀ D.Y₁ := by
  have ht := t_mul_t D hs
  have hab := h3.X₁_eab.1
  have hcomm : ∀ a ∈ D.X₁, ∀ b ∈ conjBy D.t D.X₁, a * b = b * a := fun a ha b hb =>
    hs.comps.comm a (h3.X₁_le ha) b (X₂_le_K₂ D hs h3.toSPL3X hb)
  have hY : D.Y₁ = (commDiagHom ht hab hcomm).range := by
    rw [h3.Y₁_eq]; exact commutator_eq_range ht hab hcomm
  intro V hV hVN
  let ψ := commDiagHom ht hab hcomm
  let U : Subgroup G := (V.comap ψ).map D.X₁.subtype
  have hUX : U ≤ D.X₁ := Subgroup.map_subtype_le _
  have hUN : Normalizes (zpowers D.h₁) U := by
    intro h hh u hu
    obtain ⟨u', hu'V, rfl⟩ := hu
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hh
    have hcomm12 : Commute D.h₁ D.h₂ := H₁_H₂_comm D hs h1 _ (mem_zpowers _) _ (mem_zpowers _)
    have ha : D.h₁ ^ i ∈ D.K₁ := zpow_mem h1.h₁_mem i
    have hb : D.t * D.h₁ ^ i * D.t⁻¹ ∈ D.K₂ := t_conj_K₁ D hs _ ha
    have hu1 : (u' : G) ∈ D.K₁ := h3.X₁_le u'.2
    have hv : D.t * (u' : G)⁻¹ * D.t⁻¹ ∈ D.K₂ := t_conj_K₁ D hs _ (Subgroup.inv_mem _ hu1)
    have hbu : D.t * D.h₁ ^ i * D.t⁻¹ * (u' : G) = (u' : G) * (D.t * D.h₁ ^ i * D.t⁻¹) :=
      (hs.comps.comm _ hu1 _ hb).symm
    have hbvb : D.t * D.h₁ ^ i * D.t⁻¹ * (D.t * (u' : G)⁻¹ * D.t⁻¹) * (D.t * D.h₁ ^ i * D.t⁻¹)⁻¹
        ∈ D.K₂ :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hv) (Subgroup.inv_mem _ hb)
    have hca : D.t * D.h₁ ^ i * D.t⁻¹ * (D.t * (u' : G)⁻¹ * D.t⁻¹) * (D.t * D.h₁ ^ i * D.t⁻¹)⁻¹ *
        (D.h₁ ^ i)⁻¹ = (D.h₁ ^ i)⁻¹ * (D.t * D.h₁ ^ i * D.t⁻¹ * (D.t * (u' : G)⁻¹ * D.t⁻¹) *
        (D.t * D.h₁ ^ i * D.t⁻¹)⁻¹) :=
      (hs.comps.comm _ (Subgroup.inv_mem _ ha) _ hbvb).symm
    let u'' : ↥D.X₁ := ⟨D.h₁ ^ i * (u' : G) * (D.h₁ ^ i)⁻¹,
      h3.H_X₁ _ (H₁_le_H D hh) _ u'.2⟩
    refine ⟨u'', ?_, rfl⟩
    show ψ u'' ∈ V
    have hg : D.h₁ ^ i * (D.t * D.h₁ ^ i * D.t⁻¹) ∈ D.H₀ := by
      have : D.h₁ ^ i * (D.t * D.h₁ ^ i * D.t⁻¹) = (D.h₁ * D.h₂) ^ i := by
        rw [hcomm12.mul_zpow]
        congr 1
        unfold SPLNot1.h₂
        rw [conj_zpow]
      rw [this]; exact zpow_mem (mem_zpowers _) i
    have e : ψ u'' = (D.h₁ ^ i * (D.t * D.h₁ ^ i * D.t⁻¹)) * ψ u' *
        (D.h₁ ^ i * (D.t * D.h₁ ^ i * D.t⁻¹))⁻¹ := by
      show (D.h₁ ^ i * (u' : G) * (D.h₁ ^ i)⁻¹) *
          (D.t * (D.h₁ ^ i * (u' : G) * (D.h₁ ^ i)⁻¹)⁻¹ * D.t⁻¹) =
        (D.h₁ ^ i * (D.t * D.h₁ ^ i * D.t⁻¹)) * ((u' : G) * (D.t * (u' : G)⁻¹ * D.t⁻¹)) *
          (D.h₁ ^ i * (D.t * D.h₁ ^ i * D.t⁻¹))⁻¹
      calc (D.h₁ ^ i * (u' : G) * (D.h₁ ^ i)⁻¹) *
            (D.t * (D.h₁ ^ i * (u' : G) * (D.h₁ ^ i)⁻¹)⁻¹ * D.t⁻¹)
          = D.h₁ ^ i * (u' : G) * ((D.h₁ ^ i)⁻¹ * (D.t * D.h₁ ^ i * D.t⁻¹ *
              (D.t * (u' : G)⁻¹ * D.t⁻¹) * (D.t * D.h₁ ^ i * D.t⁻¹)⁻¹)) := by group
        _ = D.h₁ ^ i * (u' : G) * (D.t * D.h₁ ^ i * D.t⁻¹ * (D.t * (u' : G)⁻¹ * D.t⁻¹) *
              (D.t * D.h₁ ^ i * D.t⁻¹)⁻¹ * (D.h₁ ^ i)⁻¹) := by rw [← hca]
        _ = D.h₁ ^ i * ((u' : G) * (D.t * D.h₁ ^ i * D.t⁻¹)) * (D.t * (u' : G)⁻¹ * D.t⁻¹) *
              (D.t * D.h₁ ^ i * D.t⁻¹)⁻¹ * (D.h₁ ^ i)⁻¹ := by group
        _ = D.h₁ ^ i * (D.t * D.h₁ ^ i * D.t⁻¹ * (u' : G)) * (D.t * (u' : G)⁻¹ * D.t⁻¹) *
              (D.t * D.h₁ ^ i * D.t⁻¹)⁻¹ * (D.h₁ ^ i)⁻¹ := by rw [← hbu]
        _ = _ := by group
    rw [e]
    exact hVN _ hg _ hu'V
  rcases irred_X₁_H₁ D hs h1 h3 U hUX hUN with h | h
  · left
    rw [eq_bot_iff]
    intro y hy
    have hy' : y ∈ D.Y₁ := hV hy
    rw [hY] at hy'
    obtain ⟨u', rfl⟩ := hy'
    have hu : (u' : G) ∈ U := ⟨u', hy, rfl⟩
    rw [h] at hu
    have : u' = 1 := Subtype.ext (Subgroup.mem_bot.mp hu)
    rw [this, map_one]; exact Subgroup.one_mem _
  · right
    apply le_antisymm hV
    rw [hY]
    rintro _ ⟨u', rfl⟩
    have hu : (u' : G) ∈ U := by rw [h]; exact u'.2
    obtain ⟨u'', hu''V, hu''⟩ := hu
    have : u'' = u' := Subtype.ext hu''
    rw [this] at hu''V
    exact hu''V

theorem irred_X₃ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    IrredUnder D.H D.X₃ := by
  refine irredUnder_conjBy (H := D.H) (H' := D.H₀) D.a (irred_Y₁_H₀ D hs h1 h3) ?_
  intro h hh
  exact SPLNot1.H₀_le_H D.toSPLNot1 (h3.a_facts.a_H₀ h hh)

theorem irred_X₄ (hs : SPLSetup D.toSPLNot0) (h1 : SPL2Set D.toSPLNot1) (h3 : SPL3M2 D) :
    IrredUnder D.H D.X₄ := by
  refine irredUnder_conjBy (H := D.H) (H' := D.H) D.w₁ (irred_X₃ D hs h1 h3) ?_
  intro h hh
  exact w₁_inv_norm_H D hs h1 h hh

end IrredX

end CFSG.GH74.GLS.SP.Local
