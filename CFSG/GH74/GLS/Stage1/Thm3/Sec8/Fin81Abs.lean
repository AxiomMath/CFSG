module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx38
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Closed4
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Gen

public section

open Equiv Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Fin81

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}
  {t : G}

theorem exists_fn_fg_of_setup (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : Nat.card ↥S = 2 ^ 7) {Sg : Subgroup G} (hSg : Sig810 S K₁ W₂ h t Sg) :
    ∃ (fn : Multiplicative V4 →* G) (fg : R0 →* G), (∀ v, fn v ∈ Aof S K₁ W₂ h) ∧
      Function.Injective fn ∧ Function.Injective fg ∧ (∀ r, fg r ∈ S ⊓ Sg) ∧
      (∀ r v, fg r * fn v * (fg r)⁻¹ = fn (ψ r v)) := by
  have hV := hs.card_V₁ hII hq
  have hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ (1 + 1) := by norm_num; omega
  have hVh := hs.V₁h_card hII hq
  have hVc : Nat.card ↥(Vof S K₁ W₂) = 4 := by omega
  have hVhc : Nat.card ↥(conjugate (Vof S K₁ W₂) h) = 4 := by omega
  have hdisj : Vof S K₁ W₂ ⊓ conjugate (Vof S K₁ W₂) h = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ conjugate (Vof S K₁ W₂) h ⊓ Qof S K₂ := ⟨hx.2, hs.P₁_le_Q₂ hII hx.1.2⟩
    rw [hs.V₁h_inf_Q hII hq (Or.inr rfl)] at this
    exact this
  obtain ⟨θ, hθinj, hθA⟩ := exists_hom_two_cyclic (Vof S K₁ W₂) (conjugate (Vof S K₁ W₂) h)
    hs.V₁_cyclic hs.V₁h_cyclic hVc hVhc (hs.V₁V_comm hII hq hrec) hdisj
  have hAdef : Aof S K₁ W₂ h = Vof S K₁ W₂ ⊔ conjugate (Vof S K₁ W₂) h := rfl
  rw [← hAdef] at hθA
  obtain ⟨hnorm, -, -, -⟩ := hs.lemma82d hII hq hrec
  have hNA := hs.N_le_normalizer_A hII hq hrec hk
  have hSgN : Sg ≤ normalizer ((Aof S K₁ W₂ h : Subgroup G) : Set G) :=
    (le_sup_right.trans hSg.2.2.1.symm.le).trans hNA
  have hkerc : ∀ σ ∈ Sg, (∀ a ∈ Aof S K₁ W₂ h, σ * a = a * σ) → σ ∈ zpowers (h ^ 3) := by
    intro σ hσ hc
    have h1 : Basic.conjHom (Aof S K₁ W₂ h) Sg hSgN ⟨σ, hσ⟩ = 1 := by
      ext a
      show σ * (a : G) * σ⁻¹ = a
      calc σ * (a : G) * σ⁻¹ = (a * σ) * σ⁻¹ := by rw [hc a a.2]
        _ = a := by group
    exact (hs.conjHom_ker_iff hII hq hrec hk hSg hSgN ⟨σ, hσ⟩).1 h1
  have hAW := hs.A_le_W hII hq hrec (le_refl _) hk
  obtain ⟨hN, ⟨e0⟩⟩ := hSg.2.2.2
  exact exists_fn_fg (Aof S K₁ W₂ h) S Sg h θ hθinj hθA (hs.A_le_S hII hq hrec) hnorm hSg.2.2.1
    hSg.2.1 hkerc hS7 (by rw [hs.card_A hII hq hrec hk]; norm_num) (hs.S_pgroup hII) hs.h_three
    (fun a ha => hs.h_cube a (hAW ha)) hN e0


theorem stageA_equiv (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hP8 : Nat.card ↥(Pof S K₁) = 8)
    (hS7 : Nat.card ↥S = 2 ^ 7) (hSg : ∃ Sg : Subgroup G, Concl810 S K₁ W₂ h t Sg) :
    Nonempty (M128 ≃* ↥S) := by
  obtain ⟨Sg, hSg⟩ := hSg
  have hSig : Sig810 S K₁ W₂ h t Sg := ⟨hSg.1, hSg.2.1, hSg.2.2.1, hSg.2.2.2.1⟩
  obtain ⟨fn, fg, hfnA, hfn, hfg, hfgS, hcomp⟩ := hs.exists_fn_fg_of_setup hII hq hrec hP8 hS7 hSig
  have hAS := hs.A_le_S hII hq hrec
  refine nonempty_mulEquiv_M128 (fn.codRestrict S (fun v => hAS (hfnA v)))
    (fg.codRestrict S (fun r => (hfgS r).1)) ?_ ?_ ?_ (by rw [hS7]; norm_num)
  · intro x y hxy
    exact hfg (congrArg Subtype.val hxy)
  · intro r v
    exact Subtype.ext (hcomp r v)
  · intro v r hvr
    have h1 : fn v = fg r := congrArg Subtype.val hvr
    have h2 : fn v ∈ Aof S K₁ W₂ h ⊓ Sg := ⟨hfnA v, h1 ▸ (hfgS r).2⟩
    rw [hSig.2.1, Subgroup.mem_bot] at h2
    exact hfn (h2.trans (map_one fn).symm)

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
