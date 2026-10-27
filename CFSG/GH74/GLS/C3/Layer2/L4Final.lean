module

public import CFSG.GH74.GLS.C3.Layer2.Final
public import CFSG.GH74.GLS.C3.Layer2.L4Cv7
public import CFSG.GH74.GLS.C3.Layer2.L4ModelE2Check
public import CFSG.GH74.GLS.C3.Layer2.L4ModelE3Check
public import CFSG.GH74.Uniqueness.Section165GapFinal

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model
  CFSG.GH74.GLS.C3.Layer2.L4

theorem cent6_of_hcard
    {n : ℕ} [NeZero n] (hn : n = 6) (α : ↥(T0 n) ≃* ↥(T0 n))
    (E : Subgroup ↥(T0 n)) (hvE : vHat n α ∈ E)
    (hcard : Nat.card ↥(Hgrp n ((vHat n α : ↥(T0 n)) : Amb n)) = 64) :
    ∀ g ∈ Fgrp n, (∀ e ∈ liftT n E, g * e = e * g) → g ∈ T0 n := by
  intro g hgF hgc
  have hz : ((vHat n α : ↥(T0 n)) : Amb n) ∈ liftT n E := ⟨vHat n α, hvE, rfl⟩
  have hgH : g ∈ Hgrp n ((vHat n α : ↥(T0 n)) : Amb n) :=
    ⟨hgF, Subgroup.mem_centralizer_singleton_iff.2 (hgc _ hz)⟩
  have hle : T0 n ≤ Hgrp n ((vHat n α : ↥(T0 n)) : Amb n) := by
    intro t ht
    refine ⟨T0_le_Fgrp n ht, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (vHat_comm α ⟨t, ht⟩)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, card_T0 n (Or.inl hn)])
  rw [← heq] at hgH
  exact hgH

theorem exists_equiv_centralizer_v_of_config
    (hZD : CFSG.GH74.Uniqueness.S_ZD)
    {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}
    (hn : n = 6 ∨ n = 7) (h : IsAConfig n x K T Q S a)
    (hG : IsSimpleGroup G) (hnab : ∃ u w : G, u * w ≠ w * u)
    (hnt : ∃ t ∈ T, ∃ q ∈ Q, t * q ≠ q * t)
    (hW2 : ∀ q ∈ Q, q ≠ 1 → (Nat.card ↥(centralizer ({q} : Set G))).factorization 2 ≤
      (Nat.card ↥(centralizer ({x} : Set G))).factorization 2) :
    ∃ v' : alternatingGroup (Fin (n + 4)), orderOf v' = 2 ∧
      numMoved (v' : Equiv.Perm (Fin (n + 4))) = 8 ∧
      Nonempty (↥(centralizer ({x * (a * x * a⁻¹)} : Set G)) ≃*
        ↥(centralizer ({v'} : Set (alternatingGroup (Fin (n + 4)))))) := by
  have hn' : NeZero n := ⟨by rcases hn with rfl | rfl <;> norm_num⟩
  obtain ⟨ι, hι1, hιQ, hιT⟩ := h.exists_equiv_Fgrp_T0 hn hnt
  let c : Coord h := ⟨ι, hι1, hιQ, hιT⟩
  have hM := c.modelIso hn hW2
  have hclX : ∀ s t : ↥(T0 n), orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = c.alpha s) →
      s ∈ c.XSet → t ∈ c.XSet := fun s t _ hst hs =>
    (c.isConj_of_model s t hst).symm.trans hs
  have hclV : ∀ s t : ↥(T0 n), orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = c.alpha s) →
      s ∈ c.VSet → t ∈ c.VSet := fun s t _ hst hs =>
    (c.isConj_of_model s t hst).symm.trans hs
  obtain ⟨E, hEmem, hEcard, hEcomm, hEsq, hETn, hEα, hED, hEσ, hEhc⟩ :=
    model_E1 n hn c.alpha c.uElt c.XSet c.VSet c.alpha_x0T_ne c.alpha_uElt c.alpha_alpha
      (fun _ => c.hext) c.x0T_mem_XSet c.x0T_mul_alpha_mem_VSet (c.disjoint_XV hn) hclX hclV
      (c.hQ_model hn hW2)
  have hE1 : E1Pkg n c.alpha c.XSet c.VSet E :=
    ⟨hEmem, hEcard, hEcomm, hEsq, hETn, hEα, hED, hEσ, hEhc⟩
  obtain ⟨A, hAmem, hAcard, hAcomm, hAsq, hb, hsplit, hzc⟩ :=
    model_E2 n hn c.alpha c.uElt c.XSet c.VSet c.alpha_x0T_ne c.alpha_uElt c.alpha_alpha
      (fun _ => c.hext) c.x0T_mem_XSet c.x0T_mul_alpha_mem_VSet (c.disjoint_XV hn) hclX hclV
      (c.hQ_model hn hW2) E hEmem
  have hvE : vHat n c.alpha ∈ E := (hEmem _).2 (Or.inr (Or.inl rfl))
  have hE2 : E2Pkg n c.alpha c.uElt c.XSet E A :=
    ⟨hAmem, hAcard, hAcomm, hAsq,
      fun hn6 => cent6_of_hcard hn6 c.alpha E hvE (by rw [hEhc]; simp [hn6]), hb, hsplit, hzc⟩
  rcases hn with rfl | rfl
  · exact exists_equiv_centralizer_v6 c hE1 hE2 hZD rfl hG hnab hM
  · have hE3 : ∀ b : Fin 4 → ↥(T0 7), Function.Injective b →
        (∀ i, b i ∈ A ∧ orderOf (b i) = 2 ∧ b i ∈ c.XSet ∧ b i ∉ E) →
        (∀ t ∈ A, orderOf t = 2 → t ∈ c.XSet → t ∉ E → ∃ i, t = b i) → E3Out 7 E A b :=
      fun b hbinj hb1 hb2 => by
        obtain ⟨w, hwF, hwo, hwE, hwC0, -, hwinv, hM9all, hM9ex⟩ :=
          model_E3 7 (Or.inr rfl) rfl c.alpha c.uElt c.XSet c.VSet c.alpha_x0T_ne c.alpha_uElt
            c.alpha_alpha (fun _ => c.hext) c.x0T_mem_XSet c.x0T_mul_alpha_mem_VSet
            (c.disjoint_XV (Or.inr rfl)) hclX hclV (c.hQ_model (Or.inr rfl) hW2) E hEmem A hAmem
            b hbinj hb1 hb2
        exact ⟨w, hwF, hwo, hwE, hwC0, hwinv, hM9all, hM9ex⟩
    exact exists_equiv_centralizer_v7 c hE1 hE2 hE3 hZD rfl hG hnab hM

theorem b_L2_Cv_of
    (hZD : CFSG.GH74.Uniqueness.S_ZD) : B_L2_Cv := by
  intro G _ _ hG n x K T Q S a hn h
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four ▸ le_rfl
  obtain ⟨hs, hnab, -⟩ := isKProperSimple_iff.1 hG.kproper
  have hnt := h.exists_noncomm hn hG4
  have hW2 := b_L2_W2 G hG n x K T Q S a hn h
  exact exists_equiv_centralizer_v_of_config hZD hn h hs hnab hnt hW2

theorem b_L2_Cv
    : B_L2_Cv := b_L2_Cv_of CFSG.GH74.Uniqueness.S_ZD_unconditional

end CFSG.GH74.GLS
