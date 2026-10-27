module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SN
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMCentB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMGraph

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B E1 : Subgroup G}

theorem sec9m_exists_cent (h36 : Asc82Lemma36) (h68 : Asc82Lemma68) (hB8 : Asc82Sec8B)
    (hT : Asc82Tab9M) (h6 : Asc82Tab6M) (hN : Asc82NormA6)
    (hctx : Sec9E1 G t L S z g B t₀ E1) :
    ∃ s ∈ Asub9 t t₀ B, s ∉ zpowers t ⊔ B ∧
      ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B), m * s = s * m := by
  have hc : Sec9Ctx G t L S z g B t₀ := hctx.choice.toSec9Ctx
  obtain ⟨-, -, -, h4, hv, -⟩ := asc82Lemma9N_of h36 h68 hB8 hT G t L S z g B t₀ hctx.choice
  have hOA := sec9m_O_cent_A hv
  have hMB := sec9m_M_cent_B hT h6 hctx
  obtain ⟨W, hWcard, hWinv, hWmem⟩ := sec9m_exists_W hctx hMB hOA
  have hB16 : Nat.card ↥B = 16 := by rw [hc.B_e16.2]; norm_num
  obtain ⟨hK, htransK⟩ := sec9m_autL h6 hc
  have hKH := sec9m_autIn_le hT h6 hc
  have ht0A : t₀ ∈ Asub9 t t₀ B := by
    rw [Asub9]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers t₀))
  have htA : t ∈ Asub9 t t₀ B := by
    rw [Asub9]; exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_zpowers t))
  have ht0n := sec9n_t0_not_mem_A8 hT hc
  rcases sec9m_graph (V := ↥B) (H := autIn (centMod (Asub9 t t₀ B) B) B)
      (fun b b' hb hb' => by
        obtain ⟨k, hk, hkb⟩ := htransK b b' hb hb'
        exact ⟨k, hKH hk, hkb⟩)
      (fun φ hφ => sec9m_centralizer_trivial hN hc.B_e16 hK φ (fun k hk => hφ k (hKH hk)))
      W (by rw [hB16]; exact hWcard) hWinv with h1 | h2 | h3
  ·
    exfalso
    refine sec9m_E1_not_le_A hctx (fun e he => ?_)
    have heM : e ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B) := Subgroup.mem_sup_left he
    obtain ⟨w, hw, hw1, -⟩ := hWmem e heM
    have het : e * t * e⁻¹ * t⁻¹ = 1 := by rw [← hw1, h1 w hw]; rfl
    have het' : e * t = t * e := by
      calc e * t = e * t * e⁻¹ * e := by group
        _ = t * e := by rw [mul_inv_eq_one.mp het]
    have hle : zpowers t ⊔ B ≤ centralizer ({e} : Set G) := by
      refine sup_le ?_ ?_
      · rw [zpowers_le, mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact het'
      · intro b hb
        rw [mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]; exact hMB e heM b hb
    have hecent : e ∈ centralizer ((zpowers t ⊔ B : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      exact (mem_centralizer_iff.mp (hle hx) e (Set.mem_singleton e)).symm
    have heA : e ∈ centMod (Asub9 t t₀ B) B ⊓ centralizer (Asub9 t t₀ B : Set G) := by
      rw [h4]; exact ⟨hctx.le_N he, hecent⟩
    exact sec9m_E1_cent_A hctx hv e he heA.2
  ·
    refine ⟨t₀, ht0A, ht0n, fun m hm => ?_⟩
    obtain ⟨w, hw, -, hw2⟩ := hWmem m hm
    have h0 : m * t₀ * m⁻¹ * t₀⁻¹ = 1 := by rw [← hw2, h2 w hw]; rfl
    calc m * t₀ = m * t₀ * m⁻¹ * m := by group
      _ = t₀ * m := by rw [mul_inv_eq_one.mp h0]
  ·
    refine ⟨t * t₀, (Asub9 t t₀ B).mul_mem htA ht0A, fun hs => ht0n ?_, fun m hm => ?_⟩
    · have htB : t ∈ zpowers t ⊔ B := Subgroup.mem_sup_left (mem_zpowers t)
      have h' : t⁻¹ * (t * t₀) ∈ zpowers t ⊔ B := Subgroup.mul_mem _ (Subgroup.inv_mem _ htB) hs
      rwa [inv_mul_cancel_left] at h'
    · obtain ⟨w, hw, hw1, hw2⟩ := hWmem m hm
      have hαB : ((w.1 : ↥B) : G) ∈ B := w.1.2
      have hα12 : ((w.1 : ↥B) : G) = ((w.2 : ↥B) : G) := congrArg Subtype.val (h3 w hw)
      have e1 : m * t * m⁻¹ = ((w.1 : ↥B) : G) * t := by rw [hw1]; group
      have e2 : m * t₀ * m⁻¹ = ((w.1 : ↥B) : G) * t₀ := by rw [hα12, hw2]; group
      have htα : t * ((w.1 : ↥B) : G) = ((w.1 : ↥B) : G) * t := sec9n_t_B hc _ hαB
      have hαα : ((w.1 : ↥B) : G) * ((w.1 : ↥B) : G) = 1 := by
        rw [← pow_two]; exact hc.B_e16.1.2 _ hαB
      have hcomm : m * (t * t₀) * m⁻¹ = t * t₀ := by
        calc m * (t * t₀) * m⁻¹ = (m * t * m⁻¹) * (m * t₀ * m⁻¹) := by group
          _ = (((w.1 : ↥B) : G) * t) * (((w.1 : ↥B) : G) * t₀) := by rw [e1, e2]
          _ = ((w.1 : ↥B) : G) * (t * ((w.1 : ↥B) : G)) * t₀ := by group
          _ = ((w.1 : ↥B) : G) * (((w.1 : ↥B) : G) * t) * t₀ := by rw [htα]
          _ = (((w.1 : ↥B) : G) * ((w.1 : ↥B) : G)) * t * t₀ := by group
          _ = t * t₀ := by rw [hαα, one_mul]
      calc m * (t * t₀) = m * (t * t₀) * m⁻¹ * m := by group
        _ = (t * t₀) * m := by rw [hcomm]

end CFSG.OddStandard.SmallF3.Omega
