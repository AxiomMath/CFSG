module

public import CFSG.LocalAnalysis.OddStandard.ONanIdV
public import CFSG.LocalAnalysis.OddStandard.ONanLocSyl

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

@[expose] def y0E : AlpE := gen 0 * gen 2

@[expose] def InZBE (e : AlpE) : Prop := e = 1 ∨ e = zc ∨ e = invE 1 ∨ e = zc * invE 1

instance (e : AlpE) : Decidable (InZBE e) := inferInstanceAs (Decidable (_ ∨ _))

theorem xE_mul_y0E : xE * y0E = invE 1 := by decide

theorem y0E_sq : y0E * y0E = zc := by decide

theorem w3_not_ZB : ¬ InZBE (gen 0 ^ 2) := by decide

set_option maxRecDepth 100000 in
theorem W_cover_E : ∀ e : AlpE, InWE e → InZBE e ∨ InZBE ((gen 0 ^ 2)⁻¹ * e) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sq_eq_zc_xW : ∀ y : AlpE, y.d = 0 → y * y = zc → InWE (xE⁻¹ * y) := by
  decide +kernel

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem y0_eq : v1 * v3 = D.E.φ y0E := by rw [y0E, map_mul, AlpEmb.φ_v1, AlpEmb.φ_v3]

theorem z_eq : invRep v1 v2 v3 s t 0 = D.E.φ zc := by rw [AlpEmb.φ_zc]; rfl

theorem b_eq : invRep v1 v2 v3 s t 1 = D.E.φ (invE 1) := (AlpEmb.φ_invE D.E 1).symm

theorem y0_mem_V : v1 * v3 ∈ alpV v1 v2 v3 := by
  rw [D.y0_eq, AlpEmb.alpV_eq_map D.E]
  exact Subgroup.mem_map_of_mem _ (mem_Vsub.2 rfl)

theorem y0_sq : v1 * v3 * (v1 * v3) = invRep v1 v2 v3 s t 0 := by
  rw [D.y0_eq, ← map_mul, y0E_sq, D.z_eq]

theorem x_mul_y0 : xel v1 v2 v3 * (v1 * v3) = invRep v1 v2 v3 s t 1 := by
  rw [D.y0_eq, D.x_eq, ← map_mul, xE_mul_y0E, D.b_eq]

@[expose] def InZB (_D : FusCtx G v1 v2 v3 s t) (g : G) : Prop :=
  g = 1 ∨ g = invRep v1 v2 v3 s t 0 ∨ g = invRep v1 v2 v3 s t 1 ∨
    g = invRep v1 v2 v3 s t 0 * invRep v1 v2 v3 s t 1

theorem inZB_phi (e : AlpE) : D.InZB (D.E.φ e) ↔ InZBE e := by
  rw [InZB, InZBE, D.z_eq, D.b_eq, ← map_mul, ← map_one D.E.φ, D.E.φ_eq_iff, D.E.φ_eq_iff,
    D.E.φ_eq_iff, D.E.φ_eq_iff]

theorem exists_phi_of_mem_W {w : G} (hw : w ∈ alpW v1 v2 v3) :
    ∃ e : AlpE, InWE e ∧ D.E.φ e = w := by
  have hwV := D.W_le_V hw
  rw [AlpEmb.alpV_eq_map D.E] at hwV
  obtain ⟨e, -, rfl⟩ := Subgroup.mem_map.1 hwV
  exact ⟨e, (D.mem_W_phi e).1 hw, rfl⟩

omit [Finite G] D in
theorem w3_mem_W : v1 ^ 2 ∈ alpW v1 v2 v3 := subset_closure (by simp)

theorem w3_eq : v1 ^ 2 = D.E.φ (gen 0 ^ 2) := by rw [map_pow, AlpEmb.φ_v1]

theorem W_cover {w : G} (hw : w ∈ alpW v1 v2 v3) : D.InZB w ∨ D.InZB ((v1 ^ 2)⁻¹ * w) := by
  obtain ⟨e, he, rfl⟩ := D.exists_phi_of_mem_W hw
  rw [D.inZB_phi, D.w3_eq, ← map_inv, ← map_mul, D.inZB_phi]
  exact W_cover_E e he

theorem not_inZB_w3 : ¬ D.InZB (v1 ^ 2) := by
  rw [D.w3_eq, D.inZB_phi]
  exact w3_not_ZB

theorem W_le_closure : alpW v1 v2 v3 ≤
    closure ({invRep v1 v2 v3 s t 0, invRep v1 v2 v3 s t 1, v1 ^ 2} : Set G) := by
  intro w hw
  have hz : invRep v1 v2 v3 s t 0 ∈ closure ({invRep v1 v2 v3 s t 0, invRep v1 v2 v3 s t 1,
      v1 ^ 2} : Set G) := subset_closure (by simp)
  have hb : invRep v1 v2 v3 s t 1 ∈ closure ({invRep v1 v2 v3 s t 0, invRep v1 v2 v3 s t 1,
      v1 ^ 2} : Set G) := subset_closure (by simp)
  have h3 : v1 ^ 2 ∈ closure ({invRep v1 v2 v3 s t 0, invRep v1 v2 v3 s t 1, v1 ^ 2} : Set G) :=
    subset_closure (by simp)
  have hZB : ∀ u : G, D.InZB u → u ∈ closure ({invRep v1 v2 v3 s t 0, invRep v1 v2 v3 s t 1,
      v1 ^ 2} : Set G) := by
    rintro u (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact hz
    · exact hb
    · exact mul_mem hz hb
  rcases D.W_cover hw with h | h
  · exact hZB w h
  · have e : w = v1 ^ 2 * ((v1 ^ 2)⁻¹ * w) := by group
    rw [e]
    exact mul_mem h3 (hZB _ h)

theorem sq_mem_centralizer_W_of_fix {n : G} (hn : n ∈ normalizer (alpW v1 v2 v3 : Set G))
    (hz : n * invRep v1 v2 v3 s t 0 * n⁻¹ = invRep v1 v2 v3 s t 0)
    (hb : n * invRep v1 v2 v3 s t 1 * n⁻¹ = invRep v1 v2 v3 s t 1) :
    n ^ 2 ∈ centralizer (alpW v1 v2 v3 : Set G) := by
  set z := invRep v1 v2 v3 s t 0 with hzdef
  set b := invRep v1 v2 v3 s t 1 with hbdef
  have hfix : ∀ u : G, D.InZB u → n * u * n⁻¹ = u := by
    rintro u (rfl | rfl | rfl | rfl)
    · group
    · exact hz
    · exact hb
    · calc n * (z * b) * n⁻¹ = (n * z * n⁻¹) * (n * b * n⁻¹) := by group
        _ = z * b := by rw [hz, hb]
  have hw3 : n * v1 ^ 2 * n⁻¹ ∈ alpW v1 v2 v3 := (mem_normalizer_iff.1 hn _).1 w3_mem_W
  have hnot : ¬ D.InZB (n * v1 ^ 2 * n⁻¹) := by
    intro h
    apply D.not_inZB_w3
    have e := hfix _ h
    have e2 : v1 ^ 2 = n * v1 ^ 2 * n⁻¹ := by
      have := congrArg (fun y => n⁻¹ * y * n) e
      simp only [show n⁻¹ * (n * (n * v1 ^ 2 * n⁻¹) * n⁻¹) * n = n * v1 ^ 2 * n⁻¹ by group,
        show n⁻¹ * (n * v1 ^ 2 * n⁻¹) * n = v1 ^ 2 by group] at this
      exact this.symm
    rw [e2]
    exact h
  set u := (v1 ^ 2)⁻¹ * (n * v1 ^ 2 * n⁻¹) with hu
  have huZB : D.InZB u := (D.W_cover hw3).resolve_left hnot
  have hun := hfix u huZB
  have hu2 : u * u = 1 := by
    rcases huZB with h | h | h | h <;> rw [h]
    · group
    · exact D.rep_sq 0
    · exact D.rep_sq 1
    · have hc : z * b = b * z := D.comm_V D.z_mem_V' D.b_mem_V
      calc z * b * (z * b) = z * z * (b * b) := by
            rw [show z * b * (z * b) = z * (b * z) * b by group, ← hc]; group
        _ = 1 := by rw [D.rep_sq 0, D.rep_sq 1, one_mul]
  have hw3' : n ^ 2 * v1 ^ 2 * (n ^ 2)⁻¹ = v1 ^ 2 := by
    have e1 : n * v1 ^ 2 * n⁻¹ = v1 ^ 2 * u := by rw [hu]; group
    calc n ^ 2 * v1 ^ 2 * (n ^ 2)⁻¹ = n * (n * v1 ^ 2 * n⁻¹) * n⁻¹ := by rw [pow_two]; group
      _ = n * (v1 ^ 2 * u) * n⁻¹ := by rw [e1]
      _ = (n * v1 ^ 2 * n⁻¹) * (n * u * n⁻¹) := by group
      _ = v1 ^ 2 * u * u := by rw [e1, hun]
      _ = v1 ^ 2 := by rw [mul_assoc, hu2, mul_one]
  have hz2 : n ^ 2 * z * (n ^ 2)⁻¹ = z := by
    calc n ^ 2 * z * (n ^ 2)⁻¹ = n * (n * z * n⁻¹) * n⁻¹ := by rw [pow_two]; group
      _ = z := by rw [hz, hz]
  have hb2 : n ^ 2 * b * (n ^ 2)⁻¹ = b := by
    calc n ^ 2 * b * (n ^ 2)⁻¹ = n * (n * b * n⁻¹) * n⁻¹ := by rw [pow_two]; group
      _ = b := by rw [hb, hb]
  rw [mem_centralizer_iff]
  intro w hw
  have hle : closure ({z, b, v1 ^ 2} : Set G) ≤ centralizer ({n ^ 2} : Set G) := by
    rw [closure_le]
    intro y hy
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    have key : ∀ y : G, n ^ 2 * y * (n ^ 2)⁻¹ = y → n ^ 2 * y = y * n ^ 2 := fun y h => by
      calc n ^ 2 * y = n ^ 2 * y * (n ^ 2)⁻¹ * n ^ 2 := by group
        _ = y * n ^ 2 := by rw [h]
    rcases hy with rfl | rfl | rfl
    · exact (key _ hz2).symm
    · exact (key _ hb2).symm
    · exact (key _ hw3').symm
  exact mem_centralizer_singleton_iff.1 (hle (D.W_le_closure hw))

theorem mem_centralizer_V_of_odd {n : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hy : n * (v1 * v3) = v1 * v3 * n) {k : ℕ} (hk : Odd k)
    (hnk : n ^ k ∈ centralizer (alpV v1 v2 v3 : Set G)) :
    n ∈ centralizer (alpV v1 v2 v3 : Set G) := by
  set x := xel v1 v2 v3 with hxdef
  set z := invRep v1 v2 v3 s t 0 with hzdef
  set b := invRep v1 v2 v3 s t 1 with hbdef
  set y0 := v1 * v3 with hy0
  have hny0 : n * y0 * n⁻¹ = y0 := by rw [hy, mul_inv_cancel_right]
  have hnz : n * z * n⁻¹ = z := by
    rw [hzdef, ← D.y0_sq]
    calc n * (y0 * y0) * n⁻¹ = (n * y0 * n⁻¹) * (n * y0 * n⁻¹) := by group
      _ = y0 * y0 := by rw [hny0]
  have hxn : x⁻¹ * (n * x * n⁻¹) ∈ alpW v1 v2 v3 := by
    have hV : n * x * n⁻¹ ∈ alpV v1 v2 v3 := conj_mem_V hn D.x_mem_V
    rw [AlpEmb.alpV_eq_map D.E] at hV
    obtain ⟨e, he, he'⟩ := Subgroup.mem_map.1 hV
    have hsq : D.E.φ (e * e) = D.E.φ zc := by
      rw [map_mul, he', ← D.z_eq]
      have hx2 : x * x = z := D.xel_sq
      calc n * x * n⁻¹ * (n * x * n⁻¹) = n * (x * x) * n⁻¹ := by group
        _ = z := by rw [hx2, hnz]
    have hW := sq_eq_zc_xW e (mem_Vsub.1 he) (D.E.inj hsq)
    rw [← D.mem_W_phi, map_mul, map_inv, ← D.x_eq, he'] at hW
    exact hW
  have hnx : n * x * n⁻¹ = x := by
    rcases D.conj_x_of_mem hxn with h | h
    · exact h
    · exfalso
      have h' : n * x * n⁻¹ = x⁻¹ := h
      have hsq : n * n * x * (n * n)⁻¹ = x := by
        calc n * n * x * (n * n)⁻¹ = n * (n * x * n⁻¹) * n⁻¹ := by group
          _ = n * x⁻¹ * n⁻¹ := by rw [h']
          _ = (n * x * n⁻¹)⁻¹ := by group
          _ = x := by rw [h', inv_inv]
      have hpow : ∀ m : ℕ, n ^ (2 * m + 1) * x * (n ^ (2 * m + 1))⁻¹ = x⁻¹ := by
        intro m
        induction m with
        | zero => simpa using h'
        | succ m ih =>
          have e : n ^ (2 * (m + 1) + 1) = n * (n * n ^ (2 * m + 1)) := by
            rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by ring, pow_succ', pow_succ']
          rw [e]
          calc n * (n * n ^ (2 * m + 1)) * x * (n * (n * n ^ (2 * m + 1)))⁻¹ =
              n * (n * (n ^ (2 * m + 1) * x * (n ^ (2 * m + 1))⁻¹) * n⁻¹) * n⁻¹ := by group
            _ = n * (n * x⁻¹ * n⁻¹) * n⁻¹ := by rw [ih]
            _ = (n * n * x * (n * n)⁻¹)⁻¹ := by simp only [mul_inv_rev, inv_inv, mul_assoc]
            _ = x⁻¹ := by rw [hsq]
      obtain ⟨m, rfl⟩ := hk
      have h1 := hpow m
      have h2 : n ^ (2 * m + 1) * x * (n ^ (2 * m + 1))⁻¹ = x := by
        have hc : x * n ^ (2 * m + 1) = n ^ (2 * m + 1) * x := mem_centralizer_iff.1 hnk x D.x_mem_V
        rw [← hc, mul_inv_cancel_right]
      rw [h1] at h2
      apply D.rep_ne_one 0
      calc invRep v1 v2 v3 s t 0 = x * x := D.xel_sq.symm
        _ = x * x⁻¹ := by rw [h2]
        _ = 1 := mul_inv_cancel x
  have hnb : n * b * n⁻¹ = b := by
    rw [hbdef, ← D.x_mul_y0]
    calc n * (x * y0) * n⁻¹ = (n * x * n⁻¹) * (n * y0 * n⁻¹) := by group
      _ = x * y0 := by rw [hnx, hny0]
  have hn2 := D.sq_mem_centralizer_W_of_fix (D.normalizer_V_le_W hn) hnz hnb
  have hn2V : n ^ 2 ∈ centralizer (alpV v1 v2 v3 : Set G) :=
    D.mem_centralizer_V_of_W (pow_mem hn 2) hn2
  obtain ⟨m, rfl⟩ := hk
  have e : n = n ^ (2 * m + 1) * ((n ^ 2) ^ m)⁻¹ := by
    rw [← pow_mul, pow_succ', mul_inv_cancel_right]
  rw [e]
  exact mul_mem hnk (inv_mem (pow_mem hn2V m))

theorem exists_pow_mem_centralizer_V {n : G} (hn : n ∈ normalizer (alpV v1 v2 v3 : Set G))
    (hy : n * (v1 * v3) = v1 * v3 * n) :
    ∃ e : ℕ, n ^ (2 ^ e) ∈ centralizer (alpV v1 v2 v3 : Set G) := by
  have hpos : 0 < orderOf n := orderOf_pos n
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  refine ⟨e, D.mem_centralizer_V_of_odd (pow_mem hn _) ?_ hm ?_⟩
  · exact (Commute.pow_left hy _).eq
  · rw [← pow_mul, ← hnm, pow_orderOf_eq_one]
    exact one_mem _

end FusCtx

end CFSG.OddStandard.ONanRec
