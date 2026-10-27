module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFD1
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFD4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFRel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section D3outer




variable {n : ℕ}


section D3

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem WFFrame.far_not_nbr' (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (k l : Fin 4) :
    M l ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (conjSub y (M k)) := fun hnb =>
  hfr.far_not_nbr h k l (Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen h.hyp (hfr.far_mem h k).1
    (hfr.mem l).1 hnb)

theorem WFFrame.far_gen (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (k : Fin 4) :
    ∃ b, b ∈ conjSub y (M k) ∧ b ∈ W ∧ b * b = y * t * y⁻¹ := by
  obtain ⟨hJΩ, hJu, hJD⟩ := hfr.far_mem h k
  have h2g := h.exit.2.2.2.1
  have hJsyl : IsSylow2In (conjSub y (M k)) (conjSub y (M k)) :=
    ⟨le_rfl, h2g _ hJΩ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hJq8 : Q8Facts (conjSub y (M k)) (y * t * y⁻¹) := by
    obtain ⟨e⟩ := members_q8_of_isPGroup h.hStd.perp h2g _ hJΩ
    exact q8Facts_of_iso hJu e
  obtain ⟨-, -, hcyc, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D h.hyp h.hW hJD hJΩ hJsyl
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card ↥(conjSub y (M k) ⊓ W) := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgJ : (g : Y) ∈ conjSub y (M k) := g.2.1
  have hgW : (g : Y) ∈ W := g.2.2
  refine ⟨g, hgJ, hgW, ?_⟩
  rcases hJq8.sq_cases _ hgJ with e | e
  · exfalso
    have h2 : orderOf g ∣ 2 := by
      refine orderOf_dvd_of_pow_eq_one ?_
      apply Subtype.ext
      show (g : Y) ^ 2 = 1
      rw [pow_two]; exact e
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · exact e

theorem WFFrame.u_notW (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) {i : Fin 4}
    (hmv : ¬ ∀ m ∈ M i, x * m = m * x) :
    x * a i * x⁻¹ ∈ M i ∧ x * a i * x⁻¹ ∉ W := by
  have hq := h.q8 (hfr.mem i)
  have hu : x * a i * x⁻¹ ∈ M i := hfr.act_mem hxM i (hfr.haM i)
  refine ⟨hu, fun hW => ?_⟩
  have hc := h.abelian _ (hfr.haW i) _ hW
  have hfix : ZFix x t (a i) := by
    rcases eq_or_mul_t_of_comm hq (hfr.haM i) hu (hfr.sq h i) (hfr.act_sq h hxt i) hc with e | e
    · exact Or.inl e
    · exact Or.inr e
  exact hmv (hq.cent_of_fix hxo hxt (fun m hm => hfr.act_mem hxM i hm) (hfr.haM i) (hfr.sq h i) hfix)

theorem WFFrame.d3 (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) (k : Fin 4) :
    conjSub (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) (conjSub y (M k)) = conjSub y (M k) := by
  obtain ⟨hJΩ, hJu, hJD⟩ := hfr.far_mem h k
  obtain ⟨b, hbJ, hbW, hbb⟩ := hfr.far_gen h k
  rw [hfr.fuse] at hJu hbb
  have h2g := h.exit.2.2.2.1
  have hJq8 : Q8Facts (conjSub y (M k)) (a 0 * a 1 * a 2 * a 3) := by
    obtain ⟨e⟩ := members_q8_of_isPGroup h.hStd.perp h2g _ hJΩ
    exact q8Facts_of_iso hJu e
  obtain ⟨kk, hkk, hprod, hrel⟩ := hfr.frame_rel h h.hW h.t_mem hJΩ hJD hJu
    (hfr.far_ne h k 0) (hfr.far_not_nbr' h k 0) (w := b) (Subgroup.mem_inf.mpr ⟨hbJ, hbW⟩) hbb
  have hv : ∀ i, x * a i * x⁻¹ ∈ M i ∧ x * a i * x⁻¹ ∉ W := fun i =>
    hfr.u_notW h hxo hxt hxM (hmv i)
  have hcr : ∀ (i j : Fin 4), i ≠ j → ∀ {m m' : Y}, m ∈ M i → m' ∈ M j → m * m' = m' * m :=
    fun i j hij m m' hm hm' => hfr.cross h hij hm hm'
  have hk : ∀ i, kk i ∈ M i := fun i => (Subgroup.mem_inf.mp (hkk i).1).1
  have hact : ∀ i, (x * a i * x⁻¹) * b * (x * a i * x⁻¹)⁻¹ = kk i * b := fun i =>
    hrel i _ (hv i).1 (hv i).2
  have hconj : ∀ (i j : Fin 4), i ≠ j → ∀ (g : Y), g ∈ M j →
      (x * a i * x⁻¹) * g * (x * a i * x⁻¹)⁻¹ = g := fun i j hij g hg => by
    have := hcr i j hij (hv i).1 hg
    exact mul_inv_eq_iff_eq_mul.mpr this
  have heb : (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * b * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹)⁻¹ =
      (a 0 * a 1 * a 2 * a 3) * b := by
    have e : x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ =
        (x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹) := by group
    obtain ⟨v, hvd⟩ : ∃ v : Fin 4 → Y, ∀ i, v i = x * a i * x⁻¹ := ⟨_, fun _ => rfl⟩
    have hvM : ∀ i, v i ∈ M i := fun i => by rw [hvd]; exact (hv i).1
    have hact' : ∀ i, v i * b * (v i)⁻¹ = kk i * b := fun i => by rw [hvd]; exact hact i
    have hconj' : ∀ i j, i ≠ j → ∀ g ∈ M j, v i * g * (v i)⁻¹ = g := fun i j hij g hg => by
      rw [hvd]; exact hconj i j hij g hg
    have e' : x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ = v 0 * v 1 * v 2 * v 3 := by
      rw [hvd 0, hvd 1, hvd 2, hvd 3]; group
    rw [e']
    have hks : kk 3 * kk 2 * kk 1 * kk 0 = a 0 * a 1 * a 2 * a 3 := by
      rw [← hprod]
      exact TwinMu.rev4 (hcr 0 1 (by decide) (hk 0) (hk 1)) (hcr 0 2 (by decide) (hk 0) (hk 2))
        (hcr 0 3 (by decide) (hk 0) (hk 3)) (hcr 1 2 (by decide) (hk 1) (hk 2))
        (hcr 1 3 (by decide) (hk 1) (hk 3)) (hcr 2 3 (by decide) (hk 2) (hk 3))
    calc (v 0 * v 1 * v 2 * v 3) * b * (v 0 * v 1 * v 2 * v 3)⁻¹
        = v 0 * (v 1 * (v 2 * (v 3 * b * (v 3)⁻¹) * (v 2)⁻¹) * (v 1)⁻¹) * (v 0)⁻¹ := by group
      _ = v 0 * (v 1 * (v 2 * (kk 3 * b) * (v 2)⁻¹) * (v 1)⁻¹) * (v 0)⁻¹ := by rw [hact' 3]
      _ = v 0 * (v 1 * ((v 2 * kk 3 * (v 2)⁻¹) * (v 2 * b * (v 2)⁻¹)) * (v 1)⁻¹) * (v 0)⁻¹ := by
          group
      _ = v 0 * (v 1 * (kk 3 * (kk 2 * b)) * (v 1)⁻¹) * (v 0)⁻¹ := by
          rw [hconj' 2 3 (by decide) _ (hk 3), hact' 2]
      _ = v 0 * (((v 1 * kk 3 * (v 1)⁻¹) * (v 1 * kk 2 * (v 1)⁻¹)) * (v 1 * b * (v 1)⁻¹)) *
            (v 0)⁻¹ := by group
      _ = v 0 * (kk 3 * kk 2 * (kk 1 * b)) * (v 0)⁻¹ := by
          rw [hconj' 1 3 (by decide) _ (hk 3), hconj' 1 2 (by decide) _ (hk 2), hact' 1]
      _ = ((v 0 * kk 3 * (v 0)⁻¹) * (v 0 * kk 2 * (v 0)⁻¹) * (v 0 * kk 1 * (v 0)⁻¹)) *
            (v 0 * b * (v 0)⁻¹) := by group
      _ = kk 3 * kk 2 * kk 1 * (kk 0 * b) := by
          rw [hconj' 0 3 (by decide) _ (hk 3), hconj' 0 2 (by decide) _ (hk 2),
            hconj' 0 1 (by decide) _ (hk 1), hact' 0]
      _ = (kk 3 * kk 2 * kk 1 * kk 0) * b := by group
      _ = (a 0 * a 1 * a 2 * a 3) * b := by rw [hks]
  obtain ⟨e, he⟩ : ∃ e, e = x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ := ⟨_, rfl⟩
  rw [← he] at heb ⊢
  have hes : e * (a 0 * a 1 * a 2 * a 3) = (a 0 * a 1 * a 2 * a 3) * e := by
    rw [he]; exact hfr.d1_es h hxo hxt hxM hmv
  have hesi : e * (a 0 * a 1 * a 2 * a 3) * e⁻¹ = a 0 * a 1 * a 2 * a 3 := mul_inv_eq_iff_eq_mul.mpr hes
  by_contra hne
  have hJ'Ω : conjSub e (conjSub y (M k)) ∈ CoreAssembly.conjClass (tightCore R) :=
    h.hyp.conjInvariant e _ hJΩ
  have hJ'u : IsUniqueInvolution (conjSub e (conjSub y (M k))) (a 0 * a 1 * a 2 * a 3) := by
    have := hJu.conj e
    rwa [hesi] at this
  have hcomm : Commutes (conjSub y (M k)) (conjSub e (conjSub y (M k))) := by
    intro m hm m' hm'
    have h1 := A7T22.le_trivialOnQuot_of_twin h.hyp hJ'Ω hJΩ hne hJ'u hJu hm'
    exact (commute_of_trivialOnQuot (h2g _ hJΩ) h1 hm).symm
  have hsb : (a 0 * a 1 * a 2 * a 3) * b ∈ conjSub e (conjSub y (M k)) := by
    rw [← heb]; exact conj_mem_conjSub hbJ
  have hb1 : b ≠ 1 := fun e1 => by
    rw [e1, one_mul] at hbb
    exact (hfr.s_ne h).1 hbb.symm
  have hbs : b ≠ a 0 * a 1 * a 2 * a 3 := fun e1 => by
    have hb2 : (a 0 * a 1 * a 2 * a 3) * (a 0 * a 1 * a 2 * a 3) = a 0 * a 1 * a 2 * a 3 := by
      rw [e1] at hbb; exact hbb
    rw [hfr.s_sq h] at hb2
    exact (hfr.s_ne h).1 hb2.symm
  obtain ⟨m, hmJ, hmnc⟩ := hJq8.exists_noncomm b hbJ hb1 hbs
  have hcm := hcomm m hmJ _ hsb
  have hmc : m * (a 0 * a 1 * a 2 * a 3) = (a 0 * a 1 * a 2 * a 3) * m := (hJq8.z_central m hmJ).symm
  apply hmnc
  have h3 : (a 0 * a 1 * a 2 * a 3) * (m * b) = (a 0 * a 1 * a 2 * a 3) * (b * m) := by
    calc (a 0 * a 1 * a 2 * a 3) * (m * b) = m * (a 0 * a 1 * a 2 * a 3) * b := by rw [← mul_assoc, ← hmc, mul_assoc]
      _ = m * ((a 0 * a 1 * a 2 * a 3) * b) := by rw [mul_assoc]
      _ = ((a 0 * a 1 * a 2 * a 3) * b) * m := hcm
      _ = (a 0 * a 1 * a 2 * a 3) * (b * m) := by rw [mul_assoc]
  exact (mul_left_cancel h3).symm

end D3

end D3outer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
