module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ESup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFAct
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFDefs

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

section WMouter




variable {n : ℕ}


section WM

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem WFFrame.s_mem_W (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) :
    y * t * y⁻¹ ∈ W := by
  rw [hfr.fuse]
  exact W.mul_mem (W.mul_mem (W.mul_mem (hfr.haW 0) (hfr.haW 1)) (hfr.haW 2)) (hfr.haW 3)

theorem WFFrame.frame_split (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (l : Fin 4) :
    ∃ Q : Y, a 0 * a 1 * a 2 * a 3 = a l * Q ∧ ∀ m ∈ M l, m * Q = Q * m := by
  have hc := hfr.comm_a h
  have hcr : ∀ p q : Fin 4, p ≠ q → ∀ m ∈ M p, m * a q = a q * m := fun p q hpq m hm =>
    hfr.cross h hpq hm (hfr.haM q)
  have c2 : ∀ p q r : Fin 4, q ≠ p → r ≠ p → ∀ m ∈ M p, m * (a q * a r) = (a q * a r) * m :=
    fun p q r hq hr m hm => by
      calc m * (a q * a r) = (m * a q) * a r := (mul_assoc _ _ _).symm
        _ = (a q * m) * a r := by rw [hcr p q (Ne.symm hq) m hm]
        _ = a q * (m * a r) := mul_assoc _ _ _
        _ = a q * (a r * m) := by rw [hcr p r (Ne.symm hr) m hm]
        _ = (a q * a r) * m := (mul_assoc _ _ _).symm
  have c3 : ∀ p q r r' : Fin 4, q ≠ p → r ≠ p → r' ≠ p → ∀ m ∈ M p,
      m * (a q * a r * a r') = (a q * a r * a r') * m := fun p q r r' hq hr hr' m hm => by
    calc m * (a q * a r * a r') = (m * (a q * a r)) * a r' := (mul_assoc _ _ _).symm
      _ = ((a q * a r) * m) * a r' := by rw [c2 p q r hq hr m hm]
      _ = (a q * a r) * (m * a r') := mul_assoc _ _ _
      _ = (a q * a r) * (a r' * m) := by rw [hcr p r' (Ne.symm hr') m hm]
      _ = (a q * a r * a r') * m := (mul_assoc _ _ _).symm
  fin_cases l
  · refine ⟨a 1 * a 2 * a 3, ?_, fun m hm => c3 0 1 2 3 (by decide) (by decide) (by decide) m hm⟩
    show a 0 * a 1 * a 2 * a 3 = a 0 * (a 1 * a 2 * a 3)
    group
  · refine ⟨a 0 * a 2 * a 3, ?_, fun m hm => c3 1 0 2 3 (by decide) (by decide) (by decide) m hm⟩
    calc a 0 * a 1 * a 2 * a 3 = (a 0 * a 1) * a 2 * a 3 := rfl
      _ = (a 1 * a 0) * a 2 * a 3 := by rw [hc 0 1]
      _ = a 1 * (a 0 * a 2 * a 3) := by group
  · refine ⟨a 0 * a 1 * a 3, ?_, fun m hm => c3 2 0 1 3 (by decide) (by decide) (by decide) m hm⟩
    calc a 0 * a 1 * a 2 * a 3 = a 0 * (a 1 * a 2) * a 3 := by group
      _ = a 0 * (a 2 * a 1) * a 3 := by rw [hc 1 2]
      _ = (a 0 * a 2) * a 1 * a 3 := by group
      _ = (a 2 * a 0) * a 1 * a 3 := by rw [hc 0 2]
      _ = a 2 * (a 0 * a 1 * a 3) := by group
  · refine ⟨a 0 * a 1 * a 2, ?_, fun m hm => c3 3 0 1 2 (by decide) (by decide) (by decide) m hm⟩
    calc a 0 * a 1 * a 2 * a 3 = a 0 * a 1 * (a 2 * a 3) := by group
      _ = a 0 * a 1 * (a 3 * a 2) := by rw [hc 2 3]
      _ = a 0 * (a 1 * a 3) * a 2 := by group
      _ = a 0 * (a 3 * a 1) * a 2 := by rw [hc 1 3]
      _ = (a 0 * a 3) * a 1 * a 2 := by group
      _ = (a 3 * a 0) * a 1 * a 2 := by rw [hc 0 3]
      _ = a 3 * (a 0 * a 1 * a 2) := by group

theorem fin4_other : ∀ i j : Fin 4, i ≠ j → ∃ l : Fin 4, l ≠ i ∧ l ≠ j := by decide +kernel

theorem wfWM_proved (n : ℕ) : WFWM n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W h M a y hfr i j hij vi hvi hviW vj hvj hvjW k
  have hP := h.partI
  have hW := h.hW
  have c : Q3CL.Thompson.Ctx (CoreAssembly.conjClass (tightCore R)) W := Q3CL.T8.ctxOf hP hW
  have h2g := h.exit.2.2.2.1
  have hq8 := fun l => h.q8 (hfr.mem l)
  have ht := (hq8 0).z_sq
  have ht1 := (hq8 0).z_ne
  obtain ⟨s, hs⟩ : ∃ s, s = y * t * y⁻¹ := ⟨_, rfl⟩
  have hsW : s ∈ W := hs ▸ hfr.s_mem_W
  have hst : s ≠ t := hs ▸ hfr.fuse_ne
  have hsa : s = a 0 * a 1 * a 2 * a 3 := hs.trans hfr.fuse
  obtain ⟨J, hJ⟩ : ∃ J, J = conjSub y (M k) := ⟨_, rfl⟩
  have hJΩ : J ∈ CoreAssembly.conjClass (tightCore R) := by
    rw [hJ]; exact h.hyp.conjInvariant y _ (hfr.mem k).1
  have hJu : IsUniqueInvolution J s := by rw [hJ, hs]; exact (h.uniqInv (hfr.mem k)).conj y
  have hJD : J ∈ DSet (CoreAssembly.conjClass (tightCore R)) W :=
    twin_mem_DSet hP h2g hW hsW hJΩ hJu
  have hJsyl : IsSylow2In J J := ⟨le_rfl, h2g J hJΩ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hJq8 : Q8Facts J s := by
    obtain ⟨e⟩ := members_q8_of_isPGroup h.hStd.perp h2g J hJΩ
    exact q8Facts_of_iso hJu e
  have hs2 : s * s = 1 := hJu.sq
  obtain ⟨b, hbJ, hbW, hbb⟩ : ∃ b, b ∈ J ∧ b ∈ W ∧ b * b = s := by
    obtain ⟨-, -, hcyc, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D h.hyp hW hJD hJΩ hJsyl
    obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf g = Nat.card ↥(J ⊓ W) := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgJ : (g : Y) ∈ J := g.2.1
    have hgW : (g : Y) ∈ W := g.2.2
    refine ⟨g, hgJ, hgW, ?_⟩
    rcases hJq8.sq_cases _ hgJ with e | e
    · exfalso
      have h2 : orderOf g ∣ 2 := by
        refine orderOf_dvd_of_pow_eq_one ?_
        apply Subtype.ext
        simpa [sq] using e
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    · exact e
  have hMD : ∀ l, M l ∈ DSet (CoreAssembly.conjClass (tightCore R)) W := fun l =>
    twin_mem_DSet hP h2g hW h.t_mem (hfr.mem l).1 (h.uniqInv (hfr.mem l))
  have hMsyl : ∀ l, IsSylow2In (M l) (M l) := fun l =>
    ⟨le_rfl, h2g _ (hfr.mem l).1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hMJ : ∀ l, M l ≠ J := fun l e => hst (((e ▸ h.uniqInv (hfr.mem l) : IsUniqueInvolution J t).eq hJu).symm)
  have hnot : ∀ l, J ∉ omegaNbr (CoreAssembly.conjClass (tightCore R)) (M l) := by
    intro l hnb
    have hperp := kPerp_datum h.hStd.perp (hfr.mem l).1 (h.uniqInv (hfr.mem l))
    have hmem : J ∈ KPerp (CoreAssembly.conjClass (tightCore R)) (M l) := Set.mem_insert_of_mem _ hnb
    rw [hperp] at hmem
    obtain ⟨-, z, hz1, hz2⟩ := hmem
    exact hst ((hz2.eq hJu).symm.trans (hz1.eq (h.uniqInv (hfr.mem l))))
  obtain ⟨σ, hσK⟩ : ∃ σ : Asc77.Thompson.Rep (CoreAssembly.conjClass (tightCore R)) W, σ.K = J :=
    ⟨Q3CL.T8.mkRep hP hW hJΩ hJD hJsyl, rfl⟩
  have hconj_s : ∀ (v : Y) (l : Fin 4) (hv : v ∈ M l) (hvW : v ∉ W), v * s * v⁻¹ = t * s := by
    intro v l hv hvW
    exact c.conj_involution (⟨M l, M l, v, (hfr.mem l).1, hMD l, hMsyl l, hv, hvW⟩ :
      Asc77.Thompson.Rep (CoreAssembly.conjClass (tightCore R)) W) σ
      (by rw [hσK]; exact hMJ l) (by rw [hσK]; exact hnot l) (h.uniqInv (hfr.mem l))
      (by rw [hσK]; exact hJu)
  have hcomm_b : ∀ (v : Y) (l : Fin 4) (hv : v ∈ M l) (hvW : v ∉ W),
      v * b * v⁻¹ * b⁻¹ ∈ M l ⊓ W := by
    intro v l hv hvW
    exact c.comm_mem (⟨M l, M l, v, (hfr.mem l).1, hMD l, hMsyl l, hv, hvW⟩ :
      Asc77.Thompson.Rep (CoreAssembly.conjClass (tightCore R)) W) σ
      (by rw [hσK]; exact hMJ l) (v := b) (by rw [hσK]; exact Subgroup.mem_inf.mpr ⟨hbJ, hbW⟩)
  have hE : ∀ (v : Y) (l : Fin 4) (hv : v ∈ M l) (hvW : v ∉ W),
      ∃ e, e ∈ M l ∧ e * e = t ∧ v * b * v⁻¹ = e * b := by
    intro v l hv hvW
    have hmem := hcomm_b v l hv hvW
    refine ⟨v * b * v⁻¹ * b⁻¹, hmem.1, ?_, by group⟩
    have hvN : v ∈ Subgroup.normalizer (W : Set Y) := (hMD l).2 hv
    have hp : v * b * v⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hvN b).mp hbW
    have hbi : b⁻¹ ∈ W := W.inv_mem hbW
    have hcm := h.abelian _ hp _ hbi
    have hpp : (v * b * v⁻¹) * (v * b * v⁻¹) = t * s := by
      calc _ = v * (b * b) * v⁻¹ := by group
        _ = v * s * v⁻¹ := by rw [hbb]
        _ = t * s := hconj_s v l hv hvW
    have hbb' : b⁻¹ * b⁻¹ = s := by
      calc b⁻¹ * b⁻¹ = (b * b)⁻¹ := by group
        _ = s⁻¹ := by rw [hbb]
        _ = s := inv_eq_of_mul_eq_one_right hs2
    calc (v * b * v⁻¹ * b⁻¹) * (v * b * v⁻¹ * b⁻¹)
        = (v * b * v⁻¹) * ((b⁻¹ * (v * b * v⁻¹)) * b⁻¹) := by group
      _ = (v * b * v⁻¹) * (((v * b * v⁻¹) * b⁻¹) * b⁻¹) := by rw [← hcm]
      _ = ((v * b * v⁻¹) * (v * b * v⁻¹)) * (b⁻¹ * b⁻¹) := by group
      _ = (t * s) * s := by rw [hpp, hbb']
      _ = t := by rw [mul_assoc, hs2, mul_one]
  obtain ⟨ei, hei, hei2, hvib⟩ := hE vi i hvi hviW
  obtain ⟨ej, hej, hej2, hvjb⟩ := hE vj j hvj hvjW
  have hcross_i : vi * ej = ej * vi := hfr.cross h hij hvi hej
  have hcb : (vi * vj) * b * (vi * vj)⁻¹ = ej * (ei * b) := by
    calc (vi * vj) * b * (vi * vj)⁻¹ = vi * (vj * b * vj⁻¹) * vi⁻¹ := by group
      _ = vi * (ej * b) * vi⁻¹ := by rw [hvjb]
      _ = (vi * ej * vi⁻¹) * (vi * b * vi⁻¹) := by group
      _ = ej * (ei * b) := by rw [mul_inv_eq_iff_eq_mul.mpr hcross_i, hvib]
  have hcs : (vi * vj) * s * (vi * vj)⁻¹ = s := by
    have h1 := hconj_s vj j hvj hvjW
    have h2 := hconj_s vi i hvi hviW
    have htv : vi * t * vi⁻¹ = t := mul_inv_eq_iff_eq_mul.mpr (hfr.t_comm h i hvi).symm
    calc (vi * vj) * s * (vi * vj)⁻¹ = vi * (vj * s * vj⁻¹) * vi⁻¹ := by group
      _ = vi * (t * s) * vi⁻¹ := by rw [h1]
      _ = (vi * t * vi⁻¹) * (vi * s * vi⁻¹) := by group
      _ = t * (t * s) := by rw [htv, h2]
      _ = s := by rw [← mul_assoc, ht, one_mul]
  intro heq
  rw [← hJ] at heq
  have hcN : vi * vj ∈ Subgroup.normalizer (W : Set Y) :=
    Subgroup.mul_mem _ ((hMD i).2 hvi) ((hMD j).2 hvj)
  obtain ⟨d, hd⟩ : ∃ d, d = (vi * vj) * b * (vi * vj)⁻¹ := ⟨_, rfl⟩
  have hdJ : d ∈ J := by
    have := conj_mem_conjSub (n := vi * vj) hbJ
    rw [heq] at this
    rwa [hd]
  have hdW : d ∈ W := by rw [hd]; exact (Subgroup.mem_normalizer_iff.mp hcN b).mp hbW
  have hdd : d * d = s := by
    calc d * d = (vi * vj) * (b * b) * (vi * vj)⁻¹ := by rw [hd]; group
      _ = s := by rw [hbb, hcs]
  have hdb : d * b = b * d := h.abelian _ hdW _ hbW
  have hbs : b * s = s * b := ((hJq8.z_central b hbJ)).symm
  rcases hJq8.cent_cyc b hbJ hbb d hdJ hdb with e | e | e | e
  · exfalso
    rw [e] at hdd
    exact hJu.ne_one (by simpa using hdd.symm)
  ·
    have h1 : ej * (ei * b) = b := by rw [← hcb, ← hd]; exact e
    have h2 : ej * ei = 1 := by
      have : (ej * ei) * b = 1 * b := by rw [one_mul, mul_assoc]; exact h1
      exact mul_right_cancel this
    have hei' : ei = ej⁻¹ := eq_inv_of_mul_eq_one_right h2
    have heiMj : ei ∈ M j := by rw [hei']; exact (M j).inv_mem hej
    have hcen : ∀ g ∈ M i, ei * g = g * ei := fun g hg => (hfr.cross h hij hg heiMj).symm
    rcases (hq8 i).center ei hei hcen with e1 | e1
    · rw [e1] at hei2
      exact ht1 (by simpa using hei2.symm)
    · rw [e1, ht] at hei2
      exact ht1 hei2.symm
  · exfalso
    rw [e, hs2] at hdd
    exact hJu.ne_one hdd.symm
  ·
    have h1 : ej * (ei * b) = b * s := by rw [← hcb, ← hd]; exact e
    have h2 : ej * ei = s := by
      have : (ej * ei) * b = s * b := by rw [mul_assoc, h1, hbs]
      exact mul_right_cancel this
    obtain ⟨l, hli, hlj⟩ := fin4_other i j hij
    obtain ⟨Q, hQ, hQc⟩ := hfr.frame_split h l
    have hal : a l ∈ M l := hfr.haM l
    have hal1 : a l ≠ 1 := by
      intro e1
      have := hfr.sq h l
      rw [e1, one_mul] at this
      exact ht1 this.symm
    have halt : a l ≠ t := by
      intro e1
      have := hfr.sq h l
      rw [e1, ht] at this
      exact ht1 this.symm
    obtain ⟨m, hmM, hmnc⟩ := (hq8 l).exists_noncomm (a l) hal hal1 halt
    have hcomm_eq := (hq8 l).comm_eq (a l) hal m hmM hmnc
    have h3 : a l * m = t * (m * a l) := by
      calc a l * m = (a l * m * (a l)⁻¹ * m⁻¹) * (m * a l) := by group
        _ = t * (m * a l) := by rw [hcomm_eq]
    have h4 : m * a l = t * (a l * m) := by
      calc m * a l = (t * t) * (m * a l) := by rw [ht, one_mul]
        _ = t * (t * (m * a l)) := by rw [mul_assoc]
        _ = t * (a l * m) := by rw [← h3]
    have hms : m * s * m⁻¹ = t * s := by
      have e1 : s = a l * Q := hsa.trans hQ
      have hmQ : m * Q * m⁻¹ = Q := mul_inv_eq_iff_eq_mul.mpr (hQc m hmM)
      have hma : m * a l * m⁻¹ = t * a l := by rw [h4]; group
      calc m * s * m⁻¹ = (m * a l * m⁻¹) * (m * Q * m⁻¹) := by rw [e1]; group
        _ = (t * a l) * Q := by rw [hma, hmQ]
        _ = t * s := by rw [e1]; group
    have hmee : m * (ej * ei) * m⁻¹ = ej * ei := by
      have hj' : m * ej = ej * m := hfr.cross h hlj hmM hej
      have hi' : m * ei = ei * m := hfr.cross h hli hmM hei
      calc m * (ej * ei) * m⁻¹ = (m * ej) * ei * m⁻¹ := by group
        _ = (ej * m) * ei * m⁻¹ := by rw [hj']
        _ = ej * (m * ei) * m⁻¹ := by group
        _ = ej * (ei * m) * m⁻¹ := by rw [hi']
        _ = ej * ei := by group
    rw [h2, hms] at hmee
    exact ht1 (mul_right_cancel (hmee.trans (one_mul s).symm))
end WM

end WMouter

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
