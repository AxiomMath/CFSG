module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFD3

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

section D5outer




variable {n : ℕ}


section D5

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem mem_normalizer_closure {Z : Type*} [Group Z] [Finite Z] {T : Set Z} {p : Z}
    (hp : ∀ g ∈ T, p * g * p⁻¹ ∈ Subgroup.closure T) :
    p ∈ Subgroup.normalizer (Subgroup.closure T : Set Z) := by
  have hcl : Subgroup.closure T ≤ (Subgroup.closure T).comap (MulAut.conj p).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro g hg
    show (MulAut.conj p).toMonoidHom g ∈ Subgroup.closure T
    simpa [MulAut.conj_apply] using hp g hg
  have h : ∀ v ∈ Subgroup.closure T, p * v * p⁻¹ ∈ Subgroup.closure T := fun v hv => by
    have := hcl hv
    simpa [MulAut.conj_apply] using this
  set V := Subgroup.closure T with hV
  have hle : conjSub p V ≤ V := by
    rintro _ ⟨v, hv, rfl⟩
    simpa [MulAut.conj_apply] using h v hv
  have hcard : Nat.card V ≤ Nat.card (conjSub p V) := by
    have : Nat.card (conjSub p V) = Nat.card V :=
      Subgroup.card_map_of_injective (f := (MulAut.conj p).toMonoidHom) (MulAut.conj p).injective
    omega
  have heq : conjSub p V = V := Subgroup.eq_of_le_of_card_ge hle hcard
  refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
  have h1 : p * z * p⁻¹ ∈ V ↔ z ∈ V := by
    have h2 : ∀ x : Z, x ∈ V ↔ p⁻¹ * x * p ∈ V := fun x => by
      rw [← mem_conjSub_iff, heq]
    rw [h2 (p * z * p⁻¹)]
    have : p⁻¹ * (p * z * p⁻¹) * p = z := by group
    rw [this]
  exact h1.symm

theorem WFFrame.far_q8 (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (k : Fin 4) :
    Q8Facts (conjSub y (M k)) (y * t * y⁻¹) := by
  obtain ⟨hJΩ, hJu, -⟩ := hfr.far_mem h k
  obtain ⟨e⟩ := members_q8_of_isPGroup h.hStd.perp h.exit.2.2.2.1 _ hJΩ
  exact q8Facts_of_iso hJu e

theorem WFFrame.far_comm (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {i j : Fin 4} (hij : i ≠ j) :
    Commutes (conjSub y (M i)) (conjSub y (M j)) := by
  intro m hm m' hm'
  rw [mem_conjSub_iff] at hm hm'
  have := hfr.cross h hij hm hm'
  calc m * m' = y * ((y⁻¹ * m * y) * (y⁻¹ * m' * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * m' * y) * (y⁻¹ * m * y)) * y⁻¹ := by rw [this]
    _ = m' * m := by group

theorem WFFrame.t_mem_Pg (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) :
    t ∈ conjSub y (M 0) ⊔ conjSub y (M 1) ⊔ conjSub y (M 2) ⊔ conjSub y (M 3) := by
  obtain ⟨k, hk, hkprod⟩ := wfD4_proved n Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h M a y hfr
  have hkJ : ∀ i, y * k i * y⁻¹ ∈ conjSub y (M i) := fun i => conj_mem_conjSub (hk i).1
  have e : t = (y * k 0 * y⁻¹) * (y * k 1 * y⁻¹) * (y * k 2 * y⁻¹) * (y * k 3 * y⁻¹) := by
    calc t = y * (y⁻¹ * t * y) * y⁻¹ := by group
      _ = y * (k 0 * k 1 * k 2 * k 3) * y⁻¹ := by rw [hkprod]
      _ = _ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (le_sup4 (fun i => conjSub y (M i)) 0 (hkJ 0)) (le_sup4 (fun i => conjSub y (M i)) 1 (hkJ 1)))
    (le_sup4 (fun i => conjSub y (M i)) 2 (hkJ 2))) (le_sup4 (fun i => conjSub y (M i)) 3 (hkJ 3))

theorem WFFrame.v_act_s (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {i : Fin 4} {v : Y}
    (hv : v ∈ M i) (hvW : v ∉ W) :
    v * (a 0 * a 1 * a 2 * a 3) * v⁻¹ = (a 0 * a 1 * a 2 * a 3) * t := by
  have hq := h.q8 (hfr.mem i)
  have hvN : v ∈ Subgroup.normalizer (W : Set Y) :=
    (twin_mem_DSet h.partI h.exit.2.2.2.1 h.hW h.t_mem (hfr.mem i).1 (h.uniqInv (hfr.mem i))).2 hv
  have hvai : v * a i * v⁻¹ = a i * t := by
    have h1 : v * a i * v⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hvN (a i)).mp (hfr.haW i)
    have h2 : v * a i * v⁻¹ ∈ M i := (M i).mul_mem ((M i).mul_mem hv (hfr.haM i)) ((M i).inv_mem hv)
    have h3 : (v * a i * v⁻¹) * (v * a i * v⁻¹) = t := by
      calc (v * a i * v⁻¹) * (v * a i * v⁻¹) = v * (a i * a i) * v⁻¹ := by group
        _ = v * t * v⁻¹ := by rw [hfr.sq h i]
        _ = t := by rw [← hfr.t_comm h i hv]; group
    have hcomm := h.abelian _ (hfr.haW i) _ h1
    rcases eq_or_mul_t_of_comm hq (hfr.haM i) h2 (hfr.sq h i) h3 hcomm with e | e
    · exfalso
      have hc : v * a i = a i * v := mul_inv_eq_iff_eq_mul.mp e
      rcases hq.cent_cyc (a i) (hfr.haM i) (hfr.sq h i) v hv hc with e1 | e1 | e1 | e1
      · exact hvW (by rw [e1]; exact W.one_mem)
      · exact hvW (by rw [e1]; exact hfr.haW i)
      · exact hvW (by rw [e1]; exact h.t_mem)
      · exact hvW (by rw [e1]; exact W.mul_mem (hfr.haW i) h.t_mem)
    · exact e
  have hvap : ∀ p, p ≠ i → v * a p * v⁻¹ = a p := fun p hp =>
    mul_inv_eq_iff_eq_mul.mpr (hfr.cross h (Ne.symm hp) hv (hfr.haM p))
  obtain ⟨c, hc⟩ : ∃ c : Fin 4 → Y, ∀ p, c p = if p = i then t else 1 := ⟨_, fun _ => rfl⟩
  have hvp : ∀ p, v * a p * v⁻¹ = a p * c p := fun p => by
    by_cases hp : p = i
    · subst hp; rw [hc, if_pos rfl]; exact hvai
    · rw [hc, if_neg hp, mul_one]; exact hvap p hp
  have hcc : c 0 * c 1 * c 2 * c 3 = t := by
    simp only [hc]
    fin_cases i <;> simp
  have hti : ∀ p, t * a p = a p * t := fun p => hfr.t_comm h p (hfr.haM p)
  have hac : ∀ p q, a p * c q = c q * a p := fun p q => by
    rw [hc]; split_ifs
    · exact (hti p).symm
    · simp
  have e : v * (a 0 * a 1 * a 2 * a 3) * v⁻¹ =
      (v * a 0 * v⁻¹) * (v * a 1 * v⁻¹) * (v * a 2 * v⁻¹) * (v * a 3 * v⁻¹) := by group
  rw [e, hvp 0, hvp 1, hvp 2, hvp 3]
  rw [← hcc, ← prod4_mul2 (hac 1 0) (hac 2 0) (hac 2 1) (hac 3 0) (hac 3 1) (hac 3 2)]

theorem WFFrame.split_gen (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {k : Fin 4 → Y}
    (hk : ∀ i, k i ∈ M i) (l : Fin 4) :
    ∃ Q : Y, k 0 * k 1 * k 2 * k 3 = k l * Q ∧ ∀ m ∈ M l, m * Q = Q * m := by
  have hc : ∀ p q : Fin 4, p ≠ q → k p * k q = k q * k p := fun p q hpq =>
    hfr.cross h hpq (hk p) (hk q)
  have hcr : ∀ p q : Fin 4, p ≠ q → ∀ m ∈ M p, m * k q = k q * m := fun p q hpq m hm =>
    hfr.cross h hpq hm (hk q)
  have c2 : ∀ p q r : Fin 4, q ≠ p → r ≠ p → ∀ m ∈ M p, m * (k q * k r) = (k q * k r) * m :=
    fun p q r hq hr m hm => by
      calc m * (k q * k r) = (m * k q) * k r := (mul_assoc _ _ _).symm
        _ = (k q * m) * k r := by rw [hcr p q (Ne.symm hq) m hm]
        _ = k q * (m * k r) := mul_assoc _ _ _
        _ = k q * (k r * m) := by rw [hcr p r (Ne.symm hr) m hm]
        _ = (k q * k r) * m := (mul_assoc _ _ _).symm
  have c3 : ∀ p q r r' : Fin 4, q ≠ p → r ≠ p → r' ≠ p → ∀ m ∈ M p,
      m * (k q * k r * k r') = (k q * k r * k r') * m := fun p q r r' hq hr hr' m hm => by
    calc m * (k q * k r * k r') = (m * (k q * k r)) * k r' := (mul_assoc _ _ _).symm
      _ = ((k q * k r) * m) * k r' := by rw [c2 p q r hq hr m hm]
      _ = (k q * k r) * (m * k r') := mul_assoc _ _ _
      _ = (k q * k r) * (k r' * m) := by rw [hcr p r' (Ne.symm hr') m hm]
      _ = (k q * k r * k r') * m := (mul_assoc _ _ _).symm
  fin_cases l
  · refine ⟨k 1 * k 2 * k 3, ?_, fun m hm => c3 0 1 2 3 (by decide) (by decide) (by decide) m hm⟩
    show k 0 * k 1 * k 2 * k 3 = k 0 * (k 1 * k 2 * k 3)
    group
  · refine ⟨k 0 * k 2 * k 3, ?_, fun m hm => c3 1 0 2 3 (by decide) (by decide) (by decide) m hm⟩
    calc k 0 * k 1 * k 2 * k 3 = (k 0 * k 1) * k 2 * k 3 := rfl
      _ = (k 1 * k 0) * k 2 * k 3 := by rw [hc 0 1 (by decide)]
      _ = k 1 * (k 0 * k 2 * k 3) := by group
  · refine ⟨k 0 * k 1 * k 3, ?_, fun m hm => c3 2 0 1 3 (by decide) (by decide) (by decide) m hm⟩
    calc k 0 * k 1 * k 2 * k 3 = k 0 * (k 1 * k 2) * k 3 := by group
      _ = k 0 * (k 2 * k 1) * k 3 := by rw [hc 1 2 (by decide)]
      _ = (k 0 * k 2) * k 1 * k 3 := by group
      _ = (k 2 * k 0) * k 1 * k 3 := by rw [hc 0 2 (by decide)]
      _ = k 2 * (k 0 * k 1 * k 3) := by group
  · refine ⟨k 0 * k 1 * k 2, ?_, fun m hm => c3 3 0 1 2 (by decide) (by decide) (by decide) m hm⟩
    calc k 0 * k 1 * k 2 * k 3 = k 0 * k 1 * (k 2 * k 3) := by group
      _ = k 0 * k 1 * (k 3 * k 2) := by rw [hc 2 3 (by decide)]
      _ = k 0 * (k 1 * k 3) * k 2 := by group
      _ = k 0 * (k 3 * k 1) * k 2 := by rw [hc 1 3 (by decide)]
      _ = (k 0 * k 3) * k 1 * k 2 := by group
      _ = (k 3 * k 0) * k 1 * k 2 := by rw [hc 0 3 (by decide)]
      _ = k 3 * (k 0 * k 1 * k 2) := by group

theorem WFFrame.prod_not_pair (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {k : Fin 4 → Y}
    (hk : ∀ i, k i ∈ M i ∧ k i * k i = t) {i j : Fin 4} (hij : i ≠ j) {n n' : Y}
    (hn : n ∈ M i) (hn' : n' ∈ M j) : k 0 * k 1 * k 2 * k 3 ≠ n * n' := by
  intro heq
  obtain ⟨l, hli, hlj⟩ := fin4_other i j hij
  obtain ⟨Q, hQ, hQc⟩ := hfr.split_gen h (fun p => (hk p).1) l
  have hq := h.q8 (hfr.mem l)
  have ht := hq.z_sq
  have ht1 := hq.z_ne
  have hal1 : k l ≠ 1 := fun e1 => by
    have := (hk l).2
    rw [e1, one_mul] at this
    exact ht1 this.symm
  have halt : k l ≠ t := fun e1 => by
    have := (hk l).2
    rw [e1, ht] at this
    exact ht1 this.symm
  obtain ⟨m, hmM, hmnc⟩ := hq.exists_noncomm (k l) (hk l).1 hal1 halt
  have hcomm_eq := hq.comm_eq (k l) (hk l).1 m hmM hmnc
  have h3 : k l * m = t * (m * k l) := by
    calc k l * m = (k l * m * (k l)⁻¹ * m⁻¹) * (m * k l) := by group
      _ = t * (m * k l) := by rw [hcomm_eq]
  have h4 : m * k l = t * (k l * m) := by
    calc m * k l = (t * t) * (m * k l) := by rw [ht, one_mul]
      _ = t * (t * (m * k l)) := by rw [mul_assoc]
      _ = t * (k l * m) := by rw [← h3]
  have hmQ : m * Q * m⁻¹ = Q := mul_inv_eq_iff_eq_mul.mpr (hQc m hmM)
  have hma : m * k l * m⁻¹ = t * k l := by rw [h4]; group
  have hms : m * (k 0 * k 1 * k 2 * k 3) * m⁻¹ = t * (k 0 * k 1 * k 2 * k 3) := by
    calc m * (k 0 * k 1 * k 2 * k 3) * m⁻¹ = (m * k l * m⁻¹) * (m * Q * m⁻¹) := by rw [hQ]; group
      _ = (t * k l) * Q := by rw [hma, hmQ]
      _ = t * (k 0 * k 1 * k 2 * k 3) := by rw [hQ]; group
  have hmn : m * (n * n') * m⁻¹ = n * n' := by
    have hj' : m * n' = n' * m := hfr.cross h hlj hmM hn'
    have hi' : m * n = n * m := hfr.cross h hli hmM hn
    calc m * (n * n') * m⁻¹ = (m * n) * n' * m⁻¹ := by group
      _ = (n * m) * n' * m⁻¹ := by rw [hi']
      _ = n * (m * n') * m⁻¹ := by group
      _ = n * (n' * m) * m⁻¹ := by rw [hj']
      _ = n * n' := by group
  rw [heq, hmn] at hms
  exact ht1 (by
    have h5 : t * (n * n') = 1 * (n * n') := by rw [one_mul]; exact hms.symm
    exact mul_right_cancel h5)

theorem WFFrame.t_not_mem_pair (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {k l : Fin 4} (hkl : k ≠ l) :
    t ∉ conjSub y (M k) ⊔ conjSub y (M l) := by
  intro hmem
  obtain ⟨mk, hmk, ml, hml, hprod⟩ := mem_sup2 (hfr.far_comm h hkl) hmem
  obtain ⟨kk, hkk, hkprod⟩ := wfD4_proved n Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h M a y hfr
  refine hfr.prod_not_pair h hkk hkl (mem_conjSub_iff.mp hmk) (mem_conjSub_iff.mp hml) ?_
  rw [← hkprod]
  calc y⁻¹ * t * y = y⁻¹ * (mk * ml) * y := by rw [← hprod]
    _ = (y⁻¹ * mk * y) * (y⁻¹ * ml * y) := by group

theorem WFFrame.d5_commutator (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) (k : Fin 4) {v : Y} (hv : v ∈ conjSub y (M k)) :
    (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * v * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹)⁻¹ * v⁻¹ = 1 ∨
      (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹) * v * (x * (a 0 * a 1 * a 2 * a 3) * x⁻¹)⁻¹ * v⁻¹ =
        a 0 * a 1 * a 2 * a 3 := by
  have hd := h.hStd.datum
  have ht := (h.q8 (hfr.mem 0)).z_sq
  have ht1 := (h.q8 (hfr.mem 0)).z_ne
  obtain ⟨s, hs⟩ : ∃ s, s = a 0 * a 1 * a 2 * a 3 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ := ⟨_, rfl⟩
  have hs2 : s * s = 1 := by rw [hs]; exact hfr.s_sq h
  have hts : t * s = s * t := by rw [hs]; exact hfr.s_comm_t h
  have hee : e * e = 1 := by rw [he]; exact hfr.d1_ee h x
  have hes : e * s = s * e := by rw [he, hs]; exact hfr.d1_es h hxo hxt hxM hmv
  have het : e * t = t * e := by rw [he]; exact hfr.d1_et h hxt
  obtain ⟨hne1, hnet, hnes, hnest⟩ := hfr.d1_ne h hxo hxt hxM hmv
  rw [← he] at hne1 hnet hnes hnest
  rw [← hs] at hnes hnest
  have he' : e = x * s * x⁻¹ := by rw [he, hs]
  have hD3 : ∀ i, conjSub e (conjSub y (M i)) = conjSub y (M i) := fun i => by
    rw [he]; exact hfr.d3 h hxo hxt hxM hmv i
  have hsy : y * t * y⁻¹ = s := by rw [hs]; exact hfr.fuse
  rw [← he, ← hs]
  have hMne : ∀ p q : Fin 4, p ≠ q → M p ≠ M q := fun p q hpq e => hpq (hfr.inj e)
  have hJq : ∀ i, Q8Facts (conjSub y (M i)) s := fun i => by
    have := hfr.far_q8 h i
    rwa [hsy] at this
  have hJu : ∀ i, IsUniqueInvolution (conjSub y (M i)) s := fun i => by
    have := (hfr.far_mem h i).2.1
    rwa [hsy] at this
  have hJΩ : ∀ i, conjSub y (M i) ∈ CoreAssembly.conjClass (tightCore R) := fun i =>
    (hfr.far_mem h i).1
  have hJcom := fun i j (hij : i ≠ j) => hfr.far_comm h hij
  have hBa : ∀ q : Y, q * (x * (a 0 * a 1) * x⁻¹) = (x * (a 0 * a 1) * x⁻¹) * q →
      (q * e * q⁻¹ = 1 ∨ q * e * q⁻¹ = t ∨ q * e * q⁻¹ = e ∨ q * e * q⁻¹ = t * e) := by
    intro q hq
    have hsF : s ∈ FrameInv (CoreAssembly.conjClass (tightCore R)) K W := by
      rw [hs]
      exact ⟨M, a, hfr.inj, hfr.mem, fun p => ⟨Subgroup.mem_inf.mpr ⟨hfr.haM p, hfr.haW p⟩,
        hfr.ha4 p⟩, rfl⟩
    have hnorm := hB Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h W h.hW h.t_mem (M 0) (hfr.mem 0) (M 1)
      (hfr.mem 1) (hMne 0 1 (by decide)) (a 0) (Subgroup.mem_inf.mpr ⟨hfr.haM 0, hfr.haW 0⟩) (a 1)
      (Subgroup.mem_inf.mpr ⟨hfr.haM 1, hfr.haW 1⟩) (hfr.ha4 0) (hfr.ha4 1) s hsF
    have hq' : x⁻¹ * q * x ∈ Subgroup.centralizer ({a 0 * a 1} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc x⁻¹ * q * x * (a 0 * a 1) = x⁻¹ * (q * (x * (a 0 * a 1) * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * (a 0 * a 1) * x⁻¹) * q) * x := by rw [hq]
        _ = (a 0 * a 1) * (x⁻¹ * q * x) := by group
    have hs' : (x⁻¹ * q * x) * s * (x⁻¹ * q * x)⁻¹ ∈ Subgroup.closure ({t, s} : Set Y) :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hq') s).mp (Subgroup.subset_closure (by simp))
    have hqe : q * e * q⁻¹ = x * ((x⁻¹ * q * x) * s * (x⁻¹ * q * x)⁻¹) * x⁻¹ := by
      rw [he']; group
    have hxti : x * t * x⁻¹ = t := by rw [hxt]; group
    rcases klein_closure ht hs2 hts _ hs' with e1 | e1 | e1 | e1
    · left; rw [hqe, e1]; group
    · right; left; rw [hqe, e1, hxti]
    · right; right; left; rw [hqe, e1, he']
    · right; right; right
      rw [hqe, e1]
      calc x * (t * s) * x⁻¹ = (x * t * x⁻¹) * (x * s * x⁻¹) := by group
        _ = t * e := by rw [hxti, he']
  obtain ⟨hv0M, hv0W⟩ := hfr.u_notW h hxo hxt hxM (hmv 0)
  obtain ⟨hv1M, hv1W⟩ := hfr.u_notW h hxo hxt hxM (hmv 1)
  obtain ⟨ua, hua⟩ : ∃ ua, ua = (x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) := ⟨_, rfl⟩
  have huax : ua = x * (a 0 * a 1) * x⁻¹ := by rw [hua]; group
  have hua2 : ua * ua = 1 := by
    rw [huax]
    have h01 : (a 0 * a 1) * (a 0 * a 1) = 1 := by
      have hcm := hfr.comm_a h 0 1
      calc (a 0 * a 1) * (a 0 * a 1) = a 0 * (a 1 * a 0) * a 1 := by group
        _ = a 0 * (a 0 * a 1) * a 1 := by rw [← hcm]
        _ = (a 0 * a 0) * (a 1 * a 1) := by group
        _ = 1 := by rw [hfr.sq h 0, hfr.sq h 1, ht]
    calc x * (a 0 * a 1) * x⁻¹ * (x * (a 0 * a 1) * x⁻¹) =
        x * ((a 0 * a 1) * (a 0 * a 1)) * x⁻¹ := by group
      _ = 1 := by rw [h01]; group
  have hv0t : (x * a 0 * x⁻¹) * t * (x * a 0 * x⁻¹)⁻¹ = t :=
    mul_inv_eq_iff_eq_mul.mpr (hfr.t_comm h 0 hv0M).symm
  have huas : ua * s * ua⁻¹ = s := by
    have h0 := hfr.v_act_s h hv0M hv0W
    have h1 := hfr.v_act_s h hv1M hv1W
    rw [← hs] at h0 h1
    calc ua * s * ua⁻¹ = (x * a 0 * x⁻¹) * ((x * a 1 * x⁻¹) * s * (x * a 1 * x⁻¹)⁻¹) *
          (x * a 0 * x⁻¹)⁻¹ := by rw [hua]; group
      _ = (x * a 0 * x⁻¹) * (s * t) * (x * a 0 * x⁻¹)⁻¹ := by rw [h1]
      _ = ((x * a 0 * x⁻¹) * s * (x * a 0 * x⁻¹)⁻¹) *
            ((x * a 0 * x⁻¹) * t * (x * a 0 * x⁻¹)⁻¹) := by group
      _ = (s * t) * t := by rw [h0, hv0t]
      _ = s := by rw [mul_assoc, ht, mul_one]
  have hmove : conjSub ua (conjSub y (M k)) ≠ conjSub y (M k) := by
    rw [hua]
    exact wfWM_proved n Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h M a y hfr 0 1 (by decide) _ hv0M hv0W _
      hv1M hv1W k
  have hJ'Ω : conjSub ua (conjSub y (M k)) ∈ CoreAssembly.conjClass (tightCore R) :=
    h.hyp.conjInvariant ua _ (hJΩ k)
  have hJ'u : IsUniqueInvolution (conjSub ua (conjSub y (M k))) s := by
    have := (hJu k).conj ua
    rwa [huas] at this
  obtain ⟨l, hl⟩ : ∃ l, conjSub y (M l) = conjSub ua (conjSub y (M k)) := by
    have h1 : IsUniqueInvolution (conjSub y⁻¹ (conjSub ua (conjSub y (M k)))) t := by
      have := hJ'u.conj y⁻¹
      have e : y⁻¹ * s * y⁻¹⁻¹ = t := by rw [← hsy]; group
      rwa [e] at this
    have h2 : conjSub y⁻¹ (conjSub ua (conjSub y (M k))) ∈
        twinSet (CoreAssembly.conjClass (tightCore R)) K :=
      ⟨h.hyp.conjInvariant _ _ hJ'Ω, t, hd.hz, h1⟩
    obtain ⟨l, hl⟩ := hfr.surj _ h2
    exact ⟨l, by rw [hl, conjSub_conjSub_inv]⟩
  have hlk : l ≠ k := fun e => hmove (by rw [← hl, e])
  obtain ⟨v', hv'd⟩ : ∃ v', v' = ua * v * ua⁻¹ := ⟨_, rfl⟩
  have hv'l : v' ∈ conjSub y (M l) := by
    rw [hl, hv'd]; exact conj_mem_conjSub hv
  have hcvv : v * v' = v' * v := hJcom k l (Ne.symm hlk) v hv v' hv'l
  obtain ⟨q, hq⟩ : ∃ q, q = v * v' := ⟨_, rfl⟩
  have hqua : q * ua = ua * q := by
    have h1 : ua * v' * ua⁻¹ = v := by
      rw [hv'd]
      calc ua * (ua * v * ua⁻¹) * ua⁻¹ = (ua * ua) * v * (ua * ua)⁻¹ := by group
        _ = v := by rw [hua2]; group
    have : ua * q * ua⁻¹ = q := by
      rw [hq]
      calc ua * (v * v') * ua⁻¹ = (ua * v * ua⁻¹) * (ua * v' * ua⁻¹) := by group
        _ = v' * v := by rw [← hv'd, h1]
        _ = v * v' := hcvv.symm
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  have hqe := hBa q (by rw [← huax]; exact hqua)
  have hqP : q ∈ conjSub y (M 0) ⊔ conjSub y (M 1) ⊔ conjSub y (M 2) ⊔ conjSub y (M 3) := by
    have hk' := le_sup4 (fun i => conjSub y (M i)) k
    have hl' := le_sup4 (fun i => conjSub y (M i)) l
    rw [hq]
    exact Subgroup.mul_mem _ (hk' hv) (hl' hv'l)
  have hqe' : q * e * q⁻¹ = e ∨ q * e * q⁻¹ = t * e := by
    rcases hqe with e1 | e1 | e1 | e1
    · exfalso
      apply hne1
      have : e = q⁻¹ * (q * e * q⁻¹) * q := by group
      rw [this, e1]; group
    · exfalso
      have hee' : e = q⁻¹ * t * q⁻¹⁻¹ := by
        calc e = q⁻¹ * (q * e * q⁻¹) * q := by group
          _ = q⁻¹ * t * q⁻¹⁻¹ := by rw [e1]; group
      have hP' := P_comm_center (J := fun i => conjSub y (M i)) (fun i => hJq i) hJcom
        (r := q⁻¹) (q := t) (Subgroup.inv_mem _ hqP) (hfr.t_mem_Pg h)
      rcases hP' with e2 | e2
      · exact hnet (by rw [hee']; exact mul_inv_eq_one.mp e2)
      · exact hnest (by rw [hee']; exact mul_inv_eq_iff_eq_mul.mp e2)
    · exact Or.inl e1
    · exact Or.inr e1
  have hcomm_qe : q * e * q⁻¹ * e⁻¹ = 1 ∨ q * e * q⁻¹ * e⁻¹ = t := by
    rcases hqe' with e1 | e1
    · left; rw [e1]; group
    · right; rw [e1]; group
  have hev : ∀ w ∈ conjSub y (M k), e * w * e⁻¹ ∈ conjSub y (M k) := fun w hw => by
    have := conj_mem_conjSub (n := e) hw
    rwa [hD3 k] at this
  have hev' : ∀ w ∈ conjSub y (M l), e * w * e⁻¹ ∈ conjSub y (M l) := fun w hw => by
    have := conj_mem_conjSub (n := e) hw
    rwa [hD3 l] at this
  have hqJ : q * e * q⁻¹ * e⁻¹ ∈ conjSub y (M k) ⊔ conjSub y (M l) := by
    have e1 : q * e * q⁻¹ * e⁻¹ = (v * v') * (e * v' * e⁻¹)⁻¹ * (e * v * e⁻¹)⁻¹ := by
      rw [hq]; group
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hv)
      (Subgroup.mem_sup_right hv'l)) (Subgroup.inv_mem _ (Subgroup.mem_sup_right (hev' _ hv'l))))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left (hev _ hv)))
  have hqe1 : q * e * q⁻¹ * e⁻¹ = 1 := by
    rcases hcomm_qe with e1 | e1
    · exact e1
    · exact absurd (e1 ▸ hqJ) (hfr.t_not_mem_pair h (Ne.symm hlk))
  have hqe_comm : q * e = e * q := by
    have h1 : q * e * q⁻¹ = e := mul_inv_eq_one.mp hqe1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hc1 : v⁻¹ * (e * v * e⁻¹) ∈ conjSub y (M k) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) (hev v hv)
  have hc2 : v⁻¹ * (e * v * e⁻¹) = v' * (e * v' * e⁻¹)⁻¹ := by
    have hq' : (e * v * e⁻¹) * (e * v' * e⁻¹) = v * v' := by
      have : e * (v * v') * e⁻¹ = v * v' := by
        rw [← hq]; exact mul_inv_eq_iff_eq_mul.mpr hqe_comm.symm
      calc (e * v * e⁻¹) * (e * v' * e⁻¹) = e * (v * v') * e⁻¹ := by group
        _ = v * v' := this
    calc v⁻¹ * (e * v * e⁻¹) =
        v⁻¹ * ((e * v * e⁻¹) * (e * v' * e⁻¹)) * (e * v' * e⁻¹)⁻¹ := by group
      _ = v⁻¹ * (v * v') * (e * v' * e⁻¹)⁻¹ := by rw [hq']
      _ = v' * (e * v' * e⁻¹)⁻¹ := by group
  have hc3 : v⁻¹ * (e * v * e⁻¹) ∈ conjSub y (M l) := by
    rw [hc2]; exact Subgroup.mul_mem _ hv'l (Subgroup.inv_mem _ (hev' _ hv'l))
  have hcen : ∀ g ∈ conjSub y (M k), (v⁻¹ * (e * v * e⁻¹)) * g = g * (v⁻¹ * (e * v * e⁻¹)) :=
    fun g hg => (hJcom k l (Ne.symm hlk) g hg _ hc3).symm
  rcases (hJq k).center _ hc1 hcen with e1 | e1
  · left
    calc e * v * e⁻¹ * v⁻¹ = v * (v⁻¹ * (e * v * e⁻¹)) * v⁻¹ := by group
      _ = 1 := by rw [e1]; group
  · right
    calc e * v * e⁻¹ * v⁻¹ = v * (v⁻¹ * (e * v * e⁻¹)) * v⁻¹ := by group
      _ = v * s * v⁻¹ := by rw [e1]
      _ = s := mul_inv_eq_iff_eq_mul.mpr ((hJq k).z_central v hv).symm

theorem WFFrame.d5 (hB : WFB0 n) (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J)
    (hmv : ∀ i, ¬ ∀ m ∈ M i, x * m = m * x) :
    conjSub y (M 0) ⊔ conjSub y (M 1) ⊔ conjSub y (M 2) ⊔ conjSub y (M 3) ≤
      Subgroup.normalizer (Subgroup.closure ({t, a 0 * a 1 * a 2 * a 3,
        x * (a 0 * a 1 * a 2 * a 3) * x⁻¹} : Set Y) : Set Y) := by
  have hsy : y * t * y⁻¹ = a 0 * a 1 * a 2 * a 3 := hfr.fuse
  obtain ⟨s, hs⟩ : ∃ s, s = a 0 * a 1 * a 2 * a 3 := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ := ⟨_, rfl⟩
  have hs2 : s * s = 1 := by rw [hs]; exact hfr.s_sq h
  have hJq : ∀ i, Q8Facts (conjSub y (M i)) s := fun i => by
    have := hfr.far_q8 h i
    rwa [hsy, ← hs] at this
  have hJcom := fun i j (hij : i ≠ j) => hfr.far_comm h hij
  have hcomm_ce : ∀ k, ∀ v ∈ conjSub y (M k), e * v * e⁻¹ * v⁻¹ = 1 ∨ e * v * e⁻¹ * v⁻¹ = s := by
    intro k v hv
    have := hfr.d5_commutator hB h hxo hxt hxM hmv k hv
    rwa [← he, ← hs] at this
  rw [← he, ← hs]
  have hsA : ∀ g ∈ conjSub y (M 0) ⊔ conjSub y (M 1) ⊔ conjSub y (M 2) ⊔ conjSub y (M 3),
      s * g = g * s := fun g hg =>
    (Subgroup.mem_centralizer_singleton_iff.mp (P_le_centralizer (J := fun i => conjSub y (M i))
      hJq hg)).symm
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hB' : conjSub y (M 0) ⊔ conjSub y (M 1) ⊔ conjSub y (M 2) ⊔ conjSub y (M 3) ≤
      commSub (conjSub y (M 0) ⊔ conjSub y (M 1) ⊔ conjSub y (M 2) ⊔ conjSub y (M 3)) s e hs2 hsA := by
    have : ∀ k, conjSub y (M k) ≤
        commSub (conjSub y (M 0) ⊔ conjSub y (M 1) ⊔ conjSub y (M 2) ⊔ conjSub y (M 3)) s e hs2 hsA := by
      intro k g hg
      refine ⟨le_sup4 (fun i => conjSub y (M i)) k hg, ?_⟩
      have e1 : g * e * g⁻¹ * e⁻¹ = (e * g * e⁻¹ * g⁻¹)⁻¹ := by group
      rcases hcomm_ce k g hg with e2 | e2
      · left; rw [e1, e2]; group
      · right; rw [e1, e2, hsi]
    exact sup_le (sup_le (sup_le (this 0) (this 1)) (this 2)) (this 3)
  intro p hp
  have hpe : p * e * p⁻¹ * e⁻¹ = 1 ∨ p * e * p⁻¹ * e⁻¹ = s := (hB' hp).2
  have hpt : p * t * p⁻¹ * t⁻¹ = 1 ∨ p * t * p⁻¹ * t⁻¹ = s :=
    P_comm_center (J := fun i => conjSub y (M i)) hJq hJcom hp (hfr.t_mem_Pg h)
  have hps : p * s * p⁻¹ = s := mul_inv_eq_iff_eq_mul.mpr (hsA p hp).symm
  apply mem_normalizer_closure
  intro g hg
  have hts_mem : t ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have hs_mem : s ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  have he_mem : e ∈ Subgroup.closure ({t, s, e} : Set Y) := Subgroup.subset_closure (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rcases hpt with e1 | e1
    · have : p * g * p⁻¹ = g := mul_inv_eq_one.mp e1
      rw [this]; exact hts_mem
    · have : p * g * p⁻¹ = s * g := mul_inv_eq_iff_eq_mul.mp e1
      rw [this]; exact Subgroup.mul_mem _ hs_mem hts_mem
  · rw [hps]; exact hs_mem
  · rcases hpe with e1 | e1
    · have : p * g * p⁻¹ = g := mul_inv_eq_one.mp e1
      rw [this]; exact he_mem
    · have : p * g * p⁻¹ = s * g := mul_inv_eq_iff_eq_mul.mp e1
      rw [this]; exact Subgroup.mul_mem _ hs_mem he_mem

end D5

end D5outer

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
