module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFStepC
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFAssemble
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFGen

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

section StepCEnd




variable {n : ℕ}

section Gen4

variable {Z : Type*} [Group Z]

theorem conjSub_le_centralizer_conj {A : Subgroup Z} {t : Z} (g : Z)
    (h : A ≤ Subgroup.centralizer ({t} : Set Z)) :
    conjSub g A ≤ Subgroup.centralizer ({g * t * g⁻¹} : Set Z) := by
  intro z hz
  rw [mem_conjSub_iff] at hz
  have h1 := Subgroup.mem_centralizer_singleton_iff.mp (h hz)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc z * (g * t * g⁻¹) = g * ((g⁻¹ * z * g) * t) * g⁻¹ := by group
    _ = g * (t * (g⁻¹ * z * g)) * g⁻¹ := by rw [h1]
    _ = (g * t * g⁻¹) * z := by group

theorem conjSub_normal_conj {N : Subgroup Z} {t : Z} (g : Z)
    (hn : (N.subgroupOf (Subgroup.centralizer ({t} : Set Z))).Normal) :
    ((conjSub g N).subgroupOf (Subgroup.centralizer ({g * t * g⁻¹} : Set Z))).Normal := by
  have hconj : ∀ w : ↥(Subgroup.centralizer ({g * t * g⁻¹} : Set Z)),
      g⁻¹ * (w : Z) * g ∈ Subgroup.centralizer ({t} : Set Z) := fun w => by
    have hwc := Subgroup.mem_centralizer_singleton_iff.mp w.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * (w : Z) * g * t = g⁻¹ * ((w : Z) * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * (w : Z)) * g := by rw [hwc]
      _ = t * (g⁻¹ * (w : Z) * g) := by group
  refine ⟨fun a ha b => ?_⟩
  rw [Subgroup.mem_subgroupOf] at ha ⊢
  rw [mem_conjSub_iff] at ha ⊢
  have h1 := hn.conj_mem ⟨g⁻¹ * (a : Z) * g, hconj a⟩ (Subgroup.mem_subgroupOf.mpr ha)
    ⟨g⁻¹ * (b : Z) * g, hconj b⟩
  have h2 := Subgroup.mem_subgroupOf.mp h1
  have e : g⁻¹ * ((b : Z) * (a : Z) * (b : Z)⁻¹) * g =
      g⁻¹ * (b : Z) * g * (g⁻¹ * (a : Z) * g) * (g⁻¹ * (b : Z) * g)⁻¹ := by group
  simpa [Subgroup.coe_mul, Subgroup.coe_inv, e] using h2

theorem le_sup4 (J : Fin 4 → Subgroup Z) (i : Fin 4) : J i ≤ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 := by
  fin_cases i
  · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem sup4_conj_mem {A B : Fin 4 → Subgroup Z} (hA : ∀ i j, i ≠ j → Commutes (A i) (A j)) (c : Z)
    (hmap : ∀ i, ∃ j, conjSub c (A i) = B j) {p : Z} (hp : p ∈ A 0 ⊔ A 1 ⊔ A 2 ⊔ A 3) :
    c * p * c⁻¹ ∈ B 0 ⊔ B 1 ⊔ B 2 ⊔ B 3 := by
  obtain ⟨p₀, h₀, p₁, h₁, p₂, h₂, p₃, h₃, rfl⟩ := mem_sup4 (hA 0 1 (by decide)) (hA 0 2 (by decide))
    (hA 0 3 (by decide)) (hA 1 2 (by decide)) (hA 1 3 (by decide)) (hA 2 3 (by decide)) hp
  have hB : ∀ i, ∀ q ∈ A i, c * q * c⁻¹ ∈ B 0 ⊔ B 1 ⊔ B 2 ⊔ B 3 := fun i q hq => by
    obtain ⟨j, hj⟩ := hmap i
    have := conj_mem_conjSub (n := c) hq
    rw [hj] at this
    exact le_sup4 B j this
  have e : c * (p₀ * p₁ * p₂ * p₃) * c⁻¹ =
      (c * p₀ * c⁻¹) * (c * p₁ * c⁻¹) * (c * p₂ * c⁻¹) * (c * p₃ * c⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hB 0 _ h₀) (hB 1 _ h₁)) (hB 2 _ h₂))
    (hB 3 _ h₃)

theorem fin4_three : ∀ c : Fin 4, ∃ i₁ i₂ i₃ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ i₃ ∧ i₂ ≠ i₃ ∧ i₁ ≠ c ∧ i₂ ≠ c ∧
    i₃ ≠ c := by
  decide +kernel

theorem prod_coeff {t : Z} (ht : t * t = 1) {c : Fin 4 → Z} {c₀ : Fin 4} (h1 : c c₀ = 1)
    (h2 : ∀ i, i ≠ c₀ → c i = t) : c 0 * c 1 * c 2 * c 3 = t := by
  have key : ∀ c₀ : Fin 4, c c₀ = 1 → (∀ i, i ≠ c₀ → c i = t) → c 0 * c 1 * c 2 * c 3 = t := by
    intro c₀
    fin_cases c₀
    · intro h1 h2
      have e0 : c 0 = 1 := h1
      rw [e0, h2 1 (by decide), h2 2 (by decide), h2 3 (by decide)]
      calc 1 * t * t * t = (t * t) * t := by group
        _ = t := by rw [ht, one_mul]
    · intro h1 h2
      have e0 : c 1 = 1 := h1
      rw [e0, h2 0 (by decide), h2 2 (by decide), h2 3 (by decide)]
      calc t * 1 * t * t = t * (t * t) := by group
        _ = t := by rw [ht, mul_one]
    · intro h1 h2
      have e0 : c 2 = 1 := h1
      rw [e0, h2 0 (by decide), h2 1 (by decide), h2 3 (by decide)]
      calc t * t * 1 * t = (t * t) * t := by group
        _ = t := by rw [ht, one_mul]
    · intro h1 h2
      have e0 : c 3 = 1 := h1
      rw [e0, h2 0 (by decide), h2 1 (by decide), h2 2 (by decide)]
      calc t * t * t * 1 = (t * t) * t := by group
        _ = t := by rw [ht, one_mul]
  exact key c₀ h1 h2

end Gen4
section Frame4

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem WFFrame.sup_eq (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) :
    (⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, J : Subgroup Y) =
      M 0 ⊔ M 1 ⊔ M 2 ⊔ M 3 := by
  apply le_antisymm
  · refine iSup₂_le fun J hJ => ?_
    obtain ⟨i, rfl⟩ := hfr.surj J hJ
    exact le_sup4 M i
  · have hle : ∀ i, M i ≤ (⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, J : Subgroup Y) :=
      fun i => le_iSup₂ (f := fun (J : Subgroup Y)
        (_ : J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K) => J) (M i) (hfr.mem i)
    exact sup_le (sup_le (sup_le (hle 0) (hle 1)) (hle 2)) (hle 3)

theorem WFIn.odd_pow (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {N : Subgroup Y}
    (hN : WFOddNormal (Subgroup.centralizer ({t} : Set Y))
      (⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, J) N) :
    ∀ g ∈ N, ∃ m : ℕ, Odd m ∧
      g ^ m ∈ (⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, J : Subgroup Y) := by
  obtain ⟨hNC, hNn, hPN, hodd⟩ := hN
  have hPn := v3_P_normalTwo h.hStd h.exit.2.2.2.1
  have hnorm : ((⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, J : Subgroup Y).subgroupOf N).Normal := by
    refine ⟨fun a' ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hPn.2.2 (g : Y) (by
      have := hNC g.2
      exact this) (a' : Y) ha
  exact exists_odd_pow_mem hnorm hodd

theorem WFFrame.c6_core (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) {x : Y}
    (hxo : Odd (orderOf x)) (hxt : x * t = t * x)
    (hxM : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) K, conjSub x J = J) {k : Fin 4 → Y}
    (hk : ∀ i, k i ∈ M i ∧ k i * k i = t)
    (hc : x * (k 0 * k 1 * k 2 * k 3) * x⁻¹ * (k 0 * k 1 * k 2 * k 3)⁻¹ = 1 ∨
      x * (k 0 * k 1 * k 2 * k 3) * x⁻¹ * (k 0 * k 1 * k 2 * k 3)⁻¹ = t) (i : Fin 4) :
    ∀ m ∈ M i, x * m = m * x := by
  obtain ⟨g, hg⟩ : ∃ g : Fin 4 → Y, ∀ j, g j = x * k j * x⁻¹ * (k j)⁻¹ := ⟨_, fun _ => rfl⟩
  have hgM : ∀ j, g j ∈ M j := fun j => by
    rw [hg j]
    exact (M j).mul_mem (hfr.act_mem hxM j (hk j).1) ((M j).inv_mem (hk j).1)
  have hprod : x * (k 0 * k 1 * k 2 * k 3) * x⁻¹ * (k 0 * k 1 * k 2 * k 3)⁻¹ = g 0 * g 1 * g 2 * g 3 := by
    have e1 : x * (k 0 * k 1 * k 2 * k 3) * x⁻¹ =
        (g 0 * k 0) * (g 1 * k 1) * (g 2 * k 2) * (g 3 * k 3) := by
      rw [hg 0, hg 1, hg 2, hg 3]; group
    have e2 : (g 0 * k 0) * (g 1 * k 1) * (g 2 * k 2) * (g 3 * k 3) =
        (g 0 * g 1 * g 2 * g 3) * (k 0 * k 1 * k 2 * k 3) :=
      (prod4_mul2 (hfr.cross h (i := 1) (j := 0) (by decide) (hgM 1) (hk 0).1)
        (hfr.cross h (i := 2) (j := 0) (by decide) (hgM 2) (hk 0).1)
        (hfr.cross h (i := 2) (j := 1) (by decide) (hgM 2) (hk 1).1)
        (hfr.cross h (i := 3) (j := 0) (by decide) (hgM 3) (hk 0).1)
        (hfr.cross h (i := 3) (j := 1) (by decide) (hgM 3) (hk 1).1)
        (hfr.cross h (i := 3) (j := 2) (by decide) (hgM 3) (hk 2).1)).symm
    rw [e1, e2]; group
  rw [hprod] at hc
  have hgi := hfr.indep h hgM hc i
  have hq := h.q8 (hfr.mem i)
  have hfix : ZFix x t (k i) := by
    have e : x * k i * x⁻¹ = g i * k i := by rw [hg i]; group
    rcases hgi with e1 | e1
    · left; rw [e, e1, one_mul]
    · right; rw [e, e1]; exact hfr.t_comm h i (hk i).1
  exact hq.cent_of_fix hxo hxt (fun m hm => hfr.act_mem hxM i hm) (hk i).1 (hk i).2 hfix

end Frame4
section StepCMain

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}
  {M : Fin 4 → Subgroup Y} {a : Fin 4 → Y} {y : Y}

theorem WFFrame.pair_mem_W (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (i j : Fin 4) {ε : Y}
    (hε : ε = 1 ∨ ε = t) : a i * (ε * a j) ∈ W := by
  have hεW : ε ∈ W := by
    rcases hε with e | e
    · rw [e]; exact W.one_mem
    · rw [e]; exact h.t_mem
  exact W.mul_mem (hfr.haW i) (W.mul_mem hεW (hfr.haW j))

theorem WFFrame.pair_sq (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (i j : Fin 4) {ε : Y}
    (hε : ε = 1 ∨ ε = t) : (a i * (ε * a j)) * (a i * (ε * a j)) = 1 := by
  have ht := (h.q8 (hfr.mem 0)).z_sq
  have hεW : ε ∈ W := by
    rcases hε with e | e
    · rw [e]; exact W.one_mem
    · rw [e]; exact h.t_mem
  have hqW : ε * a j ∈ W := W.mul_mem hεW (hfr.haW j)
  have hcm : Commute (ε * a j) (a i) := h.abelian _ hqW _ (hfr.haW i)
  have hεsq : (ε * a j) * (ε * a j) = t := by
    have htc : t * a j = a j * t := hfr.t_comm h j (hfr.haM j)
    rcases hε with e | e
    · rw [e, one_mul]; exact hfr.sq h j
    · rw [e]
      calc t * a j * (t * a j) = t * (a j * t) * a j := by group
        _ = t * (t * a j) * a j := by rw [← htc]
        _ = (t * t) * (a j * a j) := by group
        _ = t := by rw [ht, hfr.sq h j, one_mul]
  calc (a i * (ε * a j)) * (a i * (ε * a j)) = (a i * a i) * ((ε * a j) * (ε * a j)) := by
        exact hcm.mul_mul_mul_comm (a i) (ε * a j)
    _ = 1 := by rw [hfr.sq h i, hεsq, ht]

theorem WFFrame.pair_mul (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W)
    (hfr : WFFrame (CoreAssembly.conjClass (tightCore R)) K t W M a y) (i j k : Fin 4) :
    (a i * ((1 : Y) * a j)) * (a j * ((1 : Y) * a k)) = a i * (t * a k) := by
  calc (a i * ((1 : Y) * a j)) * (a j * ((1 : Y) * a k)) = a i * (a j * a j) * a k := by group
    _ = a i * t * a k := by rw [hfr.sq h j]
    _ = a i * (t * a k) := by group

end StepCMain
section StepCFinal

theorem wfStepC_of_leaves (hB : WFB0 n) (hWM : WFWM n) (hD4 : WFD4 n) : WFStepC n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W h x hxo hxt hxM hNx hcent
  obtain ⟨N, hN, hxN⟩ := hNx
  obtain ⟨J₀, hJ₀, hc₀, hothers⟩ := hcent
  obtain ⟨M, a, y, hfr⟩ := h.exists_frame
  obtain ⟨c₀, rfl⟩ := hfr.surj J₀ hJ₀
  have hmoved : ∀ i, i ≠ c₀ → ¬ ∀ m ∈ M i, x * m = m * x := fun i hi =>
    hothers (M i) (hfr.mem i) (fun e => hi (hfr.inj e))
  obtain ⟨i₁, i₂, i₃, h12, h13, h23, h1c, h2c, h3c⟩ := fin4_three c₀
  obtain ⟨c, hc⟩ := exists_comm_coeff x M t
  have hcc₀ : c c₀ = 1 := by
    rcases hc c₀ with ⟨-, e⟩ | ⟨hn, -⟩
    · exact e
    · exact absurd hc₀ hn
  have hcne : ∀ i, i ≠ c₀ → c i = t := fun i hi => by
    rcases hc i with ⟨hcen, -⟩ | ⟨-, e⟩
    · exact absurd hcen (hmoved i hi)
    · exact e
  have hq8 := fun k => h.q8 (hfr.mem k)
  have ht := (hq8 0).z_sq
  have hcs : c 0 * c 1 * c 2 * c 3 = t := prod_coeff ht hcc₀ hcne
  obtain ⟨E, hE⟩ : ∃ E, E = x * (a 0 * a 1 * a 2 * a 3) * x⁻¹ := ⟨_, rfl⟩
  have hgE : (x * y) * t * (x * y)⁻¹ = E := by rw [hE]; exact hfr.gt_eq x
  have hEprod : E = (x * a 0 * x⁻¹) * (x * a 1 * x⁻¹) * (x * a 2 * x⁻¹) * (x * a 3 * x⁻¹) := by
    rw [hE]; group
  have hEt : E * t = t * E := by rw [hEprod]; exact (hfr.t_e h hxM).symm
  have hEs : E * (a 0 * a 1 * a 2 * a 3) = t * ((a 0 * a 1 * a 2 * a 3) * E) := by
    have := hfr.e_s h hxo hxt hxM hc
    rw [hcs] at this
    rw [hEprod]; exact this
  have hbE : ∀ i j, i ≠ c₀ → j ≠ c₀ → ∀ ε : Y, (ε = 1 ∨ ε = t) →
      (a i * (ε * a j)) * E = E * (a i * (ε * a j)) := by
    intro i j hi hj ε hε
    have := hfr.pair_e h hxo hxt hxM hc i j hε
    rw [hcne i hi, hcne j hj, ht, one_mul] at this
    rw [hEprod]; exact this.symm
  obtain ⟨J, hJ⟩ : ∃ J : Fin 4 → Subgroup Y, ∀ k, J k = conjSub (x * y) (M k) := ⟨_, fun _ => rfl⟩
  have hJq : ∀ k, Q8Facts (J k) E := fun k => by rw [hJ k, hE]; exact hfr.eTwin_q8 h x k
  have hJcom : ∀ i j, i ≠ j → Commutes (J i) (J j) := fun i j hij => by
    rw [hJ i, hJ j]; exact hfr.eTwin_comm h x hij
  have hMcom : ∀ i j, i ≠ j → Commutes (M i) (M j) := fun i j hij =>
    h.comm (hfr.mem i) (hfr.mem j) (fun e => hij (hfr.inj e))
  have hJinj : Function.Injective J := fun i j e =>
    hfr.inj (conjSub_injective (x * y) (by rw [← hJ i, ← hJ j]; exact e))
  have hJperm : ∀ b : Y, b * E = E * b → ∀ k, ∃ j, conjSub b (J k) = J j := fun b hb k => by
    obtain ⟨j, hj⟩ := hfr.eTwin_perm h x (c := b) (by rw [← hE]; exact hb) k
    exact ⟨j, by rw [hJ k, hJ j]; exact hj⟩
  have hNC := hN.1
  have hNn := hN.2.1
  have hPN := hN.2.2.1
  rw [hfr.sup_eq] at hPN
  have hoddN := h.odd_pow hN
  rw [hfr.sup_eq] at hoddN
  obtain ⟨Ne, hNe⟩ : ∃ Ne, Ne = conjSub (x * y) N := ⟨_, rfl⟩
  have hNeC : Ne ≤ Subgroup.centralizer ({E} : Set Y) := by
    rw [hNe, ← hgE]; exact conjSub_le_centralizer_conj (x * y) hNC
  have hNeNorm : (Ne.subgroupOf (Subgroup.centralizer ({E} : Set Y))).Normal := by
    rw [hNe, ← hgE]; exact conjSub_normal_conj (x * y) hNn
  have hPNe : J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 ≤ Ne := by
    have : ∀ k, J k ≤ Ne := fun k => by
      rw [hJ k, hNe]; exact conjSub_mono ((le_sup4 M k).trans hPN)
    exact sup_le (sup_le (sup_le (this 0) (this 1)) (this 2)) (this 3)
  have hPCe : ∀ c ∈ Subgroup.centralizer ({E} : Set Y), ∀ p ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3,
      c * p * c⁻¹ ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 := fun c hc p hp =>
    sup4_conj_mem hJcom c (hJperm c (Subgroup.mem_centralizer_singleton_iff.mp hc)) hp
  have hodde : ∀ ℓ ∈ Ne, ∃ m : ℕ, Odd m ∧ ℓ ^ m ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 := by
    intro ℓ hℓ
    rw [hNe, mem_conjSub_iff] at hℓ
    obtain ⟨m, hm, hmP⟩ := hoddN _ hℓ
    refine ⟨m, hm, ?_⟩
    have h1 := sup4_conj_mem hMcom (x * y) (B := J) (fun i => ⟨i, (hJ i).symm⟩) hmP
    have e1 : ((x * y)⁻¹ * ℓ * (x * y)) ^ m = (x * y)⁻¹ * ℓ ^ m * (x * y) := by
      simpa using conj_pow (a := (x * y)⁻¹) (b := ℓ) (i := m)
    rw [e1] at h1
    have e2 : (x * y) * ((x * y)⁻¹ * ℓ ^ m * (x * y)) * (x * y)⁻¹ = ℓ ^ m := by group
    rwa [e2] at h1
  have hset : ∀ b ∈ ({a i₁ * ((1 : Y) * a i₂), a i₂ * ((1 : Y) * a i₃),
      (a i₁ * ((1 : Y) * a i₂)) * (a i₂ * ((1 : Y) * a i₃))} : Set Y),
      ∃ i j ε, i ≠ j ∧ i ≠ c₀ ∧ j ≠ c₀ ∧ (ε = 1 ∨ ε = t) ∧ b = a i * (ε * a j) := by
    rintro b (rfl | rfl | rfl)
    · exact ⟨i₁, i₂, 1, h12, h1c, h2c, Or.inl rfl, rfl⟩
    · exact ⟨i₂, i₃, 1, h23, h2c, h3c, Or.inl rfl, rfl⟩
    · exact ⟨i₁, i₃, t, h13, h1c, h3c, Or.inr rfl, hfr.pair_mul h i₁ i₂ i₃⟩
  have hbC : ∀ i j, i ≠ c₀ → j ≠ c₀ → ∀ ε : Y, (ε = 1 ∨ ε = t) →
      a i * (ε * a j) ∈ Subgroup.centralizer ({E} : Set Y) := fun i j hi hj ε hε =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hbE i j hi hj ε hε)
  have hb₁ := hbC i₁ i₂ h1c h2c 1 (Or.inl rfl)
  have hb₂ := hbC i₂ i₃ h2c h3c 1 (Or.inl rfl)
  have hb11 := hfr.pair_sq h i₁ i₂ (ε := 1) (Or.inl rfl)
  have hb22 := hfr.pair_sq h i₂ i₃ (ε := 1) (Or.inl rfl)
  have hb12 : (a i₁ * ((1 : Y) * a i₂)) * (a i₂ * ((1 : Y) * a i₃)) =
      (a i₂ * ((1 : Y) * a i₃)) * (a i₁ * ((1 : Y) * a i₂)) :=
    h.abelian _ (hfr.pair_mem_W h i₁ i₂ (Or.inl rfl)) _ (hfr.pair_mem_W h i₂ i₃ (Or.inl rfl))
  have hperm : ∀ b ∈ ({a i₁ * ((1 : Y) * a i₂), a i₂ * ((1 : Y) * a i₃),
      (a i₁ * ((1 : Y) * a i₂)) * (a i₂ * ((1 : Y) * a i₃))} : Set Y),
      ∀ i, ∃ j, conjSub b (J i) = J j := by
    intro b hb i
    obtain ⟨p, q, ε, hpq, hp, hq, hε, rfl⟩ := hset b hb
    exact hJperm _ (hbE p q hp hq ε hε) i
  have hmove : ∀ b ∈ ({a i₁ * ((1 : Y) * a i₂), a i₂ * ((1 : Y) * a i₃),
      (a i₁ * ((1 : Y) * a i₂)) * (a i₂ * ((1 : Y) * a i₃))} : Set Y),
      ∀ i, conjSub b (J i) ≠ J i := by
    intro b hb i
    obtain ⟨p, q, ε, hpq, hp, hq, hε, rfl⟩ := hset b hb
    rw [hJ i]
    exact hfr.moves_pair hWM h hxo hxt hxM hpq (hmoved p hp) (hmoved q hq) hε i
  have hG : ∀ b ∈ ({a i₁ * ((1 : Y) * a i₂), a i₂ * ((1 : Y) * a i₃),
      (a i₁ * ((1 : Y) * a i₂)) * (a i₂ * ((1 : Y) * a i₃))} : Set Y),
      ∀ d ∈ Subgroup.centralizer ({E} : Set Y), d * b = b * d → d * t = t * d := by
    intro b hb d hd hdb
    obtain ⟨p, q, ε, hpq, hp, hq, hε, rfl⟩ := hset b hb
    exact hfr.G1 hB h hEt hEs hpq hε (Subgroup.mem_centralizer_singleton_iff.mp hd) hdb
  have key := c7_core (s := E) (t := t) hJq hJcom hJinj hNeC hNeNorm hPNe hPCe hodde hb₁ hb₂ hb11 hb22
    hb12 hperm hmove hG
  have hxe_mem : (x * y) * x * (x * y)⁻¹ ∈ Ne := by
    rw [hNe, mem_conjSub_iff]
    have e : (x * y)⁻¹ * ((x * y) * x * (x * y)⁻¹) * (x * y) = x := by group
    rw [e]; exact hxN
  obtain ⟨r, hr, c', hc'N, hc't, hxe⟩ := key _ hxe_mem
  obtain ⟨k, hk, hkprod⟩ := hD4 Y R S t K K' K₃ u₁ u₂ u₃ K₄ W h M a y hfr
  have htP : t ∈ J 0 ⊔ J 1 ⊔ J 2 ⊔ J 3 := by
    have hkJ : ∀ i, (x * y) * k i * (x * y)⁻¹ ∈ J i := fun i => by
      rw [hJ i]; exact conj_mem_conjSub (hk i).1
    have e : t = ((x * y) * k 0 * (x * y)⁻¹) * ((x * y) * k 1 * (x * y)⁻¹) *
        ((x * y) * k 2 * (x * y)⁻¹) * ((x * y) * k 3 * (x * y)⁻¹) := by
      calc t = x * t * x⁻¹ := by rw [hxt]; group
        _ = (x * y) * (y⁻¹ * t * y) * (x * y)⁻¹ := by group
        _ = (x * y) * (k 0 * k 1 * k 2 * k 3) * (x * y)⁻¹ := by rw [hkprod]
        _ = _ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (le_sup4 J 0 (hkJ 0))
      (le_sup4 J 1 (hkJ 1))) (le_sup4 J 2 (hkJ 2))) (le_sup4 J 3 (hkJ 3))
  have hcomm : ((x * y) * x * (x * y)⁻¹) * t * ((x * y) * x * (x * y)⁻¹)⁻¹ * t⁻¹ = 1 ∨
      ((x * y) * x * (x * y)⁻¹) * t * ((x * y) * x * (x * y)⁻¹)⁻¹ * t⁻¹ = E := by
    rw [hxe]
    have h1 : (r * c') * t * (r * c')⁻¹ * t⁻¹ = r * t * r⁻¹ * t⁻¹ := by
      calc (r * c') * t * (r * c')⁻¹ * t⁻¹ = r * (c' * t * c'⁻¹) * r⁻¹ * t⁻¹ := by group
        _ = r * t * r⁻¹ * t⁻¹ := by rw [show c' * t * c'⁻¹ = t from mul_inv_eq_iff_eq_mul.mpr hc't]
    rw [h1]
    exact P_comm_center hJq hJcom hr htP
  have hxt' : x⁻¹ * t * x = t := by
    calc x⁻¹ * t * x = x⁻¹ * (t * x) := mul_assoc _ _ _
      _ = x⁻¹ * (x * t) := by rw [hxt]
      _ = t := by group
  have hτ : (x * y)⁻¹ * t * (x * y) = y⁻¹ * t * y := by
    calc (x * y)⁻¹ * t * (x * y) = y⁻¹ * (x⁻¹ * t * x) * y := by group
      _ = y⁻¹ * t * y := by rw [hxt']
  have hc6 : x * (y⁻¹ * t * y) * x⁻¹ * (y⁻¹ * t * y)⁻¹ = 1 ∨
      x * (y⁻¹ * t * y) * x⁻¹ * (y⁻¹ * t * y)⁻¹ = t := by
    have e : x * (y⁻¹ * t * y) * x⁻¹ * (y⁻¹ * t * y)⁻¹ = (x * y)⁻¹ * (((x * y) * x * (x * y)⁻¹) * t *
        ((x * y) * x * (x * y)⁻¹)⁻¹ * t⁻¹) * (x * y) := by
      rw [← hτ]; group
    rw [e]
    rcases hcomm with h0 | h0
    · left; rw [h0]; group
    · right; rw [h0, ← hgE]; group
  have hall := hfr.c6_core h hxo hxt hxM hk (by rw [← hkprod]; exact hc6) i₁
  exact hmoved i₁ h1c hall

end StepCFinal

end StepCEnd

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
