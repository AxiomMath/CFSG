module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.KappaCoord

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.KappaD

open Subgroup CFSG.Sporadic.Schreier.Tits

section Matrices

variable {G : Type} [Group G] {d : Data G}

@[expose] def GActs (d : Data G) (n : G) (M : Mat6) : Prop :=
  ∀ i, n * pb d i * n⁻¹ = mono d (M i)

theorem gActs_one : GActs d 1 1 := fun i => by
  rw [show (1 : Mat6) i = Pi.single i 1 from funext fun j => Matrix.one_eq_pi_single, mono_single]
  simp

theorem mono_snoc (v : Fin 5 → ZMod 2) (c : ZMod 2) :
    mono d (Fin.snoc v c : Fin 6 → ZMod 2) =
      (List.ofFn fun j : Fin 5 => pb d j.castSucc ^ (v j).val).prod * d.t ^ c.val := by
  rw [mono, List.ofFn_succ', List.concat_eq_append, List.prod_append]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.prod_cons, List.prod_nil, mul_one]
  rfl

theorem sMat_castSucc (T : Mat5) (i : Fin 5) :
    sMat T i.castSucc = (Fin.snoc (T i) 0 : Fin 6 → ZMod 2) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Fin.snoc_last]
    simp [sMat, show i.val ≠ 5 by omega]
  · simp [sMat]

theorem sMat_last (T : Mat5) : sMat T (Fin.last 5) = Pi.single 5 1 := by
  ext j
  fin_cases j <;> simp [sMat]

end Matrices

section Order

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem gActs_mul (hd : d.Hyp) {n n' : G} {M M' : Mat6} (h : GActs d n M) (h' : GActs d n' M') :
    GActs d (n * n') (M' * M) := fun i => by
  have e : n * n' * pb d i * (n * n')⁻¹ = n * (n' * pb d i * n'⁻¹) * n⁻¹ := by group
  rw [e, h' i, conj_mono hd h]
  rfl

theorem pbasis_mem (j : Fin 5) : pbasis j ∈ titsD := by
  fin_cases j
  · exact Model.parrottF_le_titsD (Model.parrottV_mem_parrottF (i := 12) (by simp))
  · exact Model.parrottF_le_titsD (Model.parrottV_mem_parrottF (i := 11) (by simp))
  · exact Model.parrottF_le_titsD (Model.parrottV_mem_parrottF (i := 10) (by simp))
  · exact Model.parrottF_le_titsD (Model.parrottV_mem_parrottF (i := 9) (by simp))
  · exact Model.parrottF_le_titsD (Model.parrottV_mem_parrottF (i := 7) (by simp))

theorem lift_pbasis (d : Data G) (j : Fin 5) : d.lift (pbasis j) = pb d j.castSucc := by
  fin_cases j
  · exact Data.s56_pv12 d
  all_goals rfl

theorem lift_ofFn_prod (d : Data G) {n : ℕ} (f : Fin n → Equiv.Perm (Fin 1755))
    (hf : ∀ j, f j ∈ titsD) :
    d.lift (List.ofFn f).prod = (List.ofFn fun j => d.lift (f j)).prod := by
  induction n with
  | zero => simp [d.lift_one]
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, d.lift_mul (hf 0)
      (titsD.list_prod_mem fun y hy => by obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy; exact hf _),
      ih (fun i => f i.succ) fun i => hf _]

theorem conj_pb_of_acts (hd : d.Hyp) {x : G} (hx : x ∈ centralizer ({d.t} : Set G)) {M : Mat5}
    (hρ : (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ∈ titsD)
    (hM : Acts (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) M) (i : Fin 5) :
    x * pb d i.castSucc * x⁻¹ = mono d (Fin.snoc (M i) 0 : Fin 6 → ZMod 2) := by
  have hpow : ∀ (j : Fin 5) (k : ℕ), pbasis j ^ k ∈ titsD := fun j k => pow_mem (pbasis_mem j) k
  have hprod : (List.ofFn fun j : Fin 5 => pbasis j ^ (M i j).val).prod ∈ titsD :=
    titsD.list_prod_mem fun y hy => by obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hy; exact hpow j _
  have h1 : x * d.lift (pbasis i) * x⁻¹ =
      d.lift (List.ofFn fun j : Fin 5 => pbasis j ^ (M i j).val).prod :=
    hd.conj_lift_eq hx (pbasis_mem i) hprod (by rw [← hM i]; group)
  have h2 : ∀ j : Fin 5, d.lift (pbasis j ^ (M i j).val) = pb d j.castSucc ^ (M i j).val :=
    fun j => by rw [d.lift_pow (pbasis_mem j), lift_pbasis]
  rw [← lift_pbasis, h1, lift_ofFn_prod d _ fun j => hpow j _, mono_snoc]
  simp [h2]

theorem gActs_lift (hd : d.Hyp) {π : Equiv.Perm (Fin 1755)} (hπ : π ∈ titsD) {T : Mat5}
    (hT : Acts π T) : GActs d (d.lift π) (sMat T) := by
  have hx : d.lift π ∈ centralizer ({d.t} : Set G) := hd.L_le (d.lift_mem π)
  have hρ : (d.ρ ⟨d.lift π, hx⟩ : Equiv.Perm (Fin 1755)) = π := hd.ρ_lift hπ
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [sMat_last, mono_single]
    show d.lift π * d.t * (d.lift π)⁻¹ = d.t
    rw [hd.L_comm_t (d.lift_mem π)]
    group
  · rw [sMat_castSucc]
    exact conj_pb_of_acts hd hx (by rw [hρ]; exact hπ) (by rw [hρ]; exact hT) i

theorem gActs_x (hd : d.Hyp) {x : G} (hxV : x ∈ d.s56V) {e₁ e₂ e₃ d₁ : ZMod 2}
    (hε : d.s56Eps x = d.z ^ e₁.val * d.pv 11 ^ e₂.val * d.pv 10 ^ e₃.val * d.pv 9)
    (hδ : x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ = d.z ^ d₁.val * d.pv 11 ^ (e₃ + 1).val * d.pv 10) :
    GActs d x (xMat e₁ e₂ e₃ 1 d₁ (e₃ + 1) 1) := by
  have hxE : ∀ e ∈ d.E, x * e * x⁻¹ = e := fun e he => by
    rw [Data.s56_V_comm_E hxV he]
    group
  have hεL : d.s56Eps x ∈ d.L := Data.s56_E_le_L d (hd.s56_eps_mem_E (Data.s56_V_le_M d hxV))
  intro i
  fin_cases i
  · simpa [xMat, mono_eq, pb] using hxE _ hd.s56_z_mem_E
  · simpa [xMat, mono_eq, pb] using hxE _ (Data.s56_pv11_mem_E d)
  · simpa [xMat, mono_eq, pb] using hxE _ hd.s56_pv10_mem_E
  · simpa [xMat, mono_eq, pb] using hxE _ (node09K_pv9_mem_E d)
  · simp only [xMat, mono_eq, pb]
    simp
    calc x * d.pv 7 * x⁻¹ = (x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹) * d.pv 7 := by group
      _ = _ := by rw [hδ]
  · simp only [xMat, mono_eq, pb]
    simp
    rw [hd.s56_conj_t, ← hd.L_comm_t hεL, hε]

theorem gActs_prod (hd : d.Hyp) {g : Letter → G} {Mℓ : Letter → Mat6}
    (hg : ∀ ℓ, GActs d (g ℓ) (Mℓ ℓ)) (hN : ∀ ℓ, g ℓ ∈ d.N) :
    ∀ ws : List Letter, GActs d (ws.map g).prod (prodRev (ws.map Mℓ)) ∧ (ws.map g).prod ∈ d.N
  | [] => ⟨gActs_one, one_mem _⟩
  | ℓ :: ws => by
    have ih := gActs_prod hd hg hN ws
    exact ⟨gActs_mul hd (hg ℓ) ih.1, mul_mem (hN ℓ) ih.2⟩

theorem noBadX (h49 : d.Thm49Statement) (hd : d.Hyp) (hD : d.ρ.range = titsD.subgroupOf titsA)
    (τ : Fin 4 → Equiv.Perm (Fin 1755)) (hτ : ∀ j, τ j ∈ titsN)
    (T : Fin 4 → Mat5) (hT : ∀ j, Acts (τ j) (T j))
    (SL : Set Mat5) (hSL : ∀ π ∈ titsN, ∃ M ∈ SL, Acts π M)
    (words : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → List Letter)
    (hwords : ∀ e₁ e₂ e₃ d₁, WordOK SL T (words e₁ e₂ e₃ d₁) e₁ e₂ e₃ 1 d₁ (e₃ + 1) 1)
    {x : G} (hx : x ∈ d.s56V ⊓ d.N) {e₁ e₂ e₃ d₁ : ZMod 2}
    (hε : d.s56Eps x = d.z ^ e₁.val * d.pv 11 ^ e₂.val * d.pv 10 ^ e₃.val * d.pv 9)
    (hδ : x * d.pv 7 * x⁻¹ * (d.pv 7)⁻¹ = d.z ^ d₁.val * d.pv 11 ^ (e₃ + 1).val * d.pv 10) :
    False := by
  obtain ⟨hxV, hxN⟩ := mem_inf.1 hx
  let g : Letter → G := fun | none => x | some j => d.lift (τ j)
  have hg : ∀ ℓ, GActs d (g ℓ) (letterMat e₁ e₂ e₃ 1 d₁ (e₃ + 1) 1 T ℓ) := by
    rintro (_ | j)
    · exact gActs_x hd hxV hε hδ
    · exact gActs_lift hd (titsN_le_titsD (hτ j)) (hT j)
  have hN : ∀ ℓ, g ℓ ∈ d.N := by
    rintro (_ | j)
    · exact hxN
    · exact (mem_inf.1 (hd.s56_lift_mem_CNt (hτ j))).1
  obtain ⟨hw, hwN⟩ := gActs_prod hd hg hN (words e₁ e₂ e₃ d₁)
  obtain ⟨hrow, hblk⟩ := hwords e₁ e₂ e₃ d₁
  set w := ((words e₁ e₂ e₃ d₁).map g).prod
  set M := prodRev ((words e₁ e₂ e₃ d₁).map (letterMat e₁ e₂ e₃ 1 d₁ (e₃ + 1) 1 T))
  have hwt : w * d.t = d.t * w := by
    have h5 := hw 5
    have hM5 : M 5 = Pi.single 5 1 := funext fun j => by
      rw [hrow j]
      simp [Pi.single_apply]
    rw [hM5, mono_single] at h5
    change w * d.t * w⁻¹ = d.t at h5
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5
  have hwC : w ∈ centralizer ({d.t} : Set G) := mem_centralizer_singleton_iff.2 hwt
  have hρD : (d.ρ ⟨w, hwC⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
    have hmem : d.ρ ⟨w, hwC⟩ ∈ d.ρ.range := ⟨_, rfl⟩
    rw [hD] at hmem
    exact mem_subgroupOf.1 hmem
  have hρN : (d.ρ ⟨w, hwC⟩ : Equiv.Perm (Fin 1755)) ∈ titsN := by
    rw [← Model.titsD_inf_normalizer_parrottF]
    exact mem_inf.2 ⟨hρD, (hd.mem_normalizer_tSup_iff Model.parrottF_le_titsD hwC).1 hwN⟩
  obtain ⟨M', hM'SL, hM'⟩ := hSL _ hρN
  apply hblk
  convert hM'SL using 1
  funext i j
  have h1 := (hw i.castSucc).symm.trans (conj_pb_of_acts hd hwC hρD hM' i)
  have h2 := congrFun (B_coord_unique hd h1) j.castSucc
  simpa [blk] using h2

end Order

end CFSG.LocalAnalysis.EvenBN.Tits.N.KappaD
