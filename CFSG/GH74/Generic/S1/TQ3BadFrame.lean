module

public import CFSG.GH74.Generic.S1.TQ3BarGeom
public import CFSG.GH74.Generic.S1.SymNbhd
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
open CFSG.ClassicalInvolution.WeakCT CFSG.GH74.Filter.ClassicalOdd
open scoped MatrixGroups commutatorElement

section Model

variable {F : Type} [Field F]

theorem zblkMat_mul_self (c d : Fin 4) : zblkMat F c d * zblkMat F c d = 1 := by
  unfold zblkMat
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  by_cases h : i = c ∨ i = d <;> simp [h]

theorem det_zblkMat {c d : Fin 4} (hcd : c ≠ d) : (zblkMat F c d).det = 1 := by
  unfold zblkMat
  rw [det_diagonal]
  fin_cases c <;> fin_cases d <;> simp [Fin.prod_univ_four] at hcd ⊢

theorem isBlockAt_zblkMat (c d : Fin 4) : IsBlockAt c d (zblkMat F c d) := by
  intro i j hij
  unfold zblkMat
  by_cases hi : i = j
  · subst hi
    have : ¬ (i = c ∨ i = d) := fun h => hij ⟨h, h⟩
    simp [this]
  · simp [hi]

theorem exists_zblk (h2 : (2 : F) ≠ 0) {c d : Fin 4} (hcd : c ≠ d) :
    ∃ z : ↥(StatedSL 4 F), z ∈ blkLin (F := F) c d ∧
      ((z : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = zblkMat F c d ∧ z * z = 1 ∧ z ≠ 1 ∧
      ∀ g ∈ blkLin (F := F) c d, g * z = z * g := by
  let zS : ↥(StatedSL 4 F) :=
    ⟨⟨zblkMat F c d, zblkMat F c d, zblkMat_mul_self c d, zblkMat_mul_self c d⟩, by
      rw [statedSL_eq_detOne, mem_detOne]
      exact det_zblkMat hcd⟩
  refine ⟨zS, isBlockAt_zblkMat c d, rfl, ?_, ?_, ?_⟩
  · exact Subtype.ext (Units.ext (zblkMat_mul_self c d))
  · intro h
    have h' := congrArg
      (fun x : ↥(StatedSL 4 F) => ((x : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) c c) h
    simp only [zS, zblkMat, Matrix.diagonal_apply_eq] at h'
    apply h2
    have h'' : (-1 : F) = 1 := by simpa using h'
    linear_combination -h''
  · intro g hg
    refine Subtype.ext (Units.ext ?_)
    show (((g : GL (Fin 4) F) * (zS : GL (Fin 4) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      (((zS : GL (Fin 4) F) * (g : GL (Fin 4) F) : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    rw [Units.val_mul, Units.val_mul]
    exact IsBlockAt.comm_diagonal hg (fun i => if i = c ∨ i = d then -1 else 1) (by simp)

theorem comm_refl_of_mat_zblk {c d : Fin 4} {s : ↥(StatedSL 4 F)}
    (hs : ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = zblkMat F c d) (i : Fin 4) :
    (s : GL (Fin 4) F) * reflDiag F i = reflDiag F i * (s : GL (Fin 4) F) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hs]
  change zblkMat F c d * reflDiagMat F i = reflDiagMat F i * zblkMat F c d
  unfold zblkMat reflDiagMat
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext j
  exact mul_comm _ _

theorem blkLin_sup_data [Finite F] (hF3 : Nat.card F = 3) {a b d : Fin 4} (hab : a ≠ b)
    (had : a ≠ d) (hbd : b ≠ d) :
    IsQuasisimple ↥(blkLin (F := F) a b ⊔ blkLin (F := F) b d) ∧
      Nonempty (↥(blkLin (F := F) a b ⊔ blkLin (F := F) b d) ≃* SL(3, F)) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF3]; exact ⟨1, rfl⟩)
  obtain ⟨W, hW⟩ := blkLin_standardPair (F := F) a b d hab had hbd
  obtain ⟨hWe, -⟩ := lin_pair_fusion h2 hW
  obtain ⟨hWq, -⟩ := lin_pair_W_facts hW
  obtain ⟨θ, c, hrange, hker, -⟩ := hW
  have hinj : Function.Injective θ :=
    (MonoidHom.ker_eq_bot_iff θ).1 (by
      rw [eq_bot_iff]
      exact hker.trans (center_sl3_three hF3).le)
  subst hWe
  refine ⟨hWq, ⟨?_⟩⟩
  exact ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm

theorem blkLin_sup_le_reflCent {a b d c : Fin 4} (hca : c ≠ a) (hcb : c ≠ b) (hcd : c ≠ d) :
    blkLin (F := F) a b ⊔ blkLin (F := F) b d ≤ reflCent F c := by
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · rw [mem_reflCent]
    exact blkLin_comm_refl a b c hca hcb g hg
  · rw [mem_reflCent]
    exact blkLin_comm_refl b d c hcb hcd g hg

end Model

section Involutions

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_sq_of_mem_pPrimeCore' {X : Type*} [Group X] [Finite X] {h : X} (h2 : h * h = 1)
    (hO : h ∈ pPrimeCore 2 X) : h = 1 := by
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := pPrimeCore_coprime_card
  have hdvd : orderOf (⟨h, hO⟩ : pPrimeCore 2 X) ∣ Nat.card (pPrimeCore 2 X) :=
    orderOf_dvd_natCard _
  have h2' : orderOf (⟨h, hO⟩ : pPrimeCore 2 X) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [sq] using h2
  have h1 : orderOf (⟨h, hO⟩ : pPrimeCore 2 X) = 1 := by
    have : Nat.Coprime (orderOf (⟨h, hO⟩ : pPrimeCore 2 X)) (Nat.card (pPrimeCore 2 X)) := by
      refine Nat.Coprime.coprime_dvd_left h2' hcop
    exact Nat.Coprime.eq_one_of_dvd this hdvd
  have := orderOf_eq_one_iff.mp h1
  exact congrArg Subtype.val this

theorem eq_of_barOf_eq {y : G} {u w : G} (hu : u ∈ centralizer ({y} : Set G))
    (hw : w ∈ centralizer ({y} : Set G)) (hu2 : u * u = 1) (hw2 : w * w = 1) (huw : u * w = w * u)
    (h : barOf hu = barOf hw) : u = w := by
  set U : ↥(centralizer ({y} : Set G)) := ⟨u, hu⟩ with hU
  set W : ↥(centralizer ({y} : Set G)) := ⟨w, hw⟩ with hW
  have h1 : U⁻¹ * W ∈ pPrimeCore 2 ↥(centralizer ({y} : Set G)) := (QuotientGroup.eq).1 h
  have hUW : U * W = W * U := Subtype.ext huw
  have hUU : U * U = 1 := Subtype.ext hu2
  have hWW : W * W = 1 := Subtype.ext hw2
  have hsq : (U⁻¹ * W) * (U⁻¹ * W) = 1 := by
    have hUi : U⁻¹ = U := inv_eq_of_mul_eq_one_right hUU
    rw [hUi]
    calc (U * W) * (U * W) = (W * U) * (U * W) := by rw [hUW]
      _ = W * (U * U) * W := by group
      _ = 1 := by rw [hUU, mul_one, hWW]
  have h2 := eq_one_of_sq_of_mem_pPrimeCore' hsq h1
  have hUW' : U = W := by
    have := congrArg (fun z => U * z) h2
    simpa using this.symm
  exact congrArg Subtype.val hUW'

theorem eq_or_eq_mul_of_conj_eq' {y : G} (hy2 : orderOf y = 2) {K : Subgroup (CentralizerBar y)}
    (hcent : centralizer (K : Set (CentralizerBar y)) = Subgroup.zpowers (xbar y)) {u v : G}
    (hu : u ∈ centralizer ({y} : Set G)) (hv : v ∈ centralizer ({y} : Set G))
    (hu2 : u * u = 1) (hv2 : v * v = 1) (huv : u * v = v * u)
    (h : ∀ k ∈ K, barOf hu * k * (barOf hu)⁻¹ = barOf hv * k * (barOf hv)⁻¹) :
    u = v ∨ u = v * y := by
  have hyy : y * y = 1 := by rw [← sq, ← hy2]; exact pow_orderOf_eq_one y
  have hz : (barOf hv)⁻¹ * barOf hu ∈ centralizer (K : Set (CentralizerBar y)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have := h k hk
    calc k * ((barOf hv)⁻¹ * barOf hu)
        = (barOf hv)⁻¹ * (barOf hv * k * (barOf hv)⁻¹) * barOf hu := by group
      _ = (barOf hv)⁻¹ * (barOf hu * k * (barOf hu)⁻¹) * barOf hu := by rw [this]
      _ = (barOf hv)⁻¹ * barOf hu * k := by group
  rw [hcent] at hz
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hxo : orderOf (xbar y) = 2 := orderOf_xbar hy2
  have hxx : xbar y ^ 2 = 1 := by
    have := pow_orderOf_eq_one (xbar y)
    rwa [hxo] at this
  have hcases : xbar y ^ n = 1 ∨ xbar y ^ n = xbar y := by
    rcases Int.emod_two_eq_zero_or_one n with h0 | h1
    · left
      rw [← Int.emod_add_mul_ediv n 2, h0, _root_.zpow_add, _root_.zpow_mul]
      simp [hxx]
    · right
      rw [← Int.emod_add_mul_ediv n 2, h1, _root_.zpow_add, _root_.zpow_mul]
      simp [hxx]
  have hyv : v * y = y * v := (mem_centralizer_singleton_iff.1 hv)
  have hyu : u * y = y * u := (mem_centralizer_singleton_iff.1 hu)
  rcases hcases with h1 | h1
  · left
    rw [h1] at hn
    have : barOf hu = barOf hv := by
      have := congrArg (fun z => barOf hv * z) hn
      simpa using this.symm
    exact eq_of_barOf_eq hu hv hu2 hv2 huv this
  · right
    rw [h1] at hn
    have hvy : v * y ∈ centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc v * y * y = (y * v) * y := by rw [hyv]
        _ = y * (v * y) := by group
    have hvy2 : (v * y) * (v * y) = 1 := by
      calc (v * y) * (v * y) = v * (y * v) * y := by group
        _ = v * (v * y) * y := by rw [← hyv]
        _ = (v * v) * (y * y) := by group
        _ = 1 := by rw [hv2, hyy, one_mul]
    have huvy : u * (v * y) = (v * y) * u := by
      calc u * (v * y) = (u * v) * y := by group
        _ = (v * u) * y := by rw [huv]
        _ = v * (u * y) := by group
        _ = v * (y * u) := by rw [hyu]
        _ = (v * y) * u := by group
    have : barOf hu = barOf hvy := by
      have e1 : barOf hvy = barOf hv * xbar y := rfl
      rw [e1]
      have := congrArg (fun z => barOf hv * z) hn
      simpa using this.symm
    exact eq_of_barOf_eq hu hvy hu2 hvy2 huvy this

end Involutions

section Frame

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

structure Q3FrameB (G : Type) [Group G] [Finite G] (F : Type) [Field F] where
  X : Fin 5 → G
  D : ∀ e, LayerData (X e) (StatedSL 4 F)
  X_sq : ∀ e, X e * X e = 1
  X_ne : ∀ e, X e ≠ 1
  X_inj : ∀ i j, i ≠ j → X i ≠ X j
  X_comm : ∀ i j, X i * X j = X j * X i
  X_prod : X 0 * X 1 * X 2 * X 3 * X 4 = 1
  act : ∀ e j, ActsAsReflOn (D e).iso
    (barOf (mem_centralizer_singleton_iff.2 (X_comm _ _) :
      X (e.succAbove j) ∈ centralizer ({X e} : Set G))) (reflDiag F j)
  cent : ∀ e, centralizer ((D e).K : Set (CentralizerBar (X e))) = Subgroup.zpowers (xbar (X e))
  xK : ∀ e, xbar (X e) ∈ (D e).K

omit [Finite F] in
theorem exists_q3FrameB (hExact : S1LiftExactProp) {x : G} {K : Subgroup (CentralizerBar x)}
    (hset : S1Setup G x K) {u : Fin 4 → G} {hu : ∀ i, u i ∈ centralizer ({x} : Set G)}
    (hf : S1Frame x K u hu) (hlin : S1SymFrameLin x u F) :
    ∃ Fr : Q3FrameB G F, Fr.X = symX x u := by
  obtain ⟨hconj, hsq, hXc, hprod, hinj⟩ := symX_facts hset.shape.2 hset.inv hf
  have hw : ∀ e j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G) := fun e j =>
    mem_centralizer_singleton_iff.2 (hXc _ _)
  have hloc : ∀ e : Fin 5, ∃ (K' : Subgroup (CentralizerBar (symX x u e)))
      (hw' : ∀ j, symX x u (e.succAbove j) ∈ centralizer ({symX x u e} : Set G)),
        S1Setup G (symX x u e) K' ∧ S1Front G (symX x u e) K' ∧
        ∃ e' : ↥K' ≃* ↥(StatedSL 4 F), ∀ j, ActsAsReflOn e' (barOf (hw' j)) (reflDiag F j) := by
    intro e
    obtain ⟨K', hw', hset', hfront', -, e', he'⟩ := hlin e
    exact ⟨K', hw', hset', hfront', e', he'⟩
  choose D hDK hDact using sym_layerData hExact x u hw hloc
  refine ⟨⟨symX x u, D, hsq, ?_, hinj, hXc, hprod, fun e j => hDact e j, ?_, ?_⟩, rfl⟩
  · intro e h
    have h1 := hconj e
    rw [h] at h1
    have : x = 1 := isConj_one_right.1 h1.symm
    have := hset.inv
    rw [‹x = 1›, orderOf_one] at this
    exact absurd this (by norm_num)
  · intro e
    obtain ⟨K', hw', hset', hfront', -⟩ := hlin e
    rw [(hDK e).trans hfront'.layer_eq]
    exact hfront'.cent_eq
  · intro e
    obtain ⟨K', hw', hset', hfront', -⟩ := hlin e
    rw [(hDK e).trans hfront'.layer_eq]
    exact hset'.shape.2

namespace Q3FrameB

variable (Fr : Q3FrameB G F)

omit [Finite F] in
theorem X_mem_cent (i j : Fin 5) : Fr.X i ∈ centralizer ({Fr.X j} : Set G) :=
  mem_centralizer_singleton_iff.2 (Fr.X_comm _ _)

omit [Finite F] in
theorem orderOf_X (e : Fin 5) : orderOf (Fr.X e) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [sq]; exact Fr.X_sq e) (Fr.X_ne e)

omit [Finite F] in
theorem act' (e : Fin 5) (j : Fin 4) {k : Fin 5} (hk : e.succAbove j = k) :
    ActsAsReflOn (Fr.D e).iso (barOf (Fr.X_mem_cent k e)) (reflDiag F j) := by
  subst hk
  exact Fr.act e j

omit [Finite F] in
theorem ι_comm_X (e : Fin 5) {j : Fin 4} {k : Fin 5} (hk : e.succAbove j = k)
    {s : ↥(StatedSL 4 F)}
    (hs : (s : GL (Fin 4) F) * reflDiag F j = reflDiag F j * (s : GL (Fin 4) F)) :
    (Fr.D e).ι s * Fr.X k = Fr.X k * (Fr.D e).ι s :=
  (Fr.D e).ι_comm_of (Fr.X_mem_cent k e) (Fr.act' e j hk) hs

omit [Finite F] in
theorem comm_of_ι_X (e : Fin 5) {j : Fin 4} {k : Fin 5} (hk : e.succAbove j = k)
    {s : ↥(StatedSL 4 F)} (hs : (Fr.D e).ι s * Fr.X k = Fr.X k * (Fr.D e).ι s) :
    (s : GL (Fin 4) F) * reflDiag F j = reflDiag F j * (s : GL (Fin 4) F) :=
  (Fr.D e).comm_of_ι_comm (Fr.X_mem_cent k e) (Fr.act' e j hk) hs

omit [Finite F] in
theorem exists_s0 (e : Fin 5) :
    ∃ s₀ : ↥(StatedSL 4 F), s₀ ∈ Subgroup.center ↥(StatedSL 4 F) ∧ s₀ * s₀ = 1 ∧ s₀ ≠ 1 ∧
      (Fr.D e).ι s₀ = Fr.X e := by
  set De := Fr.D e with hDe
  let k : ↥De.K := ⟨xbar (Fr.X e), Fr.xK e⟩
  have hxo : orderOf (xbar (Fr.X e)) = 2 := orderOf_xbar (Fr.orderOf_X e)
  have hxx : xbar (Fr.X e) * xbar (Fr.X e) = 1 := by
    have := pow_orderOf_eq_one (xbar (Fr.X e))
    rw [hxo] at this
    rw [← sq]
    exact this
  have hkc : ∀ g : ↥De.K, g * k = k * g := fun g => Subtype.ext (xbar_comm (Fr.X e) g.1)
  refine ⟨De.iso k, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg De.iso (hkc (De.iso.symm g))
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  · rw [← map_mul]
    have : k * k = 1 := Subtype.ext hxx
    rw [this, map_one]
  · intro h
    have : k = 1 := De.iso.injective (h.trans (map_one _).symm)
    exact xbar_ne_one (Fr.orderOf_X e) (congrArg Subtype.val this)
  · set s₀ := De.iso k with hs₀
    have hz : De.ι s₀ ∈ centralizer ({Fr.X e} : Set G) := De.ι_mem_cent s₀
    have hproj := De.proj_ιC s₀
    rw [hs₀, MulEquiv.symm_apply_apply] at hproj
    have hs₀2 : s₀ * s₀ = 1 := by
      rw [hs₀, ← map_mul]
      have : k * k = 1 := Subtype.ext hxx
      rw [this, map_one]
    have hz2 : De.ι s₀ * De.ι s₀ = 1 := by rw [← map_mul, hs₀2, map_one]
    have hX2 : Fr.X e * Fr.X e = 1 := Fr.X_sq e
    have hcomm : De.ι s₀ * Fr.X e = Fr.X e * De.ι s₀ := De.ι_comm_self s₀
    exact eq_of_barOf_eq hz (Fr.X_mem_cent e e) hz2 hX2 hcomm hproj

theorem blk_le_of_layers (hF3 : Nat.card F = 3) {e f : Fin 5} {a b c d a' b' c' d' : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hab' : a' ≠ b') (hac' : a' ≠ c') (had' : a' ≠ d') (hbc' : b' ≠ c') (hbd' : b' ≠ d')
    (hcd' : c' ≠ d')
    (hC : e.succAbove c = f) (hC' : f.succAbove c' = e) (hD : e.succAbove d = f.succAbove d') :
    (blkLin (F := F) a' b').map (Fr.D f).ι ≤ (blkLin (F := F) a b).map (Fr.D e).ι := by
  classical
  set De := Fr.D e with hDe
  set Df := Fr.D f with hDf
  obtain ⟨hSgq, -⟩ := blkLin_sup_data (F := F) hF3 hab' had' hbd'
  set Sg : Subgroup ↥(StatedSL 4 F) := blkLin (F := F) a' b' ⊔ blkLin (F := F) b' d' with hSg
  have hSgperf : ⁅Sg, Sg⁆ = Sg := Subgroup.isPerfect_iff.mp hSgq.1
  have hSgle : Sg ≤ reflCent F c' :=
    blkLin_sup_le_reflCent (fun h => hac' h.symm) (fun h => hbc' h.symm) (fun h => hcd' h)
  set P : Subgroup G := Sg.map Df.ι with hP
  have hPperf : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hSgperf]
  have hPe : P ≤ centralizer ({Fr.X e} : Set G) := by
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_singleton_iff]
    exact Fr.ι_comm_X f hC' (mem_reflCent.1 (hSgle hs))
  have hPrange : P ≤ De.ι.range := De.le_range_ι hPperf hPe
  set Bf : Subgroup G := (blkLin (F := F) a' b').map Df.ι with hBf
  have hBfP : Bf ≤ P := Subgroup.map_mono le_sup_left
  have hBfrange : Bf ≤ De.ι.range := hBfP.trans hPrange
  set Bt : Subgroup ↥(StatedSL 4 F) := Bf.comap De.ι with hBt
  have hmap : Bt.map De.ι = Bf := by
    rw [hBt, Subgroup.map_comap_eq]
    exact inf_eq_right.2 hBfrange
  have hodd3 : Odd (Nat.card F) := by rw [hF3]; exact ⟨1, rfl⟩
  have hBfodd : OddGenerated Bf :=
    oddGenerated_map Df.ι (blkLin_oddGenerated hodd3 a' b' hab')
  have hBtodd : OddGenerated Bt := oddGenerated_comap De.ι_injective hBfodd hBfrange
  have hBtcomm : ∀ t ∈ Bt, (t : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (t : GL (Fin 4) F) ∧
      (t : GL (Fin 4) F) * reflDiag F d = reflDiag F d * (t : GL (Fin 4) F) := by
    intro t ht
    have ht' : De.ι t ∈ Bf := ht
    obtain ⟨s', hs', hst⟩ := ht'
    constructor
    · refine Fr.comm_of_ι_X e hC ?_
      rw [← hst]
      exact Df.ι_comm_self s'
    · refine Fr.comm_of_ι_X e (rfl : e.succAbove d = e.succAbove d) ?_
      rw [← hst]
      exact Fr.ι_comm_X f hD.symm (blkLin_comm_refl a' b' d' (fun h => had' h.symm)
        (fun h => hbd' h.symm) s' hs')
  have hle : Bt ≤ blkLin a b :=
    (linBlockOps3 hF3).odd_le a b c d hab hac had hbc hbd hcd Bt hBtcomm hBtodd
  rw [← hmap]
  exact Subgroup.map_mono hle

theorem blk_eq_of_layers (hF3 : Nat.card F = 3) {e f : Fin 5} {a b c d a' b' c' d' : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hab' : a' ≠ b') (hac' : a' ≠ c') (had' : a' ≠ d') (hbc' : b' ≠ c') (hbd' : b' ≠ d')
    (hcd' : c' ≠ d')
    (hC : e.succAbove c = f) (hC' : f.succAbove c' = e) (hD : e.succAbove d = f.succAbove d') :
    (blkLin (F := F) a b).map (Fr.D e).ι = (blkLin (F := F) a' b').map (Fr.D f).ι :=
  le_antisymm
    (Fr.blk_le_of_layers hF3 hab' hac' had' hbc' hbd' hcd' hab hac had hbc hbd hcd hC' hC hD.symm)
    (Fr.blk_le_of_layers hF3 hab hac had hbc hbd hcd hab' hac' had' hbc' hbd' hcd' hC hC' hD)

end Q3FrameB

end Frame

end CFSG.GH74.Generic.S1
