module

public import CFSG.GH74.Generic.S1.TQ3BadFrame
public import CFSG.GH74.Generic.S1.TQ3BarMain
public import CFSG.GH74.Generic.S1.TDualLin

public section

namespace CFSG.GH74.Generic.S1

open Matrix CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank Subgroup CFSG.GH74.Generic
open CFSG.ClassicalInvolution.WeakCT CFSG.GH74.Filter.ClassicalOdd
open scoped MatrixGroups commutatorElement

section Frame

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]

namespace Q3FrameB

variable (Fr : Q3FrameB G F)

omit [Finite F] in
theorem X_mul_mem_cent (i j k : Fin 5) : Fr.X i * Fr.X j ∈ centralizer ({Fr.X k} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((Commute.mul_left (Fr.X_comm i k) (Fr.X_comm j k) : Commute (Fr.X i * Fr.X j) (Fr.X k))).eq

@[expose] noncomputable def Ablk : Subgroup G :=
  (blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1).map (Fr.D 2).ι

@[expose] noncomputable def Jblk : Subgroup G := (blkLin (F := F) 2 3).map (Fr.D 4).ι

theorem A_data (hF3 : Nat.card F = 3) :
    IsQuasisimple ↥Fr.Ablk ∧ Nonempty (↥Fr.Ablk ≃* SL(3, F)) := by
  obtain ⟨hq, ⟨e⟩⟩ := blkLin_sup_data (F := F) hF3 (a := 3) (b := 0) (d := 1) (by decide)
    (by decide) (by decide)
  have eA : ↥(blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1) ≃* ↥Fr.Ablk :=
    Subgroup.equivMapOfInjective _ (Fr.D 2).ι (Fr.D 2).ι_injective
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eA hq, ⟨eA.symm.trans e⟩⟩

theorem A_center (hF3 : Nat.card F = 3) :
    ∀ z ∈ Fr.Ablk, (∀ w ∈ Fr.Ablk, z * w = w * z) → z = 1 := by
  intro z hz hzc
  obtain ⟨-, ⟨e⟩⟩ := Fr.A_data hF3
  have := Q3Frame.q3_eq_one_of_central_of_equiv e (center_sl3_three hF3) (z := ⟨z, hz⟩)
    (fun w => Subtype.ext (hzc w w.2))
  exact congrArg Subtype.val this

theorem A_card (hF3 : Nat.card F = 3) : Nat.card ↥Fr.Ablk = 5616 := by
  obtain ⟨-, ⟨e⟩⟩ := Fr.A_data hF3
  rw [Nat.card_congr e.toEquiv, card_sl3_three hF3]

omit [Finite F] in
theorem A_comm_X {a : G} (ha : a ∈ Fr.Ablk) :
    a * Fr.X 2 = Fr.X 2 * a ∧ a * Fr.X 3 = Fr.X 3 * a := by
  obtain ⟨s, hs, rfl⟩ := ha
  have hle : blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1 ≤ reflCent F 2 :=
    blkLin_sup_le_reflCent (a := 3) (b := 0) (d := 1) (c := 2) (by decide) (by decide) (by decide)
  exact ⟨(Fr.D 2).ι_comm_self s, Fr.ι_comm_X 2 (j := 2) (k := 3) (by decide)
    (mem_reflCent.1 (hle hs))⟩

omit [Finite F] in
theorem act_X23 (hu : Fr.X 2 * Fr.X 3 ∈ centralizer ({Fr.X 2} : Set G)) :
    ActsAsReflOn (Fr.D 2).iso (barOf hu) (reflDiag F 2) := by
  have h3 : Fr.X 3 ∈ centralizer ({Fr.X 2} : Set G) := Fr.X_mem_cent 3 2
  have hact : ActsAsReflOn (Fr.D 2).iso (barOf h3) (reflDiag F 2) := Fr.act 2 2
  intro k k' hkk'
  apply hact k k'
  have hx : barOf hu = xbar (Fr.X 2) * barOf h3 := rfl
  rw [hx] at hkk'
  have hc : ∀ g : CentralizerBar (Fr.X 2), xbar (Fr.X 2) * g * (xbar (Fr.X 2))⁻¹ = g := fun g => by
    rw [← xbar_comm (Fr.X 2) g, mul_inv_cancel_right]
  rw [← hkk']
  calc barOf h3 * (k : CentralizerBar (Fr.X 2)) * (barOf h3)⁻¹
      = xbar (Fr.X 2) * (barOf h3 * (k : CentralizerBar (Fr.X 2)) * (barOf h3)⁻¹) *
          (xbar (Fr.X 2))⁻¹ := (hc _).symm
    _ = xbar (Fr.X 2) * barOf h3 * (k : CentralizerBar (Fr.X 2)) *
          (xbar (Fr.X 2) * barOf h3)⁻¹ := by group

omit [Finite F] in
theorem X23_mul_self : (Fr.X 2 * Fr.X 3) * (Fr.X 2 * Fr.X 3) = 1 := by
  have hc23 : Fr.X 2 * Fr.X 3 = Fr.X 3 * Fr.X 2 := Fr.X_comm 2 3
  calc (Fr.X 2 * Fr.X 3) * (Fr.X 2 * Fr.X 3) = Fr.X 2 * (Fr.X 3 * Fr.X 2) * Fr.X 3 := by group
    _ = Fr.X 2 * (Fr.X 2 * Fr.X 3) * Fr.X 3 := by rw [← hc23]
    _ = (Fr.X 2 * Fr.X 2) * (Fr.X 3 * Fr.X 3) := by group
    _ = 1 := by rw [Fr.X_sq 2, Fr.X_sq 3, one_mul]

omit [Finite F] in
theorem X23_eq_cases {s : ↥(StatedSL 4 F)}
    (hs : ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = zblkMat F 2 3) (hs2 : s * s = 1) :
    Fr.X 2 * Fr.X 3 = (Fr.D 4).ι s ∨ Fr.X 2 * Fr.X 3 = (Fr.D 4).ι s * Fr.X 4 := by
  set D4 := Fr.D 4 with hD4
  have hu : Fr.X 2 * Fr.X 3 ∈ centralizer ({Fr.X 4} : Set G) := Fr.X_mul_mem_cent 2 3 4
  have hv : D4.ι s ∈ centralizer ({Fr.X 4} : Set G) := D4.ι_mem_cent s
  have h2 : Fr.X 2 ∈ centralizer ({Fr.X 4} : Set G) := Fr.X_mem_cent 2 4
  have h3 : Fr.X 3 ∈ centralizer ({Fr.X 4} : Set G) := Fr.X_mem_cent 3 4
  have hact2 : ActsAsReflOn D4.iso (barOf h2) (reflDiag F 2) := Fr.act' 4 2 (by decide)
  have hact3 : ActsAsReflOn D4.iso (barOf h3) (reflDiag F 3) := Fr.act' 4 3 (by decide)
  have hbu : barOf hu = barOf h2 * barOf h3 := rfl
  have hbv : barOf hv = ((D4.iso.symm s : ↥D4.K) : CentralizerBar (Fr.X 4)) := by
    have := D4.proj_ιC s
    rw [← this]
    rfl
  have hsGL : (s : GL (Fin 4) F) = reflDiag F 2 * reflDiag F 3 := by
    apply Units.ext
    rw [Units.val_mul]
    show ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = reflDiagMat F 2 * reflDiagMat F 3
    rw [hs, Q3Frame.zblk_two_three_eq]
  have hv2 : D4.ι s * D4.ι s = 1 := by rw [← map_mul, hs2, map_one]
  have hs2c : D4.ι s * Fr.X 2 = Fr.X 2 * D4.ι s :=
    Fr.ι_comm_X 4 (j := 2) (k := 2) (by decide) (comm_refl_of_mat_zblk hs 2)
  have hs3c : D4.ι s * Fr.X 3 = Fr.X 3 * D4.ι s :=
    Fr.ι_comm_X 4 (j := 3) (k := 3) (by decide) (comm_refl_of_mat_zblk hs 3)
  have huv : (Fr.X 2 * Fr.X 3) * D4.ι s = D4.ι s * (Fr.X 2 * Fr.X 3) := by
    calc (Fr.X 2 * Fr.X 3) * D4.ι s = Fr.X 2 * (Fr.X 3 * D4.ι s) := mul_assoc _ _ _
      _ = Fr.X 2 * (D4.ι s * Fr.X 3) := by rw [hs3c]
      _ = (Fr.X 2 * D4.ι s) * Fr.X 3 := (mul_assoc _ _ _).symm
      _ = (D4.ι s * Fr.X 2) * Fr.X 3 := by rw [hs2c]
      _ = D4.ι s * (Fr.X 2 * Fr.X 3) := mul_assoc _ _ _
  refine eq_or_eq_mul_of_conj_eq' (Fr.orderOf_X 4) (Fr.cent 4) hu hv Fr.X23_mul_self hv2 huv ?_
  intro k hk
  have hKn : D4.K.Normal := D4.normal
  set kk : ↥D4.K := ⟨k, hk⟩ with hkk
  have hk3 : barOf h3 * k * (barOf h3)⁻¹ ∈ D4.K := hKn.conj_mem _ hk _
  have hk23 : barOf h2 * (barOf h3 * k * (barOf h3)⁻¹) * (barOf h2)⁻¹ ∈ D4.K :=
    hKn.conj_mem _ hk3 _
  have hka : barOf hu * k * (barOf hu)⁻¹ ∈ D4.K := hKn.conj_mem _ hk _
  have hkb : barOf hv * k * (barOf hv)⁻¹ ∈ D4.K := hKn.conj_mem _ hk _
  have e3 := hact3 kk ⟨_, hk3⟩ rfl
  have e2 := hact2 ⟨_, hk3⟩ ⟨_, hk23⟩ rfl
  have hLHS : (⟨barOf hu * k * (barOf hu)⁻¹, hka⟩ : ↥D4.K) = ⟨_, hk23⟩ :=
    Subtype.ext (by
      show barOf hu * k * (barOf hu)⁻¹ =
        barOf h2 * (barOf h3 * k * (barOf h3)⁻¹) * (barOf h2)⁻¹
      rw [hbu]; group)
  have hL : ((D4.iso ⟨barOf hu * k * (barOf hu)⁻¹, hka⟩ : ↥(StatedSL 4 F)) : GL (Fin 4) F) =
      reflDiag F 2 * (reflDiag F 3 * ((D4.iso kk : ↥(StatedSL 4 F)) : GL (Fin 4) F) *
        (reflDiag F 3)⁻¹) * (reflDiag F 2)⁻¹ := by
    rw [hLHS, e2, e3]
  have hR : ((D4.iso ⟨barOf hv * k * (barOf hv)⁻¹, hkb⟩ : ↥(StatedSL 4 F)) : GL (Fin 4) F) =
      (s : GL (Fin 4) F) * ((D4.iso kk : ↥(StatedSL 4 F)) : GL (Fin 4) F) *
        (s : GL (Fin 4) F)⁻¹ := by
    have hb' : (⟨barOf hv * k * (barOf hv)⁻¹, hkb⟩ : ↥D4.K) =
        D4.iso.symm s * kk * (D4.iso.symm s)⁻¹ := Subtype.ext (by
      show barOf hv * k * (barOf hv)⁻¹ = ((D4.iso.symm s : ↥D4.K) : CentralizerBar (Fr.X 4)) * k *
        ((D4.iso.symm s : ↥D4.K) : CentralizerBar (Fr.X 4))⁻¹
      rw [hbv])
    rw [hb', map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    simp
  have heq : D4.iso ⟨barOf hu * k * (barOf hu)⁻¹, hka⟩ =
      D4.iso ⟨barOf hv * k * (barOf hv)⁻¹, hkb⟩ := by
    apply Subtype.ext
    rw [hL, hR, hsGL]
    group
  have := D4.iso.injective heq
  exact congrArg Subtype.val this

theorem X23_eq_ι (hF3 : Nat.card F = 3) {s : ↥(StatedSL 4 F)}
    (hs : ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = zblkMat F 2 3) (hs2 : s * s = 1)
    (hs1 : s ≠ 1) (hsb : s ∈ blkLin (F := F) 2 3) : Fr.X 2 * Fr.X 3 = (Fr.D 4).ι s := by
  have h2 := q3_two_ne_zero hF3
  have hF4 : Nat.card F % 4 = 3 := by rw [hF3]
  rcases Fr.X23_eq_cases hs hs2 with h | h
  · exact h
  exfalso
  obtain ⟨s₀, hs₀c, hs₀2, hs₀1, hs₀x⟩ := Fr.exists_s0 4
  have hmat := Q3Frame.central_mul_mat hF4 h2 hs₀c hs₀1 hsb hs2 hs1
  have hz' : s₀ * s ∈ blkLin (F := F) 0 1 := by
    rw [mem_blkLin, hmat]
    exact isBlockAt_zblkMat 0 1
  have hscomm : s * s₀ = s₀ * s := Subgroup.mem_center_iff.1 hs₀c s
  have hy : Fr.X 2 * Fr.X 3 = (Fr.D 4).ι (s₀ * s) := by
    calc Fr.X 2 * Fr.X 3 = (Fr.D 4).ι s * Fr.X 4 := h
      _ = (Fr.D 4).ι s * (Fr.D 4).ι s₀ := by rw [hs₀x]
      _ = (Fr.D 4).ι (s * s₀) := (map_mul _ _ _).symm
      _ = (Fr.D 4).ι (s₀ * s) := by rw [hscomm]
  have hle : (blkLin (F := F) 0 1).map (Fr.D 4).ι ≤ (blkLin (F := F) 0 1).map (Fr.D 2).ι :=
    Fr.blk_le_of_layers hF3 (e := 2) (f := 4) (a := 0) (b := 1) (c := 3) (d := 2) (a' := 0)
      (b' := 1) (c' := 2) (d' := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hA : Fr.X 2 * Fr.X 3 ∈ Fr.Ablk := by
    rw [hy]
    exact Subgroup.map_mono le_sup_right (hle ⟨s₀ * s, hz', rfl⟩)
  have hcent : ∀ w ∈ Fr.Ablk, (Fr.X 2 * Fr.X 3) * w = w * (Fr.X 2 * Fr.X 3) := by
    intro w hw
    obtain ⟨hw2, hw3⟩ := Fr.A_comm_X hw
    calc (Fr.X 2 * Fr.X 3) * w = Fr.X 2 * (Fr.X 3 * w) := mul_assoc _ _ _
      _ = Fr.X 2 * (w * Fr.X 3) := by rw [hw3]
      _ = (Fr.X 2 * w) * Fr.X 3 := (mul_assoc _ _ _).symm
      _ = (w * Fr.X 2) * Fr.X 3 := by rw [hw2]
      _ = w * (Fr.X 2 * Fr.X 3) := mul_assoc _ _ _
  have h1 := Fr.A_center hF3 _ hA hcent
  apply Fr.X_inj 2 3 (by decide)
  have h3 : Fr.X 3 = (Fr.X 2)⁻¹ := eq_inv_of_mul_eq_one_right h1
  calc Fr.X 2 = (Fr.X 2)⁻¹ := (inv_eq_of_mul_eq_one_right (Fr.X_sq 2)).symm
    _ = Fr.X 3 := h3.symm

theorem perf2 (hF3 : Nat.card F = 3) {Q : Subgroup G}
    (hQ : Q ≤ centralizer ({Fr.X 2} : Set G) ⊓ centralizer ({Fr.X 2 * Fr.X 3} : Set G))
    (hperf : ⁅Q, Q⁆ = Q) : Q ≤ Fr.Ablk := by
  set D2 := Fr.D 2 with hD2
  have h2 := q3_two_ne_zero hF3
  have hQX : Q ≤ centralizer ({Fr.X 2} : Set G) := fun q hq => (Subgroup.mem_inf.1 (hQ hq)).1
  have hQc : ∀ q ∈ Q, q * (Fr.X 2 * Fr.X 3) = (Fr.X 2 * Fr.X 3) * q := fun q hq =>
    mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hQ hq)).2
  have hrange : Q ≤ D2.ι.range := D2.le_range_ι hperf hQX
  set Q' : Subgroup ↥(StatedSL 4 F) := Q.comap D2.ι with hQ'
  have hmap : Q'.map D2.ι = Q := by
    rw [hQ', Subgroup.map_comap_eq]
    exact inf_eq_right.2 hrange
  have hQ'perf : ⁅Q', Q'⁆ = Q' := by
    apply Subgroup.map_injective D2.ι_injective
    rw [Subgroup.map_commutator, hmap, hperf]
  have hcX : Fr.X 2 * Fr.X 3 ∈ centralizer ({Fr.X 2} : Set G) := Fr.X_mul_mem_cent 2 3 2
  have hactc := Fr.act_X23 hcX
  have hQ'le : Q' ≤ reflCent F 2 := by
    intro t ht
    rw [mem_reflCent]
    exact D2.comm_of_ι_comm hcX hactc (hQc (D2.ι t) ht)
  have hSigcard : Nat.card ↥(blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1) = 5616 := by
    have hcm : Nat.card ↥Fr.Ablk = Nat.card ↥(blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1) :=
      Subgroup.card_map_of_injective D2.ι_injective
    exact hcm.symm.trans (Fr.A_card hF3)
  have hle2 : blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1 ≤ reflCent F 2 :=
    blkLin_sup_le_reflCent (a := 3) (b := 0) (d := 1) (c := 2) (by decide) (by decide) (by decide)
  have hcard : Nat.card (reflCent F 2) ≤
      2 * Nat.card ↥(blkLin (F := F) 3 0 ⊔ blkLin (F := F) 0 1) := by
    rw [hSigcard]
    calc Nat.card (reflCent F 2) ≤ Nat.card (GL (Fin 3) F) := card_reflCent_le h2 2
      _ = 11232 := card_gl3_three hF3
      _ = 2 * 5616 := by norm_num
  have hle := perfect_le_of_card_le_two_mul hle2 hcard hQ'le hQ'perf
  rw [← hmap]
  exact Subgroup.map_mono hle

theorem perfx (hF3 : Nat.card F = 3) {s : ↥(StatedSL 4 F)}
    (hs : ((s : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = zblkMat F 2 3) (hs2 : s * s = 1)
    (hs1 : s ≠ 1) (hsb : s ∈ blkLin (F := F) 2 3) {Q : Subgroup G}
    (hQ : Q ≤ centralizer ({Fr.X 4} : Set G) ⊓ centralizer ({Fr.X 2 * Fr.X 3} : Set G))
    (hperf : ⁅Q, Q⁆ = Q) : Q = ⊥ := by
  set D4 := Fr.D 4 with hD4
  have h2 := q3_two_ne_zero hF3
  have hc := Fr.X23_eq_ι hF3 hs hs2 hs1 hsb
  have hQX : Q ≤ centralizer ({Fr.X 4} : Set G) := fun q hq => (Subgroup.mem_inf.1 (hQ hq)).1
  have hrange : Q ≤ D4.ι.range := D4.le_range_ι hperf hQX
  set Q' : Subgroup ↥(StatedSL 4 F) := Q.comap D4.ι with hQ'
  have hmap : Q'.map D4.ι = Q := by
    rw [hQ', Subgroup.map_comap_eq]
    exact inf_eq_right.2 hrange
  have hQ'perf : ⁅Q', Q'⁆ = Q' := by
    apply Subgroup.map_injective D4.ι_injective
    rw [Subgroup.map_commutator, hmap, hperf]
  have hcomm : ∀ g ∈ Q', g * s = s * g := by
    intro g hg
    have hg' : D4.ι g ∈ Q := hg
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hQ hg')).2
    rw [hc, ← map_mul, ← map_mul] at h1
    exact D4.ι_injective h1
  have hle := perfect_le_pair_lin h2 (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) hsb hs2 hs1 Q' hcomm hQ'perf
  have hsolv : Group.IsSolvable ↥(blkLin (F := F) 0 1 ⊔ blkLin (F := F) 2 3) := by
    have := blkLin_isSolvable (F := F) hF3 (a := 0) (b := 1) (by decide)
    have := blkLin_isSolvable (F := F) hF3 (a := 2) (b := 3) (by decide)
    exact q3_isSolvable_sup_of_commute (fun a ha b hb => blkLin_commute 0 1 2 3
      (by decide) (by decide) (by decide) (by decide) a ha b hb)
  have hQ's : Group.IsSolvable ↥Q' := by
    have : Group.IsSolvable ↥(Q'.subgroupOf (blkLin (F := F) 0 1 ⊔ blkLin (F := F) 2 3)) :=
      inferInstance
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hle).surjective
  have hbot : Q' = ⊥ := q3_eq_bot_of_perfect_of_isSolvable hQ'perf hQ's
  rw [← hmap, hbot, Subgroup.map_bot]

theorem A_comm_J (hF3 : Nat.card F = 3) :
    ∀ a ∈ Fr.Ablk, ∀ j ∈ Fr.Jblk, a * j = j * a := by
  have I_a : (blkLin (F := F) 2 3).map (Fr.D 4).ι = (blkLin (F := F) 1 2).map (Fr.D 1).ι :=
    Fr.blk_eq_of_layers hF3 (e := 4) (f := 1) (a := 2) (b := 3) (c := 1) (d := 0) (a' := 1)
      (b' := 2) (c' := 3) (d' := 0) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have I_b : (blkLin (F := F) 3 0).map (Fr.D 2).ι = (blkLin (F := F) 3 0).map (Fr.D 1).ι :=
    Fr.blk_eq_of_layers hF3 (e := 2) (f := 1) (a := 3) (b := 0) (c := 1) (d := 2) (a' := 3)
      (b' := 0) (c' := 1) (d' := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have I_c : (blkLin (F := F) 0 1).map (Fr.D 2).ι = (blkLin (F := F) 0 1).map (Fr.D 4).ι :=
    Fr.blk_eq_of_layers hF3 (e := 2) (f := 4) (a := 0) (b := 1) (c := 3) (d := 2) (a' := 0)
      (b' := 1) (c' := 2) (d' := 3) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hA : Fr.Ablk = (blkLin (F := F) 3 0).map (Fr.D 2).ι ⊔ (blkLin (F := F) 0 1).map (Fr.D 2).ι :=
    Subgroup.map_sup _ _ _
  have hle : Fr.Ablk ≤ centralizer (Fr.Jblk : Set G) := by
    rw [hA]
    refine sup_le ?_ ?_
    · rw [I_b]
      rintro _ ⟨g, hg, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hj' : j ∈ (blkLin (F := F) 1 2).map (Fr.D 1).ι := by
        rw [← I_a]
        exact hj
      obtain ⟨h, hh, rfl⟩ := hj'
      rw [← map_mul, ← map_mul, blkLin_commute 3 0 1 2 (by decide) (by decide) (by decide)
        (by decide) g hg h hh]
    · rw [I_c]
      rintro _ ⟨g, hg, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      obtain ⟨h, hh, rfl⟩ := hj
      rw [← map_mul, ← map_mul, blkLin_commute 0 1 2 3 (by decide) (by decide) (by decide)
        (by decide) g hg h hh]
  exact fun a ha j hj => (Subgroup.mem_centralizer_iff.1 (hle ha) j hj).symm

theorem cfg (hF3 : Nat.card F = 3) :
    Q3Cfg G F (Fr.X 2 * Fr.X 3) (Fr.X 4) (Fr.X 2) (Fr.X 4 * (Fr.X 2 * Fr.X 3)) Fr.Ablk Fr.Jblk := by
  have h2 := q3_two_ne_zero hF3
  have hF4 : Nat.card F % 4 = 3 := by rw [hF3]
  have hodd3 : Odd (Nat.card F) := by rw [hF3]; exact ⟨1, rfl⟩
  obtain ⟨s, hsb, hsmat, hss, hs1, hscen⟩ := exists_zblk h2 (c := 2) (d := 3) (by decide)
  have hc : Fr.X 2 * Fr.X 3 = (Fr.D 4).ι s := Fr.X23_eq_ι hF3 hsmat hss hs1 hsb
  obtain ⟨s₀, hs₀c, hs₀2, hs₀1, hs₀x⟩ := Fr.exists_s0 4
  have hcc : (Fr.X 2 * Fr.X 3) * (Fr.X 2 * Fr.X 3) = 1 := Fr.X23_mul_self
  have hc1 : Fr.X 2 * Fr.X 3 ≠ 1 := by
    intro h
    apply Fr.X_inj 2 3 (by decide)
    have h3 : Fr.X 3 = (Fr.X 2)⁻¹ := eq_inv_of_mul_eq_one_right h
    calc Fr.X 2 = (Fr.X 2)⁻¹ := (inv_eq_of_mul_eq_one_right (Fr.X_sq 2)).symm
      _ = Fr.X 3 := h3.symm
  have hcomm : ∀ k : Fin 5, (Fr.X 2 * Fr.X 3) * Fr.X k = Fr.X k * (Fr.X 2 * Fr.X 3) := fun k =>
    mem_centralizer_singleton_iff.1 (Fr.X_mul_mem_cent 2 3 k)
  have hc2 : orderOf (Fr.X 2 * Fr.X 3) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [sq]; exact hcc) hc1
  have hyy : (Fr.X 4 * (Fr.X 2 * Fr.X 3)) * (Fr.X 4 * (Fr.X 2 * Fr.X 3)) = 1 := by
    calc (Fr.X 4 * (Fr.X 2 * Fr.X 3)) * (Fr.X 4 * (Fr.X 2 * Fr.X 3))
        = Fr.X 4 * ((Fr.X 2 * Fr.X 3) * Fr.X 4) * (Fr.X 2 * Fr.X 3) := by group
      _ = Fr.X 4 * (Fr.X 4 * (Fr.X 2 * Fr.X 3)) * (Fr.X 2 * Fr.X 3) := by rw [hcomm 4]
      _ = (Fr.X 4 * Fr.X 4) * ((Fr.X 2 * Fr.X 3) * (Fr.X 2 * Fr.X 3)) := by group
      _ = 1 := by rw [Fr.X_sq 4, hcc, one_mul]
  have hy1 : Fr.X 4 * (Fr.X 2 * Fr.X 3) ≠ 1 := by
    intro h
    have h4 : Fr.X 2 * Fr.X 3 = Fr.X 4 := by
      have h5 : Fr.X 2 * Fr.X 3 = (Fr.X 4)⁻¹ := eq_inv_of_mul_eq_one_right h
      rw [h5]
      exact inv_eq_of_mul_eq_one_right (Fr.X_sq 4)
    have hprod := Fr.X_prod
    have hassoc : Fr.X 0 * Fr.X 1 * Fr.X 2 * Fr.X 3 * Fr.X 4 =
        Fr.X 0 * Fr.X 1 * (Fr.X 2 * Fr.X 3) * Fr.X 4 := by group
    rw [hassoc, h4] at hprod
    have h01 : Fr.X 0 * Fr.X 1 = 1 := by
      calc Fr.X 0 * Fr.X 1 = Fr.X 0 * Fr.X 1 * (Fr.X 4 * Fr.X 4) := by rw [Fr.X_sq 4, mul_one]
        _ = Fr.X 0 * Fr.X 1 * Fr.X 4 * Fr.X 4 := by group
        _ = 1 := hprod
    apply Fr.X_inj 0 1 (by decide)
    have h3 : Fr.X 1 = (Fr.X 0)⁻¹ := eq_inv_of_mul_eq_one_right h01
    calc Fr.X 0 = (Fr.X 0)⁻¹ := (inv_eq_of_mul_eq_one_right (Fr.X_sq 0)).symm
      _ = Fr.X 1 := h3.symm
  have hymem : Fr.X 4 * (Fr.X 2 * Fr.X 3) ∈ Fr.Ablk := by
    have hmat := Q3Frame.central_mul_mat hF4 h2 hs₀c hs₀1 hsb hss hs1
    have hz' : s₀ * s ∈ blkLin (F := F) 0 1 := by
      rw [mem_blkLin, hmat]
      exact isBlockAt_zblkMat 0 1
    have hle : (blkLin (F := F) 0 1).map (Fr.D 4).ι ≤ (blkLin (F := F) 0 1).map (Fr.D 2).ι :=
      Fr.blk_le_of_layers hF3 (e := 2) (f := 4) (a := 0) (b := 1) (c := 3) (d := 2) (a' := 0)
        (b' := 1) (c' := 2) (d' := 3) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    have hy : Fr.X 4 * (Fr.X 2 * Fr.X 3) = (Fr.D 4).ι (s₀ * s) := by
      rw [map_mul, hs₀x, hc]
    rw [hy]
    exact Subgroup.map_mono le_sup_right (hle ⟨s₀ * s, hz', rfl⟩)
  have hAV : Fr.Ablk ≤ centralizer ({Fr.X 2} : Set G) ⊓ centralizer ({Fr.X 2 * Fr.X 3} : Set G) := by
    intro a ha
    obtain ⟨hw2, hw3⟩ := Fr.A_comm_X ha
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_centralizer_singleton_iff]
      exact hw2
    · rw [mem_centralizer_singleton_iff]
      calc a * (Fr.X 2 * Fr.X 3) = (a * Fr.X 2) * Fr.X 3 := (mul_assoc _ _ _).symm
        _ = (Fr.X 2 * a) * Fr.X 3 := by rw [hw2]
        _ = Fr.X 2 * (a * Fr.X 3) := mul_assoc _ _ _
        _ = Fr.X 2 * (Fr.X 3 * a) := by rw [hw3]
        _ = (Fr.X 2 * Fr.X 3) * a := (mul_assoc _ _ _).symm
  obtain ⟨q8J, hq8J, hq8Jblk⟩ := exists_q8_blkLin (F := F) hF4 (c := 2) (d := 3) (by decide)
  obtain ⟨q8A, hq8A, hq8Ablk⟩ := exists_q8_blkLin (F := F) hF4 (c := 0) (d := 1) (by decide)
  have e1 : (Fr.X 4 * (Fr.X 2 * Fr.X 3)) * (Fr.X 2 * Fr.X 3) = Fr.X 4 := by
    rw [mul_assoc, hcc, mul_one]
  have e2 : (Fr.X 2 * Fr.X 3) * (Fr.X 4 * (Fr.X 2 * Fr.X 3)) = Fr.X 4 := by
    calc (Fr.X 2 * Fr.X 3) * (Fr.X 4 * (Fr.X 2 * Fr.X 3))
        = ((Fr.X 2 * Fr.X 3) * Fr.X 4) * (Fr.X 2 * Fr.X 3) := (mul_assoc _ _ _).symm
      _ = (Fr.X 4 * (Fr.X 2 * Fr.X 3)) * (Fr.X 2 * Fr.X 3) := by rw [hcomm 4]
      _ = Fr.X 4 := e1
  have hJC : Fr.Jblk ≤ centralizer ({Fr.X 2 * Fr.X 3} : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_centralizer_singleton_iff, hc, ← map_mul, ← map_mul, hscen t ht]
  exact ⟨hc2, Fr.orderOf_X 4, Fr.orderOf_X 2, hyy, hy1, mem_centralizer_singleton_iff.2 (hcomm 4).symm,
    mem_centralizer_singleton_iff.2 (hcomm 2).symm, mem_centralizer_singleton_iff.2 (e1.trans e2.symm),
    e1.symm, hymem, (Fr.A_data hF3).1, (Fr.A_data hF3).2, Fr.A_center hF3, hAV,
    fun Q hQ hperf => Fr.perf2 hF3 hQ hperf,
    fun Q hQ hperf => Fr.perfx hF3 hsmat hss hs1 hsb hQ hperf, hJC, Fr.A_comm_J hF3,
    oddGenerated_map (Fr.D 4).ι (blkLin_oddGenerated hodd3 2 3 (by decide)),
    ⟨(Fr.D 4).ι.comp q8J, (Fr.D 4).ι_injective.comp hq8J, fun g => ⟨q8J g, hq8Jblk g, rfl⟩⟩,
    ⟨(Fr.D 2).ι.comp q8A, (Fr.D 2).ι_injective.comp hq8A, fun g =>
      Subgroup.map_mono le_sup_right ⟨q8A g, hq8Ablk g, rfl⟩⟩⟩

end Q3FrameB

end Frame

end CFSG.GH74.Generic.S1
