module

public import CFSG.HardMathSupport.U4FF.ClassDatumFields
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverType
public import CFSG.HardMathSupport.U4FF.ClassDatumHecke

public section

namespace CFSG.HardMathSupport.U4FF

open Matrix
open scoped MatrixGroups
open CFSG.LieType.Universal.Unitary (SU conjTr antidiag mem_SU)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.Quasithin.SmithCurtis (CurtisDatum SplitOver)
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  (CentralCoverData CoverRankOne IsCentralCover IsPElt splitOver_of_pow_card_sub_one)
open CFSG.HardMathSupport.U4FF.Datum

section Datum

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem U_eq_s (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) :
    ∀ u ∈ UpperU K n, ∃ x ∈ Xs K n s, ∃ v ∈ Uss K n s, u = x * v := by
  fin_cases s
  · exact fun u hu => U_eq0 hK hu
  · exact fun u hu => U_eq1 hK hu

theorem X_normUs_s (s : Fin 2) :
    ∀ x ∈ Xs K n s, ∀ v ∈ Uss K n s, x * v * x⁻¹ ∈ Uss K n s := by
  fin_cases s
  · exact fun x hx v hv => X0_normUs0 hx hv
  · exact fun x hx v hv => X1_normUs1 hx hv

theorem n_normUs_s (s : Fin 2) :
    ∀ v ∈ Uss K n s, nSimple K n s * v * (nSimple K n s)⁻¹ ∈ Uss K n s := by
  fin_cases s
  · exact fun v hv => n0_normUs0 hv
  · exact fun v hv => n1_normUs1 hv

theorem n_normUs'_s (s : Fin 2) :
    ∀ v ∈ Uss K n s, (nSimple K n s)⁻¹ * v * nSimple K n s ∈ Uss K n s := by
  fin_cases s
  · exact fun v hv => n0_normUs0' hv
  · exact fun v hv => n1_normUs1' hv

theorem n_conjY_s (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) :
    ∀ y ∈ Jconj K n (Xs K n s), nSimple K n s * y * (nSimple K n s)⁻¹ ∈ Xs K n s := by
  fin_cases s
  · exact fun y hy => n0_conjY0 hK hy
  · exact fun y hy => n1_conjY1 hy

theorem H_normUs_s (s : Fin 2) :
    ∀ h ∈ Hd K n, ∀ v ∈ Uss K n s, h * v * h⁻¹ ∈ Uss K n s := by
  fin_cases s
  · exact fun h hh v hv => H_normUs0 hh hv
  · exact fun h hh v hv => H_normUs1 hh hv

theorem H_normX_s (s : Fin 2) :
    ∀ h ∈ Hd K n, ∀ x ∈ Xs K n s, h * x * h⁻¹ ∈ Xs K n s := by
  fin_cases s
  · exact fun h hh x hx => H_normX0 hh hx
  · exact fun h hh x hx => H_normX1 hh hx

theorem X_ne_bot_s (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) : Xs K n s ≠ ⊥ := by
  fin_cases s
  · exact X0_ne_bot hK
  · exact X1_ne_bot hK

theorem bruhatY_s (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) :
    ∀ y ∈ Jconj K n (Xs K n s), y ≠ 1 →
      ∃ h ∈ Hd K n, ∃ a ∈ Xs K n s, ∃ c ∈ Xs K n s, y = a * (h * nSimple K n s) * c := by
  fin_cases s
  · exact fun y hy hy1 => bruhatY0 hK hy hy1
  · exact fun y hy hy1 => bruhatY1 hK hy hy1

open Classical in
@[expose] noncomputable def phi4 (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) (x : G4 K n) :
    G4 K n :=
  if hx : x ∈ Xs K n s ∧ x ≠ 1 then (phi_ex hK s hx.1 hx.2).choose else 1

open Classical in
@[expose] noncomputable def psi4 (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) (x : G4 K n) :
    G4 K n :=
  if hx : x ∈ Xs K n s ∧ x ≠ 1 then (psi_ex hK s hx.1 hx.2).choose else 1

theorem phi4_mem (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) {x : G4 K n} (hx : x ∈ Xs K n s)
    (hx1 : x ≠ 1) : phi4 hK s x ∈ Hd K n := by
  unfold phi4
  rw [dif_pos ⟨hx, hx1⟩]
  exact (phi_ex hK s hx hx1).choose_spec.1

theorem psi4_mem (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) {x : G4 K n} (hx : x ∈ Xs K n s)
    (hx1 : x ≠ 1) : psi4 hK s x ∈ Hd K n := by
  unfold psi4
  rw [dif_pos ⟨hx, hx1⟩]
  exact (psi_ex hK s hx hx1).choose_spec.1

theorem phi4_spec (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) {x : G4 K n} (hx : x ∈ Xs K n s)
    (hx1 : x ≠ 1) :
    ∃ l ∈ LowerU K n, ∃ u ∈ UpperU K n, x * nSimple K n s = l * phi4 hK s x * u := by
  unfold phi4
  rw [dif_pos ⟨hx, hx1⟩]
  obtain ⟨l, hl, u, hu, e⟩ := (phi_ex hK s hx hx1).choose_spec.2
  exact ⟨l, hl, u, hu, e⟩

theorem psi4_spec (hK : Nat.card K = (2 ^ n) ^ 2) (s : Fin 2) {x : G4 K n} (hx : x ∈ Xs K n s)
    (hx1 : x ≠ 1) :
    ∃ a ∈ Xs K n s, ∃ u ∈ UpperU K n,
      nSimple K n s * x * nSimple K n s = a * nSimple K n s * psi4 hK s x * u := by
  unfold psi4
  rw [dif_pos ⟨hx, hx1⟩]
  obtain ⟨a, ha, u, hu, e⟩ := (psi_ex hK s hx hx1).choose_spec.2
  exact ⟨a, ha, u, hu, e⟩

end Datum

section Interface

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def datum4 (hK : Nat.card K = (2 ^ n) ^ 2) :
    CurtisDatum (G4 K n) csB 2 where
  U := UpperU K n
  L := LowerU K n
  H := Hd K n
  X := Xs K n
  Y := fun s => Jconj K n (Xs K n s)
  Us := Uss K n
  Q := fun s => Jconj K n (Uss K n s)
  n := nSimple K n
  nW := nHom K n
  isPGroup_U := isPGroup_U
  isPGroup_L := isPGroup_L
  U_inf_L := UpperU_inf_LowerU
  H_comm := fun _ ha _ hb => Hd_comm ha hb
  H_normU := fun _ hh _ hu => H_normU hh hu
  H_normU' := fun _ hh _ hu => H_normU' hh hu
  H_normL := fun _ hh _ hl => H_normL hh hl
  H_normX := fun s => H_normX_s s
  H_normQ := fun s => H_normJconj (H_normUs_s s)
  X_le := fun s => Xs_le_U s
  X_ne_bot := fun s => X_ne_bot_s hK s
  U_eq := fun s => U_eq_s hK s
  Us_le := fun s => Uss_le_U s
  X_normUs := fun s => X_normUs_s s
  n_normUs := fun s => n_normUs_s s
  n_normUs' := fun s => n_normUs'_s s
  Y_le := fun s => Jconj_le_L (Xs_le_U s)
  Q_le := fun s => Jconj_le_L (Uss_le_U s)
  L_le := fun s => L_le_Jconj_sup (U_eq_s hK s)
  X_normQ := fun s => X_normJconj (X_normUs_s s) (n_normUs_s s) (n_normUs'_s s) (n_conjY_s hK s)
  Y_normQ := fun s => Jconj_normJconj (X_normUs_s s)
  n_normQ := fun s => n_normJconj (jSU_comm_nHom _) (n_normUs_s s)
  n_conjX := fun s => n_conjX_of (jSU_comm_nHom _) (n_conjY_s hK s)
  n_conjY := fun s => n_conjY_s hK s
  n_sq := fun s => by
    rw [nSimple_sq]
    exact one_mem _
  n_normH := fun _ _ hh => nHom_normH' _ hh
  phi := phi4 hK
  psi := psi4 hK
  phi_mem := fun s _ hx hx1 => phi4_mem hK s hx hx1
  psi_mem := fun s _ hx hx1 => psi4_mem hK s hx hx1
  phi_spec := fun s _ hx hx1 => phi4_spec hK s hx hx1
  psi_spec := fun s _ hx hx1 => psi4_spec hK s hx hx1
  bruhatY := fun s => bruhatY_s hK s
  nW_one := map_one _
  nW_simple_mul := fun w s _ => by
    rw [map_mul]
    rfl
  nW_conj := fun w s h => nW_conj_all w s h
  heckeDeg_mul := fun w s h => heckeDeg_mul_G4 hK w s h
  cover := fun g => cover_G4 hK g

theorem datum4_U (hK : Nat.card K = (2 ^ n) ^ 2) : (datum4 hK).U = UpperU K n := rfl

theorem datum4_L (hK : Nat.card K = (2 ^ n) ^ 2) : (datum4 hK).L = LowerU K n := rfl

theorem datum4_H (hK : Nat.card K = (2 ^ n) ^ 2) : (datum4 hK).H = Hd K n := rfl

theorem datum4_nW_w0 (hK : Nat.card K = (2 ^ n) ^ 2) : (datum4 hK).nW w0 = jSU K n :=
  nHom_w0

@[expose] noncomputable def cover4 (hK : Nat.card K = (2 ^ n) ^ 2) :
    CentralCoverData (datum4 hK) (MonoidHom.id (G4 K n)) 2 where
  cover :=
    { surj := Function.surjective_id
      ker_le := by
        rw [MonoidHom.ker_id]
        exact bot_le
      coprime := by
        rw [MonoidHom.ker_id, Subgroup.card_bot]
        exact Nat.coprime_one_left 2 }
  nhatW := (datum4 hK).nW
  map_nhatW := fun _ => rfl
  nhatW_one := (datum4 hK).nW_one
  nhatW_simple_mul := fun w s _ => by
    show nHom K n (csB.simple s * w) = nHom K n (csB.simple s) * nHom K n w
    rw [map_mul]
  hcomm := fun _ ha _ hb => Hd_comm ha hb

theorem cover4_lU (hK : Nat.card K = (2 ^ n) ^ 2) : (cover4 hK).lU = UpperU K n := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, isPElt_of_mem_U hx⟩

theorem cover4_lL (hK : Nat.card K = (2 ^ n) ^ 2) : (cover4 hK).lL = LowerU K n := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, isPElt_of_mem_L hx⟩

theorem fq_neg (x : Fq K n) : -x = x :=
  Subtype.ext (by rw [NegMemClass.coe_neg, CharTwo.neg_eq])

theorem fq_unit_neg (u : (Fq K n)ˣ) : -u = u := Units.ext (fq_neg _)

theorem unit_neg (u : Kˣ) : -u = u := Units.ext (by rw [Units.val_neg, CharTwo.neg_eq])

theorem phi_id0 (hK : Nat.card K = (2 ^ n) ^ 2) (u : Kˣ) :
    x0 hK (u : K) * nHom K n s0 =
      y0 hK ((u⁻¹ : Kˣ) : K) * hTor0 hK (-u) * x0 hK (-((u⁻¹ : Kˣ) : K)) := by
  rw [unit_neg, CharTwo.neg_eq]
  exact rank0_phi hK u

theorem psi_id0 (hK : Nat.card K = (2 ^ n) ^ 2) (u : Kˣ) :
    nHom K n s0 * x0 hK (u : K) * nHom K n s0 =
      x0 hK (-((u⁻¹ : Kˣ) : K)) * nHom K n s0 * hTor0 hK (-u) * x0 hK (-((u⁻¹ : Kˣ) : K)) := by
  rw [unit_neg, CharTwo.neg_eq]
  exact rank0_psi hK u

theorem phi_id1 (hK : Nat.card K = (2 ^ n) ^ 2) (u : (Fq K n)ˣ) :
    x1 hK (u : Fq K n) * nHom K n s1 =
      y1 hK ((u⁻¹ : (Fq K n)ˣ) : Fq K n) * hTor1 hK (-u) *
        x1 hK (-((u⁻¹ : (Fq K n)ˣ) : Fq K n)) := by
  rw [fq_unit_neg, fq_neg]
  exact rank1_phi hK u

theorem psi_id1 (hK : Nat.card K = (2 ^ n) ^ 2) (u : (Fq K n)ˣ) :
    nHom K n s1 * x1 hK (u : Fq K n) * nHom K n s1 =
      x1 hK (-((u⁻¹ : (Fq K n)ˣ) : Fq K n)) * nHom K n s1 * hTor1 hK (-u) *
        x1 hK (-((u⁻¹ : (Fq K n)ˣ) : Fq K n)) := by
  rw [fq_unit_neg, fq_neg]
  exact rank1_psi hK u

@[expose] noncomputable def xs4 (hK : Nat.card K = (2 ^ n) ^ 2) : (s : Fin 2) → Fs K n s → G4 K n
  | 0, c => x0 hK c
  | 1, c => x1 hK c

@[expose] noncomputable def ys4 (hK : Nat.card K = (2 ^ n) ^ 2) : (s : Fin 2) → Fs K n s → G4 K n
  | 0, c => y0 hK c
  | 1, c => y1 hK c

@[expose] noncomputable def hh4 (hK : Nat.card K = (2 ^ n) ^ 2) :
    (s : Fin 2) → (Fs K n s)ˣ → G4 K n
  | 0, u => hTor0 hK u
  | 1, u => hTor1 hK u

theorem x0_zero (hK : Nat.card K = (2 ^ n) ^ 2) : x0 hK (0 : K) = 1 :=
  eq_of_gm_eq (by rw [gm_x0 hK, x0Mat_zero, gm_one])

theorem x1_zero (hK : Nat.card K = (2 ^ n) ^ 2) : x1 hK (0 : Fq K n) = 1 :=
  eq_of_gm_eq (by
    rw [gm_x1 hK]
    show x1Mat ((0 : Fq K n) : K) = _
    rw [gm_one]
    exact x1Mat_zero)

theorem x0_inj (hK : Nat.card K = (2 ^ n) ^ 2) : Function.Injective (x0 hK : K → G4 K n) := by
  intro c d h
  have := congrArg (fun g => gm g 0 1) h
  simp only [gm_x0 hK] at this
  simpa [x0Mat] using this

theorem x1_inj (hK : Nat.card K = (2 ^ n) ^ 2) :
    Function.Injective (x1 hK : Fq K n → G4 K n) := by
  intro c d h
  have := congrArg (fun g => gm g 1 2) h
  simp only [gm_x1 hK] at this
  exact Subtype.ext (by simpa [x1Mat] using this)

theorem x0_surj (hK : Nat.card K = (2 ^ n) ^ 2) {g : G4 K n} (hg : g ∈ X0 K n) :
    ∃ c : K, x0 hK c = g := by
  obtain ⟨c, hc⟩ := mem_X0.mp hg
  exact ⟨c, eq_of_gm_eq (by rw [gm_x0 hK, hc])⟩

theorem x1_surj (hK : Nat.card K = (2 ^ n) ^ 2) {g : G4 K n} (hg : g ∈ X1 K n) :
    ∃ c : Fq K n, x1 hK c = g := by
  obtain ⟨c, hcq, hc⟩ := mem_X1.mp hg
  exact ⟨⟨c, hcq⟩, eq_of_gm_eq (by rw [gm_x1 hK, hc])⟩

@[expose] noncomputable def rank1_4 (hK : Nat.card K = (2 ^ n) ^ 2) :
    CoverRankOne (cover4 hK) (Fs K n) where
  x := xs4 hK
  y := ys4 hK
  hh := hh4 hK
  x_mem := Fin.forall_fin_two.mpr
    ⟨fun c => ⟨x0_mem_X0 hK c, isPElt_of_mem_U (X0_le_U n (x0_mem_X0 hK c))⟩,
     fun c => ⟨x1_mem_X1 hK c, isPElt_of_mem_U (X1_le_U n (x1_mem_X1 hK c))⟩⟩
  x_surj := Fin.forall_fin_two.mpr
    ⟨fun _ hg => x0_surj hK hg.1, fun _ hg => x1_surj hK hg.1⟩
  x_zero := Fin.forall_fin_two.mpr ⟨x0_zero hK, x1_zero hK⟩
  x_inj := Fin.forall_fin_two.mpr ⟨x0_inj hK, x1_inj hK⟩
  y_mem := Fin.forall_fin_two.mpr
    ⟨fun c => ⟨y0_mem_L hK c, isPElt_of_mem_L (y0_mem_L hK c)⟩,
     fun c => ⟨y1_mem_L hK c, isPElt_of_mem_L (y1_mem_L hK c)⟩⟩
  hh_mem := Fin.forall_fin_two.mpr ⟨fun u => hTor0_mem hK u, fun u => hTor1_mem hK u⟩
  hh_mul := Fin.forall_fin_two.mpr ⟨fun u v => hTor0_mul hK u v, fun u v => hTor1_mul hK u v⟩
  hh_one := Fin.forall_fin_two.mpr ⟨hTor0_one hK, hTor1_one hK⟩
  phi_id := Fin.forall_fin_two.mpr ⟨phi_id0 hK, phi_id1 hK⟩
  psi_id := Fin.forall_fin_two.mpr ⟨psi_id0 hK, psi_id1 hK⟩

theorem rank1_4_hh0 (hK : Nat.card K = (2 ^ n) ^ 2) (u : Kˣ) :
    (rank1_4 hK).hh 0 u = hTor0 hK u := rfl

theorem rank1_4_hh1 (hK : Nat.card K = (2 ^ n) ^ 2) (v : (Fq K n)ˣ) :
    (rank1_4 hK).hh 1 v = hTor1 hK v := rfl

theorem hodd4 (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∀ h ∈ (datum4 hK).H.comap (MonoidHom.id _), IsPElt 2 h → h = 1 :=
  fun _ hh hp => Hd_eq_one_of_isPElt hK hh hp

theorem splitOver4 (hK : Nat.card K = (2 ^ n) ^ 2) (k : Type*) [Field k] [Algebra K k] :
    SplitOver k ((datum4 hK).H.comap (MonoidHom.id _)) :=
  splitOver_of_pow_card_sub_one k (fun _ hh => Hd_pow_card_sub_one hh)

end Interface

end CFSG.HardMathSupport.U4FF
