module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28LocalVSub
public import CFSG.LocalAnalysis.AGLEmbedding.G28InSitu

set_option linter.unusedSectionVars false

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.RankThree.PartTwo.Sec4.Item434G28 CFSG.PreuniquenessRankFour.Helpers
open scoped commutatorElement

attribute [local irreducible] txL tU tZ tO tzc gW

section InSitu


variable {K : Type} [Field K] [Finite K] [CharP K 2] (M : G28Model K)

theorem phi_pow_zE (i : ℕ) : (phi ^ i : MulAut (adjointGroup .G2 K)) (zE M) = zE M := by
  induction i with
  | zero => rfl
  | succ k ih => rw [pow_succ', MulAut.mul_apply, ih, phi_zE]

theorem mk_conj_mk_inv (g v : adjointGroup .G2 K) (i : ℕ) :
    (mk g i : MulAut (adjointGroup .G2 K)) * MulAut.conj v * (mk g i)⁻¹ =
      MulAut.conj (g * (phi ^ i : MulAut (adjointGroup .G2 K)) v * g⁻¹) := by
  unfold mk
  have h := phi_pow_mul_conj v i
  calc MulAut.conj g * phi ^ i * MulAut.conj v * (MulAut.conj g * phi ^ i)⁻¹
      = MulAut.conj g * (phi ^ i * MulAut.conj v) * (phi ^ i)⁻¹ * (MulAut.conj g)⁻¹ := by group
    _ = MulAut.conj g * (MulAut.conj ((phi ^ i : MulAut (adjointGroup .G2 K)) v) * phi ^ i) *
          (phi ^ i)⁻¹ * (MulAut.conj g)⁻¹ := by rw [h]
    _ = MulAut.conj g * MulAut.conj ((phi ^ i : MulAut (adjointGroup .G2 K)) v) *
          (MulAut.conj g)⁻¹ := by group
    _ = MulAut.conj (g * (phi ^ i : MulAut (adjointGroup .G2 K)) v * g⁻¹) := by
      simp [map_mul, map_inv]

@[expose] noncomputable def NA : Subgroup (MulAut (adjointGroup .G2 K)) :=
  Subgroup.normalizer (Subgroup.zpowers (zb M) : Set (MulAut (adjointGroup .G2 K)))

theorem mk_mem_NA {g : adjointGroup .G2 K} (hg : g ∈ SX M) (i : ℕ) : mk g i ∈ NA M := by
  apply mem_normalizer_of_conj_le
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have e : (mk g i : MulAut (adjointGroup .G2 K)) * zb M ^ k * (mk g i)⁻¹ =
      ((mk g i : MulAut (adjointGroup .G2 K)) * zb M * (mk g i)⁻¹) ^ k := by rw [conj_zpow]
  rw [e]
  apply Subgroup.zpow_mem
  have h1 : (mk g i : MulAut (adjointGroup .G2 K)) * zb M * (mk g i)⁻¹ =
      MulAut.conj (g * zE M * g⁻¹) := by
    have := mk_conj_mk_inv g (zE M) i
    rw [phi_pow_zE] at this
    exact this
  rw [h1]
  have hg' : g * zE M * g⁻¹ ∈ Subgroup.zpowers (zE M) :=
    (Subgroup.mem_normalizer_iff.mp hg (zE M)).mp (Subgroup.mem_zpowers _)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hg'
  rw [← hj, map_zpow]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) j

theorem exists_mk_of_mem_NA (hK : Nat.card K = 8) {α : MulAut (adjointGroup .G2 K)}
    (hα : α ∈ NA M) : ∃ g ∈ SX M, ∃ i < 3, α = mk g i := by
  obtain ⟨g, i, hi, rfl⟩ := exists_mk hK α
  refine ⟨g, ?_, i, hi, rfl⟩
  have h := (Subgroup.mem_normalizer_iff.mp hα (zb M)).mp (Subgroup.mem_zpowers _)
  have h1 : (mk g i : MulAut (adjointGroup .G2 K)) * zb M * (mk g i)⁻¹ =
      MulAut.conj (g * zE M * g⁻¹) := by
    have := mk_conj_mk_inv g (zE M) i
    rw [phi_pow_zE] at this
    exact this
  rw [h1] at h
  have hg : g * zE M * g⁻¹ ∈ Subgroup.zpowers (zE M) := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨j, conj_injective_X ?_⟩
    rw [map_zpow]
    exact hj
  apply mem_normalizer_of_conj_le
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [show g * zE M ^ k * g⁻¹ = (g * zE M * g⁻¹) ^ k by rw [conj_zpow]]
  exact Subgroup.zpow_mem _ hg k

theorem phi_mem_NA : (phi : MulAut (adjointGroup .G2 K)) ∈ NA M := by
  have := mk_mem_NA M (g := 1) ((SX M).one_mem) 1
  simpa [mk] using this

theorem conj_mem_NA {g : adjointGroup .G2 K} (hg : g ∈ SX M) :
    (MulAut.conj g : MulAut (adjointGroup .G2 K)) ∈ NA M := by
  have := mk_mem_NA M hg 0
  simpa [mk] using this

theorem NA_le (hK : Nat.card K = 8) (hPS : PX M = SX M)
    {Y₀ : Subgroup (MulAut (adjointGroup .G2 K))} (hweak : GLBWeakCore 3 (T0 M hK) ≤ Y₀) :
    NA M ≤ Y₀ := by
  intro α hα
  obtain ⟨g, hg, i, hi, rfl⟩ := exists_mk_of_mem_NA M hK hα
  have hconj : (MulAut.conj g : MulAut (adjointGroup .G2 K)) ∈ Y₀ := by
    have hle : (PX M).map
        (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) ≤ Y₀ := by
      unfold PX
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact hweak (conj_gElt_mem_weakCore M hK hj)
    exact hle ⟨g, hPS ▸ hg, rfl⟩
  have hphi : (phi : MulAut (adjointGroup .G2 K)) ^ i ∈ Y₀ :=
    Subgroup.pow_mem _ (hweak (phi_mem_weakCore M hK)) i
  exact Subgroup.mul_mem _ hconj hphi

theorem NA_maximal (hmax : ∀ H : Subgroup (adjointGroup .G2 K), SX M ≤ H → H = SX M ∨ H = ⊤)
    (hK : Nat.card K = 8) (H : Subgroup (MulAut (adjointGroup .G2 K))) (hNH : NA M ≤ H) :
    H = NA M ∨ H = ⊤ := by
  let c : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K) := MulAut.conj
  have hS : SX M ≤ H.comap c := fun g hg => hNH (conj_mem_NA M hg)
  have hphi : (phi : MulAut (adjointGroup .G2 K)) ∈ H := hNH (phi_mem_NA M)
  rcases hmax (H.comap c) hS with h | h
  · left
    refine le_antisymm (fun α hα => ?_) hNH
    obtain ⟨g, i, hi, rfl⟩ := exists_mk hK α
    have hc : MulAut.conj g ∈ H := by
      have : mk g i * (phi ^ i : MulAut (adjointGroup .G2 K))⁻¹ = MulAut.conj g := by
        simp [mk]
      rw [← this]
      exact Subgroup.mul_mem _ hα (Subgroup.inv_mem _ (Subgroup.pow_mem _ hphi i))
    have hg : g ∈ SX M := by
      rw [← h]
      exact hc
    exact mk_mem_NA M hg i
  · right
    rw [eq_top_iff]
    intro α _
    obtain ⟨g, i, hi, rfl⟩ := exists_mk hK α
    have hc : MulAut.conj g ∈ H := by
      have : g ∈ H.comap c := by rw [h]; exact Subgroup.mem_top g
      exact this
    exact Subgroup.mul_mem _ hc (Subgroup.pow_mem _ hphi i)

@[expose] noncomputable def V0 : Subgroup (MulAut (adjointGroup .G2 K)) :=
  (VX M).map (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K))

theorem V0_le_NA : V0 M ≤ NA M := by
  rintro _ ⟨v, hv, rfl⟩
  exact conj_mem_NA M (VX_le_SX M hv)

theorem zE_mem_VX : zE M ∈ VX M := by
  rw [mem_VX_iff]
  unfold Cen
  group

theorem zb_mem_V0 : zb M ∈ V0 M := ⟨zE M, zE_mem_VX M, rfl⟩

theorem cen_phi_pow {v : adjointGroup .G2 K} (hv : Cen M v) (i : ℕ) :
    Cen M ((phi ^ i : MulAut (adjointGroup .G2 K)) v) := by
  unfold Cen at *
  have := congrArg (fun w => (phi ^ i : MulAut (adjointGroup .G2 K)) w) hv
  simpa [map_mul, map_inv, phi_pow_zE] using this

theorem NA_le_normalizer_V0 (hK : Nat.card K = 8) :
    NA M ≤ Subgroup.normalizer (V0 M : Set (MulAut (adjointGroup .G2 K))) := by
  intro α hα
  obtain ⟨g, hg, i, hi, rfl⟩ := exists_mk_of_mem_NA M hK hα
  apply mem_normalizer_of_conj_le
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨g * (phi ^ i : MulAut (adjointGroup .G2 K)) v * g⁻¹, ?_, ?_⟩
  · have hv' : Cen M v := (mem_VX_iff M).mp hv
    have h1 := cen_phi_pow M hv' i
    show _ ∈ VX M
    rw [mem_VX_iff]
    rcases cen_or_inv M hg with h | h
    · exact (h.mul h1).mul h.inv'
    · exact (h.mul_cen h1).mul_inv h.inv'
  · exact (mk_conj_mk_inv g v i).symm

theorem V0_perfect (hSU : SUStruct M) : ⁅V0 M, V0 M⁆ = V0 M := by
  unfold V0
  rw [← Subgroup.map_commutator, hSU.1]

theorem V0_onto (hSU : SUStruct M) : ∃ (d : TauCeti.ValidLieTypeIndex) (ψ : V0 M →* CatGroup d),
    IsUThreeEightIndex d ∧ Function.Surjective ψ := by
  obtain ⟨d, ψ, hd, hψ⟩ := hSU.2.2.2.1
  have hinj : Function.Injective
      (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) := conj_injective_X
  let e := (Subgroup.equivMapOfInjective (VX M)
    (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) hinj).symm
  exact ⟨d, ψ.comp e.toMonoidHom, hd, hψ.comp e.surjective⟩

theorem comm_of_commutator_bot {A : Type*} [Group A] {W V : Subgroup A} (h : ⁅W, V⁆ = ⊥) {w v : A}
    (hw : w ∈ W) (hv : v ∈ V) : v * w = w * v := by
  have h1 := Subgroup.commutator_mem_commutator hw hv
  rw [h, Subgroup.mem_bot, commutatorElement_def] at h1
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1)).symm

theorem zb_comm_V0 : ∀ v ∈ V0 M, zb M * v = v * zb M := by
  rintro _ ⟨v, hv, rfl⟩
  have hc : Cen M v := (mem_VX_iff M).mp hv
  have h1 : zE M * v = v * zE M := by
    unfold Cen at hc
    calc zE M * v = (v * zE M * v⁻¹) * v := by rw [hc]
      _ = v * zE M := by group
  show MulAut.conj (zE M) * MulAut.conj v = MulAut.conj v * MulAut.conj (zE M)
  rw [← map_mul, ← map_mul, h1]

theorem V0_simple (hSU : SUStruct M) :
    ∀ U : Subgroup (MulAut (adjointGroup .G2 K)), U ≤ V0 M →
      V0 M ≤ Subgroup.normalizer (U : Set (MulAut (adjointGroup .G2 K))) →
      U = ⊥ ∨ U ≤ Subgroup.zpowers (zb M) ∨ U = V0 M :=
  simple_map (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)) conj_injective_X
    hSU.2.1

theorem V0_quasi (hK : Nat.card K = 8) (hSU : SUStruct M)
    (W : Subgroup (MulAut (adjointGroup .G2 K))) (hW : W ≤ NA M)
    (hN : V0 M ≤ Subgroup.normalizer (W : Set (MulAut (adjointGroup .G2 K)))) :
    V0 M ≤ W ∨ ⁅W, V0 M⁆ = ⊥ :=
  quasi_of_simple (V0_perfect M hSU) (zb_comm_V0 M) (V0_simple M hSU) (NA_le_normalizer_V0 M hK)
    hW hN

theorem trace_rho_conj (g : adjointGroup .G2 K) (Z : Matrix (Fin 6) (Fin 6) GF8) :
    Matrix.trace (M.rho g * Z * M.rho g⁻¹) = Matrix.trace Z := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, rho_inv_mul, one_mul]

theorem trace_frobM (A : Matrix (Fin 6) (Fin 6) GF8) :
    Matrix.trace (frobM A) = (Matrix.trace A) ^ 2 := by
  show ∑ i, frobGF8 (A i i) = (∑ i, A i i) ^ 2
  rw [← map_sum]
  rfl

theorem V0_centralizer (hK : Nat.card K = 8) (hSU : SUStruct M) :
    NA M ⊓ Subgroup.centralizer (V0 M : Set (MulAut (adjointGroup .G2 K))) ≤
      Subgroup.zpowers (zb M) := by
  rintro α ⟨hα, hαC⟩
  obtain ⟨g, hg, i, hi, rfl⟩ := exists_mk_of_mem_NA M hK hα
  have hcomm : ∀ v ∈ VX M, g * (phi ^ i : MulAut (adjointGroup .G2 K)) v * g⁻¹ = v := by
    intro v hv
    have h1 := Subgroup.mem_centralizer_iff.mp hαC (MulAut.conj v) ⟨v, hv, rfl⟩
    have h2 := mk_conj_mk_inv g v i
    rw [← h1, mul_inv_cancel_right] at h2
    exact conj_injective_X h2.symm
  obtain ⟨v, hv, h2, h4⟩ := hSU.2.2.2.2
  have htr : ∀ j : ℕ, j = i → Matrix.trace (M.rho v) =
      Matrix.trace (M.rho ((phi ^ j : MulAut (adjointGroup .G2 K)) v)) := by
    intro j hj
    subst hj
    have e := congrArg M.rho (hcomm v hv)
    rw [map_mul, map_mul] at e
    have := trace_rho_conj M g (M.rho ((phi ^ j : MulAut (adjointGroup .G2 K)) v))
    rw [e] at this
    exact this
  have hphi1 : ∀ w : adjointGroup .G2 K, M.rho ((phi ^ 1 : MulAut (adjointGroup .G2 K)) w) =
      frobM (M.rho w) := fun w => by rw [pow_one]; exact rho_phi M w
  have hphi2 : ∀ w : adjointGroup .G2 K, M.rho ((phi ^ 2 : MulAut (adjointGroup .G2 K)) w) =
      frobM (frobM (M.rho w)) := fun w => by
    rw [pow_two, MulAut.mul_apply, rho_phi, rho_phi]
  have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi3 with rfl | rfl | rfl
  ·
    have hz := hcomm (zE M) (zE_mem_VX M)
    simp only [pow_zero, MulAut.one_apply] at hz hcomm
    have hcen : Cen M g := by
      unfold Cen
      have : g * zE M = zE M * g := by
        calc g * zE M = (g * zE M * g⁻¹) * g := by group
          _ = zE M * g := by rw [hz]
      calc g * zE M * g⁻¹ = zE M * g * g⁻¹ := by rw [this]
        _ = zE M := by group
    have hgV : g ∈ VX M := (mem_VX_iff M).mpr hcen
    have hgC : g ∈ Subgroup.centralizer (VX M : Set (adjointGroup .G2 K)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have := hcomm v hv
      calc v * g = (g * v * g⁻¹) * g := by rw [this]
        _ = g * v := by group
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hSU.2.2.1 ⟨hgV, hgC⟩)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← hk]
    simp [mk, zb, map_zpow]
  ·
    exfalso
    have := htr 1 rfl
    rw [hphi1, trace_frobM] at this
    exact h2 this.symm
  ·
    exfalso
    have := htr 2 rfl
    rw [hphi2, trace_frobM, trace_frobM] at this
    exact h4 (by rw [show (M.rho v).trace ^ 4 = ((M.rho v).trace ^ 2) ^ 2 by ring]; exact this.symm)

theorem g28InSitu_aut (hK : Nat.card K = 8) (hSU : SUStruct M)
    {Y₀ : Subgroup (MulAut (adjointGroup .G2 K))} (hweak : GLBWeakCore 3 (T0 M hK) ≤ Y₀)
    (hne : Y₀ ≠ ⊤) : G28InSitu (T0 M hK) Y₀ (zb M) (V0 M) := by
  obtain ⟨hPS, -, hmax⟩ := omega_facts M hK
  have hY : Y₀ = NA M := by
    rcases NA_maximal M hmax hK Y₀ (NA_le M hK hPS hweak) with h | h
    · exact h
    · exact absurd h hne
  subst hY
  have hVN := NA_le_normalizer_V0 M hK
  have hqu : ∀ W : Subgroup (MulAut (adjointGroup .G2 K)), W ≤ NA M →
      V0 M ≤ Subgroup.normalizer (W : Set (MulAut (adjointGroup .G2 K))) →
      V0 M ≤ W ∨ ⁅W, V0 M⁆ = ⊥ := fun W hW hN => V0_quasi M hK hSU W hW hN
  refine ⟨zb_mem_T0 M hK, ?_, orderOf_zb M, center_T0_le M hK, card_T0 M hK, V0_le_NA M,
    V0_perfect M hSU, hVN, zb_mem_V0 M, V0_onto M hSU, hqu, V0_centralizer M hK hSU, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact zb_comm_T0 M hK hh
  · intro W hW hWN
    rcases hqu W hW (fun v hv => hWN (V0_le_NA M hv)) with h | h
    · exact Or.inr (Or.inr h)
    · right
      left
      intro w hw
      apply V0_centralizer M hK hSU
      exact ⟨hW hw, Subgroup.mem_centralizer_iff.mpr
        (fun v hv => comm_of_commutator_bot h hw hv)⟩

end InSitu

end CFSG.AGLEmbedding.KFactProofs.G28
