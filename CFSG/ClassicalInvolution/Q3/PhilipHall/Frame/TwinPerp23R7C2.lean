module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E8

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7Y

variable {Q : Type} [Group Q] [Finite Q] {A B : Subgroup Q} {z : Q}

theorem eq_of_comm_q8 (hz : ∀ q : Q, q * z = z * q) (hsA : IsUniqueInvolution A z)
    (h8A : Nat.card A = 8) (hnabA : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) {w : Q} (hw : w ∈ A)
    (hc : ∀ y ∈ A, y * w = w * y) : w = 1 ∨ w = z :=
  F7E.mem_inf_q8 (B := Subgroup.centralizer (A : Set Q)) hz hsA h8A hnabA
    (fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy x hx) hw
    (Subgroup.mem_centralizer_iff.mpr fun y hy => hc y hy)

theorem eq_of_comm_sup (hz : ∀ q : Q, q * z = z * q) (hsA : IsUniqueInvolution A z)
    (hsB : IsUniqueInvolution B z) (h8A : Nat.card A = 8) (h8B : Nat.card B = 8)
    (hnabA : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x) (hnabB : ∃ x ∈ B, ∃ y ∈ B, x * y ≠ y * x)
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) {w : Q} (hw : w ∈ A ⊔ B)
    (hc : ∀ y ∈ A ⊔ B, y * w = w * y) : w = 1 ∨ w = z := by
  have hAN : A ≤ Subgroup.normalizer (B : Set Q) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hcomm a ha b hb, mul_inv_cancel_right]
      exact hb
    · intro hb
      have h := hcomm a⁻¹ (A.inv_mem ha) _ hb
      have e1 : b = a⁻¹ * (a * b * a⁻¹) * a := by group
      rw [e1, h, inv_mul_cancel_right]
      exact hb
  have hw' : w ∈ ((A ⊔ B : Subgroup Q) : Set Q) := hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hAN] at hw'
  obtain ⟨a, ha, b, hb, rfl⟩ := hw'
  have hcA : ∀ y ∈ A, y * a = a * y := by
    intro y hy
    have h1 := hc y (Subgroup.mem_sup_left hy)
    have h2 := hcomm y hy b hb
    apply mul_right_cancel (b := b)
    calc y * a * b = y * (a * b) := by group
      _ = a * b * y := h1
      _ = a * (b * y) := by group
      _ = a * (y * b) := by rw [h2]
      _ = a * y * b := by group
  have hcB : ∀ y ∈ B, y * b = b * y := by
    intro y hy
    have h1 := hc y (Subgroup.mem_sup_right hy)
    have h2 := hcomm a ha y hy
    apply mul_left_cancel (a := a)
    calc a * (y * b) = (a * y) * b := by group
      _ = (y * a) * b := by rw [h2]
      _ = y * (a * b) := by group
      _ = a * b * y := h1
      _ = a * (b * y) := by group
  rcases eq_of_comm_q8 hz hsA h8A hnabA ha hcA with rfl | rfl <;>
    rcases eq_of_comm_q8 hz hsB h8B hnabB hb hcB with rfl | rfl
  · left; group
  · right; group
  · right; group
  · left; exact hsA.sq

end F7Y

section Steps

variable {n : ℕ}

section Facts

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_conj_e_mod_t (hc : P23Cfg n Y R S t K' W u e g) {C : Subgroup Y}
    (hCdef : C = Subgroup.centralizer ({t} : Set Y)) {x : Y} (hxC : x ∈ C) (htC : t ∈ C) (heC : e ∈ C)
    (hxeC : x * e * x⁻¹ ∈ C) (hxW : x * (u * e) * x⁻¹ ∈ W) :
    F7I.piC C ⟨x * e * x⁻¹, hxeC⟩ = F7I.piC C ⟨e, heC⟩ ∨
      F7I.piC C ⟨x * e * x⁻¹, hxeC⟩ = F7I.piC C ⟨t, htC⟩ * F7I.piC C ⟨e, heC⟩ := by
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hd.hW
  have hz' : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have cue : u * e = e * u := T7K.comm_e_of_mem_W hd hd.huW
  have cte : t * e = e * t := T7K.comm_e_of_mem_W hd hd.hzW
  have hmemC : ∀ c : Y, c ∈ C ↔ c * t = t * c := fun c => by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff]
  have hxt : x * t = t * x := (hmemC x).mp hxC
  have hxC' : x ∈ Subgroup.centralizer ({t} : Set Y) := Subgroup.mem_centralizer_singleton_iff.mpr hxt
  have hWt : W ≤ C := fun w hw => (hmemC w).mpr (hWab w hw t hd.hzW)
  have huC : u ∈ C := hWt hd.huW
  have hbackW : ∀ {a b : Y} (ha : a ∈ W) (hb : b ∈ W),
      F7I.piC C ⟨a, hWt ha⟩ = F7I.piC C ⟨b, hWt hb⟩ → a = b :=
    fun ha hb h => congrArg Subtype.val (F7I.piC_inj hW2 ha hb h)
  obtain ⟨hsA, hsB, h8A, h8B, nA, nB, hcommAB, heA, heB, b₁, b', hub, hb₁, hb', -, -, -, -⟩ :=
    p23_twin_q8 hc hCdef htC heC
  have hz : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C,
      q * F7I.piC C ⟨t, htC⟩ = F7I.piC C ⟨t, htC⟩ * q := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    change F7I.piC C c * _ = _ * F7I.piC C c
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext ((hmemC _).mp c.2))
  have hXA : (conjSub (F7I.piC C ⟨x, hxC⟩) (((tightCore R).subgroupOf C).map (F7I.piC C)) =
          ((tightCore R).subgroupOf C).map (F7I.piC C) ∧
        conjSub (F7I.piC C ⟨x, hxC⟩) ((K'.subgroupOf C).map (F7I.piC C)) =
          (K'.subgroupOf C).map (F7I.piC C)) ∨
      (conjSub (F7I.piC C ⟨x, hxC⟩) (((tightCore R).subgroupOf C).map (F7I.piC C)) =
          (K'.subgroupOf C).map (F7I.piC C) ∧
        conjSub (F7I.piC C ⟨x, hxC⟩) ((K'.subgroupOf C).map (F7I.piC C)) =
          ((tightCore R).subgroupOf C).map (F7I.piC C)) := by
    rw [F7I.conjSub_map_piC, F7I.conjSub_map_piC]
    rcases p23_conj_twins hc hxC' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
  have hu' : (⟨u, huC⟩ : ↥C) = b₁ * b' := Subtype.ext hub.symm
  obtain ⟨X, hX⟩ : ∃ X, F7I.piC C ⟨x, hxC⟩ = X := ⟨_, rfl⟩
  obtain ⟨E₀, hE₀⟩ : ∃ E₀, F7I.piC C ⟨e, heC⟩ = E₀ := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, F7I.piC C ⟨u, huC⟩ = U := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, F7I.piC C ⟨t, htC⟩ = T := ⟨_, rfl⟩
  rw [hX] at hXA
  rw [hT] at hsA hsB hz
  rw [hE₀] at heA heB
  have hUb : U = F7I.piC C b₁ * F7I.piC C b' := by rw [← hU, hu', map_mul]
  set A := ((tightCore R).subgroupOf C).map (F7I.piC C) with hAdef
  set B := (K'.subgroupOf C).map (F7I.piC C) with hBdef
  have hcenter : ∀ {w : ↥C ⧸ classicalInvolutionOddCore ↥C}, w ∈ A ⊔ B →
      (∀ y ∈ A ⊔ B, y * w = w * y) → w = 1 ∨ w = T :=
    fun hw hc' => F7Y.eq_of_comm_sup hz hsA hsB h8A h8B nA nB hcommAB hw hc'
  have hXAB : conjSub X (A ⊔ B) = A ⊔ B := by
    rw [Sec13.L94T.conjSub_sup_eq]
    rcases hXA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  have hconjAB : ∀ y ∈ A ⊔ B, X * y * X⁻¹ ∈ A ⊔ B := by
    intro y hy
    rw [← hXAB, mem_conjSub_iff]
    have e1 : X⁻¹ * (X * y * X⁻¹) * X = y := by group
    rw [e1]
    exact hy
  have hconjAB' : ∀ y ∈ A ⊔ B, X⁻¹ * y * X ∈ A ⊔ B := by
    intro y hy
    rw [← hXAB, mem_conjSub_iff] at hy
    exact hy
  have hcmul : ∀ c d : ↥C ⧸ classicalInvolutionOddCore ↥C, (∀ y ∈ A ⊔ B, y * c = c * y) →
      (∀ y ∈ A ⊔ B, y * d = d * y) → ∀ y ∈ A ⊔ B, y * (c * d) = (c * d) * y := by
    intro c d hc' hd' y hy
    calc y * (c * d) = (y * c) * d := by group
      _ = (c * y) * d := by rw [hc' y hy]
      _ = c * (y * d) := by group
      _ = c * (d * y) := by rw [hd' y hy]
      _ = (c * d) * y := by group
  have hcinv : ∀ c : ↥C ⧸ classicalInvolutionOddCore ↥C, (∀ y ∈ A ⊔ B, y * c = c * y) →
      ∀ y ∈ A ⊔ B, y * c⁻¹ = c⁻¹ * y := by
    intro c hc' y hy
    calc y * c⁻¹ = c⁻¹ * (c * y) * c⁻¹ := by group
      _ = c⁻¹ * (y * c) * c⁻¹ := by rw [hc' y hy]
      _ = c⁻¹ * y := by group
  have hcE₀ : ∀ y ∈ A ⊔ B, y * E₀ = E₀ * y := by
    intro y hy
    have hle : A ⊔ B ≤ Subgroup.centralizer ({E₀} : Set (↥C ⧸ classicalInvolutionOddCore ↥C)) :=
      sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (heA a ha).symm)
        (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (heB a ha).symm)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hcE₁ : ∀ y ∈ A ⊔ B, y * (X * E₀ * X⁻¹) = (X * E₀ * X⁻¹) * y := by
    intro y hy
    have h := hcE₀ _ (hconjAB' y hy)
    calc y * (X * E₀ * X⁻¹) = X * ((X⁻¹ * y * X) * E₀) * X⁻¹ := by group
      _ = X * (E₀ * (X⁻¹ * y * X)) * X⁻¹ := by rw [h]
      _ = (X * E₀ * X⁻¹) * y := by group
  have hU1 : U ∈ A ⊔ B := by
    rw [hUb]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hb₁) (Subgroup.mem_sup_right hb')
  have hT1 : T ∈ A ⊔ B := Subgroup.mem_sup_left hsA.mem
  have hcS : ∀ S : ↥C ⧸ classicalInvolutionOddCore ↥C, (S = 1 ∨ S = T) →
      ∀ y ∈ A ⊔ B, y * S = S * y := by
    rintro S (rfl | rfl) y _
    · group
    · exact hz y
  have hE₁ : F7I.piC C ⟨x * e * x⁻¹, hxeC⟩ = X * E₀ * X⁻¹ := by
    rw [← hX, ← hE₀]
    show F7I.piC C (⟨x, hxC⟩ * ⟨e, heC⟩ * (⟨x, hxC⟩)⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hkey : ∀ s : ↥C, x * (u * e) * x⁻¹ = (s : Y) → X * (U * E₀) * X⁻¹ = F7I.piC C s := by
    intro s h
    have h' : (⟨x, hxC⟩ : ↥C) * (⟨u, huC⟩ * ⟨e, heC⟩) * (⟨x, hxC⟩)⁻¹ = s := Subtype.ext h
    have h2 := congrArg (F7I.piC C) h'
    simp only [map_mul, map_inv] at h2
    rw [hX, hU, hE₀] at h2
    exact h2
  have hI : ∀ S, S ∈ A ⊔ B → X * (U * E₀) * X⁻¹ = S → False := by
    intro S hS h
    have e1 : X * E₀ * X⁻¹ = (X * U * X⁻¹)⁻¹ * S := by rw [← h]; group
    have hmem : X * E₀ * X⁻¹ ∈ A ⊔ B := by
      rw [e1]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hconjAB U hU1)) hS
    rcases hcenter hmem hcE₁ with h1 | h1
    · have h2 : E₀ = 1 := by
        calc E₀ = X⁻¹ * (X * E₀ * X⁻¹) * X := by group
          _ = 1 := by rw [h1]; group
      apply hd.he1
      exact hbackW heW W.one_mem (by rw [hE₀, h2]; exact (map_one _).symm)
    · have h2 : E₀ = T := by
        calc E₀ = X⁻¹ * (X * E₀ * X⁻¹) * X := by group
          _ = X⁻¹ * T * X := by rw [h1]
          _ = T := by rw [hz X⁻¹, inv_mul_cancel_right]
      have het : e = t := hbackW heW hd.hzW (by rw [hE₀, h2, ← hT])
      exact e_not_mem_sup hc (het ▸ Subgroup.mem_sup_left hz'.mem)
  have hII : ∀ S, (S = 1 ∨ S = T) → X * (U * E₀) * X⁻¹ = S * E₀ → False := by
    intro S hS h
    have e1 : X * U * X⁻¹ = S * E₀ * (X * E₀ * X⁻¹)⁻¹ := by
      calc X * U * X⁻¹ = (X * (U * E₀) * X⁻¹) * (X * E₀ * X⁻¹)⁻¹ := by group
        _ = S * E₀ * (X * E₀ * X⁻¹)⁻¹ := by rw [h]
    have hcV : ∀ y ∈ A ⊔ B, y * (X * U * X⁻¹) = (X * U * X⁻¹) * y := by
      rw [e1]
      exact hcmul _ _ (hcmul _ _ (hcS S hS) hcE₀) (hcinv _ hcE₁)
    have hUX : U = X⁻¹ * (X * U * X⁻¹) * X := by group
    rcases hcenter (hconjAB U hU1) hcV with h1 | h1
    · apply hd.hu1
      refine hbackW hd.huW W.one_mem ?_
      rw [hU, hUX, h1]
      calc X⁻¹ * 1 * X = 1 := by group
        _ = F7I.piC C 1 := (map_one _).symm
    · apply hd.huz
      refine hbackW hd.huW hd.hzW ?_
      rw [hU, hUX, h1, hz X⁻¹, inv_mul_cancel_right, ← hT]
  have hIII : ∀ S, (S = 1 ∨ S = T) → X * (U * E₀) * X⁻¹ = U * S * E₀ →
      F7I.piC C ⟨x * e * x⁻¹, hxeC⟩ = F7I.piC C ⟨e, heC⟩ ∨
        F7I.piC C ⟨x * e * x⁻¹, hxeC⟩ = F7I.piC C ⟨t, htC⟩ * F7I.piC C ⟨e, heC⟩ := by
    intro S hS h
    have hcc : ∀ y ∈ A ⊔ B, y * (S * E₀ * (X * E₀ * X⁻¹)⁻¹) = (S * E₀ * (X * E₀ * X⁻¹)⁻¹) * y :=
      hcmul _ _ (hcmul _ _ (hcS S hS) hcE₀) (hcinv _ hcE₁)
    have e1 : X * U * X⁻¹ * U⁻¹ = S * E₀ * (X * E₀ * X⁻¹)⁻¹ := by
      calc X * U * X⁻¹ * U⁻¹ = (X * (U * E₀) * X⁻¹) * (X * E₀ * X⁻¹)⁻¹ * U⁻¹ := by group
        _ = U * S * E₀ * (X * E₀ * X⁻¹)⁻¹ * U⁻¹ := by rw [h]
        _ = U * (S * E₀ * (X * E₀ * X⁻¹)⁻¹) * U⁻¹ := by group
        _ = (S * E₀ * (X * E₀ * X⁻¹)⁻¹) * U * U⁻¹ := by rw [hcc U hU1]
        _ = S * E₀ * (X * E₀ * X⁻¹)⁻¹ := by group
    have hw : X * U * X⁻¹ * U⁻¹ ∈ A ⊔ B :=
      Subgroup.mul_mem _ (hconjAB U hU1) (Subgroup.inv_mem _ hU1)
    have hc1 := hcenter hw (by rw [e1]; exact hcc)
    rw [e1] at hc1
    have hT2 : T * T = 1 := hsA.sq
    have hTi : T⁻¹ = T := inv_eq_of_mul_eq_one_right hT2
    obtain ⟨D, hD, hDE⟩ : ∃ D, (D = 1 ∨ D = T) ∧ X * E₀ * X⁻¹ = D * E₀ := by
      refine ⟨(S * E₀ * (X * E₀ * X⁻¹)⁻¹)⁻¹ * S, ?_, by group⟩
      rcases hc1 with h1 | h1 <;> rw [h1] <;> rcases hS with rfl | rfl
      · left; group
      · right; group
      · right; rw [hTi]; group
      · left; rw [hTi]; exact hT2
    rcases hD with rfl | rfl
    · left
      rw [hE₁, hDE, one_mul, hE₀]
    · right
      rw [hE₁, hDE, hT, hE₀]
  have hue2 : u * e * (u * e) = 1 := by
    calc u * e * (u * e) = u * (e * u) * e := by group
      _ = u * (u * e) * e := by rw [cue]
      _ = (u * u) * (e * e) := by group
      _ = 1 := by rw [hd.hu2, hd.he2, one_mul]
  have ha2 : x * (u * e) * x⁻¹ * (x * (u * e) * x⁻¹) = 1 := by
    calc x * (u * e) * x⁻¹ * (x * (u * e) * x⁻¹) = x * (u * e * (u * e)) * x⁻¹ := by group
      _ = 1 := by rw [hue2]; group
  have hwB := mem_B_of_involution hc hxW ha2
  rcases T7K.mem_cases_of_commuting_involutions hd.hu2 hz'.sq hd.he2 (comm_ut hc) cue cte hwB with
    h | h | h | h | h | h | h | h
  · exact (hI 1 (Subgroup.one_mem _) (by rw [hkey 1 h, map_one])).elim
  · exact (hI T hT1 (by rw [hkey ⟨t, htC⟩ h, hT])).elim
  · exact (hI U hU1 (by rw [hkey ⟨u, huC⟩ h, hU])).elim
  · exact (hI (U * T) (Subgroup.mul_mem _ hU1 hT1)
      (by rw [hkey (⟨u, huC⟩ * ⟨t, htC⟩) h, map_mul, hU, hT])).elim
  · exact (hII 1 (Or.inl rfl) (by rw [hkey ⟨e, heC⟩ h, hE₀, one_mul])).elim
  · exact (hII T (Or.inr rfl) (by rw [hkey (⟨t, htC⟩ * ⟨e, heC⟩) h, map_mul, hT, hE₀])).elim
  · exact hIII 1 (Or.inl rfl) (by rw [hkey (⟨u, huC⟩ * ⟨e, heC⟩) h, map_mul, hU, hE₀, mul_one])
  · exact hIII T (Or.inr rfl)
      (by rw [hkey (⟨u, huC⟩ * ⟨t, htC⟩ * ⟨e, heC⟩) h, map_mul, map_mul, hU, hT, hE₀])

end Facts

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
