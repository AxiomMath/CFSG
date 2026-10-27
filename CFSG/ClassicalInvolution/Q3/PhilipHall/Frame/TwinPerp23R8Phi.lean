module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E8
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8Z
import CFSG.ClassicalInvolution.Asc77.AscT8YC6
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R56Zstar

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7I

variable {Q : Type} [Group Q]

theorem conj_comm_of_cent [Finite Q] {A B : Subgroup Q} {eb : Q}
    (hperm : ∀ q : Q, (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A))
    (heA : ∀ x ∈ A, eb * x = x * eb) (heB : ∀ x ∈ B, eb * x = x * eb)
    (hMB : ∀ m : Q, (∀ x ∈ A, m * x = x * m) → (∀ x ∈ B, m * x = x * m) → m * eb = eb * m)
    (γ δ : Q) : (γ * eb * γ⁻¹) * (δ * eb * δ⁻¹) = (δ * eb * δ⁻¹) * (γ * eb * γ⁻¹) := by
  have hcent : ∀ ρ : Q, (∀ x ∈ A, ρ * eb * ρ⁻¹ * x = x * (ρ * eb * ρ⁻¹)) ∧
      (∀ x ∈ B, ρ * eb * ρ⁻¹ * x = x * (ρ * eb * ρ⁻¹)) := by
    intro ρ
    have key : ∀ x : Q, (ρ⁻¹ * x * ρ ∈ A ∨ ρ⁻¹ * x * ρ ∈ B) →
        ρ * eb * ρ⁻¹ * x = x * (ρ * eb * ρ⁻¹) := by
      intro x hx
      have h1 : eb * (ρ⁻¹ * x * ρ) = (ρ⁻¹ * x * ρ) * eb := by
        rcases hx with hx | hx
        · exact heA _ hx
        · exact heB _ hx
      calc ρ * eb * ρ⁻¹ * x = ρ * (eb * (ρ⁻¹ * x * ρ)) * ρ⁻¹ := by group
        _ = ρ * ((ρ⁻¹ * x * ρ) * eb) * ρ⁻¹ := by rw [h1]
        _ = x * (ρ * eb * ρ⁻¹) := by group
    have hmem : ∀ (H : Subgroup Q) (x : Q), x ∈ H → ρ⁻¹ * x * ρ ∈ conjSub ρ⁻¹ H := by
      intro H x hx
      rw [mem_conjSub_iff]
      have e : ρ⁻¹⁻¹ * (ρ⁻¹ * x * ρ) * ρ⁻¹ = x := by group
      rw [e]
      exact hx
    constructor
    · intro x hx
      apply key
      rcases hperm ρ⁻¹ with ⟨h1, -⟩ | ⟨h1, -⟩
      · left; rw [← h1]; exact hmem A x hx
      · right; rw [← h1]; exact hmem A x hx
    · intro x hx
      apply key
      rcases hperm ρ⁻¹ with ⟨-, h1⟩ | ⟨-, h1⟩
      · right; rw [← h1]; exact hmem B x hx
      · left; rw [← h1]; exact hmem B x hx
  have h := hMB _ (hcent (γ⁻¹ * δ)).1 (hcent (γ⁻¹ * δ)).2
  have h' := (F7E.conj_comm_iff γ ((γ⁻¹ * δ) * eb * (γ⁻¹ * δ)⁻¹) eb).mpr h
  have e : γ * ((γ⁻¹ * δ) * eb * (γ⁻¹ * δ)⁻¹) * γ⁻¹ = δ * eb * δ⁻¹ := by group
  rw [e] at h'
  exact h'.symm

theorem closure_comm {X : Set Q} (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    ∀ a ∈ Subgroup.closure X, ∀ b ∈ Subgroup.closure X, a * b = b * a := by
  have hc : X.Pairwise Commute := fun x hx y hy _ => hXc x hx y hy
  have hab := Subgroup.isMulCommutative_closure hc
  intro a ha b hb
  have := hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val this

theorem eq_one_of_odd_normalized [Finite Q]
    (hO : ∀ N : Subgroup Q, N.Normal → Odd (Nat.card N) → N = ⊥)
    {M P : Subgroup Q} (hMn : M.Normal) (hPodd : Odd (Nat.card P))
    (hMP : M ≤ Subgroup.normalizer (P : Set Q)) {d : Q} (hdP : d ∈ P) (hdM : d ∈ M) : d = 1 := by
  have hSodd : Odd (Nat.card ↥(P ⊓ M)) := Odd.of_dvd_nat hPodd (Subgroup.card_dvd_of_le inf_le_left)
  have hMS : M ≤ Subgroup.normalizer ((P ⊓ M : Subgroup Q) : Set Q) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hMP hm) h).mp h1,
        M.mul_mem (M.mul_mem hm h2) (M.inv_mem hm)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hMP hm) h).mpr h1, ?_⟩
      have := M.mul_mem (M.mul_mem (M.inv_mem hm) h2) hm
      have e : m⁻¹ * (m * h * m⁻¹) * m = h := by group
      rwa [e] at this
  have hSO : P ⊓ M ≤ oddCoreOf M :=
    AscFusion.le_oddCoreOf_of_normal_odd inf_le_right hMS hSodd
  have hON : (oddCoreOf M).Normal := by
    constructor
    intro x hx q
    have hqM : conjSub q M = M := by
      ext y
      rw [mem_conjSub_iff]
      constructor
      · intro hy
        have := hMn.conj_mem _ hy q
        have e : q * (q⁻¹ * y * q) * q⁻¹ = y := by group
        rwa [e] at this
      · intro hy
        have := hMn.conj_mem _ hy q⁻¹
        have e : q⁻¹ * y * q⁻¹⁻¹ = q⁻¹ * y * q := by group
        rwa [e] at this
    have := conj_mem_conjSub (n := q) hx
    rwa [← Thompson.oddCoreOf_conjSub_eq, hqM] at this
  have hbot := hO _ hON (oddCoreOf_odd_natCard M)
  have hd : d ∈ oddCoreOf M := hSO ⟨hdP, hdM⟩
  rw [hbot] at hd
  exact (Subgroup.mem_bot.mp hd)

theorem quot_odd_normal_eq_bot {Y : Type} [Group Y] [Finite Y] (C : Subgroup Y)
    (N : Subgroup (↥C ⧸ classicalInvolutionOddCore ↥C)) (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    N = ⊥ :=
  eq_bot_iff.mpr ((CFSG.ComponentClassification.OddCore.maximal _ N hN hodd).trans
    (CFSG.ComponentClassification.OddCore.quotient_corefree ↥C).le)

end F7I


section MBar

variable {n : ℕ}

@[expose] def P23MBar (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
      ∀ x : ↥(Subgroup.centralizer ({t} : Set Y)), (x : Y) = e → ∀ m : ↥(Subgroup.centralizer ({t} : Set Y)) ⧸ classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)),
        (∀ a ∈ ((tightCore R).subgroupOf (Subgroup.centralizer ({t} : Set Y))).map (F7I.piC (Subgroup.centralizer ({t} : Set Y))), m * a = a * m) →
        (∀ a ∈ (K'.subgroupOf (Subgroup.centralizer ({t} : Set Y))).map (F7I.piC (Subgroup.centralizer ({t} : Set Y))), m * a = a * m) →
        m * F7I.piC (Subgroup.centralizer ({t} : Set Y)) x = F7I.piC (Subgroup.centralizer ({t} : Set Y)) x * m

theorem p23E7MBar_of_mbar (hMB : P23MBar n) : P23E7MBar n :=
  fun hcit hP Y _ _ R S t K' W u e g hc _ _ hZ => hMB hcit hP Y R S t K' W u e g hc hZ

@[expose] def P23E8PhiAE (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → SecAE R u 5 → SecAE R e 6 →
        ∀ a ∈ p23ABar t 1 e, ∀ b ∈ p23ABar t 1 e, a * b = b * a

theorem p23E8Phi_of_steps (hT : Thm4RTwinBelow 3 n) (hMB : P23MBar n) (hAE : P23E8PhiAE n) :
    P23E8Phi n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hcase he6
  rcases hcase with hZ | hAE5
  swap
  · exact hAE hcit hP Y R S t K' W u e g hc hno hAE5 he6
  have hZ' := R56.p23_zstar_cu hT hc hZ
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hWt : W ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  have htC : t ∈ C := hWt hd.hzW
  have heC : e ∈ C := hWt heW
  obtain ⟨-, -, -, -, -, -, -, heA, heB, -⟩ := p23_twin_q8 hc hCdef htC heC
  have hperm : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (conjSub q (((tightCore R).subgroupOf C).map (F7I.piC C)) =
          ((tightCore R).subgroupOf C).map (F7I.piC C) ∧
        conjSub q ((K'.subgroupOf C).map (F7I.piC C)) = (K'.subgroupOf C).map (F7I.piC C)) ∨
      (conjSub q (((tightCore R).subgroupOf C).map (F7I.piC C)) =
          (K'.subgroupOf C).map (F7I.piC C) ∧
        conjSub q ((K'.subgroupOf C).map (F7I.piC C)) =
          ((tightCore R).subgroupOf C).map (F7I.piC C)) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    change (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _) ∨
      (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _)
    rw [F7I.conjSub_map_piC, F7I.conjSub_map_piC]
    rcases p23_conj_twins hc c.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
  have hMB' := hMB hcit hP Y R S t K' W u e g hc hZ' ⟨e, heC⟩ rfl
  have hcc := F7I.conj_comm_of_cent hperm heA heB hMB'
  apply F7I.closure_comm
  rintro _ ⟨x, ⟨c, hcC, hx⟩, rfl⟩ _ ⟨y, ⟨d, hdC, hy⟩, rfl⟩
  have ex : x = ⟨c, hcC⟩ * ⟨e, heC⟩ * ⟨c, hcC⟩⁻¹ := Subtype.ext (by rw [hx, one_mul]; rfl)
  have ey : y = ⟨d, hdC⟩ * ⟨e, heC⟩ * ⟨d, hdC⟩⁻¹ := Subtype.ext (by rw [hy, one_mul]; rfl)
  change F7I.piC C x * F7I.piC C y = F7I.piC C y * F7I.piC C x
  rw [ex, ey]
  simp only [map_mul, map_inv]
  exact hcc _ _

theorem p23MBar_proved : P23MBar n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  have hWt : W ≤ C := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWab w hw t hd.hzW)
  have htC : t ∈ C := hWt hd.hzW
  have heC : e ∈ C := hWt heW
  have huC : u ∈ C := hWt hd.huW
  set A := ((tightCore R).subgroupOf C).map (F7I.piC C) with hAdef
  set B := (K'.subgroupOf C).map (F7I.piC C) with hBdef
  intro x hx m hmA hmB
  have hx' : x = ⟨e, heC⟩ := Subtype.ext hx
  subst hx'
  obtain ⟨qA, -, -, -, -, -, -, heA, heB, b₁, b', hub, ha, hb, -⟩ := p23_twin_q8 hc hCdef htC heC
  have hperm : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C,
      (conjSub q A = A ∧ conjSub q B = B) ∨ (conjSub q A = B ∧ conjSub q B = A) := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    change (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _) ∨
      (conjSub (F7I.piC C c) _ = _ ∧ conjSub (F7I.piC C c) _ = _)
    rw [hAdef, hBdef, F7I.conjSub_map_piC, F7I.conjSub_map_piC]
    rcases p23_conj_twins hc c.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [h1, h2]; exact ⟨rfl, rfl⟩
    · right; rw [h1, h2]; exact ⟨rfl, rfl⟩
  have hu' : (⟨u, huC⟩ : ↥C) = b₁ * b' := Subtype.ext hub.symm
  set M := Subgroup.centralizer ((A : Set (↥C ⧸ classicalInvolutionOddCore ↥C)) ∪ B) with hMdef
  have hmemM : ∀ w, (∀ a ∈ A, w * a = a * w) → (∀ a ∈ B, w * a = a * w) → w ∈ M := by
    intro w hwA hwB
    rw [Subgroup.mem_centralizer_iff]
    rintro h (hh | hh)
    · exact (hwA h hh).symm
    · exact (hwB h hh).symm
  have hMcomm : ∀ w ∈ M, (∀ a ∈ A, w * a = a * w) ∧ (∀ a ∈ B, w * a = a * w) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff] at hw
    exact ⟨fun a ha => (hw a (Or.inl ha)).symm, fun a ha => (hw a (Or.inr ha)).symm⟩
  have hMn : M.Normal := by
    constructor
    intro w hw q
    obtain ⟨hwA, hwB⟩ := hMcomm w hw
    have key : ∀ y : ↥C ⧸ classicalInvolutionOddCore ↥C, (q⁻¹ * y * q ∈ A ∨ q⁻¹ * y * q ∈ B) →
        q * w * q⁻¹ * y = y * (q * w * q⁻¹) := by
      intro y hy
      have h1 : w * (q⁻¹ * y * q) = (q⁻¹ * y * q) * w := by
        rcases hy with hy | hy
        · exact hwA _ hy
        · exact hwB _ hy
      calc q * w * q⁻¹ * y = q * (w * (q⁻¹ * y * q)) * q⁻¹ := by group
        _ = q * ((q⁻¹ * y * q) * w) * q⁻¹ := by rw [h1]
        _ = y * (q * w * q⁻¹) := by group
    have hmem : ∀ (H : Subgroup (↥C ⧸ classicalInvolutionOddCore ↥C)) y, y ∈ H →
        q⁻¹ * y * q ∈ conjSub q⁻¹ H := by
      intro H y hy
      rw [mem_conjSub_iff]
      have e : q⁻¹⁻¹ * (q⁻¹ * y * q) * q⁻¹ = y := by group
      rw [e]
      exact hy
    apply hmemM
    · intro y hy
      apply key
      rcases hperm q⁻¹ with ⟨h1, -⟩ | ⟨h1, -⟩
      · left; rw [← h1]; exact hmem A y hy
      · right; rw [← h1]; exact hmem A y hy
    · intro y hy
      apply key
      rcases hperm q⁻¹ with ⟨-, h1⟩ | ⟨-, h1⟩
      · right; rw [← h1]; exact hmem B y hy
      · left; rw [← h1]; exact hmem B y hy
  have hlift : ∀ w ∈ M, ∃ c' : ↥C, (c' : Y) * u = u * c' ∧ F7I.piC C c' = w := by
    intro w hw
    obtain ⟨hwA, hwB⟩ := hMcomm w hw
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) w
    change ∃ c' : ↥C, (c' : Y) * u = u * c' ∧ F7I.piC C c' = F7I.piC C c
    change ∀ a ∈ A, F7I.piC C c * a = a * F7I.piC C c at hwA
    change ∀ a ∈ B, F7I.piC C c * a = a * F7I.piC C c at hwB
    have hwu : F7I.piC C c * F7I.piC C ⟨u, huC⟩ = F7I.piC C ⟨u, huC⟩ * F7I.piC C c := by
      rw [hu', map_mul]
      calc F7I.piC C c * (F7I.piC C b₁ * F7I.piC C b')
          = (F7I.piC C c * F7I.piC C b₁) * F7I.piC C b' := by group
        _ = (F7I.piC C b₁ * F7I.piC C c) * F7I.piC C b' := by rw [hwA _ ha]
        _ = F7I.piC C b₁ * (F7I.piC C c * F7I.piC C b') := by group
        _ = F7I.piC C b₁ * (F7I.piC C b' * F7I.piC C c) := by rw [hwB _ hb]
        _ = _ := by group
    have huu : (⟨u, huC⟩ : ↥C) * ⟨u, huC⟩ = 1 := Subtype.ext hd.hu2
    have hprod : F7I.piC C (⟨u, huC⟩ * (c * ⟨u, huC⟩ * c⁻¹)) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hwu, mul_inv_cancel_right, ← map_mul, huu,
        map_one]
    have hO1 : u * ((c : Y) * u * (c : Y)⁻¹) ∈ oddCoreOf C := (F7I.piC_eq_one_iff _).mp hprod
    have hodd : Odd (orderOf (u * ((c : Y) * u * (c : Y)⁻¹))) :=
      Odd.of_dvd_nat (oddCoreOf_odd_natCard C) (Subgroup.orderOf_dvd_natCard _ hO1)
    have hx2 : ((c : Y) * u * (c : Y)⁻¹) * (c * u * c⁻¹) = 1 := by
      calc ((c : Y) * u * (c : Y)⁻¹) * (c * u * c⁻¹) = c * (u * u) * c⁻¹ := by group
        _ = 1 := by rw [hd.hu2, mul_one]; simp
    obtain ⟨k, hk⟩ := T3Core.exists_conj_of_mul_mem_odd hd.hu2 hx2 hodd
    have hgO : (u * ((c : Y) * u * (c : Y)⁻¹)) ^ k ∈ oddCoreOf C := (oddCoreOf C).pow_mem hO1 k
    have hgC : (u * ((c : Y) * u * (c : Y)⁻¹)) ^ k ∈ C := oddCoreOf_le_self C hgO
    refine ⟨⟨_, C.inv_mem hgC⟩ * c, ?_, ?_⟩
    · show ((u * ((c : Y) * u * (c : Y)⁻¹)) ^ k)⁻¹ * c * u = u * (((u * ((c : Y) * u * (c : Y)⁻¹)) ^ k)⁻¹ * c)
      set gg := (u * ((c : Y) * u * (c : Y)⁻¹)) ^ k
      calc gg⁻¹ * c * u = gg⁻¹ * ((c : Y) * u * (c : Y)⁻¹) * c := by group
        _ = gg⁻¹ * (gg * u * gg⁻¹) * c := by rw [hk]
        _ = u * (gg⁻¹ * c) := by group
    · rw [map_mul, (F7I.piC_eq_one_iff _).mpr ((oddCoreOf C).inv_mem hgO), one_mul]
  set X := oddCoreOf (Subgroup.centralizer ({u} : Set Y)) ⊓ C with hXdef
  have hXC : X ≤ C := inf_le_right
  set P := (X.subgroupOf C).map (F7I.piC C) with hPdef
  have hPodd : Odd (Nat.card P) := by
    refine Odd.of_dvd_nat ?_ (Subgroup.card_map_dvd _ _)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXC).toEquiv]
    exact Odd.of_dvd_nat (oddCoreOf_odd_natCard _) (Subgroup.card_dvd_of_le inf_le_left)
  have hMP : M ≤ Subgroup.normalizer (P : Set (↥C ⧸ classicalInvolutionOddCore ↥C)) := by
    intro w hw
    obtain ⟨c', hc'u, rfl⟩ := hlift w hw
    have hc'U : (c' : Y) ∈ Subgroup.centralizer ({u} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hc'u
    have hcX : conjSub (c' : Y) X = X := by
      apply mem_normalizer_iff_conjSub_eq.mp
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := Subgroup.mem_normalizer_iff.mp
        (Sec7.le_normalizer_oddCoreOf (Subgroup.centralizer ({u} : Set Y)) hc'U) h
      have h2 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer c'.2) h
      constructor
      · rintro ⟨ha1, ha2⟩
        exact ⟨h1.mp ha1, h2.mp ha2⟩
      · rintro ⟨ha1, ha2⟩
        exact ⟨h1.mpr ha1, h2.mpr ha2⟩
    apply mem_normalizer_iff_conjSub_eq.mpr
    rw [hPdef, F7I.conjSub_map_piC, hcX]
  have hmM : m ∈ M := hmemM m hmA hmB
  obtain ⟨m', hm'u, rfl⟩ := hlift m hmM
  have hm'U : (m' : Y) ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hm'u
  have hw0 := ((T8YY.mem_zStarOf_iff _).mp hZ).2 _ hm'U
  set w1 : ↥C := (⟨e, heC⟩ : ↥C)⁻¹ * m'⁻¹ * ⟨e, heC⟩ * m' with hw1
  have hw1X : (w1 : Y) ∈ X := by
    refine ⟨?_, w1.2⟩
    have e1 : (w1 : Y) = (u * e)⁻¹ * (m' : Y)⁻¹ * (u * e) * m' := by
      show e⁻¹ * (m' : Y)⁻¹ * e * m' = _
      have hmu' : (m' : Y)⁻¹ * u = u * (m' : Y)⁻¹ := by
        calc (m' : Y)⁻¹ * u = (m' : Y)⁻¹ * (u * m') * (m' : Y)⁻¹ := by group
          _ = (m' : Y)⁻¹ * ((m' : Y) * u) * (m' : Y)⁻¹ := by rw [hm'u]
          _ = u * (m' : Y)⁻¹ := by group
      calc e⁻¹ * (m' : Y)⁻¹ * e * m' = e⁻¹ * (u⁻¹ * (u * (m' : Y)⁻¹)) * e * m' := by group
        _ = e⁻¹ * (u⁻¹ * ((m' : Y)⁻¹ * u)) * e * m' := by rw [hmu']
        _ = (u * e)⁻¹ * (m' : Y)⁻¹ * (u * e) * m' := by group
    rw [e1]
    exact hw0
  have hw1P : F7I.piC C w1 ∈ P := F7I.mem_map_piC.mpr ⟨w1, hw1X, rfl⟩
  have heM : F7I.piC C ⟨e, heC⟩ ∈ M := hmemM _ heA heB
  have hw1M : F7I.piC C w1 ∈ M := by
    rw [hw1, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact M.mul_mem (M.mul_mem (M.mul_mem (M.inv_mem heM) (M.inv_mem hmM)) heM) hmM
  have h1 := F7I.eq_one_of_odd_normalized (F7I.quot_odd_normal_eq_bot C) hMn hPodd hMP hw1P hw1M
  rw [hw1, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  set mm := F7I.piC C m'
  set ee := F7I.piC C ⟨e, heC⟩
  calc mm * ee = mm * ee * (ee⁻¹ * mm⁻¹ * ee * mm) := by rw [h1, mul_one]
    _ = ee * mm := by group

theorem p23E7MBar_proved : P23E7MBar n := p23E7MBar_of_mbar p23MBar_proved

theorem p23E8Phi_of_ae (hT : Thm4RTwinBelow 3 n) (hAE : P23E8PhiAE n) : P23E8Phi n :=
  p23E8Phi_of_steps hT p23MBar_proved hAE

end MBar

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
