module

public import CFSG.GroupTheory.ThompsonAxB
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer
import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {X : Type*} [Group X]

theorem pCore_eq_open_pCore' (p : ℕ) (G : Type*) [Group G] :
    CFSG.pCore p G = CFSG.Open.pCore p G := (CFSG.Open.pCore_eq_pCore p G).symm

theorem orderOf_coprime_of_mem_GLAPPrimeCoreOf [Finite X] {p : ℕ} (hp : p.Prime)
    {C : Subgroup X} {d : X} (hd : d ∈ GLAPPrimeCoreOf p C) :
    (orderOf d).Coprime p := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hd
  have h1 : orderOf (⟨y, hy⟩ : ↥(GLAPPrimeCore p ↥C)) ∣ Nat.card ↥(GLAPPrimeCore p ↥C) :=
    orderOf_dvd_natCard _
  have h2 : orderOf (⟨y, hy⟩ : ↥(GLAPPrimeCore p ↥C)) = orderOf y :=
    Subgroup.orderOf_mk _ _
  have h3 : orderOf (y : X) = orderOf y := Subgroup.orderOf_coe y
  change (orderOf (y : X)).Coprime p
  rw [h3]
  exact Nat.Coprime.coprime_dvd_left (h2 ▸ h1)
    (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore hp ↥C).symm

theorem comm_of_mem_GLAPPrimeCoreOf_centralizer [Finite X] {p : ℕ} (hp : p.Prime) {e : X}
    {d m : X} (hd : d ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({e} : Set X)))
    (hm : m ∈ Subgroup.centralizer ({e} : Set X)) (hmp : m ∈ CFSG.pCore p X) :
    d * m = m * d := by
  have :=CFSG.pCore_normal (p := p) (G := X)
  set C := Subgroup.centralizer ({e} : Set X) with hC
  set D := GLAPPrimeCoreOf p C with hD
  have hDconj : ∀ g ∈ C, ∀ x ∈ D, g * x * g⁻¹ ∈ D := by
    intro g hg x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    refine Subgroup.mem_map.2 ⟨(⟨g, hg⟩ : ↥C) * y * (⟨g, hg⟩ : ↥C)⁻¹,
      (GLAPPrimeCore.normal p ↥C).conj_mem y hy _, ?_⟩
    simp
  have hcD : d * m * d⁻¹ * m⁻¹ ∈ D := by
    have h1 : m * d⁻¹ * m⁻¹ ∈ D := hDconj m hm _ (D.inv_mem hd)
    have h2 := D.mul_mem hd h1
    have h3 : d * (m * d⁻¹ * m⁻¹) = d * m * d⁻¹ * m⁻¹ := by group
    rwa [h3] at h2
  have hcP : d * m * d⁻¹ * m⁻¹ ∈ CFSG.pCore p X := by
    have h1 : d * m * d⁻¹ ∈ CFSG.pCore p X :=
      (CFSG.pCore_normal (p := p) (G := X)).conj_mem m hmp d
    exact (CFSG.pCore p X).mul_mem h1 (inv_mem hmp)
  have hcop : (orderOf (d * m * d⁻¹ * m⁻¹)).Coprime p :=
    orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hcD
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := p) (G := X)) ⟨_, hcP⟩
  have hk' : (d * m * d⁻¹ * m⁻¹) ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd : orderOf (d * m * d⁻¹ * m⁻¹) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hone : orderOf (d * m * d⁻¹ * m⁻¹) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hdvd
  have hc1 : d * m * d⁻¹ * m⁻¹ = 1 := orderOf_eq_one_iff.mp hone
  have h2 : d * m * d⁻¹ = m := by
    rw [mul_inv_eq_one] at hc1
    exact hc1
  have h3 := congrArg (· * d) h2
  simpa using h3

theorem glaPPrimeCoreOf_centralizer_le_centralizer_pCore [Finite X] {p : ℕ} (hp : p.Prime)
    {e : X} (he : IsPGroup p (Subgroup.zpowers e)) :
    GLAPPrimeCoreOf p (Subgroup.centralizer ({e} : Set X)) ≤
      Subgroup.centralizer (CFSG.Open.pCore p X : Set X) := by
  have :=Fact.mk hp
  have :=CFSG.pCore_normal (p := p) (G := X)
  set C := Subgroup.centralizer ({e} : Set X) with hC
  set N := CFSG.pCore p X with hN
  intro d hd
  have hdC : d ∈ C := by
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.1 hd
    exact y.2
  have hde : Commute d e := Subgroup.mem_centralizer_singleton_iff.mp hdC
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hr' : r ∈ N := hr
  let α : ↥(Subgroup.zpowers d) →* MulAut N :=
    (MulAut.conjNormal (H := N)).comp (Subgroup.zpowers d).subtype
  let β : ↥(Subgroup.zpowers e) →* MulAut N :=
    (MulAut.conjNormal (H := N)).comp (Subgroup.zpowers e).subtype
  have hcomm : ∀ a b, α a * β b = β b * α a := by
    intro a b
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    have hab : (a : X) * (b : X) = (b : X) * (a : X) := by
      rw [← hi, ← hj]
      exact ((hde.zpow_left i).zpow_right j).eq
    show MulAut.conjNormal (a : X) * MulAut.conjNormal (b : X) =
      MulAut.conjNormal (b : X) * MulAut.conjNormal (a : X)
    rw [← map_mul, ← map_mul, hab]
  have hfix : ∀ a r, (∀ b, β b r = r) → α a r = r := by
    intro a r hfr
    have hre : e * (r : X) * e⁻¹ = (r : X) := by
      have h := hfr ⟨e, Subgroup.mem_zpowers e⟩
      have h' := congrArg Subtype.val h
      simpa [β, MulAut.conjNormal_apply] using h'
    have hrC : (r : X) ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hre).symm
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    have hai : (a : X) ∈ GLAPPrimeCoreOf p C := by
      rw [← hi]
      exact (GLAPPrimeCoreOf p C).zpow_mem hd i
    have hcomm' : (a : X) * (r : X) = (r : X) * (a : X) :=
      comm_of_mem_GLAPPrimeCoreOf_centralizer hp hai hrC r.2
    apply Subtype.ext
    show (MulAut.conjNormal (a : X) r : X) = (r : X)
    rw [MulAut.conjNormal_apply, hcomm', mul_inv_cancel_right]
  have hA : ¬ p ∣ Nat.card ↥(Subgroup.zpowers d) := by
    rw [Nat.card_zpowers]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1
      (orderOf_coprime_of_mem_GLAPPrimeCoreOf hp hd).symm
  have hT := CFSG.GroupTheory.thompson_A_times_B (p := p) (R := ↥N)
    (A := ↥(Subgroup.zpowers d)) (B := ↥(Subgroup.zpowers e))
    (CFSG.pCore_isPGroup (p := p) (G := X)) hA he α β hcomm hfix
  have h1 := congrArg (fun φ : MulAut N => φ ⟨r, hr'⟩)
    (hT ⟨d, Subgroup.mem_zpowers d⟩)
  have h2 : (d * (r : X) * d⁻¹) = (r : X) := by
    have h3 := congrArg Subtype.val h1
    simpa [α, MulAut.conjNormal_apply] using h3
  have h4 : d * (r : X) = (r : X) * d := (mul_inv_eq_iff_eq_mul.mp h2)
  exact h4.symm

end CFSG.HardMathSupport.Timmesfeld.Proving

end
