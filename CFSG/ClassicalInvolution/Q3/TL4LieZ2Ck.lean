module

public import Certificates.Data.TL4LieZ2Inv
public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.LieZ2

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Q3.TA3.Check CFSG.GH74.KGroups Certificates.TL4LieZ2Inv

section Check

variable {M : Type} [Group M] [DecidableEq M]

theorem eq_of_q8InvCheck {P A : Subgroup M} {LP LA reps : List M}
    (hLP : ∀ g, g ∈ LP ↔ g ∈ P) (hLA : ∀ g ∈ A, g ∈ LA) (hPA : P ≤ A)
    (h : q8InvCheck LP LA reps = true) {t a b c : M} (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (ha : a ∈ P) (hb : b ∈ P) (haa : a * a = t) (hbb : b * b = t) (hba : b * a = t * a * b)
    (hc : c ∈ A) (hc2 : c * c = 1) (hca : c * a = a * c) (hcb : c * b = b * c) :
    c = 1 ∨ c = t := by
  obtain ⟨hcov, hall⟩ := Bool.and_eq_true_iff.1 h
  have htP : t ∈ P := haa ▸ P.mul_mem ha ha
  have h1 := List.all_eq_true.1 hcov t ((hLP t).2 htP)
  rw [decide_eq_true (show t * t = 1 ∧ t ≠ 1 from ⟨ht2, ht1⟩), Bool.not_true,
    Bool.false_or] at h1
  obtain ⟨g, hgL, hg⟩ := List.any_eq_true.1 h1
  obtain ⟨r, hr, hgr⟩ := List.any_eq_true.1 hg
  have hgr' : g * t * g⁻¹ = r := of_decide_eq_true hgr
  have hgP : g ∈ P := (hLP g).1 hgL
  have hconj : ∀ x y : M, g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ := fun x y => by
    group
  have hcomm : ∀ x y : M, x * y = y * x →
      g * x * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * x * g⁻¹) := fun x y hxy => by
    rw [hconj, hconj, hxy]
  have hta : a * t = t * a := by rw [← haa, mul_assoc]
  have htb : b * t = t * b := by rw [← hbb, mul_assoc]
  have htc : c * t = t * c := by
    rw [← haa, ← mul_assoc, hca, mul_assoc, hca, mul_assoc]
  have hmemP : ∀ x ∈ P, g * x * g⁻¹ ∈ P := fun x hx =>
    P.mul_mem (P.mul_mem hgP hx) (P.inv_mem hgP)
  have hcentP : ∀ x ∈ P, x * t = t * x → g * x * g⁻¹ ∈ centB LP r := fun x hx hxt =>
    List.mem_filter.2 ⟨(hLP _).2 (hmemP x hx), decide_eq_true (by
      rw [← hgr']
      exact hcomm x t hxt)⟩
  have hrr := List.all_eq_true.1 hall r hr
  unfold q8InvAt at hrr
  have ha' : g * a * g⁻¹ ∈ (centB LP r).filter fun x => decide (x * x = r) :=
    List.mem_filter.2 ⟨hcentP a ha hta, decide_eq_true (by rw [hconj, haa, hgr'])⟩
  have hb' : g * b * g⁻¹ ∈ (centB LP r).filter fun x => decide (x * x = r) :=
    List.mem_filter.2 ⟨hcentP b hb htb, decide_eq_true (by rw [hconj, hbb, hgr'])⟩
  have h2 := List.all_eq_true.1 (List.all_eq_true.1 hrr _ ha') _ hb'
  have hrel : g * b * g⁻¹ * (g * a * g⁻¹) = r * (g * a * g⁻¹) * (g * b * g⁻¹) := by
    rw [hconj, hba, ← hgr']
    group
  rw [decide_eq_true hrel, Bool.not_true, Bool.false_or] at h2
  have hc' : g * c * g⁻¹ ∈ centB LA r :=
    List.mem_filter.2 ⟨hLA _ (A.mul_mem (A.mul_mem (hPA hgP) hc) (A.inv_mem (hPA hgP))),
      decide_eq_true (by
        rw [← hgr']
        exact hcomm c t htc)⟩
  have h3 := List.all_eq_true.1 h2 _ hc'
  have hprem : g * c * g⁻¹ * (g * c * g⁻¹) = 1 ∧
      g * c * g⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * (g * c * g⁻¹) ∧
      g * c * g⁻¹ * (g * b * g⁻¹) = g * b * g⁻¹ * (g * c * g⁻¹) :=
    ⟨by rw [hconj, hc2]; group, hcomm c a hca, hcomm c b hcb⟩
  rw [decide_eq_true hprem, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq,
    decide_eq_true_eq] at h3
  rcases h3 with h3 | h3
  · left
    have := congrArg (fun w => g⁻¹ * w * g) h3
    simpa [mul_assoc] using this
  · right
    rw [← hgr'] at h3
    have := congrArg (fun w => g⁻¹ * w * g) h3
    simpa [mul_assoc] using this

end Check

section Model

variable {X : Type} [Group X] {n : ℕ}

theorem eq_one_or_conj_of_autModel (Mo : AutModel X (Equiv.Perm (Fin n)))
    {LP LA reps : List (Equiv.Perm (Fin n))} (hLP : ∀ g, g ∈ LP ↔ g ∈ Mo.P)
    (hLA : ∀ g ∈ Mo.A, g ∈ LA) (hPA : Mo.P ≤ Mo.A) (h : q8InvCheck LP LA reps = true)
    {z i j : X} (hz1 : z ≠ 1) (hzz : z * z = 1) (hii : i * i = z) (hjj : j * j = z)
    (hji : j * i = z * i * j) {β : MulAut X} (hβ : β * β = 1) (hβi : β i = i)
    (hβj : β j = j) : β = 1 ∨ β = MulAut.conj z := by
  set ι : X →* Equiv.Perm (Fin n) := Mo.P.subtype.comp Mo.e.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp Mo.e.injective
  have hιP : ∀ x, ι x ∈ Mo.P := fun x => (Mo.e x).2
  set σ : Equiv.Perm (Fin n) := (Mo.Φ β : Equiv.Perm (Fin n)) with hσ
  have hspec : ∀ x, ι (β x) = σ * ι x * σ⁻¹ := fun x => Mo.spec β x
  have hσσ : σ * σ = 1 := by
    rw [hσ, ← AutModel.Φ_mul, hβ, AutModel.Φ_one]
  have hσc : ∀ x, β x = x → σ * ι x = ι x * σ := fun x hx => by
    have h1 := hspec x
    rw [hx] at h1
    calc σ * ι x = σ * ι x * σ⁻¹ * σ := by group
      _ = ι x * σ := by rw [← h1]
  rcases eq_of_q8InvCheck hLP hLA hPA h (t := ι z) (a := ι i) (b := ι j) (c := σ)
    (fun h0 => hz1 (hιinj (by rw [h0, map_one]))) (by rw [← map_mul, hzz, map_one])
    (hιP i) (hιP j) (by rw [← map_mul, hii]) (by rw [← map_mul, hjj])
    (by rw [← map_mul, hji, map_mul, map_mul]) (Mo.Φ β).2 hσσ (hσc i hβi) (hσc j hβj)
    with h1 | h1
  · left
    apply Mo.Φ.injective
    rw [map_one]
    exact Subtype.ext h1
  · right
    ext x
    apply hιinj
    rw [hspec, h1, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem concl163_of_autModel (Mo : AutModel X (Equiv.Perm (Fin n)))
    {LP LA reps : List (Equiv.Perm (Fin n))} (hLP : ∀ g, g ∈ LP ↔ g ∈ Mo.P)
    (hLA : ∀ g ∈ Mo.A, g ∈ LA) (hPA : Mo.P ≤ Mo.A) (h : q8InvCheck LP LA reps = true)
    {Φ : Set (Subgroup X)} (hΦ : TypeRFam 3 Φ) :
    ∀ L ∈ Φ, ∀ a : X, IsUniqueInvolution L a → ∀ P : Subgroup X, IsSylow2In P L →
      ∀ β : MulAut X, β * β = 1 → (∀ x ∈ P, β x = x) → β = 1 ∨ β = MulAut.conj a := by
  intro L hL a ha P hP β hβ hfix
  obtain ⟨e⟩ := hΦ.quat L hL P hP
  let e' : ↥P ≃* QuaternionGroup 2 := e
  have hco : ∀ u v : QuaternionGroup 2,
      ((e'.symm (u * v) : ↥P) : X) = (e'.symm u : X) * (e'.symm v : X) := fun u v => by
    rw [map_mul, Subgroup.coe_mul]
  have hz1 : ((e'.symm (QuaternionGroup.a 2) : ↥P) : X) ≠ 1 := fun h0 => by
    have h1 : e'.symm (QuaternionGroup.a 2) = e'.symm 1 := by
      rw [map_one]
      exact Subtype.ext h0
    exact absurd (e'.symm.injective h1) (by decide)
  have hzz : ((e'.symm (QuaternionGroup.a 2) : ↥P) : X) *
      (e'.symm (QuaternionGroup.a 2) : X) = 1 := by
    rw [← hco, show (QuaternionGroup.a 2 * QuaternionGroup.a 2 : QuaternionGroup 2) = 1 by
      decide, map_one, Subgroup.coe_one]
  have hza : ((e'.symm (QuaternionGroup.a 2) : ↥P) : X) = a :=
    (ha.unique _ (hP.1 (e'.symm (QuaternionGroup.a 2)).2) hzz).resolve_left hz1
  rw [← hza]
  refine eq_one_or_conj_of_autModel Mo hLP hLA hPA h hz1 hzz
    (i := (e'.symm (QuaternionGroup.a 1) : X)) (j := (e'.symm (QuaternionGroup.xa 0) : X))
    ?_ ?_ ?_ hβ (hfix _ (e'.symm _).2) (hfix _ (e'.symm _).2)
  · rw [← hco, show (QuaternionGroup.a 1 * QuaternionGroup.a 1 : QuaternionGroup 2) =
      QuaternionGroup.a 2 by decide]
  · rw [← hco, show (QuaternionGroup.xa 0 * QuaternionGroup.xa 0 : QuaternionGroup 2) =
      QuaternionGroup.a 2 by decide]
  · rw [← hco, ← hco, ← hco, show (QuaternionGroup.xa 0 * QuaternionGroup.a 1 :
      QuaternionGroup 2) = QuaternionGroup.a 2 * QuaternionGroup.a 1 * QuaternionGroup.xa 0 by
      decide]

end Model

end CFSG.ClassicalInvolution.Q3.TL4.LieZ2
