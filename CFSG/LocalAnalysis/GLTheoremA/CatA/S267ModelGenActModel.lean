module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenB
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.GH74.Uniqueness.SU.SU7Gen3
import CFSG.CGT.T75P.SylowSplit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenActData

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

variable {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω} {X : Type} [Group X]

private theorem actHom_apply_of_mem (hS : S.Normal) {π : ↥S →* X} (hπ : Function.Surjective π)
    {Γ : Ω →* MulAut X}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩) (s : ↥S)
    (y : X) : Γ s y = π s * y * (π s)⁻¹ := by
  obtain ⟨g, rfl⟩ := hπ y
  rw [hΓ, ← map_mul, ← map_inv, ← map_mul]
  rfl

private theorem card_map_comap (π : ↥S →* X) (hπ : Function.Surjective π) (H : Subgroup X) :
    Nat.card ((H.comap π).map S.subtype) = Nat.card H * Nat.card π.ker := by
  rw [Subgroup.card_map_of_injective S.subtype_injective]
  have h := CFSG.GH74.Uniqueness.SU.SU7.Gen.card_map_mul_card_inf_ker π (H.comap π)
  rw [Subgroup.map_comap_eq_self_of_surjective hπ, inf_eq_right.2 (Subgroup.ker_le_comap π H)] at h
  exact h.symm

theorem actFix_comap_eq_centralizer (hS : S.Normal) {π : ↥S →* X} (hπ : Function.Surjective π)
    {Γ : Ω →* MulAut X}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩)
    {B : Subgroup Ω} {H : Subgroup X} (hHB : (H.comap π).map S.subtype ≤ B) :
    actFix (fun x : ↥B => Γ x) ((H.comap π).map S.subtype) =
      Subgroup.centralizer (H : Set X) := by
  ext g
  rw [mem_actFix, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg a ha
    obtain ⟨s, rfl⟩ := hπ a
    have hsH : (s : Ω) ∈ (H.comap π).map S.subtype := ⟨s, ha, rfl⟩
    have h1 : Γ (s : Ω) g = g := hg ⟨s, hHB hsH⟩ hsH
    rw [actHom_apply_of_mem hS hπ hΓ] at h1
    calc π s * g = π s * g * (π s)⁻¹ * π s := by group
      _ = g * π s := by rw [h1]
  · rintro hg x ⟨s, hs, hsx⟩
    have h1 : Γ (x : Ω) g = Γ (s : Ω) g := by rw [← hsx]; rfl
    rw [h1, actHom_apply_of_mem hS hπ hΓ, hg (π s) hs, mul_inv_cancel_right]

private theorem map_conj_eq_of_mem_normalizer {J : Subgroup X} {a : X}
    (ha : a ∈ Subgroup.normalizer (J : Set X)) {φ : MulAut X} (hφ : ∀ y, φ y = a * y * a⁻¹) :
    J.map φ.toMonoidHom = J := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    show φ j ∈ J
    rw [hφ]
    exact (Subgroup.mem_normalizer_iff.1 ha j).1 hj
  · intro hy
    refine ⟨a⁻¹ * y * a, ?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.1 ha (a⁻¹ * y * a)).2
      rw [show a * (a⁻¹ * y * a) * a⁻¹ = y by group] at h
      exact h hy
    · show φ (a⁻¹ * y * a) = y
      rw [hφ]
      group

theorem actData_of_modelAGen_comap (hS : S.Normal) {π : ↥S →* X} (hπ : Function.Surjective π)
    (hker : Nat.card π.ker = p) {Γ : Ω →* MulAut X}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩) {n : ℕ}
    (hn : 3 ≤ n) {A A₁ A₁₂ J : Subgroup X} {t : X} (hAc : Nat.card A = p ^ n) (h1 : A₁ ≤ A₁₂)
    (h12 : A₁₂ ≤ A) (hA₁c : Nat.card A₁ = p) (hA₁₂c : Nat.card A₁₂ = p ^ 2)
    (hJ : GLAPComponent p (Subgroup.centralizer (A₁ : Set X)) J)
    (hAN : A ≤ Subgroup.normalizer (J : Set X)) (hcent : ∀ x ∈ A, CentMod p J x → x ∈ A₁)
    (hlay : GLAPLayer p (J ⊓ Subgroup.centralizer (A₁₂ : Set X)) ≠ ⊥) (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) (hJt : J ≤ Subgroup.centralizer ({t} : Set X))
    (hAt : A ≤ Subgroup.centralizer ({t} : Set X)) :
    ActData p ((A.comap π).map S.subtype) fun x => Γ x := by
  classical
  set M := (A.comap π).map S.subtype with hM
  have hDM : (A₁.comap π).map S.subtype ≤ M :=
    Subgroup.map_mono (Subgroup.comap_mono (h1.trans h12))
  have hEM : (A₁₂.comap π).map S.subtype ≤ M := Subgroup.map_mono (Subgroup.comap_mono h12)
  have hΓs := actHom_apply_of_mem hS hπ hΓ
  have hcM : ∀ x : ↥M, ∃ s : ↥S, π s ∈ A ∧ ((x : Ω) = s) := by
    rintro ⟨_, s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  have hpn : p ^ 2 * (p * p) ≤ p ^ n * p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0; simp
    · calc p ^ 2 * (p * p) = p ^ 3 * p := by ring
        _ ≤ p ^ n * p := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right h0 hn)
  refine ⟨(A₁.comap π).map S.subtype, (A₁₂.comap π).map S.subtype, J, t, hDM, hEM,
    Subgroup.map_mono (Subgroup.comap_mono h1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ht1, ht2, hJt, ?_⟩
  · rw [card_map_comap π hπ, hA₁c, hker, sq]
  · rw [card_map_comap π hπ, card_map_comap π hπ, hA₁c, hAc, hker]
    exact hpn
  · intro _
    rw [card_map_comap π hπ, hA₁₂c, hker]
    ring
  · rw [actFix_comap_eq_centralizer hS hπ hΓ hDM]
    exact hJ
  · intro x
    obtain ⟨s, hs, hxs⟩ := hcM x
    exact map_conj_eq_of_mem_normalizer (hAN hs) fun y => by
      show Γ (x : Ω) y = _
      rw [hxs, hΓs]
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := hcM x
    have hc : CentMod p J (π s) := by
      rw [centMod_iff]
      refine ⟨hAN hs, fun j hj => ?_⟩
      have h2 := hx j hj
      rw [show (Γ (x : Ω)) j = π s * j * (π s)⁻¹ by rw [hxs, hΓs]] at h2
      rw [commutatorElement_def]
      convert h2 using 1
      group
    rw [hxs]
    exact ⟨s, hcent _ hs hc, rfl⟩
  · intro _
    rw [actFix_comap_eq_centralizer hS hπ hΓ hEM]
    exact hlay
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := hcM x
    show Γ (x : Ω) t = t
    rw [hxs, hΓs]
    have hst : π s * t = t * π s := Subgroup.mem_centralizer_singleton_iff.1 (hAt hs)
    rw [hst, mul_inv_cancel_right]

private theorem exists_of_mem_map_comap {π : ↥S →* X} {H : Subgroup X} {x : Ω}
    (hx : x ∈ (H.comap π).map S.subtype) : ∃ s : ↥S, π s ∈ H ∧ x = s := by
  obtain ⟨s, hs, rfl⟩ := hx
  exact ⟨s, hs, rfl⟩

private theorem map_pow_eq_of_map_eq {J : Subgroup X} {ψ : MulAut X}
    (hJψ : J.map ψ.toMonoidHom = J) (k : ℕ) : J.map (ψ ^ k).toMonoidHom = J := by
  induction k with
  | zero => exact Subgroup.map_id J
  | succ k ih =>
    rw [pow_succ, show ((ψ ^ k * ψ : MulAut X)).toMonoidHom =
      (ψ ^ k).toMonoidHom.comp ψ.toMonoidHom from rfl, ← Subgroup.map_map, hJψ, ih]

theorem actData_of_modelBGen_comap (hp : p.Prime) (hS : S.Normal) {π : ↥S →* X}
    (hπ : Function.Surjective π) (hker : Nat.card π.ker = p) {Γ : Ω →* MulAut X}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩) {n : ℕ}
    (hn : 2 ≤ n) {ψ : MulAut X} (hψout : ψ ∉ (MulAut.conj : X →* MulAut X).range)
    {A A₁ J : Subgroup X} {t : X} (hAc : Nat.card A = p ^ n) (h1 : A₁ ≤ A)
    (hA₁c : Nat.card A₁ = p) (hJ : GLAPComponent p (Subgroup.centralizer (A₁ : Set X)) J)
    (hAN : A ≤ Subgroup.normalizer (J : Set X)) (hJψ : J.map ψ.toMonoidHom = J)
    (hk : ∀ a ∈ A, ∀ k : ℕ, k < p →
      (∀ j ∈ J, j * (a * (ψ ^ k) j * a⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p J) → k = 0 ∧ a ∈ A₁)
    (hlay : GLAPLayer p (J ⊓ fixSubgroup ψ) ≠ ⊥) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1)
    (hJt : J ≤ Subgroup.centralizer ({t} : Set X))
    (hAt : A ≤ Subgroup.centralizer ({t} : Set X)) {b : Ω} (hb : Γ b = ψ) (hbp : b ^ p = 1)
    (hbM : ∀ m ∈ (A.comap π).map S.subtype, b * m = m * b) :
    ActData p ((A.comap π).map S.subtype ⊔ Subgroup.zpowers b) fun x => Γ x := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set M := (A.comap π).map S.subtype with hM
  set Z := Subgroup.zpowers b with hZ
  set D := (A₁.comap π).map S.subtype with hD
  set E := D ⊔ Z with hE
  have hΓs := actHom_apply_of_mem hS hπ hΓ
  have hDM : D ≤ M := Subgroup.map_mono (Subgroup.comap_mono h1)
  have hMZ : ∀ m ∈ M, ∀ y ∈ Z, m * y = y * m := by
    intro m hm y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_right (hbM m hm).symm j)
  have hψp : ψ ^ p = 1 := by rw [← hb, ← map_pow, hbp, map_one]
  have hZk : ∀ y ∈ Z, ∃ k : ℕ, k < p ∧ y = b ^ k := fun y hy => by
    obtain ⟨k, hk, hky⟩ := exists_pow_lt_of_pow_eq_one hp.pos hbp hy
    exact ⟨k, hk, hky.symm⟩
  have hinn : ∀ k : ℕ, k < p → ∀ s : ↥S, b ^ k = (s : Ω) → k = 0 := by
    intro k hk s hks
    by_contra hk0
    apply pow_not_mem_range_conj hp hψp hψout hk hk0
    refine ⟨π s, MulEquiv.ext fun y => ?_⟩
    rw [← hb, ← map_pow, hks, hΓs]
    rfl
  have hMZinf : M ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyM, hyZ⟩
    obtain ⟨s, -, rfl⟩ := exists_of_mem_map_comap hyM
    obtain ⟨k, hk, hks⟩ := hZk _ hyZ
    rw [Subgroup.mem_bot, hks, hinn k hk s hks.symm, pow_zero]
  have hb1 : b ≠ 1 := by
    intro h
    apply hψout
    refine ⟨1, ?_⟩
    rw [map_one, ← hb, h, map_one]
  have hZc : Nat.card Z = p := by
    rw [hZ, Nat.card_zpowers, orderOf_eq_prime hbp hb1]
  have hDc : Nat.card D = p ^ 2 := by rw [hD, card_map_comap π hπ, hA₁c, hker, sq]
  have hMc : Nat.card M = p ^ (n + 1) := by rw [hM, card_map_comap π hπ, hAc, hker, pow_succ]
  have hB'c : Nat.card ↥(M ⊔ Z) = p ^ (n + 2) := by
    rw [CFSG.CGT.T75P.card_sup_of_commute hMZ hMZinf, hMc, hZc]
    ring
  have hDZinf : D ⊓ Z = ⊥ := eq_bot_iff.2 fun y hy => hMZinf.le ⟨hDM hy.1, hy.2⟩
  have hEc : Nat.card E = p ^ 3 := by
    rw [hE, CFSG.CGT.T75P.card_sup_of_commute (fun d hd y hy => hMZ d (hDM hd) y hy) hDZinf, hDc,
      hZc]
    ring
  have hDB' : D ≤ M ⊔ Z := hDM.trans le_sup_left
  have hEB' : E ≤ M ⊔ Z := sup_le_sup_right hDM Z
  have hdec : ∀ x : ↥(M ⊔ Z), ∃ s : ↥S, π s ∈ A ∧ ∃ k : ℕ, k < p ∧ (x : Ω) = s * b ^ k := by
    intro x
    obtain ⟨m, hm, y, hy, hxy⟩ := CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute hMZ x.2
    obtain ⟨s, hs, rfl⟩ := exists_of_mem_map_comap hm
    obtain ⟨k, hk, rfl⟩ := hZk y hy
    exact ⟨s, hs, k, hk, hxy.symm⟩
  have hΓx : ∀ (s : ↥S) (k : ℕ) (y : X), Γ ((s : Ω) * b ^ k) y = π s * (ψ ^ k) y * (π s)⁻¹ := by
    intro s k y
    rw [map_mul, MulAut.mul_apply, map_pow, hb, hΓs]
  refine ⟨D, E, J, t, hDB', hEB', le_sup_left, by rw [hDc], ?_, fun _ => hEc, ?_, ?_, ?_, ?_,
    ht1, ht2, hJt, ?_⟩
  · rw [hDc, hB'c]
    calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
      _ ≤ p ^ (n + 2) := Nat.pow_le_pow_right hp.pos (by omega)
  · rw [actFix_comap_eq_centralizer hS hπ hΓ hDB']
    exact hJ
  · intro x
    obtain ⟨s, hs, k, -, hx⟩ := hdec x
    have e : (Γ (x : Ω)).toMonoidHom =
        (MulAut.conj (π s)).toMonoidHom.comp (ψ ^ k).toMonoidHom := by
      ext y
      show Γ (x : Ω) y = π s * (ψ ^ k) y * (π s)⁻¹
      rw [hx, hΓx]
    show J.map (Γ (x : Ω)).toMonoidHom = J
    rw [e, ← Subgroup.map_map, map_pow_eq_of_map_eq hJψ k]
    exact map_conj_eq_of_mem_normalizer (hAN hs) fun y => rfl
  · intro x hx
    obtain ⟨s, hs, k, hkp, hxs⟩ := hdec x
    have h2 : ∀ j ∈ J, j * (π s * (ψ ^ k) j * (π s)⁻¹)⁻¹ ∈ GLAPPrimeCoreOf p J := by
      intro j hj
      have := hx j hj
      rwa [show (Γ (x : Ω)) j = π s * (ψ ^ k) j * (π s)⁻¹ by rw [hxs, hΓx]] at this
    obtain ⟨rfl, hsA₁⟩ := hk _ hs k hkp h2
    rw [hxs, pow_zero, mul_one]
    exact ⟨s, hsA₁, rfl⟩
  · intro _
    have hfixE : J ⊓ actFix (fun x : ↥(M ⊔ Z) => Γ x) E = J ⊓ fixSubgroup ψ := by
      ext g
      simp only [Subgroup.mem_inf, mem_actFix, mem_fixSubgroup]
      constructor
      · rintro ⟨hgJ, hg⟩
        refine ⟨hgJ, ?_⟩
        have hbZ : b ∈ M ⊔ Z := Subgroup.mem_sup_right (Subgroup.mem_zpowers b)
        have := hg ⟨b, hbZ⟩ (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))
        rwa [show (Γ b) = ψ from hb] at this
      · rintro ⟨hgJ, hgψ⟩
        have hψk : ∀ k : ℕ, (ψ ^ k) g = g := fun k => by
          induction k with
          | zero => rfl
          | succ k ih => rw [pow_succ, MulAut.mul_apply, hgψ, ih]
        refine ⟨hgJ, fun x hxE => ?_⟩
        obtain ⟨d, hd, y, hy, hdy⟩ := CFSG.GH74.Uniqueness.SU.SU1.mem_sup_of_commute
          (fun d hd y hy => hMZ d (hDM hd) y hy) hxE
        obtain ⟨s, hs, rfl⟩ := exists_of_mem_map_comap hd
        obtain ⟨k, -, rfl⟩ := hZk y hy
        show Γ (x : Ω) g = g
        rw [← hdy, hΓx, hψk, (Subgroup.mem_centralizer_iff.1 (hJ.1 hgJ)) (π s) hs,
          mul_inv_cancel_right]
    rw [hfixE]
    exact hlay
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := exists_of_mem_map_comap hx
    show Γ (x : Ω) t = t
    rw [hxs, hΓs, Subgroup.mem_centralizer_singleton_iff.1 (hAt (h1 hs)), mul_inv_cancel_right]

theorem exists_involution_lift_commute (hS : S.Normal) {π : ↥S →* X} (hπ : Function.Surjective π)
    (hπZ : π.ker ≤ Subgroup.center ↥S) (hodd : Odd (Nat.card π.ker)) {Γ : Ω →* MulAut X}
    (hΓ : ∀ (b : Ω) (g : ↥S), Γ b (π g) = π ⟨b * g * b⁻¹, hS.conj_mem _ g.2 _⟩) {t : X}
    (ht2 : t ^ 2 = 1) :
    ∃ s : ↥S, π s = t ∧ s ^ 2 = 1 ∧ ∀ x : Ω, Γ x t = t → x * (s : Ω) = (s : Ω) * x := by
  classical
  haveI := hS
  set n := Nat.card π.ker with hn
  have hzn : ∀ z ∈ π.ker, z ^ n = 1 := by
    intro z hz
    have h := congrArg Subtype.val (show (⟨z, hz⟩ : π.ker) ^ n = 1 from pow_card_eq_one')
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h
    exact h
  obtain ⟨s, hs⟩ := hπ t
  have hs2 : s ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hs, ht2]
  refine ⟨s ^ n, ?_, ?_, fun x hx => ?_⟩
  · obtain ⟨m, hm⟩ := hodd
    rw [map_pow, hs, hm, pow_succ, pow_mul, ht2, one_pow, one_mul]
  · rw [← pow_mul, mul_comm n 2, pow_mul, hzn _ hs2]
  · have hconj : π (MulAut.conjNormal x s) = π s := by
      have e : MulAut.conjNormal x s = ⟨x * s * x⁻¹, hS.conj_mem _ s.2 _⟩ :=
        Subtype.ext (MulAut.conjNormal_apply x s)
      rw [e, ← hΓ, hs, hx]
    have hz : s⁻¹ * MulAut.conjNormal x s ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hconj, inv_mul_cancel]
    have hc : Commute s (s⁻¹ * MulAut.conjNormal x s) := Subgroup.mem_center_iff.1 (hπZ hz) s
    have hfix : MulAut.conjNormal x (s ^ n) = s ^ n := by
      rw [map_pow, ← mul_inv_cancel_left s (MulAut.conjNormal x s), hc.mul_pow, hzn _ hz,
        mul_one]
    have h' := congrArg Subtype.val hfix
    rw [MulAut.conjNormal_apply] at h'
    calc x * ((s ^ n : ↥S) : Ω) = x * ((s ^ n : ↥S) : Ω) * x⁻¹ * x := by group
      _ = ((s ^ n : ↥S) : Ω) * x := by rw [h']

end CFSG.LocalAnalysis.GLTheoremA.S267.ModelGen

end
