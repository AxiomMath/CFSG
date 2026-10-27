module

public import Mathlib.Tactic.NormNum.Prime
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48TI

public section

namespace CFSG.HardMathSupport.Malle.Coordinator

variable {G : Type*} [Group G] [Finite G]

theorem le_of_isPGroup_of_not_dvd {p : ℕ} [Fact p.Prime] {P H M : Subgroup G} (hPH : P ≤ H)
    (hHM : H ≤ M) (hH : IsPGroup p H) (hPM : ¬ p ∣ P.relIndex M) : H ≤ P := by
  obtain ⟨k, hk⟩ := hH.index (P.subgroupOf H)
  have hrel : P.relIndex H = p ^ k := hk
  have hmul := Subgroup.relIndex_mul_relIndex P H M hPH hHM
  rcases k with _ | k
  · exact Subgroup.relIndex_eq_one.mp (by simpa using hrel)
  · exact absurd (Dvd.intro _ (by rw [← hmul, hrel, pow_succ, mul_comm (p ^ k), mul_assoc]))
      hPM

theorem mem_of_pElement_of_not_dvd {p : ℕ} [Fact p.Prime] {P M : Subgroup G} (hP : IsPGroup p P)
    (hPM' : P ≤ M) (hPM : ¬ p ∣ P.relIndex M) {y : G} (hyM : y ∈ M)
    (hyN : y ∈ Subgroup.normalizer (P : Set G)) (hy : ∃ m : ℕ, y ^ (p ^ m) = 1) : y ∈ P := by
  have hz : IsPGroup p (Subgroup.zpowers y) := by
    obtain ⟨m, hm⟩ := hy
    obtain ⟨j, -, hj⟩ :=
      (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp (orderOf_dvd_of_pow_eq_one hm)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hle : Subgroup.zpowers y ≤ Subgroup.normalizer (P : Set G) :=
    (Subgroup.zpowers_le).mpr hyN
  have hsup := IsPGroup.to_sup_of_normal_right' hz hP hle
  have hle' : Subgroup.zpowers y ⊔ P ≤ P :=
    le_of_isPGroup_of_not_dvd le_sup_right (sup_le ((Subgroup.zpowers_le).mpr hyM) hPM') hsup hPM
  exact hle' (le_sup_left (b := P) (Subgroup.mem_zpowers y))

omit [Finite G] in
theorem exists_pow_orderOf_eq_prime {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) {g : G} (hg : g ∈ P) (hg1 : g ≠ 1) :
    ∃ k : ℕ, orderOf (g ^ (p ^ k)) = p := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨g, hg⟩
  have hn' : orderOf g = p ^ n := by rwa [Subgroup.orderOf_mk] at hn
  rcases n with _ | n
  · exact absurd (orderOf_eq_one_iff.mp (by simpa using hn')) hg1
  · refine ⟨n, ?_⟩
    have hdvd : p ^ n ∣ orderOf g := by
      rw [hn']
      exact pow_dvd_pow p (Nat.le_succ n)
    rw [orderOf_pow_of_dvd (pow_ne_zero n hp.out.ne_zero) hdvd, hn', pow_succ,
      Nat.mul_div_cancel_left _ (pow_pos hp.out.pos n)]

theorem ti_of_centralizer_le {p : ℕ} [Fact p.Prime] {P M : Subgroup G} (hPM' : P ≤ M)
    (hP : IsPGroup p P) (hPM : ¬ p ∣ P.relIndex M) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hC : ∀ x ∈ P, orderOf x = p → ∀ g ∈ M, g * x = x * g →
      g ∈ Subgroup.normalizer (P : Set G)) :
    ∀ a ∈ M, a ∉ Subgroup.normalizer (P : Set G) → ∀ g ∈ P, a⁻¹ * g * a ∈ P → g = 1 := by
  intro a haM haN g hg hga
  by_contra hg1
  obtain ⟨k, hk⟩ := exists_pow_orderOf_eq_prime hP hg hg1
  set x := g ^ (p ^ k) with hx
  have hxP : x ∈ P := P.pow_mem hg _
  have hxa : a⁻¹ * x * a ∈ P := by
    have : a⁻¹ * x * a = (a⁻¹ * g * a) ^ (p ^ k) := by
      simpa [hx] using (conj_pow (a := a⁻¹) (b := g) (i := p ^ k)).symm
    rw [this]
    exact P.pow_mem hga _
  set Q := P.map (MulAut.conj a).toMonoidHom with hQ
  have hmemQ : ∀ y, y ∈ Q ↔ a⁻¹ * y * a ∈ P := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hz
    · intro hy
      exact ⟨a⁻¹ * y * a, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hQN : Q ≤ Subgroup.normalizer (P : Set G) := by
    intro y hy
    have hyM : y ∈ M := by
      have h1 := (hmemQ y).mp hy
      have : y = a * (a⁻¹ * y * a) * a⁻¹ := by group
      rw [this]
      exact M.mul_mem (M.mul_mem haM (hPM' h1)) (M.inv_mem haM)
    refine hC x hxP hk y hyM ?_
    have h1 := hab _ ((hmemQ y).mp hy) _ hxa
    calc y * x = a * ((a⁻¹ * y * a) * (a⁻¹ * x * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * x * a) * (a⁻¹ * y * a)) * a⁻¹ := by rw [h1]
      _ = x * y := by group
  have hQp : IsPGroup p Q := hP.map _
  have hsup := IsPGroup.to_sup_of_normal_right' hQp hP hQN
  have hQM : Q ≤ M := by
    rintro _ ⟨z, hz, rfl⟩
    exact M.mul_mem (M.mul_mem haM (hPM' hz)) (M.inv_mem haM)
  have hQP : Q ≤ P :=
    le_sup_left.trans (le_of_isPGroup_of_not_dvd le_sup_right (sup_le hQM hPM') hsup hPM)
  have hcard : Nat.card Q = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj a).injective
  have hQeq : Q = P := Subgroup.eq_of_le_of_card_ge hQP hcard.ge
  apply haN
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have : a * h * a⁻¹ ∈ Q := ⟨h, hh, rfl⟩
    rwa [hQeq] at this
  · intro hh
    rw [← hQeq] at hh
    have := (hmemQ _).mp hh
    simpa [mul_assoc] using this

theorem relIndex_modEq_one_of_centralizer_le {p : ℕ} [Fact p.Prime] {P M : Subgroup G}
    (hPM' : P ≤ M) (hP : IsPGroup p P) (hPM : ¬ p ∣ P.relIndex M)
    (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a)
    (hC : ∀ x ∈ P, orderOf x = p → ∀ g ∈ M, g * x = x * g →
      g ∈ Subgroup.normalizer (P : Set G)) :
    (M ⊓ Subgroup.normalizer (P : Set G)).relIndex M ≡ 1 [MOD Nat.card P] := by
  set N := M ⊓ Subgroup.normalizer (P : Set G) with hN
  have hPN : P ≤ N := le_inf hPM' Subgroup.le_normalizer
  have h := CFSG.AGLEmbedding.KFactProofs.Sp48.relIndex_modEq_of_ti (p := p) M P N N hPN le_rfl
    inf_le_left hP
    (fun y hy hy3 => mem_of_pElement_of_not_dvd hP hPM' hPM hy.1 hy.2 hy3)
    (fun a haM haN g hg hga => ti_of_centralizer_le hPM' hP hPM hab hC a haM
      (fun h => haN ⟨haM, h⟩) g hg hga)
  rwa [Subgroup.relIndex_self] at h

end CFSG.HardMathSupport.Malle.Coordinator
