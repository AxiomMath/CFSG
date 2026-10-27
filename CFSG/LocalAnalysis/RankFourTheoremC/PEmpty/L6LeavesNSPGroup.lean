module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesDeltaCyc
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNS

open Subgroup CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6Delta

theorem normal_zpowers_of_central {G : Type} [Group G] {c : G} (hc : ∀ g : G, g * c = c * g) :
    (zpowers c).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have h : g * c ^ k * g⁻¹ = c ^ k := by
    have hcm : Commute g (c ^ k) := Commute.zpow_right (hc g) k
    rw [hcm.eq]
    group
  rw [h]
  exact Subgroup.zpow_mem_zpowers _ _

theorem sylow_centralizer_x_abelian {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) {Q B : Subgroup G} {x : G} (hQ : IsPGroup p Q) (hxQ : x ∈ Q)
    (hxc : ∀ q ∈ Q, q * x = x * q) (hxo : orderOf x = p)
    (hxfr : x ∉ (frattini ↥Q).map Q.subtype) (hBQ : B ≤ Q) (hBc : Nat.card B = p ^ 2)
    (hxB : x ∈ B) (hΩ : ∀ q ∈ Q, q ^ p = 1 → q ∈ B) :
    ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  classical
  set x' : ↥Q := ⟨x, hxQ⟩ with hx'
  have hx'fr : x' ∉ frattini ↥Q := fun h => hxfr ⟨x', h, rfl⟩
  obtain ⟨T, hTc, hxT⟩ := exists_coatom_not_mem_of_not_mem_frattini hx'fr
  set T' : Subgroup G := T.map Q.subtype with hT'
  have hT'Q : T' ≤ Q := Subgroup.map_subtype_le T
  have hxT' : x ∉ T' := by
    rintro ⟨y, hy, hyx⟩
    exact hxT (by rwa [show y = x' from Subtype.ext hyx] at hy)
  have hT'p : IsPGroup p T' := hQ.to_le hT'Q
  have hTcyc : IsCyclic ↥T' := by
    by_cases hT'bot : T' = ⊥
    · have : Subsingleton ↥T' := by
        rw [hT'bot]
        infer_instance
      exact isCyclic_of_subsingleton
    · have hcard : Nat.card ↥(B ⊓ T') = p :=
        card_inf_eq_prime B T' hBc hT'p hT'bot
          (fun g hg hgp => hΩ g (hT'Q hg) hgp) ⟨x, hxB, hxT'⟩
      refine isCyclic_of_pow_eq_one_mem hp2 hT'p ((B ⊓ T').subgroupOf T') ?_ ?_
      · rw [← hcard]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
      · intro g hg
        have hg' : (g : G) ^ p = 1 := by simpa using congrArg Subtype.val hg
        exact (Subgroup.mem_subgroupOf).2 ⟨hΩ g (hT'Q g.2) hg', g.2⟩
  have hTcomm : ∀ s t : ↥Q, s ∈ T → t ∈ T → s * t = t * s := by
    intro s t hs ht
    have hs' : (s : G) ∈ T' := ⟨s, hs, rfl⟩
    have ht' : (t : G) ∈ T' := ⟨t, ht, rfl⟩
    haveI := hTcyc
    have h2 := comm_of_isCyclic (G := ↥T') ⟨s, hs'⟩ ⟨t, ht'⟩
    have h3 : (s : G) * t = t * s := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hx'c : ∀ g : ↥Q, g * x' = x' * g := fun g => Subtype.ext (hxc g g.2)
  have hZn : (zpowers x').Normal := normal_zpowers_of_central hx'c
  have htop : T ⊔ zpowers x' = ⊤ := by
    refine hTc.2 _ (lt_of_le_of_ne le_sup_left fun h => hxT ?_)
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x')
  have hdec : ∀ a : ↥Q, ∃ t ∈ T, ∃ k : ℤ, a = t * x' ^ k := by
    intro a
    have ha : a ∈ T ⊔ zpowers x' := htop ▸ Subgroup.mem_top a
    obtain ⟨t, ht, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ⟨t, ht, k, rfl⟩
  intro a ha b hb
  obtain ⟨t₁, ht₁, i, hi⟩ := hdec ⟨a, ha⟩
  obtain ⟨t₂, ht₂, j, hj⟩ := hdec ⟨b, hb⟩
  have key : (⟨a, ha⟩ : ↥Q) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
    rw [hi, hj, Commute.mul_mul_mul_comm (Commute.zpow_right (hx'c t₂) i).symm,
      Commute.mul_mul_mul_comm (Commute.zpow_right (hx'c t₁) j).symm, hTcomm t₁ t₂ ht₁ ht₂,
      (Commute.zpow_zpow_self x' i j).eq]
  exact congrArg Subtype.val key

open scoped IsMulCommutative in
theorem transfer_center_commutator {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    {P : Subgroup X} (hP : IsPGroup p P) (hPidx : ¬ p ∣ P.index)
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {g : X} (hgP : g ∈ P) (hgZ : g ∈ center X)
    (hgc : g ∈ commutator X) : g = 1 := by
  haveI : IsMulCommutative ↥P := ⟨⟨fun a b => Subtype.ext (hPab a a.2 b b.2)⟩⟩
  haveI : P.FiniteIndex := inferInstance
  let T : X →* ↥P := MonoidHom.transfer (MonoidHom.id ↥P)
  have h1 : T g = 1 := MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker T hgc)
  have hkey : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * g ^ k * g₀ ∈ P → g₀⁻¹ * g ^ k * g₀ = g ^ k := by
    intro k g₀ _
    have h := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hgZ k) g₀⁻¹
    rw [h, mul_assoc, inv_mul_cancel, mul_one]
  have h2 : T g = ⟨g ^ P.index, MonoidHom.transfer_eq_pow_aux g hkey⟩ :=
    MonoidHom.transfer_eq_pow (MonoidHom.id ↥P) g hkey
  have h3 : g ^ P.index = 1 := by
    have := congrArg Subtype.val (h2.symm.trans h1)
    simpa using this
  obtain ⟨n, hn⟩ := hP ⟨g, hgP⟩
  have hgn : g ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hd1 : orderOf g ∣ P.index := orderOf_dvd_of_pow_eq_one h3
  have hd2 : orderOf g ∣ p ^ n := orderOf_dvd_of_pow_eq_one hgn
  have hcop : Nat.Coprime (p ^ n) P.index :=
    Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hPidx)
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd2 hcop) hd1)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNS
