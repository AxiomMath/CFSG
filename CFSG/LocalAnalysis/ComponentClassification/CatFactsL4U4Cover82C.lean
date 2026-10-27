module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover82B
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover82P
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4AltCentC

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Cover82

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.GSThmB

theorem ne_bot_of_isPComponent_subgroupOf {X : Type*} [Group X] {C K : Subgroup X}
    (hK : IsPComponent 2 (K.subgroupOf C)) : K ≠ ⊥ := by
  rintro rfl
  rw [bot_subgroupOf] at hK
  obtain ⟨K', hK', -, hmap, -⟩ := hK
  rw [Subgroup.map_bot] at hmap
  subst hmap
  obtain ⟨⟨-, hs, -⟩, -⟩ := hK'
  obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
  apply hab
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  congr 1
  exact Subsingleton.elim _ _

theorem eq_one_of_central_pow {X : Type*} [Group X] [Finite X]
    (hZ : center (X ⧸ pPrimeCore 2 X) = ⊥) {w : X} (hw : w ∈ center X) {k : ℕ}
    (hk : w ^ 2 ^ k = 1) : w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : w ∈ pPrimeCore 2 X := by
    rw [← QuotientGroup.eq_one_iff, ← mem_bot, ← hZ, mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hw g]
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := pPrimeCore_coprime_card
  have h1 : orderOf (⟨w, hO⟩ : pPrimeCore 2 X) ∣ Nat.card (pPrimeCore 2 X) :=
    orderOf_dvd_natCard _
  have h2 : orderOf (⟨w, hO⟩ : pPrimeCore 2 X) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    rw [SubgroupClass.coe_pow]
    exact hk
  have h3 : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 X)) := Nat.Coprime.pow_left k hcop
  have h4 := Nat.dvd_gcd h2 h1
  rw [h3.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact congrArg Subtype.val h4

theorem a10CoverComponents_of (hLift : A10DoubleTransLift) : A10CoverComponents := by
  intro Y _ _ hYq hYZ hA y₀ hy₀Z hy₀2 M hMC hMcomp hZM
  classical
  obtain ⟨e⟩ := hA
  set ψ : Y →* Perm (Fin 10) := (alternatingGroup (Fin 10)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (center Y))) with hψ
  have hψe : ∀ y, ψ y = ((e (QuotientGroup.mk y) : alternatingGroup (Fin 10)) :
      Perm (Fin 10)) := fun y => rfl
  have hψker : ∀ y, ψ y = 1 ↔ y ∈ center Y := by
    intro y
    rw [hψe, OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hψA : ∀ y, ψ y ∈ alternatingGroup (Fin 10) := fun y => (e (QuotientGroup.mk y)).2
  set π := ψ y₀ with hπ
  have hπ2 : π * π = 1 := by
    rw [hπ, ← map_mul, ← sq]
    exact (hψker _).mpr hy₀2
  have hπ1 : π ≠ 1 := fun h => hy₀Z ((hψker y₀).mp h)
  have hMp : ⁅M, M⁆ = M := commutator_eq_self_of_isPComponent hMC hMcomp
  have hMne : M ≠ ⊥ := ne_bot_of_isPComponent_subgroupOf hMcomp
  set X := M.map ψ with hX
  have hXp : ⁅X, X⁆ = X := by rw [hX, ← map_commutator, hMp]
  have hXπ : ∀ x ∈ X, x * π = π * x := by
    rintro _ ⟨m, hm, rfl⟩
    rw [hπ, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp (hMC hm)]
  have hXne : X ≠ ⊥ := by
    intro hXb
    apply hMne
    have hMZ : M ≤ center Y := fun m hm => (hψker m).mp (by
      have : ψ m ∈ X := ⟨m, hm, rfl⟩
      rwa [hXb, mem_bot] at this)
    rw [← hMp, commutator_eq_bot_iff_le_centralizer]
    exact hMZ.trans (center_le_centralizer _)
  have hsupp : π.support.card = 4 := by
    rcases AZ.support_card_of_alt_involution (show π ∈ alternatingGroup (Fin 10) from hψA y₀)
      hπ2 hπ1 with h | h
    · exact h
    · exact absurd (eq_bot_of_perfect_of_card_support hXp hXπ hπ2 (by omega) (by omega)) hXne
  have hXfix := AltCent.fixes_support_of_perfect hXp hXπ (by omega)
  have : Nontrivial ↥X := X.nontrivial_iff_ne_bot.mpr hXne
  have hperf : Group.IsPerfect ↥X := Subgroup.isPerfect_iff.mpr hXp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨x, hxX⟩, hx2⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 2
    (two_dvd_card_of_perfect hperf)
  rw [Subgroup.orderOf_mk] at hx2
  have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx2
    norm_num at hx2
  have hxA : x ∈ alternatingGroup (Fin 10) := AltCent.le_alternatingGroup_of_perfect hXp hxX
  have hxsupp : x.support.card = 4 := by
    have hle : x.support ⊆ π.supportᶜ := by
      intro a ha
      rw [Finset.mem_compl]
      intro haπ
      exact (mem_support.mp ha) (hXfix x hxX a haπ)
    have h6 := Finset.card_le_card hle
    rw [Finset.card_compl, Fintype.card_fin, hsupp] at h6
    rcases AZ.support_card_of_alt_involution hxA hxx hx1 with h | h
    · exact h
    · omega
  have hxk : Multiset.card x.cycleType = 2 := by
    have h1 := sum_cycleType x
    rw [Idx.cycleType_eq_replicate hxx, Multiset.sum_replicate, smul_eq_mul, hxsupp] at h1
    omega
  obtain ⟨a, b, c, d, hn, hxd, -⟩ := AltCent.exists_dt hxx hxk
  obtain ⟨m, hmM, hmx⟩ := hxX
  obtain ⟨k, n, hnodd, hk⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
  have hψm₂ : ψ (m ^ n) = x := by
    rw [map_pow, hmx]
    obtain ⟨j, rfl⟩ := hnodd
    rw [pow_succ, pow_mul, sq, hxx, one_pow, one_mul]
  have hw1 : (m ^ n) ^ 2 ≠ 1 :=
    hLift Y hYq hYZ e (m ^ n) a b c d hn (by rw [← hψe, hψm₂, hxd])
  have hwZ : (m ^ n) ^ 2 ∈ center Y :=
    (hψker _).mp (by rw [map_pow, hψm₂, sq, hxx])
  have hwM : (m ^ n) ^ 2 ∈ M := pow_mem (pow_mem hmM n) 2
  have hw2k : ((m ^ n) ^ 2) ^ 2 ^ k = 1 := by
    rw [← pow_mul, ← pow_mul, show n * (2 * 2 ^ k) = 2 * (2 ^ k * n) by ring, pow_mul', ← hk,
      pow_orderOf_eq_one, one_pow]
  apply hw1
  have hwc : (⟨(m ^ n) ^ 2, hwM⟩ : ↥M) ∈ center ↥M := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_center_iff.mp hwZ g)
  have h1 := eq_one_of_central_pow hZM hwc (k := k) (Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hw2k))
  exact congrArg Subtype.val h1

theorem cf82Cover_of_lift (hMult : MultiplierL4U4) (hLift : A10DoubleTransLift) : CF82Cover :=
  cf82Cover_of hMult (a10CoverComponents_of hLift)

end Cover82

end CFSG.ComponentClassification.CatFactsL4U4
