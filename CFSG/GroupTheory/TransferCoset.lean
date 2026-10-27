module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.GroupTheory

open MulAction Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem not_mem_commutator_of_conj_mem_coset {p : ℕ} [Fact p.Prime]
    {P S : Subgroup G} (hPidx : ¬ p ∣ P.index)
    (hSn : (S.subgroupOf P).Normal) (hSidx : S.relIndex P = p) {y : G} (hyP : y ∈ P)
    (hyS : y ∉ S) (hyp : y ^ p = 1)
    (hfus : ∀ g : G, g * y * g⁻¹ ∈ P → y⁻¹ * (g * y * g⁻¹) ∈ S) :
    y ∉ commutator G := by
  classical
  let Q := P ⧸ S.subgroupOf P
  have hcardQ : Nat.card Q = p := by
    change Nat.card (P ⧸ S.subgroupOf P) = p
    rw [← Subgroup.index_eq_card]
    exact hSidx
  haveI : IsCyclic Q := isCyclic_of_prime_card hcardQ
  letI : CommGroup Q := IsCyclic.commGroup
  let φ : P →* Q := QuotientGroup.mk' (S.subgroupOf P)
  let V : G →* Q := φ.transfer
  have hy1 : y ≠ 1 := fun h => hyS (h ▸ S.one_mem)
  have hord : orderOf y = p := orderOf_eq_prime hyp hy1
  have hφpow : φ ⟨y, hyP⟩ ^ p = 1 := by
    rw [← map_pow]
    have h : ((⟨y, hyP⟩ : P) ^ p) = 1 := Subtype.ext (by simpa using hyp)
    rw [h, map_one]
  have hφne : φ ⟨y, hyP⟩ ≠ 1 := by
    intro h
    apply hyS
    have h1 : (⟨y, hyP⟩ : P) ∈ (QuotientGroup.mk' (S.subgroupOf P)).ker := by
      rw [MonoidHom.mem_ker]
      simpa only [φ] using h
    rw [QuotientGroup.ker_mk'] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hkey : ∀ (k : ℕ) (x : G) (hk : x⁻¹ * y ^ k * x ∈ P), k = 1 ∨ k = p →
      φ ⟨x⁻¹ * y ^ k * x, hk⟩ = φ ⟨y, hyP⟩ ^ k := by
    rintro k x hk (hk1 | hkp)
    · subst k
      have hs : y⁻¹ * (x⁻¹ * y * x) ∈ S := by
        have h := hfus x⁻¹ (by simpa [pow_one] using hk)
        simpa using h
      have hs1 : y⁻¹ * (x⁻¹ * y ^ 1 * x) ∈ S := by simpa [pow_one] using hs
      have hqmem : (⟨y, hyP⟩ : P)⁻¹ * ⟨x⁻¹ * y ^ 1 * x, hk⟩ ∈ S.subgroupOf P := by
        rw [Subgroup.mem_subgroupOf]
        simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hs1
      have heq : φ ⟨y, hyP⟩ = φ ⟨x⁻¹ * y ^ 1 * x, hk⟩ := by
        show (QuotientGroup.mk' (S.subgroupOf P)) ⟨y, hyP⟩ =
          (QuotientGroup.mk' (S.subgroupOf P)) ⟨x⁻¹ * y ^ 1 * x, hk⟩
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        exact hqmem
      rw [pow_one (φ ⟨y, hyP⟩)]
      exact heq.symm
    · subst k
      have hone : (⟨x⁻¹ * y ^ p * x, hk⟩ : P) = 1 := Subtype.ext (by simp [hyp])
      have hypP : ((⟨y, hyP⟩ : P) ^ p) = 1 := Subtype.ext (by simpa using hyp)
      rw [hone, map_one, ← map_pow, hypP, map_one]
  have hV : V y = φ ⟨y, hyP⟩ ^ P.index := by
    haveI : Fintype (Quotient (orbitRel (zpowers y) (G ⧸ P))) := Fintype.ofFinite _
    rw [show V y = φ.transfer y from rfl,
      MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
      Subgroup.index_eq_sum_minimalPeriod P y,
      ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun q _ => ?_
    have hper : Function.IsPeriodicPt (fun x : G ⧸ P => y • x) (orderOf y) q.out := by
      change (fun x : G ⧸ P => y • x)^[orderOf y] q.out = q.out
      rw [smul_iterate]
      simp [pow_orderOf_eq_one]
    have hdvd : Function.minimalPeriod (fun x : G ⧸ P => y • x) q.out ∣ p := by
      have h := hper.minimalPeriod_dvd
      rwa [hord] at h
    exact hkey _ (Quotient.out q.out) _ ((Nat.dvd_prime Fact.out).mp hdvd)
  have hVne : V y ≠ 1 := by
    rw [hV]
    intro hpow
    have hdvd : orderOf (φ ⟨y, hyP⟩) ∣ P.index := orderOf_dvd_of_pow_eq_one hpow
    have hφord : orderOf (φ ⟨y, hyP⟩) = p := orderOf_eq_prime hφpow hφne
    rw [hφord] at hdvd
    exact hPidx hdvd
  intro hycomm
  have hker : y ∈ V.ker := Abelianization.commutator_subset_ker V hycomm
  exact hVne (MonoidHom.mem_ker.mp hker)

theorem false_of_isSimpleGroup_of_conj_mem_coset [IsSimpleGroup G]
    (hnc : ∃ a b : G, a * b ≠ b * a) {p : ℕ} [Fact p.Prime]
    {P S : Subgroup G} (hPidx : ¬ p ∣ P.index)
    (hSn : (S.subgroupOf P).Normal) (hSidx : S.relIndex P = p) {y : G} (hyP : y ∈ P)
    (hyS : y ∉ S) (hyp : y ^ p = 1)
    (hfus : ∀ g : G, g * y * g⁻¹ ∈ P → y⁻¹ * (g * y * g⁻¹) ∈ S) : False := by
  have hcomm : commutator G = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hbot | htop
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have hbot' : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊥ := by
        rwa [← commutator_def]
      have hle : (⊤ : Subgroup G) ≤
          Subgroup.centralizer (↑(⊤ : Subgroup G) : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hbot'
      have ha : a ∈ Subgroup.centralizer (↑(⊤ : Subgroup G) : Set G) :=
        hle (Subgroup.mem_top a)
      exact hab ((Subgroup.mem_centralizer_iff.mp ha b (Subgroup.mem_top b)).symm)
    · exact htop
  have hy : y ∉ commutator G :=
    not_mem_commutator_of_conj_mem_coset hPidx hSn hSidx hyP hyS hyp hfus
  exact hy (hcomm ▸ Subgroup.mem_top y)

end CFSG.GroupTheory
