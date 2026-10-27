module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.CentralExtOdd
public import CFSG.LocalAnalysis.AGLEmbeddingD2.HSFiveCaseTwo
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
public import CFSG.Sporadic.Bridge.HSSurj
import CFSG.GroupTheory.SmallOrderNotSimple
public import CFSG.Walter.W67.CentralExt

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.AGLEmbeddingD2.CentralExt

theorem eq_three_or_five_of_sq_dvd_hs {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h : q ^ 2 ∣ 44352000) : q = 3 ∨ q = 5 := by
  have hd : q ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11 :=
    (dvd_pow_self q two_ne_zero).trans (by norm_num [h])
  have hp : ∀ {r : ℕ}, r.Prime → q ∣ r → q = r := fun hr hqr =>
    (Nat.prime_dvd_prime_iff_eq hq hr).mp hqr
  rcases (Nat.Prime.dvd_mul hq).mp hd with hd | h11
  · rcases (Nat.Prime.dvd_mul hq).mp hd with hd | h7
    · rcases (Nat.Prime.dvd_mul hq).mp hd with hd | h5
      · rcases (Nat.Prime.dvd_mul hq).mp hd with h2 | h3
        · exact absurd (hp Nat.prime_two (hq.dvd_of_dvd_pow h2)) hq2
        · exact Or.inl (hp Nat.prime_three (hq.dvd_of_dvd_pow h3))
      · exact Or.inr (hp Nat.prime_five (hq.dvd_of_dvd_pow h5))
    · rw [hp (by norm_num) h7] at h
      norm_num at h
  · rw [hp (by norm_num) h11] at h
    norm_num at h

theorem hs_multiplier_native
    (Γ : Type) [Group Γ] [Finite Γ] (ψ : Γ →* CFSG.Blueprint.NativeSporadic.HS)
    (hψ : Function.Surjective ψ) (hψker : ψ.ker ≤ Subgroup.center Γ) (z : Γ)
    (hzψ : z ∈ ψ.ker ⊓ commutator Γ) : ∃ k : ℕ, z ^ 2 ^ k = 1 := by
  have hcard : Nat.card CFSG.Blueprint.NativeSporadic.HS = 44352000 := CFSG.Sporadic.HS.card_HS
  have hodd : ∀ {q : ℕ}, q.Prime → q ∣ orderOf z → q = 2 := by
    intro q hq hqz
    by_contra hq2
    have : Fact q.Prime := ⟨hq⟩
    have hwo : orderOf (z ^ (orderOf z / q)) = q :=
      orderOf_pow_orderOf_div (orderOf_pos z).ne' hqz
    have hwz : z ^ (orderOf z / q) ∈ ψ.ker ⊓ commutator Γ := Subgroup.pow_mem _ hzψ _
    have hwp : IsPGroup q (Subgroup.zpowers (z ^ (orderOf z / q))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwo, pow_one])
    have htr : ∀ P : Sylow q Γ, IsMulCommutative (P : Subgroup Γ) →
        z ^ (orderOf z / q) = 1 := by
      intro P hP
      have h := CFSG.Walter.W67.inf_commutator_eq_bot_of_isPGroup P hP
        (Subgroup.zpowers_le.mpr (hψker hwz.1)) hwp
      have hmem : z ^ (orderOf z / q) ∈ Subgroup.zpowers (z ^ (orderOf z / q)) ⊓ commutator Γ :=
        ⟨Subgroup.mem_zpowers _, hwz.2⟩
      rwa [h, Subgroup.mem_bot] at hmem
    have hw1 : z ^ (orderOf z / q) = 1 := by
      obtain ⟨P⟩ : Nonempty (Sylow q Γ) := inferInstance
      by_cases hsq : q ^ 2 ∣ Nat.card CFSG.Blueprint.NativeSporadic.HS
      · rw [hcard] at hsq
        rcases eq_three_or_five_of_sq_dvd_hs hq hq2 hsq with rfl | rfl
        · obtain ⟨x, y, h, -, -, hxy, hc9, hhx, hhy⟩ := CFSG.SectionRank.HS_sylow3_square_witness
          refine htr P (isMulCommutative_sylow_of_square hψ hψker hxy ?_ (by simpa using hhx)
            hhy P)
          rw [hc9, hcard, CFSG.GroupTheory.factorization_eq_of_pow_dvd (k := 2) Nat.prime_three
            (by norm_num) (by norm_num) (by norm_num)]
        · obtain ⟨x, y, h, hx5, hy5, -, hzx, hzy, hc, hhx, hhy, hhz⟩ :=
            CFSG.SectionRank.HS_sylow5_cubic_witness
          have hT : (Nat.card CFSG.Blueprint.NativeSporadic.HS).factorization 5 = 3 := by
            rw [hcard]
            exact CFSG.GroupTheory.factorization_eq_of_pow_dvd Nat.prime_five (by norm_num)
              (by norm_num) (by norm_num)
          obtain ⟨C, hC, hCcard⟩ := exists_complement_of_cubic hψ hψker hx5 hy5 hzx hzy hc hT
            (by simpa using hhx) (by simpa using hhy) hhz
          exact eq_one_of_complement hψ hψker hC hCcard hwz hwp
      · exact htr P (isMulCommutative_sylow_of_not_sq_dvd hψ hψker hsq P)
    exact hq.one_lt.ne' (by rw [← hwo, hw1, orderOf_one])
  refine ⟨(orderOf z).primeFactorsList.length, ?_⟩
  rw [← Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos z).ne' hodd]
  exact pow_orderOf_eq_one z

theorem kFactHSMultiplier :
    KFactHSMultiplier := by
  intro Γ _ _ φ hφ hker z hz
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have e' : CFSG.Blueprint.NativeSporadic.HS ≃* (TauCeti.CFSGIndex.sporadic .HS).Group := e
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : Γ →* CFSG.Blueprint.NativeSporadic.HS, ∀ g, ψ g = e'.symm (φ g) :=
    ⟨MonoidHom.comp (MulEquiv.toMonoidHom e'.symm) φ, fun g => rfl⟩
  have hψ : Function.Surjective ψ := fun t => by
    obtain ⟨g, hg⟩ := hφ (e' t)
    exact ⟨g, by rw [hψdef, hg, MulEquiv.symm_apply_apply]⟩
  have hkerψ : ψ.ker = φ.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψdef]
    constructor
    · intro h
      rw [← MulEquiv.apply_symm_apply e' (φ g), h, map_one]
    · intro h
      rw [h, map_one]
  exact hs_multiplier_native Γ ψ hψ (hkerψ ▸ hker) z (hkerψ ▸ hz)

end CFSG.AGLEmbeddingD2
