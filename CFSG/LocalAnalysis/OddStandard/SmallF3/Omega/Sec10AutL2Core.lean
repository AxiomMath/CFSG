module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10AutL2Count
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHarrisT

public section

namespace CFSG.OddStandard.SmallF3.Omega.AutL2

open CFSG.ComponentClassification.AutL2Facts CFSG.GorensteinWalter Subgroup

variable {F : Type} [Field F] [Finite F]

theorem card_le_sixteen (hH : HarrisHyp F) (hF : Nat.card F = 3 ^ 4)
    {A : Subgroup (PGammaL2 F)} (hA : A ≤ sylS0 F) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card A ≤ 16 := by
  have hmul := Subgroup.card_ker_mul_card_range (projHom A)
  have hdvd : Nat.card (projHom A).range ∣ 4 :=
    card_ringAut_eq_four hF ▸ Subgroup.card_subgroup_dvd_card _
  rw [← hmul]
  by_cases hR : ∃ c : Fˣ, nm F c true 1 ∈ A
  · obtain ⟨c, ht⟩ := hR
    calc Nat.card (projHom A).ker * Nat.card (projHom A).range ≤ 4 * 4 :=
          Nat.mul_le_mul (card_ker_le_four hA hc ht) (Nat.le_of_dvd (by norm_num) hdvd)
      _ = 16 := by norm_num
  · push Not at hR
    haveI := isCyclic_ringAut F
    obtain ⟨⟨σ, hσR⟩, hgen⟩ := IsCyclic.exists_generator (α := ↥(projHom A).range)
    have hord : orderOf σ = Nat.card (projHom A).range := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hgen, ← Subgroup.orderOf_coe]
    obtain ⟨e, he, hRe⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card (projHom A).range ∣ 2 ^ 2 by simpa using hdvd)
    obtain ⟨g, hg⟩ := hσR
    obtain ⟨b, -, ε, σ', -, hgeq⟩ := hA g.2
    have hσ' : σ' = σ := by rw [← hg, projHom_apply, hgeq]; rfl
    have hker : Nat.card (projHom A).ker ≤ 2 ^ (4 - e) := by
      haveI : NeZero (2 ^ (4 - e)) := ⟨by positivity⟩
      refine card_ker_le_pow hA hR fun a hx => ?_
      have hcomm := hc _ hx _ g.2
      rw [hgeq] at hcomm
      exact rot_pow_eq_one hH hF (mem_zpowers_of_nm_mem hA hx) (e := e) (σ := σ')
        (by rw [hσ', hord, hRe]) (rot_fix_or_inv hcomm)
    rw [hRe]
    calc Nat.card (projHom A).ker * 2 ^ e ≤ 2 ^ (4 - e) * 2 ^ e := Nat.mul_le_mul_right _ hker
      _ = 2 ^ 4 := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
      _ = 16 := by norm_num

theorem card_le_sixteen_of_isPGroup (hH : HarrisHyp F) (hF : Nat.card F = 3 ^ 4)
    {A : Subgroup (PGammaL2 F)} (hp : IsPGroup 2 A) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) :
    Nat.card A ≤ 16 := by
  have hS := hH.isSylowIn_stdTS (K := ⊤) le_top
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  have hQS : IsSylowIn (Q : Subgroup (PGammaL2 F)) ⊤ :=
    ⟨le_top, Q.isPGroup', fun Q' _ h1 h2 => Q.is_maximal' h1 h2⟩
  obtain ⟨g, -, hg⟩ := hS.exists_conj hQS
  have hBS : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ sylS0 F := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : x ∈ (stdTS F ⊤).map (MulAut.conj g).toMonoidHom := hg ▸ hQ hx
    obtain ⟨s, hs, hsx⟩ := hxQ
    have : (MulAut.conj g⁻¹).toMonoidHom x = s := by
      rw [← hsx]
      simp [MulAut.conj_apply]
      group
    rw [this]
    exact hs.1
  have hBc : ∀ x ∈ A.map (MulAut.conj g⁻¹).toMonoidHom, ∀ y ∈ A.map (MulAut.conj g⁻¹).toMonoidHom,
      x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  have h := card_le_sixteen hH hF hBS hBc
  rwa [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at h

end CFSG.OddStandard.SmallF3.Omega.AutL2
