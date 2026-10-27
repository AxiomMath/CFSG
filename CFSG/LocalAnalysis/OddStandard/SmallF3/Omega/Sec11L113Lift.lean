module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Card

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint Equiv

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem sec113_isPGroup_zpowers {y : G} (hy : y * y = 1) : IsPGroup 2 (Subgroup.zpowers y) := by
  have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem sec113_rho_inv (hm : Sec11Model t L S z K1 K2 T Alt φ) {m : G}
    (hmM : m ∈ secM t S L) : hm.perm.rho m⁻¹ = (hm.perm.rho m)⁻¹ := by
  have h := hm.perm.rho_mul ((secM t S L).inv_mem hmM) hmM
  rw [inv_mul_cancel, hm.perm.rho_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem sec113_lift [Finite G] {R : Subgroup G} (hctx : Sec11Ctx G t L S z K1 K2 T R)
    (hm : Sec11Model t L S z K1 K2 T Alt φ) {P : Perm (Fin 6) → Prop}
    (hP : ∀ σ τ : Perm (Fin 6), ((σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) → P τ →
      P (σ * τ * σ⁻¹))
    {y : G} (hyM : y ∈ secM t S L) (hy2 : y * y = 1)
    (hyT : hm.perm.rho y ∈ sec113Tstar hm (sec113_T_le_M hctx)) (hPy : P (hm.perm.rho y)) :
    ∃ x ∈ T, x * x = 1 ∧ P (hm.perm.rho x) := by
  have hTM := sec113_T_le_M hctx
  set U : Subgroup G := ((sec113Tstar hm hTM).comap hm.perm.rhoHom).map (secM t S L).subtype
    with hU
  have hmemU : ∀ m : G, m ∈ U ↔ m ∈ secM t S L ∧ hm.perm.rho m ∈ sec113Tstar hm hTM := by
    intro m
    constructor
    · rintro ⟨⟨m', hm'⟩, hmc, rfl⟩
      exact ⟨hm', hmc⟩
    · rintro ⟨hmM, hmT⟩
      exact ⟨⟨m, hmM⟩, hmT, rfl⟩
  have hTU : T ≤ U := fun x hx =>
    (hmemU x).2 ⟨hTM hx, (mem_sec113Tstar hm hTM).2 ⟨x, hx, rfl⟩⟩
  have hUM : U ≤ secM t S L := fun m hm' => ((hmemU m).1 hm').1
  have hyU : y ∈ U := (hmemU y).2 ⟨hyM, hyT⟩
  have hSylT : IsSylow2Of T U := by
    refine ⟨hTU, hctx.sylowT.2.1, ?_⟩
    intro h2
    apply hctx.sylowT.2.2
    rw [← Subgroup.relIndex_mul_relIndex T U (secM t S L) hTU hUM]
    exact Dvd.dvd.mul_right h2 _
  obtain ⟨Q', hQ'syl, hyQ'⟩ := exists_isSylow2Of_ge (sec113_isPGroup_zpowers hy2)
    (Subgroup.zpowers_le.mpr hyU)
  obtain ⟨u, huU, hu⟩ := hSylT.exists_conj_mem hQ'syl
  have hx0T : u⁻¹ * y * u ∈ T := (hu y).1 (hyQ' (Subgroup.mem_zpowers y))
  refine ⟨u⁻¹ * y * u, hx0T, ?_, ?_⟩
  · calc u⁻¹ * y * u * (u⁻¹ * y * u) = u⁻¹ * (y * y) * u := by group
      _ = 1 := by rw [hy2]; group
  · have huM : u ∈ secM t S L := hUM huU
    have hu'M : u⁻¹ ∈ secM t S L := (secM t S L).inv_mem huM
    have hu'T : hm.perm.rho u⁻¹ ∈ sec113Tstar hm hTM := ((hmemU u⁻¹).1 (U.inv_mem huU)).2
    have hρ : hm.perm.rho (u⁻¹ * y * u) =
        hm.perm.rho u⁻¹ * hm.perm.rho y * (hm.perm.rho u⁻¹)⁻¹ := by
      rw [hm.perm.rho_mul ((secM t S L).mul_mem hu'M hyM) huM, hm.perm.rho_mul hu'M hyM]
      congr 1
      have h := sec113_rho_inv hm hu'M
      rw [inv_inv] at h
      exact h
    rw [hρ]
    exact hP _ _ (sec113_Tstar_pres hm hTM hu'T) hPy

end CFSG.OddStandard.SmallF3.Omega
