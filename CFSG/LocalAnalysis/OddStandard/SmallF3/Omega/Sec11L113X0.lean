module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L113Seed

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint Equiv

variable {G : Type} [Group G] {t : G} {L S : Subgroup G} {z : G} {K1 K2 T : Subgroup G}
  {Alt : Subgroup (Perm (Fin 6))} {φ : (Fin 6 → ZMod 2) → G}

theorem sec113_exists_x0_A [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hm : Sec11Model t L S z K1 K2 T Alt φ)
    (hAlt : Alt = alternatingGroup (Fin 6)) :
    ∃ x ∈ T, x * x = 1 ∧ Sec113TypeA (hm.perm.rho x) := by
  have hTM := sec113_T_le_M hctx
  obtain ⟨τ, hτT, hτ⟩ :=
    sec113_exists_tau_A hm hTM (sec113_Q_le_T hp hctx) (sec113_A_le_T hp hctx) hAlt
  obtain ⟨y0, hy0M, hy02, hρy0⟩ := sec113_seedA hp hctx hm
  obtain ⟨g, hg, hgτ⟩ := sec113_conjA6 hτ
  obtain ⟨y1, hy1M, hy12, hρy1⟩ :=
    sec113_conj_seed hm hy0M hy02 (τ := τ) (hAlt.ge hg) (by rw [hρy0]; exact hgτ)
  exact sec113_lift hctx hm (fun σ _ h hτ' => hτ'.conj h) hy1M hy12
    (by rw [hρy1]; exact hτT) (by rw [hρy1]; exact hτ)

theorem sec113_exists_x0_S [Finite G] (hp : Asc82Pre11) {R : Subgroup G}
    (hctx : Sec11Ctx G t L S z K1 K2 T R) (hm : Sec11Model t L S z K1 K2 T Alt φ)
    (hAlt : Alt = ⊤) {r : G} (hr2 : r * r = 1) (hrT : r ∈ T)
    (hract : ∀ v, r * φ v * r⁻¹ = φ (permVec (swap 0 1) v)) :
    ∃ x ∈ T, x * x = 1 ∧ Sec113TypeS (hm.perm.rho x) := by
  have hTM := sec113_T_le_M hctx
  have hrM : r ∈ secM t S L := hTM hrT
  have hρr : hm.perm.rho r = swap 0 1 := hm.perm.rho_eq hrM _ hract
  have h01 : swap (0 : Fin 6) 1 ∈ sec113Tstar hm hTM :=
    (mem_sec113Tstar hm hTM).2 ⟨r, hrT, hρr⟩
  obtain ⟨τ, hτT, hτ⟩ := sec113_exists_tau_S hm hTM (sec113_Q_le_T hp hctx)
    (sec113_A_le_T hp hctx) hAlt h01
  obtain ⟨g, hgτ⟩ := sec113_conjS6 hτ
  obtain ⟨y1, hy1M, hy12, hρy1⟩ := sec113_conj_seed hm hrM hr2 (τ := τ)
    (hAlt.ge (Subgroup.mem_top g)) (by rw [hρr]; exact hgτ)
  exact sec113_lift hctx hm (fun σ _ h hτ' => hτ'.conj h) hy1M hy12
    (by rw [hρy1]; exact hτT) (by rw [hρy1]; exact hτ)

end CFSG.OddStandard.SmallF3.Omega
