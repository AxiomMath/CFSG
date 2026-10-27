module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDForward
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDSetU
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDSwapLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDShape
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDConj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDExist
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {G : Type} [Group G] {L : Subgroup G}

private theorem sec4FD_glue_facts [Finite G] (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) (hσ : quadSign Q = 1) {s : G} {t : OGroup Q}
    (ht6 : invType t = (6, 1)) {ρ : ↥L →* ↥(omegaGroup hQ)}
    (h : Sec4FDCover L s (omegaGroup hQ) t ρ) (v : G) (hvL : v ∈ L) (hvs : v * s = s * v)
    (hvord : orderOf v = 2) (K : Subgroup G)
    (hK : IsComponentIn K (L ⊓ centralizer ({s} : Set G) ⊓ centralizer ({v} : Set G)))
    (hlie : LieModel (↥K ⧸ oddCore ↥K) .PSp 2 3 1) :
    ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) ∈ Sec4FDDt hQ t ∧
      ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) *
          ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) = 1 ∧
      ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) ≠ 1 ∧
      (invType ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) = (2, -1) ∨
        invType ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) = (6, -1)) ∧
      fixSp t ≤ commSp ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) := by
  haveI : NeZero (2 : ZMod 3) := ⟨(isUnit_of_invertible (2 : ZMod 3)).ne_zero⟩
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have hvv : v * v = 1 := by
    have h1 := pow_orderOf_eq_one v
    rw [hvord, pow_two] at h1
    exact h1
  have hvvL : (⟨v, hvL⟩ : ↥L) * ⟨v, hvL⟩ = 1 := Subtype.ext (by simpa using hvv)
  have hcomm : ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) * t =
      t * ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) :=
    Sec4FDCover.image_comm h hvL hvs
  have hmemX : ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) ∈ omegaGroup hQ :=
    (ρ ⟨v, hvL⟩).2
  have hmemD : ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) ∈ Sec4FDDt hQ t :=
    (mem_sec4FDDt_iff hQ).mpr ⟨hmemX, hcomm⟩
  have huu_sub : ρ (⟨v, hvL⟩ : ↥L) * ρ (⟨v, hvL⟩ : ↥L) = 1 := by
    rw [← map_mul, hvvL, map_one]
  have huu : ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) *
      ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) = 1 := by
    have h1 := congrArg (fun z : ↥(omegaGroup hQ) => ((z : OGroup Q))) huu_sub
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h1
  have hu1 : ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) ≠ 1 := by
    intro hone
    have hρ1 : ρ (⟨v, hvL⟩ : ↥L) = 1 := by
      apply Subtype.ext
      simpa using hone
    have hker : (⟨v, hvL⟩ : ↥L) ∈ ρ.ker := MonoidHom.mem_ker.mpr hρ1
    have hvone : (⟨v, hvL⟩ : ↥L) = 1 := h.cover.eq_one_of_mul_self_eq_one hker hvvL
    have hv1 : v = 1 := by simpa using congrArg Subtype.val hvone
    have h2 := hvord
    rw [hv1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hdvd : 25920 ∣ Nat.card ↥(Sec4FDDt hQ t ⊓
      Subgroup.centralizer ({((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q)} :
        Set (OGroup Q))) := by
    have h1 := h.dvd_of_component (X := omegaGroup hQ) (Pr := OGroup Q) hvL hK hlie
    simpa only [Sec4FDDt] using h1
  obtain ⟨htypes, hF⟩ :=
    sec4FD_shape hQ hdim hσ h.y_sq ht6 hmemD huu hu1 hdvd
  exact ⟨hmemD, huu, hu1, htypes, hF⟩

theorem sec4FD_concl_of_model [Finite G] (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 7) (hσ : quadSign Q = 1) {s : G} {t : OGroup Q}
    (ht6 : invType t = (6, 1)) {ρ : ↥L →* ↥(omegaGroup hQ)}
    (h : Sec4FDCover L s (omegaGroup hQ) t ρ)
    (htype : ∀ (v : G) (hvL : v ∈ L), v * v = 1 → ∀ (r : ℕ) (α : ℤˣ),
      (r = 2 ∨ r = 4 ∨ r = 6) →
        (InducesTypeSome L v 7 1 r α ↔
          invType ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) = (r, α))) :
    Sec4FDConcl L s (L ⊓ centralizer ({s} : Set G)) := by
  haveI : NeZero (2 : ZMod 3) := ⟨(isUnit_of_invertible (2 : ZMod 3)).ne_zero⟩
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  have htt : t * t = 1 := h.y_sq
  unfold Sec4FDConcl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨hvD, hvord, K, hK, hlie⟩ := hv
    have hvL : v ∈ L := (Subgroup.mem_inf.mp hvD).1
    have hvs : v * s = s * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hvD).2
    have hvv : v * v = 1 := by
      have h1 := pow_orderOf_eq_one v
      rw [hvord, pow_two] at h1
      exact h1
    obtain ⟨-, -, -, htypes, -⟩ :=
      sec4FD_glue_facts hQ hdim hσ ht6 h v hvL hvs hvord K hK hlie
    rcases htypes with h2 | h6
    · exact Or.inl ((htype v hvL hvv 2 (-1) (Or.inl rfl)).mpr h2)
    · exact Or.inr ((htype v hvL hvv 6 (-1) (Or.inr (Or.inr rfl))).mpr h6)
  · intro v v' hv hv' hsame
    obtain ⟨hvD, hvord, K, hK, hlie⟩ := hv
    obtain ⟨hv'D, hv'ord, K', hK', hlie'⟩ := hv'
    have hvL : v ∈ L := (Subgroup.mem_inf.mp hvD).1
    have hv'L : v' ∈ L := (Subgroup.mem_inf.mp hv'D).1
    have hvs : v * s = s * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hvD).2
    have hv's : v' * s = s * v' :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hv'D).2
    have hvv : v * v = 1 := by
      have h1 := pow_orderOf_eq_one v
      rw [hvord, pow_two] at h1
      exact h1
    have hv'v' : v' * v' = 1 := by
      have h1 := pow_orderOf_eq_one v'
      rw [hv'ord, pow_two] at h1
      exact h1
    obtain ⟨hu, huu, -, htypes, hF⟩ :=
      sec4FD_glue_facts hQ hdim hσ ht6 h v hvL hvs hvord K hK hlie
    obtain ⟨hu', hu'u', -, htypes', hF'⟩ :=
      sec4FD_glue_facts hQ hdim hσ ht6 h v' hv'L hv's hv'ord K' hK' hlie'
    have hty : invType ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) =
        invType ((ρ ⟨v', hv'L⟩ : ↥(omegaGroup hQ)) : OGroup Q) := by
      rcases hsame with ⟨h2, h2'⟩ | ⟨h6, h6'⟩
      · rw [(htype v hvL hvv 2 (-1) (Or.inl rfl)).mp h2,
            (htype v' hv'L hv'v' 2 (-1) (Or.inl rfl)).mp h2']
      · rw [(htype v hvL hvv 6 (-1) (Or.inr (Or.inr rfl))).mp h6,
            (htype v' hv'L hv'v' 6 (-1) (Or.inr (Or.inr rfl))).mp h6']
    obtain ⟨c, hc, hconj⟩ :=
      sec4FD_exists_conj hQ hdim hσ htt ht6 hu hu' huu hu'u' hF hF' hty
    refine h.mem_conjClassIn hvL hv'L hvs hv's hvv hv'v'
      ((mem_sec4FDDt_iff hQ).mp hc).1 ((mem_sec4FDDt_iff hQ).mp hc).2 ?_
    exact hconj.symm
  · obtain ⟨u, hu, huu, hu1, htypeu, hKex⟩ := sec4FD_exists_two hQ hdim hσ htt ht6
    obtain ⟨K, hK, hoc, hlie⟩ := hKex
    have huX : u ∈ omegaGroup hQ := ((mem_sec4FDDt_iff hQ).mp hu).1
    have hut : u * t = t * u := ((mem_sec4FDDt_iff hQ).mp hu).2
    obtain ⟨v, hvL, hvs, hvv, hρv⟩ := h.exists_lift_invol huX hut huu
    have hv1 : v ≠ 1 := by
      intro hv1
      apply hu1
      rw [← hρv]
      have h1 : (⟨v, hvL⟩ : ↥L) = 1 := Subtype.ext (by simpa using hv1)
      rw [h1, map_one]
      rfl
    have hord : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hvv) hv1
    have hK' : IsComponentIn K (omegaGroup hQ ⊓ centralizer ({t} : Set (OGroup Q)) ⊓
        centralizer ({((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q)} :
          Set (OGroup Q))) := by
      rw [hρv]
      simpa only [Sec4FDDt] using hK
    obtain ⟨K', hK', hlie'⟩ :=
      h.exists_component_of_component hvL hvs hvv hK' hoc hlie
    refine ⟨v, ?_, ?_⟩
    · refine ⟨?_, hord, K', hK', hlie'⟩
      exact Subgroup.mem_inf.mpr
        ⟨hvL, Subgroup.mem_centralizer_singleton_iff.mpr hvs⟩
    · exact (htype v hvL hvv 2 (-1) (Or.inl rfl)).mpr (by rw [hρv]; exact htypeu)
  · obtain ⟨u, hu, huu, hu1, htypeu, hKex⟩ := sec4FD_exists_six hQ hdim hσ htt ht6
    obtain ⟨K, hK, hoc, hlie⟩ := hKex
    have huX : u ∈ omegaGroup hQ := ((mem_sec4FDDt_iff hQ).mp hu).1
    have hut : u * t = t * u := ((mem_sec4FDDt_iff hQ).mp hu).2
    obtain ⟨v, hvL, hvs, hvv, hρv⟩ := h.exists_lift_invol huX hut huu
    have hv1 : v ≠ 1 := by
      intro hv1
      apply hu1
      rw [← hρv]
      have h1 : (⟨v, hvL⟩ : ↥L) = 1 := Subtype.ext (by simpa using hv1)
      rw [h1, map_one]
      rfl
    have hord : orderOf v = 2 := orderOf_eq_prime (by rw [pow_two]; exact hvv) hv1
    have hK' : IsComponentIn K (omegaGroup hQ ⊓ centralizer ({t} : Set (OGroup Q)) ⊓
        centralizer ({((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q)} :
          Set (OGroup Q))) := by
      rw [hρv]
      simpa only [Sec4FDDt] using hK
    obtain ⟨K', hK', hlie'⟩ :=
      h.exists_component_of_component hvL hvs hvv hK' hoc hlie
    refine ⟨v, ?_, ?_⟩
    · refine ⟨?_, hord, K', hK', hlie'⟩
      exact Subgroup.mem_inf.mpr
        ⟨hvL, Subgroup.mem_centralizer_singleton_iff.mpr hvs⟩
    · exact (htype v hvL hvv 6 (-1) (Or.inr (Or.inr rfl))).mpr (by rw [hρv]; exact htypeu)
  · intro v hv ht2
    obtain ⟨hvD, hvord, K, hK, hlie⟩ := hv
    have hvL : v ∈ L := (Subgroup.mem_inf.mp hvD).1
    have hvs : v * s = s * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hvD).2
    have hvv : v * v = 1 := by
      have h1 := pow_orderOf_eq_one v
      rw [hvord, pow_two] at h1
      exact h1
    obtain ⟨hu, huu, -, htypes, hF⟩ :=
      sec4FD_glue_facts hQ hdim hσ ht6 h v hvL hvs hvord K hK hlie
    have hty : invType ((ρ ⟨v, hvL⟩ : ↥(omegaGroup hQ)) : OGroup Q) = (2, -1) :=
      (htype v hvL hvv 2 (-1) (Or.inl rfl)).mp ht2
    obtain ⟨c, hc, hswap⟩ := sec4FD_exists_swap hQ hdim hσ htt ht6 hu huu hF hty
    exact h.mem_conjClassIn_swap hvL hvs hvv hc hswap

end CFSG.OddStandard.SmallF3.Omega
