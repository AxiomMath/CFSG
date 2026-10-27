module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarAut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFStarCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSTypes

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec5c_mono_of_norm (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) 1) {g : OGroup Q}
    (hg : g ∈ omegaGroup hQ) (hn : ∀ b ∈ ffB0 fr, g⁻¹ * b * g ∈ ffB0 fr) :
    ∃ (σ : Equiv.Perm (Fin 6)) (K : Finset (Fin 6)),
      σ ∈ alternatingGroup (Fin 6) ∧ Even K.card ∧ g = fr.permOrth σ * fr.signChange K := by
  have h : ∀ b ∈ ffB0 fr, simAct Q (orthToSim Q g)⁻¹ b ∈ ffB0 fr := by
    intro b hb
    rw [← map_inv, simAct_orthToSim, inv_inv]
    exact hn b hb
  obtain ⟨σ, K, hσK⟩ := ffMono_of_normalizes fr (orthToSim Q g) h
  have hg_eq : g = fr.permOrth σ * fr.signChange K := orthToSim_injective hσK
  have hmem : fr.permOrth σ * fr.signChange K ∈ omegaGroup hQ := by rwa [hg_eq] at hg
  obtain ⟨hσ, hKe⟩ := (ffMono_mem_omega_iff hQ fr σ K).mp hmem
  exact ⟨σ, K, hσ, hKe, hg_eq⟩

theorem sec5c_cent_B0 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) (fr : NFrame Q (Fin 6) 1) {g : OGroup Q}
    (hg : g ∈ omegaGroup hQ) (hc : ∀ b ∈ ffB0 fr, g * b = b * g) : g ∈ ffB0 fr := by
  have hcomm : ∀ b ∈ ffB1 hQ fr,
      omegaToProj hQ ⟨g, hg⟩ * b = b * omegaToProj hQ ⟨g, hg⟩ := by
    intro b hb
    rw [ffB1, mem_ffStar_iff] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    apply Subtype.ext
    change (omegaToProj hQ ⟨g, hg⟩ : ProjOrth Q) * (omegaToProj hQ b' : ProjOrth Q) =
      (omegaToProj hQ b' : ProjOrth Q) * (omegaToProj hQ ⟨g, hg⟩ : ProjOrth Q)
    rw [coe_omegaToProj, coe_omegaToProj, ← map_mul, ← map_mul, hc (b' : OGroup Q) hb']
  have hn := ff_star_cent_omega hQ hdim hsgn fr (omegaToProj hQ ⟨g, hg⟩) hcomm
  have hg' : g ∈ ffLift hQ (ffB1 hQ fr) := (mem_ffLift_iff hQ).mpr ⟨hg, hn⟩
  rwa [ffLift_ffB1 hQ fr] at hg'

theorem sec5c_elemAb2_img (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {D : Subgroup ↥(omegaGroup hQ)}
    (hπ : (⟨piOrth Q, ff_piOrth_mem_omegaGroup_six_minus hQ hdim hsgn⟩ : ↥(omegaGroup hQ)) ∈ D)
    (hE : IsElemAb2 D 5) : IsElemAb2 (D.map (omegaToProj hQ)) 4 := by
  let U : Subgroup ↥(omegaProj hQ) := D.map (omegaToProj hQ)
  change IsElemAb2 U 4
  have hsub : ((D.map (omegaGroup hQ).subtype).subgroupOf (omegaGroup hQ)) = D := by
    ext g
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨d, hd, hdg⟩
      have hdg' : d = g := Subtype.ext hdg
      rwa [hdg'] at hd
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hstar : ffStar hQ (D.map (omegaGroup hQ).subtype) = U := by
    show ((D.map (omegaGroup hQ).subtype).subgroupOf (omegaGroup hQ)).map (omegaToProj hQ) = U
    rw [hsub]
  have hSle : D.map (omegaGroup hQ).subtype ≤ omegaGroup hQ := Subgroup.map_subtype_le D
  have hπ' : piOrth Q ∈ D.map (omegaGroup hQ).subtype :=
    Subgroup.mem_map.mpr
      ⟨⟨piOrth Q, ff_piOrth_mem_omegaGroup_six_minus hQ hdim hsgn⟩, hπ, rfl⟩
  have hlift_eq : ffLift hQ U = D.map (omegaGroup hQ).subtype := by
    rw [← hstar]
    exact ffLift_ffStar hQ hSle hπ'
  have hcardD : Nat.card ↥(D.map (omegaGroup hQ).subtype) = Nat.card ↥D :=
    Subgroup.card_subtype (omegaGroup hQ) D
  have hcard_lift : Nat.card ↥(ffLift hQ U) = Nat.card ↥D := by
    rw [hlift_eq, hcardD]
  have hUcard : Nat.card ↥U = 2 ^ 4 := by
    have h := ffLift_card hQ hdim hsgn U
    rw [hcard_lift, hE.2] at h
    norm_num at h ⊢
    omega
  refine ⟨?_, hUcard⟩
  refine ⟨?_, ?_⟩
  · haveI : IsMulCommutative D := hE.1.1
    show IsMulCommutative (D.map (omegaToProj hQ))
    infer_instance
  · intro x hx
    obtain ⟨d, hd, rfl⟩ :=
      Subgroup.mem_map.mp (show x ∈ D.map (omegaToProj hQ) from hx)
    rw [← map_pow, hE.1.2 d hd, map_one]

theorem sec5c_cent_type1 (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (h2 : 2 ≤ Module.finrank (ZMod 3) V) (fr : NFrame Q (Fin 6) 1) {x : ProjSim Q} {α : ℤˣ}
    (hx : SimHasType x 1 α) (hc : ∀ b ∈ ffB1 hQ fr, ffSimOmegaAct hQ h2 x b = b) :
    ∃ i : Fin 6, x = projOrthToProjSim Q (toProj Q (fr.signChange {i})) := by
  obtain ⟨K, hK⟩ := ff_star_cent_sim hQ h2 fr hc
  have hKle : K.card ≤ 6 := by simpa using Finset.card_le_univ K
  have hodd : Odd K.card := by
    rcases Nat.even_or_odd K.card with he | ho
    · exfalso
      obtain ⟨b, hb, hbe⟩ := ff_exists_mem_ffB1_signChange hQ fr he
      have hmem : SimInOmegaStar hQ x :=
        ⟨(b : ProjOrth Q), b.2, by rw [hbe, ← hK]⟩
      exact (ff_simHasType_odd_not_simInOmegaStar hQ hdim (show Odd 1 from ⟨0, rfl⟩) hx) hmem
    · exact ho
  have hcard : K.card = 1 ∨ K.card = 3 ∨ K.card = 5 := by
    rcases hodd with ⟨m, hm⟩
    omega
  rcases hcard with h1 | h3 | h5
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h1
    exact ⟨i, by rw [hK, hi]⟩
  · exfalso
    obtain ⟨α', hα'⟩ := ff_simHasType_signChange hQ fr (K := K) (Or.inr h3)
    rw [← hK, h3] at hα'
    rcases ff_simHasType_rank hQ hdim hx hα' with h | h <;> omega
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (show Kᶜ.card = 1 by
      rw [Finset.card_compl, Fintype.card_fin]
      omega)
    exact ⟨i, by rw [hK, ← ff_toProj_signChange_compl fr K, hi]⟩

end CFSG.OddStandard.SmallF3.Omega
