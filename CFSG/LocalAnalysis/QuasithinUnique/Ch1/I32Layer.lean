module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Orbit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.I32Diag

public section

namespace CFSG.QuasithinUnique.I32

open CFSG.ComponentClassification

section Layer

variable {Y : Type*} [Group Y] [Finite Y]

omit [Finite Y] in
theorem le_normalizer_of_conjugate_le {B N' : Subgroup Y}
    (h : ∀ z ∈ N', CFSG.conjugate B z ≤ B) : N' ≤ Subgroup.normalizer (B : Set Y) := by
  intro z hz
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
  refine le_antisymm (h z hz) ?_
  have h1 : CFSG.conjugate (CFSG.conjugate B z⁻¹) z ≤ CFSG.conjugate B z :=
    BenderBranch.conjugate_mono (h z⁻¹ (N'.inv_mem hz)) z
  rwa [BenderBranch.conjugate_conjugate, inv_mul_cancel, BenderBranch.conjugate_one] at h1

variable {s : Y}

theorem normalClosure_layer_eq (hs : s * s = 1) {Kb Lb : Subgroup Y}
    (hK : CFSG.Open.IsComponentOf Kb ⊤) (hLperf : ⁅Lb, Lb⁆ = Lb) (hLne : Lb ≠ ⊥)
    (hLfix : Lb ≤ Subgroup.centralizer ({s} : Set Y)) (hLA : Lb ≤ orbitSub s Kb) :
    (⨆ y ∈ Layer.subgroup Y, CFSG.conjugate Lb y) = orbitSub s Kb := by
  set M : Subgroup Y := ⨆ y ∈ Layer.subgroup Y, CFSG.conjugate Lb y with hM
  have hfixmap : Lb.map (MulAut.conj s).toMonoidHom = Lb := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h' : s * x = x * s := (Subgroup.mem_centralizer_singleton_iff.mp (hLfix hx)).symm
      change s * x * s⁻¹ ∈ Lb
      rw [h', mul_inv_cancel_right]
      exact hx
    · intro hy
      refine ⟨y, hy, ?_⟩
      have h' : s * y = y * s := (Subgroup.mem_centralizer_singleton_iff.mp (hLfix hy)).symm
      change s * y * s⁻¹ = y
      rw [h', mul_inv_cancel_right]
  have hLM : Lb ≤ M := by
    have : Lb = CFSG.conjugate Lb 1 := (BenderBranch.conjugate_one Lb).symm
    rw [this]
    exact le_iSup₂_of_le (1 : Y) (Subgroup.one_mem _) le_rfl
  have hMA : M ≤ orbitSub s Kb :=
    iSup₂_le fun y hy => conjugate_le_of_mem_normalizer hLA (layer_le_normalizer_orbitSub hK hy)
  refine le_antisymm hMA ?_
  have hMlayer : M ≤ Layer.subgroup Y := hMA.trans (orbitSub_le_layer hK)
  have hMconj : ∀ z ∈ Layer.subgroup Y, CFSG.conjugate M z ≤ M := by
    intro z hz
    rw [hM, conjugate_iSup]
    refine iSup_le fun y => ?_
    rw [conjugate_iSup]
    refine iSup_le fun hy => ?_
    rw [BenderBranch.conjugate_conjugate]
    exact le_iSup₂_of_le (y * z) (Subgroup.mul_mem _ hy hz) le_rfl
  have hMsub : CFSG.Open.IsSubnormal M ⊤ :=
    isSubnormal_of_le_layer hMlayer (le_normalizer_of_conjugate_le hMconj)
  have hKM : Kb ≤ M := by
    rcases LocalComponents.subnormal_contains_or_commutes Kb M hK hMsub with hle | hcomm
    · exact hle
    · exfalso
      have h1 : ⁅Lb, Kb⁆ = ⊥ := by
        rw [Subgroup.commutator_comm]
        exact le_bot_iff.mp (hcomm ▸ Subgroup.commutator_mono le_rfl hLM)
      have h2 : ⁅Lb, CFSG.conjugate Kb s⁆ = ⊥ := by
        rw [conjugate_eq_map_conj hs, ← hfixmap, ← Subgroup.map_commutator, h1, Subgroup.map_bot]
      have h3 : ⁅Lb, orbitSub s Kb⁆ = ⊥ := by
        unfold orbitSub
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
        refine sup_le ?_ ?_
        · rw [← Subgroup.le_centralizer_iff]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
        · rw [← Subgroup.le_centralizer_iff]
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
      have h4 : Lb = ⊥ := by
        rw [← hLperf]
        exact le_bot_iff.mp (h3 ▸ Subgroup.commutator_mono le_rfl hLA)
      exact hLne h4
  have hKsM : CFSG.conjugate Kb s ≤ M := by
    have hMinv : M.map (MulAut.conj s).toMonoidHom ≤ M := by
      rw [hM, Subgroup.map_iSup]
      refine iSup_le fun y => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hy => ?_
      have hconj := map_conjugate (MulAut.conj s).toMonoidHom Lb y
      rw [hfixmap] at hconj
      rw [hconj]
      refine le_iSup₂_of_le ((MulAut.conj s).toMonoidHom y) ?_ le_rfl
      exact (Layer.normal Y).conj_mem y hy s
    rw [conjugate_eq_map_conj hs]
    exact (Subgroup.map_mono hKM).trans hMinv
  exact sup_le hKM hKsM

omit [Finite Y] in
theorem conj_conj_self (hs : s * s = 1) (y : Y) :
    (MulAut.conj s) ((MulAut.conj s) y) = y := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  change s * (s * y * s⁻¹) * s⁻¹ = y
  rw [hsinv]
  calc s * (s * y * s) * s = (s * s) * y * (s * s) := by group
    _ = y := by rw [hs]; simp

omit [Finite Y] in
theorem conj_eq_self_of_mem_centralizer {x : Y} (hx : x ∈ Subgroup.centralizer ({s} : Set Y)) :
    (MulAut.conj s) x = x := by
  have h' : s * x = x * s := (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
  change s * x * s⁻¹ = x
  rw [h', mul_inv_cancel_right]

theorem exists_diagonal_hom (hs : s * s = 1) {Kb Lb : Subgroup Y}
    (hK : CFSG.Open.IsComponentOf Kb ⊤) (hne : CFSG.conjugate Kb s ≠ Kb)
    (hLperf : ⁅Lb, Lb⁆ = Lb) (hLne : Lb ≠ ⊥)
    (hLfix : Lb ≤ Subgroup.centralizer ({s} : Set Y)) (hLA : Lb ≤ orbitSub s Kb)
    (hLsub : CFSG.Open.IsSubnormal Lb (Subgroup.centralizer ({s} : Set Y))) :
    ∃ ψ : ↥Kb →* ↥Lb, Function.Surjective ψ ∧ CFSG.Open.IsQuasisimple ↥Lb := by
  have hKs : CFSG.Open.IsComponentOf (CFSG.conjugate Kb s) ⊤ := isComponentOf_conjugate hK s
  have hcommKK : ⁅Kb, CFSG.conjugate Kb s⁆ = ⊥ := commute_of_ne_component hK hKs (fun h => hne h.symm)
  let σ : Y ≃* Y := MulAut.conj s
  have hσ : ∀ y, σ (σ y) = y := conj_conj_self hs
  have hconjσ : CFSG.conjugate Kb s = Kb.map σ.toMonoidHom := conjugate_eq_map_conj hs Kb
  have hcomm : ∀ a ∈ Kb, ∀ b ∈ Kb, a * σ b = σ b * a := by
    intro a ha b hb
    have hKC : Kb ≤ Subgroup.centralizer ((CFSG.conjugate Kb s : Subgroup Y) : Set Y) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommKK
    have hσb : σ b ∈ CFSG.conjugate Kb s := by
      rw [hconjσ]
      exact ⟨b, hb, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hKC ha) (σ b) hσb).symm
  have hfix : ∀ x ∈ Subgroup.centralizer ({s} : Set Y), σ x = x := fun x hx =>
    conj_eq_self_of_mem_centralizer hx
  let τ := tau σ Kb hcomm
  have hLA' : Lb ≤ Kb ⊔ Kb.map σ.toMonoidHom := by
    unfold orbitSub at hLA
    rwa [hconjσ] at hLA
  have hLR : Lb ≤ τ.range := by
    have hLC : Lb ≤ (Kb ⊔ Kb.map σ.toMonoidHom) ⊓ Subgroup.centralizer ({s} : Set Y) :=
      le_inf hLA' hLfix
    calc Lb = ⁅Lb, Lb⁆ := hLperf.symm
      _ ≤ ⁅(Kb ⊔ Kb.map σ.toMonoidHom) ⊓ Subgroup.centralizer ({s} : Set Y),
          (Kb ⊔ Kb.map σ.toMonoidHom) ⊓ Subgroup.centralizer ({s} : Set Y)⁆ :=
        Subgroup.commutator_mono hLC hLC
      _ ≤ τ.range := commutator_le_range σ hσ Kb hcomm _ hfix
  have hRC : τ.range ≤ Subgroup.centralizer ({s} : Set Y) := by
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := tau_fixed σ hσ Kb hcomm a
    change s * τ a * s⁻¹ = τ a at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hker : τ.ker ≠ ⊤ := by
    intro htop
    apply hne
    have hle : Kb ≤ CFSG.conjugate Kb s := by
      intro a ha
      rw [hconjσ]
      exact mem_map_of_tau_eq_one σ Kb hcomm
        (a := ⟨a, ha⟩) (MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top _))
    exact (LocalComponents.eq_of_le Kb _ hK hKs hle).symm
  have hRq : CFSG.Open.IsQuasisimple ↥τ.range :=
    Quasisimple.range_quasisimple_of_ker_ne_top hK.2.2 τ hker
  have hRL : τ.range = Lb := by
    refine le_antisymm ?_ hLR
    have hsub : CFSG.Open.IsSubnormal (Lb.subgroupOf τ.range) ⊤ := by
      have h1 := CFSG.Quasithin.A3.subnormal_of_le_of_le hLsub hLR hRC
      have h2 := CFSG.Quasithin.A3.subnormal_comap τ.range.subtype h1
      rwa [show τ.range.comap τ.range.subtype = ⊤ from Subgroup.subgroupOf_self _] at h2
    have hmap : (Lb.subgroupOf τ.range).map τ.range.subtype = Lb :=
      Subgroup.map_subgroupOf_eq_of_le hLR
    have hperf' : ⁅Lb.subgroupOf τ.range, Lb.subgroupOf τ.range⁆ = Lb.subgroupOf τ.range := by
      apply Subgroup.map_injective τ.range.subtype_injective
      rw [Subgroup.map_commutator, hmap, hLperf]
    have : Group.IsPerfect ↥(Lb.subgroupOf τ.range) := Subgroup.isPerfect_iff.mpr hperf'
    rcases Quasisimple.perfect_subnormal_eq_bot_or_eq_top hRq _ hsub with hbot | htop
    · exfalso
      apply hLne
      rw [← hmap, hbot, Subgroup.map_bot]
    · exact Subgroup.subgroupOf_eq_top.mp htop
  refine ⟨τ.codRestrict Lb (fun a => hRL ▸ (⟨a, rfl⟩ : τ a ∈ τ.range)), ?_, hRL ▸ hRq⟩
  intro l
  obtain ⟨a, ha⟩ := (hRL.symm ▸ l.2 : (l : Y) ∈ τ.range)
  exact ⟨a, Subtype.ext ha⟩

end Layer

end CFSG.QuasithinUnique.I32
