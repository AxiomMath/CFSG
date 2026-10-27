module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S14B
public import CFSG.LocalAnalysis.EvenBN.Tits.N.P3S17

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N

open Subgroup CFSG.Open CFSG.Sporadic.Schreier.Tits

section S14C

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}


theorem six_six_false (h49 : d.Thm49Statement) (hd : d.Hyp) (h11 : Node11 d z₀) (h13 : Node13 d)
    (hP1a : IsElemAbelian 2 (P1 d)) {k : G} (hkt : k * d.t * k⁻¹ = d.t * d.pv 7)
    (hDB : zpowers (d.t * d.pv 7) ⊔ (d.s56V ⊓ centralizer ({d.t * d.pv 7} : Set G)) =
      d.B.map (MulAut.conj k).toMonoidHom)
    (hVP : d.s56V = (P1 d).map (MulAut.conj k).toMonoidHom) : False := by
  obtain ⟨g, hgP, hgt⟩ := exists_P1_conj_t_mul_pv7 h13
  have hP1t := t_not_mem_P1 hd h13 hP1a
  have hU := inf_centralizer_eq_conj_F hd h11 hkt hP1t hDB hVP
  have hFP := F_le_P1 h11
  have hgF : ∀ f ∈ d.F, g * f = f * g := fun f hf => elemAbelian_comm hP1a hgP (hFP hf)
  have hginv : ∀ f ∈ d.F, g⁻¹ * f * g = f := fun f hf => by
    calc g⁻¹ * f * g = g⁻¹ * (f * g) := by group
      _ = g⁻¹ * (g * f) := by rw [hgF f hf]
      _ = f := by group
  have hx₀ : g⁻¹ * k ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e1 : g⁻¹ * (d.t * d.pv 7) * g = d.t := by rw [← hgt]; group
    calc g⁻¹ * k * d.t = (g⁻¹ * (k * d.t * k⁻¹) * g) * (g⁻¹ * k) := by group
      _ = d.t * (g⁻¹ * k) := by rw [hkt, e1]
  have hFB : IsElemAbelian 2 d.B := hd.B_facts.2.2.1
  have hFcs : ∀ f ∈ d.F, f * (d.t * d.pv 7) = (d.t * d.pv 7) * f := by
    intro f hf
    have h1 : f * d.t = d.t * f := hd.L_comm_t (d.liftSub_le _ hf)
    have h2 : f * d.pv 7 = d.pv 7 * f :=
      elemAbelian_comm hFB (mem_sup_left hf) (mem_sup_left pv7_mem_F)
    calc f * (d.t * d.pv 7) = (f * d.t) * d.pv 7 := by group
      _ = d.t * (f * d.pv 7) := by rw [h1]; group
      _ = d.t * (d.pv 7 * f) := by rw [h2]
      _ = d.t * d.pv 7 * f := by group
  have hFN : ∀ f ∈ d.F, f ∈ normalizer
      ((d.s56V ⊓ centralizer ({d.t * d.pv 7} : Set G) : Subgroup G) : Set G) := by
    intro f hf
    have hfM : f ∈ d.M := Q_le_M h49 hd (hd.s56_F_le_Q h49 hf)
    exact mem_normalizer_inf (M_le_Hg h49 hd hfM) (mem_normalizer_centralizer_singleton (hFcs f hf))
  have hUF₃ : d.s56V ⊓ centralizer ({d.t * d.pv 7} : Set G) =
      (d.F.map (MulAut.conj (g⁻¹ * k)).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rw [hU, map_conj_map_conj', show g * (g⁻¹ * k) = k by group]
  have hFN₃ : ∀ f ∈ d.F, f ∈ normalizer
      ((d.F.map (MulAut.conj (g⁻¹ * k)).toMonoidHom : Subgroup G) : Set G) := by
    intro f hf
    have h := hFN f hf
    rw [hUF₃, mem_normalizer_map_conj_iff, hginv f hf] at h
    exact h
  have hFD : Model.parrottF ≤ titsD := Model.parrottF_le_titsD
  have hED : Model.hatE ≤ titsD := Model.hatE_le_titsJ.trans titsJ_le_titsD
  have haA := (d.ρ ⟨g⁻¹ * k, hx₀⟩).2
  have hF₃ : d.F.map (MulAut.conj (g⁻¹ * k)).toMonoidHom =
      d.liftSub (Model.parrottF.map
        (MulAut.conj (d.ρ ⟨g⁻¹ * k, hx₀⟩ : Equiv.Perm (Fin 1755))).toMonoidHom) :=
    hd.map_conj_liftSub hx₀ hFD
  have hF'D : Model.parrottF.map
      (MulAut.conj (d.ρ ⟨g⁻¹ * k, hx₀⟩ : Equiv.Perm (Fin 1755))).toMonoidHom ≤ titsD := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (Model.conj_mem_titsD_iff haA (titsD_le_titsA (hFD hx))).2 (hFD hx)
  have hN : ∀ f ∈ Model.parrottF, f ∈ normalizer
      ((Model.parrottF.map (MulAut.conj (d.ρ ⟨g⁻¹ * k, hx₀⟩ :
        Equiv.Perm (Fin 1755))).toMonoidHom : Subgroup (Equiv.Perm (Fin 1755))) :
        Set (Equiv.Perm (Fin 1755))) := by
    intro f hf
    refine mem_normalizer_of_lift (d := d) hFD hF'D hf ?_
    rw [← hF₃]
    exact hFN₃ _ (Data.mem_liftSub.2 ⟨f, hf, hFD hf, rfl⟩)
  have hEF : d.E ⊓ d.F ≤ d.F ⊓ d.F.map (MulAut.conj (g⁻¹ * k)).toMonoidHom := by
    rintro e ⟨heE, heF⟩
    refine ⟨heF, ?_⟩
    have heU : e ∈ d.s56V ⊓ centralizer ({d.t * d.pv 7} : Set G) :=
      ⟨hd.s56_E_le_V h49 heE, mem_centralizer_singleton_iff.2 (hFcs e heF)⟩
    rw [hUF₃, mem_map_conj_iff', hginv e heF] at heU
    exact heU
  have h16 : 16 ≤ Nat.card (Model.parrottF ⊓ Model.parrottF.map
      (MulAut.conj (d.ρ ⟨g⁻¹ * k, hx₀⟩ : Equiv.Perm (Fin 1755))).toMonoidHom :
      Subgroup (Equiv.Perm (Fin 1755))) := by
    have e1 : Nat.card (Model.parrottF ⊓ Model.parrottF.map
        (MulAut.conj (d.ρ ⟨g⁻¹ * k, hx₀⟩ : Equiv.Perm (Fin 1755))).toMonoidHom :
        Subgroup (Equiv.Perm (Fin 1755))) =
        Nat.card (d.F ⊓ d.F.map (MulAut.conj (g⁻¹ * k)).toMonoidHom : Subgroup G) := by
      rw [← d.card_liftSub (inf_le_left.trans hFD), liftSub_inf' hFD hF'D, ← hF₃]
      rfl
    have e2 := Subgroup.card_le_of_le hEF
    have e3 : Nat.card (d.E ⊓ d.F : Subgroup G) = Nat.card (Model.hatE ⊓ Model.parrottF :
        Subgroup (Equiv.Perm (Fin 1755))) := by
      rw [← d.card_liftSub (inf_le_left.trans hED), liftSub_inf' hED hFD]
      rfl
    have e4 := Model.sixteen_le_card_hatE_inf_parrottF
    omega
  have hFeq := Model.map_conj_parrottF_eq_of_normalizer haA hN h16
  have hF₃F : d.F.map (MulAut.conj (g⁻¹ * k)).toMonoidHom = d.F := by
    rw [hF₃, hFeq]
    rfl
  have hFg : d.F.map (MulAut.conj g).toMonoidHom = d.F := by
    ext x
    rw [mem_map_conj_iff']
    constructor
    · intro h
      have hx : x = g⁻¹ * x * g := by
        have h1 := hgF _ h
        calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          _ = (g⁻¹ * x * g) * g * g⁻¹ := by rw [h1]
          _ = g⁻¹ * x * g := by group
      rw [hx]
      exact h
    · intro h
      rw [hginv x h]
      exact h
  have hUeq : d.s56V ⊓ centralizer ({d.t * d.pv 7} : Set G) = d.F := by
    rw [hUF₃, hF₃F, hFg]
  have hv7V : d.pv 7 ∈ d.s56V := by
    have : d.pv 7 ∈ d.s56V ⊓ centralizer ({d.t * d.pv 7} : Set G) := by
      rw [hUeq]
      exact pv7_mem_F
    exact this.1
  have hv7CMt : d.pv 7 ∈ CMt d :=
    mem_inf.2 ⟨pv7_mem_M hd, mem_centralizer_singleton_iff.2 (hd.L_comm_t (pv_mem_L 7))⟩
  have hv7E : d.pv 7 ∈ d.E := by
    rw [← CMt_inf_V h49 hd]
    exact ⟨hv7CMt, hv7V⟩
  exact pv7_not_mem_E hv7E

end S14C

end CFSG.LocalAnalysis.EvenBN.Tits.N
