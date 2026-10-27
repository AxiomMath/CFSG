module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Stage3

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

theorem card_perm_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

@[expose] def g23 : Fin 5 → ZMod 2 := ![0, 0, 1, 1, 0]

theorem g23_even : isEven g23 := by decide +kernel

@[expose] def g1w : evenWeight 5 := ⟨g1, g1_even⟩

@[expose] def g23w : evenWeight 5 := ⟨g23, g23_even⟩

theorem g1_add_z0 : g1 + z0 = g23 := by decide +kernel

theorem fix_E : ∀ v : Fin 5 → ZMod 2, isEven v → (∀ σ ∈ Eset, pact σ v = v) →
    v = 0 ∨ v = g1 ∨ v = g23 ∨ v = z0 := by decide +kernel

theorem fixD_g1 : ∀ σ ∈ Dset, pact σ g1 = g1 → σ ∈ Eset := by decide +kernel

@[expose] def rho13 : Equiv.Perm (Fin 5) := Equiv.swap (0 : Fin 5) 2 * Equiv.swap (1 : Fin 5) 3

theorem rho13_inv : rho13⁻¹ = rho13 := by decide +kernel

theorem rho13_mem_Dset : rho13 ∈ Dset := by decide +kernel

theorem rho13_not_mem_Eset : rho13 ∉ Eset := by decide +kernel

theorem pact_rho13_g1 : pact rho13 g1 = g23 := by decide +kernel

theorem rho13_conj_E : ∀ σ ∈ Eset, rho13 * σ * rho13⁻¹ ∈ Eset := by decide +kernel

theorem rho13_conj_E' : ∀ σ ∈ Eset, rho13⁻¹ * σ * rho13 ∈ Eset := by decide +kernel

theorem vact_rho13_g1w : vact rho13 g1w = g23w := Subtype.ext pact_rho13_g1

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

@[expose] noncomputable def relabel (C : StdCfg T M H S L) (ρ : Equiv.Perm (Fin 5))
    (h1 : ∀ σ ∈ Estd, ρ * σ * ρ⁻¹ ∈ Estd) (h2 : ∀ σ ∈ Estd, ρ⁻¹ * σ * ρ ∈ Estd) :
    StdCfg T M H S L where
  hcs := C.hcs
  hj := C.hj
  F := C.F
  D := C.D.conj ρ
  hsurj := by
    intro τ
    obtain ⟨h, hh⟩ := C.hsurj (ρ⁻¹ * τ * ρ)
    refine ⟨h, ?_⟩
    show ρ * C.D.π h * ρ⁻¹ = τ
    rw [hh]
    group
  hker := by
    intro h
    rw [← C.hker h]
    show ρ * C.D.π h * ρ⁻¹ = 1 ↔ C.D.π h = 1
    constructor
    · intro h0
      have : C.D.π h = ρ⁻¹ * (ρ * C.D.π h * ρ⁻¹) * ρ := by group
      rw [this, h0]
      group
    · intro h0
      rw [h0]
      group
  hRE := fun r hr => h1 _ (C.hRE r hr)
  hRE' := by
    intro σ hσ
    obtain ⟨r, hr, hπ⟩ := C.hRE' _ (h2 σ hσ)
    refine ⟨r, hr, ?_⟩
    show ρ * C.D.π ⟨r, baum_le_H C.hcs hr⟩ * ρ⁻¹ = σ
    rw [hπ]
    group
  hHeq := C.hHeq

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem mem_U_of_cent {u : G} (hu : u ∈ centerOf (baum S)) : u ∈ blockU L := by
  have huR : u ∈ baum S := (Subgroup.mem_inf.mp hu).1
  have hcomm : ∀ r ∈ baum S, r * u = u * r := fun r hr =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 r hr
  set h : ↥H := ⟨u, baum_le_H C.hcs huR⟩ with hh
  have hπ : C.D.π h = 1 := by
    apply vact_faithful
    intro w
    have hc : h * C.iV w = C.iV w * h :=
      Subtype.ext (hcomm _ (C.U_le_R (C.iV_mem_U w))).symm
    exact X.vact_fixed_of_comm h w hc
  rw [← C.Q_eq_U X.hTC]
  exact (C.hker h).mp hπ

theorem cent_cases {u : G} (hu : u ∈ centerOf (baum S)) :
    u = 1 ∨ u = ((C.iV g1w : ↥H) : G) ∨ u = ((C.iV g23w : ↥H) : G) ∨ u = C.zU := by
  obtain ⟨w, hw⟩ := C.exists_iV_of_mem_U (X.mem_U_of_cent hu)
  have hcomm : ∀ r ∈ baum S, r * u = u * r := fun r hr =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 r hr
  have hfix : ∀ σ ∈ Eset, pact σ w.1 = w.1 := by
    intro σ hσ
    obtain ⟨r, hr, hπ⟩ := C.hRE' σ hσ
    have hc : (⟨r, baum_le_H C.hcs hr⟩ : ↥H) * C.iV w = C.iV w * ⟨r, baum_le_H C.hcs hr⟩ := by
      apply Subtype.ext
      show r * ((C.iV w : ↥H) : G) = ((C.iV w : ↥H) : G) * r
      rw [← hw]
      exact hcomm r hr
    have := X.vact_fixed_of_comm ⟨r, baum_le_H C.hcs hr⟩ w hc
    rw [hπ] at this
    exact congrArg Subtype.val this
  rcases fix_E w.1 w.2 hfix with h | h | h | h
  · left
    have : w = 0 := Subtype.ext h
    rw [hw, this, C.iV_zero]
    rfl
  · right; left
    rw [hw]
    exact congrArg (fun y : ↥H => (y : G)) (congrArg C.iV (Subtype.ext h))
  · right; right; left
    rw [hw]
    exact congrArg (fun y : ↥H => (y : G)) (congrArg C.iV (Subtype.ext h))
  · right; right; right
    have : w = StdCfg.z0V := Subtype.ext h
    rw [hw, this, ← C.zU_eq_iV]

theorem exists_w_of_Z {u : G} (hu : u ∈ centerOf (baum S)) (huZ : u ∉ centerOf (borelP M L)) :
    u = ((C.iV g1w : ↥H) : G) ∨ u = ((C.iV g23w : ↥H) : G) := by
  rcases X.cent_cases hu with h | h | h | h
  · exact absurd (h ▸ one_mem _) huZ
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd ((X.centerOf_P_iff _).mpr (Or.inr h)) huZ

end Sec

end CFSG.QuasithinUnique.A5
