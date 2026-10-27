module

public import CFSG.Quasithin.Background.B1MoreElevenF

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem resHom_mem_stabSub_subgroupOf' {W U' : Subgroup V} {g : MulAut V} (hW : g ∈ stabSub W)
    (hU : g ∈ stabSub U') : resHom W ⟨g, hW⟩ ∈ stabSub (U'.subgroupOf W) := by
  intro x
  show (resHom W ⟨g, hW⟩ x : W) ∈ U'.subgroupOf W ↔ x ∈ U'.subgroupOf W
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact hU (x : V)

@[expose] noncomputable def secHom (W U' : Subgroup V) :
    ↥(stabSub W ⊓ stabSub U') →* MulAut (Sec W U') :=
  (quotHom (U'.subgroupOf W)).comp
    (((resHom W).comp (Subgroup.inclusion
      (inf_le_left : stabSub W ⊓ stabSub U' ≤ stabSub W))).codRestrict
      (stabSub (U'.subgroupOf W)) (fun g => resHom_mem_stabSub_subgroupOf' g.2.1 g.2.2))

theorem secHom_apply (W U' : Subgroup V) (g : ↥(stabSub W ⊓ stabSub U')) (w : ↥W) :
    secHom W U' g (QuotientGroup.mk w) =
      QuotientGroup.mk (⟨(g : MulAut V) (w : V), (g.2.1 (w : V)).2 w.2⟩ : ↥W) := rfl

theorem secHom_eq_one_iff {W U' : Subgroup V} (g : ↥(stabSub W ⊓ stabSub U')) :
    secHom W U' g = 1 ↔ (g : MulAut V) ∈ centSec W U' := by
  constructor
  · intro h
    refine ⟨g.2.1, fun w hw => ?_⟩
    have h1 := congrArg (fun φ : MulAut (Sec W U') => φ (QuotientGroup.mk (⟨w, hw⟩ : ↥W))) h
    simp only [secHom_apply, MulAut.one_apply] at h1
    have h2 := (mk_eq_mk_iff (U := U'.subgroupOf W) _ _).1 h1
    simpa [Subgroup.mem_subgroupOf] using h2
  · intro h
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H w =>
      rw [secHom_apply, MulAut.one_apply]
      refine (mk_eq_mk_iff (U := U'.subgroupOf W) _ _).2 ?_
      rw [Subgroup.mem_subgroupOf]
      simpa using h.2 (w : V) w.2

theorem mem_autSec_iff_secHom {X : Subgroup (MulAut V)} {W U' : Subgroup V}
    (hX : X ≤ stabSub W ⊓ stabSub U') {ψ : MulAut (Sec W U')} :
    ψ ∈ autSec X W U' ↔
      ∃ g : ↥(stabSub W ⊓ stabSub U'), (g : MulAut V) ∈ X ∧ secHom W U' g = ψ := by
  rw [B1Red.mem_autSec_iff]
  constructor
  · rintro ⟨h, hhX, hU, hψ⟩
    exact ⟨⟨(h : MulAut V), hX hhX⟩, hhX, hψ⟩
  · rintro ⟨g, hgX, hψ⟩
    exact ⟨⟨(g : MulAut V), g.2.1⟩, hgX, resHom_mem_stabSub_subgroupOf' g.2.1 g.2.2, hψ⟩

variable {Γ : Type} [Group Γ]

@[expose] noncomputable def secAct (ρ : Γ →* MulAut V) (W U' : Subgroup V)
    (hW : ∀ g : Γ, ρ g ∈ stabSub W) (hU : ∀ g : Γ, ρ g ∈ stabSub U') :
    Γ →* MulAut (Sec W U') :=
  (secHom W U').comp (ρ.codRestrict (stabSub W ⊓ stabSub U')
    (fun g => Subgroup.mem_inf.2 ⟨hW g, hU g⟩))

theorem secAct_apply (ρ : Γ →* MulAut V) (W U' : Subgroup V) (hW : ∀ g : Γ, ρ g ∈ stabSub W)
    (hU : ∀ g : Γ, ρ g ∈ stabSub U') (g : Γ) (w : ↥W) :
    secAct ρ W U' hW hU g (QuotientGroup.mk w) =
      QuotientGroup.mk (⟨ρ g (w : V), (hW g (w : V)).2 w.2⟩ : ↥W) := rfl

theorem secAct_eq_one_iff (ρ : Γ →* MulAut V) (W U' : Subgroup V) (hW : ∀ g : Γ, ρ g ∈ stabSub W)
    (hU : ∀ g : Γ, ρ g ∈ stabSub U') (g : Γ) :
    secAct ρ W U' hW hU g = 1 ↔ ∀ w ∈ W, ρ g w * w⁻¹ ∈ U' := by
  have := secHom_eq_one_iff (W := W) (U' := U')
    (ρ.codRestrict (stabSub W ⊓ stabSub U') (fun g => Subgroup.mem_inf.2 ⟨hW g, hU g⟩) g)
  exact this.trans ⟨fun h => h.2, fun h => ⟨hW g, h⟩⟩

theorem autSec_map_eq (ρ : Γ →* MulAut V) (W U' : Subgroup V) (hW : ∀ g : Γ, ρ g ∈ stabSub W)
    (hU : ∀ g : Γ, ρ g ∈ stabSub U') (X : Subgroup Γ) :
    autSec (X.map ρ) W U' = X.map (secAct ρ W U' hW hU) := by
  have hX : X.map ρ ≤ stabSub W ⊓ stabSub U' := by
    rintro _ ⟨g, -, rfl⟩
    exact ⟨hW g, hU g⟩
  ext ψ
  rw [mem_autSec_iff_secHom hX]
  constructor
  · rintro ⟨g, ⟨x, hx, hxg⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    show secHom W U' ⟨ρ x, _⟩ = secHom W U' g
    congr 1
    exact Subtype.ext hxg
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨ρ x, hW x, hU x⟩, ⟨x, hx, rfl⟩, rfl⟩

end CFSG.CGT.PushingUpLit.BHS
