module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Hyp
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911ZJ
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911E16
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911ConjRank
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911W1
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911ConclL34
public import CFSG.GH74.GLS.Stage2.Signalizer.L64Sub
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

namespace EndAux

section Transport

variable {G : Type} [Group G]

theorem map_center_eq_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  ext b
  rw [Subgroup.mem_map, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩ g
    obtain ⟨a', rfl⟩ := e.surjective g
    have := Subgroup.mem_center_iff.mp ha a'
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, this]
  · intro hb
    refine ⟨e.symm b, Subgroup.mem_center_iff.mpr fun g => ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hb (e g)

theorem lieModel_quot_center_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {t : StatedLieTag} {n p f : ℕ} (h : LieModel (A ⧸ Subgroup.center A) t n p f) :
    LieModel (B ⧸ Subgroup.center B) t n p f :=
  CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e (map_center_eq_of_equiv e)) h

theorem isPGroup_center_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) {p : ℕ}
    (h : IsPGroup p ↥(Subgroup.center A)) : IsPGroup p ↥(Subgroup.center B) := by
  have hm : IsPGroup p ↥((Subgroup.center A).map e.toMonoidHom) :=
    h.of_equiv ((Subgroup.center A).equivMapOfInjective e.toMonoidHom e.injective)
  rw [map_center_eq_of_equiv] at hm
  exact hm

theorem isComponent_conj (c : G) (N : Subgroup G) {J : Subgroup ↥N} (hJ : IsComponent J) :
    IsComponent (((J.map N.subtype).map (MulAut.conj c).toMonoidHom).subgroupOf
      (N.map (MulAut.conj c).toMonoidHom)) := by
  let e : ↥N ≃* ↥(N.map (MulAut.conj c).toMonoidHom) := (MulAut.conj c).subgroupMap N
  have h := LocalCores.isComponent_map_mulEquiv e hJ
  have heq : ((J.map N.subtype).map (MulAut.conj c).toMonoidHom).subgroupOf
      (N.map (MulAut.conj c).toMonoidHom) = J.map e.toMonoidHom := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, hjy⟩
      exact ⟨j, hj, Subtype.ext hjy⟩
    · rintro ⟨j, hj, hjy⟩
      exact ⟨(j : G), ⟨j, hj, rfl⟩, by rw [← hjy]; rfl⟩
  rw [heq]
  exact h

theorem layer_eq_top_of_qs {Q : Type*} [Group Q] (hq : IsQuasisimple Q) : layer Q = ⊤ :=
  top_le_iff.mp (le_sSup (show IsComponent (⊤ : Subgroup Q) from
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hq,
      Subgroup.IsSubnormal.top⟩))

theorem commutator_Em_ne_bot_of_qs {J₁ W₁ : Subgroup G} {z : G} (hq : IsQuasisimple ↥J₁)
    (hz : z ∈ J₁) (hW0 : W₁ ≠ ⊥) (hWz : ⁅W₁, zpowers z⁆ = W₁) : ⁅Em J₁, W₁⁆ ≠ ⊥ := by
  have hEm : Em J₁ = J₁ := by
    rw [Em_def, layer_eq_top_of_qs hq, Subgroup.map_top, Subgroup.range_subtype]
  rw [hEm]
  intro hbot
  apply hW0
  calc W₁ = ⁅W₁, zpowers z⁆ := hWz.symm
    _ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro w hw y hy
      have hyJ : y ∈ J₁ := Subgroup.zpowers_le.mpr hz hy
      have h1 : ⁅y, w⁆ = 1 :=
        Subgroup.mem_bot.mp (hbot ▸ Subgroup.commutator_mem_commutator hyJ hw)
      exact Subgroup.mem_bot.mpr (by rw [← commutatorElement_inv, h1, inv_one])

end Transport

end EndAux

open EndAux in
theorem end911_of (h43E : Prop4_3E) : End911 := by
  intro G _ _ z k S M p X V N H hXE J hJ hL
  have hp := H.ctx.prime
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : p ≠ 2 := H.ctx.odd
  have hoddp : Odd p := hp.odd_of_ne_two hpodd
  have hNtop : N ≠ ⊤ := H.hN.1
  have hZodd := odd_card_center_of_component hp hoddp H.hFm hJ
  have hZp := isPGroup_center_of_component hp H.hFm hJ
  obtain ⟨E, hEJ, hEe, hE16⟩ := exists_elemAb16 hJ hL hZodd
  have := hEe
  set J' : Subgroup G := J.map N.subtype with hJ'
  set E' : Subgroup G := E.map N.subtype with hE'
  have hE'e : IsElementaryAbelian 2 ↥E' := IsElementaryAbelian.map N.subtype
  have hE'16 : Nat.card ↥E' = 16 := by
    rw [hE', Subgroup.card_map_of_injective N.subtype_injective, hE16]
  obtain ⟨g, hg⟩ := exists_conj_mem_of_rank H.ctx.ctx.central H.ctx.ctx.std.gen4 hE'e hE'16
  have hgJ : g * z * g⁻¹ ∈ J' := Subgroup.map_mono hEJ hg
  set φ : G →* G := (MulAut.conj g⁻¹).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.conj g⁻¹).injective
  set N₁ : Subgroup G := N.map φ with hN₁def
  set J₁ : Subgroup G := J'.map φ with hJ₁def
  set X₂ : Subgroup G := X.map φ with hX₂def
  have hzJ₁ : z ∈ J₁ := ⟨g * z * g⁻¹, hgJ, by simp [hφ]; group⟩
  have hJN₁ : J₁ ≤ N₁ := Subgroup.map_mono (Subgroup.map_subtype_le J)
  have hN₁top : N₁ ≠ ⊤ := by
    intro h
    apply hNtop
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [← Subgroup.card_map_of_injective hφinj, ← hN₁def, h, Subgroup.card_top]
  have hJN : IsComponent (J₁.subgroupOf N₁) := isComponent_conj g⁻¹ N hJ
  have hX₂p : IsPGroup p ↥X₂ :=
    (H.ctx.P_pgroup.to_le H.hXP).of_equiv (X.equivMapOfInjective φ hφinj)
  have hX₂0 : X₂ ≠ ⊥ := fun h => H.hX0 ((Subgroup.map_eq_bot_iff_of_injective X hφinj).mp h)
  have hJ'Em : J' ≤ Em N := by
    rw [Em_def]
    exact Subgroup.map_mono (le_sSup hJ)
  have hX₂J : X₂ ≤ centralizer (J₁ : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    have h1 : j * x = x * j := Subgroup.mem_centralizer_iff.mp (hXE hx) j (hJ'Em hj)
    show φ j * φ x = φ x * φ j
    rw [← map_mul, ← map_mul, h1]
  have hX₂N : normalizer (X₂ : Set G) ≤ N₁ := by
    rw [hX₂def, ← Subgroup.map_equiv_normalizer_eq X (MulAut.conj g⁻¹)]
    exact Subgroup.map_mono H.hXN
  obtain ⟨W₁, hW0, hWp, hWJ, hWz, hWinv⟩ :=
    exists_W₁ H.ctx hN₁top hzJ₁ hJN hJN₁ hX₂p hX₂0 hX₂J hX₂N
  have hJ₁top : J₁ ≠ ⊤ := fun h => hN₁top (top_le_iff.mp (h ▸ hJN₁))
  have hSig : Sig4Sub G z J₁ p W₁ :=
    ⟨hJ₁top, ⟨hp, hpodd, hzJ₁, hWJ, hWp, hW0,
      fun c hcJ hcz => hWinv c hcJ (Subgroup.mem_centralizer_singleton_iff.mp hcz), hWz⟩⟩
  let eJ : ↥J ≃* ↥J₁ := (J.equivMapOfInjective N.subtype N.subtype_injective).trans
    ((MulAut.conj g⁻¹).subgroupMap J')
  have hJqs : IsQuasisimple ↥J₁ := CFSG.LocalCores.isQuasisimple_of_mulEquiv eJ hJ.1
  have hL₁ : LieModel (↥J₁ ⧸ Subgroup.center ↥J₁) .PSL 3 2 2 :=
    lieModel_quot_center_of_equiv eJ hL
  have hZp₁ : IsPGroup p ↥(Subgroup.center ↥J₁) := isPGroup_center_of_equiv eJ hZp
  have hE : ⁅Em J₁, W₁⁆ ≠ ⊥ := commutator_Em_ne_bot_of_qs hJqs hzJ₁ hW0 hWz
  have hconc := L64.prop4_3Esub_of h43E H.ctx.ctx hSig hE
  exact false_of_concl43E_L34 hp hpodd hzJ₁ hJqs hL₁ hZp₁ hWJ hW0 hWp hWz hconc

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
