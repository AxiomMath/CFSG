module

public import CFSG.Quasithin.Background.C118Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftNatY

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup

section Dict

variable {G : Type} [Group G] {X V : Subgroup G}

@[expose] def vEquiv (hVX : V ≤ X) : ↥V ≃* ↥(V.subgroupOf X) :=
  (Subgroup.subgroupOfEquivOfLe hVX).symm

@[expose] def autEmbed (hVX : V ≤ X) : MulAut ↥V ≃* MulAut ↥(V.subgroupOf X) :=
  MulAut.congr (vEquiv hVX)

theorem autEmbed_apply_coe (hVX : V ≤ X) (φ : MulAut ↥V) (v : ↥(V.subgroupOf X)) :
    ((((autEmbed hVX φ) v : ↥(V.subgroupOf X)) : ↥X) : G) =
      ((φ ((vEquiv hVX).symm v) : ↥V) : G) := rfl

theorem top_le_normalizer_subgroupOf (hVX : V ≤ X) (hX : X ≤ Subgroup.normalizer (V : Set G)) :
    (⊤ : Subgroup ↥X) ≤ Subgroup.normalizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) :=
  fun x _ => (mem_normalizer_subgroupOf_iff hVX x).2 (hX x.2)

theorem autEmbed_rho (hVX : V ≤ X) (hX : X ≤ Subgroup.normalizer (V : Set G)) (p : ↥X) :
    autEmbed hVX (rho V X hX p) =
      rho (V.subgroupOf X) ⊤ (top_le_normalizer_subgroupOf hVX hX) ⟨p, Subgroup.mem_top p⟩ := by
  apply MulEquiv.ext
  intro v'
  apply Subtype.ext
  apply Subtype.ext
  rw [autEmbed_apply_coe, rho_apply_coe, rho_apply_coe]
  rfl

theorem autOn_subgroupOf (hVX : V ≤ X) (hX : X ≤ Subgroup.normalizer (V : Set G)) {A : Subgroup G}
    (hAX : A ≤ X) :
    autOn (A.subgroupOf X) (V.subgroupOf X) = (autOn A V).map (autEmbed hVX).toMonoidHom := by
  have hX' := top_le_normalizer_subgroupOf hVX hX
  ext φ'
  rw [mem_autOn_iff_rho hX' le_top, Subgroup.mem_map]
  constructor
  · rintro ⟨p', hp'A, rfl⟩
    refine ⟨rho V X hX (p' : ↥X), ?_, ?_⟩
    · rw [mem_autOn_iff_rho hX hAX]
      exact ⟨(p' : ↥X), hp'A, rfl⟩
    · exact autEmbed_rho hVX hX (p' : ↥X)
  · rintro ⟨φ, hφ, rfl⟩
    rw [mem_autOn_iff_rho hX hAX] at hφ
    obtain ⟨p, hpA, rfl⟩ := hφ
    exact ⟨⟨p, Subgroup.mem_top p⟩, hpA, (autEmbed_rho hVX hX p).symm⟩

end Dict

section Maps

variable {G : Type} [Group G] {X V : Subgroup G}

theorem oddOrderSubgroup_map_of_injective {A B : Type*} [Group A] [Group B] {f : A →* B}
    (hf : Function.Injective f) (Y : Subgroup A) :
    oddOrderSubgroup (Y.map f) = (oddOrderSubgroup Y).map f := by
  unfold oddOrderSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨hy, hodd⟩
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    rwa [orderOf_injective f hf] at hodd
  · rintro ⟨x, ⟨hx, hodd⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rwa [orderOf_injective f hf]⟩

theorem rhoPreimage_map (hVX : V ≤ X) (hX : X ≤ Subgroup.normalizer (V : Set G))
    (D : Subgroup (MulAut V)) :
    (rhoPreimage (V.subgroupOf X) ⊤ (top_le_normalizer_subgroupOf hVX hX)
        (D.map (autEmbed hVX).toMonoidHom)).map X.subtype = rhoPreimage V X hX D := by
  ext g
  constructor
  · rintro ⟨g', hg', rfl⟩
    have hg'' : g' ∈ rhoPreimage (V.subgroupOf X) ⊤ (top_le_normalizer_subgroupOf hVX hX)
        (D.map (autEmbed hVX).toMonoidHom) := hg'
    rw [mem_rhoPreimage_top] at hg''
    refine ⟨g'.2, ?_⟩
    rw [← autEmbed_rho hVX hX g'] at hg''
    have := (Subgroup.mem_map_equiv (f := autEmbed hVX)).1 hg''
    simpa using this
  · intro hg
    obtain ⟨hgX, hgD⟩ := hg
    refine ⟨⟨g, hgX⟩, ?_, rfl⟩
    show (⟨g, hgX⟩ : ↥X) ∈ rhoPreimage (V.subgroupOf X) ⊤ (top_le_normalizer_subgroupOf hVX hX)
        (D.map (autEmbed hVX).toMonoidHom)
    rw [mem_rhoPreimage_top, ← autEmbed_rho hVX hX ⟨g, hgX⟩]
    exact Subgroup.mem_map_of_mem _ hgD

theorem blockOf_map (hVX : V ≤ X) (hX : X ≤ Subgroup.normalizer (V : Set G))
    {R : Subgroup G} (hRX : R ≤ X) (D : Subgroup (MulAut V)) :
    (blockOf (⊤ : Subgroup ↥X) (R.subgroupOf X) (V.subgroupOf X)
        (top_le_normalizer_subgroupOf hVX hX) (D.map (autEmbed hVX).toMonoidHom)).map X.subtype =
      blockOf X R V hX D := by
  have hbaum : (baum (R.subgroupOf X)).map X.subtype = baum R := by
    rw [← baum_map_of_injective X.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hRX]
  unfold blockOf
  rw [← oddOrderSubgroup_map_of_injective X.subtype_injective,
    Subgroup.map_inf _ _ _ X.subtype_injective, Subgroup.map_sup, map_oddOrderSubgroup_top, hbaum,
    rhoPreimage_map hVX hX D]

theorem modComm_map (hVX : V ≤ X) (D : Subgroup (MulAut V)) :
    (modComm (V.subgroupOf X) (D.map (autEmbed hVX).toMonoidHom)).map X.subtype = modComm V D := by
  unfold modComm
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨g', ⟨a', ⟨a, ha, rfl⟩, v', rfl⟩, rfl⟩
    refine ⟨a, ha, (vEquiv hVX).symm v', ?_⟩
    simp only [map_mul, map_inv, Subgroup.coe_subtype]
    rfl
  · rintro ⟨a, ha, v, rfl⟩
    refine ⟨((autEmbed hVX a) (vEquiv hVX v) : ↥X) * ((vEquiv hVX v : ↥(V.subgroupOf X)) : ↥X)⁻¹,
      ⟨autEmbed hVX a, ⟨a, ha, rfl⟩, vEquiv hVX v, rfl⟩, ?_⟩
    simp only [map_mul, map_inv, Subgroup.coe_subtype]
    rfl

end Maps

end CFSG.QuasithinUnique.Setup.Lift
