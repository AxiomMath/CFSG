module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12S8SplDef

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem s8_ext_iota_mem {G : Type} [Group G] {V : Subgroup G}
    {Γ : Type} [Group Γ] (ι : ↥V →* Γ) (ρ : Γ →* MulAut ↥V) (hker : ρ.ker = ι.range)
    {Z : Subgroup (MulAut ↥V)} (a : ↥V) : ι a ∈ Z.comap ρ := by
  have h : ι a ∈ ρ.ker := by
    rw [hker]
    exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
  rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp h]
  exact Subgroup.one_mem Z

private theorem s8_ext_coord_aux {G : Type} [Group G] {V : Subgroup G}
    {Γ : Type} [Group Γ] (ι : ↥V →* Γ) (ρ : Γ →* MulAut ↥V) (hι : Function.Injective ι)
    {Z : Subgroup (MulAut ↥V)} (hιmem : ∀ a : ↥V, ι a ∈ Z.comap ρ)
    {Vi : Subgroup ↥V} {φi' : (Fin 5 → ZMod 2) → ↥V} (hc : Sec128Coord Vi φi') :
    Sec128Coord ((Vi.map ι).subgroupOf (Z.comap ρ))
      (fun v => (⟨ι (φi' v), hιmem (φi' v)⟩ : ↥(Z.comap ρ))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_of_mem ι (hc.mem v hv)
  · intro v w hv hw
    apply Subtype.ext
    show ι (φi' (v + w)) = ι (φi' v) * ι (φi' w)
    rw [hc.mul v w hv hw, map_mul]
  · intro v hv hv1
    have h : ι (φi' v) = ι 1 := by
      simpa using congrArg Subtype.val hv1
    exact hc.inj v hv (hι h)
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    obtain ⟨v, hv, hvx⟩ := hc.surj a ha
    refine ⟨v, hv, ?_⟩
    apply Subtype.ext
    show ι (φi' v) = (x : Γ)
    rw [hvx, hax]

theorem s8_ext_data {G : Type} [Group G] {V : Subgroup G} (hcomm : ∀ a b : ↥V, a * b = b * a)
    {Γ : Type} [Group Γ] (ι : ↥V →* Γ) (ρ : Γ →* MulAut ↥V) (hι : Function.Injective ι)
    (hker : ρ.ker = ι.range) (hequi : ∀ (γ : Γ) (a : ↥V), γ * ι a * γ⁻¹ = ι (ρ γ a))
    {Z : Subgroup (MulAut ↥V)} (hZ : Z ≤ ρ.range) {V1 V2 : Subgroup ↥V}
    (hsp : Sec128SplitNatOn V Z V1 V2) :
    ∃ (φ1 φ2 : (Fin 5 → ZMod 2) → ↥(Z.comap ρ)) (α β : ↥(Z.comap ρ) →* S8A5),
      S8Data ((V1.map ι).subgroupOf (Z.comap ρ)) ((V2.map ι).subgroupOf (Z.comap ρ)) φ1 φ2 α β := by
  obtain ⟨φ1', φ2', ψ, hsup, hinf, hc1, hc2, hact⟩ := hsp
  have hιmem : ∀ a : ↥V, ι a ∈ Z.comap ρ := fun a => s8_ext_iota_mem ι ρ hker a
  let φ1 : (Fin 5 → ZMod 2) → ↥(Z.comap ρ) := fun v => ⟨ι (φ1' v), hιmem (φ1' v)⟩
  let φ2 : (Fin 5 → ZMod 2) → ↥(Z.comap ρ) := fun v => ⟨ι (φ2' v), hιmem (φ2' v)⟩
  let α : ↥(Z.comap ρ) →* S8A5 :=
    (MonoidHom.fst S8A5 S8A5).comp (ψ.symm.toMonoidHom.comp (ρ.subgroupComap Z))
  let β : ↥(Z.comap ρ) →* S8A5 :=
    (MonoidHom.snd S8A5 S8A5).comp (ψ.symm.toMonoidHom.comp (ρ.subgroupComap Z))
  have hρ : ∀ g : ↥(Z.comap ρ), ρ (g : Γ) = (ψ (α g, β g) : MulAut ↥V) := by
    intro g
    have h1 : (α g, β g) = ψ.symm (ρ.subgroupComap Z g) := Prod.ext rfl rfl
    rw [h1, MulEquiv.apply_symm_apply]
    rfl
  refine ⟨φ1, φ2, α, β, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact s8_ext_coord_aux ι ρ hι hιmem hc1
  · exact s8_ext_coord_aux ι ρ hι hιmem hc2
  · intro x hx y hy
    rw [Subgroup.mem_subgroupOf] at hx hy
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hy
    apply Subtype.ext
    show (x : Γ) * (y : Γ) = (y : Γ) * (x : Γ)
    rw [← hax, ← hby, ← map_mul ι a b, ← map_mul ι b a, hcomm a b]
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rw [Subgroup.mem_subgroupOf] at hx1 hx2
    obtain ⟨a, ha, hax⟩ := Subgroup.mem_map.mp hx1
    obtain ⟨b, hb, hby⟩ := Subgroup.mem_map.mp hx2
    have hab : a = b := hι (hax.trans hby.symm)
    have ha1 : a = 1 := by
      have hmem : a ∈ V1 ⊓ V2 := Subgroup.mem_inf.mpr ⟨ha, hab ▸ hb⟩
      rw [hinf] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact Subtype.ext (by rw [← hax, ha1, map_one]; rfl)
  · intro g v hv
    apply Subtype.ext
    show (g : Γ) * ι (φ1' v) * (g : Γ)⁻¹ =
      ι (φ1' (permVec ((α g : S8A5) : Equiv.Perm (Fin 5)) v))
    rw [hequi (g : Γ) (φ1' v), hρ g, (hact (α g) (β g) v hv).1]
  · intro g v hv
    apply Subtype.ext
    show (g : Γ) * ι (φ2' v) * (g : Γ)⁻¹ =
      ι (φ2' (permVec ((β g : S8A5) : Equiv.Perm (Fin 5)) v))
    rw [hequi (g : Γ) (φ2' v), hρ g, (hact (α g) (β g) v hv).2]
  · intro g hα hβ
    have hρg : ρ (g : Γ) = 1 := by
      rw [hρ g, hα, hβ]
      simp
    have hmem : (g : Γ) ∈ ρ.ker := MonoidHom.mem_ker.mpr hρg
    have hrange : (g : Γ) ∈ ι.range := by rwa [← hker]
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hrange
    have ha' : a ∈ V1 ⊔ V2 := by rw [hsup]; exact Subgroup.mem_top a
    obtain ⟨a1, ha1, a2, ha2, haeq⟩ := s8_mem_sup_of_commute (fun x _ y _ => hcomm x y) ha'
    have hg : g = (⟨ι a1, hιmem a1⟩ : ↥(Z.comap ρ)) * ⟨ι a2, hιmem a2⟩ := by
      apply Subtype.ext
      show (g : Γ) = ι a1 * ι a2
      calc (g : Γ) = ι a := ha.symm
        _ = ι (a1 * a2) := congrArg ι haeq
        _ = ι a1 * ι a2 := map_mul ι a1 a2
    rw [hg]
    exact Subgroup.mul_mem_sup
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem ι ha1))
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem ι ha2))
  · intro a b
    have hmemZ : (ψ (a, b) : MulAut ↥V) ∈ Z := (ψ (a, b)).2
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.mp (hZ hmemZ)
    have hγZ : γ ∈ Z.comap ρ := by
      rw [Subgroup.mem_comap, hγ]
      exact (ψ (a, b)).2
    have hρZ : ρ.subgroupComap Z ⟨γ, hγZ⟩ = ψ (a, b) := Subtype.ext hγ
    refine ⟨⟨γ, hγZ⟩, ?_, ?_⟩
    · change (ψ.symm (ρ.subgroupComap Z ⟨γ, hγZ⟩)).1 = a
      rw [hρZ, MulEquiv.symm_apply_apply]
    · change (ψ.symm (ρ.subgroupComap Z ⟨γ, hγZ⟩)).2 = b
      rw [hρZ, MulEquiv.symm_apply_apply]

end CFSG.OddStandard.SmallF3.Omega
