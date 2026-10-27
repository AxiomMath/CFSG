module

public import CFSG.GH74.E2.Local
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH74.E2

open Subgroup

theorem localK_of_component {G : Type} [Group G] [Finite G] (hH : Hyp G) {t : G}
    (ht : orderOf t = 2)
    (huniq : ∀ K₁ K₂ : Subgroup G, IsCompCen t K₁ → IsCompCen t K₂ → K₁ = K₂)
    {K : Subgroup G} (hK : IsCompCen t K) :
    LocalK ↥(Cen t) (CFSG.pCore 2 ↥(Cen t)) (K.subgroupOf (Cen t)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : CFSG.pPrimeCore 2 ↥(Cen t) = ⊥ := hH.pPrimeCore_cen_bot ht
  have hfit : CFSG.fittingSubgroup ↥(Cen t) = CFSG.pCore 2 ↥(Cen t) :=
    CFSG.Fitting_eq_pcore _ 2 hcore
  have hKc : CFSG.IsComponent (K.subgroupOf (Cen t)) := hK.2
  have huniqC : ∀ L : Subgroup ↥(Cen t), CFSG.IsComponent L → L = K.subgroupOf (Cen t) := by
    intro L hL
    have hso : (L.map (Cen t).subtype).subgroupOf (Cen t) = L :=
      Subgroup.comap_map_eq_self_of_injective (Cen t).subtype_injective L
    have h1 : IsCompCen t (L.map (Cen t).subtype) := by
      refine ⟨?_, ?_⟩
      · rintro _ ⟨x, -, rfl⟩
        exact x.2
      · rw [hso]
        exact hL
    have h2 := huniq _ _ h1 hK
    rw [← h2, hso]
  have hKnormal : (K.subgroupOf (Cen t)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 := CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hKc
    have h2 := huniqC _ h1
    have h3 : g * n * g⁻¹ ∈ (K.subgroupOf (Cen t)).map (MulAut.conj g).toMonoidHom :=
      ⟨n, hn, rfl⟩
    rwa [h2] at h3
  have hlayer : CFSG.layer ↥(Cen t) = K.subgroupOf (Cen t) := by
    have h1 : {L : Subgroup ↥(Cen t) | CFSG.IsComponent L} = {K.subgroupOf (Cen t)} := by
      ext L
      exact ⟨fun hL => huniqC L hL, fun hL => by rw [Set.mem_singleton_iff] at hL; exact hL ▸ hKc⟩
    simp only [CFSG.layer.eq_sSup]
    rw [h1, sSup_singleton]
  have hQnormal : (CFSG.pCore 2 ↥(Cen t)).Normal := CFSG.pCore_normal (p := 2) (G := ↥(Cen t))
  have hcomm : ∀ q ∈ CFSG.pCore 2 ↥(Cen t), ∀ k ∈ K.subgroupOf (Cen t), q * k = k * q := by
    intro q hq k hk
    have h1 := CFSG.LocalCores.fitting_layer_commute (G := ↥(Cen t))
    have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
    rw [hfit] at h2
    have h3 := h2 hq
    rw [mem_centralizer_iff] at h3
    rw [hlayer] at h3
    exact (h3 k hk).symm
  refine ⟨hQnormal, CFSG.pCore_isPGroup (p := 2) (G := ↥(Cen t)), hKnormal, hKc.1, hcomm, ?_⟩
  intro c hcq hck
  have hle : CFSG.generalizedFitting ↥(Cen t) ≤ Subgroup.centralizer ({c} : Set ↥(Cen t)) := by
    simp only [CFSG.generalizedFitting.eq_sup]
    rw [hfit, hlayer]
    refine sup_le (fun q hq => ?_) (fun k hk => ?_)
    · rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hcq q hq
    · rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      exact hck k hk
  have hcgen : c ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥(Cen t) : Set ↥(Cen t)) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 := hle hy
    rw [mem_centralizer_iff] at h1
    exact (h1 c rfl).symm
  have hcF := CFSG.centralizer_generalizedFitting_le ↥(Cen t) hcgen
  have hcF' : c ∈ CFSG.pCore 2 ↥(Cen t) ⊔ K.subgroupOf (Cen t) := by
    simp only [CFSG.generalizedFitting.eq_sup] at hcF
    rwa [hfit, hlayer] at hcF
  have := hQnormal
  obtain ⟨q, hq, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hcF'
  have hkcen : (⟨k, hk⟩ : ↥(K.subgroupOf (Cen t))) ∈
      Subgroup.center ↥(K.subgroupOf (Cen t)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have h1 : q * k * (x : ↥(Cen t)) = (x : ↥(Cen t)) * (q * k) := hck x x.2
    have h2 : q * (x : ↥(Cen t)) = (x : ↥(Cen t)) * q := hcomm q hq x x.2
    have h3 : q * (k * (x : ↥(Cen t))) = q * ((x : ↥(Cen t)) * k) := by
      calc q * (k * (x : ↥(Cen t))) = q * k * (x : ↥(Cen t)) := (mul_assoc _ _ _).symm
        _ = (x : ↥(Cen t)) * (q * k) := h1
        _ = ((x : ↥(Cen t)) * q) * k := (mul_assoc _ _ _).symm
        _ = (q * (x : ↥(Cen t))) * k := by rw [h2]
        _ = q * ((x : ↥(Cen t)) * k) := mul_assoc _ _ _
    exact (mul_left_cancel h3).symm
  let Zc : Subgroup ↥(Cen t) :=
    (Subgroup.center ↥(K.subgroupOf (Cen t))).map (K.subgroupOf (Cen t)).subtype
  have hZcnormal : Zc.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hn
    have hz' : z ∈ Subgroup.center ↥(K.subgroupOf (Cen t)) := hz
    have hmem : g * ((z : ↥(Cen t))) * g⁻¹ ∈ K.subgroupOf (Cen t) := hKnormal.conj_mem _ z.2 g
    refine ⟨⟨_, hmem⟩, ?_, rfl⟩
    show (⟨g * (z : ↥(Cen t)) * g⁻¹, hmem⟩ : ↥(K.subgroupOf (Cen t))) ∈
      Subgroup.center ↥(K.subgroupOf (Cen t))
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    have hx' : g⁻¹ * (x : ↥(Cen t)) * g ∈ K.subgroupOf (Cen t) := by
      have h1 := hKnormal.conj_mem _ x.2 g⁻¹
      simpa using h1
    have h1 := Subgroup.mem_center_iff.mp hz' ⟨g⁻¹ * (x : ↥(Cen t)) * g, hx'⟩
    have h2 : g⁻¹ * (x : ↥(Cen t)) * g * (z : ↥(Cen t)) =
        (z : ↥(Cen t)) * (g⁻¹ * (x : ↥(Cen t)) * g) := congrArg Subtype.val h1
    show (x : ↥(Cen t)) * (g * (z : ↥(Cen t)) * g⁻¹) = g * (z : ↥(Cen t)) * g⁻¹ * (x : ↥(Cen t))
    calc (x : ↥(Cen t)) * (g * (z : ↥(Cen t)) * g⁻¹)
        = g * (g⁻¹ * (x : ↥(Cen t)) * g * (z : ↥(Cen t))) * g⁻¹ := by group
      _ = g * ((z : ↥(Cen t)) * (g⁻¹ * (x : ↥(Cen t)) * g)) * g⁻¹ := by rw [h2]
      _ = g * (z : ↥(Cen t)) * g⁻¹ * (x : ↥(Cen t)) := by group
  have hZcabel : IsMulCommutative ↥Zc := ⟨⟨fun a b => by
    obtain ⟨z₁, hz₁, h₁⟩ := a.2
    obtain ⟨z₂, hz₂, h₂⟩ := b.2
    apply Subtype.ext
    have e1 : (a : ↥(Cen t)) = (z₁ : ↥(Cen t)) := h₁.symm
    have e2 : (b : ↥(Cen t)) = (z₂ : ↥(Cen t)) := h₂.symm
    show (a : ↥(Cen t)) * b = b * a
    rw [e1, e2]
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz₂) z₁)⟩⟩
  have hZcnil : Group.IsNilpotent ↥Zc := by
    let : CommGroup ↥Zc := IsMulCommutative.instCommGroup
    infer_instance
  have hZcF : Zc ≤ CFSG.fittingSubgroup ↥(Cen t) := le_sSup ⟨hZcnormal, hZcnil⟩
  have hkQ : k ∈ CFSG.pCore 2 ↥(Cen t) := by
    rw [← hfit]
    exact hZcF ⟨⟨k, hk⟩, hkcen, rfl⟩
  exact (CFSG.pCore 2 ↥(Cen t)).mul_mem hq hkQ

end CFSG.GH74.E2
