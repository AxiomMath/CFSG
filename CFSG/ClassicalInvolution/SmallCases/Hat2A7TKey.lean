module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TFix
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7TTwoTight

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section Key

variable {F : Type} [Group F] [Finite F]

omit [Finite F] in
theorem mem_normalizer_map_conj {M : Subgroup F} {x : F} (hx : x ∈ Subgroup.normalizer (M : Set F))
    (g : F) : g * x * g⁻¹ ∈ Subgroup.normalizer ((M.map (MulAut.conj g).toMonoidHom : Subgroup F) :
      Set F) := by
  rw [← map_conj_eq_iff_mem_normalizer, map_map_conj]
  have h1 : g * x * g⁻¹ * g = g * x := by group
  rw [h1]
  have h2 := map_conj_eq_iff_mem_normalizer.mpr hx
  calc M.map (MulAut.conj (g * x)).toMonoidHom
      = (M.map (MulAut.conj x).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
        rw [map_map_conj]
    _ = M.map (MulAut.conj g).toMonoidHom := by rw [h2]

variable (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F) (P1 : ClassicalQuasisimple F)

include hZ IH P1 in
theorem mem_normalizer_of_conj_mem {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z)
    (hodd : Odd (Nat.card (cliqueSet K))) {a : F} (ha : a ∈ cliqueGrp K) (ha1 : a ≠ 1) {g : F}
    (hb : g * a * g⁻¹ ∈ Subgroup.normalizer (cliqueGrp K : Set F)) :
    g ∈ Subgroup.normalizer (cliqueGrp K : Set F) := by
  have hKm : IsMember K := ⟨z, hK⟩
  set b : F := g * a * g⁻¹ with hbdef
  have hb2 : b * b = 1 := by
    have := cliqueGrp_sq hZ IH hKm ha
    calc b * b = g * (a * a) * g⁻¹ := by rw [hbdef]; group
      _ = 1 := by rw [this]; group
  have hb1 : b ≠ 1 := by
    intro h
    apply ha1
    have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [this, ← hbdef, h]
    group
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
  obtain ⟨N, hN, hbN⟩ := exists_member_normalized hZ IH hK hodd
    (Subgroup.zpowers_le.mpr hb) (isPGroup_zpowers_of_orderOf_eq_two hbo)
  have hbN' : b ∈ Subgroup.normalizer (N : Set F) := hbN (Subgroup.mem_zpowers b)
  obtain ⟨zN, hzN⟩ := hN.1
  obtain ⟨R, hRN, hR2, hR8, hRb⟩ := exists_two_subgroup_centralizing hzN.witness hbN' hb2
  obtain ⟨hzR, huniq⟩ := two_subgroup_unique_involution hzN hRN hR2 (by omega)
  set R' : Subgroup F := R.map (MulAut.conj g⁻¹).toMonoidHom with hR'def
  have hR'H : R' ≤ Subgroup.normalizer (cliqueGrp K : Set F) := by
    rintro _ ⟨r, hr, rfl⟩
    refine centralizer_le_normalizer hZ IH hKm ha ha1 ?_
    show g⁻¹ * r * g⁻¹⁻¹ * a = a * (g⁻¹ * r * g⁻¹⁻¹)
    have h1 : b * r = r * b := hRb r hr
    calc g⁻¹ * r * g⁻¹⁻¹ * a = g⁻¹ * (r * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * r) * g := by rw [← hbdef, ← h1]
      _ = a * (g⁻¹ * r * g⁻¹⁻¹) := by group
  obtain ⟨M', hM', hR'M'⟩ := exists_member_normalized hZ IH hK hodd hR'H (hR2.map _)
  set M : Subgroup F := M'.map (MulAut.conj g).toMonoidHom with hMdef
  have hRM : R ≤ Subgroup.normalizer (M : Set F) := by
    intro r hr
    have h1 : g⁻¹ * r * g ∈ Subgroup.normalizer (M' : Set F) :=
      hR'M' ⟨r, hr, by simp⟩
    have h2 := mem_normalizer_map_conj h1 g
    have h3 : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
    rwa [h3] at h2
  obtain ⟨zM, hzM⟩ := isMember_map_conj hM'.1 g
  have hMz : M ≤ Subgroup.centralizer ({zN} : Set F) :=
    le_centralizer_of_two_group_normalizes hzM (P1 M zM hzM) hRM hR2 (by omega) hzR huniq
  have hzNA : zN ∈ cliqueGrp K := Subgroup.subset_closure ⟨N, hzN, hN.2⟩
  have hzN1 : zN ≠ 1 := by
    intro h
    have := hzN.orderOf_eq_two
    rw [h, orderOf_one] at this
    omega
  have hKM : CommOrEq K M :=
    (mem_clique_iff_le_centralizer hZ IH hKm ⟨zM, hzM⟩ hzNA hzN1).mp hMz
  have hKgM : CommOrEq (K.map (MulAut.conj g).toMonoidHom) M :=
    commOrEq_map_conj' hM'.2 g
  have hKKg : CommOrEq K (K.map (MulAut.conj g).toMonoidHom) :=
    commOrEq_trans hZ IH hKm ⟨zM, hzM⟩ (isMember_map_conj hKm g) hKM hKgM.symm
  exact mem_normalizer_of_commOrEq hZ IH hKm hKKg

end Key

end CFSG.ClassicalInvolution.Hat2A7T
