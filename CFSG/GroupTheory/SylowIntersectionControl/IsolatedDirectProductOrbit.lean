module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs
import CFSG.GroupTheory.SylowIntersectionControl.GomiComponentIsolated
import CFSG.GroupTheory.NormalizerInterval
import CFSG.LocalAnalysis.ComponentClassification.SubgroupFixedInvolution

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type} [Group G] [Finite G]

private def conjOrbit (H A : Subgroup G) : Set (Subgroup G) :=
  {B | ∃ h ∈ H, B = A.map (MulAut.conj h).toMonoidHom}

omit [Finite G] in
private theorem map_conj_one_eq (B : Subgroup G) :
    B.map (MulAut.conj (1 : G)).toMonoidHom = B := by
  ext y
  simp

omit [Finite G] in
private theorem self_mem_conjOrbit (H A : Subgroup G) : A ∈ conjOrbit H A :=
  ⟨1, one_mem H, (map_conj_one_eq A).symm⟩

omit [Finite G] in
private theorem conjOrbit_subset {S : Set (Subgroup G)} {H A : Subgroup G}
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hA : A ∈ S) :
    conjOrbit H A ⊆ S := by
  rintro _ ⟨h, -, rfl⟩
  exact hSG h A hA

omit [Finite G] in
private theorem map_conj_mem_conjOrbit {H A B : Subgroup G} (hB : B ∈ conjOrbit H A) {k : G}
    (hk : k ∈ H) : B.map (MulAut.conj k).toMonoidHom ∈ conjOrbit H A := by
  obtain ⟨h, hh, rfl⟩ := hB
  exact ⟨k * h, mul_mem hk hh, Subgroup.map_conj_map_conj A h k⟩

omit [Finite G] in
private theorem of_map_conj_mem_conjOrbit {H A B : Subgroup G} {k : G} (hk : k ∈ H)
    (hB : B.map (MulAut.conj k).toMonoidHom ∈ conjOrbit H A) : B ∈ conjOrbit H A := by
  have := map_conj_mem_conjOrbit hB (inv_mem hk)
  rwa [Subgroup.map_conj_map_conj, inv_mul_cancel, map_conj_one_eq] at this

private theorem mem_normalizer_of_forall_conj_mem {X : Subgroup G} {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ normalizer (X : Set G) := by
  let f : X → X := fun x => ⟨g * x * g⁻¹, h x x.2⟩
  have hf : Function.Surjective f := Finite.injective_iff_surjective.mp fun a b hab =>
    Subtype.ext (by simpa [f] using congrArg Subtype.val hab)
  refine mem_normalizer_iff.mpr fun x => ⟨h x, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := hf ⟨_, hx⟩
  have hyx : (y : G) = x := by simpa [f] using congrArg Subtype.val hy
  exact hyx ▸ y.2

private theorem mem_normalizer_sSup {T : Set (Subgroup G)} {k : G}
    (h : ∀ B ∈ T, B.map (MulAut.conj k).toMonoidHom ∈ T) :
    k ∈ normalizer ((sSup T : Subgroup G) : Set G) := by
  have hle : (sSup T).map (MulAut.conj k).toMonoidHom ≤ sSup T :=
    map_le_iff_le_comap.mpr (sSup_le fun B hB => map_le_iff_le_comap.mp (le_sSup (h B hB)))
  exact mem_normalizer_of_forall_conj_mem fun x hx => hle ⟨x, hx, rfl⟩

private theorem sSup_conjOrbit_inf_sSup_sdiff_eq_bot {S : Set (Subgroup G)} {N H A : Subgroup G}
    (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hA : A ∈ S) :
    sSup (conjOrbit H A) ⊓ sSup (S \ conjOrbit H A) = ⊥ := by
  set O := conjOrbit H A with hO
  have hOS : O ⊆ S := conjOrbit_subset hSG hA
  refine le_bot_iff.mp fun x hx => ?_
  have hxE : x ∈ sSup O := (mem_inf.mp hx).1
  have hxE' : x ∈ sSup (S \ O) := (mem_inf.mp hx).2
  have hxN : x ∈ N := (hN.sSup_diff_le O hOS) hxE
  have hx1 : (⟨x, hxN⟩ : N) = 1 := by
    refine hN.ext_coord fun J hJ => ?_
    rw [map_one]
    refine (hN.coord_eq_one_iff hJ ⟨x, hxN⟩).mpr ?_
    by_cases hJO : J ∈ O
    · have hsub : S \ O ⊆ S \ {J} := fun y hy => ⟨hy.1, fun hyJ => hy.2 (hyJ ▸ hJO)⟩
      exact sSup_le_sSup hsub hxE'
    · have hsub : O ⊆ S \ {J} := fun y hy => ⟨hOS hy, fun hyJ => hJO (hyJ ▸ hy)⟩
      exact sSup_le_sSup hsub hxE
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hx1

omit [Finite G] in
private theorem mem_of_mem_sup_of_le {E H N : Subgroup G} (hHE : H ≤ normalizer (E : Set G))
    (hEN : E ≤ N) (hHN : H ⊓ N = ⊥) {c : G} (hc : c ∈ E ⊔ H) (hcN : c ∈ N) : c ∈ E := by
  have hc' : c ∈ H ⊔ E := by rwa [sup_comm] at hc
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right H E hHE] at hc'
  obtain ⟨h, hh, e, he, hhe⟩ := hc'
  have heN : e ∈ N := hEN he
  have hhN : h ∈ N := by
    have : h = c * e⁻¹ := by rw [← hhe]; group
    rw [this]
    exact mul_mem hcN (inv_mem heN)
  have hh1 : h = 1 := by
    have : h ∈ H ⊓ N := mem_inf.mpr ⟨hh, hhN⟩
    rwa [hHN, mem_bot] at this
  rw [← hhe, hh1]
  simpa using he

theorem IsPIsolatedOver.exists_map_conj_eq_of_isDirectProduct {H N : Subgroup G}
    {S : Set (Subgroup G)} (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H)
    (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    (hHN : H ⊓ N = ⊥) (hS : ∀ J ∈ S, 2 ∣ Nat.card J) {A B : Subgroup G} (hA : A ∈ S)
    (hB : B ∈ S) : ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom = B := by
  by_cases hBO : B ∈ conjOrbit H A
  · obtain ⟨h, hh, hhB⟩ := hBO
    exact ⟨h, hh, hhB.symm⟩
  · set O := conjOrbit H A with hO
    set E := sSup O with hE
    set E' := sSup (S \ O) with hE'
    have hOS : O ⊆ S := conjOrbit_subset hSG hA
    have hBE' : B ≤ E' := le_sSup ⟨hB, hBO⟩
    have hHE : H ≤ normalizer (E : Set G) := fun h hh =>
      mem_normalizer_sSup fun C hC => map_conj_mem_conjOrbit hC hh
    have hHE' : H ≤ normalizer (E' : Set G) := fun h hh =>
      mem_normalizer_sSup fun C hC =>
        ⟨hSG h C hC.1, fun hCO => hC.2 (of_map_conj_mem_conjOrbit hh hCO)⟩
    have heven : Even (Nat.card E') :=
      even_iff_two_dvd.mpr ((hS B hB).trans (Subgroup.card_dvd_of_le hBE'))
    obtain ⟨c, hcE', hcorder, hcC⟩ :=
      CFSG.ComponentClassification.SubgroupFixedInvolution.two_group_normalizing E' H heven hH hHE'
    have hHAbot : H ⊓ A = ⊥ :=
      le_antisymm (hHN ▸ le_inf inf_le_left (inf_le_right.trans (hN.le hA))) bot_le
    have hKA : 2 ∣ (H ⊓ A).relIndex A := by
      rw [hHAbot, Subgroup.relIndex_bot_left]
      exact hS A hA
    have hAE : A ≤ E := le_sSup (self_mem_conjOrbit H A)
    have hDM : ∀ d ∈ A ⊓ normalizer ((H ⊓ normalizer (A : Set G) : Subgroup G) : Set G),
        d ^ 2 ∈ H → d ∈ E ⊔ H :=
      fun d hd _ => Subgroup.mem_sup_left (hAE (mem_inf.mp hd).1)
    have ha : c ∈ normalizer (H : Set G) :=
      Subgroup.centralizer_le_normalizer (H : Set G) hcC
    have ha2 : c ^ 2 ∈ H := by
      rw [← hcorder, pow_orderOf_eq_one c]
      exact one_mem H
    have hmem : c ∈ E ⊔ H :=
      hiso.mem_of_component hN hSG hH hA hKA (M := E ⊔ H) le_sup_right hDM ha ha2
    have hEleN : E ≤ N := hN.sSup_diff_le O hOS
    have hcN : c ∈ N := (hN.sSup_diff_le (S \ O) Set.sdiff_subset) hcE'
    have hcE : c ∈ E := mem_of_mem_sup_of_le hHE hEleN hHN hmem hcN
    have hbot : E ⊓ E' = ⊥ := sSup_conjOrbit_inf_sSup_sdiff_eq_bot hN hSG hA
    have hcbot : c ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact mem_inf.mpr ⟨hcE, hcE'⟩
    rw [mem_bot] at hcbot
    have h12 : (1 : ℕ) = 2 := by rw [← hcorder, hcbot, orderOf_one]
    omega

theorem IsPIsolatedOver.inf_centralizer_of_isDirectProduct {H N : Subgroup G}
    {S : Set (Subgroup G)} (hiso : IsPIsolatedOver 2 (normalizer (H : Set G)) H)
    (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hH : IsPGroup 2 H)
    (hHN : H ⊓ N = ⊥) {A : Subgroup G} (hA : A ∈ S) (hev : 2 ∣ Nat.card A)
    (hHA : H ≤ normalizer (A : Set G)) :
    IsPIsolatedOver 2 (A ⊓ centralizer (H : Set G)) ⊥ := by
  have hNH : N ⊓ H = ⊥ := by rw [inf_comm]; exact hHN
  have hAH : A ⊓ H = ⊥ :=
    le_antisymm (hNH ▸ le_inf (inf_le_left.trans (hN.le hA)) inf_le_right) bot_le
  have hHAbot : H ⊓ A = ⊥ := by rw [inf_comm]; exact hAH
  have hKA : 2 ∣ (H ⊓ A).relIndex A := by
    rw [hHAbot, Subgroup.relIndex_bot_left]
    exact hev
  have h := hiso.inf_normalizer_of_component hN hSG hH hA hKA
  have hHnA : H ⊓ normalizer (A : Set G) = H := inf_eq_left.2 hHA
  rw [hHnA] at h
  rw [hHAbot, inf_normalizer_eq_inf_centralizer_of_inf_eq_bot hAH hHA] at h
  exact h

end CFSG.GroupTheory
