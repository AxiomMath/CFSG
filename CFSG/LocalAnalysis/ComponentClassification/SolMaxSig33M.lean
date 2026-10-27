module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig33J

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv
open scoped commutatorElement

variable {X : Type} [Group X]

theorem mem_normalizer_of_map_conj_le' [Finite X] {K : Subgroup X} {w : X}
    (h : K.map (MulAut.conj w).toMonoidHom ≤ K) : w ∈ normalizer (K : Set X) := by
  rw [mem_normalizer_iff_map_conj_eq]
  refine eq_of_le_of_card_ge h ?_
  rw [card_map_of_injective (MulAut.conj w).injective]

theorem mem_normalizer_fixedLayer [Finite X] {L : Subgroup X} {f g : X}
    (hLq : IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L))
    (hfK : zpowers f ≤ UnbalancedLayer.coreActionKernel L) (hf2 : IsPGroup 2 (zpowers f))
    (hgL : g ∈ normalizer (L : Set X)) (hgf : g * f = f * g) :
    g ∈ normalizer ((GSLit.fixedLayer L (zpowers f) : Subgroup X) : Set X) := by
  classical
  have hcl := GSLit.fixedLayer_eq_closure hLq hfK hf2
  rw [mem_normalizer_iff_map_conj_eq]
  have hle : (GSLit.fixedLayer L (zpowers f)).map (MulAut.conj g).toMonoidHom ≤
      GSLit.fixedLayer L (zpowers f) := by
    rw [hcl, MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨x, ⟨hx, k, hk⟩, rfl⟩
    obtain ⟨hxL, hxC⟩ := mem_inf.mp hx
    refine ⟨mem_inf.mpr ⟨?_, ?_⟩, k, ?_⟩
    · exact (mem_normalizer_iff.mp hgL x).mp hxL
    · rw [centralizer_zpowers_eq'] at hxC ⊢
      rw [mem_centralizer_singleton_iff] at hxC ⊢
      change g * x * g⁻¹ * f = f * (g * x * g⁻¹)
      have hginv : g⁻¹ * f = f * g⁻¹ := by
        calc g⁻¹ * f = g⁻¹ * (f * g) * g⁻¹ := by group
          _ = g⁻¹ * (g * f) * g⁻¹ := by rw [hgf]
          _ = f * g⁻¹ := by group
      calc g * x * g⁻¹ * f = g * x * (g⁻¹ * f) := by group
        _ = g * x * (f * g⁻¹) := by rw [hginv]
        _ = g * (x * f) * g⁻¹ := by group
        _ = g * (f * x) * g⁻¹ := by rw [hxC]
        _ = (g * f) * x * g⁻¹ := by group
        _ = (f * g) * x * g⁻¹ := by rw [hgf]
        _ = f * (g * x * g⁻¹) := by group
    · change orderOf ((MulAut.conj g) x) = 2 ^ k
      rw [MulEquiv.orderOf_eq]
      exact hk
  refine eq_of_le_of_card_ge hle ?_
  rw [card_map_of_injective (MulAut.conj g).injective]

theorem mem_coreActionKernel_of_mod_core [Finite X] {H K : Subgroup X} (hKH : K ≤ H)
    (hKpc : IsPComponent 2 (K.subgroupOf H)) {e : X} (heH : e ∈ H) (he2 : e * e = 1)
    (hK : ∀ x ∈ K, x⁻¹ * e⁻¹ * x * e ∈ (pPrimeCore 2 ↥H).map H.subtype) :
    e ∈ UnbalancedLayer.coreActionKernel K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := (pPrimeCore 2 ↥H).map H.subtype with hOdef
  have hinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hON : H ≤ normalizer (O : Set X) := Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥H)
  have heN : zpowers e ≤ normalizer (((O ⊔ K : Subgroup X)) : Set X) := by
    rw [zpowers_le]
    refine mem_normalizer_of_map_conj_le' ?_
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · have h1 : O.map (MulAut.conj e).toMonoidHom = O :=
        (mem_normalizer_iff_map_conj_eq.mp (hON heH))
      rw [h1]
      exact le_sup_left
    · rintro _ ⟨x, hx, rfl⟩
      have h1 := hK x hx
      rw [hinv] at h1
      have h2 : (MulAut.conj e).toMonoidHom x = x * (x⁻¹ * e * x * e) := by
        change e * x * e⁻¹ = x * (x⁻¹ * e * x * e)
        rw [hinv]
        group
      rw [h2]
      exact mul_mem (mem_sup_right hx) (mem_sup_left h1)
  have heK : e ∈ normalizer (K : Set X) :=
    le_normalizer_of_le_normalizer_sup hKH hKpc (zpowers_le.mpr heH) heN (mem_zpowers e)
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨heK, fun x hx => ?_⟩
  have h1 : x⁻¹ * e⁻¹ * x * e ∈ K := by
    have h3 : e⁻¹ * x * e ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem heK) x).mp hx
      simpa using this
    have h4 := mul_mem (inv_mem hx) h3
    simpa [mul_assoc] using h4
  exact inf_pPrimeCore_le hKH ⟨h1, hK x hx⟩

theorem mem_coreActionKernel_of_fixedLayer [Finite X] {C L Lf : Subgroup X} (hLC : L ≤ C)
    (hLpc : IsPComponent 2 (L.subgroupOf C)) (hLfL : Lf ≤ L) (hLfperf : ⁅Lf, Lf⁆ = Lf)
    (hLfq : Nontrivial (↥Lf ⧸ pPrimeCore 2 ↥Lf))
    (hsup : Lf ⊔ (pPrimeCore 2 ↥L).map L.subtype = L)
    (hcore : (pPrimeCore 2 ↥Lf).map Lf.subtype ≤ (pPrimeCore 2 ↥L).map L.subtype) {e : X}
    (heC : e ∈ C) (heK : e ∈ UnbalancedLayer.coreActionKernel Lf) :
    e ∈ UnbalancedLayer.coreActionKernel L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set OL := (pPrimeCore 2 ↥L).map L.subtype with hOLdef
  have heLf : e ∈ normalizer (Lf : Set X) := heK.1
  have heL : e ∈ normalizer (L : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    by_contra hne
    obtain ⟨heLC, heLpc⟩ := isPComponent_conj hLC hLpc heC
    have hK := GSThmB.B5a.le_coreActionKernel_of_ne hLC heLC hLpc heLpc (Ne.symm hne)
    have hLfeL : Lf ≤ L.map (MulAut.conj e).toMonoidHom := by
      intro x hx
      have h1 : e⁻¹ * x * e ∈ Lf := by
        have := (mem_normalizer_iff.mp (inv_mem heLf) x).mp hx
        simpa using this
      exact ⟨e⁻¹ * x * e, hLfL h1, by simp [mul_assoc]⟩
    have h1 : ⁅Lf, Lf⁆ ≤ OL :=
      (commutator_mono hLfL hLfeL).trans (commutator_le_of_le_coreActionKernel hK)
    rw [hLfperf] at h1
    have hodd : Nat.Coprime 2 (Nat.card Lf) := by
      have h2 : Nat.card Lf ∣ Nat.card OL := card_dvd_of_le h1
      rw [hOLdef, card_map_of_injective L.subtype_injective] at h2
      exact Nat.Coprime.coprime_dvd_right h2 pPrimeCore_coprime_card
    have htop : pPrimeCore 2 ↥Lf = ⊤ := by
      rw [eq_top_iff]
      exact le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
    have : Subsingleton (↥Lf ⧸ pPrimeCore 2 ↥Lf) := QuotientGroup.subsingleton_iff.mpr htop
    exact false_of_nontrivial_of_subsingleton (↥Lf ⧸ pPrimeCore 2 ↥Lf)
  have hON : L ≤ normalizer (OL : Set X) := fun x hx => le_normalizer_pPrimeCore (le_normalizer hx)
  have hc : ⁅zpowers e, L⁆ ≤ OL := by
    rw [← hsup]
    refine commutator_sup_le (C := normalizer (OL : Set X)) le_rfl
      (fun x hx => hON (hLfL hx)) le_normalizer ?_ ?_
    · rw [commutator_comm]
      exact (commutator_le_of_le_coreActionKernel (zpowers_le.mpr heK)).trans hcore
    · rw [commutator_le]
      intro g hg o ho
      have hgL : g ∈ normalizer (L : Set X) := (zpowers_le.mpr heL) hg
      have h1 : g * o * g⁻¹ ∈ OL :=
        (mem_normalizer_iff.mp (le_normalizer_pPrimeCore hgL) o).mp ho
      rw [commutatorElement_def]
      exact mul_mem h1 (inv_mem ho)
  refine UnbalancedLayer.mem_coreActionKernel.mpr ⟨heL, fun j hj => ?_⟩
  have h1 : ⁅e⁻¹, j⁻¹⁆ ∈ ⁅zpowers e, L⁆ :=
    commutator_mem_commutator (inv_mem (mem_zpowers e)) (inv_mem hj)
  have h2 : j⁻¹ * e⁻¹ * j * e = ⁅e⁻¹, j⁻¹⁆⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [h2]
  exact inv_mem (hc h1)

theorem map_conj_mem_pair [Finite X] {C M Jc : Subgroup X} {t b : X} (htt : t * t = 1)
    (htC : t ∈ C) (hbC : b ∈ C) (htb : t * b = b * t) (hMC : M ≤ C)
    (hMpc : IsPComponent 2 (M.subgroupOf C))
    (hJcM : Jc ≤ M ⊔ M.map (MulAut.conj t).toMonoidHom)
    (hbJc : b ∈ normalizer (Jc : Set X))
    (hJcK : ¬ Jc ≤ UnbalancedLayer.coreActionKernel M) :
    M.map (MulAut.conj b).toMonoidHom = M ∨
      M.map (MulAut.conj b).toMonoidHom = M.map (MulAut.conj t).toMonoidHom := by
  classical
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨hMbC, hMbpc⟩ := isPComponent_conj hMC hMpc hbC
  obtain ⟨hMtC, hMtpc⟩ := isPComponent_conj hMC hMpc htC
  obtain ⟨hMtbC, hMtbpc⟩ := isPComponent_conj hMtC hMtpc hbC
  have hcomm : (M.map (MulAut.conj t).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      (M.map (MulAut.conj b).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext z
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulAut.conj_apply]
    have hbt : b * t = t * b := htb.symm
    calc b * (t * z * t⁻¹) * b⁻¹ = (b * t) * z * (b * t)⁻¹ := by group
      _ = (t * b) * z * (t * b)⁻¹ := by rw [hbt]
      _ = t * (b * z * b⁻¹) * t⁻¹ := by group
  have h3 : (M.map (MulAut.conj t).toMonoidHom).map (MulAut.conj b).toMonoidHom ≠ M := by
    intro h
    apply h2
    have h4 : ((M.map (MulAut.conj t).toMonoidHom).map (MulAut.conj b).toMonoidHom).map
        (MulAut.conj t).toMonoidHom = M.map (MulAut.conj t).toMonoidHom := by rw [h]
    rw [hcomm, map_conj_map_conj_of_mul_self htt] at h4
    exact h4
  have hK1 : M.map (MulAut.conj b).toMonoidHom ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMC hMbC hMpc hMbpc (Ne.symm h1)
  have hK2 : (M.map (MulAut.conj t).toMonoidHom).map (MulAut.conj b).toMonoidHom ≤
      UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hMC hMtbC hMpc hMtbpc (Ne.symm h3)
  apply hJcK
  have hJcb : Jc = Jc.map (MulAut.conj b).toMonoidHom :=
    (mem_normalizer_iff_map_conj_eq.mp hbJc).symm
  rw [hJcb]
  refine (map_mono hJcM).trans ?_
  rw [Subgroup.map_sup]
  exact sup_le hK1 hK2

end CFSG.ComponentClassification.SolMax
