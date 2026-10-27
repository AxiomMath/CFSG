module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RCtx

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup

theorem exists_conj_of_equiv {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G}
    {T E : Subgroup G} {Q : Sylow 2 G} {x : G} {B : Subgroup G} {β : G} {S : Subgroup G}
    (c : OuterS16Ctx G L z t T E Q x B β S) {σ : G} {E₀ : Subgroup G}
    (hE₀σ : E₀ ≤ Subgroup.centralizer ({σ} : Set G)) (hiso : Nonempty (↥E ≃* ↥E₀))
    (hinv : ∀ w ∈ E₀, w * w = 1 → w ≠ 1 → ∃ g : G, g * t * g⁻¹ = w)
    {g₀ : G} (hg₀ : g₀ * z * g₀⁻¹ = σ) :
    ∃ g : G, g * z * g⁻¹ = σ ∧ E.map (MulAut.conj g).toMonoidHom = E₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : OuterE G L z t T E := c.hyp.outerE
  have hzt : ∃ x' : G, x' * z * x'⁻¹ = z * t := ⟨x, c.hyp.x_z⟩
  obtain ⟨φ⟩ := hiso
  have hE2 : IsPGroup 2 E := hO.cfg.T_pgroup.to_le hO.E_le_T
  have hE₀2 : IsPGroup 2 E₀ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hE2
    exact IsPGroup.of_card (n := n) (by rw [← Nat.card_congr φ.toEquiv]; exact hn)
  have hXp : IsPGroup 2 (E₀.map (MulAut.conj g₀⁻¹).toMonoidHom) := hE₀2.map _
  have hXC : E₀.map (MulAut.conj g₀⁻¹).toMonoidHom ≤ centralizer ({z} : Set G) := by
    rintro _ ⟨u, hu, rfl⟩
    have huσ : u * σ = σ * u := mem_centralizer_singleton_iff.1 (hE₀σ hu)
    have hA : g₀ * z = σ * g₀ := by rw [← hg₀]; group
    have hB : z * g₀⁻¹ = g₀⁻¹ * σ := by rw [← hg₀]; group
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc g₀⁻¹ * u * g₀ * z = g₀⁻¹ * u * (g₀ * z) := by group
      _ = g₀⁻¹ * u * (σ * g₀) := by rw [hA]
      _ = g₀⁻¹ * (u * σ) * g₀ := by group
      _ = g₀⁻¹ * (σ * u) * g₀ := by rw [huσ]
      _ = (g₀⁻¹ * σ) * u * g₀ := by group
      _ = (z * g₀⁻¹) * u * g₀ := by rw [hB]
      _ = z * (g₀⁻¹ * u * g₀) := by group
  obtain ⟨k, hkC, hkT⟩ := hO.cfg.exists_conj_into_T hXp hXC
  have hkz : k * z = z * k := mem_centralizer_singleton_iff.1 hkC
  obtain ⟨m, hm⟩ : ∃ m : G, m = g₀ * k := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Subgroup G, P = E₀.map (MulAut.conj m⁻¹).toMonoidHom := ⟨_, rfl⟩
  have memP : ∀ w, w ∈ P ↔ ∃ u ∈ E₀, m⁻¹ * u * m = w := by
    intro w
    rw [hP, Subgroup.mem_map]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hPT : P ≤ T := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := (memP w).1 hw
    have hmem : g₀⁻¹ * u * g₀ ∈ E₀.map (MulAut.conj g₀⁻¹).toMonoidHom :=
      ⟨u, hu, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    have h1 := hkT _ hmem
    convert h1 using 1
    rw [hm]
    group
  have hinjm : Function.Injective (MulAut.conj m⁻¹).toMonoidHom := (MulAut.conj m⁻¹).injective
  have hPiso : Nonempty (↥E ≃* ↥P) := by
    rw [hP]
    exact ⟨φ.trans (E₀.equivMapOfInjective _ hinjm)⟩
  obtain ⟨ψ⟩ := hPiso
  have hPinv : ∀ w ∈ P, w * w = 1 → w ≠ 1 → ∃ g : G, g * t * g⁻¹ = w := by
    intro w hw hw2 hw1
    obtain ⟨u, hu, rfl⟩ := (memP w).1 hw
    have hu2 : u * u = 1 := by
      calc u * u = m * ((m⁻¹ * u * m) * (m⁻¹ * u * m)) * m⁻¹ := by group
        _ = 1 := by rw [hw2]; group
    have hu1 : u ≠ 1 := by
      rintro rfl
      apply hw1
      group
    obtain ⟨g', hg'⟩ := hinv u hu hu2 hu1
    exact ⟨m⁻¹ * g', by rw [← hg']; group⟩
  have hEle : Subgroup.closure {e : G | e ∈ E ∧ e * e = 1 ∧ e ≠ 1} ≤ E :=
    hO.econfig.gen.symm.le
  have hEge : E ≤ Subgroup.closure {e : G | e ∈ E ∧ e * e = 1 ∧ e ≠ 1} :=
    hO.econfig.gen.le
  have key : ∀ y : G, ∀ hy : y ∈ Subgroup.closure {e : G | e ∈ E ∧ e * e = 1 ∧ e ≠ 1},
      ((ψ ⟨y, hEle hy⟩ : ↥P) : G) ∈ Subgroup.closure {e : G | e ∈ P ∧ e * e = 1 ∧ e ≠ 1} := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem a ha =>
      obtain ⟨haE, ha2, ha1⟩ := ha
      have hsq : ψ ⟨a, haE⟩ * ψ ⟨a, haE⟩ = 1 := by
        rw [← map_mul]
        have h1 : (⟨a, haE⟩ : ↥E) * ⟨a, haE⟩ = 1 := Subtype.ext ha2
        rw [h1, map_one]
      have hne : ψ ⟨a, haE⟩ ≠ 1 := by
        intro h
        apply ha1
        have h' : (⟨a, haE⟩ : ↥E) = 1 := ψ.injective (h.trans (map_one ψ).symm)
        exact congrArg Subtype.val h'
      apply Subgroup.subset_closure
      simp only [Set.mem_setOf_eq]
      exact ⟨(ψ ⟨a, haE⟩).2, congrArg Subtype.val hsq, fun h => hne (Subtype.ext h)⟩
    | one =>
      show ((ψ 1 : ↥P) : G) ∈ _
      rw [map_one, Subgroup.coe_one]
      exact one_mem _
    | mul a b ha hb iha ihb =>
      have hab : ((ψ ⟨a * b, hEle (mul_mem ha hb)⟩ : ↥P) : G) =
          ((ψ ⟨a, hEle ha⟩ : ↥P) : G) * ((ψ ⟨b, hEle hb⟩ : ↥P) : G) :=
        congrArg Subtype.val (map_mul ψ ⟨a, hEle ha⟩ ⟨b, hEle hb⟩)
      rw [hab]
      exact mul_mem iha ihb
    | inv a ha iha =>
      have hi : ((ψ ⟨a⁻¹, hEle (inv_mem ha)⟩ : ↥P) : G) = ((ψ ⟨a, hEle ha⟩ : ↥P) : G)⁻¹ :=
        congrArg Subtype.val (map_inv ψ ⟨a, hEle ha⟩)
      rw [hi]
      exact inv_mem iha
  have hPgen : P ≤ Subgroup.closure {e : G | e ∈ P ∧ e * e = 1 ∧ e ≠ 1} := by
    intro p hp
    have hy : (ψ.symm ⟨p, hp⟩ : G) ∈ Subgroup.closure {e : G | e ∈ E ∧ e * e = 1 ∧ e ≠ 1} :=
      hEge (ψ.symm ⟨p, hp⟩).2
    have h1 : ((ψ ⟨(ψ.symm ⟨p, hp⟩ : G), hEle hy⟩ : ↥P) : G) = p := by
      have h2 : (⟨(ψ.symm ⟨p, hp⟩ : G), hEle hy⟩ : ↥E) = ψ.symm ⟨p, hp⟩ := rfl
      rw [h2, MulEquiv.apply_symm_apply]
    rw [← h1]
    exact key _ hy
  have hPE : P ≤ E := by
    refine le_trans hPgen ?_
    refine (Subgroup.closure_le E).2 ?_
    rintro q ⟨hqP, hq2, hq1⟩
    exact hO.mem_of_conj_t hzt (hO.le_sup_of_equiv hPT ⟨ψ⟩ hqP) (hPinv q hqP hq2 hq1)
  have hPeq : P = E := Subgroup.eq_of_le_of_card_ge hPE (Nat.card_congr ψ.toEquiv).le
  have hE_eq : E₀.map (MulAut.conj m⁻¹).toMonoidHom = E := hP.symm.trans hPeq
  refine ⟨m, ?_, ?_⟩
  · rw [hm]
    calc g₀ * k * z * (g₀ * k)⁻¹ = g₀ * (k * z * k⁻¹) * g₀⁻¹ := by group
      _ = g₀ * (z * k * k⁻¹) * g₀⁻¹ := by rw [hkz]
      _ = g₀ * z * g₀⁻¹ := by group
      _ = σ := hg₀
  · rw [← hE_eq, Subgroup.map_map]
    have hcomp : (MulAut.conj m).toMonoidHom.comp (MulAut.conj m⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext a
      simp [MulAut.conj_apply, mul_assoc]
    rw [hcomp, Subgroup.map_id]

end CFSG.EvenSporadicStandard.Fin76b
